#!/usr/bin/env python3
"""Advisory comparison against anonymous exact-revision cache bytes; never import archives.

Adapted from TauCeti's pinned nightly-verify.yml / compare-build-outputs.py separation:
source verification is the hard result; missing or unusable cache evidence is inconclusive.
"""
from pathlib import Path
import argparse
import http.client
import json
import sys
import urllib.request

sys.path.insert(0, str(Path(__file__).resolve().parent))
from publication import (MAX_BYTES, PublicationError, digest, endpoint, map_url, read_map,
                         regular, validate_staging)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise PublicationError('cache comparison refuses redirects')


def fetch(url, limit):
    with urllib.request.build_opener(NoRedirect).open(url, timeout=30) as response:
        data = response.read(limit + 1)
    if len(data) > limit:
        raise PublicationError('cache response exceeds size limit')
    return data


def compare(stage, sha, artifact_endpoint, revision_endpoint, read=fetch):
    if not artifact_endpoint or not revision_endpoint:
        return {'status': 'inconclusive', 'reason': 'public SphereCeti cache endpoints are not configured'}
    try:
        validate_staging(stage)
        local = regular(stage / 'outputs.jsonl', 8 * 1024 * 1024)
        remote = read(map_url(revision_endpoint, sha), 8 * 1024 * 1024)
        names = read_map(remote)
        # Compare parsed mappings: ordering alone is not an artifact difference.
        if sorted(local.decode().splitlines()) != sorted(remote.decode().splitlines()):
            return {'status': 'divergent', 'reason': 'exact-revision output mappings differ'}
        base = endpoint(artifact_endpoint)
        remaining = MAX_BYTES
        for name in sorted(names):
            data = read(base + '/' + name, remaining)
            remaining -= len(data)
            if digest(data) != digest(regular(stage / name)):
                return {'status': 'divergent', 'reason': f'cache artifact differs: {name}'}
        return {'status': 'agreement', 'reason': f'compared {len(names)} exact-revision archive(s); no artifacts executed'}
    except (OSError, ValueError, http.client.HTTPException) as exc:
        return {'status': 'inconclusive', 'reason': f'cache evidence unavailable: {type(exc).__name__}'}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage', type=Path); p.add_argument('revision')
    p.add_argument('--artifact-endpoint', default=''); p.add_argument('--revision-endpoint', default='')
    args = p.parse_args()
    result = compare(args.stage, args.revision, args.artifact_endpoint, args.revision_endpoint)
    print(json.dumps(result, indent=2))
    # Advisory status is data; the independent source verification job owns the hard result.
