"""GitHub's GraphQL answer to bulk.QUERY, built from the same fixtures the REST fakes serve.

Inverse of sphereceti.bulk: `gh pr list --json` PR objects become pullRequests nodes, and REST
issue comments become comment nodes, so a fake can answer both the old and the bulk survey from
one table, and tests can prove both paths decide identically.
"""


def check_node(check):
    if check.get('__typename') == 'StatusContext':
        return {'__typename': 'StatusContext', 'context': check.get('context'), 'state': check.get('state'),
                'targetUrl': check.get('targetUrl'), 'createdAt': check.get('startedAt')}
    if check.get('__typename') == 'CheckRun':
        return {'__typename': 'CheckRun', 'name': check.get('name'), 'status': check.get('status'),
                'conclusion': check.get('conclusion'), 'startedAt': check.get('startedAt'),
                'completedAt': check.get('completedAt'), 'detailsUrl': check.get('detailsUrl'),
                'checkSuite': {'workflowRun': {'workflow': {'name': check.get('workflowName')}}}}
    return check


def comment_node(comment):
    user = comment.get('user') or {}
    login = user.get('login')
    if user.get('type') == 'Bot' and isinstance(login, str):
        login = login.removesuffix('[bot]')
    return {'databaseId': comment.get('id'), 'body': comment.get('body'), 'createdAt': comment.get('created_at'),
            'updatedAt': comment.get('updated_at'), 'url': comment.get('html_url'),
            'authorAssociation': comment.get('author_association'),
            'author': {'__typename': user.get('type'), 'login': login, 'databaseId': user.get('id')}}


def pr_node(pr, comments, limit=100):
    author = pr.get('author') or {}
    listed = comments[:limit]
    return {'number': pr['number'], 'title': pr['title'], 'updatedAt': pr['updatedAt'], 'state': pr['state'],
            'isDraft': pr['isDraft'], 'mergeable': pr['mergeable'], 'headRefOid': pr['headRefOid'],
            'baseRefOid': pr['baseRefOid'], 'baseRefName': pr['baseRefName'], 'headRefName': pr['headRefName'],
            'author': {'__typename': 'Bot' if author.get('is_bot') else 'User',
                       'login': (author.get('login') or '').removeprefix('app/') if author.get('is_bot')
                       else author.get('login'),
                       'id': author.get('id'), 'databaseId': author.get('databaseId'), 'name': author.get('name')},
            'headRepository': pr.get('headRepository'),
            'commits': {'nodes': [{'commit': {'statusCheckRollup': {'contexts': {'nodes': [
                check_node(c) for c in pr.get('statusCheckRollup') or []]}}}}]},
            'comments': {'totalCount': len(comments), 'nodes': [comment_node(c) for c in listed]}}


def graphql_page(prs, comments, viewer, cursor=None, page=20, limit=100):
    """One page of bulk.QUERY's answer; `comments` maps PR number (int or str) to REST comments."""
    start = int(cursor) if cursor else 0
    chunk = prs[start:start + page]
    nodes = [pr_node(pr, list(comments.get(pr['number'], comments.get(str(pr['number']), []))), limit)
             for pr in chunk]
    more = start + page < len(prs)
    return {'data': {'viewer': {'login': viewer}, 'repository': {'pullRequests': {
        'totalCount': len(prs), 'pageInfo': {'hasNextPage': more, 'endCursor': str(start + page) if more else None},
        'nodes': nodes}}}}
