#!/usr/bin/env python3
"""prices.json must stay in sync with the model registry.

Every model the engine can dispatch needs a price, or its review silently mis-charges the daily
budget (require_priced() now fails fast at runtime; this catches it at PR time, before merge).
Dependency-free — run with `python tests/test_prices.py` or under pytest.
"""
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "runner"))
import review  # noqa: E402  (runner/ on path; same import the engine uses)
import pricing  # noqa: E402


def test_every_dispatchable_model_is_priced():
    missing = sorted(m for m in review.dispatch_models() if m not in review.PRICES)
    assert not missing, (
        f"models the engine can dispatch but prices.json doesn't price: {missing}. "
        f"Add them to runner/prices.json (priced: {sorted(review.PRICES)})")


# SphereCeti: adapted from TauCetiReview #172 (baf2e680b43369805621e6ff0b6c984cab5e4ccb), which
# also moved the engine's default to gpt-6.1-sol. SphereCeti keeps the gpt-5.6-sol default, so
# this pins the explicitly selectable Sol61 rates and their admission instead.
def test_sol_61_is_priced_at_its_own_rates():
    assert review.PRICES["gpt-6.1-sol"] == (2.0, 10.0)
    assert pricing.CACHE_READ["gpt-6.1-sol"] == 0.1
    review.require_priced(review.dispatch_models(codex_model="gpt-6.1-sol"))


# SphereCeti: a local gpt-6.2-sol row (effective 2026-11-17, no upstream change prices it yet) at
# exactly Sol61's standard and long-context rates; the contributor CLI's default Codex model.
def test_sol_62_is_priced_at_sol_61_rates():
    assert review.PRICES["gpt-6.2-sol"] == review.PRICES["gpt-6.1-sol"] == (2.0, 10.0)
    assert pricing.CACHE_READ["gpt-6.2-sol"] == pricing.CACHE_READ["gpt-6.1-sol"] == 0.1
    sol62, sol61 = review._PRICE_WINDOWS["gpt-6.2-sol"], review._PRICE_WINDOWS["gpt-6.1-sol"]
    assert len(sol62) == 1 and sol62[0]["effective"] == "2026-11-17"
    assert {k: v for k, v in sol62[0].items() if k != "effective"} == \
        {k: v for k, v in sol61[-1].items() if k != "effective"}
    assert sol62[0]["long_context"] == {"threshold": 272000, "input": 4.0, "output": 15.0,
                                        "cache_read": 0.2, "cache_write": 5.0}
    review.require_priced(review.dispatch_models(codex_model="gpt-6.2-sol"))


def test_price_windows_are_well_formed():
    bad = []
    for model, windows in review._PRICE_WINDOWS.items():
        if not windows:
            bad.append(f"{model}: no rate windows")
            continue
        for w in windows:
            if not isinstance(w.get("effective"), str):
                bad.append(f"{model}: window missing `effective` date")
            for field in ("input", "output"):
                if not isinstance(w.get(field), (int, float)):
                    bad.append(f"{model}@{w.get('effective')}.{field}")
            for field in ("cache_read", "cache_write", "cache_write_5m", "cache_write_1h"):
                if field in w and not isinstance(w[field], (int, float)):
                    bad.append(f"{model}@{w.get('effective')}.{field}")
            lc = w.get("long_context")
            if lc is not None:
                if not isinstance(lc.get("threshold"), int) or isinstance(lc.get("threshold"), bool):
                    bad.append(f"{model}@{w.get('effective')}.long_context.threshold")
                for field in ("input", "output"):
                    if not isinstance(lc.get(field), (int, float)):
                        bad.append(f"{model}@{w.get('effective')}.long_context.{field}")
                for field in ("cache_read", "cache_write"):
                    if field in lc and not isinstance(lc[field], (int, float)):
                        bad.append(f"{model}@{w.get('effective')}.long_context.{field}")
        # windows must be in chronological order so "newest" / "as-of-date" resolution is correct
        effs = [w.get("effective") for w in windows]
        if effs != sorted(effs):
            bad.append(f"{model}: windows not sorted by effective date {effs}")
    assert not bad, f"malformed price windows: {bad}"


def _write_fields(model):
    """The cache-write rate fields `model`'s provider bills by, and nothing else: Anthropic prices
    a write by its TTL, OpenAI prices one write rate, and the OpenRouter route reports no writes."""
    if "/" in model:
        return ()
    return ("cache_write_5m", "cache_write_1h") if model.startswith("claude-") else ("cache_write",)


def test_every_window_carries_exactly_the_write_rates_its_family_is_billed_at():
    """The worker vendors this table and prices prompt-cache writes from it, so a window missing
    its family's write rate is a KeyError there rather than a visible gap here. A field from the
    wrong family is the same error wearing the other provider's name, so both directions fail."""
    wrong = []
    for model, windows in review._PRICE_WINDOWS.items():
        wanted = set(_write_fields(model))
        for w in windows:
            for rates, where in ((w, model), (w.get("long_context") or {}, f"{model}.long_context")):
                if not rates:
                    continue
                present = {f for f in ("cache_write", "cache_write_5m", "cache_write_1h") if f in rates}
                wrong += [f"{where}@{w['effective']}: missing {f}" for f in wanted - present]
                wrong += [f"{where}@{w['effective']}: {f} is not billed on this route" for f in present - wanted]
    assert not wrong, f"windows whose write rates do not match their family: {wrong}"


def test_write_rates_are_their_providers_published_multiple_of_the_input_rate():
    """Both providers derive a cache write from the input rate: Anthropic bills 1.25x for a
    5-minute TTL and 2x for an hour, OpenAI 1.25x. Checking only that a write exceeds input
    accepts a 5x typo, and accepts the 5-minute and 1-hour rates swapped, which is the error two
    adjacent same-shaped numbers actually invite."""
    MULTIPLES = {"cache_write": 1.25, "cache_write_5m": 1.25, "cache_write_1h": 2.0}
    bad = []
    for model, windows in review._PRICE_WINDOWS.items():
        for w in windows:
            for rates, where in ((w, model), (w.get("long_context") or {}, f"{model}.long_context")):
                if not rates:
                    continue
                for field, multiple in MULTIPLES.items():
                    if field not in rates:
                        continue
                    want = round(rates["input"] * multiple, 10)
                    if round(rates[field], 10) != want:
                        bad.append(f"{where}@{w['effective']}: {field} {rates[field]}, expected {want}")
                if rates.get("cache_read", rates["input"]) > rates["input"]:
                    bad.append(f"{where}@{w['effective']}: cache_read {rates['cache_read']} exceeds input")
    assert not bad, f"cache rates off their provider's published multiplier: {bad}"


def test_long_context_tier_is_twice_input_and_half_again_output():
    """OpenAI states the >272K tier as 2x input and 1.5x output applied to the whole request, and
    discounts its cache reads from the tier's own input rate. Stating the tier as absolute numbers
    is clearer to read than a multiplier in code, but it does have to be the right numbers."""
    bad = []
    for model, windows in review._PRICE_WINDOWS.items():
        for w in windows:
            lc = w.get("long_context")
            if lc is None:
                continue
            for field, multiple in (("input", 2.0), ("output", 1.5), ("cache_read", 2.0)):
                if field not in lc:
                    continue
                want = round(w[field] * multiple, 10)
                if round(lc[field], 10) != want:
                    bad.append(f"{model}@{w['effective']}.long_context.{field} {lc[field]}, expected {want}")
            if lc.get("threshold") != 272000:
                bad.append(f"{model}@{w['effective']}.long_context.threshold {lc.get('threshold')}")
    assert not bad, f"long-context tiers off their published multipliers: {bad}"


def test_the_rates_in_force_are_the_providers_list_prices():
    """Literal, and deliberately tedious to update: every rate here was read off the provider's
    own page, and a dated table's failure mode is a number nobody notices is wrong. A genuine
    price change adds a window and updates one line here, with the provider page as the citation.
    `cache_read` is listed because it is not a fixed multiple of input. SphereCeti: TauCetiReview
    #175's list without the unimported Opus 5.5 and Fable 5.1 rows, read through PRICES and
    CACHE_READ because this import predates #174's rates()."""
    expected = {
        "claude-opus-4-8":          (5.0,   25.0, 0.5),
        "claude-opus-5":            (5.0,   25.0, 0.5),
        "claude-sonnet-4-6":        (3.0,   15.0, 0.3),
        "claude-fable-5":           (10.0,  50.0, 1.0),
        "claude-haiku-4-5":         (1.0,   5.0,  0.1),
        "gpt-5.5":                  (5.0,   30.0, 0.5),
        "gpt-5.6-sol":              (4.0,   20.0, 0.4),
        "gpt-5.6-terra":            (2.0,   12.0, 0.2),
        "gpt-5.6-luna":             (0.2,   1.2,  0.02),
        "gpt-6-sol":                (2.0,   10.0, 0.2),
        "gpt-6.1-sol":              (2.0,   10.0, 0.1),
        "gpt-6.2-sol":              (2.0,   10.0, 0.1),
        "gpt-6-luna":               (0.1,   0.5,  0.01),
        "deepseek/deepseek-v4-pro": (0.435, 0.87, 0.004),
        "minimax/minimax-m3":       (0.3,   1.2,  0.3),
        "x-ai/grok-4.3":            (1.25,  2.5,  1.25),
    }
    assert sorted(expected) == sorted(review._PRICE_WINDOWS), (
        "a model was added to or removed from prices.json without updating this list: "
        f"{sorted(set(expected) ^ set(review._PRICE_WINDOWS))}")
    for model, (pin, pout, pcache) in expected.items():
        billed = (*review.PRICES[model], pricing.CACHE_READ[model])
        assert billed == (pin, pout, pcache), f"{model} bills {billed}, expected {(pin, pout, pcache)}"


def test_the_codex_fallback_is_priced_at_its_own_rates():
    """The seamless downgrade in run_one can route any codex rubric here, so the fallback's rates
    drive real spend and the daily budget as much as the default's do."""
    assert review.CODEX_FALLBACK_MODEL == "gpt-5.6-terra"
    assert review.PRICES[review.CODEX_FALLBACK_MODEL] == (2.0, 12.0)
    assert pricing.CACHE_READ[review.CODEX_FALLBACK_MODEL] == 0.2


def test_require_priced_rejects_unknown_model():
    try:
        review.require_priced({"definitely-not-a-real-model"})
    except SystemExit:
        return
    raise AssertionError("require_priced() should SystemExit on an unpriced model")


if __name__ == "__main__":
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        fn()
        print(f"ok  {fn.__name__}")
    print(f"\nall {len(fns)} price checks passed "
          f"({len(review.dispatch_models())} dispatchable models, all priced)")
