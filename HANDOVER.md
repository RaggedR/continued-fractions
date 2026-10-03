# Handover: `all-the-proofs.tex` is formalised end to end

**Phase 9 closed on 3 October 2026.** `mechanical_of_isSturmian` and
`isSturmian_iff_mechanical` are proved, `lean/Sturmian.lean` has no `sorry`,
`lean/build.sh` is green across all five files in about 50 seconds, and
`all-the-proofs.tex` §11 still reads "Nothing". Every statement in the paper
now has a Lean counterpart, `lem:slope` included — `exists_slopes` for the
existence half, `slopes_unique` for "exactly one", and irrationality by the
periodicity route rather than the paper's descent.

Read `lean/PLAN.md` Phase 9 for the decomposition and `lean/README.md` for
file sizes. This file records what the last session found, because one of the
findings was a hole in the paper.

## A gap in §7, found and repaired

`prop:bound`'s lower bound read the block to the left of `u'` when `s = a`.
**A factor sitting in the run of zeros before the first `1` has no block to
its left**, and the case is reachable: `isLeast_code_zero`
(`Sturmian.lean:3108`) puts the first `1` of `code γ 0` at exactly `a`, so it
fires at the tower's own base case. The conclusion `|Δ| < 1` survives, but at
`0.9948` — and `α(a+β) = 1` is an identity, so there was no slack to absorb a
missing case.

`step5_check.py` had not seen it. Claim A ran from `M = 0`, but claim B, the
decomposition, ran `for M in range(kp[0], Mmax)` — **every one of the
3,022,668 windows started at the first `1`**, so the test shared the proof's
blind spot. It now starts at `0`, reports an `in run` column, and asserts the
repair; 3,024,000 windows, and `in run` is nonzero only at intercept `0`.

The repair is **recurrence**: every factor occurs at arbitrarily large
positions, so the occurrence moves past the run, and `Δ_α` does not care where
the word sits. It is `lem:recur` in the paper and `exists_window_ge` in Lean,
proved from `ncard_factors_succ` and `eventuallyPeriodic_of_rightSpecial_empty`
— a tail that omits a factor has complexity `≤ m` at `m`, so its complexity
stops rising somewhere below `m`, so it is eventually periodic. Not the
textbook route, and it needed no new machinery.

The cheap-looking alternative — adding "`Δ_{α_j}(prefix) < α_j` at every
level" to the induction — **is false**; `s = 0, t = 0` breaks it. Do not retry
it.

## Where the Lean beat the paper

* **`Δ_α` takes a pair, not a word.** `dev α n w = w − αn`. Every use in §7
  needs only `|u|` and `|u|₁`, so `lem:dev` is one `linear_combination` and
  `τ_a` is never constructed — the dodge §6.1 already uses.
* **The slopes are a hypothesis.** `Tower` carries `α`, `β` and the step
  `α(a + β) = 1` as fields, following `tower_eq`'s precedent, so `prop:bound`
  needs no limits. `exists_slopes` discharges them on its own.
* **Irrationality is not a descent.** The paper descends on denominators. In
  Lean it is cheaper last: a rational slope makes the coding periodic with
  period `r.den`, contradicting `not_eventuallyPeriodic`. The descent never
  had to be formalised. Uniqueness, by contrast, is the contraction run
  directly: two compatible families agree to `4^{-d}` at every depth, so
  `slopes_unique` is thirty lines on top of `eps_dist`.
* **Aperiodicity is not a hypothesis.** `PLAN.md`'s target statement carried
  `hap`; the proved theorem drops it, since `IsSturmian` already implies it.
* **The exchange is invariant, not bookkeeping.** Exchanging letters sends
  weight `w` to `m − w`, and `dev (1−α) m (m−w) = −dev α m w`. So `|Δ| < 1`
  survives it, and a tower with every other level complemented needs one
  bridging lemma (`dev_derive_of_dev`), not a parallel development.
* **`sum_codeUp` needs no hypothesis on `x`** — the telescope leaves `⌈x⌉`.
* **`ncard_factors_codeUp` got shorter.** Its inlined complementation argument
  is now `exch` / `ncard_factors_exch`, reused by the tower; 1195 characters
  became 555.

The step the earlier handover called "plumbing that is not in any step" — the
letter exchange threaded through the tower — is the spine, not an afterthought:
`isSturmian_deriveSeq` does not return `11`-freeness, so every level reruns
`step_one`. And "§6.1 is irrelevant to §7" was wrong: `exists_decomp`, the
largest single piece, is positional `omega` work built on `cnt`,
`onesPos_block_length` and `onesPos_block_zero`.

## Build

```bash
./lean/build.sh                 # all five files
python3 step5_check.py          # asserts; prints nothing but its own ticks
tectonic all-the-proofs.tex
```

`build.sh` borrows an unrelated project's Mathlib. To rebuild `Sturmian.lean`
alone during a session — about 20 seconds:

```bash
cd ~/git/experiments/waarnar/loop-experiment/lean && lake env sh -c \
  "cd ~/git/continued-fractions/lean && LEAN_PATH=\$LEAN_PATH:/tmp/cf-oleans \
   lean -o /tmp/cf-oleans/Sturmian.olean Sturmian.lean"
```

The inner `cd` is load-bearing; without it `lean` cannot find the file and the
error is a bare "no such file or directory".

## If there is to be a next thing

Nothing is owed. Two candidates, both outward-facing rather than internal:

* **Upstream `exists_iterate_eq_self`** (`Palindrome.lean`, ~15 lines, no
  number theory) — `PLAN.md` already flags it as belonging in
  `Mathlib.Dynamics`.
* **Upstream the Sturmian API.** `PLAN.md`'s October 2026 survey found
  nothing comparable in Mathlib, the Isabelle AFP, or Rocq: no complexity
  function, no factor-set or special-factor API. What exists here —
  `factors`, `extBy`, `rightSpecial`, `window`, `cnt`, `deriveSeq`,
  `blockMax`, `exch`, and `isSturmian_iff_mechanical` on top of them — would
  be the first of its kind, and Berstel's definitions are verbatim ours.

## Two decisions already taken, so they are not re-litigated

* **The corrupt blob in history stays.** Commit `a74730f` carries a 92.8MB
  corruption of `lean/PLAN.md`, restored in `14fa7fe`; see `LESSONS.md`.
  Packed it costs 0.61MB. The commits are public, and GitHub warned on the
  push of 3 October (`File lean/PLAN.md is 92.84 MB`, `GH001`), so it is not
  invisible — but removing it now means rewriting *pushed* history, which the
  global `CLAUDE.md` forbids outright. Do not attempt it. If the warning ever
  becomes a rejection, that is a conversation with Robin, not a unilateral
  rewrite.
* **The root `README.md` does not restate Lean counts**, and `PLAN.md` no
  longer does either. Sizes live in `lean/README.md`. One copy of every
  number.

## Method that worked, and keeps working

- **Numerics before prose, every time** — and **extend the numerics to the
  case you are about to claim**. The §7 gap survived 3,022,668 checked factors
  because the test and the proof made the same assumption. When a proof says
  "the block to the left", check that there is one.
- **Check the test before believing a counterexample.** Three times now the
  test was wrong and the claim was right.
- **Never test on a decimal truncation.** Build slopes as
  `sqrt(n) - floor(sqrt(n))`.
- **`LESSONS.md` governs the prose.** Read it before writing any sentence in
  the `.tex`. Shortest relevant rules: no stage direction, no advance
  summaries of method, no restating a display in prose, concrete before
  general, and no paragraph over three lines in a definitional passage.
- **Three strikes.** Lothaire ch. 2 and Vuillon's "Balanced words" are
  recorded in `papers/sturmian/README.md` with citations rather than retried.
  Neither was needed: the errata's Proposition 2.1.10 is our `prop:bound`, and
  §7 proves it in half a page from `lem:blocks`.
