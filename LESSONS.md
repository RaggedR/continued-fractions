# LESSONS

Rules for writing prose in this repository. Robin rewrote or deleted nearly
every sentence I drafted on 30 September 2026; these are the patterns.

## Do not write

- **Stage direction.** "Now note that", "Look again at", "That always happens",
  "which is the shape claimed", "It remains to see". If the reader is about to
  see it, do not tell them to look.
- **Advance summaries of method.** "Each step below turns one numerator into a
  1 and pushes the problem one floor down." State the goal, not the machinery.
- **Interpretation after a result.** "The repetition is not a pattern spotted
  in a decimal expansion; it is a loop closing." The display said it.
- **Restating a display in prose**, before or after it.
- **Naming a technique being reused.** "exactly as in §2", "by the same move".
- **Defensive side conditions** the reader will not doubt ("it is never 0/0").

## Do write

- Short declaratives. "This is called a continued fraction." "We are back
  where we started."
- `so:` or `Now:` as the joint before a display. Nothing more.
- Purpose, then move: "We need an expression for (x+2)/3, so subtract 1 to get
  (x-1)/3, and use (x-1)(x+1) = 6 to get:"
- Facts at the point of use, not announced in advance.
- Chains, not split clauses: `x^2 - 1 = (x-1)(x+1) = 1`, not two sentences.

## Structure

- Concrete before general. Worked example, then the lemma.
- Define objects before proving things about them. Do not state a recurrence
  and assert existence in the same breath; it reads as circular.
- Name an induction statement and index it (`S_i`) so "assume S_i" is visibly
  not "assume the lemma".
- When a proof needs a stronger hypothesis than the conclusion, say so
  ("extra baggage") rather than smuggling it in.

## Process

- Verify arithmetic numerically before writing it into the .tex.
- Compile with `tectonic`, grep for overfull/undefined, and render the page
  with `pdftoppm` to look at it.
- Apply the edit asked for. Flag knock-on damage in chat, do not fix it
  unasked.

## Scale of edit (1 October 2026)

Robin gave fifteen local instructions on the Möbius material and rejected the
result three times, finally writing it himself. Every rejection followed the
same cause: the edit was larger than the instruction.

- **Edit at the scale asked.** "Induction on i → The proof is by induction on i"
  is a sentence edit. It is not an invitation to audit the paragraph, add a
  display, or restructure the proof.
- **A question in chat is answered in chat.** When he asked "is it M(a+b) or
  M(ab)?", the answer belonged in the reply only. Writing the negative result
  into the paper put a dead end in front of the reader.
- **Each edit must not grow the word count.** Fixing a flaw by adding two
  sentences hands him more to delete. Prefer a shorter replacement; if the fix
  genuinely needs words, say so in chat and let him decide.
- **Never justify an inequality step in prose.** "dividing by Q_i — legitimate,
  and direction-preserving, precisely because Q_i > 0 — gives" is padding.
  Write the step; the hypothesis is on the page already.
- **Rigour goes in the statement, not in a remark.** A missing hypothesis is
  added to the lemma in as few words as possible. Do not write a paragraph
  explaining that it was missing.

## Density

- No paragraph over three lines in a definitional passage. Use displays, an
  `array` of cases, or `itemize`. He calls solid prose a wall of text and he is
  right.
- Set the domain inside the definition. Do not define a map and then extend it
  in following prose.
- One motivating sentence maximum before a construction. Not a paragraph on
  why the construction is natural.

## When a passage is rejected twice

Stop editing it. Offer two options in one short message: he dictates the
sentences and I only typeset, or I revert the passage entirely. Do not attempt
a third rewrite in my own register — the register is the problem, and more
attempts produce more to delete.

## Never clobber a file (3 October 2026)

I rewrote `linkedin.txt` six times with `cat > file <<'EOF'`. Robin had edited
it between two of those turns; the heredoc destroyed his edits with no backup,
no git history, and no snapshot to recover from.

- **Once a file has been handed over, it is his.** Every later change is a
  targeted edit — the Edit tool, or read-modify-write. Never `cat >`, `>`,
  `tee`, or any whole-file rewrite on a file that already exists.
- **Re-read before editing.** The copy in my context is stale the moment he
  has seen the file. Read it, then change only the lines concerned.
- **"Undo" is a question, not an instruction.** When the word could mean
  reverting my last edit or dropping one unrequested addition, ask. Guessing
  cost nothing here only because the file was already destroyed.
- **Untracked files have no undo.** Before overwriting anything outside git,
  either `git add` it or keep a copy in the scratchpad.

## Show it on the example, not in general (3 October 2026)

In `sturmian.tex` Robin twice asked why a claim was true, I answered with a
general proof in $\alpha$, $a_1$, $\beta$, $p_m$, and he deleted the whole
section: "I can't understand a word of it."

- **"You haven't shown this" means show it on the running example.** Compute the
  thing for the Fibonacci sequence or for $\sqrt 7$. Do not introduce a general
  parameter to prove a statement about a sequence already printed on the page.
- **Never reintroduce machinery he has deleted.** Once the general case is cut,
  explanations must be built from what survives, even if that means the
  explanation is less complete. Say in chat that it is less complete; do not
  smuggle the algebra back in to fix it.
- **A new symbol per line is the failure signal.** Four displays introducing
  $a_1$, $\beta$, $p_m$, $\ell'_m$ is unreadable regardless of correctness.
- Correctness is not the bar here. Every one of those formulas was verified
  numerically and it made no difference.

## Check instead of asserting (3 October 2026)

Four failures in one session, all the same shape.

- **Measure infrastructure before recommending it.** I twice wrote that a
  lakefile for `lean/` was worth doing. It needs its own Mathlib checkout —
  7.1GB, against 36GB free. One `du -sh` on the borrowed project would have
  settled it. Do that before any recommendation whose cost is a download or a
  build.
- **Verify the prerequisites a plan claims.** Phase 7 was estimated at 150
  lines and ran longer because the plan assumed `lem:blocks` was already
  formalised. It was not. Before estimating a phase, grep for every lemma the
  sketch says is in hand.
- **Promote a target when it becomes the live one.** The converse of
  Morse–Hedlund sat under "Not attempted" with a literature note while every
  other phase had statements, a decomposition and an early failure point.
  "Not attempted" means parked. Once something is the only thing left it needs
  the same treatment as the others, and the heading must stop saying we decided
  against it.
- **Sweep the directory, not the one link.** Asked for the paper behind a
  theorem, I fetched three PDFs and stopped. The book's errata — two pages,
  same directory, free — turned out to be the most informative thing available
  about that chapter's internals, and I had skipped it. List the page or
  directory and take everything adjacent and small.
- **Do not delete a source for looking off-topic.** I downloaded a thesis,
  judged it irrelevant and deleted it. Keeping it costs 250KB; re-finding it
  costs a search. Keep it, and say in the README why it is weak.

## Never let a replace pattern be empty (3 October 2026)

I destroyed `lean/PLAN.md` — 678 lines became 1,552,614 — and committed it.
The edit was a read-modify-write in Python, which obeys the rule above, but:

```python
old = s[s.index("### Step 2 ..."):s.index("### Where the cost is")]
s = s.replace(old, new)
```

The second marker came *before* the first, so the slice was `""`, and
`str.replace("", new)` inserts `new` between every character of the file.

- **Assert the order of slice markers**: `assert ia < ib`. A slice between two
  `index` calls is empty whenever they are the wrong way round, and empty is
  the one pattern that matches everywhere.
- **Assert the pattern is non-trivial** before replacing: `assert len(old) > 200`.
- **Check the line count after any scripted edit**, not just the exit status.
  `wc -l` would have caught this in one second; I found it three commits later
  because a `grep` returned nothing.
- **Prefer `count(old) == 1` and a literal string** over a computed slice.
  Every other edit in this session used a literal anchor and none of them
  failed.
