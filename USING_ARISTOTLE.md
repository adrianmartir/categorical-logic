# Using Aristotle

[Aristotle](https://aristotle.harmonic.fun) is Harmonic's automated theorem
prover for Lean 4. It runs in the cloud on an uploaded copy of this
repository and returns modified files. The `aristotle` CLI (`aristotlelib`)
and `ARISTOTLE_API_KEY` are provided by the devcontainer.

The lifecycle is **launch → review → continue → cleanup**, and it loops:
most problems take many rounds. Keep **one long-lived Aristotle project per
problem** and drive it with `continue`, so that it accumulates context and
its own prior lemmas across rounds; do not `submit` a fresh project for
each attempt.

Two facts shape everything below:

- **Runs take hours.** Always detach them; never block a session on one.
- **The sandbox has no internet.** Aristotle can only read what is uploaded.
  Any theorem, paper, or definition it needs must be in the repo and
  attached, or it does not exist as far as the run is concerned.

## Launch runs

Set up the workspace first. Each sub-problem gets
`OpenProblemDB/<Set>/Problem<N><a|b>Workspace/` containing:

- `Attempt.lean` — imports the canonical problem file and states the
  prove/disprove pair (`Problem1a_attempt`, `Problem1a_attempt_neg`), each
  `sorry`. This is the only file the run may modify.
- `USEFUL_THEOREMS.md` — precisely-sourced statements of results the problem
  needs that mathlib lacks, plus the source PDFs next to it.
- `RUNS.md` — the run log (format below).

**Build the stub before submitting.** `lake build <module>` must succeed with
only the expected `declaration uses 'sorry'` warnings. Handing Aristotle a
stub that does not compile wastes a multi-hour run.

The prompt should state:

- **Scope:** work only in `<workspace>/Attempt.lean`; do not modify the
  canonical `OpenProblemDB/<Set>/Problem<N>.lean` or any other file.
- **Context:** read `Library/<Set>/Problem<N>.md`, naming the specific
  section, and `USEFUL_THEOREMS.md`. Name the relevant Lean definitions and
  the files they live in.
- **Both directions**, noting that at most one can hold.
- **Explicit permission to fail:** these are open problems. "Do not force a
  proof; if you cannot close either direction, leave the `sorry` and report
  what you tried and where you got stuck." Without this, the run strains for
  a proof; with it, the obstruction write-up it returns instead is often the
  most useful output of the round.

```bash
nohup aristotle submit "$(cat <<'EOF'
<prompt>
EOF
)" --project-dir . --wait --destination "$SCRATCH/problem1a_result.tar.gz" \
  > "$SCRATCH/problem1a_submit.log" 2>&1 &
```

- Run from the repo root with `--project-dir .`. The CLI excludes
  `.lake/packages/mathlib` and build artifacts automatically, so the upload
  is ~1 MB even though the working tree is several GB.
- `nohup … &` is what makes the run survive the session; `--wait` alone dies
  with it.
- Local (`type: path`) dependencies in `lake-manifest.json` are rejected by
  the API.
- Record the project ID from the log in `RUNS.md` immediately — it is the
  handle for every later command, and `aristotle list` only shows names
  Aristotle assigned itself.

## Review runs

`aristotle show <project-id>` gives status and the run's report. Statuses
seen: `QUEUED`, `RUNNING`, `COMPLETE`, `COMPLETE_WITH_ERRORS`, `IDLE`.

**Do not trust the `--destination` tarball written by `--wait`.** The
streaming connection routinely drops (`ERROR - Connection to server was
interrupted`), leaving a tarball saved at submit time that contains the
unmodified input — it looks like a result and is not one. After the run
reports `COMPLETE`, always re-download:

```bash
aristotle download <project-id> --destination "$SCRATCH/result.tar.gz"
```

Archive layout varies between `project_aristotle/` (full tree) and
`output-final_aristotle/` (which also carries `ARISTOTLE_SUMMARY.md`, one
section per run); locate the file rather than assuming a path:

```bash
find "$SCRATCH/extracted" -path "*Workspace*"
```

**Verify independently — the report is a claim, not evidence.** Three checks:

1. Copy the returned file into the repo and `lake build` it locally.
2. `#print axioms <theorem>` for every theorem claimed proved. It must be
   exactly `[propext, Classical.choice, Quot.sound]`; `sorryAx` means it is
   not proved.
3. `git status` / `git diff` to confirm only the workspace was touched.

A green `lake build` is **not** proof that the committed source builds from
clean — it can be replayed from `.olean`s that are stale with respect to an
import change, reporting `Replayed …` for a file that no longer compiles at
all. Before trusting a build as verification of anything import-related, or
before committing, wipe the project's own artifacts and rebuild:

```bash
rm -rf .lake/build/lib/lean/OpenProblemDB .lake/build/ir/OpenProblemDB
lake build OpenProblemDB
```

This removes only this project's artifacts; mathlib's stay cached, so the
rebuild is minutes, not hours.

Reports have been wrong in both directions in practice: one asserted
"everything is committed and pushed" when nothing had been committed, and
one flagged a formalization mismatch with the literature that did not exist
(the two readings were provably equivalent). Treat every mathematical claim
in a report — especially caveats about the problem statement itself — as a
hypothesis to check against primary sources before acting on it. Reading the
returned module docstring is worthwhile even when nothing was proved: the
obstruction analysis is what the next round builds on.

## Continue runs

```bash
aristotle continue <project-id> "<prompt>" --mode instruct \
  --files Library/<Set>/Problem<N>.md \
          OpenProblemDB/<Set>/Problem<N><a|b>Workspace/USEFUL_THEOREMS.md \
          OpenProblemDB/<Set>/Problem<N><a|b>Workspace/<source>.pdf
```

- `--mode instruct` redirects the project or starts new work; `--mode ask`
  asks a question about the most recent task without starting one.
- **`--files` requires the project to be `IDLE`.** Otherwise the CLI fails
  with `Files can only be uploaded when the project is idle`. Check status
  first; if a run is in flight, either wait, send the prompt without
  attachments and describe the change in prose, or — when the in-flight work
  is already superseded — `aristotle cancel <task-id>` it and resend with
  attachments. `aristotle tasks <project-id>` lists task IDs.
- **Attached files land at the sandbox repo root, not at their original
  paths**, and the in-tree copies stay stale until something moves them.
  State in the prompt exactly where each attached file belongs.
- Re-attach `USEFUL_THEOREMS.md` and its PDFs whenever they have changed.
  There is no internet in the sandbox; unattached updates are invisible.
- When retracting an earlier instruction, say so explicitly and tell it to
  ignore the previous framing. It acts on what it was last told, and will
  otherwise keep building on a withdrawn premise.

**Default response to a run that made no progress** (both `sorry`s intact,
no new lemmas): do not immediately re-prompt for another angle. Research the
obstruction the run identified, add verified and precisely-cited statements
to `USEFUL_THEOREMS.md` with source PDFs alongside, then continue with that
material attached. A run blocked on a missing classical theorem stays blocked
until the theorem is supplied.

## Cleanup runs

Cleanup is triggered when a proof exists **and has been independently
verified** (builds locally, axioms clean). It happens *before* results are
pulled into the repo — a verified-but-messy proof is not ready.

Run it as a final `continue` task, since the run knows its own proof best and
can iterate against the compiler, then verify the cleaned result locally the
same way. The bar:

- **Minimal imports** in every new file — import the specific modules used,
  not a blanket `import Mathlib`.
- **Reasonable build time.**
- **No `set_option maxHeartbeats` / `set_option synthInstance.maxHeartbeats`
  bumps.** Permitted only where genuinely unavoidable, and then scoped to the
  single declaration that needs it with a comment explaining why — never
  repeated blanket blocks over an entire file.
- **Clear and concise proofs:** dead ends, superseded lemmas, and duplicated
  commentary removed.

Afterwards:

- Results stay in the workspace. The canonical
  `OpenProblemDB/<Set>/Problem<N>.lean` keeps its `sorry` until the proof is
  signed off for promotion.
- Fold what was learned back into `Library/<Set>/Problem<N>.md` and
  `USEFUL_THEOREMS.md` — as timeless wiki content, per `SPEC.md`.
- Record the outcome in `RUNS.md`.
- Commit everything, including the source PDFs, so a fresh clone can relaunch
  a run with full context.

## `RUNS.md` format

One entry per round, newest last, in each problem workspace:

```markdown
# Aristotle runs

Project: `<project-id>` (`aristotle show <project-id>`)

## <YYYY-MM-DD> — task `<task-id>`

**Prompt:** one line on what the round was asked to do.
**Outcome:** what came back, and whether it was verified locally.
**Obstruction:** what blocked it, if anything.
```
