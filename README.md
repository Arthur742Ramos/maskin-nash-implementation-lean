# Maskin's Nash Implementation Theorem in Lean 4

This Lean 4 / Mathlib development proves that pure-strategy Nash
implementation implies Maskin monotonicity, and that Maskin monotonicity
plus no-veto power implies Nash implementation with at least three agents.
The sufficiency proof constructs the canonical mechanism.

The formal model has a finite nonempty set of alternatives `A`, a finite
set of agents `Fin n`, and weak-order (complete preorder) preferences.
`WeakOrder` requires a reflexive, transitive, total relation; `(P i).rel a b`
means agent `i` weakly prefers `a` to `b`. The social choice correspondence
`F` is nonempty-valued, as required by `hF : ∀ P, (F P).Nonempty`.
`NashImplements` equates `F P` with exactly the outcomes of pure-strategy
Nash equilibria at every preference profile `P`.

The theorem statements below are copied from the completed library, under
these instance assumptions:

```lean
variable {n : Nat} {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
```

```lean
theorem maskin_necessity (F : Profile n A → Set A)
    (hF : ∀ P, (F P).Nonempty) (Msg : (i : Fin n) → Type)
    (out : ((i : Fin n) → Msg i) → A) :
    NashImplements F Msg out → MaskinMonotone F

theorem maskin_sufficiency (hn : 3 ≤ n) (F : Profile n A → Set A)
    (hF : ∀ P, (F P).Nonempty) :
    MaskinMonotone F → NoVetoPower n F →
      ∃ (Msg : (i : Fin n) → Type) (out : ((i : Fin n) → Msg i) → A),
        NashImplements F Msg out
```

Necessity has no lower bound on the number of agents. Sufficiency requires
`3 ≤ n`. Its existential contract is proved by choosing
`Msg := fun _ => CanonMsg n A` and `out := canonOutcome n A F`.

In the canonical mechanism, each message announces an alternative, a
preference profile, and an element of `Fin n`. Rule 1 selects an admissible
alternative under unanimous announcements of the alternative and profile.
Rule 2 handles one dissenting agent and requires the common announced
alternative to satisfy `a ∈ F P`. This admissibility condition is
load-bearing: it appears both in the outcome definition and in
`Rule2Cond`, and is used in the sufficiency argument. Under Rule 2 the
dissenter's announced alternative is selected if it belongs to the
announced lower contour; otherwise the common alternative is selected.
Rule 3 uses a modulo game: for positive `n`, the sum of the announced
`Fin n` values modulo `n` chooses the agent whose alternative is selected.
For `n = 0`, the outcome definition chooses an arbitrary alternative;
this case is outside the sufficiency hypothesis.

The proofs were developed with AI assistance and mechanically checked.
The completed library builds with zero proof placeholders, and both
capstone theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound` (see `evidence/final-axioms.log`). No independent human review
of the proofs was performed. The official `lake comparator` accepts the
packaged solution: "Your solution is okay!"

The package contains:

- `Maskin/Defs.lean`: the model, canonical outcome, and necessity proof.
- `Maskin/Helpers.lean` and `Maskin/Sufficiency.lean`: canonical-mechanism
  lemmas and the sufficiency proof; `Maskin.lean` imports the library.
- `Challenge.lean`: the exact library definition bodies and two selected
  theorem statements with deliberate proof holes. `WeakOrder` is a
  structure and is excluded from comparator `definition_names`; `Profile`
  and `CanonMsg` are abbreviations counted among the nine genuine definitions.
- `Solution.lean`: imports the complete library independently of Challenge.
- `scripts/make_challenge.py`: reproduces Challenge from the final sources.
- `scripts/verify.sh`: builds all three targets and checks the library,
  regeneration, package shape, selected names and declaration kinds, and metadata.
- `scripts/check_package.py`: checks package shape and, when present,
  `evidence/final-axioms.log`; it compares current hashes with
  `evidence/verification-manifest.json`. Its `--record` option creates a
  source manifest after validation. A source manifest alone is not proof
  that the recorded verification kernels were run.
- `formalization.yaml` and `CITATION.cff`: registry and citation metadata.

The pinned toolchain is `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. After preparing verification
evidence and a source manifest for the exact validated sources, run:

```bash
./scripts/verify.sh
```

The Palomar registry search performed on 2026-10-02 (405 results,
326 projects, revision 114) found no existing Maskin implementation
entries. This statement concerns only that dated registry search.

Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.

License: BSD-3-Clause; see `LICENSE`.
