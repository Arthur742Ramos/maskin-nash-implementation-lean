module

public import Maskin.Defs
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Maskin

open scoped Classical

variable {n : Nat} {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]

def Rule1Cond (F : Profile n A → Set A) (m : (i : Fin n) → CanonMsg n A) : Prop :=
  ∃ (a : A) (P : Profile n A),
    (∀ i : Fin n, (m i).1 = a ∧ (m i).2.1 = P) ∧ a ∈ F P

def Rule2Cond (F : Profile n A → Set A) (m : (i : Fin n) → CanonMsg n A) : Prop :=
  ∃ (j : Fin n) (a : A) (P : Profile n A),
    (∀ i : Fin n, i ≠ j → (m i).1 = a ∧ (m i).2.1 = P) ∧
      ¬ ((m j).1 = a ∧ (m j).2.1 = P) ∧ a ∈ F P

theorem canonOutcome_rule1 (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (a : A) (P : Profile n A)
    (hAgree : ∀ i : Fin n, (m i).1 = a ∧ (m i).2.1 = P)
    (ha : a ∈ F P) (hn : 0 < n) : canonOutcome n A F m = a := by
  classical
  have h1 : Rule1Cond F m := ⟨a, P, hAgree, ha⟩
  unfold Rule1Cond at h1
  unfold canonOutcome
  rw [dite_eq_left h1]
  let i0 : Fin n := ⟨0, hn⟩
  obtain ⟨P0, hAgree0, _⟩ := Classical.choose_spec h1
  exact (hAgree0 i0).1.symm.trans (hAgree i0).1

theorem canonOutcome_rule3 (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A)
    (hNot1 : ¬ Rule1Cond F m) (hNot2 : ¬ Rule2Cond F m) (hn : 0 < n) :
    canonOutcome n A F m =
      (m ⟨(Finset.univ.sum (fun i : Fin n => (m i).2.2.val)) % n,
        Nat.mod_lt _ hn⟩).1 := by
  classical
  unfold Rule1Cond at hNot1
  unfold Rule2Cond at hNot2
  unfold canonOutcome
  rw [dite_eq_right hNot1, dite_eq_right hNot2, dite_eq_left hn]

theorem exists_fin_ne_two (hn : 3 ≤ n) (j j' : Fin n) :
    ∃ i : Fin n, i ≠ j ∧ i ≠ j' := by
  by_cases h0 : 0 ≠ j.val ∧ 0 ≠ j'.val
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · intro h; exact h0.1 (congrArg Fin.val h)
    · intro h; exact h0.2 (congrArg Fin.val h)
  by_cases h1 : 1 ≠ j.val ∧ 1 ≠ j'.val
  · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · intro h; exact h1.1 (congrArg Fin.val h)
    · intro h; exact h1.2 (congrArg Fin.val h)
  simp only [not_and_or, not_not] at h0 h1
  refine ⟨⟨2, by omega⟩, ?_, ?_⟩
  · intro h
    have hv : 2 = j.val := congrArg Fin.val h
    omega
  · intro h
    have hv : 2 = j'.val := congrArg Fin.val h
    omega

omit [Fintype A] [Nonempty A] [DecidableEq A] in
theorem rule2_witness_unique (hn : 3 ≤ n) (_F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (j j' : Fin n)
    (a a' : A) (P P' : Profile n A)
    (hAgree : ∀ i, i ≠ j → (m i).1 = a ∧ (m i).2.1 = P)
    (hDiff : ¬ ((m j).1 = a ∧ (m j).2.1 = P))
    (hAgree' : ∀ i, i ≠ j' → (m i).1 = a' ∧ (m i).2.1 = P')
    (_hDiff' : ¬ ((m j').1 = a' ∧ (m j').2.1 = P')) :
    j = j' ∧ a = a' ∧ P = P' := by
  classical
  obtain ⟨i, hij, hij'⟩ := exists_fin_ne_two hn j j'
  have ha : a = a' := (hAgree i hij).1.symm.trans (hAgree' i hij').1
  have hP : P = P' := (hAgree i hij).2.symm.trans (hAgree' i hij').2
  refine ⟨?_, ha, hP⟩
  by_contra hj
  obtain ⟨hja, hjP⟩ := hAgree' j hj
  exact hDiff ⟨hja.trans ha.symm, hjP.trans hP.symm⟩

theorem canonOutcome_rule2 (hn : 3 ≤ n) (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (j : Fin n) (a : A) (P : Profile n A)
    (hAgree : ∀ i, i ≠ j → (m i).1 = a ∧ (m i).2.1 = P)
    (hDiff : ¬ ((m j).1 = a ∧ (m j).2.1 = P))
    (ha : a ∈ F P)
    (hNot1 : ¬ Rule1Cond F m) :
    canonOutcome n A F m =
      if (m j).1 ∈ lowerContour P j a then (m j).1 else a := by
  classical
  have h2 : Rule2Cond F m := ⟨j, a, P, hAgree, hDiff, ha⟩
  unfold Rule2Cond at h2
  let j0 := Classical.choose h2
  let a0 := Classical.choose (Classical.choose_spec h2)
  let P0 := Classical.choose (Classical.choose_spec (Classical.choose_spec h2))
  have h0 : (∀ i, i ≠ j0 → (m i).1 = a0 ∧ (m i).2.1 = P0) ∧
      ¬ ((m j0).1 = a0 ∧ (m j0).2.1 = P0) ∧ a0 ∈ F P0 :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h2))
  obtain ⟨hj, haEq, hP⟩ :=
    rule2_witness_unique hn F m j0 j a0 a P0 P h0.1 h0.2.1 hAgree hDiff
  unfold Rule1Cond at hNot1
  unfold canonOutcome
  rw [dite_eq_right hNot1, dite_eq_left h2]
  change (if (m j0).1 ∈ lowerContour P0 j0 a0 then (m j0).1 else a0) = _
  rw [hj, haEq, hP]

theorem modulo_winner (n : Nat) (hn : 0 < n) (k : Fin n) (S : Nat) :
    ∃ z : Fin n, (z.val + S) % n = k.val := by
  refine ⟨⟨(k.val + n - S % n) % n, Nat.mod_lt _ hn⟩, ?_⟩
  have hS : S % n < n := Nat.mod_lt _ hn
  change ((k.val + n - S % n) % n + S) % n = k.val
  calc
    ((k.val + n - S % n) % n + S) % n =
        (k.val + n - S % n + S % n) % n := by simp [Nat.add_mod]
    _ = (k.val + n) % n := by congr 1; omega
    _ = k.val := by simp [Nat.mod_eq_of_lt k.isLt]

def weakOrderTied (A : Type) : WeakOrder A :=
  ⟨fun _ _ => True, fun _ => trivial, fun _ _ _ _ _ => trivial,
    fun _ _ => Or.inl trivial⟩

def weakOrderTop {A : Type} (x : A) : WeakOrder A where
  rel a b := a = x ∨ b ≠ x
  refl a := by
    by_cases ha : a = x
    · exact Or.inl ha
    · exact Or.inr ha
  trans a b c hab hbc := by
    rcases hab with ha | hb
    · exact Or.inl ha
    · rcases hbc with hb' | hc
      · exact False.elim (hb hb')
      · exact Or.inr hc
  total a b := by
    by_cases ha : a = x
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inr ha)

omit [Fintype A] [Nonempty A] [DecidableEq A] in
theorem tied_ne_top (x y : A) (hxy : y ≠ x) :
    weakOrderTied A ≠ weakOrderTop x := by
  intro h
  have hrel : (weakOrderTop x).rel y x := by
    rw [← h]
    trivial
  exact hrel.elim hxy (fun hxx => hxx rfl)

theorem spoiler_profile {n : Nat} {A : Type} (x y : A) (hxy : y ≠ x)
    (Q : Fin n → Profile n A) :
    ∃ Pnew : Profile n A, ∀ j : Fin n, Pnew ≠ Q j := by
  classical
  let Pnew : Profile n A := fun i =>
    if Q i i = weakOrderTied A then weakOrderTop x else weakOrderTied A
  refine ⟨Pnew, ?_⟩
  intro j h
  have hj := congrFun h j
  change (if Q j j = weakOrderTied A then weakOrderTop x else weakOrderTied A) =
    Q j j at hj
  by_cases hTied : Q j j = weakOrderTied A
  · rw [ite_eq_left hTied, hTied] at hj
    exact tied_ne_top x y hxy hj.symm
  · rw [ite_eq_right hTied] at hj
    exact hTied hj.symm

end Maskin

end
