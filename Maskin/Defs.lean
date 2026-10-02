import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Function.Basic

namespace Maskin

structure WeakOrder (A : Type) where
  rel : A → A → Prop
  refl : ∀ a, rel a a
  trans : ∀ a b c, rel a b → rel b c → rel a c
  total : ∀ a b, rel a b ∨ rel b a

abbrev Profile (n : Nat) (A : Type) := Fin n → WeakOrder A

variable {n : Nat} {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]

def lowerContour (P : Profile n A) (i : Fin n) (a : A) : Set A :=
  {b | (P i).rel a b}

def MaskinMonotone (F : Profile n A → Set A) : Prop :=
  ∀ (P P_ : Profile n A) (a : A), a ∈ F P →
    (∀ (i : Fin n) (b : A), (P i).rel a b → (P_ i).rel a b) → a ∈ F P_

def NoVetoPower (n : Nat) (F : Profile n A → Set A) : Prop := by
  classical
  exact ∀ (P : Profile n A) (a : A),
    n - 1 ≤ (Finset.univ.filter (fun i => ∀ b : A, (P i).rel a b)).card → a ∈ F P

abbrev CanonMsg (n : Nat) (A : Type) := A × Profile n A × Fin n

/-- The rule predicates and equality of announced profiles use local classical
decidability. Selecting existential witnesses makes the outcome noncomputable.
Agreement concerns the alternative and profile; integers may differ.
For `n = 0`, Rule 3 uses an arbitrary alternative because `Fin 0` is empty. -/
noncomputable def canonOutcome (n : Nat) (A : Type)
    [Fintype A] [Nonempty A] [DecidableEq A] (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) : A := by
  classical
  exact
    if h₁ : ∃ (a : A) (P : Profile n A),
        (∀ i : Fin n, (m i).1 = a ∧ (m i).2.1 = P) ∧ a ∈ F P then
      Classical.choose h₁
    else if h₂ : ∃ (j : Fin n) (a : A) (P : Profile n A),
        (∀ i : Fin n, i ≠ j → (m i).1 = a ∧ (m i).2.1 = P) ∧
          ¬ ((m j).1 = a ∧ (m j).2.1 = P) ∧ a ∈ F P then
      let j := Classical.choose h₂
      let a := Classical.choose (Classical.choose_spec h₂)
      let P := Classical.choose (Classical.choose_spec (Classical.choose_spec h₂))
      if (m j).1 ∈ lowerContour P j a then (m j).1 else a
    else if hn : 0 < n then
      let j : Fin n :=
        ⟨(Finset.univ.sum (fun i : Fin n => (m i).2.2.val)) % n, Nat.mod_lt _ hn⟩
      (m j).1
    else
      Classical.choice (inferInstance : Nonempty A)

variable {Msg : (i : Fin n) → Type}

def attainable (out : ((i : Fin n) → Msg i) → A)
    (m : (i : Fin n) → Msg i) (i : Fin n) : Set A :=
  {a | ∃ m_ : Msg i, out (Function.update m i m_) = a}

def IsNashEq (P : Profile n A) (out : ((i : Fin n) → Msg i) → A)
    (m : (i : Fin n) → Msg i) : Prop :=
  ∀ i : Fin n, attainable out m i ⊆ lowerContour P i (out m)

def NashImplements (F : Profile n A → Set A) (Msg : (i : Fin n) → Type)
    (out : ((i : Fin n) → Msg i) → A) : Prop :=
  ∀ P : Profile n A, {a : A | ∃ m, IsNashEq P out m ∧ out m = a} = F P

theorem maskin_necessity (F : Profile n A → Set A)
    (hF : ∀ P, (F P).Nonempty) (Msg : (i : Fin n) → Type)
    (out : ((i : Fin n) → Msg i) → A) :
    NashImplements F Msg out → MaskinMonotone F := by
  intro h P P_ a ha hmono
  rw [← h P] at ha
  rcases ha with ⟨m, hEq, hm⟩
  rw [← h P_]
  refine ⟨m, ?_, hm⟩
  intro i b hb
  change (P_ i).rel (out m) b
  rw [hm]
  apply hmono i b
  have hrel : (P i).rel (out m) b := hEq i hb
  rwa [hm] at hrel

theorem maskin_sufficiency (hn : 3 ≤ n) (F : Profile n A → Set A)
    (hF : ∀ P, (F P).Nonempty) :
    MaskinMonotone F → NoVetoPower n F →
      ∃ (Msg : (i : Fin n) → Type) (out : ((i : Fin n) → Msg i) → A),
        NashImplements F Msg out := by
  sorry

end Maskin
