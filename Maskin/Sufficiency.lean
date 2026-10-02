import Maskin.Helpers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Maskin

variable {n : Nat} {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]

/-- A deviation from admissible consensus attains every lower-contour alternative. -/
theorem rule1_deviation_attain (hn : 3 ≤ n) (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (a0 : A) (P0 : Profile n A)
    (hAgree : ∀ i, (m i).1 = a0 ∧ (m i).2.1 = P0) (ha0 : a0 ∈ F P0)
    (j : Fin n) (b : A) (hb : b ∈ lowerContour P0 j a0) :
    b ∈ attainable (canonOutcome n A F) m j := by
  classical
  let z0 : Fin n := ⟨0, by omega⟩
  let v : CanonMsg n A := (b, P0, z0)
  let md := Function.update m j v
  refine ⟨v, ?_⟩
  change canonOutcome n A F md = b
  by_cases hba : b = a0
  · subst b
    apply canonOutcome_rule1 F md a0 P0 _ ha0 (by omega)
    intro i
    by_cases hij : i = j
    · subst i
      simp [md, v]
    · simpa [md, Function.update_of_ne hij] using hAgree i
  · have hAgr : ∀ i, i ≠ j → (md i).1 = a0 ∧ (md i).2.1 = P0 := by
      intro i hij
      simpa [md, Function.update_of_ne hij] using hAgree i
    have hDiff : ¬ ((md j).1 = a0 ∧ (md j).2.1 = P0) := by
      simpa [md, v] using hba
    have hNot1 : ¬ Rule1Cond F md := by
      rintro ⟨a1, P1, hAgr1, _⟩
      obtain ⟨k, hkj, _⟩ := exists_fin_ne_two hn j j
      have ej : b = a1 := by simpa [md, v] using (hAgr1 j).1
      have ek : (m k).1 = a1 := by
        simpa [md, Function.update_of_ne hkj] using (hAgr1 k).1
      exact hba (ej.trans (ek.symm.trans (hAgree k).1))
    rw [canonOutcome_rule2 hn F md j a0 P0 hAgr hDiff ha0 hNot1]
    simp [md, v, hb]

/-- In the modulo rule, an agent can choose an integer making itself the winner. -/
private theorem modulo_deviation_outcome (hn : 0 < n) (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (j : Fin n) (b : A) (Pnew : Profile n A)
    (z : Fin n)
    (hz : (z.val + (Finset.univ.erase j).sum (fun k => (m k).2.2.val)) % n = j.val)
    (hNot1 : ¬ Rule1Cond F (Function.update m j (b, Pnew, z)))
    (hNot2 : ¬ Rule2Cond F (Function.update m j (b, Pnew, z))) :
    canonOutcome n A F (Function.update m j (b, Pnew, z)) = b := by
  classical
  let md := Function.update m j (b, Pnew, z)
  have hS : (Finset.univ.sum (fun k : Fin n => (md k).2.2.val)) =
      z.val + (Finset.univ.erase j).sum (fun k => (m k).2.2.val) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp [md]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [md, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hw : (⟨(Finset.univ.sum (fun k : Fin n => (md k).2.2.val)) % n,
      Nat.mod_lt _ hn⟩ : Fin n) = j := by
    apply Fin.ext
    change (Finset.univ.sum (fun k : Fin n => (md k).2.2.val)) % n = j.val
    rw [hS]
    exact hz
  rw [canonOutcome_rule3 F md hNot1 hNot2 hn, hw]
  simp [md]

/-- All agents other than the dissenter rank a Rule 2 equilibrium outcome top. -/
theorem rule2_eq_toprank (hn : 3 ≤ n) (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A) (j0 : Fin n) (a : A) (P0 : Profile n A)
    (hAgree : ∀ i, i ≠ j0 → (m i).1 = a ∧ (m i).2.1 = P0)
    (hDiff : ¬ ((m j0).1 = a ∧ (m j0).2.1 = P0))
    (P : Profile n A) (hNash : IsNashEq P (canonOutcome n A F) m)
    (o : A) (ho : canonOutcome n A F m = o)
    (i : Fin n) (hi : i ≠ j0) (b : A) : (P i).rel o b := by
  classical
  by_cases hNT : ∃ x y : A, x ≠ y
  · obtain ⟨x, y, hxy⟩ := hNT
    obtain ⟨Pnew, hPnew⟩ := spoiler_profile x y hxy.symm (fun k => (m k).2.1)
    let T := (Finset.univ.erase i).sum (fun k => (m k).2.2.val)
    obtain ⟨z, hz⟩ := modulo_winner n (by omega) i T
    let v : CanonMsg n A := (b, Pnew, z)
    let md := Function.update m i v
    have hNot1 : ¬ Rule1Cond F md := by
      rintro ⟨a1, P1, hAgr, _⟩
      obtain ⟨k, hki, _⟩ := exists_fin_ne_two hn i j0
      have ek : (m k).2.1 = P1 := by
        simpa [md, Function.update_of_ne hki] using (hAgr k).2
      have ei : Pnew = P1 := by simpa [md, v] using (hAgr i).2
      exact hPnew k (ei.trans ek.symm)
    have hNot2 : ¬ Rule2Cond F md := by
      rintro ⟨j1, a1, P1, hAgr, _, _⟩
      by_cases hj1i : j1 = i
      · subst j1
        obtain ⟨k, hki, hkj⟩ := exists_fin_ne_two hn i j0
        have ek : (m k).1 = a1 ∧ (m k).2.1 = P1 := by
          simpa [md, Function.update_of_ne hki] using hAgr k hki
        have ej : (m j0).1 = a1 ∧ (m j0).2.1 = P1 := by
          simpa [md, Function.update_of_ne hi.symm] using hAgr j0 hi.symm
        have ha1 : a1 = a := ek.1.symm.trans (hAgree k hkj).1
        have hP1 : P1 = P0 := ek.2.symm.trans (hAgree k hkj).2
        exact hDiff ⟨ej.1.trans ha1, ej.2.trans hP1⟩
      · have ei : Pnew = P1 := by
          simpa [md, v] using (hAgr i (Ne.symm hj1i)).2
        by_cases hj1j : j1 = j0
        · subst j1
          obtain ⟨k, hki, hkj⟩ := exists_fin_ne_two hn i j0
          have ek : (m k).2.1 = P1 := by
            simpa [md, Function.update_of_ne hki] using (hAgr k hkj).2
          exact hPnew k (ei.trans ek.symm)
        · have ej : (m j0).2.1 = P1 := by
            simpa [md, Function.update_of_ne hi.symm] using (hAgr j0 (Ne.symm hj1j)).2
          exact hPnew j0 (ei.trans ej.symm)
    have hout : canonOutcome n A F md = b :=
      modulo_deviation_outcome (by omega) F m i b Pnew z hz hNot1 hNot2
    have hmem := hNash i (show b ∈ attainable (canonOutcome n A F) m i from ⟨v, hout⟩)
    change (P i).rel (canonOutcome n A F m) b at hmem
    rwa [ho] at hmem
  · have hbo : b = o := by
      by_contra hne
      exact hNT ⟨b, o, hne⟩
    rw [hbo]
    exact (P i).refl o

/-- Every agent ranks a Rule 3 equilibrium outcome top. -/
theorem rule3_eq_toprank (hn : 3 ≤ n) (F : Profile n A → Set A)
    (m : (i : Fin n) → CanonMsg n A)
    (hNot1 : ¬ Rule1Cond F m) (hNot2 : ¬ Rule2Cond F m)
    (P : Profile n A) (hNash : IsNashEq P (canonOutcome n A F) m)
    (o : A) (ho : canonOutcome n A F m = o)
    (j : Fin n) (b : A) : (P j).rel o b := by
  classical
  by_cases hNT : ∃ x y : A, x ≠ y
  · obtain ⟨x, y, hxy⟩ := hNT
    obtain ⟨Pnew, hPnew⟩ := spoiler_profile x y hxy.symm (fun k => (m k).2.1)
    let T := (Finset.univ.erase j).sum (fun k => (m k).2.2.val)
    obtain ⟨z, hz⟩ := modulo_winner n (by omega) j T
    let v : CanonMsg n A := (b, Pnew, z)
    let md := Function.update m j v
    have hNot1d : ¬ Rule1Cond F md := by
      rintro ⟨a1, P1, hAgr, _⟩
      obtain ⟨l, hlj, _⟩ := exists_fin_ne_two hn j j
      have el : (m l).2.1 = P1 := by
        simpa [md, Function.update_of_ne hlj] using (hAgr l).2
      have ej : Pnew = P1 := by simpa [md, v] using (hAgr j).2
      exact hPnew l (ej.trans el.symm)
    have hNot2d : ¬ Rule2Cond F md := by
      rintro ⟨j1, a1, P1, hAgr, _, hMem⟩
      by_cases hj1 : j1 = j
      · subst j1
        have hAgrm : ∀ k, k ≠ j → (m k).1 = a1 ∧ (m k).2.1 = P1 := by
          intro k hk
          simpa [md, Function.update_of_ne hk] using hAgr k hk
        by_cases hdm : (m j).1 = a1 ∧ (m j).2.1 = P1
        · apply hNot1
          refine ⟨a1, P1, ?_, hMem⟩
          intro k
          by_cases hk : k = j
          · subst k
            exact hdm
          · exact hAgrm k hk
        · exact hNot2 ⟨j, a1, P1, hAgrm, hdm, hMem⟩
      · have ej : Pnew = P1 := by
          simpa [md, v] using (hAgr j (Ne.symm hj1)).2
        obtain ⟨l, hlj1, hlj⟩ := exists_fin_ne_two hn j1 j
        have el : (m l).2.1 = P1 := by
          simpa [md, Function.update_of_ne hlj] using (hAgr l hlj1).2
        exact hPnew l (ej.trans el.symm)
    have hout : canonOutcome n A F md = b :=
      modulo_deviation_outcome (by omega) F m j b Pnew z hz hNot1d hNot2d
    have hmem := hNash j (show b ∈ attainable (canonOutcome n A F) m j from ⟨v, hout⟩)
    change (P j).rel (canonOutcome n A F m) b at hmem
    rwa [ho] at hmem
  · have hbo : b = o := by
      by_contra hne
      exact hNT ⟨b, o, hne⟩
    rw [hbo]
    exact (P j).refl o

/-- The canonical mechanism Nash-implements a monotone correspondence with no veto. -/
theorem maskin_sufficiency (hn : 3 ≤ n) (F : Profile n A → Set A)
    (hF : ∀ P, (F P).Nonempty) :
    MaskinMonotone F → NoVetoPower n F →
      ∃ (Msg : (i : Fin n) → Type) (out : ((i : Fin n) → Msg i) → A),
        NashImplements F Msg out := by
  classical
  intro hMono hNVP
  refine ⟨fun _ => CanonMsg n A, canonOutcome n A F, ?_⟩
  intro P
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨m, hNash, rfl⟩ := ha
    by_cases h1 : Rule1Cond F m
    · obtain ⟨a0, P0, hAgr, ha0⟩ := h1
      have hout := canonOutcome_rule1 F m a0 P0 hAgr ha0 (by omega)
      rw [hout]
      apply hMono P0 P a0 ha0
      intro j b hb
      have hmem := hNash j (rule1_deviation_attain hn F m a0 P0 hAgr ha0 j b hb)
      change (P j).rel (canonOutcome n A F m) b at hmem
      rwa [hout] at hmem
    · by_cases h2 : Rule2Cond F m
      · obtain ⟨j0, a0, P0, hAgr, hDiff, _⟩ := h2
        have htop : ∀ i : Fin n, i ≠ j0 → ∀ b : A, (P i).rel (canonOutcome n A F m) b :=
          fun i hi b => rule2_eq_toprank hn F m j0 a0 P0 hAgr hDiff P hNash _ rfl i hi b
        apply hNVP P (canonOutcome n A F m)
        have hcard : (Finset.univ.erase j0).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
        have hsub : Finset.univ.erase j0 ⊆ Finset.univ.filter
            (fun i => ∀ b : A, (P i).rel (canonOutcome n A F m) b) := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, htop i (Finset.ne_of_mem_erase hi)⟩
        calc
          n - 1 = (Finset.univ.erase j0).card := hcard.symm
          _ ≤ _ := Finset.card_le_card hsub
      · have htop : ∀ j : Fin n, ∀ b : A, (P j).rel (canonOutcome n A F m) b :=
          fun j b => rule3_eq_toprank hn F m h1 h2 P hNash _ rfl j b
        apply hNVP P (canonOutcome n A F m)
        have hsub : Finset.univ ⊆ Finset.univ.filter
            (fun i => ∀ b : A, (P i).rel (canonOutcome n A F m) b) := by
          intro i _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, htop i⟩
        calc
          n - 1 ≤ n := Nat.sub_le n 1
          _ = (Finset.univ : Finset (Fin n)).card := by rw [Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
  · intro a ha
    let c : Fin n := ⟨0, by omega⟩
    let mc : (i : Fin n) → CanonMsg n A := fun _ => (a, P, c)
    have hcons : canonOutcome n A F mc = a :=
      canonOutcome_rule1 F mc a P (fun _ => ⟨rfl, rfl⟩) ha (by omega)
    refine ⟨mc, ?_, hcons⟩
    intro j b hb
    obtain ⟨v, hv⟩ := hb
    rw [hcons]
    change (P j).rel a b
    let md := Function.update mc j v
    change canonOutcome n A F md = b at hv
    by_cases hvv : v.1 = a ∧ v.2.1 = P
    · have hAgr : ∀ i, (md i).1 = a ∧ (md i).2.1 = P := by
        intro i
        by_cases hij : i = j
        · subst i
          simpa [md] using hvv
        · simp [md, mc, Function.update_of_ne hij]
      have hout := canonOutcome_rule1 F md a P hAgr ha (by omega)
      have hba : b = a := hv.symm.trans hout
      rw [hba]
      exact (P j).refl a
    · have hAgr : ∀ i, i ≠ j → (md i).1 = a ∧ (md i).2.1 = P := by
        intro i hij
        simp [md, mc, Function.update_of_ne hij]
      have hDiff : ¬ ((md j).1 = a ∧ (md j).2.1 = P) := by
        simpa [md] using hvv
      have hNot1 : ¬ Rule1Cond F md := by
        rintro ⟨a1, P1, hAgr1, _⟩
        obtain ⟨k, hkj, _⟩ := exists_fin_ne_two hn j j
        have ek : a = a1 ∧ P = P1 := by
          simpa [md, mc, Function.update_of_ne hkj] using hAgr1 k
        have ej : v.1 = a1 ∧ v.2.1 = P1 := by simpa [md] using hAgr1 j
        exact hvv ⟨ej.1.trans ek.1.symm, ej.2.trans ek.2.symm⟩
      rw [canonOutcome_rule2 hn F md j a P hAgr hDiff ha hNot1] at hv
      by_cases hmem : (md j).1 ∈ lowerContour P j a
      · rw [ite_eq_left hmem] at hv
        rw [← hv]
        exact hmem
      · rw [ite_eq_right hmem] at hv
        rw [← hv]
        exact (P j).refl a

end Maskin
