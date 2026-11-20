import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Establish `hx : 0 < L.sc.x` using `lt_trans one_pos L.sc.one_lt_alt`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X'`. Check the signs of the components of the expression.

Establish `h0 : 0 ≤ L.sc.w'' D.R.n` using `by unfold Scale.w''; positivity`. Establish `h1` using `L.etaSz_pos`. Conclude with `le_trans (by linarith) (le_max_left _ _)`.
-/
theorem wB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ wB L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    positivity
  have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have h1 := L.etaSz_pos
  exact le_trans (by linarith) (le_max_left _ _)

/- English proof (translation)
Use `set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ`. Establish `hρ' : (D.eTau ρ : D.R.GG) = plc g` using `by rw [hρ, Equiv.apply_symm_apply]`. Establish `hj : j.1 + 1 ≤ D.R.m` using `j.2`. Establish `hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ)`. Establish `hj' : j.1 + 1 - 1 < D.R.m` using `by have := j.2; omega`.

Rewrite using `[wj, dif_pos hj']`. Establish `: (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j` using `Fin.ext (by simp)`. Rewrite using `[this]`. Establish `hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces` using `by rw [hρ']; exact hg`. Establish `key : wj D (j.1 + 1) ρ ≤ wB L`.

Distinguish the cases in `h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces`. Take `⟨t, ht', e⟩` from `Finset.mem_image.mp h2`. Establish `a` using `(L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2`. Establish `b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ)` using `le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩`. Conclude with `le_trans (by linarith) (le_max_right _ _)`.

Establish `a` using `(L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2`. Conclude with `le_trans a (le_max_left _ _)`. Rewrite `key` using `[hw]`. Establish `he : (hcAt D g).e j = (D.hc ρ).e j` using `rfl`. Rewrite using `[he]`.

Break down `le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h` into its components or cases. Rewrite using `[show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by`. Conclude with `Int.toNat_of_nonneg h]` after adjusting the coercions. Use `Int.floor_le ((D.hc ρ).e j)` as an intermediate fact. Establish `: (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ)` using `by exact_mod_cast this`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Int.toNat_eq_zero.2 h.le]`. Simplify using `using wB_nonneg L`.
-/
theorem floor_size_le_wB {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hg : ¬ Thick D.host g) :
    ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) ≤ wB L := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρ' : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρ']; exact hg
  have key : wj D (j.1 + 1) ρ ≤ wB L := by
    by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
      have a := (L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2
      have b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ) :=
        le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩
      exact le_trans (by linarith) (le_max_right _ _)
    · have a := (L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2
      exact le_trans a (le_max_left _ _)
  rw [hw] at key
  have he : (hcAt D g).e j = (D.hc ρ).e j := rfl
  rw [he]
  rcases le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h
  · rw [show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h]
    have := Int.floor_le ((D.hc ρ).e j)
    have : (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    simpa using wB_nonneg L

/- English proof (translation)
Introduce `D L`. Establish `hB` using `wB_nonneg L`. Establish `h1 : wMax D ≤ ⌊wB L⌋₊`. Apply `csSup_le'` to reduce the goal to its premises. Introduce and unpack `s ⟨g, j, hg, rfl⟩`.

Conclude with `Nat.le_floor (floor_size_le_wB L g j hg)`. Establish `h2 : (wMax D : ℝ) ≤ wB L` using `le_trans (by exact_mod_cast h1) (Nat.floor_le hB)`. Use `⟨h2, ?_⟩` and prove the remaining obligations. Establish `h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2`. Use `Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Unfold `wHat wP`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wMax_le_wB : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  intro D L
  have hB := wB_nonneg L
  have h1 : wMax D ≤ ⌊wB L⌋₊ := by
    apply csSup_le'
    rintro s ⟨g, j, hg, rfl⟩
    exact Nat.le_floor (floor_size_le_wB L g j hg)
  have h2 : (wMax D : ℝ) ≤ wB L :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le hB)
  refine ⟨h2, ?_⟩
  have h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)
    push_cast at this
    exact this
  unfold wHat wP
  push_cast
  linarith

end GlobalTheory.HTW.Rec
