import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSm

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Establish `hg : D.what₂.places.resChar w ∈ L.gTypes`. Rewrite using `[hwi]`. Unfold `SizeData₂.gTypes`. Apply the tactic sequence `fin_cases i <;> simp`. Establish `hFj : ∀ j ∈ SizeData₂.lifts D, L.F j w = FTypeG D j`.

Introduce `j hj`. Rewrite using `[hF j hj w]`. Conclude with `if_pos hg`. Establish `hEj : ∀ j ∈ SizeData₂.lifts D, L.E u j w = vDG D u w + EatG L Xe ce i u j w`. Introduce `j hj`.

Rewrite using `[hE.edef u j hj w]`. Unfold `Eval vDG`. Simplify using `only`. Rewrite using `[if_neg hw]`. Use `fin_cases i`.

Establish `h0 : D.what₂.places.resChar w = D.host.g 0` using `hwi`. Rewrite using `[if_pos h0]`. Both sides reduce to the same expression. Establish `h1 : D.what₂.places.resChar w = D.host.g 1` using `hwi`. Rewrite using `[if_neg (by rw [h1]; exact D.host.g_ne.symm), if_pos h1]`.

Both sides reduce to the same expression. Establish `hvD : 0 ≤ vDG D u w` using `Nat.cast_nonneg _`. Use `set A : ℝ := (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) with hA`. Use `set B : ℝ := (D.R.f : ℝ) * (Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz) with hB`. Establish `hη` using `L.etaSz_pos.le`.

Establish `hN0 : 0 ≤ Nm D` using `by unfold Nm; positivity`. Establish `ht : (D.R.t : ℝ) ≤ Nm D`. Establish `h1 : D.R.t + 1 ≤ D.R.m * (D.R.t + 1)` using `Nat.le_mul_of_pos_left _ (by have := D.R.two_le_m; omega)`. Establish `h2 : D.R.t ≤ D.R.N D.R.m` using `by unfold Ranks.N; omega`. Unfold `Nm`.

Conclude with `h2` after adjusting the coercions. Establish `hA0 : 0 ≤ A` using `mul_nonneg (Nat.cast_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hη))`. Establish `hBA : B ≤ 2 * A`. Establish `h3 : Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz ≤ 2 * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left ht hN0, mul_nonneg (sq_nonneg (D.R.m : ℝ)) hη]`.

Establish `h4` using `mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ (D.R.f : ℝ))`. Rewrite using `[hA, hB]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m`. Unfold `SizeData₂.lifts`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) = -(∑ j ∈ SizeData₂.lifts D, vNN Xe i u j w) - (D.R.m : ℝ) * (ce.g * A) - (D.R.m : ℝ) * vDG D u w`. Establish `: ∀ j ∈ SizeData₂.lifts D, L.F j w - L.E u j w = -vNN Xe i u j w - (ce.g * A + vDG D u w)`. Introduce `j hj`. Rewrite using `[hFj j hj, hEj j hj]`.

Unfold `EatG`. Rewrite using `[hA]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, hcard]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hEr : Formalism.MainNotions.LiftErrorLocal.errC D L = (D.R.m : ℝ) * B`. Unfold `Formalism.MainNotions.LiftErrorLocal.errC`. Rewrite using `[hB]`. Unfold `Nm`. Expand and normalize the polynomial expressions, which then agree.

Establish `hl : Formalism.MainNotions.LiftErrorLocal.lifts D = SizeData₂.lifts D` using `rfl`. Rewrite using `[hEr, hl, hsum]`. Establish `hm0 : (0 : ℝ) ≤ (D.R.m : ℝ)` using `Nat.cast_nonneg _`. Establish `h1 : C1 * ((D.R.m : ℝ) * B) ≤ (D.R.m : ℝ) * (ce.g * A)`. Establish `h5 : C1 * ((D.R.m : ℝ) * B) ≤ C1 * ((D.R.m : ℝ) * (2 * A))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBA hm0) hC1`.

Establish `h6 : (2 * C1) * ((D.R.m : ℝ) * A) ≤ ce.g * ((D.R.m : ℝ) * A)` using `mul_le_mul_of_nonneg_right hC (mul_nonneg hm0 hA0)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : 0 ≤ (D.R.m : ℝ) * vDG D u w` using `mul_nonneg hm0 hvD`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sumFE_atG_le {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (i : Fin 2) (w : D.what₂.places.Pl)
    (hwi : D.what₂.places.resChar w = D.host.g i) (u : D.what₂.Word) (hw : D.what₂.places.resChar w ≠ (D.mem u).A.T) :
    ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) ≤
      -(∑ j ∈ Formalism.MainNotions.LiftErrorLocal.lifts D, vNN Xe i u j w) - C1 * Formalism.MainNotions.LiftErrorLocal.errC D L := by
  have hg : D.what₂.places.resChar w ∈ L.gTypes := by
    rw [hwi]
    unfold SizeData₂.gTypes
    fin_cases i <;> simp
  have hFj : ∀ j ∈ SizeData₂.lifts D, L.F j w = FTypeG D j := by
    intro j hj
    rw [hF j hj w]
    exact if_pos hg
  have hEj : ∀ j ∈ SizeData₂.lifts D, L.E u j w = vDG D u w + EatG L Xe ce i u j w := by
    intro j hj
    rw [hE.edef u j hj w]
    unfold Eval vDG
    dsimp only
    rw [if_neg hw]
    fin_cases i
    · have h0 : D.what₂.places.resChar w = D.host.g 0 := hwi
      rw [if_pos h0]
      rfl
    · have h1 : D.what₂.places.resChar w = D.host.g 1 := hwi
      rw [if_neg (by rw [h1]; exact D.host.g_ne.symm), if_pos h1]
      rfl
  have hvD : 0 ≤ vDG D u w := Nat.cast_nonneg _
  set A : ℝ := (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) with hA
  set B : ℝ := (D.R.f : ℝ) * (Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz) with hB
  have hη := L.etaSz_pos.le
  have hN0 : 0 ≤ Nm D := by unfold Nm; positivity
  have ht : (D.R.t : ℝ) ≤ Nm D := by
    have h1 : D.R.t + 1 ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_left _ (by have := D.R.two_le_m; omega)
    have h2 : D.R.t ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    unfold Nm
    exact_mod_cast h2
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hη))
  have hBA : B ≤ 2 * A := by
    have h3 : Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz ≤ 2 * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := by
      nlinarith [mul_le_mul_of_nonneg_left ht hN0, mul_nonneg (sq_nonneg (D.R.m : ℝ)) hη]
    have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ (D.R.f : ℝ))
    rw [hA, hB]
    linarith
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
    unfold SizeData₂.lifts
    simp
  have hsum : ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) =
      -(∑ j ∈ SizeData₂.lifts D, vNN Xe i u j w) - (D.R.m : ℝ) * (ce.g * A) - (D.R.m : ℝ) * vDG D u w := by
    have : ∀ j ∈ SizeData₂.lifts D, L.F j w - L.E u j w = -vNN Xe i u j w - (ce.g * A + vDG D u w) := by
      intro j hj
      rw [hFj j hj, hEj j hj]
      unfold EatG
      rw [hA]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul,
      hcard]
    ring
  have hEr : Formalism.MainNotions.LiftErrorLocal.errC D L = (D.R.m : ℝ) * B := by
    unfold Formalism.MainNotions.LiftErrorLocal.errC
    rw [hB]
    unfold Nm
    ring
  have hl : Formalism.MainNotions.LiftErrorLocal.lifts D = SizeData₂.lifts D := rfl
  rw [hEr, hl, hsum]
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have h1 : C1 * ((D.R.m : ℝ) * B) ≤ (D.R.m : ℝ) * (ce.g * A) := by
    have h5 : C1 * ((D.R.m : ℝ) * B) ≤ C1 * ((D.R.m : ℝ) * (2 * A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBA hm0) hC1
    have h6 : (2 * C1) * ((D.R.m : ℝ) * A) ≤ ce.g * ((D.R.m : ℝ) * A) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hm0 hA0)
    nlinarith
  have h2 : 0 ≤ (D.R.m : ℝ) * vDG D u w := mul_nonneg hm0 hvD
  linarith

/- English proof (translation)
Introduce `u w hw hgm φ hφ F hF1 _`. Choose the witnesses or unpack the hypotheses as in `⟨i, hwi⟩ : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by`. Break down `Finset.mem_insert.1 hgm with h0 | h1` into its components or cases. Conclude with `⟨0, h0⟩`. Conclude with `⟨1, Finset.mem_singleton.1 h1⟩`.

Take `⟨y, hy, hv⟩` from `h.1 i w hwi u hw (D.what₂.muAt w) φ hφ F hF1`. Use `⟨y, hy, hv.imp id fun hv => ?_⟩` and prove the remaining obligations. Establish `he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ)` using `by exact_mod_cast D.what₂.places.ramIdx_pos w`. Establish `h3` using `le_trans (sumFE_atG_le hF hE hC1 hC i w hwi u hw) hv`. Unfold `Formalism.MainNotions.LiftErrorLocal.vG at h3`.

Unfold `ur`. Rewrite `h3` using `[le_div_iff₀ he]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem noGainBound_of_local {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 C2 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (h : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) :
    NoGainBoundAtTypePrimes D L := by
  intro u w hw hgm φ hφ F hF1 _
  obtain ⟨i, hwi⟩ : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
    rcases Finset.mem_insert.1 hgm with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, Finset.mem_singleton.1 h1⟩
  obtain ⟨y, hy, hv⟩ := h.1 i w hwi u hw (D.what₂.muAt w) φ hφ F hF1
  refine ⟨y, hy, hv.imp id fun hv => ?_⟩
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h3 := le_trans (sumFE_atG_le hF hE hC1 hC i w hwi u hw) hv
  unfold Formalism.MainNotions.LiftErrorLocal.vG at h3
  unfold ur
  rw [le_div_iff₀ he] at h3
  linarith

end Formalism.MainNotions.J

end
