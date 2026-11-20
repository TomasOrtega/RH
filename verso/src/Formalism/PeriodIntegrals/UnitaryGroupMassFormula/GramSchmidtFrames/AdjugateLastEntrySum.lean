import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermBvecEI

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section om2

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[hadj, hW, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[hW'.2, one_mul, Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply]`. Introduce `e _ he`. Rewrite using `[hW'.1 _ _ (lt_of_le_of_ne (Fin.le_last e) he), zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma adjugate_last_entry_sum {U' W' Zt Z Vm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hW : U'.adjugate = W')
    (hW' : W' ∈ C2.UTset (r + 1)) (hadj : Zt.adjugate = U'.adjugate * (Z.adjugate * Vmᴴ)) (a : Fin (r + 1)) :
    Zt.adjugate (Fin.last r) a = ∑ e, Z.adjugate (Fin.last r) e * star (Vm a e) := by
  rw [hadj, hW, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · rw [hW'.2, one_mul, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
  · intro e _ he
    rw [hW'.1 _ _ (lt_of_le_of_ne (Fin.le_last e) he), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Establish `hF'` using `Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'`. Establish `hF` using `Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz`. Establish `hS : n ∈ Sset k r z` using `⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩`. Establish `hSi' : n'⁻¹ ∈ Sset k r z'` using `⟨1, one_mem_UW z', n'⁻¹, Nc.inv_mem n' hn', (one_mul _).symm⟩`.

Establish `hS' : n' ∈ Sset k r z'` using `⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩`. Establish `hV` using `(hF.1 n hS).2.1`. Establish `hU'` using `(hF'.1 n' hS').2.1`. Establish `hW'` using `(hF'.1 n'⁻¹ hSi').2.1`. Establish `hVU` using `(uMap_inv hz hn).1`.

Establish `hdU : ((C2.uMap k r z n⁻¹)ᴴ).det = 1`. Rewrite using `[Matrix.det_conjTranspose]`. Establish `: (C2.uMap k r z n⁻¹).det * (C2.uMap k r z n).det = 1`. Rewrite using `[← Matrix.det_mul, (uMap_inv hz hn).2, Matrix.det_one]`. Rewrite `this` using `[unitri_det hV, mul_one]`.

Rewrite using `[this, star_one]`. Establish `hadjU : ((C2.uMap k r z n⁻¹)ᴴ).adjugate = (C2.uMap k r z n)ᴴ` using `adj_of_inv hdU (by rw [← Matrix.conjTranspose_mul, hVU, Matrix.conjTranspose_one])`. Establish `hW : (C2.uMap k r z' n').adjugate = C2.uMap k r z' n'⁻¹` using `adj_of_inv (unitri_det hU') (uMap_inv hz' hn').1`. Establish `hadj : (Zhat k r z z' (n * y * n')).adjugate = (C2.uMap k r z' n').adjugate * ((Zhat k r z z' y).adjugate * (C2.uMap k r z n)ᴴ)`. Rewrite using `[zhat_N hz hz' hn hn' y, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjU]`.

Establish `hfr : ∀ e, n *ᵥ fvec k r z e = ∑ a, C2.uMap k r z n a e • fvec k r z a` using `(hF.1 n hS).1`. Unfold `xcofL`. Simplify using `only [adjugate_last_entry_sum hW hW' hadj, star_sum, star_mul', star_star]`. Rewrite using `[mv_sum]`. Simplify using `only [mulVec_smul, hfr, Finset.smul_sum, smul_smul, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`.
-/
theorem xcofL_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    xcofL k r z z' (n * y * n') = n *ᵥ xcofL k r z z' y := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hSi' : n'⁻¹ ∈ Sset k r z' := ⟨1, one_mem_UW z', n'⁻¹, Nc.inv_mem n' hn', (one_mul _).symm⟩
  have hS' : n' ∈ Sset k r z' := ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩
  have hV := (hF.1 n hS).2.1
  have hU' := (hF'.1 n' hS').2.1
  have hW' := (hF'.1 n'⁻¹ hSi').2.1
  have hVU := (uMap_inv hz hn).1
  have hdU : ((C2.uMap k r z n⁻¹)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose]
    have : (C2.uMap k r z n⁻¹).det * (C2.uMap k r z n).det = 1 := by
      rw [← Matrix.det_mul, (uMap_inv hz hn).2, Matrix.det_one]
    rw [unitri_det hV, mul_one] at this
    rw [this, star_one]
  have hadjU : ((C2.uMap k r z n⁻¹)ᴴ).adjugate = (C2.uMap k r z n)ᴴ :=
    adj_of_inv hdU (by rw [← Matrix.conjTranspose_mul, hVU, Matrix.conjTranspose_one])
  have hW : (C2.uMap k r z' n').adjugate = C2.uMap k r z' n'⁻¹ := adj_of_inv (unitri_det hU') (uMap_inv hz' hn').1
  have hadj : (Zhat k r z z' (n * y * n')).adjugate =
      (C2.uMap k r z' n').adjugate * ((Zhat k r z z' y).adjugate * (C2.uMap k r z n)ᴴ) := by
    rw [zhat_N hz hz' hn hn' y, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjU]
  have hfr : ∀ e, n *ᵥ fvec k r z e = ∑ a, C2.uMap k r z n a e • fvec k r z a := (hF.1 n hS).1
  unfold xcofL
  simp only [adjugate_last_entry_sum hW hW' hadj, star_sum, star_mul', star_star]
  rw [mv_sum]
  simp only [mulVec_smul, hfr, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(Formalism.QuantumDeterminants.hpkFacts k r).1`. Establish `hu : IsUnit y.det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy`. Rewrite using `[← herm_bvec_eI (y⁻¹ *ᵥ xcofL k r z z' y) a, ← fvec_lt z' a, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec, hm_symm _ hH]`. Unfold `xcofL`. Rewrite using `[hm_sum_r]`.

Use `adj_row (Zhat k r z z' y) ⟨a.val, by omega⟩ (by` as an intermediate fact. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use the proof step `omega)`.

Simplify using `only [star_star]`. Rewrite using `[show (∑ i, (Zhat k r z z' y).adjugate (Fin.last r) i * herm (Hpk k r) (y *ᵥ fvec k r z' ⟨a.val, by omega⟩) (fvec k r z i)) = 0 from this, star_zero]`.
-/
lemma ginv_xcofL_esI (z z' : Fin (2 * r + k + 1) → ℂ) {y : B.Mat k r} (hy : y ∈ B.GV k r) (a : Fin r) :
    (y⁻¹ *ᵥ xcofL k r z z' y) (esI k r a) = 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  rw [← herm_bvec_eI (y⁻¹ *ᵥ xcofL k r z z' y) a, ← fvec_lt z' a,
    ← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec,
    hm_symm _ hH]
  unfold xcofL
  rw [hm_sum_r]
  have := adj_row (Zhat k r z z' y) ⟨a.val, by omega⟩ (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  simp only [star_star]
  rw [show (∑ i, (Zhat k r z z' y).adjugate (Fin.last r) i *
      herm (Hpk k r) (y *ᵥ fvec k r z' ⟨a.val, by omega⟩) (fvec k r z i)) = 0 from this, star_zero]

/- English proof (translation)
Introduce `k r z z' hk hr hz hz' y hy hG n hn n' hn'`. Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Unfold `omW'`. Rewrite using `[xcofL_N hz hz' hn hn' y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec, show n⁻¹ *ᵥ (n *ᵥ xcofL k r z z' y) = xcofL k r z z' y by`. Rewrite using `[mulVec_mulVec, Matrix.nonsing_inv_mul _ (Nc.unit n hn), one_mulVec],`.

Use `prW_N (Nc.inv_mem n' hn') (ginv_xcofL_esI z z' hy)]`.
-/
theorem satOm' : SatOm' := by
  intro k r z z' hk hr hz hz' y hy hG n hn n' hn'
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  unfold omW'
  rw [xcofL_N hz hz' hn hn' y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    show n⁻¹ *ᵥ (n *ᵥ xcofL k r z z' y) = xcofL k r z z' y by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (Nc.unit n hn), one_mulVec],
    prW_N (Nc.inv_mem n' hn') (ginv_xcofL_esI z z' hy)]

/- English proof (translation)
The claim follows from `gfSat_of satOm satOm'`.
-/
theorem gfSat : GfSat := gfSat_of satOm satOm'

end om2

end PI.UnitaryGroupMassFormula.GsFr
