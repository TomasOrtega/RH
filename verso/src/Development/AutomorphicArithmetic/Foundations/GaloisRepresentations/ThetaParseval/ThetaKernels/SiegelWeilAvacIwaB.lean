import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
/- English proof (translation)
Use `set g := inFrame d.b p with hg`. Use `set A := g.toBlocks₁₁`. Use `set B := g.toBlocks₁₂`. Use `set D := g.toBlocks₂₂`. Establish `hgb : g = Matrix.fromBlocks A B 0 D` using `by rw [← h21, Matrix.fromBlocks_toBlocks]`.

Establish `hBm : IsUnit (incM F d.b.1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)`. Establish `hBi : IsUnit (incM F (d.b⁻¹).1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)`. Establish `hug : IsUnit g` using `(hBi.mul (Units.isUnit p.1)).mul hBm`. Establish `hdet : IsUnit (A.det * D.det)`. Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det g).1 hug`. Establish `hA : IsUnit A.det` using `isUnit_of_mul_isUnit_left hdet`. Establish `hD : IsUnit D.det` using `isUnit_of_mul_isUnit_right hdet`. Use `set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def`. Establish `hMd : IsUnit Md` using `(Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)`.

Take `⟨C', hC'⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d`. Establish `hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J)` using `p.2`. Establish `hgf` using `KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP`. Establish `hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hC'`. Rewrite `hgf` using `[hC'']`.

Establish `hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hgf`. Rewrite `hgf'` using `[hgb]`. Establish `hMdf` using `KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'`. Rewrite `hMdf` using `[← hC'']`. Establish `hM0mem` using `KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf`.

Establish `hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1)` using `(hBm.mul hMd).mul hBi`. Set `u : GL (Fin d.n ⊕ Fin d.n) (AE F E)` to `hM0u.unit`. Establish `hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F d.b.1 * Md * incM F (d.b⁻¹).1` using `IsUnit.unit_spec hM0u`. Establish `hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J))` using `by show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)`. Rewrite using `[hu]`.

Conclude with `hM0mem`. Set `m0 : d.G` to `⟨u, hmem⟩`. Establish `hm0 : inFrame d.b m0 = Md` using `by show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md`. Rewrite using `[hu]`. Simplify using `only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]`. Establish `hAu` using `(Matrix.isUnit_iff_isUnit_det A).2 hA`. Establish `hDu` using `(Matrix.isUnit_iff_isUnit_det D).2 hD`. Use `⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu, (inv_mul_cancel_right p m0).symm⟩` and prove the remaining obligations. Establish `e` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0`.

Rewrite `e` using `[inv_mul_cancel_right, hm0]`. Apply `(hMd.mul_left_inj).1` to reduce the goal to its premises. Rewrite using `[← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]`. Rewrite using `[hm0, IsUnit.unit_spec, IsUnit.unit_spec]`.
-/
theorem par_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ (n0 m0 : d.G) (A D : GL (Fin d.n) (AE F E)),
      inFrame d.b n0 = Matrix.fromBlocks 1 ((inFrame d.b p).toBlocks₁₂ * (inFrame d.b p).toBlocks₂₂⁻¹) 0 1 ∧
      inFrame d.b m0 = Matrix.fromBlocks A.1 0 0 D.1 ∧ A.1 = (inFrame d.b p).toBlocks₁₁ ∧
      D.1 = (inFrame d.b p).toBlocks₂₂ ∧ p = n0 * m0 := by
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu,
    (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
/- English proof (translation)
Use `set M := inFrame d.b q with hM`. Take `⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d q (isQ_21 hq)`. Use `⟨(d.χ (Matrix.GeneralLinearGroup.det A) : ℂ) * (((absE F E (Matrix.GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩` and prove the remaining obligations. Establish `hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k`. Rewrite using `[hD]`.

Conclude with `isQ_22 hq`. Establish `hDu : IsUnit M.toBlocks₂₂.det`. Rewrite using `[← hD]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 D.isUnit`. Establish `hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k` using `inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)`.

Establish `hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0`. Introduce `i j hi hj`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i₀`.

Substitute `hk` using the available equality. Rewrite using `[hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]`. Rewrite using `[isQ_12 hq i k hi hk, zero_mul]`. Establish `hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0`. Introduce `i j hij`.

Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Break down `hij with rfl | rfl` into its components or cases. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hX a, zero_mul, zero_mul]`. Rewrite using `[hX b, map_zero, mul_zero]`. Establish `htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0`. Establish `: Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0`. Simplify using `only [Matrix.trace, Matrix.diag]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = i₀ ∨ j = i₀`. Rewrite using `[hG j i (h.symm), mul_zero]`.

Use `push_neg at h`. Rewrite using `[hβ i j h.1 h.2, zero_mul]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, this, map_zero]`. Establish `hXD : X * (D⁻¹).1ᵀ = X`. Establish `h1 : X * D.1ᵀ = X`.

Use extensionality with `a j`. Rewrite using `[Matrix.mul_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Matrix.transpose_apply]`. Distinguish the cases in `hj : j = i₀`.

Substitute `hj` using the available equality. Rewrite using `[hX a, zero_mul]`. Rewrite using `[hD1 j j hj, Matrix.one_apply_eq, mul_one]`. Introduce `k _ hk`. Rewrite using `[Matrix.transpose_apply]`.

Distinguish the cases in `hk0 : k = i₀`. Substitute `hk0` using the available equality. Rewrite using `[hX a, zero_mul]`. Rewrite using `[hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Establish `hm0s : d.om m0 Φ ∈ d.sch` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d m0 hΦ`. Rewrite using `[hp, map_mul, Module.End.mul_apply, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]`.
-/
theorem q_T'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E i₀ (inFrame d.b q) lam) :
    ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → d.T (d.om q Φ) X = c * d.T Φ X := by
  set M := inFrame d.b q with hM
  obtain ⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d q (isQ_21 hq)
  refine ⟨(d.χ (Matrix.GeneralLinearGroup.det A) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩
  have hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k := by
    rw [hD]; exact isQ_22 hq
  have hDu : IsUnit M.toBlocks₂₂.det := by
    rw [← hD]; exact (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k :=
    inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)
  have hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0 := by
    intro i j hi hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i₀
    · subst hk; rw [hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · rw [isQ_12 hq i k hi hk, zero_mul]
  have hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0 := by
    intro i j hij
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases hij with rfl | rfl
    · rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hX a, zero_mul, zero_mul]
    · rw [hX b, map_zero, mul_zero]
  have htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
    have : Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : i = i₀ ∨ j = i₀
      · rw [hG j i (h.symm), mul_zero]
      · push_neg at h
        rw [hβ i j h.1 h.2, zero_mul]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, this, map_zero]
  have hXD : X * (D⁻¹).1ᵀ = X := by
    have h1 : X * D.1ᵀ = X := by
      ext a j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Matrix.transpose_apply]
        by_cases hj : j = i₀
        · subst hj; rw [hX a, zero_mul]
        · rw [hD1 j j hj, Matrix.one_apply_eq, mul_one]
      · intro k _ hk
        rw [Matrix.transpose_apply]
        by_cases hk0 : k = i₀
        · subst hk0; rw [hX a, zero_mul]
        · rw [hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]
      · simp
    calc X * (D⁻¹).1ᵀ = X * D.1ᵀ * (D⁻¹).1ᵀ := by rw [h1]
      _ = X * ((D⁻¹).1 * D.1)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hm0s : d.om m0 Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d m0 hΦ
  rw [hp, map_mul, Module.End.mul_apply, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
