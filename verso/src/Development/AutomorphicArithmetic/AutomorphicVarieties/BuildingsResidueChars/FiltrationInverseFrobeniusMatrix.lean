import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationEntriesOfFrobeniusMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

/- English proof (translation)
Rewrite `ha` using `[spectrum.mem_iff]`. Establish `h0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `ha` to reduce the goal to its premises. Rewrite using `[map_zero, zero_sub]`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).2 hG).neg`. Use `⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) = algebraMap L (Matrix (Fin d) (Fin d) L) a - G`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_ …`. Normalize the expressions using the abelian group laws.

Rewrite using `[← e]`. Use `((Matrix.isUnit_transpose _).2 hu).mul ?_` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]`. Conclude with `((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG`.
-/
private theorem slopeHi_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

/- English proof (translation)
Establish `hMM' : M' * M = 1` using `mul_eq_one_comm.1 hMM`. Establish `e1 : M'.map ψ * M.map ψ = 1`. Rewrite using `[← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hF : IsUnit F.det`. Use `IsUnit.mk0 _ fun h0 => ?_` and prove the remaining obligations.

Use `congrArg Matrix.det e1` as an intermediate fact. Establish `h1 : (F.map j).det = 0`. Establish `h2` using `RingHom.map_det j F`. Rewrite `h2` using `[h0, map_zero]`. Conclude with `h2.symm`.

Rewrite `this` using `[h, Matrix.det_mul, Matrix.det_mul, h1, mul_zero, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]`. Use `congr 1`.

Establish `e2 : F.map j * (F⁻¹).map j = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF, Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, Matrix.mul_one, hMM, Matrix.mul_one]`. Use `_ = _ := by`.

Rewrite using `[← Matrix.mul_assoc M, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]`.
-/
private theorem slopeHi_inv {R S : Type} [Field R] [CommRing S] [Nontrivial S] (j : R →+* S) (ψ : S →+* S)
    {d : ℕ} (M M' : Matrix (Fin d) (Fin d) S) (F : Matrix (Fin d) (Fin d) R) (hMM : M * M' = 1)
    (h : M.map ψ = M * F.map j) :
    IsUnit F.det ∧ M'.transpose.map ψ = M'.transpose * (F⁻¹).transpose.map j := by
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have e1 : M'.map ψ * M.map ψ = 1 := by
    rw [← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
  have hF : IsUnit F.det := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have := congrArg Matrix.det e1
    have h1 : (F.map j).det = 0 := by
      have h2 := RingHom.map_det j F
      rw [h0, map_zero] at h2
      exact h2.symm
    rw [h, Matrix.det_mul, Matrix.det_mul, h1, mul_zero, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨hF, ?_⟩
  rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
  congr 1
  have e2 : F.map j * (F⁻¹).map j = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M'.map ψ = M'.map ψ * (M * (F.map j * (F⁻¹).map j) * M') := by
        rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
    _ = _ := by
        rw [← Matrix.mul_assoc M, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]

/- English proof (translation)
Introduce `l _ K f hf hσ d M M' A F hMM _ hA hF b hb β hβ`. Use `haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by`. Rewrite using `[← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]`. Conclude with `Submodule.zero_mem _)⟩⟩`. Establish `hc : ((PP l).φB)^[f] = ⇑((PP l).φB ^ f)` using `(AlgHom.coe_pow _ _).symm`.

Take `⟨hA1, hA2⟩` from `slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) ((PP l).φB : Bcr l →+* Bcr l) M M' A hMM hA`. Take `⟨hF1, hF2⟩` from `slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) M M' F hMM (by rw [hc] at hF; exact hF)`. Establish `hu : IsUnit (F.map (algebraMap ↥(K0 K) (Om l))).det`. Use `hF1.map (algebraMap ↥(K0 K) (Om l))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`.

Conclude with `this`. Take `⟨-, ha'⟩` from `slopeHi_spec _ hu hβ`. Establish `e : (F.map (algebraMap ↥(K0 K) (Om l)))⁻¹ = (F⁻¹).map (algebraMap ↥(K0 K) (Om l))`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF1, Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite `ha'` using `[e, ← Matrix.transpose_map]`. Establish `h` using `UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M'.transpose M.transpose (A⁻¹).transpose (F⁻¹).transpose (by rw [← Matrix.transpose_mul, hMM, Matrix.transpose_one]) (by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hA1) hA2 (by rw [hc]; exact hF2) …`. Rewrite `h` using `[neg_neg]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.filtration_inverse_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ b : ℤ, (∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil (-b)) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ b * β⁻¹‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' A F hMM _ hA hF b hb β hβ
  haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
    rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
  have hc : ((PP l).φB)^[f] = ⇑((PP l).φB ^ f) := (AlgHom.coe_pow _ _).symm
  obtain ⟨hA1, hA2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) ((PP l).φB : Bcr l →+* Bcr l) M M' A hMM hA
  obtain ⟨hF1, hF2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
    M M' F hMM (by rw [hc] at hF; exact hF)
  have hu : IsUnit (F.map (algebraMap ↥(K0 K) (Om l))).det := by
    have := hF1.map (algebraMap ↥(K0 K) (Om l))
    rw [RingHom.map_det] at this
    exact this
  obtain ⟨-, ha'⟩ := slopeHi_spec _ hu hβ
  have e : (F.map (algebraMap ↥(K0 K) (Om l)))⁻¹ = (F⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF1, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e, ← Matrix.transpose_map] at ha'
  have h := UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M'.transpose M.transpose (A⁻¹).transpose (F⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM, Matrix.transpose_one])
    (by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hA1)
    hA2 (by rw [hc]; exact hF2) (-b) (fun i j => hb j i) β⁻¹ ha'
  rwa [neg_neg] at h
