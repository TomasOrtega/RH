import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

/- English proof (translation)
Establish `h` using `(Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)`. Take `⟨l, hl, e⟩` from `(Finsupp.mem_span_image_iff_linearCombination _).1 h`. Use `⟨l, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨k, -, hik, hkj⟩` from `hl (Finsupp.mem_support_iff.2 hne)`.

Conclude with `absurd (hik.trans_lt hkj) (not_lt.2 hi)`. Rewrite `e` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e beta_reduce`. Establish `e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i`. Rewrite using `[Matrix.mulVec_eq_sum]`. Simplify using `only [op_smul_eq_smul]`.

Rewrite using `[e2, e, add_sub_cancel]`.
-/
theorem col_coeff {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {g : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) (j : Fin r) :
    ∃ c : Fin r → AF F ⊗[F] E, (∀ i, j ≤ i → c i = 0) ∧
      (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j + adMat F X *ᵥ c := by
  have h := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 h
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, -, hik, hkj⟩ := hl (Finsupp.mem_support_iff.2 hne)
    exact absurd (hik.trans_lt hkj) (not_lt.2 hi)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e
    beta_reduce at e
    have e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i := by
      rw [Matrix.mulVec_eq_sum]; simp only [op_smul_eq_smul]
    rw [e2, e, add_sub_cancel]

omit [NumberField E] in

/- English proof (translation)
Use `choose c hc hce using col_coeff hg`. Use `⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩` and prove the remaining obligations. Establish `hji : j < i` using `not_le.1 fun h => absurd hlt (not_lt.2 (hd h))`. Establish `hle : Fin.castLE hs j ≤ Fin.castLE hs i`. Rewrite using `[Fin.le_def]`.

Simplify using `only [Fin.coe_castLE]`. Conclude with `hji.le`. Simplify using `[Matrix.one_apply_ne hji.ne', hc _ _ hle]`. Use extensionality with `k j`. Establish `h1` using `congrFun (hce (Fin.castLE hs j)) k`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1`. Rewrite using `[Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]`. Simplify using `only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢`. Rewrite using `[h1]`. Use `congr 1`.

Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)` and prove the remaining obligations. Establish `: s ≤ i.val`. Assume the negation of the conclusion as `hlt`. Conclude with `hi ⟨⟨i.val, by omega⟩, rfl⟩`.

Rewrite using `[hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]`.
-/
theorem par_of_unip {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {s : ℕ} (hs : s ≤ r) {d : Fin s → ℕ}
    (hd : Monotone d) {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) :
    ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B := by
  choose c hc hce using col_coeff hg
  refine ⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩
  · have hji : j < i := not_le.1 fun h => absurd hlt (not_lt.2 (hd h))
    have hle : Fin.castLE hs j ≤ Fin.castLE hs i := by
      rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hji.le
    simp [Matrix.one_apply_ne hji.ne', hc _ _ hle]
  · ext k j
    have h1 := congrFun (hce (Fin.castLE hs j)) k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1
    rw [Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢
    rw [h1]
    congr 1
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)
    have : s ≤ i.val := by
      by_contra hlt
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    rw [hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]

end GlobalTheory.RatLevi

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT`. Take `⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1` from `⟨_, rfl⟩`. Establish `hs : s ≤ r` using `hsdef ▸ Finset.sup_le fun k _ => k.2`. Establish `hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k` using `fun i => by`. Rewrite using `[hsdef, Finset.lt_sup_iff]`.

Conclude with `exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega`. Take `⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card` from `⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩`. Establish `hdm : Monotone d` using `fun i j hij => by`. Rewrite using `[hddef, hddef]`. Use `Finset.card_le_card fun k hk => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter] at hk ⊢`. Use `⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.le_def]`. Simplify using `only [Fin.coe_castLE]`. Conclude with `hij`.

Take `⟨hu, hl, -⟩` from `GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef`. Establish `hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d` using `⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩`. Take `⟨u, huF, m, hmF, hpm, hr⟩` from `(GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp) (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp) (by rw [Glo …`. Use `⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_inv γ, hpm, mul_inv_rev]`.
-/
theorem GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT
  obtain ⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1 := ⟨_, rfl⟩
  have hs : s ≤ r := hsdef ▸ Finset.sup_le fun k _ => k.2
  have hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := fun i => by
    rw [hsdef, Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card := ⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩
  have hdm : Monotone d := fun i j hij => by
    rw [hddef, hddef]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩
    rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hij
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef
  have hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d :=
    ⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩
  obtain ⟨u, huF, m, hmF, hpm, hr⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 _ hp
  refine ⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩
  rw [← inv_inv γ, hpm, mul_inv_rev]
