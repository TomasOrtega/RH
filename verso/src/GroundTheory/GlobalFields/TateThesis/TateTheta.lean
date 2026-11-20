import Mathlib
import GroundTheory.GlobalFields.TateThesis.GlobalZetaSplit
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def adelicTheta (F : 𝔸[K] → ℂ) (a : IdeleGroup K) : ℂ :=
  ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ)

/- English proof (translation)
The claim follows from `tsum_smul_algebraMap_eq a hF`.
-/
theorem adelicTheta_eq {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) (a : IdeleGroup K) :
    adelicTheta F a =
      ((ideleModule K a : ℝ)⁻¹ : ℂ) * adelicTheta (adelicFourier K F) a⁻¹ :=
  tsum_smul_algebraMap_eq a hF

/- English proof (translation)
Unfold `adelicTheta`. Use `conv_rhs => rw [← (Equiv.mulLeft₀ (δ : K) δ.ne_zero).tsum_eq]`. Use `tsum_congr fun ξ ↦ congrArg F ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((diagonal K δ * a : IdeleGroup K) : 𝔸[K]) * algebraMap K 𝔸[K] ξ = (a : 𝔸[K]) * algebraMap K 𝔸[K] ((δ : K) * ξ)`. Rewrite using `[Units.val_mul, coe_diagonal, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem adelicTheta_diagonal_mul (F : 𝔸[K] → ℂ) (δ : Kˣ) (a : IdeleGroup K) :
    adelicTheta F (diagonal K δ * a) = adelicTheta F a := by
  unfold adelicTheta
  conv_rhs => rw [← (Equiv.mulLeft₀ (δ : K) δ.ne_zero).tsum_eq]
  refine tsum_congr fun ξ ↦ congrArg F ?_
  change ((diagonal K δ * a : IdeleGroup K) : 𝔸[K]) * algebraMap K 𝔸[K] ξ =
    (a : 𝔸[K]) * algebraMap K 𝔸[K] ((δ : K) * ξ)
  rw [Units.val_mul, coe_diagonal, map_mul]
  ring

/- English proof (translation)
Unfold `adelicTheta`. Rewrite using `[← (Equiv.neg K).tsum_eq]`. Use `tsum_congr fun ξ ↦ congrArg F ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-((a : 𝔸[K]) * algebraMap K 𝔸[K] (-ξ)) = (a : 𝔸[K]) * algebraMap K 𝔸[K] ξ`. Rewrite using `[map_neg, mul_neg, neg_neg]`.
-/
theorem adelicTheta_neg (F : 𝔸[K] → ℂ) (a : IdeleGroup K) :
    adelicTheta (fun x ↦ F (-x)) a = adelicTheta F a := by
  unfold adelicTheta
  rw [← (Equiv.neg K).tsum_eq]
  refine tsum_congr fun ξ ↦ congrArg F ?_
  change -((a : 𝔸[K]) * algebraMap K 𝔸[K] (-ξ)) = (a : 𝔸[K]) * algebraMap K 𝔸[K] ξ
  rw [map_neg, mul_neg, neg_neg]

/- English proof (translation)
Rewrite using `[map_zero, smul_zero]`.
-/
theorem smul_algebraMap_zero (a : IdeleGroup K) : a • algebraMap K 𝔸[K] 0 = 0 := by
  rw [map_zero, smul_zero]

/- English proof (translation)
Take `⟨u, hu, hFu⟩` from `exists_summable_bound_smul_algebraMap hF hC`. Use `continuousOn_tsum (fun ξ ↦ ?_) hu (fun ξ a ha ↦ hFu a ha ξ)` and prove the remaining obligations. Establish `h : Continuous fun a : IdeleGroup K ↦ F ((a : 𝔸[K]) * algebraMap K 𝔸[K] ξ)` using `(continuous_of_mem_schwartzBruhat hF).comp (Units.continuous_val.mul continuous_const)`. Conclude with `h.continuousOn`.
-/
theorem continuousOn_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) : ContinuousOn (adelicTheta F) C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap hF hC
  refine continuousOn_tsum (fun ξ ↦ ?_) hu (fun ξ a ha ↦ hFu a ha ξ)
  have h : Continuous fun a : IdeleGroup K ↦ F ((a : 𝔸[K]) * algebraMap K 𝔸[K] ξ) :=
    (continuous_of_mem_schwartzBruhat hF).comp (Units.continuous_val.mul continuous_const)
  exact h.continuousOn

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun a ↦ ?_` and prove the remaining obligations. Take `⟨C, hC, haC⟩` from `exists_compact_mem_nhds a`. Conclude with `(continuousOn_adelicTheta hF hC).continuousAt haC`.
-/
theorem continuous_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Continuous (adelicTheta F) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  obtain ⟨C, hC, haC⟩ := exists_compact_mem_nhds a
  exact (continuousOn_adelicTheta hF hC).continuousAt haC

/- English proof (translation)
Use `IsFundamentalDomain.mk' hS.nullMeasurableSet fun u ↦ ?_` and prove the remaining obligations. Set `e : Kˣ ≃ (diagonalNormOne K).op` to `(diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp`. Establish `he : ∀ ξ : Kˣ, e ξ • u = u * diagonalToNormOne K ξ` using `fun _ ↦ rfl`. Take `⟨ξ, hξ, huniq⟩` from `h u`. Use `⟨e ξ, ?_, fun γ hγ ↦ ?_⟩` and prove the remaining obligations.

Use `show e ξ • u ∈ S`. Rewrite using `[he]`. Conclude with `hξ`. Express the relevant statement in the definitionally equal form `γ • u ∈ S at hγ`. Rewrite `hγ` using `[← e.apply_symm_apply γ, he]`.

Rewrite using `[← e.apply_symm_apply γ, huniq _ hγ]`.
-/
theorem isFundamentalDomain_of_existsUnique {S : Set (normOneSubgroup K)} (hS : MeasurableSet S)
    (h : ∀ u, ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ S) (μ : Measure (normOneSubgroup K)) :
    IsFundamentalDomain (diagonalNormOne K).op S μ := by
  refine IsFundamentalDomain.mk' hS.nullMeasurableSet fun u ↦ ?_
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, e ξ • u = u * diagonalToNormOne K ξ := fun _ ↦ rfl
  obtain ⟨ξ, hξ, huniq⟩ := h u
  refine ⟨e ξ, ?_, fun γ hγ ↦ ?_⟩
  · show e ξ • u ∈ S
    rw [he]
    exact hξ
  change γ • u ∈ S at hγ
  rw [← e.apply_symm_apply γ, he] at hγ
  rw [← e.apply_symm_apply γ, huniq _ hγ]

/- English proof (translation)
Use `(isFundamentalDomain_of_existsUnique hS hSu _).setIntegral_eq (isFundamentalDomain_normOneFundamentalDomain K _) fun γ u ↦ ?_` and prove the remaining obligations. Set `e : Kˣ ≃ (diagonalNormOne K).op` to `(diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp`. Rewrite using `[← e.apply_symm_apply γ]`. Conclude with `hh _ u`.
-/
theorem setIntegral_eq_of_existsUnique {S : Set (normOneSubgroup K)} (hS : MeasurableSet S)
    (hSu : ∀ u, ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ S) {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u) :
    ∫ u in S, h u ∂normOneMeasure K = ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  refine (isFundamentalDomain_of_existsUnique hS hSu _).setIntegral_eq
    (isFundamentalDomain_normOneFundamentalDomain K _) fun γ u ↦ ?_
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  rw [← e.apply_symm_apply γ]
  exact hh _ u

/- English proof (translation)
Take `⟨η, hη, huniq⟩` from `existsUnique_mul_mem_normOneFundamentalDomain K u⁻¹`. Establish `key : ∀ ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (normOneFundamentalDomain K)⁻¹ ↔ u⁻¹ * diagonalToNormOne K ξ⁻¹ ∈ normOneFundamentalDomain K` using `fun ξ ↦ by`. Rewrite using `[Set.mem_inv, mul_inv, map_inv]`. Use `⟨η⁻¹, (key _).2 (by rwa [inv_inv]), fun ξ hξ ↦ ?_⟩` and prove the remaining obligations. Use `huniq _ ((key ξ).1 hξ)` as an intermediate fact.

Rewrite using `[← this, inv_inv]`.
-/
theorem existsUnique_mul_mem_inv_normOneFundamentalDomain (u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (normOneFundamentalDomain K)⁻¹ := by
  obtain ⟨η, hη, huniq⟩ := existsUnique_mul_mem_normOneFundamentalDomain K u⁻¹
  have key : ∀ ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (normOneFundamentalDomain K)⁻¹ ↔
      u⁻¹ * diagonalToNormOne K ξ⁻¹ ∈ normOneFundamentalDomain K := fun ξ ↦ by
    rw [Set.mem_inv, mul_inv, map_inv]
  refine ⟨η⁻¹, (key _).2 (by rwa [inv_inv]), fun ξ hξ ↦ ?_⟩
  have := huniq _ ((key ξ).1 hξ)
  rw [← this, inv_inv]

/- English proof (translation)
Take `⟨η, hη, huniq⟩` from `existsUnique_mul_mem_normOneFundamentalDomain K (v * u)`. Use `⟨η, ?_, fun ξ hξ ↦ huniq _ ?_⟩` and prove the remaining obligations. Use `show v * (u * diagonalToNormOne K η) ∈ normOneFundamentalDomain K`. Rewrite using `[← mul_assoc]` and apply the resulting hypothesis. Express the relevant statement in the definitionally equal form `v * (u * diagonalToNormOne K ξ) ∈ normOneFundamentalDomain K at hξ show v * u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K`.

Rewrite `hξ` using `[← mul_assoc]`. Then use the resulting hypothesis.
-/
theorem existsUnique_mul_mem_preimage_normOneFundamentalDomain (v u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (v * ·) ⁻¹' normOneFundamentalDomain K := by
  obtain ⟨η, hη, huniq⟩ := existsUnique_mul_mem_normOneFundamentalDomain K (v * u)
  refine ⟨η, ?_, fun ξ hξ ↦ huniq _ ?_⟩
  · show v * (u * diagonalToNormOne K η) ∈ normOneFundamentalDomain K
    rwa [← mul_assoc]
  · change v * (u * diagonalToNormOne K ξ) ∈ normOneFundamentalDomain K at hξ
    show v * u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K
    rwa [← mul_assoc] at hξ

/- English proof (translation)
Establish `hpre : (Inv.inv ⁻¹' (normOneFundamentalDomain K)⁻¹ : Set (normOneSubgroup K)) = normOneFundamentalDomain K` using `inv_inv _`. Establish `h1` using `(Measure.measurePreserving_inv (normOneMeasure K)).setIntegral_preimage_emb (MeasurableEquiv.inv (normOneSubgroup K)).measurableEmbedding h (normOneFundamentalDomain K)⁻¹`. Rewrite `h1` using `[hpre]`. Rewrite using `[h1]`. Conclude with `setIntegral_eq_of_existsUnique (measurableSet_normOneFundamentalDomain K).inv existsUnique_mul_mem_inv_normOneFundamentalDomain hh`.
-/
theorem setIntegral_inv_eq {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u) :
    ∫ u in normOneFundamentalDomain K, h u⁻¹ ∂normOneMeasure K =
      ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  have hpre : (Inv.inv ⁻¹' (normOneFundamentalDomain K)⁻¹ : Set (normOneSubgroup K)) =
      normOneFundamentalDomain K := inv_inv _
  have h1 := (Measure.measurePreserving_inv (normOneMeasure K)).setIntegral_preimage_emb
    (MeasurableEquiv.inv (normOneSubgroup K)).measurableEmbedding h (normOneFundamentalDomain K)⁻¹
  rw [hpre] at h1
  rw [h1]
  exact setIntegral_eq_of_existsUnique (measurableSet_normOneFundamentalDomain K).inv
    existsUnique_mul_mem_inv_normOneFundamentalDomain hh

/- English proof (translation)
Establish `hS : MeasurableSet ((v * ·) ⁻¹' normOneFundamentalDomain K)` using `(measurable_const_mul v) (measurableSet_normOneFundamentalDomain K)`. Establish `h1` using `(measurePreserving_mul_left (normOneMeasure K) v).setIntegral_preimage_emb (MeasurableEquiv.mulLeft v).measurableEmbedding h (normOneFundamentalDomain K)`. Establish `h2` using `setIntegral_eq_of_existsUnique hS (existsUnique_mul_mem_preimage_normOneFundamentalDomain v) (h := fun u ↦ h (v * u)) fun ξ u ↦ by simp only [← mul_assoc, hh]`. Rewrite using `[← h2, h1]`.
-/
theorem setIntegral_mul_left_eq {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u)
    (v : normOneSubgroup K) :
    ∫ u in normOneFundamentalDomain K, h (v * u) ∂normOneMeasure K =
      ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  have hS : MeasurableSet ((v * ·) ⁻¹' normOneFundamentalDomain K) :=
    (measurable_const_mul v) (measurableSet_normOneFundamentalDomain K)
  have h1 := (measurePreserving_mul_left (normOneMeasure K) v).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft v).measurableEmbedding h (normOneFundamentalDomain K)
  have h2 := setIntegral_eq_of_existsUnique hS
    (existsUnique_mul_mem_preimage_normOneFundamentalDomain v)
    (h := fun u ↦ h (v * u)) fun ξ u ↦ by simp only [← mul_assoc, hh]
  rw [← h2, h1]

/- English proof (translation)
Rewrite using `[Subgroup.coe_mul, coe_diagonalToNormOne, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]`.
-/
theorem toIdele_mul_diagonalToNormOne (χ : HeckeCharacter K) (ξ : Kˣ) (u : normOneSubgroup K) :
    (χ.toIdele ((u * diagonalToNormOne K ξ : normOneSubgroup K) : IdeleGroup K) : ℂ) =
      χ.toIdele (u : IdeleGroup K) := by
  rw [Subgroup.coe_mul, coe_diagonalToNormOne, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]

/- English proof (translation)
Take `⟨v, hv⟩` from `hχ`. Establish `h` using `setIntegral_mul_left_eq (h := fun u ↦ (χ.toIdele (u : IdeleGroup K) : ℂ)) (fun ξ u ↦ toIdele_mul_diagonalToNormOne χ ξ u) v`. Simplify using `only [Subgroup.coe_mul, map_mul, Circle.coe_mul] at h`. Rewrite `h` using `[integral_const_mul]`. Establish `hv' : (χ.toIdele (v : IdeleGroup K) : ℂ) ≠ 1` using `fun h1 ↦ hv (Circle.ext (by simpa using h1))`.

Establish `h3 : ((χ.toIdele (v : IdeleGroup K) : ℂ) - 1) * ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K = 0`. Rewrite using `[sub_mul, one_mul, h, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hv')`.
-/
theorem setIntegral_char_eq_zero {χ : HeckeCharacter K}
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K = 0 := by
  obtain ⟨v, hv⟩ := hχ
  have h := setIntegral_mul_left_eq (h := fun u ↦ (χ.toIdele (u : IdeleGroup K) : ℂ))
    (fun ξ u ↦ toIdele_mul_diagonalToNormOne χ ξ u) v
  simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul] at h
  rw [integral_const_mul] at h
  have hv' : (χ.toIdele (v : IdeleGroup K) : ℂ) ≠ 1 := fun h1 ↦ hv (Circle.ext (by simpa using h1))
  have h3 : ((χ.toIdele (v : IdeleGroup K) : ℂ) - 1) *
      ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hv')

/- English proof (translation)
Rewrite using `[normOneClassMeasure, Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]`.
-/
theorem normOneClassMeasure_univ :
    normOneClassMeasure K Set.univ = normOneMeasure K (normOneFundamentalDomain K) := by
  rw [normOneClassMeasure, Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]

/- English proof (translation)
Simplify using `only [hχ, Circle.coe_one]`. Rewrite using `[setIntegral_const, normOneClassMeasure_univ, Measure.real_def, Complex.real_smul, mul_one]`.
-/
theorem setIntegral_char_eq_volume {χ : HeckeCharacter K}
    (hχ : ∀ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) = 1) :
    ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K =
      ((normOneClassMeasure K Set.univ).toReal : ℂ) := by
  simp only [hχ, Circle.coe_one]
  rw [setIntegral_const, normOneClassMeasure_univ, Measure.real_def, Complex.real_smul, mul_one]

def thetaIntegrand (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  adelicTheta F (moduleSection w t * (u : IdeleGroup K)) * (χ.toIdele (u : IdeleGroup K) : ℂ)

def thetaIntegral (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain K, thetaIntegrand w F χ t u ∂normOneMeasure K

/- English proof (translation)
Unfold `thetaIntegrand`. Rewrite using `[toIdele_mul_diagonalToNormOne]`. Use `congr 1`. Rewrite using `[Subgroup.coe_mul, coe_diagonalToNormOne, ← mul_assoc, mul_comm _ (diagonal K ξ)]`. Conclude with `adelicTheta_diagonal_mul F ξ _`.
-/
theorem thetaIntegrand_mul_diagonalToNormOne (w : InfinitePlace K) (F : 𝔸[K] → ℂ)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) (ξ : Kˣ) (u : normOneSubgroup K) :
    thetaIntegrand w F χ t (u * diagonalToNormOne K ξ) = thetaIntegrand w F χ t u := by
  unfold thetaIntegrand
  rw [toIdele_mul_diagonalToNormOne]
  congr 1
  rw [Subgroup.coe_mul, coe_diagonalToNormOne, ← mul_assoc, mul_comm _ (diagonal K ξ)]
  exact adelicTheta_diagonal_mul F ξ _

/- English proof (translation)
Establish `h1 : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K)` using `continuous_const.mul continuous_subtype_val`. Establish `h2 : Continuous fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ)` using `continuous_subtype_val.comp (χ.continuous_toIdele.comp continuous_subtype_val)`. Conclude with `((continuous_adelicTheta hF).comp h1).mul h2`.
-/
theorem continuous_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    Continuous (thetaIntegrand w F χ t) := by
  have h1 : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have h2 : Continuous fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ) :=
    continuous_subtype_val.comp (χ.continuous_toIdele.comp continuous_subtype_val)
  exact ((continuous_adelicTheta hF).comp h1).mul h2

/- English proof (translation)
The claim follows from `((continuous_thetaIntegrand w hF χ t).continuousOn.integrableOn_compact (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure`.
-/
theorem integrableOn_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    IntegrableOn (thetaIntegrand w F χ t) (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_thetaIntegrand w hF χ t).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

/- English proof (translation)
The claim follows from `((continuous_subtype_val.comp (χ.continuous_toIdele.comp continuous_subtype_val)).continuousOn.integrableOn_compact (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure`.
-/
theorem integrableOn_char (χ : HeckeCharacter K) :
    IntegrableOn (fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ))
      (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_subtype_val.comp (χ.continuous_toIdele.comp
    continuous_subtype_val)).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toIdele_inv (χ : HeckeCharacter K) (x : IdeleGroup K) :
    (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

/- English proof (translation)
Unfold `thetaIntegrand`. Establish `hmod : (ideleModule K (moduleSection w t⁻¹ * (u : IdeleGroup K)) : ℝ) = (t : ℝ)⁻¹`. Establish `hu : ideleModule K (u : IdeleGroup K) = 1` using `u.2`. Rewrite using `[map_mul, hu, mul_one, ideleModule_moduleSection]`. Both sides reduce to the same expression.

Establish `hinv : (moduleSection w t⁻¹ * (u : IdeleGroup K))⁻¹ = moduleSection w t * ((u⁻¹ : normOneSubgroup K) : IdeleGroup K)`. Rewrite using `[mul_inv, map_inv, inv_inv, InvMemClass.coe_inv, mul_comm]`. Establish `hχ : (χ.toIdele (u : IdeleGroup K) : ℂ) = ((χ⁻¹).toIdele ((u⁻¹ : normOneSubgroup K) : IdeleGroup K) : ℂ)`. Rewrite using `[toIdele_inv, InvMemClass.coe_inv, map_inv, inv_inv]`. Rewrite using `[adelicTheta_eq hF, hmod, hinv, hχ, Complex.ofReal_inv, inv_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaIntegrand_inv (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) :
    thetaIntegrand w F χ t⁻¹ u =
      ((t : ℝ) : ℂ) * thetaIntegrand w (adelicFourier K F) χ⁻¹ t u⁻¹ := by
  unfold thetaIntegrand
  have hmod : (ideleModule K (moduleSection w t⁻¹ * (u : IdeleGroup K)) : ℝ) = (t : ℝ)⁻¹ := by
    have hu : ideleModule K (u : IdeleGroup K) = 1 := u.2
    rw [map_mul, hu, mul_one, ideleModule_moduleSection]
    rfl
  have hinv : (moduleSection w t⁻¹ * (u : IdeleGroup K))⁻¹ =
      moduleSection w t * ((u⁻¹ : normOneSubgroup K) : IdeleGroup K) := by
    rw [mul_inv, map_inv, inv_inv, InvMemClass.coe_inv, mul_comm]
  have hχ : (χ.toIdele (u : IdeleGroup K) : ℂ) =
      ((χ⁻¹).toIdele ((u⁻¹ : normOneSubgroup K) : IdeleGroup K) : ℂ) := by
    rw [toIdele_inv, InvMemClass.coe_inv, map_inv, inv_inv]
  rw [adelicTheta_eq hF, hmod, hinv, hχ, Complex.ofReal_inv, inv_inv]
  ring

/- English proof (translation)
Unfold `thetaIntegral`. Repeatedly rewrite using `[thetaIntegrand_inv w hF χ t]`. Rewrite using `[integral_const_mul]`. Use `congr 1`. Conclude with `setIntegral_inv_eq (h := thetaIntegrand w (adelicFourier K F) χ⁻¹ t) (thetaIntegrand_mul_diagonalToNormOne w _ χ⁻¹ t)`.
-/
theorem thetaIntegral_inv (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    thetaIntegral w F χ t⁻¹ = ((t : ℝ) : ℂ) * thetaIntegral w (adelicFourier K F) χ⁻¹ t := by
  unfold thetaIntegral
  simp_rw [thetaIntegrand_inv w hF χ t]
  rw [integral_const_mul]
  congr 1
  exact setIntegral_inv_eq (h := thetaIntegrand w (adelicFourier K F) χ⁻¹ t)
    (thetaIntegrand_mul_diagonalToNormOne w _ χ⁻¹ t)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `thetaIntegral thetaIntegrand`. Simplify using `only [adelicTheta_neg]`.
-/
theorem thetaIntegral_neg (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) :
    thetaIntegral w (fun x ↦ F (-x)) χ = thetaIntegral w F χ := by
  funext t
  unfold thetaIntegral thetaIntegrand
  simp only [adelicTheta_neg]

end

end GroundTheory.Global
