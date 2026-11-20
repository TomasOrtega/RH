import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionActionPermutesPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegral

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open scoped Pointwise

namespace Formalism.L2.Th1.H

/- English proof (translation)
Establish `h1 : HasSum (fun g : G => ∫ x in g +ᵥ D, f x ∂μ) (∫ z, f z ∂μ)`. Establish `h` using `hasSum_integral_measure (μ := fun g : G => μ.restrict (g +ᵥ D)) (f := f) (by rwa [hD.sum_restrict])`. Rewrite `h` using `[hD.sum_restrict]`. Then use the resulting hypothesis. Establish `h2 : ∀ g : G, ∫ x in g +ᵥ D, f x ∂μ = ∫ x in D, f (x - ((-g : G) : V)) ∂μ`. Introduce `g`.

Rewrite using `[← Set.image_vadd, (measurePreserving_vadd g μ).setIntegral_image_emb (measurableEmbedding_const_vadd g) f D]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[AddSubgroup.vadd_def, add_comm]`. Rewrite `h1` using `[h2]`. Conclude with `(Equiv.neg G).hasSum_iff.mp h1`.
-/
theorem hasSum_unfold {V E : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddLeftInvariant]
    (G : AddSubgroup V) [Countable G] {D : Set V} (hD : IsAddFundamentalDomain G D μ) {f : V → E}
    (hf : Integrable f μ) :
    HasSum (fun y : G => ∫ z in D, f (z - (y : V)) ∂μ) (∫ z, f z ∂μ) := by
  have h1 : HasSum (fun g : G => ∫ x in g +ᵥ D, f x ∂μ) (∫ z, f z ∂μ) := by
    have h := hasSum_integral_measure (μ := fun g : G => μ.restrict (g +ᵥ D)) (f := f)
      (by rwa [hD.sum_restrict])
    rwa [hD.sum_restrict] at h
  have h2 : ∀ g : G, ∫ x in g +ᵥ D, f x ∂μ = ∫ x in D, f (x - ((-g : G) : V)) ∂μ := by
    intro g
    rw [← Set.image_vadd,
      (measurePreserving_vadd g μ).setIntegral_image_emb (measurableEmbedding_const_vadd g) f D]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [AddSubgroup.vadd_def, add_comm]
  simp_rw [h2] at h1
  exact (Equiv.neg G).hasSum_iff.mp h1

section Reps

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def repMap {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S)
    (p : S × Λ') : Λ :=
  ⟨(p.1 : V) + Ae (p.2 : V), Λ.add_mem (hS.1 _ p.1.2) (hle ⟨p.2, p.2.2, rfl⟩)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨s, hs⟩, ⟨y, hy⟩⟩ ⟨⟨s', hs'⟩, ⟨y', hy'⟩⟩ h`. Establish `h0 : s + Ae y = s' + Ae y'` using `congrArg Subtype.val h`. Establish `h1 : s - s' = Ae (y' - y)`. Rewrite using `[map_sub, sub_eq_sub_iff_add_eq_add, h0, add_comm]`.

Establish `h2 : s = s'` using `hS.2.1 s hs s' hs' (h1 ▸ ⟨y' - y, Λ'.sub_mem hy' hy, rfl⟩)`. Substitute `h2` using the available equality. Establish `h3 : y = y'` using `Ae.injective (add_left_cancel h0)`. Substitute `h3` using the available equality. Both sides reduce to the same expression.

Introduce and unpack `⟨x, hx⟩`. Take `⟨s, hs, y, hy, hxy⟩` from `hS.2.2 x hx`. Use `⟨(⟨s, hs⟩, ⟨y, hy⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h : Ae y = x - s` using `hxy`. Express the relevant statement in the definitionally equal form `s + Ae y = x`.

Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem repMap_bijective {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S) :
    Function.Bijective (repMap Ae hle hS) := by
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨y, hy⟩⟩ ⟨⟨s', hs'⟩, ⟨y', hy'⟩⟩ h
    have h0 : s + Ae y = s' + Ae y' := congrArg Subtype.val h
    have h1 : s - s' = Ae (y' - y) := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, h0, add_comm]
    have h2 : s = s' := hS.2.1 s hs s' hs' (h1 ▸ ⟨y' - y, Λ'.sub_mem hy' hy, rfl⟩)
    subst h2
    have h3 : y = y' := Ae.injective (add_left_cancel h0)
    subst h3
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, y, hy, hxy⟩ := hS.2.2 x hx
    refine ⟨(⟨s, hs⟩, ⟨y, hy⟩), Subtype.ext ?_⟩
    have h : Ae y = x - s := hxy
    change s + Ae y = x
    rw [h]
    abel

end Reps

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H Λ α δ Ae hL hU D' hD' _ S hS`. Use `set Λ' : AddSubgroup V := Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ with hΛ'`. Establish `: ProperSpace V` using `FiniteDimensional.proper ℂ V`. Establish `: DiscreteTopology Λ` using `hL.1`. Establish `hc : Countable Λ` using `TopologicalSpace.separableSpace_iff_countable.mp inferInstance`.

Establish `hc' : Countable Λ'` using `(AddSubgroup.inclusion_injective (inf_le_left : Λ' ≤ Λ)).countable`. Take `⟨hT, -⟩` from `kernelTermShift V H hU.herm α δ Ae hU.isom hU.cay`. Establish `hgq : Integrable (gq H Ae) μ` using `(cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).1`. Establish `hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ` using `ud_latA_le hU`. Set `e : S × Λ' ≃ Λ` to `Equiv.ofBijective _ (repMap_bijective Ae hle hS)`.

Set `f : V → V → ℂ` to `fun s z => gq H Ae (z - Ae.symm s)`. Establish `hf : ∀ s, Integrable (f s) μ` using `fun s => hgq.comp_sub_right _`. Establish `hfi : ∀ s, ∫ z, f s z ∂μ = ∫ z, gq H Ae z ∂μ` using `fun s => integral_sub_right_eq_self (μ := μ) (gq H Ae) (Ae.symm s)`. Establish `hFe : ∀ (p : S × Λ') z, termT H α δ ((e p : Λ) : V) z = phiC H α Ae p.1 * f p.1 (z - (p.2 : V))`. Introduce `p z`.

Rewrite using `[hT]`. Establish `h1 : ((e p : Λ) : V) = (p.1 : V) + Ae (p.2 : V)` using `rfl`. Rewrite using `[h1, ud_phi_wd hU (hS.1 _ p.1.2) (show Ae (p.2 : V) ∈ latA Λ δ Ae from ⟨p.2, p.2.2, rfl⟩)]`. Simplify using `only [f, map_add, LinearEquiv.symm_apply_apply]`. Use `congr 2`.

Normalize the expressions using the abelian group laws. Establish `hint : ∀ x : Λ, Integrable (fun z => termT H α δ (x : V) z) (μ.restrict D')`. Introduce `x`. Repeatedly rewrite using `[hT]`. Conclude with `((hgq.comp_sub_right _).const_mul _).restrict`.

Establish `hsumn : Summable fun x : Λ => ∫ z in D', ‖termT H α δ (x : V) z‖ ∂μ`. Establish `key : Summable fun p : S × Λ' => ∫ z in D', ‖termT H α δ ((e p : Λ) : V) z‖ ∂μ`. Use `(summable_prod_of_nonneg (fun p => integral_nonneg fun z => norm_nonneg _)).mpr ⟨fun s => ?_, Summable.of_finite⟩` and prove the remaining obligations. Establish `h` using `(hasSum_unfold μ Λ' hD' (hf s).norm).summable.mul_left ‖phiC H α Ae s‖`. Use `h.congr fun y => ?_` and prove the remaining obligations.

Simplify using `only [hFe, norm_mul, integral_const_mul]`. Conclude with `e.summable_iff.mp key`. Establish `hmain` using `hasSum_integral_of_summable_integral_norm hint hsumn`. Establish `hker : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ) = ∑' x : Λ, termT H α δ (x : V) z`. Introduce `z`.

Simplify using `only [kerP, termT, tsum_mul_right]`. Repeatedly rewrite using `[hker]`. Establish `hs2 : Summable fun c : S × Λ' => ∫ a in D', termT H α δ ((e c : Λ) : V) a ∂μ` using `e.summable_iff.mpr hmain.summable`. Rewrite using `[← hmain.tsum_eq, ← e.tsum_eq, hs2.tsum_prod, tsum_fintype, Finset.sum_mul, ← Finset.sum_coe_sort S]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Repeatedly rewrite using `[hFe, integral_const_mul]`. Rewrite using `[tsum_mul_left, (hasSum_unfold μ Λ' hD' (hf s)).tsum_eq, hfi]`.
-/
theorem unfoldingIntegral : UnfoldIntegral := by
  intro V _ _ _ _ _ μ _ H Λ α δ Ae hL hU D' hD' _ S hS
  classical
  set Λ' : AddSubgroup V := Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ with hΛ'
  have : ProperSpace V := FiniteDimensional.proper ℂ V
  have : DiscreteTopology Λ := hL.1
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hc' : Countable Λ' := (AddSubgroup.inclusion_injective (inf_le_left : Λ' ≤ Λ)).countable
  obtain ⟨hT, -⟩ := kernelTermShift V H hU.herm α δ Ae hU.isom hU.cay
  have hgq : Integrable (gq H Ae) μ := (cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).1
  have hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ := ud_latA_le hU
  let e : S × Λ' ≃ Λ := Equiv.ofBijective _ (repMap_bijective Ae hle hS)
  let f : V → V → ℂ := fun s z => gq H Ae (z - Ae.symm s)
  have hf : ∀ s, Integrable (f s) μ := fun s => hgq.comp_sub_right _
  have hfi : ∀ s, ∫ z, f s z ∂μ = ∫ z, gq H Ae z ∂μ := fun s =>
    integral_sub_right_eq_self (μ := μ) (gq H Ae) (Ae.symm s)
  have hFe : ∀ (p : S × Λ') z,
      termT H α δ ((e p : Λ) : V) z = phiC H α Ae p.1 * f p.1 (z - (p.2 : V)) := by
    intro p z
    rw [hT]
    have h1 : ((e p : Λ) : V) = (p.1 : V) + Ae (p.2 : V) := rfl
    rw [h1, ud_phi_wd hU (hS.1 _ p.1.2) (show Ae (p.2 : V) ∈ latA Λ δ Ae from ⟨p.2, p.2.2, rfl⟩)]
    simp only [f, map_add, LinearEquiv.symm_apply_apply]
    congr 2
    abel
  have hint : ∀ x : Λ, Integrable (fun z => termT H α δ (x : V) z) (μ.restrict D') := by
    intro x
    simp_rw [hT]
    exact ((hgq.comp_sub_right _).const_mul _).restrict
  have hsumn : Summable fun x : Λ => ∫ z in D', ‖termT H α δ (x : V) z‖ ∂μ := by
    have key : Summable fun p : S × Λ' => ∫ z in D', ‖termT H α δ ((e p : Λ) : V) z‖ ∂μ := by
      refine (summable_prod_of_nonneg (fun p => integral_nonneg fun z => norm_nonneg _)).mpr
        ⟨fun s => ?_, Summable.of_finite⟩
      have h := (hasSum_unfold μ Λ' hD' (hf s).norm).summable.mul_left ‖phiC H α Ae s‖
      refine h.congr fun y => ?_
      simp only [hFe, norm_mul, integral_const_mul]
    exact e.summable_iff.mp key
  have hmain := hasSum_integral_of_summable_integral_norm hint hsumn
  have hker : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ) = ∑' x : Λ, termT H α δ (x : V) z := by
    intro z
    simp only [kerP, termT, tsum_mul_right]
  simp_rw [hker]
  have hs2 : Summable fun c : S × Λ' => ∫ a in D', termT H α δ ((e c : Λ) : V) a ∂μ :=
    e.summable_iff.mpr hmain.summable
  rw [← hmain.tsum_eq, ← e.tsum_eq, hs2.tsum_prod, tsum_fintype,
    Finset.sum_mul, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp_rw [hFe, integral_const_mul]
  rw [tsum_mul_left, (hasSum_unfold μ Λ' hD' (hf s)).tsum_eq, hfi]

end Formalism.L2.Th1.H
