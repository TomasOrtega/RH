import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.GaloisValuations.ArithOfA
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
open Pointwise

namespace GlobalTheory.HilbertKill

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ Av hAv M _ z hz hlc hIne hC`. Set `f : G E Ω →* Multiplicative M` to `{ toFun := fun g => Multiplicative.ofAdd (z g) map_one' := by`. Establish `h` using `hz 1 1`. Rewrite `h` using `[mul_one, left_eq_add]`. Simplify using `[h]`.

Use the proof step `map_mul' := fun g h => by simp [hz] }`. Establish `hf : ∀ g, g ∈ f.ker ↔ z g = 0` using `fun g => by`. Rewrite using `[MonoidHom.mem_ker]`. Use `show Multiplicative.ofAdd (z g) = 1 ↔ _`. Rewrite using `[← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]`.

Establish `hclosed : IsClosed (f.ker : Set (G E Ω))`. Use `hlc.isClosed_fiber 0 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Conclude with `hf g`. Establish `hinv : ∀ g, z g⁻¹ = - z g` using `fun g => by`.

Establish `h` using `hz g g⁻¹`. Establish `h1 : z 1 = 0` using `(hf 1).1 f.ker.one_mem`. Rewrite `h` using `[mul_inv_cancel, h1]`. Conclude with `(neg_eq_of_add_eq_zero_right h.symm).symm`. Introduce `σ hσ`.

Use `(hf σ).1 (Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hclosed hσ)` and prove the remaining obligations. Introduce and unpack `g ((hg | ⟨A, hg⟩) | hg)`. Conclude with `Abelianization.commutator_subset_ker f hg`. Establish `hg'` using `(ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg`. Break down `GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩` into its components or cases.

Conclude with `f.ker.one_mem`. Establish `hA : IsPlaceOver A v` using `fun x => by rw [← hv x, A.mem_nonunits_iff]`. Establish `hgI : g ∈ Ine (F` using `E) A := ⟨hg'.1, fun x hx => A.mem_nonunits_iff.1 (hg'.2 x ((A.valuation_le_one_iff x).1 hx))⟩`. Take `⟨τ, hτ⟩` from `exists_smul_eq_of_isPlaceOver (hAv v) hA`. Establish `h2 : τ⁻¹ * g * τ⁻¹⁻¹ ∈ Ine (F` using `E) (τ⁻¹ • A) := conj_mem_Ine_smul hgI`.

Rewrite `h2` using `[inv_inv, ← hτ, inv_smul_smul]`. Establish `h3` using `hIne v _ h2`. Use `show z g = 0`. Establish `e : g = τ * (τ⁻¹ * g * τ) * τ⁻¹` using `by group`. Rewrite using `[e, hz, hz, h3, hinv, add_zero, add_neg_cancel]`.

Conclude with `(hf g).2 (hC g hg)`.
-/
theorem hilbertSubgroup_le_ker : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  intro E Ω _ _ _ _ _ Av hAv M _ z hz hlc hIne hC
  let f : G E Ω →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by
        have h := hz 1 1
        rw [mul_one, left_eq_add] at h
        simp [h]
      map_mul' := fun g h => by simp [hz] }
  have hf : ∀ g, g ∈ f.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  have hclosed : IsClosed (f.ker : Set (G E Ω)) := by
    convert hlc.isClosed_fiber 0 using 1
    ext g
    exact hf g
  have hinv : ∀ g, z g⁻¹ = - z g := fun g => by
    have h := hz g g⁻¹
    have h1 : z 1 = 0 := (hf 1).1 f.ker.one_mem
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  intro σ hσ
  refine (hf σ).1 (Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hclosed hσ)
  rintro g ((hg | ⟨A, hg⟩) | hg)
  · exact Abelianization.commutator_subset_ker f hg
  · have hg' := (ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg
    rcases GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩
    · exact f.ker.one_mem
    have hA : IsPlaceOver A v := fun x => by rw [← hv x, A.mem_nonunits_iff]
    have hgI : g ∈ Ine (F := E) A :=
      ⟨hg'.1, fun x hx => A.mem_nonunits_iff.1 (hg'.2 x ((A.valuation_le_one_iff x).1 hx))⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (hAv v) hA
    have h2 : τ⁻¹ * g * τ⁻¹⁻¹ ∈ Ine (F := E) (τ⁻¹ • A) := conj_mem_Ine_smul hgI
    rw [inv_inv, ← hτ, inv_smul_smul] at h2
    have h3 := hIne v _ h2
    show z g = 0
    have e : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
    rw [e, hz, hz, h3, hinv, add_zero, add_neg_cancel]
  · exact (hf g).2 (hC g hg)

end GlobalTheory.HilbertKill
