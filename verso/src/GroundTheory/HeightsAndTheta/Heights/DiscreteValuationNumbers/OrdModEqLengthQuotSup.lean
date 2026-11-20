import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Length
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI

universe u v

section Terms

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/- English proof (translation)
Rewrite using `[← length_coker_quot p x]`. Establish `hr : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) x) = Submodule.map (p.asIdeal : Submodule A A).mkQ (Ideal.span {x} : Submodule A A)`. Use extensionality with `y`. Take `⟨b, rfl⟩` from `Submodule.mkQ_surjective _ y`. Simplify using `only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Take `⟨c, rfl⟩` from `Submodule.mkQ_surjective _ z`. Conclude with `⟨c * x, ⟨c, rfl⟩, by rw [← hz, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩`. Introduce and unpack `⟨a, ⟨c, rfl⟩, hab⟩`.

Conclude with `⟨Submodule.mkQ _ c, by rw [← hab, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩`. Conclude with `((Submodule.quotEquivOfEq _ _ hr).trans (Submodule.quotientQuotientEquivQuotientSup _ _)).length_eq`.
-/
theorem ordMod_eq_length_quot_sup (p : PrimeSpectrum A) (x : A) :
    ordMod p x = length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by
  rw [← length_coker_quot p x]
  have hr : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) x) =
      Submodule.map (p.asIdeal : Submodule A A).mkQ (Ideal.span {x} : Submodule A A) := by
    ext y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
      exact ⟨c * x, ⟨c, rfl⟩, by rw [← hz, Submodule.mkQ_apply, Submodule.mkQ_apply,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩
    · rintro ⟨a, ⟨c, rfl⟩, hab⟩
      exact ⟨Submodule.mkQ _ c, by rw [← hab, Submodule.mkQ_apply, Submodule.mkQ_apply,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)).length_eq

/- English proof (translation)
Establish `hiff` using `dim_quot_eq_one_iff hdim p.asIdeal`. Rewrite using `[ordMod_eq_length_quot_sup, finsum_eq_if, finsum_eq_if]`. Distinguish the cases in `hm : p.asIdeal.IsMaximal`. Rewrite using `[if_neg (fun h => hiff.mp h hm), if_neg (fun h => h.2 (eq_maximalIdeal hm))]`. Establish `hne : p.asIdeal ≠ maximalIdeal A` using `fun h => hm (h ▸ maximalIdeal.isMaximal A)`.

Rewrite using `[if_pos (hiff.mpr hm)]`. Distinguish the cases in `hle : Module.annihilator A M ≤ p.asIdeal`. Establish `hmin : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes` using `⟨⟨p.isPrime, hle⟩, fun q hq hqp => by`. Use `hq.1` as an intermediate fact. Conclude with `(eq_of_not_max_of_le hdim hm hqp).le⟩`.

Rewrite using `[if_pos ⟨hmin, hne⟩]`. Rewrite using `[if_neg (fun h => hle h.1.le)]`. Establish `h0` using `locLen_eq_zero_of_notMem (N := M) p (by rw [Module.mem_support_iff_of_finite]; exact hle)`. Unfold `locLen at h0`. Rewrite using `[h0, zero_mul]`.
-/
theorem lengthTerm_eq (hdim : ringKrullDim A = 1) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (x : A) (p : PrimeSpectrum A) :
    (∑ᶠ (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          ordMod p x) =
      ∑ᶠ (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
          p.asIdeal ≠ maximalIdeal A),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by
  classical
  have hiff := dim_quot_eq_one_iff hdim p.asIdeal
  rw [ordMod_eq_length_quot_sup, finsum_eq_if, finsum_eq_if]
  by_cases hm : p.asIdeal.IsMaximal
  · rw [if_neg (fun h => hiff.mp h hm), if_neg (fun h => h.2 (eq_maximalIdeal hm))]
  · have hne : p.asIdeal ≠ maximalIdeal A := fun h => hm (h ▸ maximalIdeal.isMaximal A)
    rw [if_pos (hiff.mpr hm)]
    by_cases hle : Module.annihilator A M ≤ p.asIdeal
    · have hmin : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes :=
        ⟨⟨p.isPrime, hle⟩, fun q hq hqp => by
          have := hq.1
          exact (eq_of_not_max_of_le hdim hm hqp).le⟩
      rw [if_pos ⟨hmin, hne⟩]
    · rw [if_neg (fun h => hle h.1.le)]
      have h0 := locLen_eq_zero_of_notMem (N := M) p
        (by rw [Module.mem_support_iff_of_finite]; exact hle)
      unfold locLen at h0
      rw [h0, zero_mul]

end Terms

/- English proof (translation)
Introduce `A _ _ _ M _ _ _ x hdim hfin`. Establish `hq : (Ideal.span {x} • ⊤ : Submodule A M) = LinearMap.range (LinearMap.lsmul A M x)`. Rewrite using `[Submodule.ideal_span_singleton_smul, range_lsmul_eq]`. Establish `ht : Submodule.torsionBy A M x = LinearMap.ker (LinearMap.lsmul A M x)` using `rfl`. Rewrite `hfin`, the goal using `[hq]`.

Rewrite using `[ht, (h A M x hdim hfin).2]`. Use `congr 1`. Conclude with `finsum_congr (lengthTerm_eq hdim M x)`.
-/
theorem NumbersBirationalInvariance.of_lengthFormulaDimOne (h : LengthFormulaDimOne.Statement.{u, v}) :
    IndefiniteRowSideFullHecke.NumbersDVR.NumbersBirationalInvariance.Statement.{u, v} := by
  intro A _ _ _ M _ _ _ x hdim hfin
  have hq : (Ideal.span {x} • ⊤ : Submodule A M) = LinearMap.range (LinearMap.lsmul A M x) := by
    rw [Submodule.ideal_span_singleton_smul, range_lsmul_eq]
  have ht : Submodule.torsionBy A M x = LinearMap.ker (LinearMap.lsmul A M x) := rfl
  rw [hq] at hfin ⊢
  rw [ht, (h A M x hdim hfin).2]
  congr 1
  exact finsum_congr (lengthTerm_eq hdim M x)

/- English proof (translation)
The claim follows from `NumbersBirationalInvariance.of_lengthFormulaDimOne lengthFormulaDimOne`.
-/
theorem NumbersBirationalInvariance.proof : IndefiniteRowSideFullHecke.NumbersDVR.NumbersBirationalInvariance.Statement.{u, v} :=
  NumbersBirationalInvariance.of_lengthFormulaDimOne lengthFormulaDimOne

end GroundTheory.Heights₂.Heights.NumbersDVR
