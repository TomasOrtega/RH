import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalArtinExists

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.WeilRes

open Pointwise

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Use `⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => ?_⟩` and prove the remaining obligations. Use `show σ • A = A`. Use extensionality with `y`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]`.
-/
theorem mem_Dec_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ ∀ x, (σ x ∈ A ↔ x ∈ A) := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => ?_⟩
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]`.
-/
theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/- English proof (translation)
Use `eq_of_isPlaceOver (A := A) ?_ h` and prove the remaining obligations. Introduce `x`. Use `show _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal`. Rewrite using `[← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]`. Both sides reduce to the same expression.
-/
theorem under_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v)
    (h' : IsPlaceOver A w) : w.under (𝓞 K) = v := by
  refine eq_of_isPlaceOver (A := A) ?_ h
  intro x
  show _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
  rw [← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ((x.isIntegral_coe).algebraMap))`.
-/
theorem val_le_one {L : Type} [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω x) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ((x.isIntegral_coe).algebraMap))

section Res

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

end Res

end GlobalTheory.DelEps.WeilRes
