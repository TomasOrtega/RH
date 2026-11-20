import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `W _`. Set `𝒰` to `W.affineCover.finiteSubcover`. Use `⟨∐ 𝒰.X, Sigma.desc 𝒰.f, inferInstance, ?_, inferInstance⟩` and prove the remaining obligations. Establish `: IsZariskiLocalAtSource @Etale` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance`.
-/
theorem exists_affine_etale_surjective :
    ∀ (W : Scheme.{0}) [CompactSpace W], ∃ (V : Scheme.{0}) (f : V ⟶ W), IsAffine V ∧ Etale f ∧ Surjective f := by
  intro W _
  let 𝒰 := W.affineCover.finiteSubcover
  refine ⟨∐ 𝒰.X, Sigma.desc 𝒰.f, inferInstance, ?_, inferInstance⟩
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance

end GlobalTheory
