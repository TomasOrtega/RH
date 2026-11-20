import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem toReal_mem_psdCone_of_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone H.bar X := by
  intro E _ _ _ H X _ _ _ _ β hβ hp
  have h := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 (fun _ => β) (fun _ => 1)
    (fun _ => hβ) (fun _ y => hp y) (fun _ => zero_le_one)
  simpa using h

end GlobalTheory.PolFan
