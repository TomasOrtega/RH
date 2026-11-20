import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLocalEmbeddingWeilActionFiniteExtension.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.local_embedding_weil_action_finite_extension : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  first | exact @GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | exact GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | (intros; apply GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil <;> assumption)
