import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDense

/- English proof (translation)
Use `letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _`. Use `letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `: CharZero (w.adicCompletion E)` using `charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Establish `hdE : DenseRange (algebraMap E (w.adicCompletion E))` using `HeightOneSpectrum.denseRange_algebraMap E w`.

Establish `hd : DenseRange ι` using `GlobalTheory.LocDec.denseRange_of_isAlgClosed (w.adicCompletion E) E Ω hdE ι`. Establish `hnorm : ∀ (g : GalLoc w) (y : Kbar w), ‖g y‖ = ‖y‖` using `fun g y => (spectralNorm_eq_of_equiv g y).symm`. Establish `hcont : ∀ g : GalLoc w, Continuous g` using `fun g => (AddMonoidHomClass.isometry_of_norm g (hnorm g)).continuous`. Use `hd.equalizer (hcont a) (hcont b) (funext fun x => by` as an intermediate fact. Simplify using `only [Function.comp_apply]`.

Rewrite using `[ha x, hb x])`. Conclude with `AlgEquiv.ext (congrFun this)`.
-/
theorem lifts_eq_of_lifts {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} (ι : Ω →ₐ[E] Kbar w) (a b : GalLoc w) (σ : G E Ω)
    (ha : Lifts ι a σ) (hb : Lifts ι b σ) : a = b := by
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hdE : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
  have hd : DenseRange ι := GlobalTheory.LocDec.denseRange_of_isAlgClosed (w.adicCompletion E) E Ω hdE ι
  have hnorm : ∀ (g : GalLoc w) (y : Kbar w), ‖g y‖ = ‖y‖ := fun g y =>
    (spectralNorm_eq_of_equiv g y).symm
  have hcont : ∀ g : GalLoc w, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm g (hnorm g)).continuous
  have := hd.equalizer (hcont a) (hcont b) (funext fun x => by
    simp only [Function.comp_apply]; rw [ha x, hb x])
  exact AlgEquiv.ext (congrFun this)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h ι hι g τ hτ U hU V hV hgV`. Take `⟨θ, hθ, hθs, hl⟩` from `GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι`. Establish `hτθ : τ = θ g` using `lifts_eq_of_lifts ι _ _ _ hτ (hl g)`. Set `W : Set (GalLoc w)` to `θ.symm ⁻¹' V`. Establish `hW : IsOpen W` using `hV.preimage hθs`.

Establish `hτW : τ ∈ W` using `by show θ.symm τ ∈ V`. Rewrite using `[hτθ, MulEquiv.symm_apply_apply]`. Conclude with `hgV`. Establish `hnhds : {x : GalLoc w | τ * x ∈ W} ∈ nhds (1 : GalLoc w)`. Apply `(continuous_mul_left τ).continuousAt.preimage_mem_nhds` to reduce the goal to its premises.

Simplify using `using hW.mem_nhds hτW`. Take `⟨L, hL, hLs⟩` from `(krullTopology_mem_nhds_one_iff _ _ _).mp hnhds`. Set `H : Subgroup (GalLoc w)` to `U ⊓ L.fixingSubgroup`. Establish `hH : IsOpen (H : Set (GalLoc w))`. Establish `h2 : IsOpen (L.fixingSubgroup : Set (GalLoc w))` using `by haveI := hL`.

Conclude with `IntermediateField.fixingSubgroup_isOpen L`. Conclude with `hU.inter h2`. Take `⟨σ, g', hg', hmem⟩` from `GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl τ H hH`. Use `⟨σ, g', hg', hmem.1, ?_⟩` and prove the remaining obligations. Establish `e : g' = θ ⟨σ, Weil_le_Dec h σ.2⟩` using `lifts_eq_of_lifts ι _ _ _ hg' (hl _)`.

Establish `h3 : τ * (τ⁻¹ * g') ∈ W` using `hLs hmem.2`. Rewrite `h3` using `[mul_inv_cancel_left]`. Establish `h4 : θ.symm g' ∈ V` using `h3`. Rewrite `h4` using `[e, MulEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem weil_dense : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w),
    IsLocEmb A w ι → ∀ (g : Dec (F := E) A) (τ : GalLoc w), Lifts ι τ (g : G E Ω) →
    ∀ (U : Subgroup (GalLoc w)), IsOpen (U : Set (GalLoc w)) → ∀ (V : Set (Dec (F := E) A)), IsOpen V → g ∈ V →
    ∃ (σ : Weil h) (τ' : GalLoc w), Lifts ι τ' (σ : G E Ω) ∧ τ⁻¹ * τ' ∈ U ∧
      (⟨σ, Weil_le_Dec h σ.2⟩ : Dec (F := E) A) ∈ V := by
  intro E Ω _ _ _ _ _ A w h ι hι g τ hτ U hU V hV hgV
  obtain ⟨θ, hθ, hθs, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  have hτθ : τ = θ g := lifts_eq_of_lifts ι _ _ _ hτ (hl g)
  let W : Set (GalLoc w) := θ.symm ⁻¹' V
  have hW : IsOpen W := hV.preimage hθs
  have hτW : τ ∈ W := by
    show θ.symm τ ∈ V
    rw [hτθ, MulEquiv.symm_apply_apply]; exact hgV
  have hnhds : {x : GalLoc w | τ * x ∈ W} ∈ nhds (1 : GalLoc w) := by
    apply (continuous_mul_left τ).continuousAt.preimage_mem_nhds
    simpa using hW.mem_nhds hτW
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hnhds
  let H : Subgroup (GalLoc w) := U ⊓ L.fixingSubgroup
  have hH : IsOpen (H : Set (GalLoc w)) := by
    have h2 : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := by
      haveI := hL
      exact IntermediateField.fixingSubgroup_isOpen L
    exact hU.inter h2
  obtain ⟨σ, g', hg', hmem⟩ := GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl τ H hH
  refine ⟨σ, g', hg', hmem.1, ?_⟩
  have e : g' = θ ⟨σ, Weil_le_Dec h σ.2⟩ := lifts_eq_of_lifts ι _ _ _ hg' (hl _)
  have h3 : τ * (τ⁻¹ * g') ∈ W := hLs hmem.2
  rw [mul_inv_cancel_left] at h3
  have h4 : θ.symm g' ∈ V := h3
  rwa [e, MulEquiv.symm_apply_apply] at h4

end GlobalTheory.WeilDense
