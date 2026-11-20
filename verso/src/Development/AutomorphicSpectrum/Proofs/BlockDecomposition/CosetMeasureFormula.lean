import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrCoset

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hO : IsOpen ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Establish `hc : ∀ k : Fin d, Continuous fun y : Fv F v ⊗[F] E => (Algebra.TensorProduct.basis (Fv F v) bs).repr y k` using `fun k => (continuous_apply k).comp (GlobalTheory.CompanionTheory.SW.TopK.isHomeomorph_coord (Fv F v) bs).continuous`. Establish `: Rv bs v = ⋂ k : Fin d, (fun y : Fv F v ⊗[F] E => (Algebra.TensorProduct.basis (Fv F v) bs).repr y k) ⁻¹' ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v))`. Use extensionality with `y`. Simplify using `[Rv]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun k => hO.preimage (hc k)`.
-/
theorem isOpen_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (Rv bs v) := by
  have hO : IsOpen ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hc : ∀ k : Fin d, Continuous fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k := fun k =>
    (continuous_apply k).comp (GlobalTheory.CompanionTheory.SW.TopK.isHomeomorph_coord (Fv F v) bs).continuous
  have : Rv bs v = ⋂ k : Fin d, (fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k) ⁻¹'
        ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) := by
    ext y
    simp [Rv]
  rw [this]
  exact isOpen_iInter_of_finite fun k => hO.preimage (hc k)

/- English proof (translation)
The claim follows from `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Fv F v) IsModuleTopology.toContinuousAdd (Fv F v) _`.
-/
theorem continuousAdd_tens (v : HeightOneSpectrum (𝓞 F)) : ContinuousAdd (Fv F v ⊗[F] E) :=
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Fv F v)
  IsModuleTopology.toContinuousAdd (Fv F v) _

/- English proof (translation)
Establish `: (H0 S σ n : Set (HermR (Fv F v) σ n)) = ⋂ i : Fin n, ⋂ j : Fin n, (fun b : HermR (Fv F v) σ n => (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) ⁻¹' (S : Set (Fv F v ⊗[F] E))`. Use extensionality with `b`. Simplify using `only [Set.mem_iInter, Set.mem_preimage]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hS.preimage (continuous_subtype_val.matrix_elem i j)`.
-/
theorem isOpen_integral_hermitian (σ : E →ₐ[F] E) (n : ℕ) {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E))
    (hS : IsOpen (S : Set (Fv F v ⊗[F] E))) :
    IsOpen (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
  have : (H0 S σ n : Set (HermR (Fv F v) σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun b : HermR (Fv F v) σ n =>
        (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) ⁻¹' (S : Set (Fv F v ⊗[F] E)) := by
    ext b
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_subtype_val.matrix_elem i j)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := continuousAdd_tens v`. Use `haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩`. Establish `hS : IsOpen (S : Set (Fv F v ⊗[F] E))`. Rewrite using `[hG.carrier]`.

Conclude with `isOpen_Rv bs v`. Use `haveI : ContinuousAdd (HermR (Fv F v) σ n) := ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd))⟩`. Use `⟨⟨fun c => (continuous_const.add continuous_id).measurable, fun c => (continuous_id.add continuous_const).measurable⟩, fun g => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun x : HermR (Fv F v) σ n => x + -g` using `continuous_id.add continuous_const`. Establish `: {x : HermR (Fv F v) σ n | x - g ∈ H0 S σ n} = (fun x : HermR (Fv F v) σ n => x + -g) ⁻¹' (H0 S σ n : Set (HermR (Fv F v) σ n))`.

Use extensionality with `x`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[this]`. Conclude with `((isOpen_integral_hermitian σ n S hS).preimage hc).measurableSet`.
-/
theorem cosetMeas : CosetMeas := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := continuousAdd_tens v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hS : IsOpen (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    exact isOpen_Rv bs v
  haveI : ContinuousAdd (HermR (Fv F v) σ n) := ⟨continuous_induced_rng.2
    ((continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd))⟩
  refine ⟨⟨fun c => (continuous_const.add continuous_id).measurable,
    fun c => (continuous_id.add continuous_const).measurable⟩, fun g => ?_⟩
  have hc : Continuous fun x : HermR (Fv F v) σ n => x + -g := continuous_id.add continuous_const
  have : {x : HermR (Fv F v) σ n | x - g ∈ H0 S σ n} =
      (fun x : HermR (Fv F v) σ n => x + -g) ⁻¹' (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
    ext x
    simp [sub_eq_add_neg]
  rw [this]
  exact ((isOpen_integral_hermitian σ n S hS).preimage hc).measurableSet

end GlobalTheory.CompanionTheory.GunrCoset

end
