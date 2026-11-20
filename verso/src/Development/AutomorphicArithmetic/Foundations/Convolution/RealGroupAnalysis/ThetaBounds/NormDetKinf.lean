import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Transl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OneOf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Establish `h : star k.1 * k.1 = 1` using `by simp`. Establish `hd : star (k.1.det) * k.1.det = 1`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one]`. Then use the resulting hypothesis. Establish `hw : star (k.1.det w) * k.1.det w = 1` using `congrFun hd w`.

Establish `hn : ‖k.1.det w‖ * ‖k.1.det w‖ = 1`. Use `congrArg norm hw` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_star, norm_one]`. Then use the resulting hypothesis. Establish `h0 : 0 ≤ ‖k.1.det w‖` using `norm_nonneg _`. Express the relevant statement in the definitionally equal form `‖k.1.det w‖ = 1`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem norm_det_kinf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (k : Kinf E 2)
    (w : InfinitePlace E) : ‖(Unitary.toUnits k).val.det w‖ = 1 := by
  have h : star k.1 * k.1 = 1 := by simp
  have hd : star (k.1.det) * k.1.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at this
  have hw : star (k.1.det w) * k.1.det w = 1 := congrFun hd w
  have hn : ‖k.1.det w‖ * ‖k.1.det w‖ = 1 := by
    have := congrArg norm hw
    rwa [norm_mul, norm_star, norm_one] at this
  have h0 : 0 ≤ ‖k.1.det w‖ := norm_nonneg _
  change ‖k.1.det w‖ = 1
  nlinarith

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dM]`.
-/
private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ`. Establish `hl` using `lin F E D W M π`. Take `⟨U, hUF, hfd, hU⟩` from `(fockSt F E D W).cpt φ hφ`. Establish `key : ∀ k : Kinf E 2, (cptRep E 2 k Φ).1 = lift W M f.1 (W.L (infGL E 2 (Unitary.toUnits k)) φ)`. Introduce `k`.

Use function extensionality and compare the values at `h`. Establish `h1 : nu F (infGL E 2 (Unitary.toUnits k)) = 1` using `oneOf F E D (Unitary.toUnits k) (norm_det_kinf k)`. Establish `h2` using `transl F E D W M f.1 φ h (infGL E 2 (Unitary.toUnits k))`. Rewrite `h2` using `[h1, dM_one']`. Simplify using `only [mul_one] at h2`.

Express the relevant statement in the definitionally equal form `Φ.1 (h * infGL E 2 (Unitary.toUnits k)) = _`. Rewrite using `[hΦ]`. Conclude with `h2`. Use `⟨fun k => Submodule.subset_span ⟨f, hf, _, hUF (hU k), key k⟩, ?_⟩` and prove the remaining obligations. Use `haveI := hfd`.

Set `T : U →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)` to `{ toFun := fun u => lift W M f.1 u.1 map_add' := fun u u' => hl.1 f hf u.1 (hUF u.2) u'.1 (hUF u'.2) map_smul' := fun c u => hl.2.1 f.1 c u.1 }`. Establish `hle : (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype ≤ LinearMap.range T`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨⟨_, hU k⟩, (key k).symm⟩`.

Use `haveI : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype) := Submodule.finiteDimensional_of_le hle`. Conclude with `(Submodule.equivMapOfInjective (Sm E 2).subtype (Submodule.injective_subtype _) _).symm.finiteDimensional`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.kFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), KFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  have hl := lin F E D W M π
  obtain ⟨U, hUF, hfd, hU⟩ := (fockSt F E D W).cpt φ hφ
  have key : ∀ k : Kinf E 2, (cptRep E 2 k Φ).1 = lift W M f.1 (W.L (infGL E 2 (Unitary.toUnits k)) φ) := by
    intro k
    funext h
    have h1 : nu F (infGL E 2 (Unitary.toUnits k)) = 1 :=
      oneOf F E D (Unitary.toUnits k) (norm_det_kinf k)
    have h2 := transl F E D W M f.1 φ h (infGL E 2 (Unitary.toUnits k))
    rw [h1, dM_one'] at h2
    simp only [mul_one] at h2
    change Φ.1 (h * infGL E 2 (Unitary.toUnits k)) = _
    rw [hΦ]
    exact h2
  refine ⟨fun k => Submodule.subset_span ⟨f, hf, _, hUF (hU k), key k⟩, ?_⟩
  haveI := hfd
  let T : U →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun u => lift W M f.1 u.1
      map_add' := fun u u' => hl.1 f hf u.1 (hUF u.2) u'.1 (hUF u'.2)
      map_smul' := fun c u => hl.2.1 f.1 c u.1 }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype ≤ LinearMap.range T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨_, hU k⟩, (key k).symm⟩
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact (Submodule.equivMapOfInjective (Sm E 2).subtype (Submodule.injective_subtype _) _).symm.finiteDimensional
