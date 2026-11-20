import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

/- English proof (translation)
Establish `key : ∀ (R : Submodule ℂ V) (h : ∀ v ∈ R, (0 : V →ₗ[ℂ] V) v ∈ R), LinearMap.trace ℂ R ((0 : V →ₗ[ℂ] V).restrict h) = 0`. Introduce `R h`. Establish `e : (0 : V →ₗ[ℂ] V).restrict h = 0` using `rfl`. Rewrite using `[e, map_zero]`. Conclude with `⟨by rw [LinearMap.range_zero]; infer_instance, key _ _⟩`.
-/
private theorem finTrace_zero {V : Type} [AddCommGroup V] [Module ℂ V] :
    HasFinTrace (0 : V →ₗ[ℂ] V) 0 := by
  have key : ∀ (R : Submodule ℂ V) (h : ∀ v ∈ R, (0 : V →ₗ[ℂ] V) v ∈ R),
      LinearMap.trace ℂ R ((0 : V →ₗ[ℂ] V).restrict h) = 0 := by
    intro R h
    have e : (0 : V →ₗ[ℂ] V).restrict h = 0 := rfl
    rw [e, map_zero]
  exact ⟨by rw [LinearMap.range_zero]; infer_instance, key _ _⟩

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Rewrite using `[zero_smul, zero_mul]`. Conclude with `finTrace_zero`. Take `⟨hf, rfl⟩` from `h`.

Establish `key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R) (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A), LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2)`. Introduce `R hR h1 h2`. Substitute `hR` using the available equality. Establish `e : (b • A).restrict h1 = b • A.restrict h2` using `rfl`. Rewrite using `[e, map_smul, smul_eq_mul]`.

Establish `hr : LinearMap.range (b • A) = LinearMap.range A` using `LinearMap.range_smul _ _ hb`. Conclude with `⟨by rw [hr]; exact hf, key _ hr _ _⟩`.
-/
private theorem finTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, zero_mul]
    exact finTrace_zero
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

/- English proof (translation)
Introduce `v l` and use `⟨(hA v l).1.smul_measure hdt, by rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩`.
-/
private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

/- English proof (translation)
Establish `e : LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V)) = LinearMap.range A` using `LinearMap.range_comp_of_range_eq_top A (LinearEquiv.range I)`. Rewrite using `[e]`. Conclude with `h`.
-/
private theorem finite_comp {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) (I : V ≃ₗ[ℂ] V)
    (h : FiniteDimensional ℂ (LinearMap.range A)) :
    FiniteDimensional ℂ (LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V))) := by
  have e : LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V)) = LinearMap.range A :=
    LinearMap.range_comp_of_range_eq_top A (LinearEquiv.range I)
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

open UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces in
/- English proof (translation)
Introduce `G _ _ _ m τ I f`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨A, hA, hF⟩`. Conclude with `⟨_, A, hA, finite_comp A I hF.1, rfl⟩`. Introduce and unpack `t t' ⟨A, hA, -, rfl⟩ ⟨B, hB, -, rfl⟩`.

Take `rfl` from `hA.unique hB`. Both sides reduce to the same expression. Introduce `d hd`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨A, hA, hF⟩`.

Conclude with `⟨_, isInt_smul d hd hA, finTrace_smul A _ hF⟩`. Introduce and unpack `t ⟨B, hB, hF⟩`. Use `⟨_, isInt_smul d hd hB, ?_⟩` and prove the remaining obligations. Establish `e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V))` using `rfl`. Rewrite using `[e]`.

Conclude with `finTrace_smul _ _ hF`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.G.trBasic :
    UpperTheory.Gal.InertialTypesAlt.G.TrBasic := by
  intro G _ _ _ m τ I f
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨A, hA, hF⟩
    exact ⟨_, A, hA, finite_comp A I hF.1, rfl⟩
  · rintro t t' ⟨A, hA, -, rfl⟩ ⟨B, hB, -, rfl⟩
    obtain rfl := hA.unique hB
    rfl
  · intro d hd
    refine ⟨?_, ?_⟩
    · rintro z ⟨A, hA, hF⟩
      exact ⟨_, isInt_smul d hd hA, finTrace_smul A _ hF⟩
    · rintro t ⟨B, hB, hF⟩
      refine ⟨_, isInt_smul d hd hB, ?_⟩
      have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
      rw [e]
      exact finTrace_smul _ _ hF
