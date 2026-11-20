import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.Imports
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
/- English proof (translation)
Use `set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ) with hV`. Establish `: FiniteDimensional ℂ V` using `hΦ.2`. Establish `hmap : ∀ v ∈ V, d.om k v ∈ V`. Introduce `v hv`. Use `Submodule.span_induction (p := fun v _ => d.om k v ∈ V) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations.

Introduce and unpack `_ ⟨k', rfl⟩`. Use `Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, ?_⟩` and prove the remaining obligations. Simplify using `[map_mul]`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Simplify using `using V.add_mem hx hy`. Introduce `a x _ hx`. Simplify using `using V.smul_mem a hx`. Establish `hΦV : Φ ∈ V` using `Submodule.subset_span ⟨1, by simp⟩`. Use `set f : V →ₗ[ℂ] V := (d.om k).restrict hmap`.

Establish `hpow : ∀ (i : ℕ) (v : V), (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules.

Consider the case `succ i ih`. Introduce `v`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]`. Both sides reduce to the same expression. Use `⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩` and prove the remaining obligations.

Establish `h0` using `congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, hΦV⟩ : V) : d.Fn)) (minpoly.aeval ℂ f)`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum]`. Simplify `h0` using `only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero]`.
-/
theorem exists_poly_k {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ) with hV
  have : FiniteDimensional ℂ V := hΦ.2
  have hmap : ∀ v ∈ V, d.om k v ∈ V := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => d.om k v ∈ V) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, ?_⟩
      simp [map_mul]
    · simp
    · intro x y _ _ hx hy; simpa using V.add_mem hx hy
    · intro a x _ hx; simpa using V.smul_mem a hx
  have hΦV : Φ ∈ V := Submodule.subset_span ⟨1, by simp⟩
  set f : V →ₗ[ℂ] V := (d.om k).restrict hmap
  have hpow : ∀ (i : ℕ) (v : V), (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  refine ⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩
  have h0 := congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, hΦV⟩ : V) : d.Fn)) (minpoly.aeval ℂ f)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum] at h0
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero] using h0
end PositivityTheory.SiegelWeilFormula.KFP
end
end
