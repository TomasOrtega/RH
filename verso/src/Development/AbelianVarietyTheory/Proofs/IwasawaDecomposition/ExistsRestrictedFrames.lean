import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem

/- English proof (translation)
Establish `key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ), ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u`. Introduce `ι _ M`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Use `push_cast`. Simplify using `only [dotProduct, Pi.star_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.star_def, Complex.conj_mul']`. Establish `h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2`. Use `key M` as an intermediate fact. Rewrite `this` using `[h, ← key N]`.

Conclude with `this` after adjusting the coercions. Unfold `Formalism.HermitianLatticesTheory.cnorm`. Rewrite using `[h2]`.
-/
theorem cnorm_mulVec_eq_of_gram {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι μ ℂ) (N : Matrix κ μ ℂ) (h : Mᴴ * M = Nᴴ * N) (u : μ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M.mulVec u) = Formalism.HermitianLatticesTheory.cnorm (N.mulVec u) := by
  have key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ),
      ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u := by
    intro ι _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2 := by
    have := key M
    rw [h, ← key N] at this
    exact_mod_cast this
  unfold Formalism.HermitianLatticesTheory.cnorm
  rw [h2]

/- English proof (translation)
Introduce `K _ _ _ A U _ hX`. Establish `: Module.Finite K A.V` using `Module.Finite.of_basis A.b`. Set `n` to `Module.finrank K U`. Set `b : Module.Basis (Fin n) K U` to `Module.finBasis K U`. Set `E : Matrix A.ι (Fin n) K` to `LinearMap.toMatrix b A.b U.subtype`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype`. Establish `hLE : LinearMap.toMatrix A.b b g * E = 1`. Rewrite using `[← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]`. Set `M : InfinitePlace K → Matrix A.ι (Fin n) ℂ` to `fun v => (A.X v)⁻¹ * E.map v.embedding`. Establish `hM : ∀ v, Function.Injective (M v).mulVec`.

Introduce `v x y hxy`. Establish `h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1`. Simplify using `only [M]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']`. Use `congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `hP : ∀ v, ((M v)ᴴ * M v).PosDef` using `fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)`. Use `⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v), fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩` and prove the remaining obligations. Establish `h2` using `(Formalism.L2.DIV.frameOfSpec n _ (hP v)).2`. Establish `h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)`.

Establish `h4` using `LinearMap.toMatrix_mulVec_repr b A.b U.subtype x`. Use function extensionality and compare the values at `i`. Establish `h5` using `congrFun h4 i`. Simplify using `only [Submodule.subtype_apply] at h5`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt]`.

Rewrite using `[← h5]`. Simplify using `[Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord`. Rewrite using `[h3, Matrix.mulVec_mulVec]`. Conclude with `cnorm_mulVec_eq_of_gram _ _ h2 _`.
-/
theorem exists_restricted_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (U : Submodule K A.V) (L : Submodule (𝓞 K) U), (∀ v, IsUnit (A.X v).det) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K U) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      (∀ v, IsUnit (X v).det) ∧
        ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (x : A.V) := by
  intro K _ _ _ A U _ hX
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  let n := Module.finrank K U
  let b : Module.Basis (Fin n) K U := Module.finBasis K U
  let E : Matrix A.ι (Fin n) K := LinearMap.toMatrix b A.b U.subtype
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  have hLE : LinearMap.toMatrix A.b b g * E = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  let M : InfinitePlace K → Matrix A.ι (Fin n) ℂ := fun v => (A.X v)⁻¹ * E.map v.embedding
  have hM : ∀ v, Function.Injective (M v).mulVec := by
    intro v x y hxy
    have h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1 := by
      simp only [M]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']
    have := congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hP : ∀ v, ((M v)ᴴ * M v).PosDef := fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)
  refine ⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v),
    fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩
  have h2 := (Formalism.L2.DIV.frameOfSpec n _ (hP v)).2
  have h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have h4 := LinearMap.toMatrix_mulVec_repr b A.b U.subtype x
    funext i
    have h5 := congrFun h4 i
    simp only [Submodule.subtype_apply] at h5
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← h5]
    simp [Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [h3, Matrix.mulVec_mulVec]
  exact cnorm_mulVec_eq_of_gram _ _ h2 _

end GlobalTheory.Mem

end
