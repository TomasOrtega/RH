import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x`. Use `choose y hy using hd`. Establish `hd0 : ((d : 𝓞 K) : K) ≠ 0`. Use `nonZeroDivisors.coe_ne_zero d` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hy' : ∀ i, ((y i : 𝓞 K) : K) = ((d : 𝓞 K) : K) * x i`. Introduce `i`. Use `hy i` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Conclude with `this`.

Establish `h1 : ∑ i, y i • s i = 0`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Establish `: ∀ i, algebraMap (𝓞 K') K' (y i • s i) = algebraMap K K' ((d : 𝓞 K) : K) * ((s i : K') * algebraMap K K' (x i))`. Introduce `i`.

Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K K']`. Establish `e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i` using `hy' i`. Rewrite using `[e, map_mul]`. Use `show _ * (s i : K') = _`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [this]`. Rewrite using `[← Finset.mul_sum, h, mul_zero]`. Establish `h2 : ∑ i, y i * φ (s i) = 0`. Use `congrArg φ h1` as an intermediate fact. Simplify `this` using `[map_sum]`.

Establish `h3` using `congrArg (algebraMap (𝓞 K) K) h2`. Rewrite `h3` using `[map_sum, map_zero]`. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Rewrite using `[mul_zero, Finset.mul_sum, ← h3]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Establish `e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i` using `hy' i`. Rewrite using `[e]`. Use `show _ = _ * ((φ (s i) : 𝓞 K) : K)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eigenBC_relation {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (s : Fin m → 𝓞 K') (x : Fin m → K) (φ : 𝓞 K' →ₗ[𝓞 K] 𝓞 K)
    (h : ∑ i, (s i : K') * algebraMap K K' (x i) = 0) :
    ∑ i, ((φ (s i) : 𝓞 K) : K) * x i = 0 := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose y hy using hd
  have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero d
    exact_mod_cast this
  have hy' : ∀ i, ((y i : 𝓞 K) : K) = ((d : 𝓞 K) : K) * x i := by
    intro i
    have := hy i
    rw [Algebra.smul_def] at this
    exact this
  have h1 : ∑ i, y i • s i = 0 := by
    apply RingOfIntegers.coe_injective
    rw [map_sum, map_zero]
    have : ∀ i, algebraMap (𝓞 K') K' (y i • s i)
        = algebraMap K K' ((d : 𝓞 K) : K) * ((s i : K') * algebraMap K K' (x i)) := by
      intro i
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 K) K K']
      have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
      rw [e, map_mul]
      show _ * (s i : K') = _
      ring
    simp only [this]
    rw [← Finset.mul_sum, h, mul_zero]
  have h2 : ∑ i, y i * φ (s i) = 0 := by
    have := congrArg φ h1
    simpa [map_sum] using this
  have h3 := congrArg (algebraMap (𝓞 K) K) h2
  rw [map_sum, map_zero] at h3
  apply mul_left_cancel₀ hd0
  rw [mul_zero, Finset.mul_sum, ← h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
  rw [e]
  show _ = _ * ((φ (s i) : 𝓞 K) : K)
  ring

/- English proof (translation)
Use `haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation`. Take `⟨m, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')`. Use `⟨m, fun k => f (Pi.single k 1), fun k => (LinearMap.proj k).comp g, fun s => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hfg s` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Use `conv_lhs => rw [← this, LinearMap.pi_apply_eq_sum_univ f (g s)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem eigenBC_frame (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] : ∃ (m : ℕ) (b : Fin m → 𝓞 K') (φ : Fin m → (𝓞 K' →ₗ[𝓞 K] 𝓞 K)),
      ∀ s, s = ∑ k, φ k s • b k := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  refine ⟨m, fun k => f (Pi.single k 1), fun k => (LinearMap.proj k).comp g, fun s => ?_⟩
  have := LinearMap.congr_fun hfg s
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  conv_lhs => rw [← this, LinearMap.pi_apply_eq_sum_univ f (g s)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  congr 2
  funext i
  simp [Pi.single_apply, eq_comm]

/- English proof (translation)
Introduce `K K' O _ _ _ _ _ j n Λ r τ c' _`. Establish `hmap : ∀ a (c : Fin n → K), ((r a).map j).mulVec (fun i => j (c i)) = fun i => j ((r a).mulVec c i)`. Introduce `a c`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨Submodule.span_mono (Set.image_mono fun c hc => hc.1) h, fun a => ?_⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨c, ⟨-, hc⟩, rfl⟩` from `hx`. Rewrite using `[hmap, hc a]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, smul_add]`. Consider the case `smul s x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]`. Introduce and unpack `⟨h, he⟩`. Use `letI : Algebra K K' := j.toAlgebra`. Take `⟨m, s, g, hg⟩` from `Submodule.mem_span_set'.1 h`.

Use `choose l hl hlg using fun i => (g i).2`. Establish `hc : ∀ t, c' t = ∑ i, (s i : K') * j (l i t)`. Introduce `t`. Rewrite using `[← hg, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hlg i]`. Both sides reduce to the same expression. Take `⟨p, b, φ, hb⟩` from `eigenBC_frame K K'`. Establish `hc2 : c' = ∑ k, b k • (fun t => j ((∑ i, φ k (s i) • l i) t))`. Use function extensionality and compare the values at `t`.

Rewrite using `[hc, Finset.sum_apply]`. Establish `e : ∀ i, (s i : K') = ∑ k, j ((φ k (s i) : 𝓞 K) : K) * (b k : K')`. Introduce `i`. Use `congrArg (algebraMap (𝓞 K') K') (hb (s i))` as an intermediate fact. Rewrite `this` using `[map_sum]`.

Use `this.trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K K']`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl fun i _ => by rw [e i, Finset.sum_mul], Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show _ = (b k : K') * j ((∑ i, φ k (s i) • l i) t)`. Rewrite using `[Finset.sum_apply, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show _ = (b k : K') * j (((φ k (s i) : 𝓞 K) : K) * l i t)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc2]`. Use `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Λ.sum_mem fun i _ => Λ.smul_mem _ (hl i), fun a => ?_⟩, rfl⟩)` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Establish `key` using `eigenBC_relation s (fun i => (r a).mulVec (l i) t - τ a * l i t) (φ k) (by`.

Establish `h1` using `congrFun (he a) t`. Rewrite `h1` using `[← hg, Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply, ← sub_eq_zero, ← Finset.sum_sub_distrib]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hlg i, Matrix.mulVec_smul, hmap]`.

Use `show (s i : K') * j _ = (s i : K') * j _ - j (τ a) * ((s i : K') * j (l i t))`. Rewrite using `[map_sub, map_mul]`. Use the proof step `ring)`. Rewrite using `[Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← key]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul]`. Use `show ((φ k (s i) : 𝓞 K) : K) * _ - τ a * (((φ k (s i) : 𝓞 K) : K) * l i t) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eigenLattice_baseChange : ∀ (K K' O : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [CommRing O] (j : K →+* K') (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (c' : Fin n → K'), Λ.FG → (c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) ↔ c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K))) ∧ ∀ a, ((r a).map j).mulVec c' = j (τ a) • c') := by
  intro K K' O _ _ _ _ _ j n Λ r τ c' _
  have hmap : ∀ a (c : Fin n → K), ((r a).map j).mulVec (fun i => j (c i))
      = fun i => j ((r a).mulVec c i) := by
    intro a c
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  constructor
  · intro h
    refine ⟨Submodule.span_mono (Set.image_mono fun c hc => hc.1) h, fun a => ?_⟩
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, ⟨-, hc⟩, rfl⟩ := hx
      rw [hmap, hc a]
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, smul_add]
    | smul s x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
  · rintro ⟨h, he⟩
    letI : Algebra K K' := j.toAlgebra
    obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 h
    choose l hl hlg using fun i => (g i).2
    have hc : ∀ t, c' t = ∑ i, (s i : K') * j (l i t) := by
      intro t
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i]
      rfl
    obtain ⟨p, b, φ, hb⟩ := eigenBC_frame K K'
    have hc2 : c' = ∑ k, b k • (fun t => j ((∑ i, φ k (s i) • l i) t)) := by
      funext t
      rw [hc, Finset.sum_apply]
      have e : ∀ i, (s i : K') = ∑ k, j ((φ k (s i) : 𝓞 K) : K) * (b k : K') := by
        intro i
        have := congrArg (algebraMap (𝓞 K') K') (hb (s i))
        rw [map_sum] at this
        refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply (𝓞 K) K K']
        rfl
      rw [Finset.sum_congr rfl fun i _ => by rw [e i, Finset.sum_mul], Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = (b k : K') * j ((∑ i, φ k (s i) • l i) t)
      rw [Finset.sum_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = (b k : K') * j (((φ k (s i) : 𝓞 K) : K) * l i t)
      rw [map_mul]; ring
    rw [hc2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨Λ.sum_mem fun i _ => Λ.smul_mem _ (hl i), fun a => ?_⟩, rfl⟩)
    funext t
    have key := eigenBC_relation s (fun i => (r a).mulVec (l i) t - τ a * l i t) (φ k) (by
      have h1 := congrFun (he a) t
      rw [← hg, Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i, Matrix.mulVec_smul, hmap]
      show (s i : K') * j _ = (s i : K') * j _ - j (τ a) * ((s i : K') * j (l i t))
      rw [map_sub, map_mul]; ring)
    rw [Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib, ← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul]
    show ((φ k (s i) : 𝓞 K) : K) * _ - τ a * (((φ k (s i) : 𝓞 K) : K) * l i t) = _
    ring

end GlobalTheory.CM
