import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryOrth

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C c`. Introduce `z hz`. Rewrite using `[aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `W.smul_mem _ hz`.

Consider the case `add p q hp hq`. Introduce `z hz`. Rewrite using `[map_add, Matrix.add_mulVec]`. Conclude with `W.add_mem (hp z hz) (hq z hz)`. Consider the case `monomial m c h`.

Introduce `z hz`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]`. Conclude with `h _ (hW z hz)`.
-/
theorem aeval_mulVec_mem_of_stable {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : ∀ z ∈ W, γ *ᵥ z ∈ W) (p : K[X]) :
    ∀ z ∈ W, aeval γ p *ᵥ z ∈ W := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro z hz
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem _ hz
  | add p q hp hq =>
    intro z hz
    rw [map_add, Matrix.add_mulVec]
    exact W.add_mem (hp z hz) (hq z hz)
  | monomial m c h =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
    exact h _ (hW z hz)

/- English proof (translation)
Establish `h1 : (fun k => σ ((γ *ᵥ x) k)) = (γ.map σ) *ᵥ (fun k => σ (x k))`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Establish `h2 : ∑ k, σ ((γ *ᵥ x) k) * (γ *ᵥ z) k = (fun k => σ ((γ *ᵥ x) k)) ⬝ᵥ (γ *ᵥ z)` using `rfl`. Rewrite using `[h2, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec]`.

Both sides reduce to the same expression.
-/
theorem form_mulVec_mulVec {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (x z : Fin n → K) :
    ∑ k, σ ((γ *ᵥ x) k) * (γ *ᵥ z) k = ∑ k, σ (x k) * z k := by
  have h1 : (fun k => σ ((γ *ᵥ x) k)) = (γ.map σ) *ᵥ (fun k => σ (x k)) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : ∑ k, σ ((γ *ᵥ x) k) * (γ *ᵥ z) k = (fun k => σ ((γ *ᵥ x) k)) ⬝ᵥ (γ *ᵥ z) := rfl
  rw [h2, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hγ,
    Matrix.one_mulVec]
  rfl

/- English proof (translation)
Introduce `K _ σ n γ hγ q₁ q₂ a b hab _ V hV ι _ _ bs hG x hx y hy`. Establish `hcomm : ∀ p q : K[X], aeval γ p * aeval γ q = aeval γ q * aeval γ p`. Introduce `p q`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Establish `hVst : ∀ z ∈ V, γ *ᵥ z ∈ V`.

Introduce `z hz`. Rewrite `hz`, the goal using `[hV]`. Use `hcomm q₁ X` as an intermediate fact. Rewrite `this` using `[aeval_X]`. Rewrite using `[Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]`.

Establish `hsurj : ∀ z ∈ V, ∃ z' ∈ V, γ *ᵥ z' = z`. Introduce `z hz`. Set `f : V →ₗ[K] V` to `(Matrix.mulVecLin γ).restrict (p := V) (q := V) hVst`. Establish `hf : Function.Injective f`. Introduce `u v huv`.

Establish `h1 : γ *ᵥ (u : Fin n → K) = γ *ᵥ (v : Fin n → K)` using `congrArg Subtype.val huv`. Establish `h2` using `congrArg (fun t => (γ.map σ)ᵀ *ᵥ t) h1`. Simplify using `only [Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec] at h2`. Conclude with `Subtype.ext h2`. Take `⟨u, hu⟩` from `(LinearMap.injective_iff_surjective.mp hf) ⟨z, hz⟩`.

Conclude with `⟨u, u.2, congrArg Subtype.val hu⟩`. Set `W : Submodule K (Fin n → K)` to `{ carrier := {z | ∀ x ∈ V, ∑ k, σ (x k) * z k = 0} add_mem' := by`. Introduce `u v hu hv x hx`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu x hx, hv x hx, add_zero]`. Use the proof step `zero_mem' := by`.

Introduce `x _`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c u hu x hx`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hu x hx, mul_zero] }`.

Establish `hWmem : ∀ z, z ∈ W ↔ ∀ x ∈ V, ∑ k, σ (x k) * z k = 0` using `fun z => Iff.rfl`. Establish `hWst : ∀ z ∈ W, γ *ᵥ z ∈ W`. Introduce `z hz`. Rewrite `hz`, the goal using `[hWmem]`. Introduce `u hu`.

Take `⟨u', hu', rfl⟩` from `hsurj u hu`. Rewrite using `[form_mulVec_mulVec σ γ hγ]`. Conclude with `hz u' hu'`. Use `set G : Matrix ι ι K := Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k with hGdef`. Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hG`.

Establish `hGc : ∀ (c : ι → K) (i : ι), (G *ᵥ c) i = ∑ k, σ ((bs i : Fin n → K) k) * ((∑ j, c j • bs j : V) : Fin n → K) k`. Introduce `c i`. Simplify using `only [hGdef, Matrix.mulVec, dotProduct, Matrix.of_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hWbs : ∀ z : Fin n → K, (∀ i, ∑ k, σ ((bs i : Fin n → K) k) * z k = 0) → z ∈ W`. Introduce `z hz`. Rewrite using `[hWmem]`. Introduce `u hu`.

Establish `h1 : u = ((∑ j, bs.repr ⟨u, hu⟩ j • bs j : V) : Fin n → K)`. Rewrite using `[bs.sum_repr]`. Rewrite using `[h1]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Simplify using `only [mul_assoc, ← Finset.mul_sum, hz j, mul_zero]`. Establish `hVW : ∀ z ∈ V, z ∈ W → z = 0`. Introduce `z hz hzW`. Establish `h0 : G *ᵥ (bs.repr ⟨z, hz⟩ : ι → K) = 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[hGc, bs.sum_repr]`. Conclude with `(hWmem z).mp hzW _ (bs i).2`. Establish `h1 : (bs.repr ⟨z, hz⟩ : ι → K) = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hG h0`. Establish `h2 : bs.repr ⟨z, hz⟩ = 0`.

Use extensionality with `i`. Conclude with `congrFun h1 i`. Establish `h3 : (⟨z, hz⟩ : V) = 0` using `bs.repr.map_eq_zero_iff.mp h2`. Conclude with `congrArg Subtype.val h3`. Set `c : ι → K` to `G⁻¹ *ᵥ (fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k)`.

Set `y₁ : V` to `∑ j, c j • bs j`. Establish `hy₀ : y - (y₁ : Fin n → K) ∈ W`. Apply `hWbs` to reduce the goal to its premises. Introduce `i`. Establish `h1` using `hGc c i`.

Establish `h2 : G *ᵥ c = fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k`. Simplify using `only [c]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]`. Rewrite `h1` using `[h2]`. Simplify using `only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.

Conclude with `sub_eq_zero.mpr h1`. Establish `hq₂ : aeval γ q₂ *ᵥ (y₁ : Fin n → K) = 0`. Apply `hVW _ (aeval_mulVec_mem_of_stable γ V hVst q₂ _ y₁.2)` to reduce the goal to its premises. Establish `h1` using `W.neg_mem (aeval_mulVec_mem_of_stable γ W hWst q₂ _ hy₀)`. Rewrite `h1` using `[Matrix.mulVec_sub, hy, zero_sub, neg_neg]`. Then use the resulting hypothesis.

Establish `hq₁ : aeval γ q₁ *ᵥ (y₁ : Fin n → K) = 0` using `(hV _).mp y₁.2`. Establish `hy₁ : (y₁ : Fin n → K) = 0`. Establish `h1 : aeval γ (a * q₁ + b * q₂) *ᵥ (y₁ : Fin n → K) = y₁`. Rewrite using `[hab, map_one, Matrix.one_mulVec]`. Rewrite using `[← h1, map_add, map_mul, map_mul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hq₁, hq₂, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]`.

Rewrite `hy₀` using `[hy₁, sub_zero]`. Conclude with `(hWmem y).mp hy₀ x hx`.
-/
theorem ker_orthogonal_of_coprime :
    ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 →
    ∀ (q₁ q₂ a b : K[X]), a * q₁ + b * q₂ = 1 → aeval γ (q₁ * q₂) = 0 →
    ∀ (V : Submodule K (Fin n → K)), (∀ x, x ∈ V ↔ aeval γ q₁ *ᵥ x = 0) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (bs : Module.Basis ι K V),
    (Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k).det ≠ 0 →
    ∀ x ∈ V, ∀ y : Fin n → K, aeval γ q₂ *ᵥ y = 0 → ∑ k, σ (x k) * y k = 0 := by
  intro K _ σ n γ hγ q₁ q₂ a b hab _ V hV ι _ _ bs hG x hx y hy
  have hcomm : ∀ p q : K[X], aeval γ p * aeval γ q = aeval γ q * aeval γ p := by
    intro p q
    rw [← map_mul, ← map_mul, mul_comm]
  have hVst : ∀ z ∈ V, γ *ᵥ z ∈ V := by
    intro z hz
    rw [hV] at hz ⊢
    have := hcomm q₁ X
    rw [aeval_X] at this
    rw [Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hsurj : ∀ z ∈ V, ∃ z' ∈ V, γ *ᵥ z' = z := by
    intro z hz
    let f : V →ₗ[K] V := (Matrix.mulVecLin γ).restrict (p := V) (q := V) hVst
    have hf : Function.Injective f := by
      intro u v huv
      have h1 : γ *ᵥ (u : Fin n → K) = γ *ᵥ (v : Fin n → K) := congrArg Subtype.val huv
      have h2 := congrArg (fun t => (γ.map σ)ᵀ *ᵥ t) h1
      simp only [Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec] at h2
      exact Subtype.ext h2
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hf) ⟨z, hz⟩
    exact ⟨u, u.2, congrArg Subtype.val hu⟩
  let W : Submodule K (Fin n → K) :=
    { carrier := {z | ∀ x ∈ V, ∑ k, σ (x k) * z k = 0}
      add_mem' := by
        intro u v hu hv x hx
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu x hx, hv x hx, add_zero]
      zero_mem' := by
        intro x _
        simp
      smul_mem' := by
        intro c u hu x hx
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hu x hx,
          mul_zero] }
  have hWmem : ∀ z, z ∈ W ↔ ∀ x ∈ V, ∑ k, σ (x k) * z k = 0 := fun z => Iff.rfl
  have hWst : ∀ z ∈ W, γ *ᵥ z ∈ W := by
    intro z hz
    rw [hWmem] at hz ⊢
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hsurj u hu
    rw [form_mulVec_mulVec σ γ hγ]
    exact hz u' hu'
  set G : Matrix ι ι K :=
    Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k with hGdef
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hGc : ∀ (c : ι → K) (i : ι), (G *ᵥ c) i =
      ∑ k, σ ((bs i : Fin n → K) k) * ((∑ j, c j • bs j : V) : Fin n → K) k := by
    intro c i
    simp only [hGdef, Matrix.mulVec, dotProduct, Matrix.of_apply, Submodule.coe_sum,
      Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hWbs : ∀ z : Fin n → K, (∀ i, ∑ k, σ ((bs i : Fin n → K) k) * z k = 0) → z ∈ W := by
    intro z hz
    rw [hWmem]
    intro u hu
    have h1 : u = ((∑ j, bs.repr ⟨u, hu⟩ j • bs j : V) : Fin n → K) := by
      rw [bs.sum_repr]
    rw [h1]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hz j, mul_zero]
  have hVW : ∀ z ∈ V, z ∈ W → z = 0 := by
    intro z hz hzW
    have h0 : G *ᵥ (bs.repr ⟨z, hz⟩ : ι → K) = 0 := by
      funext i
      rw [hGc, bs.sum_repr]
      exact (hWmem z).mp hzW _ (bs i).2
    have h1 : (bs.repr ⟨z, hz⟩ : ι → K) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hG h0
    have h2 : bs.repr ⟨z, hz⟩ = 0 := by
      ext i
      exact congrFun h1 i
    have h3 : (⟨z, hz⟩ : V) = 0 := bs.repr.map_eq_zero_iff.mp h2
    exact congrArg Subtype.val h3
  let c : ι → K := G⁻¹ *ᵥ (fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k)
  let y₁ : V := ∑ j, c j • bs j
  have hy₀ : y - (y₁ : Fin n → K) ∈ W := by
    apply hWbs
    intro i
    have h1 := hGc c i
    have h2 : G *ᵥ c = fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k := by
      simp only [c]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
    rw [h2] at h1
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h1
  have hq₂ : aeval γ q₂ *ᵥ (y₁ : Fin n → K) = 0 := by
    apply hVW _ (aeval_mulVec_mem_of_stable γ V hVst q₂ _ y₁.2)
    have h1 := W.neg_mem (aeval_mulVec_mem_of_stable γ W hWst q₂ _ hy₀)
    rwa [Matrix.mulVec_sub, hy, zero_sub, neg_neg] at h1
  have hq₁ : aeval γ q₁ *ᵥ (y₁ : Fin n → K) = 0 := (hV _).mp y₁.2
  have hy₁ : (y₁ : Fin n → K) = 0 := by
    have h1 : aeval γ (a * q₁ + b * q₂) *ᵥ (y₁ : Fin n → K) = y₁ := by
      rw [hab, map_one, Matrix.one_mulVec]
    rw [← h1, map_add, map_mul, map_mul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hq₁, hq₂, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  rw [hy₁, sub_zero] at hy₀
  exact (hWmem y).mp hy₀ x hx

end GlobalTheory.UnitaryOrth
