import Mathlib

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

/- English proof (translation)
Set `b` to `hS.eigenvectorBasis (n := Module.finrank ℂ E) rfl`. Set `ev` to `hS.eigenvalues (n := Module.finrank ℂ E) rfl`. Establish `hb : ∀ i, S (b i) = (ev i : ℂ) • b i` using `fun i => hS.apply_eigenvectorBasis rfl i`. Establish `hev : ∀ i, 0 < ev i`. Introduce `i`.

Assume the negation of the conclusion as `hc`. Conclude with `b.orthonormal.ne_zero i (h _ (not_lt.1 hc) _ (hb i))`. Establish `key : (⟪x, S x⟫_ℂ).re = ∑ i, ev i * Complex.normSq ⟪b i, x⟫_ℂ`. Rewrite using `[← b.sum_inner_mul_inner x (S x), Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hS (b i) x, hb, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b i), mul_left_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]`. Establish `hnn : ∀ i ∈ Finset.univ, 0 ≤ ev i * Complex.normSq ⟪b i, x⟫_ℂ` using `fun i _ => mul_nonneg (hev i).le (Complex.normSq_nonneg _)`. Rewrite using `[key]`. Use `⟨Finset.sum_nonneg hnn, fun h0 => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[Finset.sum_eq_zero_iff_of_nonneg hnn]`.

Establish `hz : ∀ i, ⟪b i, x⟫_ℂ = 0` using `fun i => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hev i).ne')`. Rewrite using `[← b.sum_repr' x]`. Simplify using `[hz]`.
-/
theorem pos_of_eig {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (h : ∀ t : ℝ, t ≤ 0 → ∀ x, S x = (t : ℂ) • x → x = 0) (x : E) :
    0 ≤ (⟪x, S x⟫_ℂ).re ∧ ((⟪x, S x⟫_ℂ).re = 0 → x = 0) := by
  let b := hS.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let ev := hS.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (ev i : ℂ) • b i := fun i => hS.apply_eigenvectorBasis rfl i
  have hev : ∀ i, 0 < ev i := by
    intro i
    by_contra hc
    exact b.orthonormal.ne_zero i (h _ (not_lt.1 hc) _ (hb i))
  have key : (⟪x, S x⟫_ℂ).re = ∑ i, ev i * Complex.normSq ⟪b i, x⟫_ℂ := by
    rw [← b.sum_inner_mul_inner x (S x), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS (b i) x, hb, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b i), mul_left_comm,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ev i * Complex.normSq ⟪b i, x⟫_ℂ :=
    fun i _ => mul_nonneg (hev i).le (Complex.normSq_nonneg _)
  rw [key]
  refine ⟨Finset.sum_nonneg hnn, fun h0 => ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  have hz : ∀ i, ⟪b i, x⟫_ℂ = 0 := fun i =>
    Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hev i).ne')
  rw [← b.sum_repr' x]
  simp [hz]

section Ops

variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def matOp (m : Matrix I I ℂ) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => ∑ j, m i j • Θ j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [Finset.smul_sum, smul_comm a]

def valOp (A : Module.End ℂ V) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => A (Θ i))
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matOp_apply (m : Matrix I I ℂ) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    matOp m Θ i = ∑ j, m i j • Θ j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valOp_apply (A : Module.End ℂ V) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    valOp A Θ i = A (Θ i) := rfl

/- English proof (translation)
Simplify using `only [PiLp.inner_apply, matOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, conjTranspose_apply]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem matOp_adj (m : Matrix I I ℂ) (x y : PiLp 2 (fun _ : I => V)) :
    ⟪matOp m x, y⟫_ℂ = ⟪x, matOp mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, matOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

end Ops

/- English proof (translation)
Set `R : K → Module.End ℂ (PiLp 2 (fun _ : I => V))` to `fun k => matOp (c k) + valOp (ρ k)`. Establish `hRa : ∀ k Θ i, R k Θ i = ∑ j, c k i j • Θ j + ρ k (Θ i)` using `fun k Θ i => rfl`. Establish `hRadj : ∀ k x y, ⟪R k x, y⟫_ℂ = ⟪x, R (σ k) y⟫_ℂ`. Introduce `k x y`. Simplify using `only [R, LinearMap.add_apply, inner_add_left, inner_add_right]`.

Rewrite using `[matOp_adj, h3]`. Use `congr 1`. Simplify using `only [PiLp.inner_apply, valOp_apply, hadj]`. Set `m1 : PiLp 2 (fun _ : I => V) →ₗ[ℂ] M` to `{ toFun := fun Θ => ∑ i, X i (ι (Θ i)) map_add' := fun x y => by simp [Finset.sum_add_distrib] map_smul' := fun a x => by simp [Finset.smul_sum] }`. Establish `hm1 : ∀ Θ, m1 Θ = ∑ i, X i (ι (Θ i))` using `fun _ => rfl`.

Establish `hem : ∀ k Θ, e k (m1 Θ) = m1 (R k Θ)`. Introduce `k Θ`. Establish `h1' : ∀ i y, e k (X i y) = ∑ j, c k j i • X j y + X i (e k y)`. Introduce `i y`. Use `LinearMap.congr_fun (h1 k i) y` as an intermediate fact.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at this`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Simplify using `only [hm1, hRa, map_sum, map_add, map_smul, h1', hι, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm]`.

Set `N` to `(LinearMap.ker m1)ᗮ`. Establish `hRN : ∀ k, ∀ x ∈ N, R k x ∈ N`. Introduce `k x hx`. Rewrite `hx`, the goal using `[Submodule.mem_orthogonal']`. Introduce `u hu`.

Rewrite using `[hRadj]`. Apply `hx` to reduce the goal to its premises. Rewrite `hu`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← hem, hu, map_zero]`. Set `S : Module.End ℂ (PiLp 2 (fun _ : I => V))` to `∑ k, R k * R (σ k) - ((c0 + d : ℝ) : ℂ) • 1`.

Establish `hSa : ∀ x, S x = ∑ k, R k (R (σ k) x) - ((c0 + d : ℝ) : ℂ) • x`. Introduce `x`. Simplify using `only [S, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]`. Establish `hS : LinearMap.IsSymmetric S`. Introduce `x y`.

Rewrite using `[hSa, hSa, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hRadj, hRadj, hσ]`. Establish `hSN : ∀ x ∈ N, S x ∈ N`.

Introduce `x hx`. Rewrite using `[hSa]`. Conclude with `N.sub_mem (N.sum_mem fun k _ => hRN _ _ (hRN _ _ hx)) (N.smul_mem _ hx)`. Establish `hΦN : WithLp.toLp 2 Φ ∈ N`. Rewrite using `[Submodule.mem_orthogonal']`.

Introduce `u hu`. Rewrite using `[PiLp.inner_apply]`. Conclude with `hΦ (fun i => u i) hu`. Establish `hpos` using `pos_of_eig (S.restrict hSN) (hS.restrict_invariant hSN) (by`. Introduce `t ht x hx`.

Establish `hx' : S x.1 = (t : ℂ) • x.1` using `congrArg Subtype.val hx`. Establish `h0 : m1 x.1 = 0`. Use `h5 (t + (c0 + d)) (by linarith) _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hm1]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, _, rfl⟩`.

Rewrite `hx'` using `[hSa, sub_eq_iff_eq_add, ← add_smul]`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [Module.End.mul_apply, hem]`. Rewrite using `[← map_sum, hx', map_smul]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `h2 : ⟪x.1, x.1⟫_ℂ = 0` using `(Submodule.mem_orthogonal' _ _).1 x.2 _ h0`. Conclude with `Subtype.ext (inner_self_eq_zero.1 h2)) ⟨_, hΦN⟩`. Establish `hval : ∀ i, S (WithLp.toLp 2 Φ) i = (2 : ℂ) • ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j)`. Introduce `i`.

Establish `e1 : ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l = (d : ℂ) • Φ i`. Establish `: ∀ l, ∑ k, ∑ j, c k i j * c (σ k) j l = (d : ℂ) * (if i = l then 1 else 0)`. Introduce `l`. Use `congrFun (congrFun h4 i) l` as an intermediate fact. Simplify `this` using `[Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.smul_sum, smul_smul]`. Use `_ = ∑ l, (∑ k, ∑ j, c k i j * c (σ k) j l) • Φ l := by`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_smul]`. Use `_ = (d : ℂ) • Φ i := by simp [this]`. Establish `e2 : ∑ k, ρ k (ρ (σ k) (Φ i)) = (c0 : ℂ) • Φ i`. Use `LinearMap.congr_fun hc0 (Φ i)` as an intermediate fact.

Simplify `this` using `[LinearMap.sum_apply]`. Establish `e3 : ∑ k, ρ k (∑ l, c (σ k) i l • Φ l) = ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j)`. Rewrite using `[← Equiv.sum_comp hσ.toPerm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Function.Involutive.coe_toPerm, hσ k, map_sum, map_smul]`.

Establish `e4 : S (WithLp.toLp 2 Φ) i = ∑ k, R k (R (σ k) (WithLp.toLp 2 Φ)) i - ((c0 + d : ℝ) : ℂ) • Φ i`. Rewrite using `[hSa]`. Simplify using the standard rewrite rules. Rewrite using `[e4]`. Simplify using `only [hRa, smul_add, map_add, Finset.sum_add_distrib]`.

Rewrite using `[e1, e2, e3, two_smul]`. Use `push_cast`. Rewrite using `[add_smul]`. Normalize the expressions using the abelian group laws. Establish `hin : (⟪(⟨_, hΦN⟩ : N), S.restrict hSN ⟨_, hΦN⟩⟫_ℂ) = 2 * ∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ`.

Express the relevant statement in the definitionally equal form `⟪WithLp.toLp 2 Φ, S (WithLp.toLp 2 Φ)⟫_ℂ = _`. Rewrite using `[PiLp.inner_apply, Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hval, inner_smul_right]`. Simplify using `only [inner_sum]`.

Rewrite `hpos` using `[hin]`. Establish `h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re` using `fun z => by simp`. Rewrite `hpos` using `[h2re]`. Use `⟨by linarith [hpos.1], fun h0 => ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hpos.2 (by rw [h0, mul_zero]))` as an intermediate fact.

Use function extensionality and compare the values at `i`. Conclude with `congrArg (fun z : PiLp 2 (fun _ : I => V) => z i) this`.
-/
theorem cas_one {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (Φ : I → V) (hΦ : ∀ Θ : I → V, ∑ i, X i (ι (Θ i)) = 0 → ∑ i, ⟪Φ i, Θ i⟫_ℂ = 0) :
    0 ≤ (∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re = 0 → Φ = 0) := by
  let R : K → Module.End ℂ (PiLp 2 (fun _ : I => V)) := fun k => matOp (c k) + valOp (ρ k)
  have hRa : ∀ k Θ i, R k Θ i = ∑ j, c k i j • Θ j + ρ k (Θ i) := fun k Θ i => rfl
  have hRadj : ∀ k x y, ⟪R k x, y⟫_ℂ = ⟪x, R (σ k) y⟫_ℂ := by
    intro k x y
    simp only [R, LinearMap.add_apply, inner_add_left, inner_add_right]
    rw [matOp_adj, h3]
    congr 1
    simp only [PiLp.inner_apply, valOp_apply, hadj]
  let m1 : PiLp 2 (fun _ : I => V) →ₗ[ℂ] M :=
    { toFun := fun Θ => ∑ i, X i (ι (Θ i))
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.smul_sum] }
  have hm1 : ∀ Θ, m1 Θ = ∑ i, X i (ι (Θ i)) := fun _ => rfl
  have hem : ∀ k Θ, e k (m1 Θ) = m1 (R k Θ) := by
    intro k Θ
    have h1' : ∀ i y, e k (X i y) = ∑ j, c k j i • X j y + X i (e k y) := by
      intro i y
      have := LinearMap.congr_fun (h1 k i) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at this
      rw [← this]; abel
    simp only [hm1, hRa, map_sum, map_add, map_smul, h1', hι, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  let N := (LinearMap.ker m1)ᗮ
  have hRN : ∀ k, ∀ x ∈ N, R k x ∈ N := by
    intro k x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hRadj]
    apply hx
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← hem, hu, map_zero]
  let S : Module.End ℂ (PiLp 2 (fun _ : I => V)) := ∑ k, R k * R (σ k) - ((c0 + d : ℝ) : ℂ) • 1
  have hSa : ∀ x, S x = ∑ k, R k (R (σ k) x) - ((c0 + d : ℝ) : ℂ) • x := by
    intro x
    simp only [S, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  have hS : LinearMap.IsSymmetric S := by
    intro x y
    rw [hSa, hSa, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hRadj, hRadj, hσ]
  have hSN : ∀ x ∈ N, S x ∈ N := by
    intro x hx
    rw [hSa]
    exact N.sub_mem (N.sum_mem fun k _ => hRN _ _ (hRN _ _ hx)) (N.smul_mem _ hx)
  have hΦN : WithLp.toLp 2 Φ ∈ N := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [PiLp.inner_apply]
    exact hΦ (fun i => u i) hu
  have hpos := pos_of_eig (S.restrict hSN) (hS.restrict_invariant hSN) (by
    intro t ht x hx
    have hx' : S x.1 = (t : ℂ) • x.1 := congrArg Subtype.val hx
    have h0 : m1 x.1 = 0 := by
      refine h5 (t + (c0 + d)) (by linarith) _ ?_ ?_
      · rw [hm1]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, _, rfl⟩
      · rw [hSa, sub_eq_iff_eq_add, ← add_smul] at hx'
        rw [LinearMap.sum_apply]
        simp only [Module.End.mul_apply, hem]
        rw [← map_sum, hx', map_smul]
        push_cast
        rfl
    have h2 : ⟪x.1, x.1⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 x.2 _ h0
    exact Subtype.ext (inner_self_eq_zero.1 h2)) ⟨_, hΦN⟩
  have hval : ∀ i, S (WithLp.toLp 2 Φ) i = (2 : ℂ) • ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
    intro i
    have e1 : ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l = (d : ℂ) • Φ i := by
      have : ∀ l, ∑ k, ∑ j, c k i j * c (σ k) j l = (d : ℂ) * (if i = l then 1 else 0) := by
        intro l
        have := congrFun (congrFun h4 i) l
        simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
      calc ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l
          = ∑ k, ∑ l, ∑ j, (c k i j * c (σ k) j l) • Φ l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum, smul_smul]
        _ = ∑ l, (∑ k, ∑ j, c k i j * c (σ k) j l) • Φ l := by
            rw [Finset.sum_comm]
            simp only [Finset.sum_smul]
        _ = (d : ℂ) • Φ i := by simp [this]
    have e2 : ∑ k, ρ k (ρ (σ k) (Φ i)) = (c0 : ℂ) • Φ i := by
      have := LinearMap.congr_fun hc0 (Φ i)
      simpa [LinearMap.sum_apply] using this
    have e3 : ∑ k, ρ k (∑ l, c (σ k) i l • Φ l) = ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
      rw [← Equiv.sum_comp hσ.toPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.Involutive.coe_toPerm, hσ k, map_sum, map_smul]
    have e4 : S (WithLp.toLp 2 Φ) i = ∑ k, R k (R (σ k) (WithLp.toLp 2 Φ)) i - ((c0 + d : ℝ) : ℂ) • Φ i := by
      rw [hSa]
      simp
    rw [e4]
    simp only [hRa, smul_add, map_add, Finset.sum_add_distrib]
    rw [e1, e2, e3, two_smul]
    push_cast
    rw [add_smul]
    abel
  have hin : (⟪(⟨_, hΦN⟩ : N), S.restrict hSN ⟨_, hΦN⟩⟫_ℂ) =
      2 * ∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ := by
    change ⟪WithLp.toLp 2 Φ, S (WithLp.toLp 2 Φ)⟫_ℂ = _
    rw [PiLp.inner_apply, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval, inner_smul_right]
    simp only [inner_sum]
  rw [hin] at hpos
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [h2re] at hpos
  refine ⟨by linarith [hpos.1], fun h0 => ?_⟩
  have := congrArg Subtype.val (hpos.2 (by rw [h0, mul_zero]))
  funext i
  exact congrArg (fun z : PiLp 2 (fun _ : I => V) => z i) this

end PositivityTheory.KReal

end
