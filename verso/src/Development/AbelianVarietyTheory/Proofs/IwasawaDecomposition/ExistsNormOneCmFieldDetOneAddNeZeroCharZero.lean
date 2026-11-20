import Mathlib
open NumberField

namespace GlobalTheory.CMScalar
open Matrix Polynomial

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b : 2`. Apply the tactic sequence `by_cases h : a = b <;> simp [h, mul_comm w, sub_eq_add_neg]`.
-/
theorem eval_charpolyRev_neg {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (w : K) :
    (-A).charpolyRev.eval w = (1 + w • A).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm w, sub_eq_add_neg]

/- English proof (translation)
Use `set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => IsCMField.complexConj_apply_apply L x`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : L, c y ≠ y := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `IsCMField.complexConj_ne_one L` to reduce the goal to its premises. Use extensionality with `x`. Conclude with `h x`. Use `set i : L := y - c y with hi`. Establish `hi0 : i ≠ 0` using `sub_ne_zero.2 (Ne.symm hy)`.

Establish `hci : c i = -i` using `by rw [hi, map_sub, hcc]; ring`. Establish `hden : ∀ t : ℚ, (1 : L) + (t : L) * i ≠ 0`. Introduce `t h`. Establish `h1 : (t : L) * i = -1` using `by linear_combination h`. Establish `h2` using `congrArg c h1`.

Rewrite `h2` using `[map_mul, map_ratCast, hci, map_neg, map_one]`. Establish `: (2 : L) = 0` using `by linear_combination h1 + h2`. Conclude with `two_ne_zero this`. Set `f : ℚ → L` to `fun t => (1 - (t : L) * i) / (1 + (t : L) * i)`. Establish `hfu : ∀ t, f t * c (f t) = 1`.

Introduce `t`. Establish `hd` using `hden t`. Establish `hd' : (1 : L) - (t : L) * i ≠ 0`. Introduce `h`. Apply `hden (-t)` to reduce the goal to its premises.

Use `push_cast`. Take the linear combination `h`. Establish `e : c (f t) = (1 + (t : L) * i) / (1 - (t : L) * i)`. Simplify using `only [f, map_div₀, map_sub, map_add, map_one, map_mul, map_ratCast, hci]`. Apply the tactic sequence `congr 1 <;> ring`.

Rewrite using `[e, div_mul_div_comm]`. Conclude with `(div_eq_one_iff_eq (mul_ne_zero hd hd')).2 (by ring)`. Establish `hfinj : Function.Injective f`. Introduce `s t hst`. Simplify using `only [f] at hst`.

Rewrite `hst` using `[div_eq_div_iff (hden s) (hden t)]`. Establish `h2 : (2 : L) * ((t : L) - s) * i = 0` using `by linear_combination hst`. Establish `: ((t : L) - s) = 0`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `absurd h two_ne_zero`. Conclude with `h`. Conclude with `absurd h hi0`. Establish `: ((t - s : ℚ) : L) = 0` using `by push_cast; exact this`. Conclude with `(sub_eq_zero.1 (Rat.cast_eq_zero.1 this)).symm`.

Establish `hp : ∀ σ : L →+* K, (-(M σ)).charpolyRev ≠ 0`. Introduce `σ h`. Use `Matrix.eval_charpolyRev (M := -(M σ))` as an intermediate fact. Rewrite `this` using `[h, Polynomial.eval_zero]`. Conclude with `zero_ne_one this`.

Set `B : Set L` to `⋃ σ : L →+* K, σ ⁻¹' ((-(M σ)).charpolyRev.roots.toFinset : Set K)`. Establish `hB : B.Finite`. Apply `Set.finite_iUnion` to reduce the goal to its premises. Introduce `σ`. Conclude with `(Finset.finite_toSet _).preimage σ.injective.injOn`.

Establish `hS : (f ⁻¹' B).Finite` using `hB.preimage hfinj.injOn`. Take `⟨t, ht⟩` from `(Set.infinite_univ (α := ℚ)).diff hS |>.nonempty`. Use `⟨f t, hfu t, fun σ hσ => ht.2 ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, B, Set.mem_iUnion]`. Use `⟨σ, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_roots (hp σ), Polynomial.IsRoot, eval_charpolyRev_neg]`. Conclude with `hσ`.
-/
theorem exists_unit_norm_one_det_ne_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K]
    [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K) :
    ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨y, hy⟩ : ∃ y : L, c y ≠ y := by
    by_contra h
    push_neg at h
    apply IsCMField.complexConj_ne_one L
    ext x
    exact h x
  set i : L := y - c y with hi
  have hi0 : i ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hci : c i = -i := by rw [hi, map_sub, hcc]; ring
  have hden : ∀ t : ℚ, (1 : L) + (t : L) * i ≠ 0 := by
    intro t h
    have h1 : (t : L) * i = -1 := by linear_combination h
    have h2 := congrArg c h1
    rw [map_mul, map_ratCast, hci, map_neg, map_one] at h2
    have : (2 : L) = 0 := by linear_combination h1 + h2
    exact two_ne_zero this
  let f : ℚ → L := fun t => (1 - (t : L) * i) / (1 + (t : L) * i)
  have hfu : ∀ t, f t * c (f t) = 1 := by
    intro t
    have hd := hden t
    have hd' : (1 : L) - (t : L) * i ≠ 0 := by
      intro h; apply hden (-t); push_cast; linear_combination h
    have e : c (f t) = (1 + (t : L) * i) / (1 - (t : L) * i) := by
      simp only [f, map_div₀, map_sub, map_add, map_one, map_mul, map_ratCast, hci]
      congr 1 <;> ring
    rw [e, div_mul_div_comm]
    exact (div_eq_one_iff_eq (mul_ne_zero hd hd')).2 (by ring)
  have hfinj : Function.Injective f := by
    intro s t hst
    simp only [f] at hst
    rw [div_eq_div_iff (hden s) (hden t)] at hst
    have h2 : (2 : L) * ((t : L) - s) * i = 0 := by linear_combination hst
    have : ((t : L) - s) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h two_ne_zero
        · exact h
      · exact absurd h hi0
    have : ((t - s : ℚ) : L) = 0 := by push_cast; exact this
    exact (sub_eq_zero.1 (Rat.cast_eq_zero.1 this)).symm
  have hp : ∀ σ : L →+* K, (-(M σ)).charpolyRev ≠ 0 := by
    intro σ h
    have := Matrix.eval_charpolyRev (M := -(M σ))
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  let B : Set L := ⋃ σ : L →+* K, σ ⁻¹' ((-(M σ)).charpolyRev.roots.toFinset : Set K)
  have hB : B.Finite := by
    apply Set.finite_iUnion
    intro σ
    exact (Finset.finite_toSet _).preimage σ.injective.injOn
  have hS : (f ⁻¹' B).Finite := hB.preimage hfinj.injOn
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hS |>.nonempty
  refine ⟨f t, hfu t, fun σ hσ => ht.2 ?_⟩
  simp only [Set.mem_preimage, B, Set.mem_iUnion]
  refine ⟨σ, ?_⟩
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (hp σ), Polynomial.IsRoot, eval_charpolyRev_neg]
  exact hσ

end GlobalTheory.CMScalar
