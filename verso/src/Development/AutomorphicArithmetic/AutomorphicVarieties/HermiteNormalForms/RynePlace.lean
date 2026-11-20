import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hprod` using `InfinitePlace.prod_eq_abs_norm (x : L)`. Rewrite `hprod` using `[← Algebra.coe_norm_int]`. Establish `hn : Algebra.norm ℤ x ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hx`.

Establish `h1 : (1 : ℝ) ≤ ((|((Algebra.norm ℤ x : ℤ) : ℚ)| : ℚ) : ℝ)`. Use `Int.one_le_abs hn` as an intermediate fact. Rewrite using `[← Int.cast_abs]`. Conclude with `this` after adjusting the coercions. Take `⟨w0⟩` from `(inferInstance : Nonempty (InfinitePlace L))`.

Establish `hf : ∀ w : InfinitePlace L, 0 ≤ w (x : L) ^ w.mult` using `fun w => by positivity`. Establish `hlt : ∀ w : InfinitePlace L, w (x : L) ^ w.mult < 1` using `fun w => pow_lt_one₀ (by positivity) (hc w) InfinitePlace.mult_pos.ne'`. Establish `hle : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1` using `Finset.prod_le_one (fun w _ => hf w) (fun w _ => (hlt w).le)`. Establish `: ∏ w : InfinitePlace L, w (x : L) ^ w.mult < 1`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ryne_place (L : Type) [Field L] [NumberField L] (x : 𝓞 L) (hx : x ≠ 0) :
    ∃ w : InfinitePlace L, 1 ≤ w (x : L) := by
  classical
  by_contra hc
  push_neg at hc
  have hprod := InfinitePlace.prod_eq_abs_norm (x : L)
  rw [← Algebra.coe_norm_int] at hprod
  have hn : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h1 : (1 : ℝ) ≤ ((|((Algebra.norm ℤ x : ℤ) : ℚ)| : ℚ) : ℝ) := by
    have := Int.one_le_abs hn
    rw [← Int.cast_abs]
    exact_mod_cast this
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hf : ∀ w : InfinitePlace L, 0 ≤ w (x : L) ^ w.mult := fun w => by positivity
  have hlt : ∀ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := fun w =>
    pow_lt_one₀ (by positivity) (hc w) InfinitePlace.mult_pos.ne'
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => hf w) (fun w _ => (hlt w).le)
  have : ∏ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]
    calc w0 (x : L) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult
        ≤ w0 (x : L) ^ w0.mult * 1 := mul_le_mul_of_nonneg_left hle (hf w0)
      _ < 1 := by rw [mul_one]; exact hlt w0
  linarith

/- English proof (translation)
Introduce `L _ _ N`. Use `⟨mkHS (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => isHermitian_one), ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hterm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2`. Introduce `z`.

Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, y a ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hy (funext hc)`. Take `⟨w, hw⟩` from `ryne_place L (y a) ha`. Establish `hw' : ‖embO w (y a)‖ = w ((y a : 𝓞 L) : L)`. Simplify using `only [embO, RingHom.comp_apply]`. Conclude with `InfinitePlace.norm_embedding_eq w _`.

Simplify using `only [q, qR, mat_mkHS, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, hterm, toR]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.KT.ryne :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), (Ry L N).Nonempty := by
  intro L _ _ N
  refine ⟨mkHS (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => isHermitian_one), ?_⟩
  intro y hy
  have hterm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  obtain ⟨w, hw⟩ := ryne_place L (y a) ha
  have hw' : ‖embO w (y a)‖ = w ((y a : 𝓞 L) : L) := by
    simp only [embO, RingHom.comp_apply]
    exact InfinitePlace.norm_embedding_eq w _
  simp only [q, qR, mat_mkHS, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, hterm, toR]
  calc (1 : ℝ) ≤ ‖embO w (y a)‖ ^ 2 := by rw [hw']; nlinarith
    _ ≤ ∑ a', ‖embO w (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun a' => ‖embO w (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    _ ≤ ∑ w', ∑ a', ‖embO w' (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun w' => ∑ a', ‖embO w' (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ w)
