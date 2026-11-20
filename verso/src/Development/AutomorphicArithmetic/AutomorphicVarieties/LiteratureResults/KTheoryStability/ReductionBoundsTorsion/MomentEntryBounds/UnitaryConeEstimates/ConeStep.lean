import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `l q hq`. Establish `: q = l` using `Fin.ext (by simpa using hq)`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `l q hq`. Establish `hlt : (l : ℕ) + d < N` using `by have := q.isLt; omega`.

Establish `h1` using `ih l ⟨(l : ℕ) + d, hlt⟩ rfl`. Establish `h2` using `h ⟨(l : ℕ) + d, hlt⟩ q (by simp; omega)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cone_step {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) :
    ∀ d : ℕ, ∀ l q : Fin N, (q : ℕ) = l + d → s q ≤ s l + d * T := by
  intro d
  induction d with
  | zero =>
    intro l q hq
    have : q = l := Fin.ext (by simpa using hq)
    subst this
    simp
  | succ d ih =>
    intro l q hq
    have hlt : (l : ℕ) + d < N := by have := q.isLt; omega
    have h1 := ih l ⟨(l : ℕ) + d, hlt⟩ rfl
    have h2 := h ⟨(l : ℕ) + d, hlt⟩ q (by simp; omega)
    push_cast
    linarith

/- English proof (translation)
Establish `h1` using `cone_step h ((q : ℕ) - l) l q (by have : (l : ℕ) ≤ q := hlq; omega)`. Establish `h2 : (((q : ℕ) - l : ℕ) : ℝ) ≤ N`. Establish `: (q : ℕ) - l ≤ N` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h3 : (((q : ℕ) - l : ℕ) : ℝ) * T ≤ (((q : ℕ) - l : ℕ) : ℝ) * |T|` using `mul_le_mul_of_nonneg_left (le_abs_self T) (Nat.cast_nonneg _)`.

Establish `h4 : (((q : ℕ) - l : ℕ) : ℝ) * |T| ≤ N * |T|` using `mul_le_mul_of_nonneg_right h2 (abs_nonneg T)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cone_le {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) {l q : Fin N} (hlq : l ≤ q) :
    s q - s l ≤ N * |T| := by
  have h1 := cone_step h ((q : ℕ) - l) l q (by have : (l : ℕ) ≤ q := hlq; omega)
  have h2 : (((q : ℕ) - l : ℕ) : ℝ) ≤ N := by
    have : (q : ℕ) - l ≤ N := by omega
    exact_mod_cast this
  have h3 : (((q : ℕ) - l : ℕ) : ℝ) * T ≤ (((q : ℕ) - l : ℕ) : ℝ) * |T| :=
    mul_le_mul_of_nonneg_left (le_abs_self T) (Nat.cast_nonneg _)
  have h4 : (((q : ℕ) - l : ℕ) : ℝ) * |T| ≤ N * |T| := mul_le_mul_of_nonneg_right h2 (abs_nonneg T)
  linarith

/- English proof (translation)
Use `⟨(N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)), ?_⟩` and prove the remaining obligations. Introduce `n p k s0 s hc hs hnb hn hpb hp hk i j`. Establish `key : ∀ l m : Fin N, ‖((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖ ≤ 2 * |M| * Real.exp (1 + N * |T|)`. Introduce `l m`. Distinguish the cases in `hil : l < i`.

Rewrite using `[hnb hil]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Distinguish the cases in `hlm : m < l`. Rewrite using `[hpb hlm]`.

Simplify using the standard rewrite rules. Check the signs of the components of the expression. Use `push_neg at hil hlm`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]`. Establish `h1` using `hn i l hil`.

Establish `h2 : ‖p l m‖ ≤ |M|` using `(hp l m).trans (le_abs_self M)`. Establish `h3 : ‖k m j‖ ≤ 1` using `entry_norm_bound_of_unitary hk m j`. Establish `h4` using `cone_le hc hlm`. Establish `h5` using `(abs_le.mp (hs m)).2`. Establish `hexp : Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m) = Real.exp (s m - s0 l)`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `have entry : (diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) * (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j = ∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j) := by`.

Rewrite using `[diagonal_mul, mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_diagonal, mul_apply, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[entry]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem env (M T : ℝ) : ∃ R1 : ℝ, ∀ (n p k : Matrix (Fin N) (Fin N) ℂ) (s0 s : Fin N → ℝ), Cone T s0 →
    (∀ i, |s i - s0 i| ≤ 1) → n.BlockTriangular id → (∀ i j, i ≤ j → ‖n i j‖ ≤ 2 * Real.exp (s0 i - s0 j)) →
    p.BlockTriangular id → (∀ i j, ‖p i j‖ ≤ M) → k ∈ unitaryGroup (Fin N) ℂ →
    ∀ i j, ‖(diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j‖ ≤ R1 := by
  refine ⟨(N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)), ?_⟩
  intro n p k s0 s hc hs hnb hn hpb hp hk i j
  have key : ∀ l m : Fin N, ‖((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ 2 * |M| * Real.exp (1 + N * |T|) := by
    intro l m
    by_cases hil : l < i
    · rw [hnb hil]; simp; positivity
    by_cases hlm : m < l
    · rw [hpb hlm]; simp; positivity
    push_neg at hil hlm
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := hn i l hil
    have h2 : ‖p l m‖ ≤ |M| := (hp l m).trans (le_abs_self M)
    have h3 : ‖k m j‖ ≤ 1 := entry_norm_bound_of_unitary hk m j
    have h4 := cone_le hc hlm
    have h5 := (abs_le.mp (hs m)).2
    have hexp : Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m) = Real.exp (s m - s0 l) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-s0 i) * (‖n i l‖ * ‖p l m‖ * Real.exp (s m) * ‖k m j‖)
        ≤ Real.exp (-s0 i) * (2 * Real.exp (s0 i - s0 l) * |M| * Real.exp (s m) * 1) := by gcongr
      _ = 2 * |M| * (Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m)) := by ring
      _ = 2 * |M| * Real.exp (s m - s0 l) := by rw [hexp]
      _ ≤ 2 * |M| * Real.exp (1 + N * |T|) := by gcongr; linarith
  have entry : (diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j
      = ∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j) := by
    rw [diagonal_mul, mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_diagonal, mul_apply, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  rw [entry]
  calc ‖∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ ∑ m : Fin N, ∑ l : Fin N, (2 * |M| * Real.exp (1 + N * |T|)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => key l m))
    _ = (N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
