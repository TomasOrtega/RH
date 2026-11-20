import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)

/- English proof (translation)
Establish `h : (0 : ℝ) ≤ PT.rd E` using `by linarith [P.hrd]`. Establish `hR : (0 : ℝ) ≤ RR (E` using `E) := by`. Unfold `RR`. Conclude with `pow_nonneg h 7`. Unfold `Par.ka0`.

Conclude with `mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)`.
-/
theorem Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)

/- English proof (translation)
Establish `h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y)` using `by first`. Consider the case `(rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])`. Consider the case `(rw [← smul_sub]; norm_cast)`. Consider the case `(rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)`. Rewrite using `[h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tof_uMap_sq_smul {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (r1 : ℕ) (a y : Vsp dim) :
    ‖uMap I (((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y)‖ ^ 2 =
      (r1 : ℝ) ^ 4 * ‖uMap I a - uMap I y‖ ^ 2 := by
  have h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y) := by
    first
    | (rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])
    | (rw [← smul_sub]; norm_cast)
    | (rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)
  rw [h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

/- English proof (translation)
Use `choose y hyL hb using fun j => hpf (a j)`. Use `set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) * (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC`. Use `set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD`. Establish `hkp : 0 ≤ P.ka0 * P.ph` using `mul_nonneg (Par_ka0_nonneg P) hph.le`. Establish `h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤ ∏ j, (C * Real.exp (-(Real.pi / 2) * D j))` using `Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hb j)`.

Establish `h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) = C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, Finset.mul_sum]`. Establish `h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E` using `E) P.m : ℝ) / 4) := by`. Rewrite using `[hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _), ← Real.rpow_mul hkp, Par.p3]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Use `set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb`. Establish `hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j))`. Introduce `j`. Use `⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩` and prove the remaining obligations.

Establish `: ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `X.L.nsmul_mem (hyL j) _`. Establish `hspan` using `tof_span_condition (X := X) I r1 hr1 a y hyL hgen`. Establish `hu2` using `hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan`. Establish `hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hxb]`. Simplify using `only`. Rewrite using `[tof_uMap_sq_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hu2` using `[hsum]`. Establish `hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4`. Establish `: (0 : ℝ) < r1` using `by exact_mod_cast (by omega : 0 < r1)`. Check the signs of the components of the expression. Establish `h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4))`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `: Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j`. Rewrite using `[div_le_iff₀ hr4]`. Use `mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem t_assemble [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hpf : PerFactor P I s)
    (r1 : ℕ) (hr1 : 2 ≤ r1) (a : Fin X.r → Vsp X.dim) (ha : ∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) (hph : 0 < P.ph) :
    ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
  choose y hyL hb using fun j => hpf (a j)
  set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC
  set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD
  have hkp : 0 ≤ P.ka0 * P.ph := mul_nonneg (Par_ka0_nonneg P) hph.le
  have h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) :=
    Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hb j)
  have h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) =
      C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, Finset.mul_sum]
  have h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) := by
    rw [hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _),
      ← Real.rpow_mul hkp, Par.p3]
    congr 2; ring

  set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb
  have hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j)) := by
    intro j
    refine ⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩
    have : ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
    rw [this]; exact X.L.nsmul_mem (hyL j) _
  have hspan := tof_span_condition (X := X) I r1 hr1 a y hyL hgen
  have hu2 := hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan
  have hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxb]; dsimp only
    rw [tof_uMap_sq_smul]; ring
  rw [hsum] at hu2
  have hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4 := by
    have : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
    positivity
  have h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have : Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j := by
      rw [div_le_iff₀ hr4]
      have := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
      nlinarith
    linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C ^ X.r * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [h3]

end

end ReciprocityTheory.ChartRestriction.G.I2
