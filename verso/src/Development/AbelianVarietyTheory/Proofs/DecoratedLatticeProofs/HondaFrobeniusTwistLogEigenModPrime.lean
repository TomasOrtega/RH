import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLeStatement

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

/- English proof (translation)
Introduce `m`. Establish `hm : m = Finsupp.single () (m ())`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[hm]`.

Conclude with `h (m ())`.
-/
theorem coefLe_mv_of_ps {K : Type} [NormedField K] {r : ℝ} {A : K⟦X⟧} (h : ∀ n, ‖coeff n A‖ ≤ r) :
    ∀ m : Unit →₀ ℕ, ‖MvPowerSeries.coeff m A‖ ≤ r := by
  intro m
  have hm : m = Finsupp.single () (m ()) := by
    ext
    simp
  rw [hm]
  exact h (m ())

/- English proof (translation)
Introduce `j x`. Proceed by induction on `j generalizing x with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Conclude with `(ih (σ x)).trans (hσ x)`.
-/
theorem norm_ringHom_pow_apply {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∀ (j : ℕ) (x : K), ‖(σ ^ j) x‖ = ‖x‖ := by
  intro j x
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `m`. Rewrite using `[pow_zero, MvPowerSeries.coeff_one]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ N ih`. Introduce `m`. Rewrite using `[pow_succ, MvPowerSeries.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (ih _) (norm_nonneg _) (hM _)`.
-/
private theorem norm_coeff_pow_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {s : Type}
    (M : MvPowerSeries s K) (hM : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1) :
    ∀ (N : ℕ) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (M ^ N)‖ ≤ 1 := by
  classical
  intro N
  induction N with
  | zero =>
    intro m
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih =>
    intro m
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hM _)

/- English proof (translation)
Introduce `K _ _ _ l σ hU f e hf w hw i hi`. Establish `hU'` using `hU`. Take `⟨hlp, -, hl1, -, hσn, -⟩` from `hU`. Take `⟨hlog, hd, hint⟩` from `hf`. Take `⟨h0, h1, h0', hfe, hef⟩` from `hlog`.

Establish `hn : l ^ i ≠ 0` using `pow_ne_zero _ hlp.ne_zero`. Establish `hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖` using `norm_ringHom_pow_apply σ hσn i`. Use `set g := PowerSeries.map (σ ^ i) f with hg`. Use `set e' := PowerSeries.map (σ ^ i) e with he'`. Establish `hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X` using `PowerSeries.map_X _`.

Establish `hg0 : PowerSeries.constantCoeff g = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]`. Establish `he0 : PowerSeries.constantCoeff e' = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]`. Establish `hef' : PowerSeries.subst e' g = PowerSeries.X`.

Use `congrArg (MvPowerSeries.map (σ ^ i)) hef` as an intermediate fact. Rewrite `this` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm]`. Conclude with `this`. Establish `hd' : CoefLe 1 (d⁄dX K g)`. Introduce `k`.

Rewrite using `[PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]`. Establish `hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1) = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1))`. Rewrite using `[map_mul, map_add, map_one, map_natCast]`. Rewrite using `[hk, hτ, ← PowerSeries.coeff_derivative]`. Conclude with `hd k`.

Use `set M := Formalism.L2.Th1.C.mulBy f e w with hMdef`. Establish `hCf0 : PowerSeries.constantCoeff (PowerSeries.C w * f) = 0`. Rewrite using `[map_mul, h0, mul_zero]`. Establish `hM0 : MvPowerSeries.constantCoeff M = 0` using `PowerSeries.constantCoeff_subst_eq_zero hCf0 _ h0'`. Establish `hMint : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1` using `coefLe_mv_of_ps hw`.

Establish `hAB` using `GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' Unit M hMint i hn`. Use `set A := M ^ l ^ i with hA`. Use `set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) M) with hB`. Establish `hA0 : MvPowerSeries.constantCoeff A = 0`. Rewrite using `[hA, map_pow, hM0, zero_pow hn]`.

Establish `hB0 : MvPowerSeries.constantCoeff B = 0`. Simplify using `[hB, hM0]`. Establish `hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1` using `fun m => norm_coeff_pow_le_one M hMint _ m`. Establish `hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1`. Introduce `m`.

Establish `hb : MvPowerSeries.coeff m B = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B))`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Conclude with `max_le (hA1 m) ((hAB m).trans hl1.le)`. Establish `key` using `GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' Unit A B hA0 hB0 hA1 hB1 hAB`. Establish `hsM : PowerSeries.subst M (frobOp σ l i f) = PowerSeries.subst A g`. Establish `has` using `PowerSeries.HasSubst.of_constantCoeff_zero hM0`.

Unfold `frobOp`. Rewrite using `[PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has, PowerSeries.subst_pow has, PowerSeries.subst_X has]`. Use `set c := (σ ^ i) w with hc`. Establish `hq0 : PowerSeries.constantCoeff (PowerSeries.C c * g) = 0`. Rewrite using `[map_mul, hg0, mul_zero]`.

Establish `hmapM : MvPowerSeries.map (σ ^ i) M = PowerSeries.subst (PowerSeries.C c * g) e'`. Establish `hm : MvPowerSeries.map (σ ^ i) (PowerSeries.C w * f) = PowerSeries.C c * g`. Express the relevant statement in the definitionally equal form `PowerSeries.map (σ ^ i) (PowerSeries.C w * f) = _`. Rewrite using `[map_mul, PowerSeries.map_C]`. Rewrite using `[hMdef]`.

Unfold `Formalism.L2.Th1.C.mulBy`. Rewrite using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hCf0), hm]`. Establish `hexp : MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = PowerSeries.C c * PowerSeries.subst (PowerSeries.X ^ l ^ i) g`. Express the relevant statement in the definitionally equal form `PowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = _`. Rewrite using `[PowerSeries.expand_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hn), PowerSeries.subst_C]`.

Both sides reduce to the same expression. Establish `hexp0 : MvPowerSeries.constantCoeff (MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)) = 0`. Rewrite using `[MvPowerSeries.constantCoeff_expand]`. Conclude with `hq0`. Establish `hBg : PowerSeries.subst B g = PowerSeries.C c * frobOp σ l i f`.

Rewrite using `[hB, hmapM, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hq0), ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' he0) (PowerSeries.HasSubst.of_constantCoeff_zero hexp0), hef', PowerSeries.subst_X (PowerSeries.HasS …`. Both sides reduce to the same expression. Introduce `k`. Rewrite using `[hsM, ← hBg]`. Conclude with `key (Finsupp.single () k)`.
-/
theorem frobLog_eigen : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) →
    ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) -
      C ((σ ^ i) w) * frobOp σ l i f) := by
  intro K _ _ _ l σ hU f e hf w hw i hi
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := norm_ringHom_pow_apply σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hef' : PowerSeries.subst e' g = PowerSeries.X := by
    have := congrArg (MvPowerSeries.map (σ ^ i)) hef
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
    exact this
  have hd' : CoefLe 1 (d⁄dX K g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add, map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set M := Formalism.L2.Th1.C.mulBy f e w with hMdef
  have hCf0 : PowerSeries.constantCoeff (PowerSeries.C w * f) = 0 := by
    rw [map_mul, h0, mul_zero]
  have hM0 : MvPowerSeries.constantCoeff M = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hCf0 _ h0'
  have hMint : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1 := coefLe_mv_of_ps hw
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' Unit M hMint i hn
  set A := M ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) M) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hM0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hM0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => norm_coeff_pow_le_one M hMint _ m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' Unit A B hA0 hB0 hA1 hB1 hAB
  have hsM : PowerSeries.subst M (frobOp σ l i f) = PowerSeries.subst A g := by
    have has := PowerSeries.HasSubst.of_constantCoeff_zero hM0
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  set c := (σ ^ i) w with hc
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C c * g) = 0 := by
    rw [map_mul, hg0, mul_zero]
  have hmapM : MvPowerSeries.map (σ ^ i) M = PowerSeries.subst (PowerSeries.C c * g) e' := by
    have hm : MvPowerSeries.map (σ ^ i) (PowerSeries.C w * f) = PowerSeries.C c * g := by
      change PowerSeries.map (σ ^ i) (PowerSeries.C w * f) = _
      rw [map_mul, PowerSeries.map_C]
    rw [hMdef]
    unfold Formalism.L2.Th1.C.mulBy
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hCf0), hm]
  have hexp : MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)
      = PowerSeries.C c * PowerSeries.subst (PowerSeries.X ^ l ^ i) g := by
    change PowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = _
    rw [PowerSeries.expand_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hn),
      PowerSeries.subst_C]
    rfl
  have hexp0 : MvPowerSeries.constantCoeff (MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand]
    exact hq0
  have hBg : PowerSeries.subst B g = PowerSeries.C c * frobOp σ l i f := by
    rw [hB, hmapM, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' he0)
        (PowerSeries.HasSubst.of_constantCoeff_zero hexp0),
      hef', PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hexp0), hexp]
    rfl
  intro k
  rw [hsM, ← hBg]
  exact key (Finsupp.single () k)

end GlobalTheory.Honda
