import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

/- English proof (translation)
Rewrite using `[PowerSeries.subst, PowerSeries.subst]`. Use `first`. Consider the case `exact MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ`. Consider the case `exact MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ`. Consider the case `exact MvPowerSeries.subst_comp_subst_apply ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ`.

Consider the case `exact MvPowerSeries.subst_comp_subst_apply ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ`.
-/
theorem powerSeries_subst_subst_of_constantCoeff_zero {R : Type} [CommRing R] {α β : Type} (φ : PowerSeries R)
    {u : MvPowerSeries α R} (hu : MvPowerSeries.constantCoeff u = 0) {b : α → MvPowerSeries β R}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

/- English proof (translation)
Establish `hXs : lam.subst (X : PowerSeries K) = lam`. Establish `ha1 : PowerSeries.HasSubst (X : PowerSeries K)` using `PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X`. Use extensionality with `m`. Rewrite using `[PowerSeries.coeff_subst' ha1]`. Rewrite using `[finsum_eq_single _ m]`.

Rewrite using `[PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]`. Introduce `d hd`. Rewrite using `[PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]`. Proceed by induction on `n with`. Consider the case `zero`.

Use `⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (map_zero _)), Nat.cast_zero, map_zero, zero_mul, map_zero]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`.

Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]`. Rewrite using `[zero_pow hd.ne', map_zero, smul_zero]`. Consider the case `succ n ih`. Take `⟨e, he0, he, hlog⟩` from `ih`.

Establish `hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0`. Introduce `s`. Use `fin_cases s`. Conclude with `he0`. Conclude with `PowerSeries.constantCoeff_X`.

Establish `hPint : ∀ s, IntegralMv ((![e, X] : Fin 2 → PowerSeries K) s)`. Introduce `s`. Use `fin_cases s`. Conclude with `(integralPS_iff_mv e).mp he`. Conclude with `(integralPS_iff_mv _).mp integralPS_X`.

Establish `ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K)` using `⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Use `⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `d`. Distinguish the cases in `hd : d = 0`. Rewrite using `[hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hd (Finsupp.ext hc)`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, hP0 s, zero_pow hs]), smul_zero]`. Conclude with `h0`. Conclude with `(integralPS_iff_mv _).mpr (integralMv_subst2 h.Φint hP0 hPint)`.

Rewrite using `[← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]`. Unfold `atX atY`. Use `first`. Consider the case `rw [MvPowerSeries.subst_add ha]`. Consider the case `rw [← MvPowerSeries.coe_substAlgHom ha, map_add, MvPowerSeries.coe_substAlgHom]`.

Rewrite using `[powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha, powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Rewrite using `[hlog, hXs, Nat.cast_succ, map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulN_integral {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} (h : LawD lam Φ) (n : ℕ) :
    ∃ e : PowerSeries K, constantCoeff e = 0 ∧ IntegralPS e ∧ lam.subst e = C (n : K) * lam := by
  have hXs : lam.subst (X : PowerSeries K) = lam := by
    have ha1 : PowerSeries.HasSubst (X : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
    ext m
    rw [PowerSeries.coeff_subst' ha1]
    rw [finsum_eq_single _ m]
    · rw [PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
    · intro d hd
      rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]
  induction n with
  | zero =>
    refine ⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩
    ext k
    rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (map_zero _)),
      Nat.cast_zero, map_zero, zero_mul, map_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]
    · rw [zero_pow hd.ne', map_zero, smul_zero]
  | succ n ih =>
    obtain ⟨e, he0, he, hlog⟩ := ih
    have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0 := by
      intro s
      fin_cases s
      · exact he0
      · exact PowerSeries.constantCoeff_X
    have hPint : ∀ s, IntegralMv ((![e, X] : Fin 2 → PowerSeries K) s) := by
      intro s
      fin_cases s
      · exact (integralPS_iff_mv e).mp he
      · exact (integralPS_iff_mv _).mp integralPS_X
    have ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K) :=
      ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    refine ⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩
    · have h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd : d = 0
        · rw [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]
        · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact hd (Finsupp.ext hc)
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
            Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, hP0 s, zero_pow hs]),
            smul_zero]
      exact h0
    · exact (integralPS_iff_mv _).mpr (integralMv_subst2 h.Φint hP0 hPint)
    · rw [← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]
      unfold atX atY
      first
      | rw [MvPowerSeries.subst_add ha]
      | rw [← MvPowerSeries.coe_substAlgHom ha, map_add, MvPowerSeries.coe_substAlgHom]
      rw [powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha,
        powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha,
        MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hlog, hXs, Nat.cast_succ, map_add, map_one]
      ring

end ReciprocityTheory.ChartRestriction.L1
