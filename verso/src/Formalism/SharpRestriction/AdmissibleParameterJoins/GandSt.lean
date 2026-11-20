import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemWOfNorm

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section W

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qi32.mem_W_of_norm .. | (apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumpt …`.
-/
theorem mem_W_of_norm (i0 : K0 p →+* ℂ_[p]) (hW : ∀ x : WW p, ‖i0 (algebraMap (WW p) (K0 p) x)‖ ≤ 1) (x : K0 p)
    (hx : ‖i0 x‖ ≤ 1) : ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  first | exact UpperTheory.Reformulated.B.Qi32.mem_W_of_norm .. | (apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x hx | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_Ex hf]`. Simplify using the standard rewrite rules.
-/
theorem cc_Ex {ι K : Type} [Field K] [CharZero K] {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    constantCoeff (Ex f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Ex hf]
  simp

/- English proof (translation)
Rewrite using `[← th_log]`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero (cc_pmap _ th_zero) _ (cc_pmap _ (cc_logF p))`.
-/
theorem cc_lgE (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (iC : Kc →+* ℂ_[p])
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE) : PowerSeries.constantCoeff lgE = 0 := by
  rw [← th_log]
  exact PowerSeries.constantCoeff_subst_eq_zero (cc_pmap _ th_zero) _ (cc_pmap _ (cc_logF p))

/- English proof (translation)
Establish `: CharZero Kc` using `charZero_of_injective_algebraMap (algebraMap (K0 p) Kc).injective`. Establish `hl0` using `cc_lgE Kc iC th th_zero lgE th_log`. Use `⟨hfg, ?_⟩` and prove the remaining obligations. Take `⟨U, hU1, hU2⟩` from `K1core Kc Oc witt_mem_integers_Cp iC iC_int th th_zero th_unit lgE th_log (f - g) hfg 1 (by`. Establish `h1 : subst (diagS lgE) (1 : MvPowerSeries ι ℂ_[p]) = 1`.

Rewrite using `[← coe_substAlgHom (hs_dg hl0), map_one]`. Rewrite using `[map_one, h1, one_mul]`. Conclude with `h)`. Establish `hU : U = map (algebraMap (K0 p) Kc) (Ex (f - g))`. Establish `h1 : map (algebraMap (K0 p) Kc) (Ex (f - g)) * (map (algebraMap (K0 p) Kc) (expS p (-(f - g))) * U) = map (algebraMap (K0 p) Kc) (Ex (f - g))` using `by rw [← hU1, mul_one]`.

Rewrite `h1` using `[expS_eq_Ex p (by rw [map_neg, hfg, neg_zero]), ← mul_assoc, ← map_mul, mul_comm (Ex (f - g)), Ex_neg_mul hfg, map_one, one_mul]`. Conclude with `h1`. Establish `e0 : constantCoeff (inParam p (f - g)) = 0` using `constantCoeff_subst_eq_zero (hs_dg (cc_logF p)) (cc_dg (cc_logF p)) hfg`. Establish `hP : inParamK p Kc U = map (algebraMap (K0 p) Kc) (expS p (inParam p (f - g)))`. Rewrite using `[expS_eq_Ex p e0, hU]`.

Use `show subst (diagS (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) (map (algebraMap (K0 p) Kc) (Ex (f - g))) = map (algebraMap (K0 p) Kc) (Ex (subst (diagS (logF p)) (f - g)))`. Rewrite using `[← subst_Ex (hs_dg (cc_logF p)) hfg, map_subst (hs_dg (cc_logF p))]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[map_dg]`.

Establish `hm : ∀ n, ∃ w : WW p, algebraMap (WW p) (K0 p) w = coeff n (expS p (inParam p (f - g)))` using `fun n => mem_W_of_norm (iC.comp (algebraMap (K0 p) Kc)) (fun x => (iC_int _).mp (witt_mem_integers_Cp x)) _ (by`. Establish `h3` using `hU2 n`. Rewrite `h3` using `[hP, coeff_map]`. Conclude with `(iC_int _).mp h3)`. Use `choose G hG using hm`.

Set `Gs : MvPowerSeries ι (WW p)` to `G`. Establish `hGs : map (algebraMap (WW p) (K0 p)) Gs = expS p (inParam p (f - g))`. Use extensionality with `n`. Rewrite using `[coeff_map]`. Conclude with `hG n`.

Use `⟨Gs - 1, ?_, ?_⟩` and prove the remaining obligations. Establish `h4 : algebraMap (WW p) (K0 p) (constantCoeff Gs) = 1`. Rewrite using `[← constantCoeff_map, hGs, expS_eq_Ex p e0, cc_Ex e0]`. Rewrite using `[map_sub, map_one, sub_eq_zero]`. Conclude with `IsFractionRing.injective (WW p) (K0 p) (by rw [h4, map_one])`.

Rewrite using `[map_sub, map_one, add_sub_cancel, hGs]`.
-/
theorem simeq_of {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (f g : MvPowerSeries ι (K0 p)) (hfg : constantCoeff (f - g) = 0)
    (h : IntegralMv (expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (f - g))))) :
    FormalGroupSystem.Simeq p f g := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap (K0 p) Kc).injective
  have hl0 := cc_lgE Kc iC th th_zero lgE th_log
  refine ⟨hfg, ?_⟩
  obtain ⟨U, hU1, hU2⟩ := K1core Kc Oc witt_mem_integers_Cp iC iC_int th th_zero th_unit lgE th_log (f - g) hfg 1 (by
    have h1 : subst (diagS lgE) (1 : MvPowerSeries ι ℂ_[p]) = 1 := by
      rw [← coe_substAlgHom (hs_dg hl0), map_one]
    rw [map_one, h1, one_mul]
    exact h)
  have hU : U = map (algebraMap (K0 p) Kc) (Ex (f - g)) := by
    have h1 : map (algebraMap (K0 p) Kc) (Ex (f - g)) * (map (algebraMap (K0 p) Kc) (expS p (-(f - g))) * U) =
        map (algebraMap (K0 p) Kc) (Ex (f - g)) := by rw [← hU1, mul_one]
    rw [expS_eq_Ex p (by rw [map_neg, hfg, neg_zero]), ← mul_assoc, ← map_mul, mul_comm (Ex (f - g)), Ex_neg_mul hfg,
      map_one, one_mul] at h1
    exact h1
  have e0 : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero (hs_dg (cc_logF p)) (cc_dg (cc_logF p)) hfg
  have hP : inParamK p Kc U = map (algebraMap (K0 p) Kc) (expS p (inParam p (f - g))) := by
    rw [expS_eq_Ex p e0, hU]
    show subst (diagS (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) (map (algebraMap (K0 p) Kc) (Ex (f - g))) =
      map (algebraMap (K0 p) Kc) (Ex (subst (diagS (logF p)) (f - g)))
    rw [← subst_Ex (hs_dg (cc_logF p)) hfg, map_subst (hs_dg (cc_logF p))]
    congr 1
    funext i
    rw [map_dg]
  have hm : ∀ n, ∃ w : WW p, algebraMap (WW p) (K0 p) w = coeff n (expS p (inParam p (f - g))) := fun n =>
    mem_W_of_norm (iC.comp (algebraMap (K0 p) Kc)) (fun x => (iC_int _).mp (witt_mem_integers_Cp x)) _ (by
      have h3 := hU2 n
      rw [hP, coeff_map] at h3
      exact (iC_int _).mp h3)
  choose G hG using hm
  let Gs : MvPowerSeries ι (WW p) := G
  have hGs : map (algebraMap (WW p) (K0 p)) Gs = expS p (inParam p (f - g)) := by
    ext n
    rw [coeff_map]
    exact hG n
  refine ⟨Gs - 1, ?_, ?_⟩
  · have h4 : algebraMap (WW p) (K0 p) (constantCoeff Gs) = 1 := by
      rw [← constantCoeff_map, hGs, expS_eq_Ex p e0, cc_Ex e0]
    rw [map_sub, map_one, sub_eq_zero]
    exact IsFractionRing.injective (WW p) (K0 p) (by rw [h4, map_one])
  · rw [map_sub, map_one, add_sub_cancel, hGs]

end W

end Formalism.MainNotions.J
