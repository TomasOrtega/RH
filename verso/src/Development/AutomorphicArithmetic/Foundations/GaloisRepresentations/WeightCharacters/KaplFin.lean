import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

namespace UpperTheory.Gal.Wt.KaplanskyFiniteness

variable {k : Type} [NormedField k] [IsUltrametricDist k]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma norm_unit_le (c x : k) (hc : c ≠ 0) (h : ‖x‖ ≤ ‖c‖) : ‖1 - c⁻¹ * x‖ ≤ 1 := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
  rw [norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hc', mul_one]
  exact h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma norm_le_of_near (c x : k) (h : ‖x - c‖ ≤ ‖c‖ / 2) : ‖x‖ ≤ ‖c‖ := by
  have hx : x = (x - c) + c := by ring
  rw [hx]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) le_rfl)
  have := norm_nonneg c
  linarith

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
private lemma pow_near {u : k} {ε : ℝ} (hε : 0 ≤ ε) (hu : ‖u‖ ≤ 1) (h : ‖u - 1‖ ≤ ε) (n : ℕ) :
    ‖u ^ n - 1‖ ≤ ε := by
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h)
    rw [norm_mul]
    calc ‖u‖ * ‖u ^ n - 1‖ ≤ 1 * ε := mul_le_mul hu ih (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma eval_bound (p : Polynomial k) (x : k) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖p.eval x‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * R ^ i := by
  rw [Polynomial.eval_eq_sum_range]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx i) (norm_nonneg _)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
private lemma exists_pow_small (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ n : ℕ, M * (1 / 2 : ℝ) ^ n ≤ ε := by
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hM1) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc M * (1 / 2 : ℝ) ^ n ≤ (M + 1) * (1 / 2 : ℝ) ^ n := by nlinarith
    _ ≤ (M + 1) * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hn.le hM1.le
    _ = ε := by field_simp

end UpperTheory.Gal.Wt.KaplanskyFiniteness

open UpperTheory.Gal.Wt.KaplanskyFiniteness in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem UpperTheory.Gal.Wt.kaplFin_of :
    UpperTheory.Gal.Wt.KaplFin := by
  classical
  intro k _ _ s δ ε hδ hε hε1
  refine Finset.induction_on_max_value (fun c : k => ‖c‖) s ?_ ?_
  · intro _
    refine ⟨1, fun x _ => by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun x _ => ?_⟩
    simpa using hε.le
  · intro c s _ hmax ih hs
    obtain ⟨p', h1, h2, h3⟩ := ih fun c' hc' => hs c' (Finset.mem_insert_of_mem hc')
    have hδc : δ ≤ ‖c‖ := hs c (Finset.mem_insert_self c s)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hδc
      linarith
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    obtain ⟨n, hn⟩ := exists_pow_small (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c‖ ^ i) ε
      (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) hε
    have hev : ∀ x, ((p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n).eval x) =
        p'.eval x * (1 - c⁻¹ * x) ^ n := by
      intro x
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
    refine ⟨p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n, ?_, ?_, ?_⟩
    · intro x hx
      rw [hev, norm_mul, norm_pow]
      have hu := norm_unit_le c x hc0 (hx.trans hδc)
      calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ 1 * 1 :=
            mul_le_mul (h1 x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    · intro c' hc' x hx
      rw [hev, norm_mul, norm_pow]
      rcases Finset.mem_insert.mp hc' with rfl | hc's
      · have hxc := norm_le_of_near c' x hx
        have hu : ‖1 - c'⁻¹ * x‖ ≤ 1 / 2 := by
          have e : 1 - c'⁻¹ * x = c'⁻¹ * (c' - x) := by field_simp
          rw [e, norm_mul, norm_inv, norm_sub_rev, inv_mul_le_iff₀ hcpos]
          linarith
        calc ‖p'.eval x‖ * ‖1 - c'⁻¹ * x‖ ^ n
            ≤ (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c'‖ ^ i) * (1 / 2 : ℝ) ^ n :=
              mul_le_mul (eval_bound p' x _ hxc) (pow_le_pow_left₀ (norm_nonneg _) hu n)
                (by positivity) ((norm_nonneg _).trans (eval_bound p' x _ hxc))
          _ ≤ ε := hn
      · have hxc : ‖x‖ ≤ ‖c‖ := (norm_le_of_near c' x hx).trans (hmax c' hc's)
        have hu := norm_unit_le c x hc0 hxc
        calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ ε * 1 :=
              mul_le_mul (h2 c' hc's x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hε.le
          _ = ε := mul_one ε
    · intro x hx
      have hxδ : ‖x‖ ≤ δ := hx.trans (by nlinarith)
      have hu := norm_unit_le c x hc0 (hxδ.trans hδc)
      have hu1 : ‖(1 - c⁻¹ * x) - 1‖ ≤ ε := by
        have e : (1 - c⁻¹ * x) - 1 = -(c⁻¹ * x) := by ring
        rw [e, norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos]
        calc ‖x‖ ≤ δ * ε := hx
          _ ≤ ‖c‖ * ε := mul_le_mul_of_nonneg_right hδc hε.le
      have hun := pow_near hε.le hu hu1 n
      have e : p'.eval x * (1 - c⁻¹ * x) ^ n - 1 =
          p'.eval x * ((1 - c⁻¹ * x) ^ n - 1) + (p'.eval x - 1) := by ring
      rw [hev, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3 x hx))
      rw [norm_mul]
      calc ‖p'.eval x‖ * ‖(1 - c⁻¹ * x) ^ n - 1‖ ≤ 1 * ε :=
            mul_le_mul (h1 x hxδ) hun (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
