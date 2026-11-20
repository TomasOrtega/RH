import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalCalc

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact.

Substitute using the available equality. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem coeff_single_subst {σ τ R : Type*} [CommRing R] [Fintype σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ R) (j : τ) :
    coeff (Finsupp.single j 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single j 1) (a s) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hsplit : f = C (constantCoeff f) + ∑ s, C (coeff (Finsupp.single s 1) f) * X s +
      (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by ring
  have hlow : ∀ e : σ →₀ ℕ, Finsupp.degree e < 2 →
      coeff e (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) = 0 := by
    intro e he
    have hle : Finsupp.degree e ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain rfl : e = 0 := (Finsupp.degree_eq_zero_iff e).mp h0
      simp [coeff_zero_X, coeff_zero_eq_constantCoeff_apply]
    · have hr : e ∈ Set.range (fun t : σ => Finsupp.single t 1) := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨t, rfl⟩ := hr
      simp [coeff_X, coeff_C, Finsupp.single_eq_single_iff]
  have hord : coeff (Finsupp.single j 1)
      (subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s)) = 0 := by
    apply coeff_of_lt_order
    have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.mpr (ha0 i)
    have h2 : (2 : ℕ∞) ≤
        (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s).order :=
      le_order fun e he => hlow e (by exact_mod_cast he)
    calc ((Finsupp.degree (Finsupp.single j 1) : ℕ) : ℕ∞) < 2 := by
          rw [Finsupp.degree_single]; norm_num
      _ = 1 * 2 := by norm_num
      _ ≤ _ := mul_le_mul' h1 h2
      _ ≤ _ := le_order_subst ha _
  have hexp : subst a f = subst a (C (constantCoeff f)) +
      subst a (∑ s, C (coeff (Finsupp.single s 1) f) * X s) +
      subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by
    conv_lhs => rw [hsplit]
    rw [subst_add ha, subst_add ha]
  rw [hexp, map_add, map_add, hord, add_zero, subst_C' ha, subst_sum' ha, map_sum]
  simp [subst_mul ha, subst_C' ha, subst_X ha, coeff_C_mul, coeff_C]

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_single_ev_two {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0)
    (hq : ∀ i, constantCoeff (q i) = 0) (f : PS R 2 d) (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (ev ![p, q] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (p l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (q l) := by
  have h0 : ∀ s : Fin 2 × Fin d, constantCoeff ((![p, q] : Fin 2 → Pt R n d) s.1 s.2) = 0 := by
    rintro ⟨b, i⟩
    fin_cases b
    · exact hp i
    · exact hq i
  unfold ev
  rw [coeff_single_subst h0, Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals rfl

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem coeff_single_X {σ : Type*} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  by_cases h : s = t
  · subst h
    simp [coeff_X]
  · simp [coeff_X, h, Finsupp.single_eq_single_iff]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem constantCoeff_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  unfold pt
  exact constantCoeff_X (j, i)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem coeff_law_snd (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  rw [coeff_single_ev_two (n := 1) 0 (pt R d 0) (fun _ => by simp) (fun m => constantCoeff_pt 0 m)] at hu
  simpa [pt, coeff_single_X, mul_boole, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hu

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem coeff_law_fst (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  have hc := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [coeff_single_ev_two (n := 2) (pt R d 1) (pt R d 0) (fun m => constantCoeff_pt 1 m)
    (fun m => constantCoeff_pt 0 m)] at hc
  rw [← hc]
  simp [pt, coeff_single_X, coeff_law_snd, mul_boole, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coeff_single_law_add {n : ℕ} (G : FGLaw R d) (p q : Pt R n d)
    (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) (i : Fin d)
    (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (G.add p q i) =
      coeff (Finsupp.single j 1) (p i) + coeff (Finsupp.single j 1) (q i) := by
  show coeff (Finsupp.single j 1) (ev ![p, q] (G.F i)) = _
  rw [coeff_single_ev_two p q hp hq]
  simp [coeff_law_fst, coeff_law_snd, boole_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem dAct_add_and_one : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ dAct k B 1 = 1 := by
  intro R _ d O _ _ k _ _ _ B
  constructor
  · intro a b
    ext i j
    rw [Matrix.add_apply]
    unfold dAct FB.actK
    rw [B.A.add_act]
    simp only [coeff_map]
    rw [coeff_single_law_add B.G (B.A.act a) (B.A.act b) (B.A.const a) (B.A.const b), map_add]
  · ext i j
    unfold dAct FB.actK
    simp only [B.A.one_act, coeff_map, Matrix.one_apply, pt, coeff_single_X, Prod.mk.injEq, true_and]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]

end GlobalTheory.FormalCalc
