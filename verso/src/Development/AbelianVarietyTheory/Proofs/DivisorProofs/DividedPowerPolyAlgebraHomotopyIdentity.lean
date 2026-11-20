import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

/- English proof (translation)
Introduce `R B _ _ _ J δ Q _ _ η v g hstd hvb hve hvd ε hε hεd hεb hεe N`. Establish `hfilE : ∀ k, Q.e k ∈ fil η k` using `fun k ↦ by`. Use `(GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k (Q.e 1) (Q.e_one_mem_ext J)` as an intermediate fact. Rewrite `this` using `[hstd.var]`. Then use the resulting hypothesis. Take `⟨hot_add, hot_alg, -, hot_rel, hot_fil⟩` from `GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e N hvd hfilE`.

Take `⟨hrel_mul, -, -, -, hfil0, hfil_anti, hfil_smul⟩` from `GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R Q.P (Q.ext J) η`. Establish `hd_fil : ∀ n, ∀ x ∈ filDR R η (n + 1), dDR R Q.P x ∈ filDR R η n` using `fun n ↦ (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules.2 R Q.P (Q.ext J) η v hvd n).2.1`. Establish `hrel_le : rel R η ≤ filDR R η N` using `le_sup_right`. Set `H : DR R Q.P →+ DR R Q.P` to `AddMonoidHom.mk' (hot v Q.e N) hot_add`. Establish `hH : ∀ x, H x = hot v Q.e N x` using `fun _ ↦ rfl`.

Establish `hrelgen : ∀ m, ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1)) ∈ rel R η` using `fun m ↦ by`. Establish `: ι1 (D R Q.P (η.dpow (m + 1) (Q.e 1)) - η.dpow m (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η` using `Ideal.subset_span ⟨m, Q.e 1, Q.e_one_mem_ext J, rfl⟩`. Rewrite `this` using `[hstd.var, hstd.var, map_sub, map_smul]`. Then use the resulting hypothesis. Establish `hD0 : ι1 (D R Q.P (Q.e 0)) = 0` using `by rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]`. Establish `hε1 : ε (Q.e 1) = 0` using `by simpa using hεe 0`.

Establish `hcomp : ∀ α : DR R B, hε.mDR (g.mDR α) = α`. Introduce `α`. Proceed by induction on `α using indDR with`. Consider the case `h b => rw [g.mDR_algebraMap, hε.mDR_algebraMap, hεb]`. Consider the case `hd b => rw [g.mDR_ι, hε.mDR_ι, g.m1_D, hε.m1_D, hεb]`.

Consider the case `hm x y hx hy => rw [map_mul, map_mul, hx, hy]`. Consider the case `ha x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hεD1 : hε.mDR (ι1 (D R Q.P (Q.e 1))) = 0`. Rewrite using `[hε.mDR_ι, hε.m1_D, hε1, Derivation.map_zero, map_zero]`. Establish `big : ∀ M, ∀ x ∈ filDR R η M, N ≤ M → x - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N`.

Introduce `M x hx hM`. Use `sub_mem (sub_mem (hfil_anti N M hM hx) ?_) ?_` and prove the remaining obligations. Conclude with `hfil_anti N M hM (hd_fil M _ (hot_fil M x hx))`. Consider the cases of `M with`. Consider the case `zero => rw [Nat.le_zero.1 hM, hfil0]`.

Discharge the goal by the elementary cases of `trivial`. Consider the case `succ k => exact hfil_anti N (k + 1) hM (hot_fil k _ (hd_fil k x hx))`. Establish `hsmul_mem : ∀ n (y : DR R Q.P), Q.e n • y ∈ filDR R η n` using `fun n y ↦ by`. Simplify using `using hfil_smul n 0 (Q.e n) (hfilE n) y (by rw [hfil0]; trivial)`. Introduce `x`.

Use `GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction R B J δ Q η v g hstd hvb hve hvd (fun x ↦ x - g.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N) ?_ ?_ ?_ ?_ x` and prove the remaining obligations. Introduce `x hx`. Use `sub_mem (sub_mem (sub_mem (hrel_le hx) (hrel_le ?_)) (hrel_le ?_)) (hrel_le ?_)` and prove the remaining obligations. Conclude with `mDR_mem_rel g hstd.dp (mDR_mem_rel hε hεd hx)`. Conclude with `dDR_mem_rel R η (hot_rel x hx)`.

Conclude with `hot_rel _ (dDR_mem_rel R η hx)`. Introduce `x y hx hy`. Use `add_mem hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, hot_add]`.

Normalize the expressions using the abelian group laws. Introduce `n α`. Establish `hz` using `(GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).1`. Establish `hz'` using `(GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).1`. Establish `hdx : dDR R Q.P (Q.e n • g.mDR α) = ι1 (D R Q.P (Q.e n)) * g.mDR α + Q.e n • g.mDR (dDR R B α)`.

Rewrite using `[dDR_smul, g.mDR_dDR]`. Establish `hmx : g.mDR (hε.mDR (Q.e n • g.mDR α)) = algebraMap B Q.P (ε (Q.e n)) • g.mDR α`. Rewrite using `[hε.mDR_smul, hcomp, g.mDR_smul]`. Rewrite using `[hmx, hz, hdx, hot_add, hz', map_zero]`. Consider the cases of `n with`.

Consider the case `zero`. Rewrite using `[hD0, zero_mul, Q.e_zero, map_one, map_one, one_smul, ← hH, map_zero]`. Simplify using the standard rewrite rules. Consider the case `succ m`. Rewrite using `[hεe m, map_zero, zero_smul]`.

Break down `lt_or_ge m N with hm | hm` into its components or cases. Establish `hv` using `(GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N m α).2 hm`. Establish `hr : (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η` using `hrel_mul _ (hrelgen m) _`. Establish `key : ι1 (D R Q.P (Q.e (m + 1))) * g.mDR α = (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α + Q.e m • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)`. Rewrite using `[sub_mul, smul_mul_assoc]`.

Normalize the expressions using the abelian group laws. Rewrite using `[key, hot_add, hv]`. Establish `: Q.e (m + 1) • g.mDR α - 0 - 0 - (hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) + Q.e (m + 1) • g.mDR α + 0) = -hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α)` using `by abel`. Rewrite using `[this]`. Conclude with `hrel_le (neg_mem (hot_rel _ hr))`.

Establish `hb` using `big (m + 1) _ (hsmul_mem (m + 1) (g.mDR α)) (by omega)`. Rewrite `hb` using `[hz, hdx, hot_add, hz', map_zero]`. Simplify using `using hb`. Introduce `n α`. Establish `hdy : dDR R Q.P (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = -(ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α))`.

Rewrite using `[dDR_mul, sgn_ι, dDR_D, zero_mul, add_zero, neg_mul, g.mDR_dDR]`. Establish `hmx : g.mDR (hε.mDR (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α))) = 0`. Rewrite using `[hε.mDR_smul, map_mul, hεD1, zero_mul, smul_zero, map_zero]`. Rewrite using `[hmx, sub_zero]`. Break down `lt_or_ge n N with hn | hn` into its components or cases.

Establish `hv` using `(GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).2 hn`. Establish `hv'` using `(GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).2 hn`. Establish `hr2 : ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) ∈ rel R η`. Consider the cases of `n with`. Consider the case `zero => rw [hD0, zero_mul]`.

Conclude with `zero_mem _`. Consider the case `succ k`. Establish `: ι1 (D R Q.P (Q.e (k + 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = (ι1 (D R Q.P (Q.e (k + 1))) - Q.e k • ι1 (D R Q.P (Q.e 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)`. Establish `hsq : Q.e k • ι1 (D R Q.P (Q.e 1)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = 0`. Rewrite using `[smul_mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]`.

Rewrite using `[sub_mul, hsq, sub_zero]`. Rewrite using `[this]`. Conclude with `hrel_mul _ (hrelgen k) _`. Establish `hr1 : (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η` using `hrel_mul _ (hrelgen n) _`. Establish `hdx : dDR R Q.P (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) = ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) - Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α))`.

Rewrite using `[dDR_smul, hdy, smul_neg, sub_eq_add_neg]`. Establish `hdh : dDR R Q.P (Q.e (n + 1) • g.mDR α) = (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α + Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)`. Rewrite using `[dDR_smul, g.mDR_dDR, sub_mul, smul_mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hv, hdh, hdx, ← hH, map_sub, hH, hH, hv']`.

Establish `: Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) - ((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α + Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)) - (hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) - Q.e (n + 1) …` using `by abel`. Rewrite using `[this]`. Conclude with `hrel_le (sub_mem (neg_mem hr1) (hot_rel _ hr2))`. Conclude with `big n _ (hsmul_mem n _) hn`.
-/
theorem homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  intro R B _ _ _ J δ Q _ _ η v g hstd hvb hve hvd ε hε hεd hεb hεe N

  have hfilE : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    have := (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k (Q.e 1) (Q.e_one_mem_ext J)
    rwa [hstd.var] at this
  obtain ⟨hot_add, hot_alg, -, hot_rel, hot_fil⟩ := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e N hvd hfilE
  obtain ⟨hrel_mul, -, -, -, hfil0, hfil_anti, hfil_smul⟩ := GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R Q.P (Q.ext J) η
  have hd_fil : ∀ n, ∀ x ∈ filDR R η (n + 1), dDR R Q.P x ∈ filDR R η n := fun n ↦
    (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules.2 R Q.P (Q.ext J) η v hvd n).2.1
  have hrel_le : rel R η ≤ filDR R η N := le_sup_right
  let H : DR R Q.P →+ DR R Q.P := AddMonoidHom.mk' (hot v Q.e N) hot_add
  have hH : ∀ x, H x = hot v Q.e N x := fun _ ↦ rfl
  have hrelgen : ∀ m, ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1)) ∈ rel R η := fun m ↦ by
    have : ι1 (D R Q.P (η.dpow (m + 1) (Q.e 1)) - η.dpow m (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
      Ideal.subset_span ⟨m, Q.e 1, Q.e_one_mem_ext J, rfl⟩
    rwa [hstd.var, hstd.var, map_sub, map_smul] at this
  have hD0 : ι1 (D R Q.P (Q.e 0)) = 0 := by rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]
  have hε1 : ε (Q.e 1) = 0 := by simpa using hεe 0
  have hcomp : ∀ α : DR R B, hε.mDR (g.mDR α) = α := by
    intro α
    induction α using indDR with
    | h b => rw [g.mDR_algebraMap, hε.mDR_algebraMap, hεb]
    | hd b => rw [g.mDR_ι, hε.mDR_ι, g.m1_D, hε.m1_D, hεb]
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy]
    | ha x y hx hy => rw [map_add, map_add, hx, hy]
  have hεD1 : hε.mDR (ι1 (D R Q.P (Q.e 1))) = 0 := by
    rw [hε.mDR_ι, hε.m1_D, hε1, Derivation.map_zero, map_zero]

  have big : ∀ M, ∀ x ∈ filDR R η M, N ≤ M →
      x - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
    intro M x hx hM
    refine sub_mem (sub_mem (hfil_anti N M hM hx) ?_) ?_
    · exact hfil_anti N M hM (hd_fil M _ (hot_fil M x hx))
    · cases M with
      | zero => rw [Nat.le_zero.1 hM, hfil0]; trivial
      | succ k => exact hfil_anti N (k + 1) hM (hot_fil k _ (hd_fil k x hx))
  have hsmul_mem : ∀ n (y : DR R Q.P), Q.e n • y ∈ filDR R η n := fun n y ↦ by
    simpa using hfil_smul n 0 (Q.e n) (hfilE n) y (by rw [hfil0]; trivial)
  intro x
  refine GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction R B J δ Q η v g hstd hvb hve hvd
    (fun x ↦ x - g.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N)
    ?_ ?_ ?_ ?_ x
  ·
    intro x hx
    refine sub_mem (sub_mem (sub_mem (hrel_le hx) (hrel_le ?_)) (hrel_le ?_)) (hrel_le ?_)
    · exact mDR_mem_rel g hstd.dp (mDR_mem_rel hε hεd hx)
    · exact dDR_mem_rel R η (hot_rel x hx)
    · exact hot_rel _ (dDR_mem_rel R η hx)
  ·
    intro x y hx hy
    have := add_mem hx hy
    convert this using 1
    simp only [map_add, hot_add]
    abel
  ·
    intro n α
    have hz := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).1
    have hz' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).1
    have hdx : dDR R Q.P (Q.e n • g.mDR α) = ι1 (D R Q.P (Q.e n)) * g.mDR α + Q.e n • g.mDR (dDR R B α) := by
      rw [dDR_smul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • g.mDR α)) = algebraMap B Q.P (ε (Q.e n)) • g.mDR α := by
      rw [hε.mDR_smul, hcomp, g.mDR_smul]
    rw [hmx, hz, hdx, hot_add, hz', map_zero]
    cases n with
    | zero =>
      rw [hD0, zero_mul, Q.e_zero, map_one, map_one, one_smul, ← hH, map_zero]
      simp
    | succ m =>
      rw [hεe m, map_zero, zero_smul]
      rcases lt_or_ge m N with hm | hm
      · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N m α).2 hm
        have hr : (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
          hrel_mul _ (hrelgen m) _
        have key : ι1 (D R Q.P (Q.e (m + 1))) * g.mDR α =
            (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
              Q.e m • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
          rw [sub_mul, smul_mul_assoc]; abel
        rw [key, hot_add, hv]
        have : Q.e (m + 1) • g.mDR α - 0 - 0 -
            (hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) +
              Q.e (m + 1) • g.mDR α + 0) =
            -hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) := by abel
        rw [this]
        exact hrel_le (neg_mem (hot_rel _ hr))
      · have hb := big (m + 1) _ (hsmul_mem (m + 1) (g.mDR α)) (by omega)
        rw [hz, hdx, hot_add, hz', map_zero] at hb
        simpa using hb
  ·
    intro n α
    have hdy : dDR R Q.P (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = -(ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
      rw [dDR_mul, sgn_ι, dDR_D, zero_mul, add_zero, neg_mul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α))) = 0 := by
      rw [hε.mDR_smul, map_mul, hεD1, zero_mul, smul_zero, map_zero]
    rw [hmx, sub_zero]
    rcases lt_or_ge n N with hn | hn
    · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).2 hn
      have hv' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).2 hn

      have hr2 : ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) ∈ rel R η := by
        cases n with
        | zero => rw [hD0, zero_mul]; exact zero_mem _
        | succ k =>
          have : ι1 (D R Q.P (Q.e (k + 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) =
              (ι1 (D R Q.P (Q.e (k + 1))) - Q.e k • ι1 (D R Q.P (Q.e 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
            have hsq : Q.e k • ι1 (D R Q.P (Q.e 1)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = 0 := by
              rw [smul_mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]
            rw [sub_mul, hsq, sub_zero]
          rw [this]
          exact hrel_mul _ (hrelgen k) _
      have hr1 : (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
        hrel_mul _ (hrelgen n) _
      have hdx : dDR R Q.P (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) =
          ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
        rw [dDR_smul, hdy, smul_neg, sub_eq_add_neg]
      have hdh : dDR R Q.P (Q.e (n + 1) • g.mDR α) =
          (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α) := by
        rw [dDR_smul, g.mDR_dDR, sub_mul, smul_mul_assoc]; abel
      rw [hv, hdh, hdx, ← hH, map_sub, hH, hH, hv']
      have : Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
          ((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)) -
          (hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) -
            Q.e (n + 1) • g.mDR (dDR R B α)) =
          -((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α) -
            hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) := by abel
      rw [this]
      exact hrel_le (sub_mem (neg_mem hr1) (hot_rel _ hr2))
    · exact big n _ (hsmul_mem n _) hn

end GlobalTheory.PDForm
