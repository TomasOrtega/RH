import Mathlib
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Formalism.PieriBlockIdeals.PieriColumnMinors.RegularCuspidalTrace

noncomputable section

open Finset PowerSeries

namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

section A

section General

variable {R : Type} [CommRing R]

/- English proof (translation)
Rewrite using `[subst_C]`. Both sides reduce to the same expression.
-/
theorem subst_C_eq_C {a : R⟦X⟧} (r : R) : (C r : R⟦X⟧).subst a = C r := by
  rw [subst_C]; rfl

/- English proof (translation)
Establish `hs : HasSubst a` using `by first`. Consider the case `exact HasSubst.of_constantCoeff_zero ha`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero ha`. Consider the case `exact HasSubst.of_constantCoeff_zero' ha`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : X ∣ f - C (constantCoeff f) := by`.

Rewrite using `[X_dvd_iff, map_sub, constantCoeff_C, sub_self]`. Establish `e : f = C (constantCoeff f) + X * g`. Rewrite using `[← hg]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [e]`.

Rewrite using `[subst_add hs, subst_mul hs, subst_X hs, subst_C_eq_C]`. Simplify using `[ha]`.
-/
theorem constantCoeff_subst_of_constantCoeff_zero_alt {a : R⟦X⟧} (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := by
    first
    | exact HasSubst.of_constantCoeff_zero ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact HasSubst.of_constantCoeff_zero' ha
  obtain ⟨g, hg⟩ : X ∣ f - C (constantCoeff f) := by
    rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
  have e : f = C (constantCoeff f) + X * g := by
    rw [← hg]; ring
  conv_lhs => rw [e]
  rw [subst_add hs, subst_mul hs, subst_X hs, subst_C_eq_C]
  simp [ha]

/- English proof (translation)
Simplify using `[gamSer]`.
-/
theorem constantCoeff_gammaSeries (lam : R) (un : R⟦X⟧) : constantCoeff (gamSer lam un) = 0 := by
  simp [gamSer]

/- English proof (translation)
Use `first`. Consider the case `exact HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)`. Consider the case `exact HasSubst.of_constantCoeff_zero' (constantCoeff_gammaSeries lam un)`.
-/
theorem hasSubst_gammaSeries (lam : R) (un : R⟦X⟧) : HasSubst (gamSer lam un) := by
  first
  | exact HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact HasSubst.of_constantCoeff_zero' (constantCoeff_gammaSeries lam un)

end General

/- English proof (translation)
Introduce `l _ O _ _`. Establish `hP` using `hasSubst_pi0_alt l O`. Establish `hc` using `constantCoeff_pi0 l O`. Use `⟨fun f g => subst_add hP f g, fun f g => subst_mul hP f g, fun a => subst_C_eq_C a, subst_X hP, inc_X_sub_l_eq_q0 l O, fun f => constantCoeff_subst_of_constantCoeff_zero_alt hc f, ?_, ?_⟩` and prove the remaining obligations. Introduce `f p hp`.

Establish `hp' : HasSubst p` using `HasSubst.of_constantCoeff_zero' hp`. Conclude with `subst_comp_subst_apply hp' hP f`. Introduce `h2 f g hfg`. Take `⟨g0, -, hu⟩` from `r2_basis_holds l O h2 (inc l O f)`. Establish `hpos` using `prime_sub_one_pos_alt l`.

Set `j0 : Fin (l - 1)` to `⟨0, hpos⟩`. Establish `key : ∀ y : O⟦X⟧, inc l O y = inc l O f → (fun j : Fin (l - 1) => if j = j0 then y else 0) = g0`. Introduce `y hy`. Use `hu _ ?_` and prove the remaining obligations. Use `show inc l O f = ∑ j : Fin (l - 1), inc l O (if j = j0 then y else 0) * X ^ (j : ℕ)`.

Rewrite using `[Finset.sum_eq_single j0]`. Simplify using `[j0, hy]`. Introduce `j _ hj`. Simplify using `[hj, inc_zero]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ _) hj`. Establish `h1` using `key f rfl`. Establish `h2'` using `key g hfg.symm`. Establish `h3` using `congrFun (h1.trans h2'.symm) j0`. Simplify using `using h3`.
-/
theorem pi0Subst_laws_hold : IncLaws := by
  intro l _ O _ _
  have hP := hasSubst_pi0_alt l O
  have hc := constantCoeff_pi0 l O
  refine ⟨fun f g => subst_add hP f g, fun f g => subst_mul hP f g, fun a => subst_C_eq_C a,
    subst_X hP, inc_X_sub_l_eq_q0 l O, fun f => constantCoeff_subst_of_constantCoeff_zero_alt hc f, ?_, ?_⟩
  · intro f p hp
    have hp' : HasSubst p := HasSubst.of_constantCoeff_zero' hp
    exact subst_comp_subst_apply hp' hP f
  · intro h2 f g hfg
    obtain ⟨g0, -, hu⟩ := r2_basis_holds l O h2 (inc l O f)
    have hpos := prime_sub_one_pos_alt l
    let j0 : Fin (l - 1) := ⟨0, hpos⟩
    have key : ∀ y : O⟦X⟧, inc l O y = inc l O f →
        (fun j : Fin (l - 1) => if j = j0 then y else 0) = g0 := by
      intro y hy
      refine hu _ ?_
      show inc l O f = ∑ j : Fin (l - 1), inc l O (if j = j0 then y else 0) * X ^ (j : ℕ)
      rw [Finset.sum_eq_single j0]
      · simp [j0, hy]
      · intro j _ hj
        simp [hj, inc_zero]
      · intro hj
        exact absurd (Finset.mem_univ _) hj
    have h1 := key f rfl
    have h2' := key g hfg.symm
    have h3 := congrFun (h1.trans h2'.symm) j0
    simpa using h3

section Red

variable (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] k] (red : O →+* k)
  (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z)

include hred in
/- English proof (translation)
Rewrite using `[← map_binomialSeriesSubOne_algebraMap l O c, ← map_binomialSeriesSubOne_algebraMap l k c]`. Use extensionality with `n`. Simplify using `[hred]`.
-/
theorem map_reduction_binomialSeriesSubOne (c : ℤ_[l]) : PowerSeries.map red (br l O c) = br l k c := by
  rw [← map_binomialSeriesSubOne_algebraMap l O c, ← map_binomialSeriesSubOne_algebraMap l k c]
  ext n
  simp [hred]

include hred in
/- English proof (translation)
Unfold `pi0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun d _ => map_reduction_binomialSeriesSubOne l O k red hred d`.
-/
theorem map_reduction_pi0 : PowerSeries.map red (pi0 l O) = pi0 l k := by
  unfold pi0
  rw [map_prod]
  exact Finset.prod_congr rfl fun d _ => map_reduction_binomialSeriesSubOne l O k red hred d

end Red

/- English proof (translation)
Introduce `l _ O k _ _ _ _ red hred`. Use `⟨map_reduction_pi0 l O k red hred, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Unfold `inc`. Rewrite using `[map_subst_powerSeries red (hasSubst_pi0_alt l O), map_reduction_pi0 l O k red hred]`.

Introduce `c f`. Unfold `act`. Rewrite using `[map_subst_powerSeries red (hasSubst_binomialSeriesSubOne l O c), map_reduction_binomialSeriesSubOne l O k red hred]`. Introduce `f`. Unfold `phi`.

Rewrite using `[map_subst_powerSeries red (hasSubst_one_add_X_pow_sub_one_alt l)]`. Simplify using the standard rewrite rules.
-/
theorem pi0Subst_reduction_holds : IncRed := by
  intro l _ O k _ _ _ _ red hred
  refine ⟨map_reduction_pi0 l O k red hred, ?_, ?_, ?_⟩
  · intro g
    unfold inc
    rw [map_subst_powerSeries red (hasSubst_pi0_alt l O), map_reduction_pi0 l O k red hred]
  · intro c f
    unfold act
    rw [map_subst_powerSeries red (hasSubst_binomialSeriesSubOne l O c), map_reduction_binomialSeriesSubOne l O k red hred]
  · intro f
    unfold phi
    rw [map_subst_powerSeries red (hasSubst_one_add_X_pow_sub_one_alt l)]
    simp

/- English proof (translation)
Introduce `R _ lam un`. Establish `hs : HasSubst (gamSer lam un)` using `hasSubst_gammaSeries lam un`. Establish `hc : constantCoeff (gamSer lam un) = 0` using `constantCoeff_gammaSeries lam un`. Establish `hadd : ∀ f g : R⟦X⟧, gam0 lam un (f + g) = gam0 lam un f + gam0 lam un g`. Introduce `f g`.

Conclude with `subst_add hs f g`. Establish `hmul : ∀ f g : R⟦X⟧, gam0 lam un (f * g) = gam0 lam un f * gam0 lam un g`. Introduce `f g`. Conclude with `subst_mul hs f g`. Establish `hC : ∀ a : R, gam0 lam un (C a) = C a` using `fun a => subst_C_eq_C a`.

Establish `hX : gam0 lam un X = X * (1 + un * (X - C lam))` using `subst_X hs`. Establish `hcc : ∀ y : R⟦X⟧, constantCoeff (gam0 lam un y) = constantCoeff y` using `fun y => constantCoeff_subst_of_constantCoeff_zero_alt hc y`. Use `⟨hadd, hmul, hC, ?_, hX, ?_, hcc⟩` and prove the remaining obligations. Introduce `y`. Rewrite using `[X_dvd_iff, map_sub, hcc, sub_self]`.

Establish `e : (X : R⟦X⟧) - C lam = X + C (-lam)` using `by rw [map_neg, sub_eq_add_neg]`. Rewrite using `[e, hadd, hC, hX, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gamma_laws_hold : GamLaws := by
  intro R _ lam un
  have hs : HasSubst (gamSer lam un) := hasSubst_gammaSeries lam un
  have hc : constantCoeff (gamSer lam un) = 0 := constantCoeff_gammaSeries lam un
  have hadd : ∀ f g : R⟦X⟧, gam0 lam un (f + g) = gam0 lam un f + gam0 lam un g := by
    intro f g; exact subst_add hs f g
  have hmul : ∀ f g : R⟦X⟧, gam0 lam un (f * g) = gam0 lam un f * gam0 lam un g := by
    intro f g; exact subst_mul hs f g
  have hC : ∀ a : R, gam0 lam un (C a) = C a := fun a => subst_C_eq_C a
  have hX : gam0 lam un X = X * (1 + un * (X - C lam)) := subst_X hs
  have hcc : ∀ y : R⟦X⟧, constantCoeff (gam0 lam un y) = constantCoeff y :=
    fun y => constantCoeff_subst_of_constantCoeff_zero_alt hc y
  refine ⟨hadd, hmul, hC, ?_, hX, ?_, hcc⟩
  · intro y; rw [X_dvd_iff, map_sub, hcc, sub_self]
  · have e : (X : R⟦X⟧) - C lam = X + C (-lam) := by rw [map_neg, sub_eq_add_neg]
    rw [e, hadd, hC, hX, map_neg]; ring

/- English proof (translation)
Introduce `R k _ _ red lam un y`. Unfold `gam0`. Rewrite using `[map_subst_powerSeries red (hasSubst_gammaSeries lam un)]`. Use `congr 1`. Simplify using `[gamSer]`.
-/
theorem gamma_reduction_holds : GamRed := by
  intro R k _ _ red lam un y
  unfold gam0
  rw [map_subst_powerSeries red (hasSubst_gammaSeries lam un)]
  congr 1
  simp [gamSer]

/- English proof (translation)
Introduce `l _ O _ _ u un hun y`. Take `⟨hadd, hmul, hC, hX, hq, -, hsub, -⟩` from `pi0Subst_laws_hold l O`. Establish `hP` using `hasSubst_pi0_alt l O`. Establish `h1 : act l O u (inc l O y) = y.subst (act l O u (pi0 l O))` using `subst_comp_subst_apply hP (hasSubst_binomialSeriesSubOne l O u) y`. Establish `h2 : inc l O (gam0 (l : O) un y) = y.subst (inc l O (gamSer (l : O) un))` using `hsub y _ (constantCoeff_gammaSeries _ _)`.

Establish `h3 : inc l O (gamSer (l : O) un) = pi0 l O * (1 + inc l O un * q0 l O)`. Unfold `gamSer`. Establish `h1' : inc l O 1 = 1`. Use `hC 1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hmul, hadd, hmul, hX, hq, h1']`. Rewrite using `[h1, h2, h3, hun]`.
-/
theorem gamma_on_pi0Subst_holds : GammaOnInc := by
  intro l _ O _ _ u un hun y
  obtain ⟨hadd, hmul, hC, hX, hq, -, hsub, -⟩ := pi0Subst_laws_hold l O
  have hP := hasSubst_pi0_alt l O
  have h1 : act l O u (inc l O y) = y.subst (act l O u (pi0 l O)) :=
    subst_comp_subst_apply hP (hasSubst_binomialSeriesSubOne l O u) y
  have h2 : inc l O (gam0 (l : O) un y) = y.subst (inc l O (gamSer (l : O) un)) :=
    hsub y _ (constantCoeff_gammaSeries _ _)
  have h3 : inc l O (gamSer (l : O) un) = pi0 l O * (1 + inc l O un * q0 l O) := by
    unfold gamSer
    have h1' : inc l O 1 = 1 := by
      have := hC 1
      simpa using this
    rw [hmul, hadd, hmul, hX, hq, h1']
  rw [h1, h2, h3, hun]

/- English proof (translation)
Introduce `l _ O _ _ _ hl u c hu`. Take `⟨un0, h0, he0, -, -⟩` from `r6_holds l O hl u c hu`. Take `⟨-, -, -, hX, hq, -, -, hinj⟩` from `pi0Subst_laws_hold l O`. Establish `hinj` using `hinj hl`. Establish `hz : inc l O 0 = 0` using `inc_zero l O`.

Establish `hpi : pi0 l O ≠ 0`. Rewrite using `[← hX, ← hz]`. Conclude with `fun h => X_ne_zero (hinj h)`. Establish `hq0 : q0 l O ≠ 0`. Rewrite using `[← hq, ← hz]`.

Introduce `h`. Establish `h1` using `hinj h`. Establish `h2` using `congrArg (coeff 1) h1`. Rewrite `h2` using `[map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero, map_zero]`. Conclude with `one_ne_zero h2`.

Establish `huniq : ∀ a b : O⟦X⟧, IsUn l O u a → IsUn l O u b → a = b`. Introduce `a b ha hb`. Establish `h1 : pi0 l O * (1 + inc l O a * q0 l O) = pi0 l O * (1 + inc l O b * q0 l O)` using `ha.symm.trans hb`. Establish `h2` using `mul_left_cancel₀ hpi h1`. Establish `h3 : inc l O a * q0 l O = inc l O b * q0 l O` using `add_left_cancel h2`.

Conclude with `hinj (mul_right_cancel₀ hq0 h3)`. Use `⟨⟨un0, h0⟩, fun un hun => ⟨fun un' hun' => huniq un' un hun' hun, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[huniq un un0 hun h0]`. Conclude with `he0`.
-/
theorem unit_series_constant_holds : UnConst := by
  intro l _ O _ _ _ hl u c hu
  obtain ⟨un0, h0, he0, -, -⟩ := r6_holds l O hl u c hu
  obtain ⟨-, -, -, hX, hq, -, -, hinj⟩ := pi0Subst_laws_hold l O
  have hinj := hinj hl
  have hz : inc l O 0 = 0 := inc_zero l O
  have hpi : pi0 l O ≠ 0 := by
    rw [← hX, ← hz]
    exact fun h => X_ne_zero (hinj h)
  have hq0 : q0 l O ≠ 0 := by
    rw [← hq, ← hz]
    intro h
    have h1 := hinj h
    have h2 := congrArg (coeff 1) h1
    rw [map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero, map_zero] at h2
    exact one_ne_zero h2
  have huniq : ∀ a b : O⟦X⟧, IsUn l O u a → IsUn l O u b → a = b := by
    intro a b ha hb
    have h1 : pi0 l O * (1 + inc l O a * q0 l O) = pi0 l O * (1 + inc l O b * q0 l O) :=
      ha.symm.trans hb
    have h2 := mul_left_cancel₀ hpi h1
    have h3 : inc l O a * q0 l O = inc l O b * q0 l O := add_left_cancel h2
    exact hinj (mul_right_cancel₀ hq0 h3)
  refine ⟨⟨un0, h0⟩, fun un hun => ⟨fun un' hun' => huniq un' un hun' hun, ?_⟩⟩
  rw [huniq un un0 hun h0]
  exact he0

/- English proof (translation)
Introduce `l _ O k _ _ _ _ _ red hl hred y`. Take `⟨-, -, -, -, hcomm, -, -⟩` from `action_laws_holds l O`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(fixed_relation_holds l O hl (phi l O (inc l O y))).1 ?_` and prove the remaining obligations. Introduce `d hd`.

Rewrite using `[← hcomm, (fixed_relation_holds l O hl (inc l O y)).2 ⟨y, rfl⟩ d hd]`. Introduce `y' hy'`. Take `⟨-, hinc, -, hphi⟩` from `pi0Subst_reduction_holds l O k red hred`. Take `⟨-, -, -, -, -, -, -, hinj⟩` from `pi0Subst_laws_hold l k`. Apply `hinj hl` to reduce the goal to its premises.

Rewrite using `[← hinc, ← hy', hphi, hinc, r5_character_holds l k]`. Both sides reduce to the same expression.
-/
theorem frobenius_on_pi0Subst_holds : PhiOnInc := by
  intro l _ O k _ _ _ _ _ red hl hred y
  obtain ⟨-, -, -, -, hcomm, -, -⟩ := action_laws_holds l O
  refine ⟨?_, ?_⟩
  · refine (fixed_relation_holds l O hl (phi l O (inc l O y))).1 ?_
    intro d hd
    rw [← hcomm, (fixed_relation_holds l O hl (inc l O y)).2 ⟨y, rfl⟩ d hd]
  · intro y' hy'
    obtain ⟨-, hinc, -, hphi⟩ := pi0Subst_reduction_holds l O k red hred
    obtain ⟨-, -, -, -, -, -, -, hinj⟩ := pi0Subst_laws_hold l k
    apply hinj hl
    rw [← hinc, ← hy', hphi, hinc, r5_character_holds l k]
    rfl

/- English proof (translation)
Introduce `O _ lam a g hg`. Take `⟨q, hq⟩` from `hg`. Establish `hc : constantCoeff g = a + lam * (-constantCoeff q)`. Establish `h2` using `congrArg constantCoeff hq`. Simplify using `only [map_sub, map_mul, constantCoeff_C, constantCoeff_X] at h2`.

Take the linear combination `h2`. Use `⟨⟨-constantCoeff q, hc⟩, ?_⟩` and prove the remaining obligations. Introduce `k _ red hred`. Rewrite using `[hc, map_add, map_mul, hred, zero_mul, add_zero]`.
-/
theorem evaluation_congruence_holds : EvalCong := by
  intro O _ lam a g hg
  obtain ⟨q, hq⟩ := hg
  have hc : constantCoeff g = a + lam * (-constantCoeff q) := by
    have h2 := congrArg constantCoeff hq
    simp only [map_sub, map_mul, constantCoeff_C, constantCoeff_X] at h2
    linear_combination h2
  refine ⟨⟨-constantCoeff q, hc⟩, ?_⟩
  intro k _ red hred
  rw [hc, map_add, map_mul, hred, zero_mul, add_zero]

/- English proof (translation)
Introduce `O _ _ _ _ _ _ _ c a f f₁ hn hf`. Establish `hx : PowerSeries.HasEval c` using `hn`. Establish `hc : Continuous (RingHom.id O)` using `continuous_id`. Establish `h2` using `congrArg (PowerSeries.eval₂Hom hc hx) hf`. Rewrite `h2` using `[map_add, map_mul, map_sub]`.

Simplify using `only [PowerSeries.coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, sub_self, zero_mul, zero_add] at h2`. Conclude with `h2`.
-/
theorem linear_division_evaluation_holds : LinDivisionEval := by
  intro O _ _ _ _ _ _ _ c a f f₁ hn hf
  have hx : PowerSeries.HasEval c := hn
  have hc : Continuous (RingHom.id O) := continuous_id
  have h2 := congrArg (PowerSeries.eval₂Hom hc hx) hf
  rw [map_add, map_mul, map_sub] at h2
  simp only [PowerSeries.coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, sub_self,
    zero_mul, zero_add] at h2
  exact h2

/- English proof (translation)
Introduce `O _ lam n D Th h a b`. Take `⟨q, hq⟩` from `h a b`. Use `⟨X * q + C (Th a b), ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b = C ((1 : Matrix (Fin n) (Fin n) O) a b)`. Apply the tactic sequence `by_cases hab : a = b <;> simp [hab, Matrix.one_apply]`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, map_add, map_mul]`. Take the linear combination `X * hq`.
-/
theorem gamma_mod_q_holds : GammaModQ := by
  intro O _ lam n D Th h a b
  obtain ⟨q, hq⟩ := h a b
  refine ⟨X * q + C (Th a b), ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b = C ((1 : Matrix (Fin n) (Fin n) O) a b) := by
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, map_add, map_mul]
  linear_combination X * hq

/- English proof (translation)
Introduce `A N _ _ _ p γA γ d htor hγadd hγsmul hd`. Establish `hadd : ∀ x y, d (x + y) = d x + d y`. Introduce `x y`. Apply `eq_of_sub_eq_zero` to reduce the goal to its premises. Apply `htor` to reduce the goal to its premises.

Rewrite using `[smul_sub, smul_add, hd, hd, hd, hγadd]`. Normalize the expressions using the abelian group laws. Use `⟨hadd, ?_⟩` and prove the remaining obligations. Introduce `a x ha`. Apply `eq_of_sub_eq_zero` to reduce the goal to its premises.

Apply `htor` to reduce the goal to its premises. Rewrite using `[smul_sub, hd, hγsmul, ha, smul_comm p a (d x), hd, smul_sub]`. Conclude with `sub_self _`.
-/
theorem derivation_linear_holds : DLinear := by
  intro A N _ _ _ p γA γ d htor hγadd hγsmul hd
  have hadd : ∀ x y, d (x + y) = d x + d y := by
    intro x y
    apply eq_of_sub_eq_zero
    apply htor
    rw [smul_sub, smul_add, hd, hd, hd, hγadd]
    abel
  refine ⟨hadd, ?_⟩
  intro a x ha
  apply eq_of_sub_eq_zero
  apply htor
  rw [smul_sub, hd, hγsmul, ha, smul_comm p a (d x), hd, smul_sub]
  exact sub_self _

/- English proof (translation)
Introduce `k _ n un D y z h a`. Take `⟨hadd, hmul, hC, -, hX, -, hcc0⟩` from `gamma_laws_hold k 0 un`. Establish `h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y`. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : X ∣ y - C (constantCoeff y) := by`.

Rewrite using `[X_dvd_iff, map_sub, constantCoeff_C, sub_self]`. Establish `e : y = C (constantCoeff y) + X * g` using `by rw [← hg]; ring`. Rewrite using `[e, hadd, hmul, hC, hX]`. Rewrite using `[map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]`. Rewrite using `[mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, hcc0]`.

Simplify using the standard rewrite rules. Establish `e2 : coeff 1 (X * z a) = constantCoeff (z a)`. Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[← e2, h a]`. Establish `hsm : ∀ v : Fin n → k⟦X⟧, ((X : k⟦X⟧) • D).mulVec v = (X : k⟦X⟧) • D.mulVec v`.

Introduce `v`. Use `first`. Consider the case `exact Matrix.smul_mulVec X D v`. Consider the case `exact Matrix.smul_mulVec_assoc X D v`. Consider the case `(funext i; simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc])`.

Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, hsm]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_add]`. Rewrite using `[h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Use `first`. Consider the case `(simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)`.

Consider the case `(simp only [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)`.
-/
theorem dbar_coordinates_hold : DbarCoord := by
  intro k _ n un D y z h a
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨g, hg⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * g := by rw [← hg]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, hcc0]
    simp
  have e2 : coeff 1 (X * z a) = constantCoeff (z a) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [← e2, h a]
  have hsm : ∀ v : Fin n → k⟦X⟧, ((X : k⟦X⟧) • D).mulVec v = (X : k⟦X⟧) • D.mulVec v := by
    intro v
    first
    | exact Matrix.smul_mulVec X D v
    | exact Matrix.smul_mulVec_assoc X D v
    | (funext i; simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
        Finset.mul_sum, mul_assoc])
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_add]
  rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  first
  | (simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)
  | (simp only [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)

end A

/- English proof (translation)
Introduce `R _ l hl`. Establish `hc : constantCoeff (X ^ l : R⟦X⟧) = 0`. Rewrite using `[map_pow, constantCoeff_X, zero_pow hl.ne']`. Establish `hs : HasSubst (X ^ l : R⟦X⟧)` using `by first`. Consider the case `exact HasSubst.of_constantCoeff_zero hc`.

Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero hc`. Consider the case `exact HasSubst.of_constantCoeff_zero' hc`. Use `⟨fun f g => ?_, fun f g => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Conclude with `subst_add hs f g`. Conclude with `subst_mul hs f g`.

Conclude with `subst_C_eq_C a`. Conclude with `subst_X hs`.
-/
theorem frobenius_laws_hold : FrobLaws := by
  intro R _ l hl
  have hc : constantCoeff (X ^ l : R⟦X⟧) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hl.ne']
  have hs : HasSubst (X ^ l : R⟦X⟧) := by
    first
    | exact HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact HasSubst.of_constantCoeff_zero' hc
  refine ⟨fun f g => ?_, fun f g => ?_, fun a => ?_, ?_⟩
  · exact subst_add hs f g
  · exact subst_mul hs f g
  · exact subst_C_eq_C a
  · exact subst_X hs

/- English proof (translation)
Introduce `R _ n θ M g g' y`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[RingHom.map_mulVec]`.

Both sides reduce to the same expression.
-/
theorem semilinear_change_holds : SemilinChange := by
  intro R _ n θ M g g' y
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Introduce `R _ n h x P Q hPQ`. Use `⟨Q.det, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Matrix.det hPQ`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]`. Rewrite using `[h2, ← pow_mul]`.
-/
theorem det_dvd_holds : DetDvd := by
  intro R _ n h x P Q hPQ
  refine ⟨Q.det, ?_⟩
  have h2 := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h2
  rw [h2, ← pow_mul]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply]`.
-/
theorem map_smul_one_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (x : R) :
    ((x • (1 : Matrix (Fin n) (Fin n) R))).map f = f x • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/- English proof (translation)
Introduce `i j hij`. Set `φ` to `algebraMap R (FractionRing R)`. Establish `hinj : Function.Injective φ` using `IsFractionRing.injective R (FractionRing R)`. Establish `hm' : Φ.map φ * Φ'.map φ = (φ π ^ h) • (1 : Matrix (Fin n) (Fin n) (FractionRing R))`. Rewrite using `[← Matrix.map_mul, hm]`.

Use extensionality with `a c`. Apply the tactic sequence `by_cases hac : a = c <;> simp [hac, Matrix.one_apply]`. Establish `hc : (φ π) ^ h ≠ 0` using `pow_ne_zero _ ((map_ne_zero_iff φ hinj).2 hπ)`. Establish `hr : Φ.map φ * (((φ π) ^ h)⁻¹ • Φ'.map φ) = 1`. Rewrite using `[Matrix.mul_smul, hm', smul_smul, inv_mul_cancel₀ hc, one_smul]`.

Establish `hinv : (Φ.map φ)⁻¹ = ((φ π) ^ h)⁻¹ • Φ'.map φ` using `Matrix.inv_eq_right_inv hr`. Use `letI : Invertible (Φ.map φ) := by first`. Consider the case `exact ⟨_, mul_eq_one_comm.mp hr, hr⟩`. Consider the case `exact Matrix.invertibleOfIsUnitDet _ (Matrix.isUnit_det_of_right_inverse hr)`. Consider the case `exact Matrix.invertibleOfRightInverse _ _ hr`.

Establish `hΦK : (Φ.map φ).BlockTriangular b` using `fun a c hac => by simp [hΦ hac]`. Establish `h4` using `Matrix.blockTriangular_inv_of_blockTriangular hΦK hij`. Rewrite `h4` using `[hinv, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_eq_zero]`. Break down `h4 with h5 | h5` into its components or cases. Conclude with `absurd h5 (inv_ne_zero hc)`.

Conclude with `hinj (by rw [h5, map_zero])`.
-/
theorem blockTriangular_of_mul_eq_pow_smul_one {R : Type} [CommRing R] [IsDomain R] (π : R) (n h : ℕ)
    (Φ Φ' : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (hπ : π ≠ 0) (hΦ : Φ.BlockTriangular b)
    (hm : Φ * Φ' = (π ^ h) • (1 : Matrix (Fin n) (Fin n) R)) : Φ'.BlockTriangular b := by
  intro i j hij
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hm' : Φ.map φ * Φ'.map φ = (φ π ^ h) • (1 : Matrix (Fin n) (Fin n) (FractionRing R)) := by
    rw [← Matrix.map_mul, hm]
    ext a c
    by_cases hac : a = c <;> simp [hac, Matrix.one_apply]
  have hc : (φ π) ^ h ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff φ hinj).2 hπ)
  have hr : Φ.map φ * (((φ π) ^ h)⁻¹ • Φ'.map φ) = 1 := by
    rw [Matrix.mul_smul, hm', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hinv : (Φ.map φ)⁻¹ = ((φ π) ^ h)⁻¹ • Φ'.map φ := Matrix.inv_eq_right_inv hr
  letI : Invertible (Φ.map φ) := by
    first
    | exact ⟨_, mul_eq_one_comm.mp hr, hr⟩
    | exact Matrix.invertibleOfIsUnitDet _ (Matrix.isUnit_det_of_right_inverse hr)
    | exact Matrix.invertibleOfRightInverse _ _ hr
  have hΦK : (Φ.map φ).BlockTriangular b := fun a c hac => by simp [hΦ hac]
  have h4 := Matrix.blockTriangular_inv_of_blockTriangular hΦK hij
  rw [hinv, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_eq_zero] at h4
  rcases h4 with h5 | h5
  · exact absurd h5 (inv_ne_zero hc)
  · exact hinj (by rw [h5, map_zero])

/- English proof (translation)
Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.toBlock_apply, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun k => b k = r)]`. Establish `hz : ∑ k : {k // ¬ b k = r}, A i k * B k j = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce and unpack `⟨k, hk⟩ -`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hA (by rw [hi]; exact h), zero_mul]`. Rewrite using `[hB (by rw [hj]; exact h), mul_zero]`. Rewrite using `[hz, add_zero]`.
-/
theorem toSquareBlock_mul_of_blockTriangular_alt {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (r : ℕ) :
    (A * B).toSquareBlock b r = A.toSquareBlock b r * B.toSquareBlock b r := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.toBlock_apply, Matrix.mul_apply,
    Matrix.of_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = r)]
  have hz : ∑ k : {k // ¬ b k = r}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ -
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (by rw [hi]; exact h), zero_mul]
    · rw [hB (by rw [hj]; exact h), mul_zero]
  rw [hz, add_zero]

/- English proof (translation)
Introduce `R _ _ π n h Φ Φ' b hπ hΦ hm`. Establish `hΦ'` using `blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm`. Use `⟨hΦ', fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[← toSquareBlock_mul_of_blockTriangular_alt Φ Φ' b hΦ hΦ' r, hm]`. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.toSquareBlock_def]`. Simplify using `[Matrix.toSquareBlock_def, Matrix.one_apply, hij]`.
-/
theorem block_height_holds : BlockHeight := by
  intro R _ _ π n h Φ Φ' b hπ hΦ hm
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  refine ⟨hΦ', fun r => ?_⟩
  rw [← toSquareBlock_mul_of_blockTriangular_alt Φ Φ' b hΦ hΦ' r, hm]
  ext ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij; simp [Matrix.toSquareBlock_def]
  · simp [Matrix.toSquareBlock_def, Matrix.one_apply, hij]

/- English proof (translation)
Introduce `R _ _ π n h Φ Φ' b s hπ hΦ hm hs`. Establish `hΦ'` using `blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm`. Establish `h2` using `congrFun (congrFun hm s) s`. Rewrite `h2` using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Rewrite using `[← h2, Finset.sum_eq_single s]`.

Introduce `j _ hj`. Break down `lt_trichotomy (b j) (b s) with h3 | h3 | h3` into its components or cases. Rewrite using `[hΦ h3, zero_mul]`. Conclude with `absurd (hs j h3) hj`. Rewrite using `[hΦ' h3, mul_zero]`.

Introduce `hs'`. Conclude with `absurd (Finset.mem_univ s) hs'`.
-/
theorem block_height_on_line_holds : BlockHeightLine := by
  intro R _ _ π n h Φ Φ' b s hπ hΦ hm hs
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  have h2 := congrFun (congrFun hm s) s
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  rw [← h2, Finset.sum_eq_single s]
  · intro j _ hj
    rcases lt_trichotomy (b j) (b s) with h3 | h3 | h3
    · rw [hΦ h3, zero_mul]
    · exact absurd (hs j h3) hj
    · rw [hΦ' h3, mul_zero]
  · intro hs'; exact absurd (Finset.mem_univ s) hs'

/- English proof (translation)
Introduce `k _ h x x' hxx`. Take `⟨α, hα, hassoc⟩` from `(dvd_prime_pow X_prime h).1 ⟨x', hxx.symm⟩`. Take `⟨u, hu⟩` from `hassoc.symm`. Conclude with `⟨α, u, hα, by rw [← hu, mul_comm]⟩`.
-/
theorem unit_pow_holds : UnitPow := by
  intro k _ h x x' hxx
  obtain ⟨α, hα, hassoc⟩ := (dvd_prime_pow X_prime h).1 ⟨x', hxx.symm⟩
  obtain ⟨u, hu⟩ := hassoc.symm
  exact ⟨α, u, hα, by rw [← hu, mul_comm]⟩

/- English proof (translation)
Introduce `k _ l s p v w w' κ κ' hl heq`. Take `⟨-, hmul, hC, -⟩` from `frobenius_laws_hold k l hl`. Set `φ : k⟦X⟧ →+* LaurentSeries k` to `HahnSeries.ofPowerSeries ℤ k`. Establish `hφ : Function.Injective φ` using `HahnSeries.ofPowerSeries_injective`. Express the relevant statement in the definitionally equal form `φ (frob0 l (w' : k⟦X⟧)) * φ X ^ ((l : ℤ) * κ') * φ ((v : k⟦X⟧) * X ^ s) = φ p * φ (w : k⟦X⟧) * φ X ^ κ at heq`.

Establish `hx : φ X ≠ 0` using `(map_ne_zero_iff φ hφ).2 X_ne_zero`. Establish `hfu : frob0 l (w' : k⟦X⟧) * frob0 l ((w'⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`. Rewrite using `[← hmul, Units.mul_inv, ← map_one (C : k →+* k⟦X⟧), hC]`. Set `A : k⟦X⟧` to `frob0 l (w' : k⟦X⟧) * (v : k⟦X⟧) * ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)`. Establish `hF : IsUnit (frob0 l (w' : k⟦X⟧))` using `⟨⟨_, _, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩`.

Establish `hA : IsUnit A` using `(hF.mul v.isUnit).mul (w⁻¹).isUnit`. Establish `hww : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Use `set e : ℤ := (l : ℤ) * κ' + (s : ℤ) - κ with he`. Establish `key : φ p = φ A * φ X ^ e`.

Establish `h1 : φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) = φ p`. Rewrite using `[show φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) = φ p * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) * (φ X ^ κ * φ X ^ (-κ)) by ring, hww, ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one, mul_one]`. Rewrite using `[← h1, ← heq]`. Simplify using `only [A, map_mul, map_pow]`. Rewrite using `[he, sub_eq_add_neg, zpow_add₀ hx, zpow_add₀ hx, zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `he0 : 0 ≤ e`. Use `⟨he0, hA.unit, hφ ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, map_mul, map_pow, key, ← zpow_natCast, Int.toNat_of_nonneg he0]`. Use `exfalso push_neg at he0`.

Establish `hm : φ p * φ X ^ (-e) = φ A`. Rewrite using `[key, mul_assoc, ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one]`. Take `⟨m, hm'⟩ : ∃ m : ℕ, -e = (m : ℤ) + 1` from `⟨(-e - 1).toNat, by omega⟩`. Rewrite `hm` using `[hm', zpow_add_one₀ hx, zpow_natCast, ← map_pow, ← map_mul, ← map_mul]`. Establish `h5` using `congrArg constantCoeff (hφ hm)`.

Simplify using `only [map_mul, constantCoeff_X, mul_zero] at h5`. Conclude with `(hA.map constantCoeff).ne_zero h5.symm`.
-/
theorem frobenius_diagonal_holds : PhiDiag := by
  intro k _ l s p v w w' κ κ' hl heq
  obtain ⟨-, hmul, hC, -⟩ := frobenius_laws_hold k l hl
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  change φ (frob0 l (w' : k⟦X⟧)) * φ X ^ ((l : ℤ) * κ') * φ ((v : k⟦X⟧) * X ^ s) =
    φ p * φ (w : k⟦X⟧) * φ X ^ κ at heq
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hfu : frob0 l (w' : k⟦X⟧) * frob0 l ((w'⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← hmul, Units.mul_inv, ← map_one (C : k →+* k⟦X⟧), hC]
  let A : k⟦X⟧ := frob0 l (w' : k⟦X⟧) * (v : k⟦X⟧) * ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hF : IsUnit (frob0 l (w' : k⟦X⟧)) := ⟨⟨_, _, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩
  have hA : IsUnit A := (hF.mul v.isUnit).mul (w⁻¹).isUnit
  have hww : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  set e : ℤ := (l : ℤ) * κ' + (s : ℤ) - κ with he
  have key : φ p = φ A * φ X ^ e := by
    have h1 : φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) = φ p := by
      rw [show φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) =
        φ p * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) * (φ X ^ κ * φ X ^ (-κ)) by ring, hww,
        ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one, mul_one]
    rw [← h1, ← heq]
    simp only [A, map_mul, map_pow]
    rw [he, sub_eq_add_neg, zpow_add₀ hx, zpow_add₀ hx, zpow_natCast]
    ring
  by_cases he0 : 0 ≤ e
  · refine ⟨he0, hA.unit, hφ ?_⟩
    rw [IsUnit.unit_spec, map_mul, map_pow, key, ← zpow_natCast, Int.toNat_of_nonneg he0]
  · exfalso
    push_neg at he0
    have hm : φ p * φ X ^ (-e) = φ A := by
      rw [key, mul_assoc, ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one]
    obtain ⟨m, hm'⟩ : ∃ m : ℕ, -e = (m : ℤ) + 1 := ⟨(-e - 1).toNat, by omega⟩
    rw [hm', zpow_add_one₀ hx, zpow_natCast, ← map_pow, ← map_mul, ← map_mul] at hm
    have h5 := congrArg constantCoeff (hφ hm)
    simp only [map_mul, constantCoeff_X, mul_zero] at h5
    exact (hA.map constantCoeff).ne_zero h5.symm

/- English proof (translation)
Simplify using `[gamSer]`.
-/
theorem gammaSeries_zero_eq {k : Type} [CommRing k] (un : k⟦X⟧) :
    gamSer 0 un = X * (1 + un * X) := by
  simp [gamSer]

/- English proof (translation)
Rewrite using `[map_add, map_add, hx, zero_add]`. Use `first`. Consider the case `(rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_X_pow_mul', if_neg (by norm_num), add_zero, coeff_zero_eq_constantCoeff_apply])`. Consider the case `simp [coeff_X_pow_mul']`.
-/
theorem coeff_one_add_X_mul_add_X_sq_mul {k : Type} [CommRing k] (x y z : k⟦X⟧) (hx : coeff 1 x = 0) :
    coeff 1 (x + X * y + X ^ 2 * z) = constantCoeff y := by
  rw [map_add, map_add, hx, zero_add]
  first
  | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_X_pow_mul', if_neg (by norm_num),
      add_zero, coeff_zero_eq_constantCoeff_apply])
  | simp [coeff_X_pow_mul']

/- English proof (translation)
Introduce `k _ un g c w κ heq`. Take `⟨hadd, hmul, hC, -, hX, -, hcc0⟩` from `gamma_laws_hold k 0 un`. Establish `e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f`. Introduce `f`. Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`.

Establish `h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y`. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by`. Rewrite using `[X_dvd_iff, map_sub, constantCoeff_C, sub_self]`. Establish `e : y = C (constantCoeff y) + X * q` using `by rw [← hq]; ring`.

Rewrite using `[e, hadd, hmul, hC, hX]`. Rewrite using `[map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]`. Rewrite using `[mul_assoc, e1, e1, map_mul, hcc0]`. Simplify using the standard rewrite rules. Establish `hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q`.

Introduce `f q`. Use `first`. Consider the case `(rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)`. Consider the case `(rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])`. Consider the case `(rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];`.

Simplify using `[coeff_zero_eq_constantCoeff_apply]`. Use the proof step `ring)`. Consider the case `(simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)`. Consider the case `(simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])`. Establish `hV : IsUnit (1 + un * X : k⟦X⟧)` using `by first`.

Consider the case `(rw [isUnit_iff_constantCoeff]; simp)`. Consider the case `exact isUnit_iff_constantCoeff.2 (by simp)`. Use `set V := hV.unit with hVdef`. Establish `hV0 : constantCoeff (V : k⟦X⟧) = 1` using `by rw [IsUnit.unit_spec]; simp`. Establish `hV1' : coeff 1 (V : k⟦X⟧) = constantCoeff un`.

Rewrite using `[IsUnit.unit_spec, map_add, coeff_one, if_neg one_ne_zero, zero_add, mul_comm, e1]`. Establish `hgs : gamSer 0 un = X * (V : k⟦X⟧)` using `by rw [gammaSeries_zero_eq, IsUnit.unit_spec]`. Establish `hVcc : ∀ m : ℤ, constantCoeff ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`. Introduce `m`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`.

Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow]`. Rewrite using `[zpow_neg, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow, inv_one]`. Establish `hVn : ∀ n : ℕ, coeff 1 ((V : k⟦X⟧) ^ n) = n * constantCoeff un`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, hc1, ih, hV1', map_pow, hV0, one_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hV1 : ∀ m : ℤ, coeff 1 ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = m * constantCoeff un`. Introduce `m`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, hVn, Int.cast_natCast]`. Establish `hcc_inv : constantCoeff (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`.

Rewrite using `[map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow, inv_one]`. Establish `hinv` using `hc1 ((V ^ n : (k⟦X⟧)ˣ) : k⟦X⟧) (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)`. Rewrite `hinv` using `[Units.mul_inv, coeff_one, if_neg one_ne_zero, hcc_inv, Units.val_pow_eq_pow_val, hVn, map_pow, hV0, one_pow]`. Rewrite using `[zpow_neg, zpow_natCast]`. Use `push_cast`.

Take the linear combination `-hinv`. Set `φ : k⟦X⟧ →+* LaurentSeries k` to `HahnSeries.ofPowerSeries ℤ k`. Establish `hφ : Function.Injective φ` using `HahnSeries.ofPowerSeries_injective`. Establish `hx : φ X ≠ 0` using `(map_ne_zero_iff φ hφ).2 X_ne_zero`. Establish `hVz : ∀ m : ℤ, φ ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = φ (V : k⟦X⟧) ^ m`.

Introduce `m`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Rewrite using `[zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]`. Rewrite using `[zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val, map_pow]`. Establish `hc : c = gam0 0 un (w : k⟦X⟧) * ((V ^ κ : (k⟦X⟧)ˣ) : k⟦X⟧) * (1 + X * g) * ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)`.

Apply `hφ` to reduce the goal to its premises. Establish `hw : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hxk : φ X ^ κ ≠ 0` using `zpow_ne_zero κ hx`. Express the relevant statement in the definitionally equal form `φ (gam0 0 un (w : k⟦X⟧)) * φ (gamSer 0 un) ^ κ * φ (1 + X * g) = φ c * φ (w : k⟦X⟧) * φ X ^ κ at heq`.

Rewrite `heq` using `[hgs, map_mul, mul_zpow]`. Apply `mul_right_cancel₀ hxk` to reduce the goal to its premises. Simplify using `only [map_mul, hVz]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hw, mul_one]`.

Use `_ = (φ c * φ (w : k⟦X⟧) * φ X ^ κ) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by ring`. Use `_ = _ := by rw [← heq]; ring`. Establish `hww0 : constantCoeff (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hww1 : coeff 1 (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) + constantCoeff (w : k⟦X⟧) * coeff 1 ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 0`.

Rewrite using `[← hc1, Units.mul_inv, coeff_one, if_neg one_ne_zero]`. Establish `hC1 : coeff 1 (1 + X * g) = constantCoeff g`. Rewrite using `[map_add, coeff_one, if_neg one_ne_zero, zero_add, e1]`. Establish `hC0 : constantCoeff (1 + X * g) = 1` using `by simp`. Rewrite using `[hc]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, hcc0, hVcc, hC0, mul_one]`. Conclude with `hww0`. Simplify using `only [hc1, map_mul, h1, hcc0, hVcc, hV1, hC0, hC1]`. Take the linear combination `hww1 + ((κ : k) * constantCoeff un + constantCoeff g) * hww0`.
-/
theorem theta_diagonal_holds : ThetaDiag := by
  intro k _ un g c w κ heq
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hV : IsUnit (1 + un * X : k⟦X⟧) := by
    first
    | (rw [isUnit_iff_constantCoeff]; simp)
    | exact isUnit_iff_constantCoeff.2 (by simp)
  set V := hV.unit with hVdef
  have hV0 : constantCoeff (V : k⟦X⟧) = 1 := by rw [IsUnit.unit_spec]; simp
  have hV1' : coeff 1 (V : k⟦X⟧) = constantCoeff un := by
    rw [IsUnit.unit_spec, map_add, coeff_one, if_neg one_ne_zero, zero_add, mul_comm, e1]
  have hgs : gamSer 0 un = X * (V : k⟦X⟧) := by rw [gammaSeries_zero_eq, IsUnit.unit_spec]
  have hVcc : ∀ m : ℤ, constantCoeff ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow]
    · rw [zpow_neg, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow,
        inv_one]
  have hVn : ∀ n : ℕ, coeff 1 ((V : k⟦X⟧) ^ n) = n * constantCoeff un := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hc1, ih, hV1', map_pow, hV0, one_pow]
      push_cast
      ring
  have hV1 : ∀ m : ℤ, coeff 1 ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = m * constantCoeff un := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, hVn, Int.cast_natCast]
    · have hcc_inv : constantCoeff (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
        rw [map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow, inv_one]
      have hinv := hc1 ((V ^ n : (k⟦X⟧)ˣ) : k⟦X⟧) (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
      rw [Units.mul_inv, coeff_one, if_neg one_ne_zero, hcc_inv, Units.val_pow_eq_pow_val, hVn,
        map_pow, hV0, one_pow] at hinv
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -hinv
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hVz : ∀ m : ℤ, φ ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = φ (V : k⟦X⟧) ^ m := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val,
        map_pow]
  have hc : c = gam0 0 un (w : k⟦X⟧) * ((V ^ κ : (k⟦X⟧)ˣ) : k⟦X⟧) * (1 + X * g) *
      ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by
    apply hφ
    have hw : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hxk : φ X ^ κ ≠ 0 := zpow_ne_zero κ hx
    change φ (gam0 0 un (w : k⟦X⟧)) * φ (gamSer 0 un) ^ κ * φ (1 + X * g) =
      φ c * φ (w : k⟦X⟧) * φ X ^ κ at heq
    rw [hgs, map_mul, mul_zpow] at heq
    apply mul_right_cancel₀ hxk
    simp only [map_mul, hVz]
    calc φ c * φ X ^ κ = φ c * φ X ^ κ * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) := by
          rw [hw, mul_one]
      _ = (φ c * φ (w : k⟦X⟧) * φ X ^ κ) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by ring
      _ = _ := by rw [← heq]; ring
  have hww0 : constantCoeff (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hww1 : coeff 1 (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) +
      constantCoeff (w : k⟦X⟧) * coeff 1 ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 0 := by
    rw [← hc1, Units.mul_inv, coeff_one, if_neg one_ne_zero]
  have hC1 : coeff 1 (1 + X * g) = constantCoeff g := by
    rw [map_add, coeff_one, if_neg one_ne_zero, zero_add, e1]
  have hC0 : constantCoeff (1 + X * g) = 1 := by simp
  rw [hc]
  refine ⟨?_, ?_⟩
  · simp only [map_mul, hcc0, hVcc, hC0, mul_one]
    exact hww0
  · simp only [hc1, map_mul, h1, hcc0, hVcc, hV1, hC0, hC1]
    linear_combination hww1 + ((κ : k) * constantCoeff un + constantCoeff g) * hww0

/- English proof (translation)
Introduce `k _ n un g D`. Take `⟨hadd, hmul, hC, -, hX, -, hcc0⟩` from `gamma_laws_hold k 0 un`. Establish `e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f`. Introduce `f`. Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`.

Establish `h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y`. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by`. Rewrite using `[X_dvd_iff, map_sub, constantCoeff_C, sub_self]`. Establish `e : y = C (constantCoeff y) + X * q` using `by rw [← hq]; ring`.

Rewrite using `[e, hadd, hmul, hC, hX]`. Rewrite using `[map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]`. Rewrite using `[mul_assoc, e1, e1, map_mul, hcc0]`. Simplify using the standard rewrite rules. Establish `hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q`.

Introduce `f q`. Use `first`. Consider the case `(rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)`. Consider the case `(rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])`. Consider the case `(rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];`.

Simplify using `[coeff_zero_eq_constantCoeff_apply]`. Use the proof step `ring)`. Consider the case `(simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)`. Consider the case `(simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])`. Establish `hcoef : ∀ M N : Matrix (Fin n) (Fin n) k⟦X⟧, (M * N).map (coeff 1) = M.map (coeff 1) * N.map constantCoeff + M.map constantCoeff * N.map (coeff 1)`.

Introduce `M N`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, hc1, Finset.sum_add_distrib]`. Use `set A := ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) with hA`. Use `set G := (g : Matrix (Fin n) (Fin n) k⟦X⟧) with hG`.

Establish `hAG : A * G = 1` using `Units.inv_mul g`. Establish `hGA : G * A = 1` using `Units.mul_inv g`. Establish `hone0 : (1 : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hAG0 : A.map constantCoeff * G.map constantCoeff = 1`. Rewrite using `[← Matrix.map_mul, hAG, hone0]`.

Establish `hGA0 : G.map constantCoeff * A.map constantCoeff = 1`. Rewrite using `[← Matrix.map_mul, hGA, hone0]`. Establish `hAG1 : A.map (coeff 1) * G.map constantCoeff + A.map constantCoeff * G.map (coeff 1) = 0`. Rewrite using `[← hcoef, hAG]`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply]`. Establish `hB0 : (1 + (X : k⟦X⟧) • D).map constantCoeff = 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply]`. Establish `hB1 : (1 + (X : k⟦X⟧) • D).map (coeff 1) = D.map constantCoeff`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply, e1]`. Establish `hC0 : (G.map (gam0 0 un)).map constantCoeff = G.map constantCoeff`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, hcc0]`.

Establish `hC1 : (G.map (gam0 0 un)).map (coeff 1) = G.map (coeff 1)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, h1]`. Establish `hθ : thetaOf (chgGam un g D) = A.map constantCoeff * D.map constantCoeff * G.map constantCoeff` using `by show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map (coeff 1) = _`. Rewrite using `[hcoef, hcoef, Matrix.map_mul, hB0, hB1, hC0, hC1, Matrix.mul_one, Matrix.mul_one, Matrix.add_mul, add_right_comm, hAG1, zero_add]`.

Use `⟨?_, hθ, ?_⟩` and prove the remaining obligations. Use `show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map constantCoeff = 1`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hB0, Matrix.mul_one, hC0, hAG0]`. Rewrite using `[hθ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hGA0, Matrix.one_mul]`.
-/
theorem theta_base_change_holds : ThetaBaseChange := by
  intro k _ n un g D
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hcoef : ∀ M N : Matrix (Fin n) (Fin n) k⟦X⟧, (M * N).map (coeff 1) =
      M.map (coeff 1) * N.map constantCoeff + M.map constantCoeff * N.map (coeff 1) := by
    intro M N
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, hc1,
      Finset.sum_add_distrib]
  set A := ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) with hA
  set G := (g : Matrix (Fin n) (Fin n) k⟦X⟧) with hG
  have hAG : A * G = 1 := Units.inv_mul g
  have hGA : G * A = 1 := Units.mul_inv g
  have hone0 : (1 : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hAG0 : A.map constantCoeff * G.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hAG, hone0]
  have hGA0 : G.map constantCoeff * A.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hGA, hone0]
  have hAG1 : A.map (coeff 1) * G.map constantCoeff + A.map constantCoeff * G.map (coeff 1) = 0 := by
    rw [← hcoef, hAG]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB0 : (1 + (X : k⟦X⟧) • D).map constantCoeff = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB1 : (1 + (X : k⟦X⟧) • D).map (coeff 1) = D.map constantCoeff := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, e1]
  have hC0 : (G.map (gam0 0 un)).map constantCoeff = G.map constantCoeff := by
    ext i j
    simp only [Matrix.map_apply, hcc0]
  have hC1 : (G.map (gam0 0 un)).map (coeff 1) = G.map (coeff 1) := by
    ext i j
    simp only [Matrix.map_apply, h1]
  have hθ : thetaOf (chgGam un g D) = A.map constantCoeff * D.map constantCoeff * G.map constantCoeff := by
    show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map (coeff 1) = _
    rw [hcoef, hcoef, Matrix.map_mul, hB0, hB1, hC0, hC1, Matrix.mul_one, Matrix.mul_one,
      Matrix.add_mul, add_right_comm, hAG1, zero_add]
  refine ⟨?_, hθ, ?_⟩
  · show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map constantCoeff = 1
    rw [Matrix.map_mul, Matrix.map_mul, hB0, Matrix.mul_one, hC0, hAG0]
  · rw [hθ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hGA0, Matrix.one_mul]

/- English proof (translation)
Introduce `k _ n l h g g' P hl`. Establish `hs : HasSubst (X ^ l : k⟦X⟧)` using `HasSubst.X_pow hl.ne'`. Set `fr : k⟦X⟧ →+* k⟦X⟧` to `(substAlgHom hs).toRingHom`. Establish `hfr : ∀ y, fr y = frob0 l y` using `fun y => by`. Express the relevant statement in the definitionally equal form `substAlgHom hs y = _`.

Rewrite using `[coe_substAlgHom hs]`. Both sides reduce to the same expression. Set `g2 : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ` to `Units.map (fr.mapMatrix : Matrix (Fin n) (Fin n) k⟦X⟧ →+* Matrix (Fin n) (Fin n) k⟦X⟧).toMonoidHom g'`. Establish `hg2 : (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l) = (g2 : Matrix (Fin n) (Fin n) k⟦X⟧)`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `frob0 l _ = fr _`. Rewrite using `[hfr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨M, hM⟩`. Use `⟨((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * M * (g : Matrix (Fin n) (Fin n) k⟦X⟧), ?_⟩` and prove the remaining obligations.

Unfold `chgPhi`. Rewrite using `[hg2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv, mul_one, hM, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul]`. Introduce `x t hx`.

Conclude with `minors_dvd_mul_holds (k⟦X⟧) n n n n t x _ P _ hx`.
-/
theorem frobenius_base_change_holds : PhiBaseChange := by
  intro k _ n l h g g' P hl
  have hs : HasSubst (X ^ l : k⟦X⟧) := HasSubst.X_pow hl.ne'
  let fr : k⟦X⟧ →+* k⟦X⟧ := (substAlgHom hs).toRingHom
  have hfr : ∀ y, fr y = frob0 l y := fun y => by
    change substAlgHom hs y = _
    rw [coe_substAlgHom hs]; rfl
  let g2 : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ :=
    Units.map (fr.mapMatrix :
      Matrix (Fin n) (Fin n) k⟦X⟧ →+* Matrix (Fin n) (Fin n) k⟦X⟧).toMonoidHom g'
  have hg2 : (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l) = (g2 : Matrix (Fin n) (Fin n) k⟦X⟧) := by
    refine Matrix.ext fun a b => ?_
    change frob0 l _ = fr _
    rw [hfr]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * M *
      (g : Matrix (Fin n) (Fin n) k⟦X⟧), ?_⟩
    unfold chgPhi
    rw [hg2]
    calc _ = ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * (P *
          ((g2 : Matrix (Fin n) (Fin n) k⟦X⟧) *
            ((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧)) * M) *
          (g : Matrix (Fin n) (Fin n) k⟦X⟧) := by simp only [mul_assoc]
      _ = _ := by
        rw [Units.mul_inv, mul_one, hM, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul]
  · intro x t hx
    exact minors_dvd_mul_holds (k⟦X⟧) n n n n t x _ P _ hx

section Five

variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]

/- English proof (translation)
Rewrite using `[map_natCast, CharP.cast_eq_zero]`.
-/
theorem reduction_natCast_prime_eq_zero (l : ℕ) [CharP F l] (red : O →+* F) : red (l : O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

/- English proof (translation)
Use `first`. Consider the case `exact constantCoeff_map red y`. Consider the case `rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]`.
-/
theorem constantCoeff_map_eq (red : O →+* F) (y : O⟦X⟧) :
    constantCoeff (PowerSeries.map red y) = red (constantCoeff y) := by
  first
  | exact constantCoeff_map red y
  | rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

/- English proof (translation)
Rewrite using `[map_pow, map_sub, map_X, map_C, map_natCast, CharP.cast_eq_zero, map_zero, sub_zero]`.
-/
theorem map_X_sub_C_prime_pow_eq_X_pow (l : ℕ) [CharP F l] (red : O →+* F) (m : ℕ) :
    PowerSeries.map red ((X - C (l : O)) ^ m) = X ^ m := by
  rw [map_pow, map_sub, map_X, map_C, map_natCast, CharP.cast_eq_zero, map_zero, sub_zero]

/- English proof (translation)
Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `key : ∀ k : ℕ, ∃ s : ℤ_[l], (u : ℤ_[l]) ^ k = 1 + (l : ℤ_[l]) * ((k : ℤ_[l]) * c) + (l : ℤ_[l]) ^ 2 * s`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `succ k ih`. Take `⟨s, hs⟩` from `ih`. Use `⟨(k : ℤ_[l]) * c ^ 2 + s + s * (l : ℤ_[l]) * c, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, hs, hu]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `ht : ∃ t : ℤ_[l], r = -((m : ℤ) : ℤ_[l]) * c + (l : ℤ_[l]) * t`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Take `⟨s, hs⟩` from `key k`. Establish `h1 : ((u ^ (-(k : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (u : ℤ_[l]) ^ k = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hr, hs]`. Establish `h2 : (l : ℤ_[l]) * (r + (k : ℤ_[l]) * c + (l : ℤ_[l]) * (r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s)) = 0`. Take the linear combination `h1`.

Establish `h3` using `(mul_eq_zero.1 h2).resolve_left hl0`. Use `⟨-(r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s), ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `h3`. Take `⟨s, hs⟩` from `key k`.

Establish `h1 : ((u ^ (-(-(k : ℤ))) : ℤ_[l]ˣ) : ℤ_[l]) = (u : ℤ_[l]) ^ k`. Rewrite using `[neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]`. Rewrite `h1` using `[hr, hs]`. Establish `h2 : (l : ℤ_[l]) * (r - (k : ℤ_[l]) * c - (l : ℤ_[l]) * s) = 0`. Take the linear combination `h1`.

Establish `h3` using `(mul_eq_zero.1 h2).resolve_left hl0`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `h3`. Take `⟨t, ht⟩` from `ht`.

Rewrite using `[ht]`. Simplify using `only [map_add, map_mul, map_neg, map_intCast, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reduction_log_unit_pow_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l] (red : O →+* F)
    (u : ℤ_[l]ˣ) (c r : ℤ_[l]) (m : ℤ) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hr : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * r) :
    red (algebraMap ℤ_[l] O r) = -red (algebraMap ℤ_[l] O c) * ((m : ℤ) : F) := by
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have key : ∀ k : ℕ, ∃ s : ℤ_[l],
      (u : ℤ_[l]) ^ k = 1 + (l : ℤ_[l]) * ((k : ℤ_[l]) * c) + (l : ℤ_[l]) ^ 2 * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨(k : ℤ_[l]) * c ^ 2 + s + s * (l : ℤ_[l]) * c, ?_⟩
      rw [pow_succ, hs, hu]
      push_cast
      ring
  have ht : ∃ t : ℤ_[l], r = -((m : ℤ) : ℤ_[l]) * c + (l : ℤ_[l]) * t := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(k : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (u : ℤ_[l]) ^ k = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        simp
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r + (k : ℤ_[l]) * c +
          (l : ℤ_[l]) * (r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s)) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨-(r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s), ?_⟩
      push_cast
      linear_combination h3
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(-(k : ℤ))) : ℤ_[l]ˣ) : ℤ_[l]) = (u : ℤ_[l]) ^ k := by
        rw [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r - (k : ℤ_[l]) * c - (l : ℤ_[l]) * s) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨s, ?_⟩
      push_cast
      linear_combination h3
  obtain ⟨t, ht⟩ := ht
  rw [ht]
  simp only [map_add, map_mul, map_neg, map_intCast, map_natCast, CharP.cast_eq_zero, zero_mul,
    add_zero]
  ring

/- English proof (translation)
Introduce `ι l h _ O F _ _ _ _ red N u c wt hu hN i`. Take `⟨-, -, hdet, hD, hTh⟩` from `hN`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hdet i`. Use `⟨v, ?_⟩` and prove the remaining obligations.

Rewrite `hv` using `[Matrix.det_fin_one, Fin.sum_univ_one]`. Conclude with `hv`. Take `⟨r, hr, hcp⟩` from `hTh i`. Establish `h1 : (N.Th i).charpoly = Polynomial.X - Polynomial.C (N.Th i 0 0)` using `by show (Matrix.charmatrix (N.Th i)).det = _`. Rewrite using `[Matrix.det_fin_one, Matrix.charmatrix_apply_eq]`.

Rewrite `hcp` using `[h1, Fin.prod_univ_one]`. Establish `h2` using `congrArg (fun p => Polynomial.coeff p 0) hcp`. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at h2`. Establish `h3` using `(evaluation_congruence_holds O (l : O) (N.Th i 0 0) (N.D i 0 0) (hD i 0 0)).2 F red (by rw [map_natCast, CharP.cast_eq_zero])`. Rewrite using `[h3, h2, reduction_log_unit_pow_eq l red u c (r 0) (wt i) hu (hr 0)]`.
-/
theorem rank_one_model_holds : RankOneModel := by
  intro ι l h _ O F _ _ _ _ red N u c wt hu hN i
  obtain ⟨-, -, hdet, hD, hTh⟩ := hN
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := hdet i
    refine ⟨v, ?_⟩
    rw [Matrix.det_fin_one, Fin.sum_univ_one] at hv
    exact hv
  · obtain ⟨r, hr, hcp⟩ := hTh i
    have h1 : (N.Th i).charpoly = Polynomial.X - Polynomial.C (N.Th i 0 0) := by
      show (Matrix.charmatrix (N.Th i)).det = _
      rw [Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    rw [h1, Fin.prod_univ_one] at hcp
    have h2 := congrArg (fun p => Polynomial.coeff p 0) hcp
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_inj] at h2
    have h3 := (evaluation_congruence_holds O (l : O) (N.Th i 0 0) (N.D i 0 0) (hD i 0 0)).2 F red
      (by rw [map_natCast, CharP.cast_eq_zero])
    rw [h3, h2, reduction_log_unit_pow_eq l red u c (r 0) (wt i) hu (hr 0)]

/- English proof (translation)
Conclude with `((hc.map (algebraMap ℤ_[l] O)).map red).ne_zero`.
-/
theorem reduction_algebraMap_unit_ne_zero (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (red : O →+* F) (c : ℤ_[l])
    (hc : IsUnit c) : red (algebraMap ℤ_[l] O c) ≠ 0 := by
  exact ((hc.map (algebraMap ℤ_[l] O)).map red).ne_zero

/- English proof (translation)
Take `⟨-, -, -, hD, hTh⟩` from `hN`. Take `⟨r, hr, hcp⟩` from `hTh i`. Establish `h3` using `(theta_base_change_holds F n W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red))).2.2`. Establish `hD' : ((W.N.D i).map (PowerSeries.map W.red)).map constantCoeff = (W.N.Th i).map W.red`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply]`. Rewrite using `[constantCoeff_map_eq]`. Conclude with `(evaluation_congruence_holds O (l : O) (W.N.Th i a b) (W.N.D i a b) (hD i a b)).2 F W.red (reduction_natCast_prime_eq_zero l W.red)`. Use `show (thetaOf (chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red)))).charpoly = _`. Rewrite using `[h3, hD', Matrix.charpoly_map, hcp, Polynomial.map_prod]`.

Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, reduction_log_unit_pow_eq l W.red u c (r j) (U' i j) hu (hr j)]`.
-/
theorem charpoly_theta_eq_prod (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hN : LatW l W.N h u U') (i : ι) :
    (thetaOf (W.Gam i)).charpoly = ∏ j, (Polynomial.X -
      Polynomial.C (-W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F))) := by
  obtain ⟨-, -, -, hD, hTh⟩ := hN
  obtain ⟨r, hr, hcp⟩ := hTh i
  have h3 := (theta_base_change_holds F n W.unbar (W.g i)
    ((W.N.D i).map (PowerSeries.map W.red))).2.2
  have hD' : ((W.N.D i).map (PowerSeries.map W.red)).map constantCoeff = (W.N.Th i).map W.red := by
    ext a b
    simp only [Matrix.map_apply]
    rw [constantCoeff_map_eq]
    exact (evaluation_congruence_holds O (l : O) (W.N.Th i a b) (W.N.D i a b) (hD i a b)).2 F W.red
      (reduction_natCast_prime_eq_zero l W.red)
  show (thetaOf (chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red)))).charpoly = _
  rw [h3, hD', Matrix.charpoly_map, hcp, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    reduction_log_unit_pow_eq l W.red u c (r j) (U' i j) hu (hr j)]

/- English proof (translation)
Take `⟨hP, -, -, -, -⟩` from `hN`. Take `⟨M, hM⟩` from `hP i`. Establish `hmap : (W.N.P i).map (PowerSeries.map W.red) * M.map (PowerSeries.map W.red) = ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧)`. Rewrite using `[← Matrix.map_mul, hM]`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Use `split_ifs`. Simplify using `only [mul_one, map_X_sub_C_prime_pow_eq_X_pow]`. Simplify using `only [mul_zero, map_zero]`. Conclude with `(frobenius_base_change_holds F n l h (W.g i) (W.g (σ i)) _ (Fact.out : l.Prime).pos).1 ⟨_, hmap⟩`.
-/
theorem frobenius_mul_eq_X_pow_smul_one (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) :
    ∃ M, W.Phi l σ i * M = ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
  obtain ⟨hP, -, -, -, -⟩ := hN
  obtain ⟨M, hM⟩ := hP i
  have hmap : (W.N.P i).map (PowerSeries.map W.red) * M.map (PowerSeries.map W.red) =
      ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
    rw [← Matrix.map_mul, hM]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp only [mul_one, map_X_sub_C_prime_pow_eq_X_pow]
    · simp only [mul_zero, map_zero]
  exact (frobenius_base_change_holds F n l h (W.g i) (W.g (σ i)) _ (Fact.out : l.Prime).pos).1 ⟨_, hmap⟩

/- English proof (translation)
Establish `h2` using `(minors_divide_all_holds (O⟦X⟧) n n r _ _).1 (hN.2.1 i r S hS)`. Apply `(frobenius_base_change_holds F n l h _ _ _ (Fact.out : l.Prime).pos).2` to reduce the goal to its premises. Introduce `f g _ _`. Conclude with `(minor_reduction_holds O F W.red (l : O) n r S (W.N.P i) f g (reduction_natCast_prime_eq_zero l W.red)).2 (h2 f g)`.
-/
theorem minorsDvd_frobenius_of_sum_bound (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) (r S : ℕ)
    (hS : ∀ J : Finset (Fin n), J.card = r → (S : ℤ) ≤ ∑ j ∈ J, U' i j) :
    MinorsDvd ((X : F⟦X⟧) ^ S) r (W.Phi l σ i) := by
  have h2 := (minors_divide_all_holds (O⟦X⟧) n n r _ _).1 (hN.2.1 i r S hS)
  apply (frobenius_base_change_holds F n l h _ _ _ (Fact.out : l.Prime).pos).2
  intro f g _ _
  exact (minor_reduction_holds O F W.red (l : O) n r S (W.N.P i) f g (reduction_natCast_prime_eq_zero l W.red)).2 (h2 f g)

/- English proof (translation)
Take `⟨⟨hu, -, -⟩, -, hwt, -, -, -, hPhiE, -⟩` from `hW.1`. Take `⟨⟨v, hv⟩, -⟩` from `rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu (hW.2.2 s) i`. Establish `hmv : PowerSeries.map W.red ((W.Npsi s).P i 0 0) = ((Units.map (PowerSeries.map W.red).toMonoidHom v : (F⟦X⟧)ˣ) : F⟦X⟧) * X ^ (wt i s).toNat`. Rewrite using `[hv, map_mul, map_X_sub_C_prime_pow_eq_X_pow]`. Both sides reduce to the same expression.

Establish `heq` using `hPhiE i s`. Rewrite `heq` using `[hmv]`. Take `⟨h1, u0, hu0⟩` from `frobenius_diagonal_holds F l (wt i s).toNat _ _ (W.w i s) (W.w (σ i) s) (kap i s) (kap (σ i) s) (Fact.out : l.Prime).pos heq`. Establish `hw : (((wt i s).toNat : ℕ) : ℤ) = wt i s` using `Int.toNat_of_nonneg (hwt i s).1`. Rewrite `h1`, `hu0` using `[hw]`.

Conclude with `⟨h1, u0, hu0⟩`.
-/
theorem frobenius_diagonal_entry_eq_unit_mul (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hW : WInputs W σ l h u c U' wt kap) (i : ι) (s : Fin t) :
    0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      ∃ u0 : (F⟦X⟧)ˣ, W.Phi l σ i (W.pos s) (W.pos s) =
        (u0 : F⟦X⟧) * X ^ ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
  obtain ⟨⟨hu, -, -⟩, -, hwt, -, -, -, hPhiE, -⟩ := hW.1
  obtain ⟨⟨v, hv⟩, -⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  have hmv : PowerSeries.map W.red ((W.Npsi s).P i 0 0) =
      ((Units.map (PowerSeries.map W.red).toMonoidHom v : (F⟦X⟧)ˣ) : F⟦X⟧) * X ^ (wt i s).toNat := by
    rw [hv, map_mul, map_X_sub_C_prime_pow_eq_X_pow]
    rfl
  have heq := hPhiE i s
  rw [hmv] at heq
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_holds F l (wt i s).toNat _ _ (W.w i s) (W.w (σ i) s) (kap i s)
    (kap (σ i) s) (Fact.out : l.Prime).pos heq
  have hw : (((wt i s).toNat : ℕ) : ℤ) = wt i s := Int.toNat_of_nonneg (hwt i s).1
  rw [hw] at h1 hu0
  exact ⟨h1, u0, hu0⟩

/- English proof (translation)
Take `⟨⟨hu, -, hun⟩, -, -, -, -, -, -, hGamE⟩` from `hW.1`. Take `⟨-, hD⟩` from `rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu (hW.2.2 s) i`. Take `⟨-, hcc1⟩` from `theta_diagonal_holds F W.unbar (PowerSeries.map W.red ((W.Npsi s).D i 0 0)) (W.Gam i (W.pos s) (W.pos s)) (W.w i s) (kap i s) (hGamE i s)`. Take `⟨e, he⟩` from `((unit_series_constant_holds l O hl2 (u : ℤ_[l]) c hu).2 W.un hun).2`. Use `show coeff 1 (W.Gam i (W.pos s) (W.pos s)) = _`.

Rewrite using `[hcc1]`. Unfold `WLat.unbar`. Rewrite using `[constantCoeff_map_eq, constantCoeff_map_eq, hD, he, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_diagonal_entry_eq (l h : ℕ) [Fact l.Prime] [IsDomain O] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hl2 : l ≠ 2) (hW : WInputs W σ l h u c U' wt kap) (i : ι)
    (s : Fin t) :
    thetaOf (W.Gam i) (W.pos s) (W.pos s) =
      -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
  obtain ⟨⟨hu, -, hun⟩, -, -, -, -, -, -, hGamE⟩ := hW.1
  obtain ⟨-, hD⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  obtain ⟨-, hcc1⟩ := theta_diagonal_holds F W.unbar (PowerSeries.map W.red ((W.Npsi s).D i 0 0))
    (W.Gam i (W.pos s) (W.pos s)) (W.w i s) (kap i s) (hGamE i s)
  obtain ⟨e, he⟩ := ((unit_series_constant_holds l O hl2 (u : ℤ_[l]) c hu).2 W.un hun).2
  show coeff 1 (W.Gam i (W.pos s) (W.pos s)) = _
  rw [hcc1]
  unfold WLat.unbar
  rw [constantCoeff_map_eq, constantCoeff_map_eq, hD, he, map_add, map_mul, map_natCast,
    CharP.cast_eq_zero, zero_mul, add_zero]
  push_cast
  ring

/- English proof (translation)
Introduce `ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW i s`. Take `⟨h1, u0, hu0⟩` from `frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `frobenius_mul_eq_X_pow_smul_one l h W σ u U' hW.2.1 i`. Take `⟨-, -, -, ⟨-, hb⟩, hPhiT, -, -, -⟩` from `hW.1`.

Establish `hline` using `block_height_on_line_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b (W.pos s) X_ne_zero (hPhiT i) hM (hb s)`. Rewrite `hline` using `[hu0]`. Use `set e := (l : ℤ) * kap (σ i) s + wt i s - kap i s with he`. Establish `hdvd : (X : F⟦X⟧) ^ e.toNat ∣ X ^ h` using `⟨u0 * M (W.pos s) (W.pos s), by rw [← hline]; ring⟩`. Establish `hle : e.toNat ≤ h` using `by first`.

Consider the case `exact (pow_dvd_pow_iff X_ne_zero X_prime.not_unit).1 hdvd`. Consider the case `exact (pow_dvd_pow_iff_le X_ne_zero X_prime.not_unit).1 hdvd`. Establish `h2 : ((e.toNat : ℕ) : ℤ) ≤ (h : ℤ)` using `by exact_mod_cast hle`. Combine the linear relations using `[Int.toNat_of_nonneg h1]`.
-/
theorem alpha_bounds_hold : AlphaBounds := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW i s
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s
  refine ⟨h1, ?_⟩
  obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hW.2.1 i
  obtain ⟨-, -, -, ⟨-, hb⟩, hPhiT, -, -, -⟩ := hW.1
  have hline := block_height_on_line_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b (W.pos s) X_ne_zero
    (hPhiT i) hM (hb s)
  rw [hu0] at hline
  set e := (l : ℤ) * kap (σ i) s + wt i s - kap i s with he
  have hdvd : (X : F⟦X⟧) ^ e.toNat ∣ X ^ h :=
    ⟨u0 * M (W.pos s) (W.pos s), by rw [← hline]; ring⟩
  have hle : e.toNat ≤ h := by
    first
    | exact (pow_dvd_pow_iff X_ne_zero X_prime.not_unit).1 hdvd
    | exact (pow_dvd_pow_iff_le X_ne_zero X_prime.not_unit).1 hdvd
  have h2 : ((e.toNat : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hle
  linarith [Int.toNat_of_nonneg h1]

/- English proof (translation)
Introduce `ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap cc hl2 hW hcc`. Establish `hW'` using `hW`. Take `⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩` from `hW'`. Use `⟨reduction_algebraMap_unit_ne_zero l W.red c hc, hinj, hpos, ?_, ?_, ?_, hΦ, ?_, ?_⟩` and prove the remaining obligations. Introduce `i a b hab`.

Express the relevant statement in the definitionally equal form `coeff 1 (W.Gam i a b) = 0`. Rewrite using `[hΓ i hab, map_zero]`. Introduce `i`. Conclude with `charpoly_theta_eq_prod l h W u c U' hu hN i`. Introduce `i s`.

Conclude with `theta_diagonal_entry_eq l h W σ u c U' _ kap hl2 hW i s`. Introduce `i s`. Conclude with `(frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' _ kap hW i s).2`. Introduce `i`. Conclude with `(minors_divide_all_holds (F⟦X⟧) n n t _ _).1 (minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i t (cc i) (hcc i)) W.pos W.pos`.
-/
theorem weight_properties_of_inputs : WPropsOfInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap cc hl2 hW hcc
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  refine ⟨reduction_algebraMap_unit_ne_zero l W.red c hc, hinj, hpos, ?_, ?_, ?_, hΦ, ?_, ?_⟩
  · intro i a b hab
    change coeff 1 (W.Gam i a b) = 0
    rw [hΓ i hab, map_zero]
  · intro i
    exact charpoly_theta_eq_prod l h W u c U' hu hN i
  · intro i s
    exact theta_diagonal_entry_eq l h W σ u c U' _ kap hl2 hW i s
  · intro i s
    exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' _ kap hW i s).2
  · intro i
    exact (minors_divide_all_holds (F⟦X⟧) n n t _ _).1
      (minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i t (cc i) (hcc i)) W.pos W.pos

/- English proof (translation)
Introduce `ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap hl2 hW`. Establish `hα` using `alpha_bounds_hold ι σ l h t n O F W u c U' _ kap hl2 hW`. Establish `hU` using `hW.1.2.1`. Establish `hwt` using `hW.1.2.2.1`. Establish `hmain : ∀ cc : ι → ℕ, (∀ i (J : Finset (Fin n)), J.card = t → (cc i : ℤ) ≤ ∑ j ∈ J, U' i j) → _` using `fun cc hcc => twisted_block_bounds ι σ l h t n F (W.toWData l c σ) U' bot kap cc Fact.out (weight_properties_of_inputs ι σ l h t n O F W u c U' bot kap cc hl2 hW hcc) hwt hα`.

Establish `h0` using `hmain (fun _ => 0) (fun i J _ => by`. Simplify using `using Finset.sum_nonneg fun j _ => (hU i j).1)`. Use `⟨h0.1, h0.2.1, ?_⟩` and prove the remaining obligations. Introduce `i`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hA0 : 0 ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s)` using `Finset.sum_nonneg fun s _ => by have := (hα i s).1; linarith`. Generalize the expression as in `hA : ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) = A at *`. Establish `h1` using `(hmain (fun i' => if i' = i then A.toNat + 1 else 0) (by`. Introduce `i' J hJ`.

Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Use `hcon J hJ` as an intermediate fact. Simplify using `only [if_true]`. Use `push_cast`.

Rewrite using `[Int.toNat_of_nonneg hA0]`. Use linear arithmetic over natural numbers and integers. Simplify `Finset.sum_nonneg fun j _ => (hU i' j).1)).2.2 i` using `[hi]`. Rewrite `h1` using `[hA]`. Simplify using `only [if_true] at h1`.

Move the coercions through the operations in `at h1`. Rewrite `h1` using `[Int.toNat_of_nonneg hA0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem weight_lemma_from_inputs : LemmaWFromInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' _ kap hl2 hW
  have hU := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hmain : ∀ cc : ι → ℕ,
      (∀ i (J : Finset (Fin n)), J.card = t → (cc i : ℤ) ≤ ∑ j ∈ J, U' i j) → _ :=
    fun cc hcc => twisted_block_bounds ι σ l h t n F (W.toWData l c σ) U' bot kap cc Fact.out
      (weight_properties_of_inputs ι σ l h t n O F W u c U' bot kap cc hl2 hW hcc) hwt hα
  have h0 := hmain (fun _ => 0) (fun i J _ => by
    simpa using Finset.sum_nonneg fun j _ => (hU i j).1)
  refine ⟨h0.1, h0.2.1, ?_⟩
  intro i
  by_contra hcon
  push Not at hcon
  have hA0 : 0 ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) :=
    Finset.sum_nonneg fun s _ => by have := (hα i s).1; linarith
  generalize hA : ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) = A at *
  have h1 := (hmain (fun i' => if i' = i then A.toNat + 1 else 0) (by
    intro i' J hJ
    by_cases hi : i' = i
    · subst hi
      have := hcon J hJ
      simp only [if_true]
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega
    · simpa [hi] using Finset.sum_nonneg fun j _ => (hU i' j).1)).2.2 i
  rw [hA] at h1
  simp only [if_true] at h1
  push_cast at h1
  rw [Int.toNat_of_nonneg hA0] at h1
  omega

/- English proof (translation)
Introduce `ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW`. Establish `hα` using `alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW`. Establish `hW'` using `hW`. Take `⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩` from `hW'`. Establish `hlp : l.Prime` using `Fact.out`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i s`. Conclude with `shiftBound_holds ι σ l h (fun i => kap i s) (fun i => wt i s) hlp.two_le (fun i => hwt i s) (fun i => hα i s) i`. Introduce `i`. Establish `hΘ : (thetaOf (W.Gam i)).BlockTriangular W.b`.

Introduce `a b hab`. Express the relevant statement in the definitionally equal form `coeff 1 (W.Gam i a b) = 0`. Rewrite using `[hΓ i hab, map_zero]`. Establish `h1` using `charpolyDiagBlocks_holds F n (thetaOf (W.Gam i)) W.b (Finset.univ.image W.pos) (fun j => -W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F)) hΘ (by`. Introduce `s hs' j hj`.

Take `⟨s0, _, rfl⟩` from `Finset.mem_image.mp hs'`. Conclude with `hpos s0 j hj) (charpoly_theta_eq_prod l h W u c U' hu hN i)`. Rewrite `h1` using `[Finset.image_val_of_injOn hinj.injOn, Multiset.map_map]`. Apply `map_cast_le_of_map_neg_mul_le l hlp F (W.red (algebraMap ℤ_[l] O c)) (reduction_algebraMap_unit_ne_zero l W.red c hc)` to reduce the goal to its premises. Establish `e : ((fun s => thetaOf (W.Gam i) s s) ∘ W.pos) = fun s : Fin t => -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F)`.

Use function extensionality and compare the values at `s`. Conclude with `theta_diagonal_entry_eq l h W σ u c U' wt kap hl2 hW i s`. Rewrite `h1` using `[e]`. Conclude with `h1`. Introduce `ν hν i`.

Establish `hI : Function.Injective (fun s => W.b (W.pos s))` using `fun x y hxy => hinj (hpos y (W.pos x) hxy)`. Generalize the expression as in `hch : Finset.univ.image (fun s => W.b (W.pos s)) = ch at *`. Generalize the expression as in `hm : ∑ r ∈ Finset.univ.image W.b \ ch, ν r = m at *`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `hA0 : 0 ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h`. Use `add_nonneg (Finset.sum_nonneg fun s _ => ?_) (by positivity)` and prove the remaining obligations. Use `(hα i s).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `hA : ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h = A at *`.

Establish `hmin` using `minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i (t + m) (A.toNat + 1) (fun J hJ => by`. Use `hcon J hJ` as an intermediate fact. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg hA0]`. Use the proof step `omega)`.

Set `al : ℕ → ℕ` to `fun r => if hr : ∃ s, W.b (W.pos s) = r then ((l : ℤ) * kap (σ i) (Classical.choose hr) + wt i (Classical.choose hr) - kap i (Classical.choose hr)).toNat else 0`. Establish `hal : ∀ s, al (W.b (W.pos s)) = ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat`. Introduce `s`. Establish `hr : ∃ s', W.b (W.pos s') = W.b (W.pos s)` using `⟨s, rfl⟩`. Simplify using `only [al, dif_pos hr]`.

Rewrite using `[hI (Classical.choose_spec hr)]`. Establish `hcard : ch.card = t`. Rewrite using `[← hch, Finset.card_image_of_injective _ hI]`. Simplify using the standard rewrite rules. Take `⟨M, hM⟩` from `frobenius_mul_eq_X_pow_smul_one l h W σ u U' hN i`.

Establish `hbl` using `(block_height_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b X_ne_zero (hΦ i) hM).2`. Establish `h1` using `minor_bound_extra_holds (F⟦X⟧) X n h (A.toNat + 1) (W.Phi l σ i) W.b ch al ν X_prime (hΦ i) (by`. Rewrite using `[← hch]`. Introduce `r hr`. Take `⟨s, _, rfl⟩` from `Finset.mem_image.1 hr`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ _))`. Use the proof step `(by`. Introduce `r hr`. Rewrite `hr` using `[← hch]`. Take `⟨s, _, rfl⟩` from `Finset.mem_image.1 hr`.

Use `⟨W.pos s, fun j => ⟨hpos s j, fun h0 => by rw [h0]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hal s]`. Conclude with `(frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s).2)`. Use the proof step `(fun r hr => ⟨⟨_, hbl r⟩, hν r hr⟩)`. Use the proof step `(by rw [hcard, hm]; exact hmin)`.

Establish `hsum : ∑ r ∈ ch, al r = ∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat`. Rewrite using `[← hch, Finset.sum_image (fun x _ y _ hxy => hI hxy)]`. Conclude with `Finset.sum_congr rfl fun s _ => hal s`. Rewrite `h1` using `[hsum, hm]`. Establish `h2 : ((∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat : ℕ) : ℤ) = ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s)`.

Rewrite using `[Nat.cast_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (hα i s).1]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((A.toNat + 1 : ℕ) : ℤ) ≤ ((∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat + m * h : ℕ) : ℤ)` using `by exact_mod_cast h1`.

Move the coercions through the operations in `at h3 h2`. Rewrite `h3` using `[h2, hA, Int.toNat_of_nonneg hA0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem weight_lemma_full : LemmaWFull := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  have hlp : l.Prime := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact shiftBound_holds ι σ l h (fun i => kap i s) (fun i => wt i s) hlp.two_le
      (fun i => hwt i s) (fun i => hα i s) i
  · intro i
    have hΘ : (thetaOf (W.Gam i)).BlockTriangular W.b := by
      intro a b hab
      change coeff 1 (W.Gam i a b) = 0
      rw [hΓ i hab, map_zero]
    have h1 := charpolyDiagBlocks_holds F n (thetaOf (W.Gam i)) W.b (Finset.univ.image W.pos)
      (fun j => -W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F)) hΘ
      (by
        intro s hs' j hj
        obtain ⟨s0, _, rfl⟩ := Finset.mem_image.mp hs'
        exact hpos s0 j hj) (charpoly_theta_eq_prod l h W u c U' hu hN i)
    rw [Finset.image_val_of_injOn hinj.injOn, Multiset.map_map] at h1
    apply map_cast_le_of_map_neg_mul_le l hlp F (W.red (algebraMap ℤ_[l] O c)) (reduction_algebraMap_unit_ne_zero l W.red c hc)
    have e : ((fun s => thetaOf (W.Gam i) s s) ∘ W.pos) =
        fun s : Fin t => -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
      funext s
      exact theta_diagonal_entry_eq l h W σ u c U' wt kap hl2 hW i s
    rw [e] at h1
    exact h1
  · intro ν hν i
    have hI : Function.Injective (fun s => W.b (W.pos s)) :=
      fun x y hxy => hinj (hpos y (W.pos x) hxy)
    generalize hch : Finset.univ.image (fun s => W.b (W.pos s)) = ch at *
    generalize hm : ∑ r ∈ Finset.univ.image W.b \ ch, ν r = m at *
    by_contra hcon
    push Not at hcon
    have hA0 : 0 ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h := by
      refine add_nonneg (Finset.sum_nonneg fun s _ => ?_) (by positivity)
      have := (hα i s).1; linarith
    generalize hA : ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h = A
      at *
    have hmin := minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i (t + m) (A.toNat + 1) (fun J hJ => by
      have := hcon J hJ
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega)
    let al : ℕ → ℕ := fun r => if hr : ∃ s, W.b (W.pos s) = r then
      ((l : ℤ) * kap (σ i) (Classical.choose hr) + wt i (Classical.choose hr) -
        kap i (Classical.choose hr)).toNat else 0
    have hal : ∀ s, al (W.b (W.pos s)) = ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      intro s
      have hr : ∃ s', W.b (W.pos s') = W.b (W.pos s) := ⟨s, rfl⟩
      simp only [al, dif_pos hr]
      rw [hI (Classical.choose_spec hr)]
    have hcard : ch.card = t := by
      rw [← hch, Finset.card_image_of_injective _ hI]; simp
    obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hN i
    have hbl := (block_height_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b X_ne_zero (hΦ i) hM).2
    have h1 := minor_bound_extra_holds (F⟦X⟧) X n h (A.toNat + 1) (W.Phi l σ i) W.b ch al ν X_prime
      (hΦ i)
      (by
        rw [← hch]
        intro r hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (by
        intro r hr
        rw [← hch] at hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        refine ⟨W.pos s, fun j => ⟨hpos s j, fun h0 => by rw [h0]⟩, ?_⟩
        rw [hal s]
        exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s).2)
      (fun r hr => ⟨⟨_, hbl r⟩, hν r hr⟩)
      (by rw [hcard, hm]; exact hmin)
    have hsum : ∑ r ∈ ch, al r = ∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      rw [← hch, Finset.sum_image (fun x _ y _ hxy => hI hxy)]
      exact Finset.sum_congr rfl fun s _ => hal s
    rw [hsum, hm] at h1
    have h2 : ((∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat : ℕ) : ℤ) =
        ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Int.toNat_of_nonneg (hα i s).1]; ring
    have h3 : ((A.toNat + 1 : ℕ) : ℤ) ≤ ((∑ s : Fin t,
        ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat + m * h : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 h2
    rw [h2, hA, Int.toNat_of_nonneg hA0] at h3
    omega

/- English proof (translation)
Use `set T := Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)) with hT`. Break down `Nat.lt_or_ge m N with hmN | hmN` into its components or cases. Use `set v := f ⟨m, hmN⟩`. Establish `h1 : ∀ x ∈ T \ J, f x ≤ v`. Introduce `x hx`.

Establish `hx1 : m ≤ (x : ℕ)` using `(Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2`. Conclude with `hf (show (⟨m, hmN⟩ : Fin N) ≤ x from hx1)`. Establish `h2 : ∀ x ∈ J \ T, v ≤ f x`. Introduce `x hx`. Establish `hx2 : ¬ m ≤ (x : ℕ)` using `fun h => (Finset.mem_sdiff.1 hx).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)`.

Conclude with `hf (show x ≤ (⟨m, hmN⟩ : Fin N) from by show (x : ℕ) ≤ m; omega)`. Establish `hc : (T \ J).card = (J \ T).card`. Establish `e1` using `Finset.card_sdiff_add_card_inter T J`. Establish `e2` using `Finset.card_sdiff_add_card_inter J T`. Rewrite `e2` using `[Finset.inter_comm]`.

Use linear arithmetic over natural numbers and integers. Establish `s1` using `Finset.sum_le_card_nsmul (T \ J) f v h1`. Establish `s2` using `Finset.card_nsmul_le_sum (J \ T) f v h2`. Rewrite `s1` using `[hc]`. Rewrite `s1`, `s2` using `[nsmul_eq_mul]`.

Establish `split : ∀ S U : Finset (Fin N), ∑ x ∈ S \ U, f x + ∑ x ∈ S ∩ U, f x = ∑ x ∈ S, f x`. Introduce `S U`. Use `first`. Consider the case `exact Finset.sum_sdiff_add_sum_inter S U f`. Consider the case `(rw [add_comm]; exact Finset.sum_inter_add_sum_diff S U f)`.

Consider the case `(rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S U), Finset.sdiff_union_inter])`. Establish `e3` using `split T J`. Establish `e4` using `split J T`. Rewrite `e4` using `[Finset.inter_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT0 : T = ∅` using `Finset.filter_eq_empty_iff.2 (fun x _ => by have := x.2; omega)`. Establish `hJ0 : J = ∅` using `Finset.card_eq_zero.1 (by rw [hJ, hT0, Finset.card_empty])`. Rewrite using `[hT0, hJ0]`.
-/
theorem sum_tail_le_sum_of_antitone {N : ℕ} (f : Fin N → ℤ) (hf : Antitone f) (m : ℕ) (J : Finset (Fin N))
    (hJ : J.card = (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)), f a ≤ ∑ a ∈ J, f a := by
  set T := Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)) with hT
  rcases Nat.lt_or_ge m N with hmN | hmN
  · set v := f ⟨m, hmN⟩
    have h1 : ∀ x ∈ T \ J, f x ≤ v := by
      intro x hx
      have hx1 : m ≤ (x : ℕ) := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2
      exact hf (show (⟨m, hmN⟩ : Fin N) ≤ x from hx1)
    have h2 : ∀ x ∈ J \ T, v ≤ f x := by
      intro x hx
      have hx2 : ¬ m ≤ (x : ℕ) := fun h =>
        (Finset.mem_sdiff.1 hx).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact hf (show x ≤ (⟨m, hmN⟩ : Fin N) from by show (x : ℕ) ≤ m; omega)
    have hc : (T \ J).card = (J \ T).card := by
      have e1 := Finset.card_sdiff_add_card_inter T J
      have e2 := Finset.card_sdiff_add_card_inter J T
      rw [Finset.inter_comm] at e2
      omega
    have s1 := Finset.sum_le_card_nsmul (T \ J) f v h1
    have s2 := Finset.card_nsmul_le_sum (J \ T) f v h2
    rw [hc] at s1
    rw [nsmul_eq_mul] at s1 s2
    have split : ∀ S U : Finset (Fin N), ∑ x ∈ S \ U, f x + ∑ x ∈ S ∩ U, f x = ∑ x ∈ S, f x := by
      intro S U
      first
      | exact Finset.sum_sdiff_add_sum_inter S U f
      | (rw [add_comm]; exact Finset.sum_inter_add_sum_diff S U f)
      | (rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S U), Finset.sdiff_union_inter])
    have e3 := split T J
    have e4 := split J T
    rw [Finset.inter_comm] at e4
    linarith
  · have hT0 : T = ∅ := Finset.filter_eq_empty_iff.2 (fun x _ => by have := x.2; omega)
    have hJ0 : J = ∅ := Finset.card_eq_zero.1 (by rw [hJ, hT0, Finset.card_empty])
    rw [hT0, hJ0]

/- English proof (translation)
Establish `hm2 : (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).map Fin.valEmbedding = Finset.Ico m N`. Use extensionality with `x`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, h1, rfl⟩`.

Conclude with `⟨h1, a.2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨x, h2⟩, h1, rfl⟩`. Rewrite using `[← Finset.card_map Fin.valEmbedding, hm2, Nat.card_Ico]`.
-/
theorem card_filter_le_val_eq_sub (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card = N - m := by
  have hm2 : (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).map Fin.valEmbedding =
      Finset.Ico m N := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, h1, rfl⟩
      exact ⟨h1, a.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm2, Nat.card_Ico]

/- English proof (translation)
Introduce `ι _ σ k j t q l h _ O F _ _ _ _ _ W u c U U' bot cst kap τ hl2 hsmall hW hU hU' hblock hlink hU0 hsum hrows`. Establish `hα` using `alpha_bounds_hold ι σ l h t _ O F W u c U' _ kap hl2 hW`. Establish `hH1` using `hW.1.2.1`. Establish `hwt` using `hW.1.2.2.1`. Establish `hT0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' τ a` using `Finset.sum_nonneg fun a _ => (hH1 τ a).1`.

Establish `hcard` using `card_filter_le_val_eq_sub (k + j + t + q) (k + j + q) (by omega)`. Use `weightExchangeFull_holds ι σ k j t q l h F (W.toWData l c σ) U U' bot cst kap (fun i => if i = τ then (∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' τ a).toNat else 0) τ Fact.out hsmall (weight_properties_of_inputs ι σ l h t _ O F W u c U' bot …` and prove the remaining obligations. Introduce `i J hJ`. Distinguish the cases in `hi : i = τ`. Substitute `hi` using the available equality.

Simplify using `only [if_true]`. Rewrite using `[Int.toNat_of_nonneg hT0]`. Conclude with `sum_tail_le_sum_of_antitone (U' i) (hU' i).antitone _ J (by rw [hJ, hcard]; omega)`. Simplify `Finset.sum_nonneg fun a _ => (hH1 i a).1` using `[hi]`. Simplify using `only [if_true]`.

Rewrite using `[Int.toNat_of_nonneg hT0]`.
-/
theorem weight_exponents_from_inputs : WEFromInputs := by
  intro ι _ σ k j t q l h _ O F _ _ _ _ _ W u c U U' bot cst kap τ hl2 hsmall hW hU hU' hblock hlink
    hU0 hsum hrows
  classical
  have hα := alpha_bounds_hold ι σ l h t _ O F W u c U' _ kap hl2 hW
  have hH1 := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hT0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a := Finset.sum_nonneg fun a _ => (hH1 τ a).1
  have hcard := card_filter_le_val_eq_sub (k + j + t + q) (k + j + q) (by omega)
  refine weightExchangeFull_holds ι σ k j t q l h F (W.toWData l c σ) U U' bot cst kap
    (fun i => if i = τ then (∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' τ a).toNat else 0) τ Fact.out hsmall
    (weight_properties_of_inputs ι σ l h t _ O F W u c U' bot kap _ hl2 hW ?_) hwt hα hU hU' hblock hlink
    hU0 (hH1 τ) hsum hrows ?_
  · intro i J hJ
    by_cases hi : i = τ
    · subst hi
      simp only [if_true]
      rw [Int.toNat_of_nonneg hT0]
      exact sum_tail_le_sum_of_antitone (U' i) (hU' i).antitone _ J (by rw [hJ, hcard]; omega)
    · simpa [hi] using Finset.sum_nonneg fun a _ => (hH1 i a).1
  · simp only [if_true]
    rw [Int.toNat_of_nonneg hT0]

end Five

/- English proof (translation)
Introduce `O _ _ I _ x L _ _ em jj hx hem hC hX S`. Take `⟨w, hw⟩` from `hX`. Establish `hj : jj (X - C x) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧)`. Rewrite using `[← hw, mul_assoc, Units.mul_inv, mul_one]`. Proceed by induction on `S with`.

Consider the case `zero => intro m _`. Simplify using the standard rewrite rules. Consider the case `succ S ih`. Introduce `m hm`. Take `⟨f₁, a, rfl⟩` from `(linear_division_holds O I x hx).1 m`.

Establish `h1 : (X : L⟦X⟧) ∣ jj ((X - C x) * f₁ + C a)` using `dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero S)) hm`. Rewrite `h1` using `[map_add, map_mul, hj, hC]`. Establish `h2 : (X : L⟦X⟧) ∣ C (em a)` using `(dvd_add_right ((dvd_mul_right _ _).mul_right _)).1 h1`. Establish `h3 : em a = 0`. Use `PowerSeries.X_dvd_iff.1 h2` as an intermediate fact.

Simplify using `using this`. Establish `h4 : a = 0` using `hem (by simpa using h3)`. Substitute `h4` using the available equality. Rewrite `hm` using `[map_add, map_mul, hj, map_zero, map_zero, add_zero, pow_succ', mul_assoc]`. Establish `h5 : (X : L⟦X⟧) ^ S ∣ ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * jj f₁` using `(mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 hm`.

Rewrite `h5` using `[Units.dvd_mul_left]`. Rewrite using `[map_zero, add_zero, pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih f₁ h5)`.
-/
theorem order_descent_holds : OrderDescent := by
  intro O _ _ I _ x L _ _ em jj hx hem hC hX S
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C x) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  induction S with
  | zero => intro m _; simp
  | succ S ih =>
    intro m hm
    obtain ⟨f₁, a, rfl⟩ := (linear_division_holds O I x hx).1 m
    have h1 : (X : L⟦X⟧) ∣ jj ((X - C x) * f₁ + C a) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero S)) hm
    rw [map_add, map_mul, hj, hC] at h1
    have h2 : (X : L⟦X⟧) ∣ C (em a) :=
      (dvd_add_right ((dvd_mul_right _ _).mul_right _)).1 h1
    have h3 : em a = 0 := by
      have := PowerSeries.X_dvd_iff.1 h2
      simpa using this
    have h4 : a = 0 := hem (by simpa using h3)
    subst h4
    rw [map_add, map_mul, hj, map_zero, map_zero, add_zero, pow_succ', mul_assoc] at hm
    have h5 : (X : L⟦X⟧) ^ S ∣ ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * jj f₁ :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 hm
    rw [Units.dvd_mul_left] at h5
    rw [map_zero, add_zero, pow_succ']
    exact mul_dvd_mul_left _ (ih f₁ h5)

def pi0SubstHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] :
    O⟦X⟧ →+* O⟦X⟧ :=
  (substAlgHom (hasSubst_pi0_alt l O) : O⟦X⟧ →ₐ[O] O⟦X⟧).toRingHom

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact congrFun (coe_substAlgHom (hasSubst_pi0_alt l O)) f`.
-/
theorem pi0SubstHom_apply (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (f : O⟦X⟧) : pi0SubstHom l O f = inc l O f := by
  first
  | rfl
  | exact congrFun (coe_substAlgHom (hasSubst_pi0_alt l O)) f

/- English proof (translation)
Unfold `inc`. Rewrite using `[subst_C]`. Both sides reduce to the same expression.
-/
theorem pi0Subst_C (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (a : O) :
    inc l O (C a) = C a := by
  unfold inc
  rw [subst_C]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[RingHom.comp_apply, pi0SubstHom_apply]`.
-/
theorem coe_comp_pi0SubstHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) :
    (⇑(jj.comp (pi0SubstHom l O))) = fun y => jj (inc l O y) := by
  funext y
  rw [RingHom.comp_apply, pi0SubstHom_apply]

/- English proof (translation)
Establish `h2` using `RingHom.map_det (jj.comp (pi0SubstHom l O)) M`. Rewrite `h2` using `[RingHom.mapMatrix_apply, coe_comp_pi0SubstHom]`. Conclude with `h2`.
-/
theorem pi0Subst_det_map (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) {t : ℕ} (M : Matrix (Fin t) (Fin t) O⟦X⟧) :
    jj (inc l O M.det) = (M.map (fun y => jj (inc l O y))).det := by
  have h2 := RingHom.map_det (jj.comp (pi0SubstHom l O)) M
  rw [RingHom.mapMatrix_apply, coe_comp_pi0SubstHom] at h2
  exact h2

/- English proof (translation)
Introduce `l _ O L _ _ _ _ I ζ em u b jj hl2 hζ hζI hem hb hloc`. Take `⟨hC, hX, -⟩` from `hloc`. Take `⟨w, hw⟩` from `hX`. Establish `hj : jj (X - C (ζ ^ b - 1)) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧)`. Rewrite using `[← hw, mul_assoc, Units.mul_inv, mul_one]`.

Establish `hbI : ζ ^ b - 1 ∈ I`. Establish `h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i` using `(mul_geom_sum ζ b).symm`. Rewrite using `[h1]`. Conclude with `I.mul_mem_right _ hζI`. Establish `hlI : (l : O) ∈ I`.

Take `⟨s, hs⟩` from `r3_divisibility_holds l O ζ hl2 hζ b hb`. Establish `h2` using `congrArg constantCoeff hs`. Rewrite `h2` using `[map_sub, map_mul, map_sub, constantCoeff_pi0 l O, constantCoeff_C, constantCoeff_C, constantCoeff_X]`. Establish `h3 : (l : O) = (ζ ^ b - 1) * constantCoeff s` using `by linear_combination -h2`. Rewrite using `[h3]`.

Conclude with `I.mul_mem_right _ hbI`. Establish `hl0 : (l : O) ≠ 0`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Conclude with `(hζ.neZero').out`. Establish `hq0 : ∃ z : L⟦X⟧, IsUnit z ∧ jj (q0 l O) = X * z`.

Take `⟨g, hg, -⟩` from `r3_unit_holds l O hl2`. Establish `hq` using `q_roots_holds l O ζ hζ`. Establish `hU : IsUnit (∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1)))`. Use `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_` and prove the remaining obligations. Introduce `b' hb'`.

Rewrite `hb'` using `[Finset.mem_erase]`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Establish `e : (X - C (ζ ^ b' - 1) : O⟦X⟧) = (X - C (ζ ^ b - 1)) + C (ζ ^ b - ζ ^ b')`. Rewrite using `[map_sub, map_sub, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, map_add, hj, hC, map_add, map_mul, constantCoeff_X, zero_mul, zero_add, constantCoeff_C]`. Use `IsUnit.mk0 _ ?_` and prove the remaining obligations. Introduce `h0`. Establish `h1 : ζ ^ b - ζ ^ b' = 0` using `hem (by rw [h0, map_zero])`. Establish `h2 : b = b'` using `hζ.pow_inj (Finset.mem_Ioo.1 hb).2 (Finset.mem_Ioo.1 hb'.2).2 (sub_eq_zero.1 h1)`.

Conclude with `hb'.1 h2.symm`. Use `⟨((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * (jj (g : O⟦X⟧) * ∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Units.isUnit _).mul (((Units.isUnit g).map jj).mul hU)`. Rewrite using `[hg, hq, map_mul, map_prod, ← Finset.mul_prod_erase _ _ hb, hj]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨z, hz, hzq⟩` from `hq0`. Use `⟨hlI, hl0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hzq]`. Conclude with `associated_mul_unit_left _ _ hz`. Introduce `y a hya`.

Take `⟨s, hs⟩` from `hya`. Establish `hy : y = (X - C (l : O)) * s + C a` using `by linear_combination hs`. Rewrite using `[hy, ← pi0SubstHom_apply, map_add, map_mul, pi0SubstHom_apply, pi0SubstHom_apply, pi0SubstHom_apply, inc_X_sub_l_eq_q0, pi0Subst_C, map_add, map_mul, hzq, hC, map_add, map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul, zero_add, constantCoeff_C]`.
-/
theorem localization_facts_hold : LocFacts := by
  intro l _ O L _ _ _ _ I ζ em u b jj hl2 hζ hζI hem hb hloc
  obtain ⟨hC, hX, -⟩ := hloc
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C (ζ ^ b - 1)) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  have hbI : ζ ^ b - 1 ∈ I := by
    have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
    rw [h1]
    exact I.mul_mem_right _ hζI
  have hlI : (l : O) ∈ I := by
    obtain ⟨s, hs⟩ := r3_divisibility_holds l O ζ hl2 hζ b hb
    have h2 := congrArg constantCoeff hs
    rw [map_sub, map_mul, map_sub, constantCoeff_pi0 l O, constantCoeff_C, constantCoeff_C,
      constantCoeff_X] at h2
    have h3 : (l : O) = (ζ ^ b - 1) * constantCoeff s := by linear_combination -h2
    rw [h3]
    exact I.mul_mem_right _ hbI
  have hl0 : (l : O) ≠ 0 := by
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact (hζ.neZero').out

  have hq0 : ∃ z : L⟦X⟧, IsUnit z ∧ jj (q0 l O) = X * z := by
    obtain ⟨g, hg, -⟩ := r3_unit_holds l O hl2
    have hq := q_roots_holds l O ζ hζ
    have hU : IsUnit (∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))) := by
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_
      intro b' hb'
      rw [Finset.mem_erase] at hb'
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have e : (X - C (ζ ^ b' - 1) : O⟦X⟧) = (X - C (ζ ^ b - 1)) + C (ζ ^ b - ζ ^ b') := by
        rw [map_sub, map_sub, map_sub]; ring
      rw [e, map_add, hj, hC, map_add, map_mul, constantCoeff_X, zero_mul, zero_add,
        constantCoeff_C]
      refine IsUnit.mk0 _ ?_
      intro h0
      have h1 : ζ ^ b - ζ ^ b' = 0 := hem (by rw [h0, map_zero])
      have h2 : b = b' := hζ.pow_inj (Finset.mem_Ioo.1 hb).2 (Finset.mem_Ioo.1 hb'.2).2
        (sub_eq_zero.1 h1)
      exact hb'.1 h2.symm
    refine ⟨((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * (jj (g : O⟦X⟧) *
      ∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))), ?_, ?_⟩
    · exact (Units.isUnit _).mul (((Units.isUnit g).map jj).mul hU)
    · rw [hg, hq, map_mul, map_prod, ← Finset.mul_prod_erase _ _ hb, hj]
      ring
  obtain ⟨z, hz, hzq⟩ := hq0
  refine ⟨hlI, hl0, ?_, ?_⟩
  · rw [hzq]
    exact associated_mul_unit_left _ _ hz
  · intro y a hya
    obtain ⟨s, hs⟩ := hya
    have hy : y = (X - C (l : O)) * s + C a := by linear_combination hs
    rw [hy, ← pi0SubstHom_apply, map_add, map_mul, pi0SubstHom_apply, pi0SubstHom_apply,
      pi0SubstHom_apply, inc_X_sub_l_eq_q0, pi0Subst_C, map_add, map_mul, hzq, hC, map_add, map_mul,
      map_mul, constantCoeff_X, zero_mul, zero_mul, zero_add, constantCoeff_C]

/- English proof (translation)
Conclude with `gamma_mod_q_holds O lam n D Th h a b`.
-/
theorem one_add_X_smul_sub_C_dvd {O : Type} [CommRing O] (lam : O) {n : ℕ}
    (D : Matrix (Fin n) (Fin n) O⟦X⟧) (Th : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, (X - C lam) ∣ D a b - C (Th a b)) (a b : Fin n) :
    (X - C lam) ∣ (1 + (X : O⟦X⟧) • D) a b - C ((1 + lam • Th) a b) := by
  exact gamma_mod_q_holds O lam n D Th h a b

/- English proof (translation)
Establish `hr0 : ∀ f : L⟦X⟧, constantCoeff (rescale υ f) = constantCoeff f` using `fun f => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul]`. Establish `hD : (Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) = Matrix.diagonal (fun j => C (υ ^ a j) * (X : L⟦X⟧) ^ a j)`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `only [map_pow, rescale_X, mul_pow]`. Rewrite `h` using `[Matrix.map_mul, hD, ← Matrix.mul_assoc]`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun h i) j`.

Rewrite `hij` using `[Matrix.mul_diagonal, Matrix.mul_diagonal]`. Establish `hX : (X : L⟦X⟧) ^ a j ≠ 0` using `pow_ne_zero _ X_ne_zero`. Establish `h2 : (Γ * G.map (rescale υ)) i j * C (υ ^ a j) = G i j`. Apply `mul_right_cancel₀ hX` to reduce the goal to its premises. Rewrite using `[mul_assoc, hij]`.

Establish `h3` using `congrArg constantCoeff h2`. Rewrite `h3` using `[map_mul, constantCoeff_C, Matrix.mul_apply, map_sum]`. Rewrite using `[Matrix.mul_diagonal, Matrix.map_apply, ← h3, Matrix.mul_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hr0]`.
-/
theorem constantCoeff_conj_diagonal_rescale {L : Type} [Field L] {n : ℕ} (Γ G : Matrix (Fin n) (Fin n) L⟦X⟧) (υ : L)
    (a : Fin n → ℕ)
    (h : Γ * (G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)) :
    Γ.map constantCoeff * G.map constantCoeff * Matrix.diagonal (fun j => υ ^ a j) =
      G.map constantCoeff := by
  have hr0 : ∀ f : L⟦X⟧, constantCoeff (rescale υ f) = constantCoeff f := fun f => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale,
      pow_zero, one_mul]
  have hD : (Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      Matrix.diagonal (fun j => C (υ ^ a j) * (X : L⟦X⟧) ^ a j) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext j
    simp only [map_pow, rescale_X, mul_pow]
  rw [Matrix.map_mul, hD, ← Matrix.mul_assoc] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal] at hij
  have hX : (X : L⟦X⟧) ^ a j ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (Γ * G.map (rescale υ)) i j * C (υ ^ a j) = G i j := by
    apply mul_right_cancel₀ hX
    rw [mul_assoc, hij]
  have h3 := congrArg constantCoeff h2
  rw [map_mul, constantCoeff_C, Matrix.mul_apply, map_sum] at h3
  rw [Matrix.mul_diagonal, Matrix.map_apply, ← h3, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hr0]

/- English proof (translation)
Introduce `ι l h n _ O L _ _ _ _ I _ ζ em jj N u c U' hl2 hu hζ hζI hem hloc hU hN`. Take `⟨hP5, hTh, hloc4⟩` from `hN`. Establish `hl3 : 1 ∈ Finset.Ioo 0 l`. Use `(Fact.out : l.Prime).two_le` as an intermediate fact. Rewrite using `[Finset.mem_Ioo]`.

Use linear arithmetic over natural numbers and integers. Establish `hsum : ∀ i (J : Finset (Fin n)), ((∑ j ∈ J, (U' i j).toNat : ℕ) : ℤ) = ∑ j ∈ J, U' i j`. Introduce `i J`. Rewrite using `[Nat.cast_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (hU i j))`.

Establish `hW1 : ∀ i, ∃ M : Matrix (Fin n) (Fin n) O⟦X⟧, N.P i * M = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)`. Introduce `i`. Take `⟨Q, hQ⟩` from `hP5 i`. Conclude with `height_descent_holds l O hl2 n h (N.P i) Q hQ`. Take `⟨hlI, hl0, hq0X, hev⟩` from `localization_facts_hold l O L I ζ em (u : ℤ_[l]) 1 (jj 1) hl2 hζ hζI hem hl3 (hloc 1 hl3)`.

Use `⟨hW1, ?_, ?_, hTh, ?_⟩` and prove the remaining obligations. Introduce `i r S hS f g hf hg`. Take `⟨m', hm'⟩` from `roots_descent_holds l O I ζ hl2 hζ hζI S ((N.P i).submatrix f g).det (by`. Introduce `b hb`. Establish `hbI : ζ ^ b - 1 ∈ I`.

Establish `h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i` using `(mul_geom_sum ζ b).symm`. Rewrite using `[h1]`. Conclude with `I.mul_mem_right _ hζI`. Take `⟨hC, hX, -⟩` from `hloc b hb`. Use `order_descent_holds O I (ζ ^ b - 1) L em (jj b) hbI hem hC hX S _ ?_` and prove the remaining obligations.

Take `⟨G, H, hGH, -⟩` from `hloc4 i b hb`. Rewrite using `[pi0Subst_det_map, ← Matrix.submatrix_map, hGH]`. Use `diagonal_minors_holds L⟦X⟧ n r S X (fun a => (U' i a).toNat) G H ?_ f g hf hg` and prove the remaining obligations. Introduce `J hJ`. Establish `h1` using `hS J hJ`.

Rewrite `h1` using `[← hsum i J]`. Conclude with `h1)` after adjusting the coercions. Conclude with `⟨m', hm'⟩`. Introduce `i`. Take `⟨M, hM⟩` from `hW1 i`.

Establish `hdet` using `congrArg Matrix.det hM`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]`. Establish `hp : Prime (X - C (l : O) : O⟦X⟧)` using `linear_prime_holds O I (l : O) hlI`. Take `⟨e, -, hass⟩` from `(dvd_prime_pow hp (h * n)).1 ⟨M.det, hdet.symm⟩`. Take `⟨G, H, hGH, -⟩` from `hloc4 i 1 hl3`.

Establish `h1 : Associated ((jj 1).comp (pi0SubstHom l O) (N.P i).det) ((jj 1).comp (pi0SubstHom l O) ((X - C (l : O)) ^ e))` using `hass.map _`. Rewrite `h1` using `[RingHom.comp_apply, RingHom.comp_apply, pi0SubstHom_apply, pi0SubstHom_apply, inc_pow, inc_X_sub_l_eq_q0, map_pow, pi0Subst_det_map, hGH, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]`. Establish `hG : IsUnit (G : Matrix (Fin n) (Fin n) L⟦X⟧).det` using `(Matrix.isUnit_iff_isUnit_det _).1 G.isUnit`. Establish `hH : IsUnit (H : Matrix (Fin n) (Fin n) L⟦X⟧).det` using `(Matrix.isUnit_iff_isUnit_det _).1 H.isUnit`. Establish `h2 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat)) ((G : Matrix (Fin n) (Fin n) L⟦X⟧).det * X ^ (∑ j, (U' i j).toNat) * (H : Matrix (Fin n) (Fin n) L⟦X⟧).det)` using `((associated_mul_unit_left _ _ hH).trans (associated_unit_mul_left _ _ hG)).symm`.

Establish `h3 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat)) ((X : L⟦X⟧) ^ e)` using `(h2.trans h1).trans (hq0X.pow_pow)`. Establish `hXu : ¬ IsUnit (X : L⟦X⟧)` using `PowerSeries.X_prime.not_isUnit`. Establish `h4 : ∑ j, (U' i j).toNat = e` using `le_antisymm ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.dvd) ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.symm.dvd)`. Establish `h5 : (∑ j, U' i j).toNat = e`. Rewrite using `[← hsum i Finset.univ, Int.toNat_natCast, h4]`.

Rewrite using `[h5]`. Take `⟨v, hv⟩` from `hass.symm`. Conclude with `⟨v, by rw [← hv, mul_comm]⟩`. Introduce `i`. Use `choose e he using fun j => theta_congruence_padic l u c (U' i j) hu`.

Use `⟨fun j => -(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j, he, ?_⟩` and prove the remaining obligations. Take `⟨G, H, -, hγ⟩` from `hloc4 i 1 hl3`. Establish `hk` using `constantCoeff_conj_diagonal_rescale _ _ _ _ hγ`. Establish `hA : ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj 1 (inc l O y))).map constantCoeff = (1 + (l : O) • N.Th i).map em` using `by ext1 x y`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]`.

Conclude with `hev _ _ (one_add_X_smul_sub_C_dvd (l : O) (N.D i) (N.Th i) (hTh i) x y)`. Rewrite `hk` using `[hA]`. Establish `hunit : ∀ j, (u : ℤ_[l]) ^ (U' i j).toNat * (1 + (l : ℤ_[l]) * (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) = 1`. Introduce `j`. Rewrite using `[← he j, ← Units.val_pow_eq_pow_val, ← Units.val_mul]`.

Establish `: u ^ (U' i j).toNat * u ^ (-(U' i j)) = 1`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg (hU i j), ← zpow_add, add_neg_cancel, zpow_zero]`. Rewrite using `[this, Units.val_one]`. Set `G0 : (Matrix (Fin n) (Fin n) L)ˣ` to `Units.map (RingHom.mapMatrix (constantCoeff (R := L))).toMonoidHom G`. Establish `hG0 : (G0 : Matrix (Fin n) (Fin n) L) = (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff` using `rfl`.

Use `charpoly_diagonal_holds O L em n (N.Th i) (1 + (l : O) • N.Th i) (l : O) (fun j => algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) G0 hem hl0` and prove the remaining obligations. Use `rfl ?_`. Rewrite using `[hG0]`. Establish `hdd : Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) * Matrix.diagonal (fun j => em (1 + (l : O) * algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) = (1 : Matrix (Fin n) (Fin n) L)`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Use `congrArg (fun z => em (algebraMap ℤ_[l] O z)) (hunit j)` as an intermediate fact. Simplify using `only [map_mul, map_pow, map_add, map_one, map_natCast] at this`. Simplify using `only [map_mul, map_add, map_one, map_natCast]`.

Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdd, Matrix.mul_one]`. Use `_ = (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff * Matrix.diagonal (fun j => em (1 + (l : O) * algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) := by`. Rewrite using `[← Matrix.mul_assoc, hk]`.
-/
theorem weight_lattice_of_norm : LatWOfN := by
  intro ι l h n _ O L _ _ _ _ I _ ζ em jj N u c U' hl2 hu hζ hζI hem hloc hU hN
  obtain ⟨hP5, hTh, hloc4⟩ := hN
  have hl3 : 1 ∈ Finset.Ioo 0 l := by
    have := (Fact.out : l.Prime).two_le
    rw [Finset.mem_Ioo]; omega
  have hsum : ∀ i (J : Finset (Fin n)),
      ((∑ j ∈ J, (U' i j).toNat : ℕ) : ℤ) = ∑ j ∈ J, U' i j := by
    intro i J
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (hU i j))
  have hW1 : ∀ i, ∃ M : Matrix (Fin n) (Fin n) O⟦X⟧,
      N.P i * M = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧) := by
    intro i
    obtain ⟨Q, hQ⟩ := hP5 i
    exact height_descent_holds l O hl2 n h (N.P i) Q hQ
  obtain ⟨hlI, hl0, hq0X, hev⟩ :=
    localization_facts_hold l O L I ζ em (u : ℤ_[l]) 1 (jj 1) hl2 hζ hζI hem hl3 (hloc 1 hl3)
  refine ⟨hW1, ?_, ?_, hTh, ?_⟩
  ·
    intro i r S hS f g hf hg
    obtain ⟨m', hm'⟩ := roots_descent_holds l O I ζ hl2 hζ hζI S ((N.P i).submatrix f g).det (by
      intro b hb
      have hbI : ζ ^ b - 1 ∈ I := by
        have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
        rw [h1]
        exact I.mul_mem_right _ hζI
      obtain ⟨hC, hX, -⟩ := hloc b hb
      refine order_descent_holds O I (ζ ^ b - 1) L em (jj b) hbI hem hC hX S _ ?_
      obtain ⟨G, H, hGH, -⟩ := hloc4 i b hb
      rw [pi0Subst_det_map, ← Matrix.submatrix_map, hGH]
      refine diagonal_minors_holds L⟦X⟧ n r S X (fun a => (U' i a).toNat) G H ?_ f g hf hg
      intro J hJ
      have h1 := hS J hJ
      rw [← hsum i J] at h1
      exact_mod_cast h1)
    exact ⟨m', hm'⟩
  ·
    intro i
    obtain ⟨M, hM⟩ := hW1 i
    have hdet := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]
      at hdet
    have hp : Prime (X - C (l : O) : O⟦X⟧) := linear_prime_holds O I (l : O) hlI
    obtain ⟨e, -, hass⟩ := (dvd_prime_pow hp (h * n)).1 ⟨M.det, hdet.symm⟩
    obtain ⟨G, H, hGH, -⟩ := hloc4 i 1 hl3
    have h1 : Associated ((jj 1).comp (pi0SubstHom l O) (N.P i).det)
        ((jj 1).comp (pi0SubstHom l O) ((X - C (l : O)) ^ e)) := hass.map _
    rw [RingHom.comp_apply, RingHom.comp_apply, pi0SubstHom_apply, pi0SubstHom_apply,
      inc_pow, inc_X_sub_l_eq_q0, map_pow, pi0Subst_det_map, hGH, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum] at h1
    have hG : IsUnit (G : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 G.isUnit
    have hH : IsUnit (H : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 H.isUnit
    have h2 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat))
        ((G : Matrix (Fin n) (Fin n) L⟦X⟧).det * X ^ (∑ j, (U' i j).toNat) *
          (H : Matrix (Fin n) (Fin n) L⟦X⟧).det) :=
      ((associated_mul_unit_left _ _ hH).trans (associated_unit_mul_left _ _ hG)).symm
    have h3 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat)) ((X : L⟦X⟧) ^ e) :=
      (h2.trans h1).trans (hq0X.pow_pow)
    have hXu : ¬ IsUnit (X : L⟦X⟧) := PowerSeries.X_prime.not_isUnit
    have h4 : ∑ j, (U' i j).toNat = e :=
      le_antisymm ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.dvd)
        ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.symm.dvd)
    have h5 : (∑ j, U' i j).toNat = e := by
      rw [← hsum i Finset.univ, Int.toNat_natCast, h4]
    rw [h5]
    obtain ⟨v, hv⟩ := hass.symm
    exact ⟨v, by rw [← hv, mul_comm]⟩
  ·
    intro i
    choose e he using fun j => theta_congruence_padic l u c (U' i j) hu
    refine ⟨fun j => -(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j, he, ?_⟩
    obtain ⟨G, H, -, hγ⟩ := hloc4 i 1 hl3
    have hk := constantCoeff_conj_diagonal_rescale _ _ _ _ hγ
    have hA : ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj 1 (inc l O y))).map constantCoeff =
        (1 + (l : O) • N.Th i).map em := by
      ext1 x y
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      exact hev _ _ (one_add_X_smul_sub_C_dvd (l : O) (N.D i) (N.Th i) (hTh i) x y)
    rw [hA] at hk
    have hunit : ∀ j, (u : ℤ_[l]) ^ (U' i j).toNat *
        (1 + (l : ℤ_[l]) * (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) = 1 := by
      intro j
      rw [← he j, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have : u ^ (U' i j).toNat * u ^ (-(U' i j)) = 1 := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hU i j), ← zpow_add, add_neg_cancel, zpow_zero]
      rw [this, Units.val_one]
    let G0 : (Matrix (Fin n) (Fin n) L)ˣ :=
      Units.map (RingHom.mapMatrix (constantCoeff (R := L))).toMonoidHom G
    have hG0 : (G0 : Matrix (Fin n) (Fin n) L) =
        (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff := rfl
    refine charpoly_diagonal_holds O L em n (N.Th i) (1 + (l : O) • N.Th i) (l : O)
      (fun j => algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) G0 hem hl0
      rfl ?_
    rw [hG0]
    have hdd : Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
        Matrix.diagonal (fun j => em (1 + (l : O) *
          algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) =
        (1 : Matrix (Fin n) (Fin n) L) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      have := congrArg (fun z => em (algebraMap ℤ_[l] O z)) (hunit j)
      simp only [map_mul, map_pow, map_add, map_one, map_natCast] at this
      simp only [map_mul, map_add, map_one, map_natCast]
      exact this
    calc (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff
        = (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            (Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)))) := by
          rw [hdd, Matrix.mul_one]
      _ = (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) := by
          rw [← Matrix.mul_assoc, hk]

/- English proof (translation)
Introduce `ι σ l h t n _ O F L _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN`. Take `⟨hF, ⟨hζ, hζI, hem, hloc⟩, hNN, hNpsi⟩` from `hN`. Conclude with `⟨hF, weight_lattice_of_norm ι l h n O L I ζ em jj W.N u c U' hl2 hF.1.1 hζ hζI hem hloc (fun i a => (hF.2.1 i a).1) hNN, fun s => weight_lattice_of_norm ι l h 1 O L I ζ em jj (W.Npsi s) u c _ hl2 hF.1.1 hζ hζI hem hloc (fun i _ => (hF.2.2.1 i s).1) (hNpsi s)⟩`.
-/
theorem weight_inputs_of_norm : WInputsOfN := by
  intro ι σ l h t n _ O F L _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨hF, ⟨hζ, hζI, hem, hloc⟩, hNN, hNpsi⟩ := hN
  exact ⟨hF, weight_lattice_of_norm ι l h n O L I ζ em jj W.N u c U' hl2 hF.1.1 hζ hζI hem hloc
      (fun i a => (hF.2.1 i a).1) hNN,
    fun s => weight_lattice_of_norm ι l h 1 O L I ζ em jj (W.Npsi s) u c _ hl2 hF.1.1 hζ hζI hem hloc
      (fun i _ => (hF.2.2.1 i s).1) (hNpsi s)⟩

/- English proof (translation)
Introduce `ι _ σ l h t n _ O F L _ _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN`. Establish `hW` using `weight_inputs_of_norm ι σ l h t n O F L I W u c U' wt kap ζ em jj hl2 hN`. Take `⟨h1, h2, h3⟩` from `weight_lemma_full ι σ l h t n O F W u c U' wt kap hl2 hW`. Conclude with `⟨alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW, h1, h2, h3⟩`.
-/
theorem weight_lemma_from_lattice : LemmaWFromLattice := by
  intro ι _ σ l h t n _ O F L _ _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  have hW := weight_inputs_of_norm ι σ l h t n O F L I W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨h1, h2, h3⟩ := weight_lemma_full ι σ l h t n O F W u c U' wt kap hl2 hW
  exact ⟨alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW, h1, h2, h3⟩

/- English proof (translation)
Introduce `ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c U U' bot cst kap τ ζ em jj hl2 hlt hN`. Conclude with `weight_exponents_from_inputs ι σ k j t q l h O F W u c U U' bot cst kap τ hl2 hlt (weight_inputs_of_norm ι σ l h t (k + j + t + q) O F L I W u c U' (fun i s => bot i + ((s : ℕ) : ℤ)) kap ζ em jj hl2 hN)`.
-/
theorem weight_exponents_from_lattice : WEFromLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c U U' bot cst kap τ ζ em jj hl2 hlt hN
  exact weight_exponents_from_inputs ι σ k j t q l h O F W u c U U' bot cst kap τ hl2 hlt
    (weight_inputs_of_norm ι σ l h t (k + j + t + q) O F L I W u c U'
      (fun i s => bot i + ((s : ℕ) : ℤ)) kap ζ em jj hl2 hN)

end Formalism.CohomologicalDescent.FrobeniusPeriodChange
