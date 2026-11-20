import Formalism.PieriBlockIdeals.CapelliCentralEnveloping

noncomputable section

open Finset PowerSeries

namespace Formalism.CohomologicalDescent.HeightDescentMinors

section PartA

section Ode

variable {R : Type*} [CommRing R]

/- English proof (translation)
Break down `n with _ | m` into its components or cases. Simplify using `[add_mul]`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]`. Simplify using the standard rewrite rules. Simplify using `[add_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]`.
-/
theorem coeff_one_add_X_mul_derivative (H : R⟦X⟧) (n : ℕ) :
    coeff n ((1 + X) * d⁄dX R H) = coeff (n + 1) H * ((n : R) + 1) + coeff n H * (n : R) := by
  rcases n with _ | m
  · simp [add_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  · simp [add_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [map_zero]`. Proceed by induction on `n with`. Consider the case `zero => simpa using h0`. Consider the case `succ n ih`.

Establish `e` using `congrArg (coeff n) h`. Rewrite `e` using `[coeff_one_add_X_mul_derivative, PowerSeries.coeff_C_mul]`. Simplify using `only [ih, zero_mul, mul_zero, add_zero] at e`. Establish `e2 : (n + 1) • coeff (n + 1) H = 0`. Rewrite using `[nsmul_eq_mul, mul_comm]`.

Use `push_cast`. Conclude with `e`. Conclude with `nsmul_right_injective (Nat.succ_ne_zero n) (by simpa using e2)`.
-/
theorem eq_zero_of_binomial_ode [IsAddTorsionFree R] (c : R) (H : R⟦X⟧)
    (h : (1 + X) * d⁄dX R H = C c * H) (h0 : constantCoeff H = 0) : H = 0 := by
  ext n
  simp only [map_zero]
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have e := congrArg (coeff n) h
    rw [coeff_one_add_X_mul_derivative, PowerSeries.coeff_C_mul] at e
    simp only [ih, zero_mul, mul_zero, add_zero] at e
    have e2 : (n + 1) • coeff (n + 1) H = 0 := by
      rw [nsmul_eq_mul, mul_comm]
      push_cast
      exact e
    exact nsmul_right_injective (Nat.succ_ne_zero n) (by simpa using e2)

/- English proof (translation)
Use `eq_zero_of_binomial_ode c (F - G) (by rw [map_sub, mul_sub, hF, hG, mul_sub]) (by rw [map_sub, h0, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem eq_of_binomial_ode_of_constantCoeff_eq [IsAddTorsionFree R] (c : R) (F G : R⟦X⟧)
    (hF : (1 + X) * d⁄dX R F = C c * F) (hG : (1 + X) * d⁄dX R G = C c * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  have := eq_zero_of_binomial_ode c (F - G) (by rw [map_sub, mul_sub, hF, hG, mul_sub])
    (by rw [map_sub, h0, sub_self])
  exact sub_eq_zero.mp this

variable [BinomialRing R]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_one_add_X_mul_derivative, coeff_C_mul]`. Simplify using `only [binomialSeries_coeff, smul_eq_mul, mul_one]`. Establish `h` using `Ring.choose_smul_choose c (Nat.le_succ n)`. Rewrite `h` using `[Nat.choose_succ_self_right, Nat.succ_sub (le_refl n), Nat.sub_self, Ring.choose_one_right, nsmul_eq_mul]`.

Move the coercions through the operations in `at h`. Take the linear combination `h`.
-/
theorem binomialSeries_one_add_X_mul_derivative (c : R) :
    (1 + X) * d⁄dX R (binomialSeries R c) = C c * binomialSeries R c := by
  ext n
  rw [coeff_one_add_X_mul_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  have h := Ring.choose_smul_choose c (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, Nat.succ_sub (le_refl n), Nat.sub_self, Ring.choose_one_right,
    nsmul_eq_mul] at h
  push_cast at h
  linear_combination h

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (binomialSeries A e - 1 : A⟦X⟧) = 0`. Simplify using the standard rewrite rules.
-/
theorem hasSubst_binomialSeries_sub_one {A : Type*} [CommRing A] [Algebra R A] (e : R) :
    HasSubst (binomialSeries A e - 1 : A⟦X⟧) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (binomialSeries A e - 1 : A⟦X⟧) = 0
  simp

attribute [local instance] BinomialRing.toIsAddTorsionFree in
/- English proof (translation)
Establish `ha` using `hasSubst_binomialSeries_sub_one (A := R) e`. Use `set a : R⟦X⟧ := binomialSeries R e - 1 with hadef`. Establish `hFe : (1 + X : R⟦X⟧).subst a = binomialSeries R e`. Rewrite using `[subst_add ha, subst_X ha, ← map_one (C (R := R)), subst_C]`. Simplify using `[hadef]`.

Establish `hda : d⁄dX R a = d⁄dX R (binomialSeries R e)`. Rewrite using `[hadef, map_sub, derivative_one, sub_zero]`. Apply `eq_of_binomial_ode_of_constantCoeff_eq (d * e)` to reduce the goal to its premises. Rewrite using `[derivative_subst ha, hda]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[binomialSeries_one_add_X_mul_derivative, hFe]`. Use `_ = C e * ((1 + X) * d⁄dX R (binomialSeries R d)).subst a := by`. Rewrite using `[subst_mul ha]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = C e * (C d * (binomialSeries R d).subst a) := by`.

Rewrite using `[binomialSeries_one_add_X_mul_derivative, subst_mul ha, subst_C]`. Both sides reduce to the same expression. Use `_ = C (d * e) * (binomialSeries R d).subst a := by`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `binomialSeries_one_add_X_mul_derivative _`. Establish `h1 : binomialSeries R d = 1 + (binomialSeries R d - 1)` using `by ring`. Rewrite using `[h1, subst_add ha, ← map_one (C (R := R)), subst_C, map_add]`. Establish `h2 : constantCoeff ((binomialSeries R d - C 1 : R⟦X⟧).subst a) = 0` using `constantCoeff_subst_eq_zero (show constantCoeff a = 0 by rw [hadef]; simp) _ (by simp)`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules.
-/
theorem binomialSeries_subst_comp (d e : R) :
    (binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧) = binomialSeries R (d * e) := by
  have ha := hasSubst_binomialSeries_sub_one (A := R) e
  set a : R⟦X⟧ := binomialSeries R e - 1 with hadef
  have hFe : (1 + X : R⟦X⟧).subst a = binomialSeries R e := by
    rw [subst_add ha, subst_X ha, ← map_one (C (R := R)), subst_C]
    simp [hadef]
  have hda : d⁄dX R a = d⁄dX R (binomialSeries R e) := by
    rw [hadef, map_sub, derivative_one, sub_zero]
  apply eq_of_binomial_ode_of_constantCoeff_eq (d * e)
  · rw [derivative_subst ha, hda]
    calc (1 + X) * ((d⁄dX R (binomialSeries R d)).subst a * d⁄dX R (binomialSeries R e))
        = (d⁄dX R (binomialSeries R d)).subst a * ((1 + X) * d⁄dX R (binomialSeries R e)) := by ring
      _ = (d⁄dX R (binomialSeries R d)).subst a * (C e * (1 + X : R⟦X⟧).subst a) := by
          rw [binomialSeries_one_add_X_mul_derivative, hFe]
      _ = C e * ((1 + X) * d⁄dX R (binomialSeries R d)).subst a := by
          rw [subst_mul ha]; ring
      _ = C e * (C d * (binomialSeries R d).subst a) := by
          rw [binomialSeries_one_add_X_mul_derivative, subst_mul ha, subst_C]; rfl
      _ = C (d * e) * (binomialSeries R d).subst a := by
          rw [map_mul]; ring
  · exact binomialSeries_one_add_X_mul_derivative _
  · have h1 : binomialSeries R d = 1 + (binomialSeries R d - 1) := by ring
    rw [h1, subst_add ha, ← map_one (C (R := R)), subst_C, map_add]
    have h2 : constantCoeff ((binomialSeries R d - C 1 : R⟦X⟧).subst a) = 0 :=
      constantCoeff_subst_eq_zero
        (show constantCoeff a = 0 by rw [hadef]; simp) _ (by simp)
    rw [h2]
    simp

/- English proof (translation)
Use extensionality with `n`. Use `first`. Consider the case `simp [PowerSeries.binomialSeries_coeff, Algebra.smul_def]`. Consider the case `simp [PowerSeries.binomialSeries, Algebra.smul_def]`. Consider the case `simp [PowerSeries.binomialSeries]`.
-/
theorem map_binomialSeries_alt {A : Type*} [CommRing A] [Algebra R A] (c : R) :
    PowerSeries.map (algebraMap R A) (binomialSeries R c) = binomialSeries A c := by
  ext n
  first
    | simp [PowerSeries.binomialSeries_coeff, Algebra.smul_def]
    | simp [PowerSeries.binomialSeries, Algebra.smul_def]
    | simp [PowerSeries.binomialSeries]

/- English proof (translation)
Establish `hs` using `hasSubst_binomialSeries_sub_one (R := R) (A := R) e`. Establish `hm : PowerSeries.map (algebraMap R A) ((binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧)) = (PowerSeries.map (algebraMap R A) (binomialSeries R d)).subst (PowerSeries.map (algebraMap R A) (binomialSeries R e - 1 : R⟦X⟧))` using `by first`. Consider the case `exact PowerSeries.map_subst hs _`. Consider the case `exact PowerSeries.map_subst hs (algebraMap R A) _`. Consider the case `exact PowerSeries.map_subst (h := algebraMap R A) hs _`.

Rewrite `hm` using `[map_sub, map_one, map_binomialSeries_alt, map_binomialSeries_alt, binomialSeries_subst_comp, map_binomialSeries_alt]`. Conclude with `hm.symm`.
-/
theorem binomialSeries_subst_sub_one_eq_mul {A : Type*} [CommRing A] [Algebra R A] (d e : R) :
    (binomialSeries A d).subst (binomialSeries A e - 1 : A⟦X⟧) = binomialSeries A (d * e) := by
  have hs := hasSubst_binomialSeries_sub_one (R := R) (A := R) e
  have hm : PowerSeries.map (algebraMap R A) ((binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧)) =
      (PowerSeries.map (algebraMap R A) (binomialSeries R d)).subst
        (PowerSeries.map (algebraMap R A) (binomialSeries R e - 1 : R⟦X⟧)) := by
    first
      | exact PowerSeries.map_subst hs _
      | exact PowerSeries.map_subst hs (algebraMap R A) _
      | exact PowerSeries.map_subst (h := algebraMap R A) hs _
  rw [map_sub, map_one, map_binomialSeries_alt, map_binomialSeries_alt, binomialSeries_subst_comp, map_binomialSeries_alt] at hm
  exact hm.symm

end Ode

section Act

/- English proof (translation)
The claim follows from `PowerSeries.X_subst f`.
-/
theorem subst_X_eq_self {R : Type*} [CommRing R] (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := PowerSeries.X_subst f

/- English proof (translation)
Establish `e : ((1 + X : R⟦X⟧)) ^ d = (((1 + Polynomial.X) ^ d : Polynomial R) : R⟦X⟧)`. Simplify using `[Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]`. Rewrite using `[e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]`.
-/
theorem coeff_one_add_X_pow_alt (R : Type*) [CommRing R] (d n : ℕ) :
    coeff n ((1 + X : R⟦X⟧) ^ d) = (d.choose n : R) := by
  have e : ((1 + X : R⟦X⟧)) ^ d = (((1 + Polynomial.X) ^ d : Polynomial R) : R⟦X⟧) := by
    simp [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Use `first`. Consider the case `simp [br]`. Consider the case `(simp only [br, map_sub, map_one, sub_eq_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[PowerSeries.binomialSeries])`.
-/
theorem constantCoeff_binomialSeriesSubOne (c : ℤ_[l]) : constantCoeff (br l O c) = 0 := by
  first
    | simp [br]
    | (simp only [br, map_sub, map_one, sub_eq_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
       simp [PowerSeries.binomialSeries])

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (br l O c) = 0`. Conclude with `constantCoeff_binomialSeriesSubOne l O c`.
-/
theorem hasSubst_br_padic (c : ℤ_[l]) : HasSubst (br l O c) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (br l O c) = 0
  exact constantCoeff_binomialSeriesSubOne l O c

/- English proof (translation)
Rewrite using `[br, PowerSeries.binomialSeries_nat]`.
-/
theorem binomialSeriesSubOne_natCast (n : ℕ) : br l O (n : ℤ_[l]) = (1 + X) ^ n - 1 := by
  rw [br, PowerSeries.binomialSeries_nat]

/- English proof (translation)
Use `binomialSeriesSubOne_natCast l O 1` as an intermediate fact. Simplify using `using this`.
-/
theorem binomialSeriesSubOne_one : br l O 1 = X := by
  have := binomialSeriesSubOne_natCast l O 1
  simpa using this

/- English proof (translation)
Establish `hs` using `hasSubst_binomialSeries_sub_one (R := ℤ_[l]) (A := O) c`. Simplify using `only [act, br]`. Rewrite using `[← PowerSeries.coe_substAlgHom hs, map_sub, map_one, PowerSeries.coe_substAlgHom, binomialSeries_subst_sub_one_eq_mul]`.
-/
theorem binomialAction_binomialSeriesSubOne (c d : ℤ_[l]) : act l O c (br l O d) = br l O (d * c) := by
  have hs := hasSubst_binomialSeries_sub_one (R := ℤ_[l]) (A := O) c
  simp only [act, br]
  rw [← PowerSeries.coe_substAlgHom hs, map_sub, map_one, PowerSeries.coe_substAlgHom, binomialSeries_subst_sub_one_eq_mul]

/- English proof (translation)
Establish `e` using `binomialAction_binomialSeriesSubOne l O c d`. Rewrite `e` using `[act]`. Rewrite using `[act, act, act, PowerSeries.subst_comp_subst_apply (hasSubst_br_padic l O d) (hasSubst_br_padic l O c), e]`.
-/
theorem binomialAction_comp_eq_mul (c d : ℤ_[l]) (f : O⟦X⟧) :
    act l O c (act l O d f) = act l O (d * c) f := by
  have e := binomialAction_binomialSeriesSubOne l O c d
  rw [act] at e
  rw [act, act, act, PowerSeries.subst_comp_subst_apply (hasSubst_br_padic l O d) (hasSubst_br_padic l O c), e]

/- English proof (translation)
Rewrite using `[phi, act, binomialSeriesSubOne_natCast]`.
-/
theorem phi_eq_act_l (f : O⟦X⟧) : phi l O f = act l O (l : ℤ_[l]) f := by
  rw [phi, act, binomialSeriesSubOne_natCast]

/- English proof (translation)
Introduce `l _ O _ _`. Use `⟨binomialAction_binomialSeriesSubOne l O, binomialAction_comp_eq_mul l O, ?_, phi_eq_act_l l O, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Rewrite using `[act, binomialSeriesSubOne_one, subst_X_eq_self]`. Introduce `c f`.

Rewrite using `[phi_eq_act_l, phi_eq_act_l, binomialAction_comp_eq_mul, binomialAction_comp_eq_mul, mul_comm]`. Introduce `c f g`. Establish `hs` using `hasSubst_br_padic l O c`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[act, act, act, ← PowerSeries.coe_substAlgHom hs, map_mul]`.

Rewrite using `[act, act, act, ← PowerSeries.coe_substAlgHom hs, map_add]`. Introduce `c a`. Establish `hs` using `hasSubst_br_padic l O c`. Rewrite using `[act, ← PowerSeries.coe_substAlgHom hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[PowerSeries.smul_eq_C_mul, mul_one]`. Use `_ = a • PowerSeries.substAlgHom hs 1 := map_smul _ _ _`. Use `_ = C a := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]`.
-/
theorem action_laws_holds : ActLaws := by
  intro l _ O _ _
  refine ⟨binomialAction_binomialSeriesSubOne l O, binomialAction_comp_eq_mul l O, ?_, phi_eq_act_l l O, ?_, ?_, ?_⟩
  · intro f
    rw [act, binomialSeriesSubOne_one, subst_X_eq_self]
  · intro c f
    rw [phi_eq_act_l, phi_eq_act_l, binomialAction_comp_eq_mul, binomialAction_comp_eq_mul, mul_comm]
  · intro c f g
    have hs := hasSubst_br_padic l O c
    refine ⟨?_, ?_⟩
    · rw [act, act, act, ← PowerSeries.coe_substAlgHom hs, map_mul]
    · rw [act, act, act, ← PowerSeries.coe_substAlgHom hs, map_add]
  · intro c a
    have hs := hasSubst_br_padic l O c
    rw [act, ← PowerSeries.coe_substAlgHom hs]
    calc PowerSeries.substAlgHom hs (C a) = PowerSeries.substAlgHom hs (a • 1) := by
          rw [PowerSeries.smul_eq_C_mul, mul_one]
      _ = a • PowerSeries.substAlgHom hs 1 := map_smul _ _ _
      _ = C a := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | m` into its components or cases. Simplify using `[coeff_one_add_X_pow_alt]`. Simplify using `[q, coeff_one_add_X_pow_alt, PowerSeries.coeff_succ_X_mul]`.
-/
theorem X_mul_q_eq_one_add_X_pow_sub_one : X * q l O = (1 + X) ^ l - 1 := by
  ext n
  rcases n with _ | m
  · simp [coeff_one_add_X_pow_alt]
  · simp [q, coeff_one_add_X_pow_alt, PowerSeries.coeff_succ_X_mul]

/- English proof (translation)
Introduce `l _ O _ _`. Establish `hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧)`. Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff ((1 + X) ^ l - 1 : O⟦X⟧) = 0`. Simplify using the standard rewrite rules.

Conclude with `⟨X_mul_q_eq_one_add_X_pow_sub_one l O, by rw [phi, PowerSeries.subst_X hs, X_mul_q_eq_one_add_X_pow_sub_one]⟩`.
-/
theorem q_multiplicative_holds : QMul := by
  intro l _ O _ _
  have hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    change PowerSeries.constantCoeff ((1 + X) ^ l - 1 : O⟦X⟧) = 0
    simp
  exact ⟨X_mul_q_eq_one_add_X_pow_sub_one l O, by rw [phi, PowerSeries.subst_X hs, X_mul_q_eq_one_add_X_pow_sub_one]⟩

/- English proof (translation)
Simplify using `only [br, map_sub, map_one, map_binomialSeries_alt]`.
-/
theorem map_algebraMap_binomialSeriesSubOne (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := by
  simp only [br, map_sub, map_one, map_binomialSeries_alt]

/- English proof (translation)
Simplify using `only [pi0, map_prod, map_algebraMap_binomialSeriesSubOne]`.
-/
theorem map_pi0_padic : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := by
  simp only [pi0, map_prod, map_algebraMap_binomialSeriesSubOne]

/- English proof (translation)
Simplify using `[q0, map_pi0_padic]`.
-/
theorem map_q0_padicInt : PowerSeries.map (algebraMap ℤ_[l] O) (q0 l ℤ_[l]) = q0 l O := by
  simp [q0, map_pi0_padic]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[q]`.
-/
theorem map_q_padicInt : PowerSeries.map (algebraMap ℤ_[l] O) (q l ℤ_[l]) = q l O := by
  ext j
  simp [q]

end Act

section Mu

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use `(Fact.out : l.Prime).two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem prime_sub_one_pos : 0 < l - 1 := by
  have := (Fact.out : l.Prime).two_le
  omega

/- English proof (translation)
Rewrite using `[mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l)]`.
-/
theorem mem_mu_iff_pow_eq_one {d : ℤ_[l]} : d ∈ mu l ↔ d ^ (l - 1) = 1 := by
  rw [mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l)]

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`.
-/
theorem toZMod_eq_zero_iff_norm_lt_one (y : ℤ_[l]) : PadicInt.toZMod y = 0 ↔ ‖y‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/- English proof (translation)
Take `⟨a, ha⟩` from `ZMod.ringHom_surjective (PadicInt.toZMod (p := l)) x`. Use `set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hFdef`. Establish `hF : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1`. Introduce `z`. Simplify using `[hFdef]`.

Establish `hF' : ∀ z : ℤ_[l], Polynomial.aeval z (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * z ^ (l - 1 - 1)`. Introduce `z`. Simplify using `[hFdef, Polynomial.derivative_X_pow]`. Establish `h1 : ‖Polynomial.aeval a F‖ < 1`. Rewrite using `[← toZMod_eq_zero_iff_norm_lt_one, hF, map_sub, map_pow, ha, ZMod.pow_card_sub_one_eq_one hx, map_one, sub_self]`.

Establish `h2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1`. Rewrite using `[← PadicInt.isUnit_iff]`. Assume the negation of the conclusion as `hnu`. Establish `h3` using `PadicInt.not_isUnit_iff.mp hnu`. Rewrite `h3` using `[← toZMod_eq_zero_iff_norm_lt_one, hF', map_mul, map_natCast, map_pow, ha]`.

Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Establish `h4` using `Nat.le_of_dvd (prime_sub_one_pos l) ((ZMod.natCast_eq_zero_iff _ _).mp h)`. Establish `h5` using `prime_sub_one_pos l`. Use linear arithmetic over natural numbers and integers. Conclude with `hx (eq_zero_of_pow_eq_zero h)`.

Take `⟨z, hz0, hza, -, huniq⟩` from `hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)`. Rewrite `hza`, `huniq` using `[h2]`. Use `⟨z, ⟨(mem_mu_iff_pow_eq_one l).mpr (sub_eq_zero.mp ((hF z).symm.trans hz0)), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h6` using `(toZMod_eq_zero_iff_norm_lt_one l (z - a)).mpr hza`. Rewrite `h6` using `[map_sub, ha, sub_eq_zero]`.

Conclude with `h6`. Introduce and unpack `d ⟨hd, hdx⟩`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[hF, (mem_mu_iff_pow_eq_one l).mp hd, sub_self]`. Rewrite using `[← toZMod_eq_zero_iff_norm_lt_one, map_sub, hdx, ha, sub_self]`.
-/
theorem existsUnique_teichmuller_lift (x : ZMod l) (hx : x ≠ 0) : ∃! d, d ∈ mu l ∧ PadicInt.toZMod d = x := by
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := l)) x
  set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hFdef
  have hF : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1 := by
    intro z; simp [hFdef]
  have hF' : ∀ z : ℤ_[l], Polynomial.aeval z (Polynomial.derivative F) =
      ((l - 1 : ℕ) : ℤ_[l]) * z ^ (l - 1 - 1) := by
    intro z; simp [hFdef, Polynomial.derivative_X_pow]
  have h1 : ‖Polynomial.aeval a F‖ < 1 := by
    rw [← toZMod_eq_zero_iff_norm_lt_one, hF, map_sub, map_pow, ha, ZMod.pow_card_sub_one_eq_one hx,
      map_one, sub_self]
  have h2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [← PadicInt.isUnit_iff]
    by_contra hnu
    have h3 := PadicInt.not_isUnit_iff.mp hnu
    rw [← toZMod_eq_zero_iff_norm_lt_one, hF', map_mul, map_natCast, map_pow, ha] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · have h4 := Nat.le_of_dvd (prime_sub_one_pos l) ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have h5 := prime_sub_one_pos l
      omega
    · exact hx (eq_zero_of_pow_eq_zero h)
  obtain ⟨z, hz0, hza, -, huniq⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
  rw [h2] at hza huniq
  refine ⟨z, ⟨(mem_mu_iff_pow_eq_one l).mpr (sub_eq_zero.mp ((hF z).symm.trans hz0)), ?_⟩, ?_⟩
  · have h6 := (toZMod_eq_zero_iff_norm_lt_one l (z - a)).mpr hza
    rw [map_sub, ha, sub_eq_zero] at h6
    exact h6
  · rintro d ⟨hd, hdx⟩
    apply huniq
    · rw [hF, (mem_mu_iff_pow_eq_one l).mp hd, sub_self]
    · rw [← toZMod_eq_zero_iff_norm_lt_one, map_sub, hdx, ha, sub_self]

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[toZMod_eq_zero_iff_norm_lt_one]`. Establish `hlt : ‖d‖ ^ (l - 1) < 1` using `pow_lt_one₀ (norm_nonneg _) h (prime_sub_one_pos l).ne'`. Rewrite `hlt` using `[← norm_pow, (mem_mu_iff_pow_eq_one l).mp hd, norm_one]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem toZMod_ne_zero_of_mem_mu {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := by
  intro h
  rw [toZMod_eq_zero_iff_norm_lt_one] at h
  have hlt : ‖d‖ ^ (l - 1) < 1 := pow_lt_one₀ (norm_nonneg _) h (prime_sub_one_pos l).ne'
  rw [← norm_pow, (mem_mu_iff_pow_eq_one l).mp hd, norm_one] at hlt
  exact lt_irrefl _ hlt

/- English proof (translation)
Introduce `d hd` and use `Finset.mem_erase.mpr ⟨toZMod_ne_zero_of_mem_mu l hd, Finset.mem_univ _⟩`.
-/
theorem toZMod_mem_units_of_mem_mu : ∀ d ∈ mu l, PadicInt.toZMod d ∈ (univ.erase (0 : ZMod l)) := fun d hd => Finset.mem_erase.mpr ⟨toZMod_ne_zero_of_mem_mu l hd, Finset.mem_univ _⟩

/- English proof (translation)
Introduce `x hx y hy hxy`. Conclude with `(existsUnique_teichmuller_lift l _ (toZMod_ne_zero_of_mem_mu l hx)).unique ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩`.
-/
theorem toZMod_injOn_mu : Set.InjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l]) := by
  intro x hx y hy hxy
  exact (existsUnique_teichmuller_lift l _ (toZMod_ne_zero_of_mem_mu l hx)).unique ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩

/- English proof (translation)
Introduce `x hx`. Establish `hx0 : x ≠ 0` using `(Finset.mem_erase.mp hx).1`. Take `⟨d, ⟨hd, hdx⟩, _⟩` from `existsUnique_teichmuller_lift l x hx0`. Conclude with `⟨d, hd, hdx⟩`.
-/
theorem toZMod_surjOn_mu_nonzero : Set.SurjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l])
    ((univ.erase (0 : ZMod l) : Finset (ZMod l)) : Set (ZMod l)) := by
  intro x hx
  have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
  obtain ⟨d, ⟨hd, hdx⟩, _⟩ := existsUnique_teichmuller_lift l x hx0
  exact ⟨d, hd, hdx⟩

/- English proof (translation)
Rewrite using `[Finset.card_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]`.
-/
theorem card_mu_eq_sub_one : (mu l).card = l - 1 := by
  rw [Finset.card_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/- English proof (translation)
Rewrite using `[← ZMod.prod_Ico_one_prime l]`. Use `symm`. Use `Finset.prod_nbij (fun n : ℕ => (n : ZMod l)) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Ico]`.

Use `Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩` and prove the remaining obligations. Introduce `h`. Use `congrArg ZMod.val h` as an intermediate fact. Rewrite `this` using `[ZMod.val_natCast, Nat.mod_eq_of_lt hn.2, ZMod.val_zero]`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_Ico, Set.mem_Ico] at ha hb`. Use `congrArg ZMod.val hab` as an intermediate fact. Simplify using `only [ZMod.val_natCast, Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2] at this`. Conclude with `this`.

Introduce `x hx`. Establish `hx0 : x ≠ 0` using `(Finset.mem_erase.mp hx).1`. Use `⟨x.val, ?_, ZMod.natCast_zmod_val x⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_Ico, Set.mem_Ico]`. Use `⟨?_, ZMod.val_lt x⟩` and prove the remaining obligations.

Rewrite using `[Nat.one_le_iff_ne_zero]`. Introduce `h0`. Conclude with `hx0 ((ZMod.val_eq_zero x).mp h0)`.
-/
theorem wilson_zmod_prod_units : ∏ x ∈ (univ.erase (0 : ZMod l)), x = -1 := by
  rw [← ZMod.prod_Ico_one_prime l]
  symm
  refine Finset.prod_nbij (fun n : ℕ => (n : ZMod l)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro n hn
    rw [Finset.mem_Ico] at hn
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn.2, ZMod.val_zero] at this
    omega
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have := congrArg ZMod.val hab
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2] at this
    exact this
  · intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    simp only [Finset.coe_Ico, Set.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hx0 ((ZMod.val_eq_zero x).mp h0)

/- English proof (translation)
Establish `hp : ∏ d ∈ mu l, d ∈ mu l` using `(mem_mu_iff_pow_eq_one l).mpr (by`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_eq_one fun d hd => (mem_mu_iff_pow_eq_one l).mp hd)`. Establish `hm1 : (-1 : ℤ_[l]) ∈ mu l` using `(mem_mu_iff_pow_eq_one l).mpr ((Fact.out : l.Prime).even_sub_one hl).neg_one_pow`. Apply `toZMod_injOn_mu l hp hm1` to reduce the goal to its premises.

Rewrite using `[map_prod, map_neg, map_one, ← wilson_zmod_prod_units l]`. Conclude with `Finset.prod_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l) (fun _ _ => rfl)`.
-/
theorem prod_roots_unity_eq_neg_one (hl : l ≠ 2) : ∏ d ∈ mu l, d = -1 := by
  have hp : ∏ d ∈ mu l, d ∈ mu l := (mem_mu_iff_pow_eq_one l).mpr (by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun d hd => (mem_mu_iff_pow_eq_one l).mp hd)
  have hm1 : (-1 : ℤ_[l]) ∈ mu l :=
    (mem_mu_iff_pow_eq_one l).mpr ((Fact.out : l.Prime).even_sub_one hl).neg_one_pow
  apply toZMod_injOn_mu l hp hm1
  rw [map_prod, map_neg, map_one, ← wilson_zmod_prod_units l]
  exact Finset.prod_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l) (fun _ _ => rfl)

/- English proof (translation)
Introduce `l _`. Conclude with `⟨card_mu_eq_sub_one l, existsUnique_teichmuller_lift l, prod_roots_unity_eq_neg_one l⟩`.
-/
theorem mu_facts_hold : MuFacts := by
  intro l _
  exact ⟨card_mu_eq_sub_one l, existsUnique_teichmuller_lift l, prod_roots_unity_eq_neg_one l⟩

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | n` into its components or cases. Simplify using `using constantCoeff_binomialSeriesSubOne l O d`. Simplify using `[PowerSeries.coeff_succ_X_mul]`.
-/
theorem br_eq_X_mul_shift (d : ℤ_[l]) :
    br l O d = X * PowerSeries.mk (fun n => coeff (n + 1) (br l O d)) := by
  ext n
  rcases n with _ | n
  · simpa using constantCoeff_binomialSeriesSubOne l O d
  · simp [PowerSeries.coeff_succ_X_mul]

/- English proof (translation)
Use `first`. Consider the case `simp [br, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, Algebra.smul_def]`. Consider the case `simp [br, PowerSeries.binomialSeries, Ring.choose_one_right, Algebra.smul_def]`. Consider the case `simp [br, PowerSeries.binomialSeries, Ring.choose_one_right]`.
-/
theorem coeff_one_br (d : ℤ_[l]) : coeff 1 (br l O d) = algebraMap ℤ_[l] O d := by
  first
    | simp [br, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, Algebra.smul_def]
    | simp [br, PowerSeries.binomialSeries, Ring.choose_one_right, Algebra.smul_def]
    | simp [br, PowerSeries.binomialSeries, Ring.choose_one_right]

/- English proof (translation)
Introduce `l _ O _ _ hl`. Use `set w : O⟦X⟧ := ∏ d ∈ mu l, PowerSeries.mk (fun n => coeff (n + 1) (br l O d)) with hw`. Establish `hcc : constantCoeff w = -1`. Rewrite using `[hw, map_prod]`. Establish `: ∀ d ∈ mu l, constantCoeff (PowerSeries.mk (fun n => coeff (n + 1) (br l O d))) = algebraMap ℤ_[l] O d`.

Introduce `d _`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, coeff_one_br]`. Rewrite using `[Finset.prod_congr rfl this, ← map_prod, prod_roots_unity_eq_neg_one l hl, map_neg, map_one]`. Establish `hu : IsUnit w`. Rewrite using `[isUnit_iff_constantCoeff, hcc]`.

Conclude with `isUnit_one.neg`. Take `⟨w', hw'⟩` from `hu`. Use `⟨w', ?_, by rw [hw', hcc]⟩` and prove the remaining obligations. Rewrite using `[hw', pi0, Finset.prod_congr rfl (fun d _ => br_eq_X_mul_shift l O d), Finset.prod_mul_distrib, Finset.prod_const, card_mu_eq_sub_one, mul_comm]`.
-/
theorem r1_holds : R1 := by
  intro l _ O _ _ hl
  set w : O⟦X⟧ := ∏ d ∈ mu l, PowerSeries.mk (fun n => coeff (n + 1) (br l O d)) with hw
  have hcc : constantCoeff w = -1 := by
    rw [hw, map_prod]
    have : ∀ d ∈ mu l, constantCoeff (PowerSeries.mk (fun n => coeff (n + 1) (br l O d))) =
        algebraMap ℤ_[l] O d := by
      intro d _
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, coeff_one_br]
    rw [Finset.prod_congr rfl this, ← map_prod, prod_roots_unity_eq_neg_one l hl, map_neg, map_one]
  have hu : IsUnit w := by
    rw [isUnit_iff_constantCoeff, hcc]
    exact isUnit_one.neg
  obtain ⟨w', hw'⟩ := hu
  refine ⟨w', ?_, by rw [hw', hcc]⟩
  rw [hw', pi0, Finset.prod_congr rfl (fun d _ => br_eq_X_mul_shift l O d), Finset.prod_mul_distrib,
    Finset.prod_const, card_mu_eq_sub_one, mul_comm]

/- English proof (translation)
Establish `ha` using `hasSubst_br_padic l O c`. Simplify using `only [act, ← coe_substAlgHom ha, map_prod]`.
-/
theorem act_finset_prod {ι : Type*} (c : ℤ_[l]) (s : Finset ι) (f : ι → O⟦X⟧) :
    act l O c (∏ i ∈ s, f i) = ∏ i ∈ s, act l O c (f i) := by
  have ha := hasSubst_br_padic l O c
  simp only [act, ← coe_substAlgHom ha, map_prod]

/- English proof (translation)
Introduce `l _ O _ _ d hd`. Establish `hd1` using `(mem_mu_iff_pow_eq_one l).mp hd`. Establish `hd0 : d ≠ 0`. Introduce `h`. Rewrite `hd1` using `[h, zero_pow (prime_sub_one_pos l).ne']`.

Conclude with `zero_ne_one hd1`. Rewrite using `[pi0, act_finset_prod, Finset.prod_congr rfl (fun e _ => binomialAction_binomialSeriesSubOne l O d e)]`. Apply `Finset.prod_nbij (fun e => e * d)` to reduce the goal to its premises. Introduce `e he`. Rewrite using `[mem_mu_iff_pow_eq_one, mul_pow, (mem_mu_iff_pow_eq_one l).mp he, hd1, one_mul]`.

Introduce `e _ e' _ h`. Conclude with `mul_right_cancel₀ hd0 h`. Introduce `e he`. Use `⟨e * d ^ (l - 1 - 1), ?_, ?_⟩` and prove the remaining obligations. Establish `he1` using `(mem_mu_iff_pow_eq_one l).mp he show e * d ^ (l - 1 - 1) ∈ mu l`.

Rewrite using `[mem_mu_iff_pow_eq_one, mul_pow, he1, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hd1, one_pow]`. Use `show e * d ^ (l - 1 - 1) * d = e`. Rewrite using `[mul_assoc, ← pow_succ, Nat.sub_add_cancel (prime_sub_one_pos l), hd1, mul_one]`. Introduce `e _`. Both sides reduce to the same expression.
-/
theorem r2_inverse_holds : DivisibilityInvariant := by
  intro l _ O _ _ d hd
  have hd1 := (mem_mu_iff_pow_eq_one l).mp hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_pow (prime_sub_one_pos l).ne'] at hd1
    exact zero_ne_one hd1
  rw [pi0, act_finset_prod, Finset.prod_congr rfl (fun e _ => binomialAction_binomialSeriesSubOne l O d e)]
  apply Finset.prod_nbij (fun e => e * d)
  · intro e he
    rw [mem_mu_iff_pow_eq_one, mul_pow, (mem_mu_iff_pow_eq_one l).mp he, hd1, one_mul]
  · intro e _ e' _ h
    exact mul_right_cancel₀ hd0 h
  · intro e he
    refine ⟨e * d ^ (l - 1 - 1), ?_, ?_⟩
    · have he1 := (mem_mu_iff_pow_eq_one l).mp he
      show e * d ^ (l - 1 - 1) ∈ mu l
      rw [mem_mu_iff_pow_eq_one, mul_pow, he1, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hd1, one_pow]
    · show e * d ^ (l - 1 - 1) * d = e
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (prime_sub_one_pos l), hd1, mul_one]
  · intro e _; rfl

end Mu

/- English proof (translation)
Introduce `l _ O _ _ _ ζ hζ`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `hlpos : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `h1 : (Polynomial.X ^ l - 1 : Polynomial O) = ∏ b ∈ Finset.range l, (Polynomial.X - Polynomial.C (ζ ^ b))`. Rewrite using `[Polynomial.X_pow_sub_one_eq_prod hlpos hζ]`.

Use `symm`. Apply `Finset.prod_nbij (fun b => ζ ^ b)` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Polynomial.mem_nthRootsFinset hlpos, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Introduce `b hb b' hb' h`.

Conclude with `hζ.pow_inj (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h`. Introduce `ξ hξ`. Take `⟨i, hi, hiξ⟩` from `hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hlpos _).mp hξ)`. Conclude with `⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr hi), hiξ⟩`. Introduce `b _`.

Both sides reduce to the same expression. Establish `h2` using `congrArg (Polynomial.eval₂RingHom (C : O →+* O⟦X⟧) (1 + X)) h1`. Simplify using `only [map_sub, map_pow, map_one, map_prod, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C] at h2`. Establish `h3 : (Finset.range l).erase 0 = Finset.Ioo 0 l`. Use extensionality with `b`.

Simplify using `only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]`. Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[← Finset.mul_prod_erase (Finset.range l) _ (Finset.mem_range.mpr hlpos), h3, ← X_mul_q_eq_one_add_X_pow_sub_one l O]`. Establish `h4 : (1 + X - (C ζ) ^ 0 : O⟦X⟧) = X` using `by simp`. Rewrite `h2` using `[h4]`.

Establish `h5` using `mul_left_cancel₀ (X_ne_zero (R := O)) h2`. Rewrite using `[h5]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_pow, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_roots_holds : QRoots := by
  intro l _ O _ _ _ ζ hζ
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have h1 : (Polynomial.X ^ l - 1 : Polynomial O) =
      ∏ b ∈ Finset.range l, (Polynomial.X - Polynomial.C (ζ ^ b)) := by
    rw [Polynomial.X_pow_sub_one_eq_prod hlpos hζ]
    symm
    apply Finset.prod_nbij (fun b => ζ ^ b)
    · intro b _
      rw [Polynomial.mem_nthRootsFinset hlpos, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro b hb b' hb' h
      exact hζ.pow_inj (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h
    · intro ξ hξ
      obtain ⟨i, hi, hiξ⟩ := hζ.eq_pow_of_pow_eq_one
        ((Polynomial.mem_nthRootsFinset hlpos _).mp hξ)
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr hi), hiξ⟩
    · intro b _; rfl
  have h2 := congrArg (Polynomial.eval₂RingHom (C : O →+* O⟦X⟧) (1 + X)) h1
  simp only [map_sub, map_pow, map_one, map_prod, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
  have h3 : (Finset.range l).erase 0 = Finset.Ioo 0 l := by
    ext b; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]; omega
  rw [← Finset.mul_prod_erase (Finset.range l) _ (Finset.mem_range.mpr hlpos), h3,
    ← X_mul_q_eq_one_add_X_pow_sub_one l O] at h2
  have h4 : (1 + X - (C ζ) ^ 0 : O⟦X⟧) = X := by simp
  rw [h4] at h2
  have h5 := mul_left_cancel₀ (X_ne_zero (R := O)) h2
  rw [h5]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_sub, map_pow, map_one]
  ring

end PartA

section PartA2

section A2General

/- English proof (translation)
Use `first`. Consider the case `exact PowerSeries.map_subst ha f`. Consider the case `exact PowerSeries.map_subst ha h f`. Consider the case `exact PowerSeries.map_subst (R := R) (S := S) ha (h := h) f`. Consider the case `exact (PowerSeries.map_subst ha).symm`.
-/
lemma map_subst_powerSeries {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {a : R⟦X⟧}
    (ha : HasSubst a) (f : R⟦X⟧) :
    PowerSeries.map h (f.subst a) = (PowerSeries.map h f).subst (PowerSeries.map h a) := by
  first
    | exact PowerSeries.map_subst ha f
    | exact PowerSeries.map_subst ha h f
    | exact PowerSeries.map_subst (R := R) (S := S) ha (h := h) f
    | exact (PowerSeries.map_subst ha).symm

/- English proof (translation)
Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.mpr hf`. Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]`. Conclude with `dvd_mul_right _ _`.
-/
lemma dvd_subst_self {R : Type} [CommRing R] {a f : R⟦X⟧} (ha : HasSubst a)
    (hf : constantCoeff f = 0) : a ∣ f.subst a := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
  exact dvd_mul_right _ _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Establish `h1` using `h a (Finset.mem_insert_self a s)`.

Establish `h2` using `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Establish `e : F a * ∏ i ∈ s, F i - G a * ∏ i ∈ s, G i = (F a - G a) * ∏ i ∈ s, F i + G a * (∏ i ∈ s, F i - ∏ i ∈ s, G i)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)`.
-/
lemma dvd_prod_sub_prod_of_dvd_sub {R ι : Type} [CommRing R] (x : R) (s : Finset ι) (F G : ι → R)
    (h : ∀ i ∈ s, x ∣ F i - G i) : x ∣ ∏ i ∈ s, F i - ∏ i ∈ s, G i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : F a * ∏ i ∈ s, F i - G a * ∏ i ∈ s, G i =
        (F a - G a) * ∏ i ∈ s, F i + G a * (∏ i ∈ s, F i - ∏ i ∈ s, G i) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Finset.range_eq_Ico, Finset.prod_Ico_add' F 0 (l - 1) 1, zero_add, Nat.sub_add_cancel hl]`. Both sides reduce to the same expression.
-/
lemma prod_Ioo_eq_prod_range {M : Type} [CommMonoid M] (l : ℕ) (F : ℕ → M) :
    ∏ c ∈ Finset.Ioo 0 l, F c = ∏ k ∈ Finset.range (l - 1), F (k + 1) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' F 0 (l - 1) 1, zero_add, Nat.sub_add_cancel hl]
  rfl

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff ((1 + X) ^ l - 1 : R⟦X⟧) = 0`. Simplify using the standard rewrite rules.
-/
lemma hasSubst_one_add_X_pow_sub_one_alt {R : Type} [CommRing R] (l : ℕ) :
    HasSubst ((1 + X) ^ l - 1 : R⟦X⟧) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff ((1 + X) ^ l - 1 : R⟦X⟧) = 0
  simp

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (X ^ l : R⟦X⟧) = 0`. Simplify using `[zero_pow hl]`.
-/
lemma hasSubst_X_pow_of_ne_zero {R : Type} [CommRing R] {l : ℕ} (hl : l ≠ 0) :
    HasSubst (X ^ l : R⟦X⟧) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (X ^ l : R⟦X⟧) = 0
  simp [zero_pow hl]

end A2General

section A2

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
The claim follows from `map_algebraMap_binomialSeriesSubOne l O c`.
-/
lemma map_binomialSeriesSubOne_algebraMap (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := map_algebraMap_binomialSeriesSubOne l O c

/- English proof (translation)
The claim follows from `map_pi0_padic l O`.
-/
lemma map_pi0_algebraMap_padicInt : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := map_pi0_padic l O

/- English proof (translation)
The claim follows from `map_q_padicInt l O`.
-/
lemma map_q_padic : PowerSeries.map (algebraMap ℤ_[l] O) (q l ℤ_[l]) = q l O := map_q_padicInt l O

/- English proof (translation)
The claim follows from `map_q0_padicInt l O`.
-/
lemma map_q0_padic : PowerSeries.map (algebraMap ℤ_[l] O) (q0 l ℤ_[l]) = q0 l O := map_q0_padicInt l O

/- English proof (translation)
The claim follows from `constantCoeff_binomialSeriesSubOne l O c`.
-/
lemma constantCoeff_binomialSeriesSubOne_eq_zero (c : ℤ_[l]) : constantCoeff (br l O c) = 0 := constantCoeff_binomialSeriesSubOne l O c

/- English proof (translation)
Rewrite using `[mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l), one_pow]`.
-/
lemma one_mem_mu : (1 : ℤ_[l]) ∈ mu l := by
  rw [mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l), one_pow]

/- English proof (translation)
Rewrite using `[pi0, map_prod]`. Conclude with `Finset.prod_eq_zero (one_mem_mu l) (constantCoeff_binomialSeriesSubOne l O 1)`.
-/
lemma constantCoeff_pi0_eq_zero : constantCoeff (pi0 l O) = 0 := by
  rw [pi0, map_prod]
  exact Finset.prod_eq_zero (one_mem_mu l) (constantCoeff_binomialSeriesSubOne l O 1)

/- English proof (translation)
Rewrite using `[phi, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l)]`. Simplify using the standard rewrite rules.
-/
lemma map_phi_padic (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (phi l ℤ_[l] f) =
      phi l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [phi, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l)]
  simp

/- English proof (translation)
Establish `hl : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `: ExpChar (ZMod l) l` using `ExpChar.prime Fact.out`. Establish `h` using `MvPowerSeries.map_frobenius_expand (σ := Unit) l hl (f := F)`. Rewrite `h` using `[ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply]`. Rewrite using `[← expand_apply l hl]`.

Conclude with `h.symm`.
-/
lemma pow_prime_eq_subst_X_pow (F : (ZMod l)⟦X⟧) : F ^ l = F.subst (X ^ l : (ZMod l)⟦X⟧) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : ExpChar (ZMod l) l := ExpChar.prime Fact.out
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) l hl (f := F)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply] at h
  rw [← expand_apply l hl]
  exact h.symm

/- English proof (translation)
Establish `h0 : ∀ n, ∃ r, coeff n g = (l : ℤ_[l]) * r`. Introduce `n`. Establish `h1 : PadicInt.toZMod (coeff n g) = 0`. Use `congrArg (coeff n) h` as an intermediate fact. Simplify using `using this`.

Establish `h2 : coeff n g ∈ RingHom.ker (PadicInt.toZMod (p` using `l)) := h1`. Rewrite `h2` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Conclude with `h2`. Use `choose r hr using h0`. Conclude with `⟨PowerSeries.mk r, by ext n; rw [coeff_C_mul, coeff_mk, hr n]⟩`.
-/
lemma exists_eq_C_prime_mul_of_map_toZMod_zero (g : ℤ_[l]⟦X⟧)
    (h : PowerSeries.map (PadicInt.toZMod (p := l)) g = 0) : ∃ r, g = C (l : ℤ_[l]) * r := by
  have h0 : ∀ n, ∃ r, coeff n g = (l : ℤ_[l]) * r := by
    intro n
    have h1 : PadicInt.toZMod (coeff n g) = 0 := by
      have := congrArg (coeff n) h
      simpa using this
    have h2 : coeff n g ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2
    exact h2
  choose r hr using h0
  exact ⟨PowerSeries.mk r, by ext n; rw [coeff_C_mul, coeff_mk, hr n]⟩

end A2

/- English proof (translation)
Introduce `l _ f`. Establish `hl : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `hX : HasSubst (X ^ l : (ZMod l)⟦X⟧)` using `hasSubst_X_pow_of_ne_zero hl`. Establish `h1 : PowerSeries.map (PadicInt.toZMod (p` using `l)) ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) = X ^ l := by`. Simplify using `only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]`.

Rewrite using `[pow_prime_eq_subst_X_pow, ← PowerSeries.coe_substAlgHom hX, map_add, map_one, PowerSeries.substAlgHom_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : PowerSeries.map (PadicInt.toZMod (p` using `l)) (phi l ℤ_[l] f - f ^ l) = 0 := by`. Rewrite using `[map_sub, map_pow, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l), pow_prime_eq_subst_X_pow, h1, sub_self]`. Take `⟨r, hr⟩` from `exists_eq_C_prime_mul_of_map_toZMod_zero l _ key`.

Conclude with `⟨r, by rw [← hr]; ring⟩`.
-/
theorem r5_frobenius_holds : FrobeniusCongruence := by
  intro l _ f
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hX : HasSubst (X ^ l : (ZMod l)⟦X⟧) := hasSubst_X_pow_of_ne_zero hl
  have h1 : PowerSeries.map (PadicInt.toZMod (p := l)) ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) = X ^ l := by
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [pow_prime_eq_subst_X_pow, ← PowerSeries.coe_substAlgHom hX, map_add, map_one,
      PowerSeries.substAlgHom_X]
    ring
  have key : PowerSeries.map (PadicInt.toZMod (p := l)) (phi l ℤ_[l] f - f ^ l) = 0 := by
    rw [map_sub, map_pow, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l), pow_prime_eq_subst_X_pow, h1,
      sub_self]
  obtain ⟨r, hr⟩ := exists_eq_C_prime_mul_of_map_toZMod_zero l _ key
  exact ⟨r, by rw [← hr]; ring⟩

/- English proof (translation)
Introduce `l _ O _ _`. Take `⟨r, hr⟩` from `r5_frobenius_holds l (pi0 l ℤ_[l])`. Use `⟨PowerSeries.map (algebraMap ℤ_[l] O) r, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hr`. Rewrite `h` using `[map_phi_padic, map_pi0_algebraMap_padicInt]`.

Simplify `h` using `[map_pi0_algebraMap_padicInt]`.
-/
theorem pi0_relation_holds : FrobeniusPiZero := by
  intro l _ O _ _
  obtain ⟨r, hr⟩ := r5_frobenius_holds l (pi0 l ℤ_[l])
  refine ⟨PowerSeries.map (algebraMap ℤ_[l] O) r, ?_⟩
  have h := congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hr
  rw [map_phi_padic, map_pi0_algebraMap_padicInt] at h
  simpa [map_pi0_algebraMap_padicInt] using h

/- English proof (translation)
Introduce `l _ O _ _ _ g`. Take `⟨r, hr⟩` from `pi0_relation_holds l O`. Establish `hl : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `h0 : (l : O) = 0` using `CharP.cast_eq_zero O l`. Establish `hp : HasSubst (pi0 l O)` using `HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)`.

Establish `ha : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧)` using `hasSubst_one_add_X_pow_sub_one_alt l`. Establish `hX : HasSubst (X ^ l : O⟦X⟧)` using `hasSubst_X_pow_of_ne_zero hl`. Establish `h1 : (pi0 l O).subst ((1 + X) ^ l - 1 : O⟦X⟧) = pi0 l O ^ l`. Establish `h2` using `hr`. Unfold `phi at h2`.

Rewrite using `[h2, h0]`. Simplify using the standard rewrite rules. Unfold `inc phi`. Rewrite using `[subst_comp_subst_apply hp ha, subst_comp_subst_apply hX hp, subst_pow hp, subst_X hp, h1]`.
-/
theorem r5_character_holds : FrobeniusCharP := by
  intro l _ O _ _ _ g
  obtain ⟨r, hr⟩ := pi0_relation_holds l O
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h0 : (l : O) = 0 := CharP.cast_eq_zero O l
  have hp : HasSubst (pi0 l O) := HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)
  have ha : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := hasSubst_one_add_X_pow_sub_one_alt l
  have hX : HasSubst (X ^ l : O⟦X⟧) := hasSubst_X_pow_of_ne_zero hl
  have h1 : (pi0 l O).subst ((1 + X) ^ l - 1 : O⟦X⟧) = pi0 l O ^ l := by
    have h2 := hr
    unfold phi at h2
    rw [h2, h0]
    simp
  unfold inc phi
  rw [subst_comp_subst_apply hp ha, subst_comp_subst_apply hX hp, subst_pow hp, subst_X hp, h1]

section A2R3

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl : l ≠ 0` using `hp.ne_zero`. Establish `hpos : 0 < l` using `hp.pos`. Establish `hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / l)) l` using `Complex.isPrimitiveRoot_exp l hl`. Generalize the expression as in `Complex.exp (2 * Real.pi * Complex.I / l) = ζ at hζ`.

Rewrite using `[Polynomial.cyclotomic_eq_minpoly hζ hpos]`. Apply `minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hpos)` to reduce the goal to its premises. Simplify using `only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C]`. Establish `hs : l - 1 + 1 = l` using `Nat.sub_add_cancel hp.one_le`. Establish `hζ' : IsPrimitiveRoot ζ (l - 1 + 1)` using `by rwa [hs]`.

Establish `h` using `hζ'.prod_pow_sub_one_eq_order`. Rewrite `h` using `[(hp.even_sub_one hl2).neg_one_pow, one_mul]`. Rewrite using `[prod_Ioo_eq_prod_range, h]`. Establish `hc : (((l - 1 : ℕ) : ℂ) + 1) = (l : ℂ)`. Establish `: ((l - 1 + 1 : ℕ) : ℂ) = (l : ℂ)` using `by rw [hs]`.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[hc]`. Simplify using the standard rewrite rules.
-/
lemma cyclotomic_dvd_prod_X_pow_sub_one_sub (hl2 : l ≠ 2) :
    Polynomial.cyclotomic l ℤ ∣
      (∏ c ∈ Finset.Ioo 0 l, ((Polynomial.X : Polynomial ℤ) ^ c - 1)) - Polynomial.C (l : ℤ) := by
  have hp : l.Prime := Fact.out
  have hl : l ≠ 0 := hp.ne_zero
  have hpos : 0 < l := hp.pos
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / l)) l :=
    Complex.isPrimitiveRoot_exp l hl
  generalize Complex.exp (2 * Real.pi * Complex.I / l) = ζ at hζ
  rw [Polynomial.cyclotomic_eq_minpoly hζ hpos]
  apply minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hpos)
  simp only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C]
  have hs : l - 1 + 1 = l := Nat.sub_add_cancel hp.one_le
  have hζ' : IsPrimitiveRoot ζ (l - 1 + 1) := by rwa [hs]
  have h := hζ'.prod_pow_sub_one_eq_order
  rw [(hp.even_sub_one hl2).neg_one_pow, one_mul] at h
  rw [prod_Ioo_eq_prod_range, h]
  have hc : (((l - 1 : ℕ) : ℂ) + 1) = (l : ℂ) := by
    have : ((l - 1 + 1 : ℕ) : ℂ) = (l : ℂ) := by rw [hs]
    push_cast at this
    exact this
  rw [hc]
  simp

/- English proof (translation)
Take `⟨s, hs⟩` from `cyclotomic_dvd_prod_X_pow_sub_one_sub l hl2`. Establish `h` using `congrArg (Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧)) hs`. Simplify using `only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C, map_mul] at h`. Establish `hc : Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧) (Polynomial.cyclotomic l ℤ) = q l ℤ_[l]`. Rewrite using `[Polynomial.cyclotomic_prime, map_sum]`.

Simplify using `only [map_pow, Polynomial.aeval_X]`. Apply `mul_left_cancel₀ (X_ne_zero (R := ℤ_[l]))` to reduce the goal to its premises. Rewrite using `[(hq l ℤ_[l]).1]`. Establish `h2` using `mul_geom_sum (1 + X : ℤ_[l]⟦X⟧) l`. Simplify using `using h2`.

Establish `hl : (algebraMap ℤ ℤ_[l]⟦X⟧) (l : ℤ) = C (l : ℤ_[l])` using `by simp`. Rewrite `h` using `[hc, hl]`. Conclude with `⟨_, h⟩`.
-/
lemma q_dvd_prod_sub_l (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ (∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l]) := by
  obtain ⟨s, hs⟩ := cyclotomic_dvd_prod_X_pow_sub_one_sub l hl2
  have h := congrArg (Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧)) hs
  simp only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C,
    map_mul] at h
  have hc : Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧) (Polynomial.cyclotomic l ℤ) = q l ℤ_[l] := by
    rw [Polynomial.cyclotomic_prime, map_sum]
    simp only [map_pow, Polynomial.aeval_X]
    apply mul_left_cancel₀ (X_ne_zero (R := ℤ_[l]))
    rw [(hq l ℤ_[l]).1]
    have h2 := mul_geom_sum (1 + X : ℤ_[l]⟦X⟧) l
    simpa using h2
  have hl : (algebraMap ℤ ℤ_[l]⟦X⟧) (l : ℤ) = C (l : ℤ_[l]) := by simp
  rw [hc, hl] at h
  exact ⟨_, h⟩

/- English proof (translation)
Establish `h1 : br l ℤ_[l] (e * (l : ℤ_[l])) = phi l ℤ_[l] (br l ℤ_[l] e)`. Take `⟨a1, _, _, a4, _⟩` from `ha l ℤ_[l]`. Rewrite using `[a4, a1]`. Establish `h2 : ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) ∣ br l ℤ_[l] (e * (l : ℤ_[l]))`. Rewrite using `[h1]`.

Conclude with `dvd_subst_self (hasSubst_one_add_X_pow_sub_one_alt l) (constantCoeff_binomialSeriesSubOne_eq_zero l ℤ_[l] e)`. Rewrite `h2` using `[← (hq l ℤ_[l]).1]`. Take `⟨s, hs⟩` from `h2`. Establish `h3 : binomialSeries ℤ_[l] (e * (l : ℤ_[l])) = 1 + X * q l ℤ_[l] * s`. Rewrite using `[← hs, br]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(1 + X) ^ c * X * s, ?_⟩` and prove the remaining obligations. Rewrite using `[br, binomialSeries_add, binomialSeries_nat, mul_comm (l : ℤ_[l]) e, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma q_dvd_binomialSeriesSubOne_sub_pow (ha : ActLaws) (hq : QMul) (c : ℕ) (e : ℤ_[l]) :
    q l ℤ_[l] ∣ br l ℤ_[l] ((c : ℤ_[l]) + (l : ℤ_[l]) * e) - ((1 + X) ^ c - 1) := by
  have h1 : br l ℤ_[l] (e * (l : ℤ_[l])) = phi l ℤ_[l] (br l ℤ_[l] e) := by
    obtain ⟨a1, _, _, a4, _⟩ := ha l ℤ_[l]
    rw [a4, a1]
  have h2 : ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) ∣ br l ℤ_[l] (e * (l : ℤ_[l])) := by
    rw [h1]
    exact dvd_subst_self (hasSubst_one_add_X_pow_sub_one_alt l) (constantCoeff_binomialSeriesSubOne_eq_zero l ℤ_[l] e)
  rw [← (hq l ℤ_[l]).1] at h2
  obtain ⟨s, hs⟩ := h2
  have h3 : binomialSeries ℤ_[l] (e * (l : ℤ_[l])) = 1 + X * q l ℤ_[l] * s := by
    rw [← hs, br]
    ring
  refine ⟨(1 + X) ^ c * X * s, ?_⟩
  rw [br, binomialSeries_add, binomialSeries_nat, mul_comm (l : ℤ_[l]) e, h3]
  ring

/- English proof (translation)
The claim follows from `toZMod_ne_zero_of_mem_mu l hd`.
-/
lemma toZMod_ne_zero_of_mem_mu_alt {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := toZMod_ne_zero_of_mem_mu l hd

/- English proof (translation)
Establish `h0 : PadicInt.toZMod (d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l])) = 0`. Rewrite using `[map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Establish `hmem : d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod (p` using `l)) := h0`. Rewrite `hmem` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`. Take `⟨e, he⟩` from `hmem`.

Conclude with `⟨e, by linear_combination -he⟩`.
-/
lemma padicInt_eq_digit_add_mul (d : ℤ_[l]) :
    ∃ e : ℤ_[l], d = (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * e := by
  have h0 : PadicInt.toZMod (d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hmem : d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h0
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨e, he⟩ := hmem
  exact ⟨e, by linear_combination -he⟩

/- English proof (translation)
Use `Finset.prod_nbij (fun d => (PadicInt.toZMod d).val) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `d hd`. Rewrite using `[Finset.mem_Ioo]`. Use `⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt _⟩` and prove the remaining obligations. Introduce `h0`.

Conclude with `toZMod_ne_zero_of_mem_mu_alt l hd ((ZMod.val_eq_zero _).mp h0)`. Introduce `x hx y hy hxy`. Establish `h' : PadicInt.toZMod x = PadicInt.toZMod y` using `ZMod.val_injective _ hxy`. Conclude with `((hm l).2.1 _ (toZMod_ne_zero_of_mem_mu_alt l hx)).unique ⟨hx, rfl⟩ ⟨hy, h'.symm⟩`. Introduce `c hc`.

Rewrite `hc` using `[Finset.coe_Ioo, Set.mem_Ioo]`. Establish `hc0 : (c : ZMod l) ≠ 0`. Introduce `h`. Use `congrArg ZMod.val h` as an intermediate fact. Rewrite `this` using `[ZMod.val_natCast, Nat.mod_eq_of_lt hc.2, ZMod.val_zero]`.

Use linear arithmetic over natural numbers and integers. Take `⟨d, ⟨hd, hdc⟩, _⟩` from `(hm l).2.1 _ hc0`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Use `show (PadicInt.toZMod d).val = c`. Rewrite using `[hdc, ZMod.val_natCast, Nat.mod_eq_of_lt hc.2]`.
-/
lemma prod_mu_toZMod_val_eq_prod_Ioo (hm : MuFacts) {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ d ∈ mu l, G (PadicInt.toZMod d).val = ∏ c ∈ Finset.Ioo 0 l, G c := by
  refine Finset.prod_nbij (fun d => (PadicInt.toZMod d).val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro d hd
    rw [Finset.mem_Ioo]
    refine ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt _⟩
    intro h0
    exact toZMod_ne_zero_of_mem_mu_alt l hd ((ZMod.val_eq_zero _).mp h0)
  · intro x hx y hy hxy
    have h' : PadicInt.toZMod x = PadicInt.toZMod y := ZMod.val_injective _ hxy
    exact ((hm l).2.1 _ (toZMod_ne_zero_of_mem_mu_alt l hx)).unique ⟨hx, rfl⟩ ⟨hy, h'.symm⟩
  · intro c hc
    rw [Finset.coe_Ioo, Set.mem_Ioo] at hc
    have hc0 : (c : ZMod l) ≠ 0 := by
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc.2, ZMod.val_zero] at this
      omega
    obtain ⟨d, ⟨hd, hdc⟩, _⟩ := (hm l).2.1 _ hc0
    refine ⟨d, hd, ?_⟩
    show (PadicInt.toZMod d).val = c
    rw [hdc, ZMod.val_natCast, Nat.mod_eq_of_lt hc.2]

/- English proof (translation)
Establish `h1 : q l ℤ_[l] ∣ ∏ d ∈ mu l, br l ℤ_[l] d - ∏ d ∈ mu l, ((1 + X : ℤ_[l]⟦X⟧) ^ (PadicInt.toZMod d).val - 1)`. Apply `dvd_prod_sub_prod_of_dvd_sub` to reduce the goal to its premises. Introduce `d _`. Take `⟨e, he⟩` from `padicInt_eq_digit_add_mul l d`. Establish `h` using `q_dvd_binomialSeriesSubOne_sub_pow l ha hq (PadicInt.toZMod d).val e`.

Rewrite `h` using `[← he]`. Then use the resulting hypothesis. Rewrite `h1` using `[prod_mu_toZMod_val_eq_prod_Ioo l hm (fun c => (1 + X : ℤ_[l]⟦X⟧) ^ c - 1)]`. Establish `h2` using `dvd_add h1 (q_dvd_prod_sub_l l hq hl2)`. Establish `e : q0 l ℤ_[l] = (∏ d ∈ mu l, br l ℤ_[l] d - ∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) + ((∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l]))`. Rewrite using `[q0, pi0]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2`.
-/
lemma q_dvd_q_zero_of_ne_two (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ q0 l ℤ_[l] := by
  have h1 : q l ℤ_[l] ∣ ∏ d ∈ mu l, br l ℤ_[l] d -
      ∏ d ∈ mu l, ((1 + X : ℤ_[l]⟦X⟧) ^ (PadicInt.toZMod d).val - 1) := by
    apply dvd_prod_sub_prod_of_dvd_sub
    intro d _
    obtain ⟨e, he⟩ := padicInt_eq_digit_add_mul l d
    have h := q_dvd_binomialSeriesSubOne_sub_pow l ha hq (PadicInt.toZMod d).val e
    rwa [← he] at h
  rw [prod_mu_toZMod_val_eq_prod_Ioo l hm (fun c => (1 + X : ℤ_[l]⟦X⟧) ^ c - 1)] at h1
  have h2 := dvd_add h1 (q_dvd_prod_sub_l l hq hl2)
  have e : q0 l ℤ_[l] = (∏ d ∈ mu l, br l ℤ_[l] d -
      ∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) +
      ((∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l])) := by
    rw [q0, pi0]
    ring
  rw [e]
  exact h2

end A2R3

/- English proof (translation)
Introduce `l _ O _ _ hl2`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨g, hg⟩` from `q_dvd_q_zero_of_ne_two l ha hm hq hl2`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hg0 : constantCoeff g = -1`.

Establish `h` using `congrArg constantCoeff hg`. Establish `hq0 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l])`. Rewrite using `[q0, map_sub, constantCoeff_pi0_eq_zero, constantCoeff_C, zero_sub]`. Establish `hqc : constantCoeff (q l ℤ_[l]) = (l : ℤ_[l])`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, q, coeff_mk]`.

Simplify using the standard rewrite rules. Rewrite `h` using `[map_mul, hq0, hqc]`. Establish `h2 : (l : ℤ_[l]) * constantCoeff g = (l : ℤ_[l]) * (-1)` using `by rw [← h]; ring`. Conclude with `mul_left_cancel₀ hl0 h2`. Establish `hu : IsUnit g`.

Rewrite using `[isUnit_iff_constantCoeff, hg0]`. Conclude with `isUnit_one.neg`. Use `⟨Units.map (PowerSeries.map (algebraMap ℤ_[l] O) : ℤ_[l]⟦X⟧ →* O⟦X⟧) hu.unit, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.coe_map, IsUnit.unit_spec, ← map_q0_padic, ← map_q_padic, hg, map_mul, mul_comm]`. Both sides reduce to the same expression.

Rewrite using `[Units.coe_map, IsUnit.unit_spec]`. Express the relevant statement in the definitionally equal form `constantCoeff (PowerSeries.map (algebraMap ℤ_[l] O) g) = -1`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hg0]`. Simplify using the standard rewrite rules.
-/
theorem r3_unit_of_laws (ha : ActLaws) (hm : MuFacts) (hq : QMul) : UnitFactorQ := by
  intro l _ O _ _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := q_dvd_q_zero_of_ne_two l ha hm hq hl2
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hg0 : constantCoeff g = -1 := by
    have h := congrArg constantCoeff hg
    have hq0 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l]) := by
      rw [q0, map_sub, constantCoeff_pi0_eq_zero, constantCoeff_C, zero_sub]
    have hqc : constantCoeff (q l ℤ_[l]) = (l : ℤ_[l]) := by
      rw [← coeff_zero_eq_constantCoeff_apply, q, coeff_mk]
      simp
    rw [map_mul, hq0, hqc] at h
    have h2 : (l : ℤ_[l]) * constantCoeff g = (l : ℤ_[l]) * (-1) := by rw [← h]; ring
    exact mul_left_cancel₀ hl0 h2
  have hu : IsUnit g := by
    rw [isUnit_iff_constantCoeff, hg0]
    exact isUnit_one.neg
  refine ⟨Units.map (PowerSeries.map (algebraMap ℤ_[l] O) : ℤ_[l]⟦X⟧ →* O⟦X⟧) hu.unit, ?_, ?_⟩
  · rw [Units.coe_map, IsUnit.unit_spec, ← map_q0_padic, ← map_q_padic, hg, map_mul, mul_comm]
    rfl
  · rw [Units.coe_map, IsUnit.unit_spec]
    change constantCoeff (PowerSeries.map (algebraMap ℤ_[l] O) g) = -1
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hg0]
    simp

/- English proof (translation)
Introduce `l _ O _ _ _ ζ hl2 hζ b hb`. Take `⟨g, hg, _⟩` from `h3 l O hl2`. Establish `h1 : (X - C (ζ ^ b - 1)) ∣ q l O`. Rewrite using `[hr l O ζ hζ]`. Conclude with `Finset.dvd_prod_of_mem (fun b => (X : O⟦X⟧) - C (ζ ^ b - 1)) hb`.

Establish `h2 : pi0 l O - C (l : O) = q0 l O` using `rfl`. Rewrite using `[h2, hg]`. Conclude with `Dvd.dvd.mul_left h1 _`.
-/
theorem r3_divisibility_of_unit_roots (h3 : UnitFactorQ) (hr : QRoots) : RootOfUnityRemainder := by
  intro l _ O _ _ _ ζ hl2 hζ b hb
  obtain ⟨g, hg, _⟩ := h3 l O hl2
  have h1 : (X - C (ζ ^ b - 1)) ∣ q l O := by
    rw [hr l O ζ hζ]
    exact Finset.dvd_prod_of_mem (fun b => (X : O⟦X⟧) - C (ζ ^ b - 1)) hb
  have h2 : pi0 l O - C (l : O) = q0 l O := rfl
  rw [h2, hg]
  exact Dvd.dvd.mul_left h1 _

end PartA2

section PartB

section General

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `K generalizing g with`. Consider the case `zero => exact ⟨g.subst a, by simp⟩`. Consider the case `succ K ih`. Take `⟨h, hh⟩` from `ih (PowerSeries.mk fun p => coeff (p + 1) g)`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Establish `e : g.subst a = a * (PowerSeries.mk fun p => coeff (p + 1) g).subst a + C (constantCoeff g)` using `by conv_lhs => rw [eq_X_mul_shift_add_const g]`. Rewrite using `[subst_add ha, subst_mul ha, subst_X ha, subst_C]`. Both sides reduce to the same expression. Rewrite using `[e, hh, Finset.sum_range_succ']`. Simplify using `only [coeff_mk, coeff_zero_eq_constantCoeff_apply, pow_zero, mul_one]`.

Establish `e2 : a * ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ k = ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ (k + 1)`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[mul_add, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subst_eq_sum_range_add_pow_mul {a : R⟦X⟧} (ha : HasSubst a) (K : ℕ) (g : R⟦X⟧) :
    ∃ h : R⟦X⟧, g.subst a = ∑ k ∈ range K, C (coeff k g) * a ^ k + a ^ K * h := by
  induction K generalizing g with
  | zero => exact ⟨g.subst a, by simp⟩
  | succ K ih =>
    obtain ⟨h, hh⟩ := ih (PowerSeries.mk fun p => coeff (p + 1) g)
    refine ⟨h, ?_⟩
    have e : g.subst a = a * (PowerSeries.mk fun p => coeff (p + 1) g).subst a + C (constantCoeff g) := by
      conv_lhs => rw [eq_X_mul_shift_add_const g]
      rw [subst_add ha, subst_mul ha, subst_X ha, subst_C]
      rfl
    rw [e, hh, Finset.sum_range_succ']
    simp only [coeff_mk, coeff_zero_eq_constantCoeff_apply, pow_zero, mul_one]
    have e2 : a * ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ k =
        ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ (k + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [mul_add, e2]
    ring

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_zero]`.
-/
theorem subst_zero_eq_zero {a : R⟦X⟧} (ha : HasSubst a) : (0 : R⟦X⟧).subst a = 0 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_zero]

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff ((w : R⟦X⟧) * X ^ n) = 0`. Simplify using `[zero_pow hn.ne']`.
-/
theorem hasSubst_unit_mul_X_pow (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) : HasSubst ((w : R⟦X⟧) * X ^ n) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff ((w : R⟦X⟧) * X ^ n) = 0
  simp [zero_pow hn.ne']

/- English proof (translation)
Establish `h' : X ^ n * a = X ^ n * b`. Use `congrArg (fun t => ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * t) h` as an intermediate fact. Simplify using `only [← mul_assoc, Units.inv_mul, one_mul] at this`. Conclude with `this`. Use extensionality with `k`.

Use `congrArg (coeff (k + n)) h'` as an intermediate fact. Simplify `this` using `[PowerSeries.coeff_X_pow_mul']`.
-/
theorem cancel_unit_mul_X_pow (n : ℕ) (w : (R⟦X⟧)ˣ) {a b : R⟦X⟧}
    (h : (w : R⟦X⟧) * X ^ n * a = (w : R⟦X⟧) * X ^ n * b) : a = b := by
  have h' : X ^ n * a = X ^ n * b := by
    have := congrArg (fun t => ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * t) h
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    exact this
  ext k
  have := congrArg (coeff (k + n)) h'
  simpa [PowerSeries.coeff_X_pow_mul'] using this

def divQuotient (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) : R⟦X⟧ :=
  ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * PowerSeries.mk fun i => coeff (i + n) f

/- English proof (translation)
Establish `e : (w : R⟦X⟧) * X ^ n * divQuotient n w f = X ^ n * PowerSeries.mk fun i => coeff (i + n) f`. Unfold `divQuotient`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = X ^ n * PowerSeries.mk fun i => coeff (i + n) f := by rw [Units.mul_inv, one_mul]`.

Rewrite using `[e]`. Use extensionality with `m`. Rewrite using `[map_add, map_sum, coeff_X_pow_mul']`. Simplify using `only [coeff_C_mul_X_pow, coeff_mk]`. Distinguish the cases in `hm : m < n`.

Rewrite using `[if_neg (by omega), add_zero, Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hb (Fin.ext h.symm)`. Simplify using the standard rewrite rules. Rewrite using `[if_pos (by omega), Finset.sum_eq_zero, zero_add]`. Rewrite using `[Nat.sub_add_cancel (Nat.le_of_not_lt hm)]`. Introduce `b _`.

Rewrite using `[if_neg]`. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_sum_coeff_add_division (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) + (w : R⟦X⟧) * X ^ n * divQuotient n w f := by
  have e : (w : R⟦X⟧) * X ^ n * divQuotient n w f = X ^ n * PowerSeries.mk fun i => coeff (i + n) f := by
    unfold divQuotient
    calc (w : R⟦X⟧) * X ^ n * (((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * PowerSeries.mk fun i => coeff (i + n) f)
        = ((w : R⟦X⟧) * ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧)) * (X ^ n * PowerSeries.mk fun i => coeff (i + n) f) := by
          ring
      _ = X ^ n * PowerSeries.mk fun i => coeff (i + n) f := by rw [Units.mul_inv, one_mul]
  rw [e]
  ext m
  rw [map_add, map_sum, coeff_X_pow_mul']
  simp only [coeff_C_mul_X_pow, coeff_mk]
  by_cases hm : m < n
  · rw [if_neg (by omega), add_zero, Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  · rw [if_pos (by omega), Finset.sum_eq_zero, zero_add]
    · rw [Nat.sub_add_cancel (Nat.le_of_not_lt hm)]
    · intro b _
      rw [if_neg]
      have := b.2
      omega

/- English proof (translation)
Proceed by induction on `K with`. Consider the case `zero => simp`. Consider the case `succ K ih`. Rewrite using `[Finset.sum_range_succ, Function.iterate_succ_apply']`. Establish `h` using `eq_sum_coeff_add_division n w ((divQuotient n w)^[K] f)`.

Take the linear combination `ih + ((w : R⟦X⟧) * X ^ n) ^ K * h`.
-/
theorem eq_sum_iterated_division (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) (K : ℕ) :
    f = ∑ k ∈ range K, ((w : R⟦X⟧) * X ^ n) ^ k *
          (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) +
        ((w : R⟦X⟧) * X ^ n) ^ K * (divQuotient n w)^[K] f := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have h := eq_sum_coeff_add_division n w ((divQuotient n w)^[K] f)
    linear_combination ih + ((w : R⟦X⟧) * X ^ n) ^ K * h

/- English proof (translation)
Establish `hP` using `hasSubst_unit_mul_X_pow n hn w`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `N`. Rewrite using `[map_zero]`. Use `(X_pow_dvd_iff.mp ?_) N (Nat.lt_succ_self N)` and prove the remaining obligations.

Use `choose h hh using fun j : Fin n => subst_eq_sum_range_add_pow_mul hP (N + 1) (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f))`. Simplify using `only [coeff_mk] at hh`. Establish `e2 : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = ∑ k ∈ range (N + 1), ((w : R⟦X⟧) * X ^ n) ^ k * (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) + ((w : R⟦X⟧) * X ^ n) ^ (N + 1) …`. Rewrite using `[Finset.sum_congr rfl fun j _ => by rw [hh j]]`. Simplify using `only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `e3 : f - ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = ((w : R⟦X⟧) * X ^ n) ^ (N + 1) * ((divQuotient n w)^[N + 1] f - ∑ j : Fin n, h j * X ^ (j : ℕ))`.

Rewrite using `[e2]`. Take the linear combination `eq_sum_iterated_division n w f (N + 1)`. Rewrite using `[e3, mul_pow, ← pow_mul]`. Use `Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _) _` and prove the remaining obligations. Conclude with `Nat.le_mul_of_pos_left _ hn`.
-/
theorem eq_sum_subst_unit_mul_X_pow (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  rw [← sub_eq_zero]
  ext N
  rw [map_zero]
  refine (X_pow_dvd_iff.mp ?_) N (Nat.lt_succ_self N)
  choose h hh using fun j : Fin n =>
    subst_eq_sum_range_add_pow_mul hP (N + 1) (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f))
  simp only [coeff_mk] at hh
  have e2 : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ∑ k ∈ range (N + 1), ((w : R⟦X⟧) * X ^ n) ^ k *
          (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) +
        ((w : R⟦X⟧) * X ^ n) ^ (N + 1) * ∑ j : Fin n, h j * X ^ (j : ℕ) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hh j]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : f - ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ((w : R⟦X⟧) * X ^ n) ^ (N + 1) *
        ((divQuotient n w)^[N + 1] f - ∑ j : Fin n, h j * X ^ (j : ℕ)) := by
    rw [e2]
    linear_combination eq_sum_iterated_division n w f (N + 1)
  rw [e3, mul_pow, ← pow_mul]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _) _
  exact Nat.le_mul_of_pos_left _ hn

/- English proof (translation)
Establish `hP` using `hasSubst_unit_mul_X_pow n hn w`. Use `choose h hh using fun j : Fin n => subst_eq_sum_range_add_pow_mul hP 1 (d j)`. Simplify using `only [Finset.sum_range_one, pow_zero, mul_one, pow_one, coeff_zero_eq_constantCoeff_apply] at hh`. Establish `e : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = ∑ j : Fin n, C (constantCoeff (d j)) * X ^ (j : ℕ) + X ^ n * ((w : R⟦X⟧) * ∑ j : Fin n, h j * X ^ (j : ℕ))`. Rewrite using `[Finset.sum_congr rfl fun j _ => by rw [hh j]]`.

Simplify using `only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite `h0` using `[e]`. Establish `h1` using `congrArg (coeff (i : ℕ)) h0`.

Rewrite `h1` using `[map_add, map_sum, coeff_X_pow_mul', if_neg (by have := i.2; omega), add_zero, map_zero]`. Simplify using `only [coeff_C_mul_X_pow] at h1`. Rewrite `h1` using `[Finset.sum_eq_single i]`. Simplify using `using h1`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext h.symm)`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_eq_zero_of_sum_subst (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (d : Fin n → R⟦X⟧)
    (h0 : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0) (i : Fin n) :
    constantCoeff (d i) = 0 := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  choose h hh using fun j : Fin n => subst_eq_sum_range_add_pow_mul hP 1 (d j)
  simp only [Finset.sum_range_one, pow_zero, mul_one, pow_one,
    coeff_zero_eq_constantCoeff_apply] at hh
  have e : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      ∑ j : Fin n, C (constantCoeff (d j)) * X ^ (j : ℕ) +
        X ^ n * ((w : R⟦X⟧) * ∑ j : Fin n, h j * X ^ (j : ℕ)) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hh j]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e] at h0
  have h1 := congrArg (coeff (i : ℕ)) h0
  rw [map_add, map_sum, coeff_X_pow_mul', if_neg (by have := i.2; omega), add_zero, map_zero] at h1
  simp only [coeff_C_mul_X_pow] at h1
  rw [Finset.sum_eq_single i] at h1
  · simpa using h1
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · simp

/- English proof (translation)
Establish `hP` using `hasSubst_unit_mul_X_pow n hn w`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `d h0 j`. Rewrite using `[coeff_zero_eq_constantCoeff_apply]`.

Conclude with `constantCoeff_eq_zero_of_sum_subst n hn w d h0 j`. Consider the case `succ k ih`. Introduce `d h0 j`. Establish `hc` using `constantCoeff_eq_zero_of_sum_subst n hn w d h0`. Establish `hd : ∀ j, d j = X * PowerSeries.mk fun p => coeff (p + 1) (d j)`.

Introduce `j`. Use `conv_lhs => rw [eq_X_mul_shift_add_const (d j), hc j, map_zero, add_zero]`. Establish `h1 : (w : R⟦X⟧) * X ^ n * ∑ j : Fin n, (PowerSeries.mk fun p => coeff (p + 1) (d j)).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = (w : R⟦X⟧) * X ^ n * 0`. Rewrite using `[mul_zero, ← h0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `conv_rhs => rw [hd j, subst_mul hP, subst_X hP]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `ih (fun j => PowerSeries.mk fun p => coeff (p + 1) (d j)) (cancel_unit_mul_X_pow n w h1) j`. Simplify using `using h2`.
-/
theorem coeff_eq_zero_of_subst_sum_eq_zero (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (k : ℕ) :
    ∀ d : Fin n → R⟦X⟧, ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0 →
      ∀ j, coeff k (d j) = 0 := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  induction k with
  | zero =>
    intro d h0 j
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_eq_zero_of_sum_subst n hn w d h0 j
  | succ k ih =>
    intro d h0 j
    have hc := constantCoeff_eq_zero_of_sum_subst n hn w d h0
    have hd : ∀ j, d j = X * PowerSeries.mk fun p => coeff (p + 1) (d j) := by
      intro j
      conv_lhs => rw [eq_X_mul_shift_add_const (d j), hc j, map_zero, add_zero]
    have h1 : (w : R⟦X⟧) * X ^ n * ∑ j : Fin n, (PowerSeries.mk fun p => coeff (p + 1) (d j)).subst
        ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = (w : R⟦X⟧) * X ^ n * 0 := by
      rw [mul_zero, ← h0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [hd j, subst_mul hP, subst_X hP]
      ring
    have h2 := ih (fun j => PowerSeries.mk fun p => coeff (p + 1) (d j)) (cancel_unit_mul_X_pow n w h1) j
    simpa using h2

end General

/- English proof (translation)
Introduce `R _ n w hn f`. Establish `hP` using `hasSubst_unit_mul_X_pow n hn w`. Use `⟨fun j => PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f), eq_sum_subst_unit_mul_X_pow n hn w f, ?_⟩` and prove the remaining obligations. Introduce `g' hg'`. Establish `hg : f = ∑ j : Fin n, (g' j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ)` using `hg'`.

Use function extensionality and compare the values at `j`. Use extensionality with `k`. Establish `h0 : ∑ j : Fin n, (g' j - PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0`. Simplify using `only [subst_sub hP, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[← hg, ← eq_sum_subst_unit_mul_X_pow n hn w f, sub_self]`.

Establish `h1` using `coeff_eq_zero_of_subst_sum_eq_zero n hn w k _ h0 j`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Conclude with `h1`.
-/
theorem general_basis_holds : BasisGeneral := by
  intro R _ n w hn f
  have hP := hasSubst_unit_mul_X_pow n hn w
  refine ⟨fun j => PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f), eq_sum_subst_unit_mul_X_pow n hn w f, ?_⟩
  intro g' hg'
  have hg : f = ∑ j : Fin n, (g' j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) := hg'
  funext j
  ext k
  have h0 : ∑ j : Fin n, (g' j - PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
      ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0 := by
    simp only [subst_sub hP, sub_mul, Finset.sum_sub_distrib]
    rw [← hg, ← eq_sum_subst_unit_mul_X_pow n hn w f, sub_self]
  have h1 := coeff_eq_zero_of_subst_sum_eq_zero n hn w k _ h0 j
  rw [map_sub, sub_eq_zero] at h1
  exact h1

section General2

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `ha : HasSubst (X * s)` using `HasSubst.of_constantCoeff_zero' (by simp)`. Take `⟨h, hh⟩` from `subst_eq_sum_range_add_pow_mul ha (j + 1) f`. Rewrite using `[hh, map_add, map_sum]`. Establish `e1 : coeff j ((X * s) ^ (j + 1) * h) = 0`. Rewrite using `[mul_pow, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]`.

Rewrite using `[e1, add_zero, Finset.sum_eq_single j]`. Rewrite using `[coeff_C_mul, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow]`. Introduce `k hk hkj`. Rewrite using `[coeff_C_mul]`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases.

Rewrite using `[pow_zero, coeff_one, if_neg hj.ne', mul_zero]`. Rewrite using `[h0 k hk0 (by have := Finset.mem_range.mp hk; omega), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) h`.
-/
theorem coeff_subst_X_mul_of_low_zero (s f : R⟦X⟧) (j : ℕ) (hj : 0 < j)
    (h0 : ∀ i, 0 < i → i < j → coeff i f = 0) :
    coeff j (f.subst (X * s)) = coeff j f * constantCoeff s ^ j := by
  have ha : HasSubst (X * s) := HasSubst.of_constantCoeff_zero' (by simp)
  obtain ⟨h, hh⟩ := subst_eq_sum_range_add_pow_mul ha (j + 1) f
  rw [hh, map_add, map_sum]
  have e1 : coeff j ((X * s) ^ (j + 1) * h) = 0 := by
    rw [mul_pow, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  rw [e1, add_zero, Finset.sum_eq_single j]
  · rw [coeff_C_mul, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_pow]
  · intro k hk hkj
    rw [coeff_C_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, coeff_one, if_neg hj.ne', mul_zero]
    · rw [h0 k hk0 (by have := Finset.mem_range.mp hk; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) h

/- English proof (translation)
Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `h0 hn`. Establish `h1` using `coeff_subst_X_mul_of_low_zero s f j h0 (fun i hi hij => ih i hij hi (by omega))`.

Rewrite `h1` using `[hinv]`. Establish `h2 : coeff j f * (constantCoeff s ^ j - 1) = 0` using `by linear_combination -h1`. Conclude with `(hu j h0 hn).mul_left_eq_zero.mp h2`.
-/
theorem coeff_eq_zero_of_subst_invariant (s f : R⟦X⟧) (n : ℕ) (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∀ j, 0 < j → j < n → coeff j f = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h0 hn
    have h1 := coeff_subst_X_mul_of_low_zero s f j h0 (fun i hi hij => ih i hij hi (by omega))
    rw [hinv] at h1
    have h2 : coeff j f * (constantCoeff s ^ j - 1) = 0 := by linear_combination -h1
    exact (hu j h0 hn).mul_left_eq_zero.mp h2

/- English proof (translation)
Establish `ha : HasSubst (X * s)` using `HasSubst.of_constantCoeff_zero' (by simp)`. Establish `hc` using `coeff_eq_zero_of_subst_invariant s f n hinv hu`. Establish `hdiv` using `eq_sum_coeff_add_division n w f`. Establish `hT : ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) = C (constantCoeff f)`. Rewrite using `[Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[hc b (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite `hdiv` using `[hT]`. Establish `h1 : f.subst (X * s) = C (constantCoeff f) + (w : R⟦X⟧) * X ^ n * (divQuotient n w f).subst (X * s)` using `by conv_lhs => rw [hdiv]`. Rewrite using `[subst_add ha, subst_mul ha, hP, subst_C]`. Both sides reduce to the same expression. Rewrite `h1` using `[hinv]`.

Apply `cancel_unit_mul_X_pow n w` to reduce the goal to its premises. Take the linear combination `hdiv - h1`.
-/
theorem averagedSeries_subst_invariant (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (s f : R⟦X⟧)
    (hP : ((w : R⟦X⟧) * X ^ n).subst (X * s) = (w : R⟦X⟧) * X ^ n)
    (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    (divQuotient n w f).subst (X * s) = divQuotient n w f := by
  have ha : HasSubst (X * s) := HasSubst.of_constantCoeff_zero' (by simp)
  have hc := coeff_eq_zero_of_subst_invariant s f n hinv hu
  have hdiv := eq_sum_coeff_add_division n w f
  have hT : ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) = C (constantCoeff f) := by
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [hc b (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2]
      simp
    · simp
  rw [hT] at hdiv
  have h1 : f.subst (X * s) =
      C (constantCoeff f) + (w : R⟦X⟧) * X ^ n * (divQuotient n w f).subst (X * s) := by
    conv_lhs => rw [hdiv]
    rw [subst_add ha, subst_mul ha, hP, subst_C]
    rfl
  rw [hinv] at h1
  apply cancel_unit_mul_X_pow n w
  linear_combination hdiv - h1

/- English proof (translation)
Establish `hit : ∀ k, ((divQuotient n w)^[k] f).subst (X * s) = (divQuotient n w)^[k] f`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hinv`. Consider the case `succ k ih`.

Rewrite using `[Function.iterate_succ_apply']`. Conclude with `averagedSeries_subst_invariant n hn w s _ hP ih hu`. Use `⟨PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f), ?_⟩` and prove the remaining obligations. Establish `h` using `eq_sum_subst_unit_mul_X_pow n hn w f`. Establish `h' : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = (PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n)`.

Rewrite using `[Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]`. Rewrite using `[pow_zero, mul_one]`. Introduce `b _ hb`. Establish `hz : (PowerSeries.mk fun k => coeff (b : ℕ) ((divQuotient n w)^[k] f)) = 0`. Use extensionality with `k`.

Rewrite using `[coeff_mk, map_zero]`. Conclude with `coeff_eq_zero_of_subst_invariant s _ n (hit k) hu b (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2`. Rewrite using `[hz, subst_zero_eq_zero (hasSubst_unit_mul_X_pow n hn w), zero_mul]`. Simplify using the standard rewrite rules. Conclude with `h.trans h'`.
-/
theorem exists_subst_of_invariant (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (s f : R⟦X⟧)
    (hP : ((w : R⟦X⟧) * X ^ n).subst (X * s) = (w : R⟦X⟧) * X ^ n)
    (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∃ g : R⟦X⟧, f = g.subst ((w : R⟦X⟧) * X ^ n) := by
  have hit : ∀ k, ((divQuotient n w)^[k] f).subst (X * s) = (divQuotient n w)^[k] f := by
    intro k
    induction k with
    | zero => simpa using hinv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact averagedSeries_subst_invariant n hn w s _ hP ih hu
  refine ⟨PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f), ?_⟩
  have h := eq_sum_subst_unit_mul_X_pow n hn w f
  have h' : ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) =
      (PowerSeries.mk fun k => coeff 0 ((divQuotient n w)^[k] f)).subst ((w : R⟦X⟧) * X ^ n) := by
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [pow_zero, mul_one]
    · intro b _ hb
      have hz : (PowerSeries.mk fun k => coeff (b : ℕ) ((divQuotient n w)^[k] f)) = 0 := by
        ext k
        rw [coeff_mk, map_zero]
        exact coeff_eq_zero_of_subst_invariant s _ n (hit k) hu b
          (Nat.pos_of_ne_zero fun h => hb (Fin.ext h)) b.2
      rw [hz, subst_zero_eq_zero (hasSubst_unit_mul_X_pow n hn w), zero_mul]
    · simp
  exact h.trans h'

end General2

section Pi0

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Use `(Fact.out : l.Prime).two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem prime_sub_one_pos_alt : 0 < l - 1 := by
  have := (Fact.out : l.Prime).two_le
  omega

/- English proof (translation)
The claim follows from `hasSubst_br_padic l O c`.
-/
theorem hasSubst_binomialSeriesSubOne (c : ℤ_[l]) : HasSubst (br l O c) := hasSubst_br_padic l O c

/- English proof (translation)
Rewrite using `[pi0, map_prod]`. Conclude with `Finset.prod_eq_zero (one_mem_mu l) (constantCoeff_binomialSeriesSubOne l O 1)`.
-/
theorem constantCoeff_pi0 : constantCoeff (pi0 l O) = 0 := by
  rw [pi0, map_prod]
  exact Finset.prod_eq_zero (one_mem_mu l) (constantCoeff_binomialSeriesSubOne l O 1)

/- English proof (translation)
Apply `PowerSeries.HasSubst.of_constantCoeff_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (pi0 l O) = 0`. Conclude with `constantCoeff_pi0 l O`.
-/
theorem hasSubst_pi0_alt : HasSubst (pi0 l O) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (pi0 l O) = 0
  exact constantCoeff_pi0 l O

/- English proof (translation)
Rewrite using `[inc, inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_mul]`.
-/
theorem pi0Subst_mul (f g : O⟦X⟧) : inc l O (f * g) = inc l O f * inc l O g := by
  rw [inc, inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_mul]

/- English proof (translation)
Rewrite using `[inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_pow]`.
-/
theorem inc_pow (f : O⟦X⟧) (n : ℕ) : inc l O (f ^ n) = inc l O f ^ n := by
  rw [inc, inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_pow]

/- English proof (translation)
Rewrite using `[inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_zero]`.
-/
theorem inc_zero : inc l O 0 = 0 := by
  rw [inc, ← PowerSeries.coe_substAlgHom (hasSubst_pi0_alt l O), map_zero]

/- English proof (translation)
Establish `hs` using `hasSubst_pi0_alt l O`. Rewrite using `[inc, ← PowerSeries.coe_substAlgHom hs, map_sub, q0]`. Use `congr 1`. Rewrite using `[PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[PowerSeries.smul_eq_C_mul, mul_one]`. Use `_ = (l : O) • PowerSeries.substAlgHom hs 1 := map_smul _ _ _`. Use `_ = C (l : O) := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]`.
-/
theorem inc_X_sub_l_eq_q0 : inc l O (X - C (l : O)) = q0 l O := by
  have hs := hasSubst_pi0_alt l O
  rw [inc, ← PowerSeries.coe_substAlgHom hs, map_sub, q0]
  congr 1
  · rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  calc PowerSeries.substAlgHom hs (C (l : O)) = PowerSeries.substAlgHom hs ((l : O) • 1) := by
        rw [PowerSeries.smul_eq_C_mul, mul_one]
    _ = (l : O) • PowerSeries.substAlgHom hs 1 := map_smul _ _ _
    _ = C (l : O) := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]

/- English proof (translation)
Use `⟨_, br_eq_X_mul_shift l O c, ?_⟩` and prove the remaining obligations. Simplify using `[coeff_one_br]`.
-/
theorem br_eq_X_mul_const (c : ℤ_[l]) :
    ∃ s : O⟦X⟧, br l O c = X * s ∧ constantCoeff s = algebraMap ℤ_[l] O c := by
  refine ⟨_, br_eq_X_mul_shift l O c, ?_⟩
  simp [coeff_one_br]

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod l)ˣ)`. Establish `ho : orderOf g = l - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]`. Take `⟨d, ⟨hd, hdx⟩, -⟩` from `(hm l).2.1 (g : ZMod l) g.ne_zero`. Use `⟨d, hd, fun j h0 hj => ?_⟩` and prove the remaining obligations.

Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, hdx, sub_eq_zero]`. Introduce `h`. Establish `h' : g ^ j = 1` using `Units.ext (by simpa using h)`. Conclude with `pow_ne_one_of_lt_orderOf h0.ne' (ho ▸ hj) h'`.
-/
theorem exists_mu_generator_pow_sub_one_isUnit (hm : MuFacts) : ∃ d ∈ mu l, ∀ j, 0 < j → j < l - 1 → IsUnit (d ^ j - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨d, ⟨hd, hdx⟩, -⟩ := (hm l).2.1 (g : ZMod l) g.ne_zero
  refine ⟨d, hd, fun j h0 hj => ?_⟩
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, hdx, sub_eq_zero]
  intro h
  have h' : g ^ j = 1 := Units.ext (by simpa using h)
  exact pow_ne_one_of_lt_orderOf h0.ne' (ho ▸ hj) h'

end Pi0

/- English proof (translation)
Introduce `l _ O _ _ h2 f`. Take `⟨w, hw, -⟩` from `h1 l O h2`. Establish `h` using `hb O (l - 1) w (prime_sub_one_pos_alt l) f`. Simplify `h` using `only [inc, hw]`.
-/
theorem r2_basis_of_r1 (h1 : R1) (hb : BasisGeneral) : PowerSeriesFreeBasis := by
  intro l _ O _ _ h2 f
  obtain ⟨w, hw, -⟩ := h1 l O h2
  have h := hb O (l - 1) w (prime_sub_one_pos_alt l) f
  simpa only [inc, hw] using h

/- English proof (translation)
Introduce `l _ O _ _ h2 f`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Take `⟨w, hw, -⟩` from `h1 l O h2`. Take `⟨d, hd, hdu⟩` from `exists_mu_generator_pow_sub_one_isUnit l hm`.

Take `⟨s, hs, hs0⟩` from `br_eq_X_mul_const l O d`. Establish `hinv : f.subst (X * s) = f`. Rewrite using `[← hs]`. Conclude with `hf d hd`. Establish `hP : ((w : O⟦X⟧) * X ^ (l - 1)).subst (X * s) = (w : O⟦X⟧) * X ^ (l - 1)`.

Rewrite using `[← hs, ← hw]`. Conclude with `hi l O d hd`. Establish `hu : ∀ j, 0 < j → j < l - 1 → IsUnit (constantCoeff s ^ j - 1)`. Introduce `j h0 hj`. Rewrite using `[hs0]`.

Use `(hdu j h0 hj).map (algebraMap ℤ_[l] O)` as an intermediate fact. Simplify using `using this`. Take `⟨g, hg⟩` from `exists_subst_of_invariant (l - 1) (prime_sub_one_pos_alt l) w s f hP hinv hu`. Use `⟨g, ?_⟩` and prove the remaining obligations. Unfold `inc`.

Rewrite using `[hw]`. Conclude with `hg`. Introduce and unpack `⟨g, rfl⟩ d hd`. Establish `h` using `hi l O d hd`. Unfold `act at h`.

Unfold `act inc`. Rewrite using `[subst_comp_subst_apply (hasSubst_pi0_alt l O) (hasSubst_binomialSeriesSubOne l O d), h]`.
-/
theorem fixed_relation_of_mu_and_inverse (hm : MuFacts) (h1 : R1) (hi : DivisibilityInvariant) : RootsOfUnityInvariants := by
  intro l _ O _ _ h2 f
  constructor
  · intro hf
    obtain ⟨w, hw, -⟩ := h1 l O h2
    obtain ⟨d, hd, hdu⟩ := exists_mu_generator_pow_sub_one_isUnit l hm
    obtain ⟨s, hs, hs0⟩ := br_eq_X_mul_const l O d
    have hinv : f.subst (X * s) = f := by
      rw [← hs]
      exact hf d hd
    have hP : ((w : O⟦X⟧) * X ^ (l - 1)).subst (X * s) = (w : O⟦X⟧) * X ^ (l - 1) := by
      rw [← hs, ← hw]
      exact hi l O d hd
    have hu : ∀ j, 0 < j → j < l - 1 → IsUnit (constantCoeff s ^ j - 1) := by
      intro j h0 hj
      rw [hs0]
      have := (hdu j h0 hj).map (algebraMap ℤ_[l] O)
      simpa using this
    obtain ⟨g, hg⟩ := exists_subst_of_invariant (l - 1) (prime_sub_one_pos_alt l) w s f hP hinv hu
    refine ⟨g, ?_⟩
    unfold inc
    rw [hw]
    exact hg
  · rintro ⟨g, rfl⟩ d hd
    have h := hi l O d hd
    unfold act at h
    unfold act inc
    rw [subst_comp_subst_apply (hasSubst_pi0_alt l O) (hasSubst_binomialSeriesSubOne l O d), h]

/- English proof (translation)
Introduce `l _ O _ _ h2 S m y hm`. Take `⟨g, hg, -⟩` from `h3 l O h2`. Establish `hpos` using `prime_sub_one_pos_alt l`. Establish `hq : q l O = ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * q0 l O`. Rewrite using `[hg, Units.inv_mul_cancel_left]`.

Take `⟨a, ha, -⟩` from `hb l O h2 (((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y)`. Establish `ha' : ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y = ∑ j : Fin (l - 1), inc l O (a j) * X ^ (j : ℕ)` using `ha`. Take `⟨a0, -, huniq⟩` from `hb l O h2 (inc l O m)`. Establish `e1 : inc l O m = ∑ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ)`. Establish `hj : ∀ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ) = q0 l O ^ S * (inc l O (a j) * X ^ (j : ℕ))`.

Introduce `j`. Rewrite using `[pi0Subst_mul, inc_pow, inc_X_sub_l_eq_q0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, ← ha', hm, hq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : inc l O m = ∑ j : Fin (l - 1), inc l O (if (j : ℕ) = 0 then m else 0) * X ^ (j : ℕ)`. Rewrite using `[Finset.sum_eq_single (⟨0, hpos⟩ : Fin (l - 1))]`. Simplify using the standard rewrite rules. Introduce `b _ hb'`. Rewrite using `[if_neg (fun h => hb' (Fin.ext h)), inc_zero, zero_mul]`.

Simplify using the standard rewrite rules. Establish `e3` using `(huniq _ e1).trans (huniq _ e2).symm`. Establish `e4` using `congrFun e3 ⟨0, hpos⟩`. Conclude with `⟨a ⟨0, hpos⟩, by simpa using e4.symm⟩`.
-/
theorem fourth_relation_of_unit_and_basis (h3 : UnitFactorQ) (hb : PowerSeriesFreeBasis) : R4 := by
  intro l _ O _ _ h2 S m y hm
  obtain ⟨g, hg, -⟩ := h3 l O h2
  have hpos := prime_sub_one_pos_alt l
  have hq : q l O = ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * q0 l O := by
    rw [hg, Units.inv_mul_cancel_left]
  obtain ⟨a, ha, -⟩ := hb l O h2 (((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y)
  have ha' : ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y =
      ∑ j : Fin (l - 1), inc l O (a j) * X ^ (j : ℕ) := ha
  obtain ⟨a0, -, huniq⟩ := hb l O h2 (inc l O m)
  have e1 : inc l O m =
      ∑ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ) := by
    have hj : ∀ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ) =
        q0 l O ^ S * (inc l O (a j) * X ^ (j : ℕ)) := by
      intro j
      rw [pi0Subst_mul, inc_pow, inc_X_sub_l_eq_q0]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, ← ha', hm, hq]
    ring
  have e2 : inc l O m =
      ∑ j : Fin (l - 1), inc l O (if (j : ℕ) = 0 then m else 0) * X ^ (j : ℕ) := by
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (l - 1))]
    · simp
    · intro b _ hb'
      rw [if_neg (fun h => hb' (Fin.ext h)), inc_zero, zero_mul]
    · simp
  have e3 := (huniq _ e1).trans (huniq _ e2).symm
  have e4 := congrFun e3 ⟨0, hpos⟩
  exact ⟨a ⟨0, hpos⟩, by simpa using e4.symm⟩

end PartB

section PartB2

/- English proof (translation)
The claim follows from `dvd_subst_self ha hf`.
-/
lemma dvd_subst_of_constantCoeff_zero {R : Type} [CommRing R] (a f : R⟦X⟧) (ha : HasSubst a)
    (hf : constantCoeff f = 0) : a ∣ f.subst a := dvd_subst_self ha hf

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma algHom_C_eq {R : Type} [CommRing R] (Φ : R⟦X⟧ →ₐ[R] R⟦X⟧) (a : R) : Φ (C a) = C a := by
  calc Φ (C a) = Φ (a • 1) := by rw [PowerSeries.smul_eq_C_mul, mul_one]
    _ = a • Φ 1 := map_smul Φ a 1
    _ = C a := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert c s hc ih`. Rewrite using `[Finset.prod_insert hc, Finset.prod_insert hc]`. Establish `h1` using `h c (Finset.mem_insert_self c s)`.

Establish `h2` using `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Establish `e : a c * ∏ i ∈ s, a i - b c * ∏ i ∈ s, b i = (a c - b c) * ∏ i ∈ s, a i + b c * (∏ i ∈ s, a i - ∏ i ∈ s, b i)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)`.
-/
lemma dvd_prod_sub_prod {R ι : Type} [CommRing R] (s : Finset ι) (a b : ι → R) (x : R)
    (h : ∀ i ∈ s, x ∣ a i - b i) : x ∣ ∏ i ∈ s, a i - ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc]
    have h1 := h c (Finset.mem_insert_self c s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : a c * ∏ i ∈ s, a i - b c * ∏ i ∈ s, b i =
        (a c - b c) * ∏ i ∈ s, a i + b c * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨e, he⟩` from `ih`. Use `⟨(n : R) + e + x * e, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, he]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma one_add_pow_eq_linear_add_sq_mul {R : Type} [CommRing R] (x : R) (n : ℕ) :
    ∃ e, (1 + x) ^ n = 1 + (n : R) * x + x ^ 2 * e := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(n : R) + e + x * e, ?_⟩
    rw [pow_succ, he]
    push_cast
    ring

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
The claim follows from `constantCoeff_binomialSeriesSubOne l O c`.
-/
lemma constantCoeff_br_zero (c : ℤ_[l]) : constantCoeff (br l O c) = 0 := constantCoeff_binomialSeriesSubOne l O c

/- English proof (translation)
Use `⟨_, br_eq_X_mul_shift l O e, ?_⟩` and prove the remaining obligations. Simplify using `[coeff_one_br]`.
-/
lemma br_eq_X_mul_const_alt (e : ℤ_[l]) :
    ∃ β : O⟦X⟧, br l O e = X * β ∧ constantCoeff β = algebraMap ℤ_[l] O e := by
  refine ⟨_, br_eq_X_mul_shift l O e, ?_⟩
  simp [coeff_one_br]

/- English proof (translation)
The claim follows from `constantCoeff_pi0_eq_zero l O`.
-/
lemma constantCoeff_pi0_eq_zero_alt (hm : MuFacts) : constantCoeff (pi0 l O) = 0 := constantCoeff_pi0_eq_zero l O

/- English proof (translation)
Use `⟨PowerSeries.substAlgHom (hasSubst_pi0_alt l O), fun f => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[inc, PowerSeries.coe_substAlgHom]`. Rewrite using `[PowerSeries.coe_substAlgHom, PowerSeries.subst_X (hasSubst_pi0_alt l O)]`.
-/
lemma exists_algHom_inc_pi0 (hm : MuFacts) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, inc l O f = Φ f) ∧ Φ X = pi0 l O := by
  refine ⟨PowerSeries.substAlgHom (hasSubst_pi0_alt l O), fun f => ?_, ?_⟩
  · rw [inc, PowerSeries.coe_substAlgHom]
  · rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X (hasSubst_pi0_alt l O)]

/- English proof (translation)
Use `⟨PowerSeries.substAlgHom (hasSubst_br_padic l O c), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[act, PowerSeries.coe_substAlgHom]`.
-/
lemma exists_algHom_act (c : ℤ_[l]) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, ∀ f, act l O c f = Φ f := by
  refine ⟨PowerSeries.substAlgHom (hasSubst_br_padic l O c), fun f => ?_⟩
  rw [act, PowerSeries.coe_substAlgHom]

/- English proof (translation)
Take `⟨Φ, hΦ, hX⟩` from `exists_algHom_inc_pi0 l O hm`. Rewrite using `[hΦ]`. Use `conv_lhs => rw [eq_X_mul_shift_add_const f]`. Rewrite using `[map_add, map_mul, hX, algHom_C_eq, map_add, map_mul, constantCoeff_pi0_eq_zero_alt l O hm, zero_mul, zero_add, constantCoeff_C]`.
-/
lemma constantCoeff_inc (hm : MuFacts) (f : O⟦X⟧) : constantCoeff (inc l O f) = constantCoeff f := by
  obtain ⟨Φ, hΦ, hX⟩ := exists_algHom_inc_pi0 l O hm
  rw [hΦ]
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [map_add, map_mul, hX, algHom_C_eq, map_add, map_mul, constantCoeff_pi0_eq_zero_alt l O hm, zero_mul,
    zero_add, constantCoeff_C]

/- English proof (translation)
Take `⟨h1, -, -, h4, -⟩` from `ha l O`. Establish `hphi : br l O (e * (l : ℤ_[l])) = phi l O (br l O e)` using `by rw [h4, h1]`. Establish `hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧)` using `HasSubst.of_constantCoeff_zero' (by simp)`. Take `⟨t, ht⟩` from `dvd_subst_of_constantCoeff_zero _ (br l O e) hs (constantCoeff_br_zero l O e)`. Establish `hX` using `(hq l O).1`.

Use `⟨binomialSeries O d * t, ?_⟩` and prove the remaining obligations. Establish `h0 : br l O (e * (l : ℤ_[l])) = X * q l O * t` using `by rw [hphi, phi, ht, hX]`. Establish `h2 : binomialSeries O (e * (l : ℤ_[l])) = 1 + X * q l O * t`. Simplify using `only [br] at h0`. Take the linear combination `h0`.

Simplify using `only [br]`. Rewrite using `[binomialSeries_add, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma binomialSeriesSubOne_add_prime_mul_cong (ha : ActLaws) (hq : QMul) (d e : ℤ_[l]) :
    ∃ s : O⟦X⟧, br l O (d + e * (l : ℤ_[l])) = br l O d + X * q l O * s := by
  obtain ⟨h1, -, -, h4, -⟩ := ha l O
  have hphi : br l O (e * (l : ℤ_[l])) = phi l O (br l O e) := by rw [h4, h1]
  have hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  obtain ⟨t, ht⟩ := dvd_subst_of_constantCoeff_zero _ (br l O e) hs (constantCoeff_br_zero l O e)
  have hX := (hq l O).1
  refine ⟨binomialSeries O d * t, ?_⟩
  have h0 : br l O (e * (l : ℤ_[l])) = X * q l O * t := by rw [hphi, phi, ht, hX]
  have h2 : binomialSeries O (e * (l : ℤ_[l])) = 1 + X * q l O * t := by
    simp only [br] at h0
    linear_combination h0
  simp only [br]
  rw [binomialSeries_add, h2]
  ring

/- English proof (translation)
The claim follows from `map_pi0_padic l O`.
-/
lemma map_pi0_padicInt_algebraMap : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := map_pi0_padic l O

/- English proof (translation)
The claim follows from `map_q0_padicInt l O`.
-/
lemma map_q0_padic_alt : PowerSeries.map (algebraMap ℤ_[l] O) (q0 l ℤ_[l]) = q0 l O := map_q0_padicInt l O

/- English proof (translation)
Rewrite using `[act, act, map_subst_powerSeries _ (hasSubst_br_padic l ℤ_[l] c), map_algebraMap_binomialSeriesSubOne]`.
-/
lemma map_act_padic (c : ℤ_[l]) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (act l ℤ_[l] c f) =
      act l O c (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [act, act, map_subst_powerSeries _ (hasSubst_br_padic l ℤ_[l] c), map_algebraMap_binomialSeriesSubOne]

/- English proof (translation)
Rewrite using `[inc, inc, map_subst_powerSeries _ (hasSubst_pi0_alt l ℤ_[l]), map_pi0_padic]`.
-/
lemma map_algebraMap_pi0Subst (hm : MuFacts) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (inc l ℤ_[l] f) =
      inc l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [inc, inc, map_subst_powerSeries _ (hasSubst_pi0_alt l ℤ_[l]), map_pi0_padic]

end

/- English proof (translation)
Take `⟨hcard, -, hprod⟩` from `hm l`. Establish `hprod` using `hprod hl`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Use `choose β hβ hβ0 using br_eq_X_mul_const_alt l ℤ_[l]`. Take `⟨a1, a2, -, -, -, a6, -⟩` from `ha l ℤ_[l]`.

Take `⟨B, hB⟩ : ∃ B, B = ∏ d ∈ mu l, β d` from `⟨_, rfl⟩`. Take `⟨B', hB'⟩ : ∃ B', B' = ∏ d ∈ mu l, β (d * u)` from `⟨_, rfl⟩`. Establish `hP : pi0 l ℤ_[l] = X ^ (l - 1) * B`. Rewrite using `[pi0, hB, ← hcard, ← prod_const, ← prod_mul_distrib]`. Conclude with `prod_congr rfl fun d _ => hβ d`.

Establish `hact : act l ℤ_[l] u (pi0 l ℤ_[l]) = X ^ (l - 1) * B'`. Take `⟨Φ, hΦ⟩` from `exists_algHom_act l ℤ_[l] u`. Establish `h0 : act l ℤ_[l] u (pi0 l ℤ_[l]) = ∏ d ∈ mu l, br l ℤ_[l] (d * u)`. Rewrite using `[hΦ, pi0, map_prod]`. Use `prod_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[← hΦ]`. Conclude with `a1 u d`. Rewrite using `[h0, hB', ← hcard, ← prod_const, ← prod_mul_distrib]`. Conclude with `prod_congr rfl fun d _ => hβ _`. Establish `hB0 : constantCoeff B = -1`.

Rewrite using `[hB, map_prod, ← hprod]`. Conclude with `prod_congr rfl fun d _ => by rw [hβ0]; rfl`. Establish `hB'0 : constantCoeff B' = -u ^ (l - 1)`. Rewrite using `[hB', map_prod]`. Establish `h0 : ∀ d ∈ mu l, constantCoeff (β (d * u)) = d * u` using `fun d _ => by rw [hβ0]; rfl`.

Rewrite using `[prod_congr rfl h0, prod_mul_distrib, prod_const, hprod, hcard]`. Expand and normalize the polynomial expressions, which then agree. Establish `hBu : IsUnit B` using `isUnit_iff_constantCoeff.mpr (by rw [hB0]; exact isUnit_one.neg)`. Take `⟨Bi, hBi⟩` from `hBu.exists_right_inv`. Take `⟨r, hrdef⟩ : ∃ r, r = B' * Bi` from `⟨_, rfl⟩`.

Establish `hr : act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * r`. Rewrite using `[hact, hP, hrdef]`. Take the linear combination `(-(X ^ (l - 1) * B')) * hBi`. Establish `hQ : q l ℤ_[l] ∣ B' - B`. Rewrite using `[hB', hB]`.

Use `dvd_prod_sub_prod _ _ _ _ fun d _ => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `binomialSeriesSubOne_add_prime_mul_cong l ℤ_[l] ha hq d (d * c)`. Establish `hdu : d * u = d + d * c * (l : ℤ_[l])` using `by rw [hu]; ring`. Rewrite `hs` using `[← hdu, hβ, hβ]`. Establish `h0 : X * (β (d * u) - β d) = X * (q l ℤ_[l] * s)` using `by linear_combination hs`.

Conclude with `⟨s, mul_left_cancel₀ X_ne_zero h0⟩`. Establish `hQr : q l ℤ_[l] ∣ r - 1`. Establish `h0 : r - 1 = (B' - B) * Bi` using `by rw [hrdef]; linear_combination hBi`. Rewrite using `[h0]`. Conclude with `Dvd.dvd.mul_right hQ _`.

Establish `hP0 : pi0 l ℤ_[l] ≠ 0`. Rewrite using `[hP]`. Conclude with `mul_ne_zero (pow_ne_zero _ X_ne_zero) hBu.ne_zero`. Establish `hinv : ∀ d ∈ mu l, act l ℤ_[l] d r = r`. Introduce `d hd`.

Establish `e1 : act l ℤ_[l] d (act l ℤ_[l] u (pi0 l ℤ_[l])) = act l ℤ_[l] u (pi0 l ℤ_[l])`. Rewrite using `[a2, mul_comm, ← a2, hi l ℤ_[l] d hd]`. Rewrite `e1` using `[hr, (a6 d _ _).1, hi l ℤ_[l] d hd]`. Conclude with `mul_left_cancel₀ hP0 e1`. Take `⟨ρ, hρ⟩` from `(hf l ℤ_[l] hl r).mp hinv`.

Take `⟨Φ, hΦ, hΦX⟩` from `exists_algHom_inc_pi0 l ℤ_[l] hm`. Take `⟨y, hy⟩` from `hQr`. Take `⟨un, hun⟩` from `h4 l ℤ_[l] hl 1 (ρ - 1) y (by`. Rewrite using `[hΦ, map_sub, map_one, ← hΦ, ← hρ, hy, pow_one])`. Establish `hrr : r = 1 + inc l ℤ_[l] un * q0 l ℤ_[l]`.

Establish `h0 : ρ = 1 + (X - C (l : ℤ_[l])) * un`. Rewrite `hun` using `[pow_one]`. Take the linear combination `hun`. Rewrite using `[hρ, hΦ ρ, h0, map_add, map_one, map_mul, map_sub, hΦX, algHom_C_eq, ← hΦ, q0]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨un, by rw [hr, hrr], ?_⟩` and prove the remaining obligations. Establish `hBi0 : constantCoeff Bi = -1`. Establish `h0` using `congrArg constantCoeff hBi`. Rewrite `h0` using `[map_mul, hB0, map_one]`. Take the linear combination `-h0`.

Establish `hr0 : constantCoeff r = u ^ (l - 1)`. Rewrite using `[hrdef, map_mul, hB'0, hBi0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq00 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l])`. Rewrite using `[q0, map_sub, constantCoeff_pi0_eq_zero_alt l ℤ_[l] hm, constantCoeff_C, zero_sub]`.

Establish `hmain : u ^ (l - 1) = 1 + constantCoeff un * (-(l : ℤ_[l]))`. Establish `h0` using `congrArg constantCoeff hrr`. Rewrite `h0` using `[hr0, map_add, map_one, map_mul, constantCoeff_inc l ℤ_[l] hm, hq00]`. Conclude with `h0`. Take `⟨e, he⟩` from `one_add_pow_eq_linear_add_sq_mul ((l : ℤ_[l]) * c) (l - 1)`.

Establish `hn : ((l - 1 : ℕ) : ℤ_[l]) = (l : ℤ_[l]) - 1`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_one]`. Rewrite `hmain` using `[hu, he, hn]`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Use `⟨-c - c ^ 2 * e, ?_⟩` and prove the remaining obligations.

Establish `h0 : (l : ℤ_[l]) * constantCoeff un = (l : ℤ_[l]) * (c + (l : ℤ_[l]) * (-c - c ^ 2 * e))`. Take the linear combination `hmain`. Conclude with `mul_left_cancel₀ hl0 h0`.
-/
theorem act_unit_pi0_eq_mul_padic (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hi : DivisibilityInvariant) (hf : RootsOfUnityInvariants) (h4 : R4)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (u c : ℤ_[l]) (hu : u = 1 + (l : ℤ_[l]) * c) :
    ∃ un : ℤ_[l]⟦X⟧,
      act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * (1 + inc l ℤ_[l] un * q0 l ℤ_[l]) ∧
      ∃ e : ℤ_[l], constantCoeff un = c + (l : ℤ_[l]) * e := by
  classical
  obtain ⟨hcard, -, hprod⟩ := hm l
  have hprod := hprod hl
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  choose β hβ hβ0 using br_eq_X_mul_const_alt l ℤ_[l]
  obtain ⟨a1, a2, -, -, -, a6, -⟩ := ha l ℤ_[l]
  obtain ⟨B, hB⟩ : ∃ B, B = ∏ d ∈ mu l, β d := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = ∏ d ∈ mu l, β (d * u) := ⟨_, rfl⟩
  have hP : pi0 l ℤ_[l] = X ^ (l - 1) * B := by
    rw [pi0, hB, ← hcard, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun d _ => hβ d
  have hact : act l ℤ_[l] u (pi0 l ℤ_[l]) = X ^ (l - 1) * B' := by
    obtain ⟨Φ, hΦ⟩ := exists_algHom_act l ℤ_[l] u
    have h0 : act l ℤ_[l] u (pi0 l ℤ_[l]) = ∏ d ∈ mu l, br l ℤ_[l] (d * u) := by
      rw [hΦ, pi0, map_prod]
      refine prod_congr rfl fun d _ => ?_
      rw [← hΦ]
      exact a1 u d
    rw [h0, hB', ← hcard, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun d _ => hβ _
  have hB0 : constantCoeff B = -1 := by
    rw [hB, map_prod, ← hprod]
    exact prod_congr rfl fun d _ => by rw [hβ0]; rfl
  have hB'0 : constantCoeff B' = -u ^ (l - 1) := by
    rw [hB', map_prod]
    have h0 : ∀ d ∈ mu l, constantCoeff (β (d * u)) = d * u := fun d _ => by rw [hβ0]; rfl
    rw [prod_congr rfl h0, prod_mul_distrib, prod_const, hprod, hcard]
    ring
  have hBu : IsUnit B := isUnit_iff_constantCoeff.mpr (by rw [hB0]; exact isUnit_one.neg)
  obtain ⟨Bi, hBi⟩ := hBu.exists_right_inv
  obtain ⟨r, hrdef⟩ : ∃ r, r = B' * Bi := ⟨_, rfl⟩
  have hr : act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * r := by
    rw [hact, hP, hrdef]
    linear_combination (-(X ^ (l - 1) * B')) * hBi
  have hQ : q l ℤ_[l] ∣ B' - B := by
    rw [hB', hB]
    refine dvd_prod_sub_prod _ _ _ _ fun d _ => ?_
    obtain ⟨s, hs⟩ := binomialSeriesSubOne_add_prime_mul_cong l ℤ_[l] ha hq d (d * c)
    have hdu : d * u = d + d * c * (l : ℤ_[l]) := by rw [hu]; ring
    rw [← hdu, hβ, hβ] at hs
    have h0 : X * (β (d * u) - β d) = X * (q l ℤ_[l] * s) := by linear_combination hs
    exact ⟨s, mul_left_cancel₀ X_ne_zero h0⟩
  have hQr : q l ℤ_[l] ∣ r - 1 := by
    have h0 : r - 1 = (B' - B) * Bi := by rw [hrdef]; linear_combination hBi
    rw [h0]
    exact Dvd.dvd.mul_right hQ _
  have hP0 : pi0 l ℤ_[l] ≠ 0 := by
    rw [hP]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hBu.ne_zero
  have hinv : ∀ d ∈ mu l, act l ℤ_[l] d r = r := by
    intro d hd
    have e1 : act l ℤ_[l] d (act l ℤ_[l] u (pi0 l ℤ_[l])) = act l ℤ_[l] u (pi0 l ℤ_[l]) := by
      rw [a2, mul_comm, ← a2, hi l ℤ_[l] d hd]
    rw [hr, (a6 d _ _).1, hi l ℤ_[l] d hd] at e1
    exact mul_left_cancel₀ hP0 e1
  obtain ⟨ρ, hρ⟩ := (hf l ℤ_[l] hl r).mp hinv
  obtain ⟨Φ, hΦ, hΦX⟩ := exists_algHom_inc_pi0 l ℤ_[l] hm
  obtain ⟨y, hy⟩ := hQr
  obtain ⟨un, hun⟩ := h4 l ℤ_[l] hl 1 (ρ - 1) y (by
    rw [hΦ, map_sub, map_one, ← hΦ, ← hρ, hy, pow_one])
  have hrr : r = 1 + inc l ℤ_[l] un * q0 l ℤ_[l] := by
    have h0 : ρ = 1 + (X - C (l : ℤ_[l])) * un := by
      rw [pow_one] at hun
      linear_combination hun
    rw [hρ, hΦ ρ, h0, map_add, map_one, map_mul, map_sub, hΦX, algHom_C_eq, ← hΦ, q0]
    ring
  refine ⟨un, by rw [hr, hrr], ?_⟩

  have hBi0 : constantCoeff Bi = -1 := by
    have h0 := congrArg constantCoeff hBi
    rw [map_mul, hB0, map_one] at h0
    linear_combination -h0
  have hr0 : constantCoeff r = u ^ (l - 1) := by
    rw [hrdef, map_mul, hB'0, hBi0]
    ring
  have hq00 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l]) := by
    rw [q0, map_sub, constantCoeff_pi0_eq_zero_alt l ℤ_[l] hm, constantCoeff_C, zero_sub]
  have hmain : u ^ (l - 1) = 1 + constantCoeff un * (-(l : ℤ_[l])) := by
    have h0 := congrArg constantCoeff hrr
    rw [hr0, map_add, map_one, map_mul, constantCoeff_inc l ℤ_[l] hm, hq00] at h0
    exact h0
  obtain ⟨e, he⟩ := one_add_pow_eq_linear_add_sq_mul ((l : ℤ_[l]) * c) (l - 1)
  have hn : ((l - 1 : ℕ) : ℤ_[l]) = (l : ℤ_[l]) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hu, he, hn] at hmain
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨-c - c ^ 2 * e, ?_⟩
  have h0 : (l : ℤ_[l]) * constantCoeff un = (l : ℤ_[l]) * (c + (l : ℤ_[l]) * (-c - c ^ 2 * e)) := by
    linear_combination hmain
  exact mul_left_cancel₀ hl0 h0

/- English proof (translation)
Introduce `l _ O _ _ hl u c hu`. Take `⟨unZ, hA, e, he⟩` from `act_unit_pi0_eq_mul_padic ha hm hq hi hf h4 l hl u c hu`. Establish `H1 : act l O u (pi0 l O) = pi0 l O * (1 + inc l O (PowerSeries.map (algebraMap ℤ_[l] O) unZ) * q0 l O)`. Establish `h0` using `congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hA`. Rewrite `h0` using `[map_act_padic, map_mul, map_add, map_one, map_mul, map_algebraMap_pi0Subst l O hm, map_q0_padic_alt, map_pi0_padicInt_algebraMap]`.

Conclude with `h0`. Use `⟨PowerSeries.map (algebraMap ℤ_[l] O) unZ, H1, ⟨algebraMap ℤ_[l] O e, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, he, map_add, map_mul, map_natCast]`. Take `⟨Ψ, hΨ⟩` from `exists_algHom_act l O u`. Take `⟨Φ, hΦ, hΦX⟩` from `exists_algHom_inc_pi0 l O hm`.

Establish `h0 : act l O u (q0 l O) = act l O u (pi0 l O) - C (l : O)`. Rewrite using `[hΨ, q0, map_sub, algHom_C_eq, ← hΨ]`. Rewrite using `[h0, H1, hΦ (1 + X * _), map_add, map_one, map_mul, hΦX, ← hΦ, q0]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `isUnit_iff_constantCoeff.mpr (by simp)`.
-/
theorem sixth_relation_of_action_and_mu_laws (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hi : DivisibilityInvariant) (hf : RootsOfUnityInvariants)
    (h4 : R4) : R6 := by
  intro l _ O _ _ hl u c hu
  obtain ⟨unZ, hA, e, he⟩ := act_unit_pi0_eq_mul_padic ha hm hq hi hf h4 l hl u c hu
  have H1 : act l O u (pi0 l O) =
      pi0 l O * (1 + inc l O (PowerSeries.map (algebraMap ℤ_[l] O) unZ) * q0 l O) := by
    have h0 := congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hA
    rw [map_act_padic, map_mul, map_add, map_one, map_mul, map_algebraMap_pi0Subst l O hm,
      map_q0_padic_alt, map_pi0_padicInt_algebraMap] at h0
    exact h0
  refine ⟨PowerSeries.map (algebraMap ℤ_[l] O) unZ, H1, ⟨algebraMap ℤ_[l] O e, ?_⟩, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, he,
      map_add, map_mul, map_natCast]
  · obtain ⟨Ψ, hΨ⟩ := exists_algHom_act l O u
    obtain ⟨Φ, hΦ, hΦX⟩ := exists_algHom_inc_pi0 l O hm
    have h0 : act l O u (q0 l O) = act l O u (pi0 l O) - C (l : O) := by
      rw [hΨ, q0, map_sub, algHom_C_eq, ← hΨ]
    rw [h0, H1, hΦ (1 + X * _), map_add, map_one, map_mul, hΦX, ← hΦ, q0]
    ring
  · exact isUnit_iff_constantCoeff.mpr (by simp)

end PartB2

section PartC

section CapelliProof

variable {𝒰 : Type} [Ring 𝒰]

def orderedProd {N : ℕ} (a : Fin N → 𝒰) : 𝒰 := (List.ofFn a).prod

def columnDet {N : ℕ} (c : Fin N → Fin N → 𝒰) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • orderedProd (fun p => c p (σ p))

def columnDetAt {N : ℕ} (E : Fin N → Fin N → 𝒰) (u : 𝒰) (J : Fin N → Fin N) : 𝒰 :=
  columnDet (fun p s => capA E (u - ((p : ℕ) : 𝒰)) s (J p))

end CapelliProof

end PartC

section PartD

/- English proof (translation)
Take `⟨e, he⟩` from `one_add_pow_eq_linear_add_sq_mul (x * v) n`. Rewrite using `[he]`. Conclude with `⟨v ^ 2 * e, by ring⟩`.
-/
theorem sq_dvd_one_add_pow_sub_linear (R : Type) [CommRing R] (x v : R) (n : ℕ) :
    x ^ 2 ∣ (1 + x * v) ^ n - (1 + (n : R) * (x * v)) := by
  obtain ⟨e, he⟩ := one_add_pow_eq_linear_add_sq_mul (x * v) n
  rw [he]
  exact ⟨v ^ 2 * e, by ring⟩

/- English proof (translation)
Introduce `R _ x v U κ hU`. Take `⟨n, rfl | rfl⟩` from `κ.eq_nat_or_neg`. Use `sq_dvd_one_add_pow_sub_linear R x v n` as an intermediate fact. Simplify `this` using `[zpow_natCast, hU]`. Take `⟨s, hs⟩` from `sq_dvd_one_add_pow_sub_linear R x v n`.

Establish `h1 : ((U ^ n : Rˣ) : R) * ((U ^ (-(n : ℤ)) : Rˣ) : R) = 1`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `h2 : ((U ^ n : Rˣ) : R) = 1 + (n : R) * (x * v) + x ^ 2 * s`. Rewrite using `[Units.val_pow_eq_pow_val, hU]`.

Take the linear combination `hs`. Establish `h3 : x ^ 2 ∣ ((U ^ n : Rˣ) : R) * (((U ^ (-(n : ℤ)) : Rˣ) : R) - (1 + ((-(n : ℤ) : ℤ) : R) * (x * v)))`. Use `⟨(n : R) ^ 2 * v ^ 2 - s * (1 - n * (x * v)), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sub, h1, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Units.dvd_mul_left.mp h3`.
-/
theorem zpow_congruence_general : ZpowCongGen := by
  intro R _ x v U κ hU
  obtain ⟨n, rfl | rfl⟩ := κ.eq_nat_or_neg
  · have := sq_dvd_one_add_pow_sub_linear R x v n
    simpa [zpow_natCast, hU] using this
  · obtain ⟨s, hs⟩ := sq_dvd_one_add_pow_sub_linear R x v n
    have h1 : ((U ^ n : Rˣ) : R) * ((U ^ (-(n : ℤ)) : Rˣ) : R) = 1 := by
      rw [← Units.val_mul]; simp
    have h2 : ((U ^ n : Rˣ) : R) = 1 + (n : R) * (x * v) + x ^ 2 * s := by
      rw [Units.val_pow_eq_pow_val, hU]; linear_combination hs
    have h3 : x ^ 2 ∣ ((U ^ n : Rˣ) : R) *
        (((U ^ (-(n : ℤ)) : Rˣ) : R) - (1 + ((-(n : ℤ) : ℤ) : R) * (x * v))) := by
      refine ⟨(n : R) ^ 2 * v ^ 2 - s * (1 - n * (x * v)), ?_⟩
      rw [mul_sub, h1, h2]; push_cast; ring
    exact Units.dvd_mul_left.mp h3

/- English proof (translation)
Introduce `l _ u c m hu`. Take `⟨e, he⟩` from `zpow_congruence_general ℤ_[l] (l : ℤ_[l]) c u (-m) hu`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `: ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = (1 + ((-m : ℤ) : ℤ_[l]) * ((l : ℤ_[l]) * c)) + (l : ℤ_[l]) ^ 2 * e`. Take the linear combination `he`.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_congruence_padic : ThetaCongPadic := by
  intro l _ u c m hu
  obtain ⟨e, he⟩ := zpow_congruence_general ℤ_[l] (l : ℤ_[l]) c u (-m) hu
  refine ⟨e, ?_⟩
  have : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = (1 + ((-m : ℤ) : ℤ_[l]) * ((l : ℤ_[l]) * c)) + (l : ℤ_[l]) ^ 2 * e := by
    linear_combination he
  rw [this]; push_cast; ring

/- English proof (translation)
Introduce `O k _ _ red lam n t S P f g hl`. Establish `h1 : ((P.map (PowerSeries.map red)).submatrix f g).det = PowerSeries.map red (P.submatrix f g).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Use `⟨h1, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[h1]`. Use `map_dvd (PowerSeries.map red) h` as an intermediate fact. Simplify `this` using `[hl]`.
-/
theorem minor_reduction_holds : MinorRed := by
  intro O k _ _ red lam n t S P f g hl
  have h1 : ((P.map (PowerSeries.map red)).submatrix f g).det =
      PowerSeries.map red (P.submatrix f g).det := by
    rw [RingHom.map_det]; rfl
  refine ⟨h1, fun h => ?_⟩
  rw [h1]
  have := map_dvd (PowerSeries.map red) h
  simpa [hl] using this

/- English proof (translation)
Introduce `O L _ _ ι n Θ Γ lam r G hι hlam hΓ hG`. Establish `ha : ι lam ≠ 0` using `fun h => hlam (hι (by simpa using h))`. Establish `h1 : Γ.map ι = 1 + ι lam • Θ.map ι`. Rewrite using `[hΓ]`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.map_apply, hij]`. Establish `h2 : Matrix.diagonal (fun j => ι (1 + lam * r j)) = 1 + ι lam • Matrix.diagonal (fun j => ι (r j))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij]`. Rewrite `hG` using `[h1, h2, add_mul, mul_add, one_mul, mul_one, add_right_inj, Matrix.smul_mul, Matrix.mul_smul]`.

Establish `h3 : Θ.map ι * (G : Matrix (Fin n) (Fin n) L) = (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j))` using `smul_right_injective _ ha hG`. Establish `h4 : Θ.map ι = (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j)) * ((G⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) : Matrix (Fin n) (Fin n) L)`. Rewrite using `[← h3, mul_assoc, Units.mul_inv, mul_one]`. Apply `Polynomial.map_injective ι hι` to reduce the goal to its premises. Rewrite using `[← Matrix.charpoly_map, h4, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal, Polynomial.map_prod]`.

Simplify using the standard rewrite rules.
-/
theorem charpoly_diagonal_holds : CharpolyDiag := by
  intro O L _ _ ι n Θ Γ lam r G hι hlam hΓ hG
  have ha : ι lam ≠ 0 := fun h => hlam (hι (by simpa using h))
  have h1 : Γ.map ι = 1 + ι lam • Θ.map ι := by
    rw [hΓ]; ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, hij]
  have h2 : Matrix.diagonal (fun j => ι (1 + lam * r j)) =
      1 + ι lam • Matrix.diagonal (fun j => ι (r j)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h1, h2, add_mul, mul_add, one_mul, mul_one, add_right_inj, Matrix.smul_mul,
    Matrix.mul_smul] at hG
  have h3 : Θ.map ι * (G : Matrix (Fin n) (Fin n) L) =
      (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j)) :=
    smul_right_injective _ ha hG
  have h4 : Θ.map ι = (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j)) *
      ((G⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) : Matrix (Fin n) (Fin n) L) := by
    rw [← h3, mul_assoc, Units.mul_inv, mul_one]
  apply Polynomial.map_injective ι hι
  rw [← Matrix.charpoly_map, h4, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal,
    Polynomial.map_prod]
  simp

end PartD

section PartE

section PartE

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `h : (G * P).submatrix f g = fun i => ∑ k, G (f i) k • (fun j => P k (g j))`. Use function extensionality and compare the values at `i j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[h]`. Establish `h2` using `(Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap.map_sum (fun i k => G (f i) k • (fun j => P k (g j)))`.

Use `show (Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap _ = _`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`. Both sides reduce to the same expression.
-/
theorem det_submatrix_mul_eq_sum {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ]
    (G : Matrix α β R) (P : Matrix β γ R) (f : τ → α) (g : τ → γ) :
    ((G * P).submatrix f g).det =
      ∑ r : τ → β, (∏ i, G (f i) (r i)) * (P.submatrix r g).det := by
  classical
  have h : (G * P).submatrix f g = fun i => ∑ k, G (f i) k • (fun j => P k (g j)) := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  have h2 := (Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap.map_sum
    (fun i k => G (f i) k • (fun j => P k (g j)))
  show (Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap _ = _
  rw [h2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

/- English proof (translation)
Rewrite using `[det_submatrix_mul_eq_sum]`. Conclude with `Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (h r g) _`.
-/
theorem dvd_det_submatrix_mul_left {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ] (x : R)
    (G : Matrix α β R) (P : Matrix β γ R)
    (h : ∀ (f : τ → β) (g : τ → γ), x ∣ (P.submatrix f g).det) (f : τ → α) (g : τ → γ) :
    x ∣ ((G * P).submatrix f g).det := by
  rw [det_submatrix_mul_eq_sum]
  exact Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (h r g) _

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_mul, det_submatrix_mul_eq_sum]`. Use `Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right ?_ _` and prove the remaining obligations. Rewrite using `[← Matrix.transpose_submatrix, Matrix.det_transpose]`. Conclude with `h f r`.
-/
theorem dvd_det_submatrix_mul_right {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ] (x : R)
    (P : Matrix α β R) (H : Matrix β γ R)
    (h : ∀ (f : τ → α) (g : τ → β), x ∣ (P.submatrix f g).det) (f : τ → α) (g : τ → γ) :
    x ∣ ((P * H).submatrix f g).det := by
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_mul, det_submatrix_mul_eq_sum]
  refine Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right ?_ _
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  exact h f r

/- English proof (translation)
Distinguish the cases in `hf : Function.Injective f`. Use `swap`. Simplify using `only [Function.Injective, not_forall] at hf`. Take `⟨i, j, hij, hne⟩` from `hf`. Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij])]`.

Conclude with `dvd_zero _`. Distinguish the cases in `hg : Function.Injective g`. Use `swap`. Simplify using `only [Function.Injective, not_forall] at hg`. Take `⟨i, j, hij, hne⟩` from `hg`.

Rewrite using `[Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])]`. Conclude with `dvd_zero _`. Establish `hf' : StrictMono (f ∘ Tuple.sort f)` using `(Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)`. Establish `hg' : StrictMono (g ∘ Tuple.sort g)` using `(Tuple.monotone_sort g).strictMono_of_injective (hg.comp (Tuple.sort g).injective)`. Establish `h1` using `h _ _ hf' hg'`.

Establish `h2 : P.submatrix (f ∘ Tuple.sort f) (g ∘ Tuple.sort g) = ((P.submatrix f g).submatrix (Tuple.sort f) id).submatrix id (Tuple.sort g)`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite `h1` using `[h2, Matrix.det_permute', Matrix.det_permute]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort f)) with e1 | e1 <;>`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort g)) with e2 | e2 <;>`. Simplify `h1` using `[e1, e2]`.
-/
theorem dvd_det_submatrix_of_minorsDvd {m p t : ℕ} (x : R) (P : Matrix (Fin m) (Fin p) R) (h : MinorsDvd x t P)
    (f : Fin t → Fin m) (g : Fin t → Fin p) : x ∣ (P.submatrix f g).det := by
  by_cases hf : Function.Injective f
  swap
  · simp only [Function.Injective, not_forall] at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij])]
    exact dvd_zero _
  by_cases hg : Function.Injective g
  swap
  · simp only [Function.Injective, not_forall] at hg
    obtain ⟨i, j, hij, hne⟩ := hg
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])]
    exact dvd_zero _
  have hf' : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  have hg' : StrictMono (g ∘ Tuple.sort g) :=
    (Tuple.monotone_sort g).strictMono_of_injective (hg.comp (Tuple.sort g).injective)
  have h1 := h _ _ hf' hg'
  have h2 : P.submatrix (f ∘ Tuple.sort f) (g ∘ Tuple.sort g) =
      ((P.submatrix f g).submatrix (Tuple.sort f) id).submatrix id (Tuple.sort g) := by
    ext i j; rfl
  rw [h2, Matrix.det_permute', Matrix.det_permute] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort f)) with e1 | e1 <;>
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort g)) with e2 | e2 <;>
  simpa [e1, e2] using h1

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hx` to reduce the goal to its premises. Establish `h1` using `dvd_det_submatrix_mul_right _ M M' hcon e e`. Establish `h2 : ((x ^ h) • (1 : Matrix ι ι R)).submatrix e e = (x ^ h) • (1 : Matrix τ τ R)`.

Rewrite using `[← Matrix.submatrix_one e he]`. Both sides reduce to the same expression. Rewrite `h1` using `[hM, h2, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul, mul_comm h]`. Conclude with `h1`.
-/
theorem exists_submatrix_det_not_dvd_of_mul_eq {ι τ : Type} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    (x : R) (h : ℕ) (M M' : Matrix ι ι R) (e : τ → ι) (he : Function.Injective e)
    (hM : M * M' = (x ^ h) • (1 : Matrix ι ι R))
    (hx : ¬ x ^ (Fintype.card τ * h + 1) ∣ x ^ (Fintype.card τ * h)) :
    ∃ f g : τ → ι, ¬ x ^ (Fintype.card τ * h + 1) ∣ (M.submatrix f g).det := by
  by_contra hcon
  push Not at hcon
  apply hx
  have h1 := dvd_det_submatrix_mul_right _ M M' hcon e e
  have h2 : ((x ^ h) • (1 : Matrix ι ι R)).submatrix e e = (x ^ h) • (1 : Matrix τ τ R) := by
    rw [← Matrix.submatrix_one e he]; rfl
  rw [hM, h2, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul, mul_comm h] at h1
  exact h1

/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[pow_dvd_iff_le_emultiplicity, not_le]`. Rewrite using `[emultiplicity_mul hπ]`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.1 (ne_top_of_lt hy)`. Rewrite `hx`, the goal using `[← hm]`.

Rewrite `hy`, the goal using `[← hk]`. Normalize the coercions in `at hx hy ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_pow_dvd_mul_of_not_pow_dvd [IsDomain R] {π x y : R} {a b : ℕ} (hπ : Prime π)
    (hx : ¬ π ^ (a + 1) ∣ x) (hy : ¬ π ^ (b + 1) ∣ y) : ¬ π ^ (a + b + 1) ∣ x * y := by
  rw [pow_dvd_iff_le_emultiplicity, not_le] at hx hy ⊢
  rw [emultiplicity_mul hπ]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hy)
  rw [← hm] at hx ⊢
  rw [← hk] at hy ⊢
  norm_cast at hx hy ⊢
  omega

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `hd`. Conclude with `hπ.not_isUnit (isUnit_of_dvd_one (by simpa using hd))`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `not_pow_dvd_mul_of_not_pow_dvd hπ (h a (Finset.mem_insert_self _ _)) (ih fun r hr => h r (Finset.mem_insert_of_mem hr))`.
-/
theorem not_pow_sum_dvd_prod [IsDomain R] {π : R} (hπ : Prime π) {κ : Type} (s : Finset κ)
    (v : κ → ℕ) (y : κ → R) (h : ∀ r ∈ s, ¬ π ^ (v r + 1) ∣ y r) :
    ¬ π ^ (∑ r ∈ s, v r + 1) ∣ ∏ r ∈ s, y r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hd
    exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using hd))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact not_pow_dvd_mul_of_not_pow_dvd hπ (h a (Finset.mem_insert_self _ _))
      (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

/- English proof (translation)
Set `e0 : Fin (tt r) → {y : (Σ r : ↥I, Fin (tt r)) // y.1.1 = r.1}` to `fun i => ⟨⟨r, i⟩, rfl⟩`. Establish `he0 : Function.Bijective e0`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Establish `h1 : (⟨r, i⟩ : Σ r : ↥I, Fin (tt r)) = ⟨r, j⟩` using `congrArg Subtype.val hij`.

Simplify using `using h1`. Introduce and unpack `⟨⟨r', i⟩, hy⟩`. Establish `hr : r' = r` using `Subtype.ext hy`. Substitute `hr` using the available equality. Conclude with `⟨i, rfl⟩`.

Rewrite using `[← Matrix.det_submatrix_equiv_self (Equiv.ofBijective e0 he0)]`. Both sides reduce to the same expression.
-/
theorem det_sigma_reindexed_square_block {n : ℕ} (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (I : Finset ℕ)
    (tt : ↥I → ℕ) (F G : ∀ r : ↥I, Fin (tt r) → {j // b j = r.1}) (r : ↥I) :
    ((Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).toSquareBlock
          (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1) r.1).det =
      ((Φ.toSquareBlock b r.1).submatrix (F r) (G r)).det := by
  let e0 : Fin (tt r) → {y : (Σ r : ↥I, Fin (tt r)) // y.1.1 = r.1} := fun i => ⟨⟨r, i⟩, rfl⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      have h1 : (⟨r, i⟩ : Σ r : ↥I, Fin (tt r)) = ⟨r, j⟩ := congrArg Subtype.val hij
      simpa using h1
    · rintro ⟨⟨r', i⟩, hy⟩
      have hr : r' = r := Subtype.ext hy
      subst hr
      exact ⟨i, rfl⟩
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective e0 he0)]
  rfl

end PartE

/- English proof (translation)
Introduce `R _ m p t x P`. Conclude with `⟨fun h f g => dvd_det_submatrix_of_minorsDvd x P h f g, fun h f g _ _ => h f g⟩`.
-/
theorem minors_divide_all_holds : MinorsDvdAll := by
  intro R _ m p t x P
  exact ⟨fun h f g => dvd_det_submatrix_of_minorsDvd x P h f g, fun h f g _ _ => h f g⟩

/- English proof (translation)
Introduce `R _ m n p r t x G P H h f g _ _`. Conclude with `dvd_det_submatrix_mul_right x (G * P) H (dvd_det_submatrix_mul_left x G P (dvd_det_submatrix_of_minorsDvd x P h)) f g`.
-/
theorem minors_dvd_mul_holds : MinorsDvdMul := by
  intro R _ m n p r t x G P H h f g _ _
  exact dvd_det_submatrix_mul_right x (G * P) H (dvd_det_submatrix_mul_left x G P (dvd_det_submatrix_of_minorsDvd x P h)) f g

/- English proof (translation)
Introduce `R _ n t S x a G H hS`. Use `minors_dvd_mul_holds R n n n n t (x ^ S) G _ H ?_` and prove the remaining obligations. Introduce `f g hf hg`. Establish `h1 : (Matrix.diagonal (fun j => x ^ a j)).submatrix f g = Matrix.of fun i j => (x ^ a (f i)) * ((1 : Matrix (Fin n) (Fin n) R).submatrix f g) i j`. Use extensionality with `i j`.

Simplify using `[Matrix.diagonal_apply, Matrix.one_apply]`. Rewrite using `[h1, Matrix.det_mul_column (fun i => x ^ a (f i)), Finset.prod_pow_eq_pow_sum]`. Use `Dvd.dvd.mul_right (pow_dvd_pow x ?_) _` and prove the remaining obligations. Establish `h2` using `hS (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf.injective]; simp)`. Rewrite `h2` using `[Finset.sum_image (fun i _ j _ h => hf.injective h)]`. Then use the resulting hypothesis.
-/
theorem diagonal_minors_holds : DiagMinors := by
  intro R _ n t S x a G H hS
  refine minors_dvd_mul_holds R n n n n t (x ^ S) G _ H ?_
  intro f g hf hg
  have h1 : (Matrix.diagonal (fun j => x ^ a j)).submatrix f g =
      Matrix.of fun i j => (x ^ a (f i)) * ((1 : Matrix (Fin n) (Fin n) R).submatrix f g) i j := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [h1, Matrix.det_mul_column (fun i => x ^ a (f i)), Finset.prod_pow_eq_pow_sum]
  refine Dvd.dvd.mul_right (pow_dvd_pow x ?_) _
  have h2 := hS (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf.injective]; simp)
  rwa [Finset.sum_image (fun i _ j _ h => hf.injective h)] at h2

/- English proof (translation)
Introduce `R _ _ π n h c Φ b ch al ν hπ hΦ hsub hch hoth hdvd`. Generalize the expression as in `hI : Finset.univ.image b = I at hsub hoth hdvd ⊢`. Establish `hloc : ∀ r : ↥I, ∃ (t v : ℕ) (F G : Fin t → {j // b j = r.1}), t = (if r.1 ∈ ch then 1 else ν r.1) ∧ v = (if r.1 ∈ ch then al r.1 else ν r.1 * h) ∧ ¬ π ^ (v + 1) ∣ ((Φ.toSquareBlock b r.1).submatrix F G).det`. Introduce `r`. Distinguish the cases in `hr : r.1 ∈ ch`.

Take `⟨s, hs, u, hu⟩` from `hch r.1 hr`. Use `⟨1, al r.1, fun _ => ⟨s, (hs s).2 rfl⟩, fun _ => ⟨s, (hs s).2 rfl⟩, (if_pos hr).symm, (if_pos hr).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_one]`. Use `show ¬ π ^ (al r.1 + 1) ∣ Φ s s`. Rewrite using `[hu, pow_succ, mul_comm (π ^ al r.1) π, mul_dvd_mul_iff_right (pow_ne_zero _ hπ.ne_zero)]`.

Conclude with `fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd u.isUnit)`. Take `⟨⟨M', hM'⟩, hν⟩` from `hoth r.1 (Finset.mem_sdiff.2 ⟨r.2, hr⟩)`. Establish `hcard : Fintype.card (Fin (ν r.1)) ≤ Fintype.card {j // b j = r.1}`. Rewrite using `[Fintype.card_fin, Fintype.card_subtype]`. Conclude with `hν`.

Take `⟨e⟩` from `Function.Embedding.nonempty_of_card_le hcard`. Establish `hx : ¬ π ^ (Fintype.card (Fin (ν r.1)) * h + 1) ∣ π ^ (Fintype.card (Fin (ν r.1)) * h)`. Rewrite using `[pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]`. Use linear arithmetic over natural numbers and integers. Take `⟨F, G, hFG⟩` from `exists_submatrix_det_not_dvd_of_mul_eq π h _ M' e e.injective hM' hx`.

Rewrite `hFG` using `[Fintype.card_fin]`. Conclude with `⟨ν r.1, ν r.1 * h, F, G, (if_neg hr).symm, (if_neg hr).symm, hFG⟩`. Use `choose tt vv F G htt hvv hnd using hloc`. Establish `hBT : (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1) (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).BlockTriangular (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1)`. Introduce `x y hxy`.

Use `hΦ ?_` and prove the remaining obligations. Use `show b (G y.1 y.2).1 < b (F x.1 x.2).1`. Rewrite using `[(F x.1 x.2).2, (G y.1 y.2).2]`. Conclude with `hxy`. Establish `hnd' : ¬ π ^ (∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1), (if a ∈ ch then al a else ν a * h) + 1) ∣ (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1) (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).det`.

Rewrite using `[hBT.det]`. Use `not_pow_sum_dvd_prod hπ _ _ _ ?_` and prove the remaining obligations. Introduce `a ha`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 ha`. Rewrite using `[det_sigma_reindexed_square_block Φ b I tt F G x.1]`.

Establish `h3` using `hnd x.1`. Rewrite `h3` using `[hvv x.1]`. Then use the resulting hypothesis. Establish `hle : ∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1), (if a ∈ ch then al a else ν a * h) ≤ ∑ a ∈ I, (if a ∈ ch then al a else ν a * h)`. Use `Finset.sum_le_sum_of_subset ?_` and prove the remaining obligations. Introduce `a ha`.

Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `x.1.2`. Establish `hsumv : ∑ a ∈ I, (if a ∈ ch then al a else ν a * h) = ∑ r ∈ ch, al r + (∑ r ∈ I \ ch, ν r) * h`. Rewrite using `[← Finset.sum_sdiff hsub, add_comm, Finset.sum_mul]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun r hr => if_pos hr`. Conclude with `Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2`. Establish `hcardT : Fintype.card (Σ r : ↥I, Fin (tt r)) = ch.card + ∑ r ∈ I \ ch, ν r`. Rewrite using `[Fintype.card_sigma]`. Simplify using `only [Fintype.card_fin, htt]`.

Rewrite using `[Finset.sum_coe_sort I (fun r => if r ∈ ch then 1 else ν r), ← Finset.sum_sdiff hsub, add_comm]`. Use `congr 1`. Rewrite using `[Finset.card_eq_sum_ones]`. Conclude with `Finset.sum_congr rfl fun r hr => if_pos hr`. Conclude with `Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2`.

Establish `hall` using `dvd_det_submatrix_of_minorsDvd (π ^ c) Φ hdvd`. Establish `h1` using `hall (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1 ((Fintype.equivFinOfCardEq hcardT).symm i).2).1) (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1 ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)`. Establish `h2 : Φ.submatrix (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1 ((Fintype.equivFinOfCardEq hcardT).symm i).2).1) (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1 ((Fintype.equivFinOfCardEq hcardT).symm i).2).1) = (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => …` using `rfl`. Rewrite `h1` using `[h2, Matrix.det_submatrix_equiv_self]`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_le, ← hsumv]`. Conclude with `hnd' (dvd_trans (pow_dvd_pow π (Nat.succ_le_of_lt (lt_of_le_of_lt hle hc))) h1)`.
-/
theorem minor_bound_extra_holds : MinorBoundExtra := by
  intro R _ _ π n h c Φ b ch al ν hπ hΦ hsub hch hoth hdvd
  generalize hI : Finset.univ.image b = I at hsub hoth hdvd ⊢
  have hloc : ∀ r : ↥I, ∃ (t v : ℕ) (F G : Fin t → {j // b j = r.1}),
      t = (if r.1 ∈ ch then 1 else ν r.1) ∧ v = (if r.1 ∈ ch then al r.1 else ν r.1 * h) ∧
      ¬ π ^ (v + 1) ∣ ((Φ.toSquareBlock b r.1).submatrix F G).det := by
    intro r
    by_cases hr : r.1 ∈ ch
    · obtain ⟨s, hs, u, hu⟩ := hch r.1 hr
      refine ⟨1, al r.1, fun _ => ⟨s, (hs s).2 rfl⟩, fun _ => ⟨s, (hs s).2 rfl⟩,
        (if_pos hr).symm, (if_pos hr).symm, ?_⟩
      rw [Matrix.det_fin_one]
      show ¬ π ^ (al r.1 + 1) ∣ Φ s s
      rw [hu, pow_succ, mul_comm (π ^ al r.1) π,
        mul_dvd_mul_iff_right (pow_ne_zero _ hπ.ne_zero)]
      exact fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd u.isUnit)
    · obtain ⟨⟨M', hM'⟩, hν⟩ := hoth r.1 (Finset.mem_sdiff.2 ⟨r.2, hr⟩)
      have hcard : Fintype.card (Fin (ν r.1)) ≤ Fintype.card {j // b j = r.1} := by
        rw [Fintype.card_fin, Fintype.card_subtype]; exact hν
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      have hx : ¬ π ^ (Fintype.card (Fin (ν r.1)) * h + 1) ∣
          π ^ (Fintype.card (Fin (ν r.1)) * h) := by
        rw [pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]; omega
      obtain ⟨F, G, hFG⟩ := exists_submatrix_det_not_dvd_of_mul_eq π h _ M' e e.injective hM' hx
      rw [Fintype.card_fin] at hFG
      exact ⟨ν r.1, ν r.1 * h, F, G, (if_neg hr).symm, (if_neg hr).symm, hFG⟩
  choose tt vv F G htt hvv hnd using hloc
  have hBT : (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
      (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).BlockTriangular
        (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1) := by
    intro x y hxy
    refine hΦ ?_
    show b (G y.1 y.2).1 < b (F x.1 x.2).1
    rw [(F x.1 x.2).2, (G y.1 y.2).2]
    exact hxy
  have hnd' : ¬ π ^ (∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1),
      (if a ∈ ch then al a else ν a * h) + 1) ∣
      (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).det := by
    rw [hBT.det]
    refine not_pow_sum_dvd_prod hπ _ _ _ ?_
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    rw [det_sigma_reindexed_square_block Φ b I tt F G x.1]
    have h3 := hnd x.1
    rwa [hvv x.1] at h3
  have hle : ∑ a ∈ Finset.univ.image (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1),
      (if a ∈ ch then al a else ν a * h) ≤ ∑ a ∈ I, (if a ∈ ch then al a else ν a * h) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    exact x.1.2
  have hsumv : ∑ a ∈ I, (if a ∈ ch then al a else ν a * h) =
      ∑ r ∈ ch, al r + (∑ r ∈ I \ ch, ν r) * h := by
    rw [← Finset.sum_sdiff hsub, add_comm, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun r hr => if_pos hr
    · exact Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2
  have hcardT : Fintype.card (Σ r : ↥I, Fin (tt r)) = ch.card + ∑ r ∈ I \ ch, ν r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, htt]
    rw [Finset.sum_coe_sort I (fun r => if r ∈ ch then 1 else ν r), ← Finset.sum_sdiff hsub,
      add_comm]
    congr 1
    · rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun r hr => if_pos hr
    · exact Finset.sum_congr rfl fun r hr => if_neg (Finset.mem_sdiff.1 hr).2
  have hall := dvd_det_submatrix_of_minorsDvd (π ^ c) Φ hdvd
  have h1 := hall
    (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1
      ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
    (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1
      ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
  have h2 : Φ.submatrix
      (fun i => (F ((Fintype.equivFinOfCardEq hcardT).symm i).1
        ((Fintype.equivFinOfCardEq hcardT).symm i).2).1)
      (fun i => (G ((Fintype.equivFinOfCardEq hcardT).symm i).1
        ((Fintype.equivFinOfCardEq hcardT).symm i).2).1) =
      (Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).submatrix
          (Fintype.equivFinOfCardEq hcardT).symm (Fintype.equivFinOfCardEq hcardT).symm := rfl
  rw [h2, Matrix.det_submatrix_equiv_self] at h1
  by_contra hc
  rw [not_le, ← hsumv] at hc
  exact hnd' (dvd_trans (pow_dvd_pow π (Nat.succ_le_of_lt (lt_of_le_of_lt hle hc))) h1)

end PartE

section PartG

section Lin

variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)

/- English proof (translation)
Use `⟨⟨fun {n} hn => ?_⟩, Polynomial.monic_X_sub_C c⟩` and prove the remaining obligations. Rewrite `hn` using `[Polynomial.natDegree_X_sub_C]`. Take `rfl : n = 0` from `by omega`. Simplify using `using hc`.
-/
theorem X_sub_C_isDistinguished (hc : c ∈ I) :
    (Polynomial.X - Polynomial.C c : Polynomial O).IsDistinguishedAt I := by
  refine ⟨⟨fun {n} hn => ?_⟩, Polynomial.monic_X_sub_C c⟩
  rw [Polynomial.natDegree_X_sub_C] at hn
  obtain rfl : n = 0 := by omega
  simpa using hc

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coe_X_sub_C_polynomial_powerSeries : ((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧) = X - C c := by
  simp

/- English proof (translation)
Introduce `h`. Use `IsAdicComplete.le_jacobson_bot I` as an intermediate fact. Rewrite `this` using `[h, top_le_iff, Ideal.jacobson_eq_top_iff]`. Conclude with `bot_ne_top this`.
-/
theorem ideal_ne_top_alt : I ≠ ⊤ := by
  intro h
  have := IsAdicComplete.le_jacobson_bot I
  rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at this
  exact bot_ne_top this

/- English proof (translation)
Establish `: Nontrivial (O ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr (ideal_ne_top_alt I)`. Rewrite using `[coe_X_sub_C_polynomial_powerSeries, map_sub, PowerSeries.map_X, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero, sub_zero, order_X]`. Both sides reduce to the same expression.
-/
theorem order_X_sub_C_mod_eq_one (hc : c ∈ I) :
    ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map
      (Ideal.Quotient.mk I)).order.toNat) = 1 := by
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ideal_ne_top_alt I)
  rw [coe_X_sub_C_polynomial_powerSeries, map_sub, PowerSeries.map_X, PowerSeries.map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero, sub_zero, order_X]
  rfl

end Lin

/- English proof (translation)
Introduce `O _ _ I _ c hc`. Establish `H` using `(X_sub_C_isDistinguished I c hc).isWeierstrassDivisorAt'`. Prove the components needed by the constructor for the conclusion. Introduce `f`. Take `⟨hd, he⟩` from `H.isWeierstrassDivisionAt_div_mod f`.

Rewrite `hd` using `[order_X_sub_C_mod_eq_one I c hc]`. Generalize the expression as in `H.div f = qq at he`. Generalize the expression as in `H.mod f = rr at he hd`. Establish `hC : rr = Polynomial.C (rr.coeff 0)` using `Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hd))`. Use `⟨qq, rr.coeff 0, ?_⟩` and prove the remaining obligations.

Rewrite `he` using `[coe_X_sub_C_polynomial_powerSeries, hC, Polynomial.coe_C]`. Simplify using `using he`. Introduce `f₁ f₂ a₁ a₂ h`. Establish `hdeg : ∀ a : O, (Polynomial.C a : Polynomial O).degree < ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ)` using `fun a => by`. Rewrite using `[order_X_sub_C_mod_eq_one I c hc]`.

Conclude with `lt_of_le_of_lt Polynomial.degree_C_le (by simp)`. Use `H.eq_of_mul_add_eq_mul_add (q := f₁) (q' := f₂) (hdeg a₁) (hdeg a₂) (by rw [coe_X_sub_C_polynomial_powerSeries, Polynomial.coe_C, Polynomial.coe_C]; exact h)` as an intermediate fact. Conclude with `⟨this.1, Polynomial.C_injective this.2⟩`.
-/
theorem linear_division_holds : LinDivision := by
  intro O _ _ I _ c hc
  have H := (X_sub_C_isDistinguished I c hc).isWeierstrassDivisorAt'
  constructor
  · intro f
    obtain ⟨hd, he⟩ := H.isWeierstrassDivisionAt_div_mod f
    rw [order_X_sub_C_mod_eq_one I c hc] at hd
    generalize H.div f = qq at he
    generalize H.mod f = rr at he hd
    have hC : rr = Polynomial.C (rr.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hd))
    refine ⟨qq, rr.coeff 0, ?_⟩
    rw [coe_X_sub_C_polynomial_powerSeries, hC, Polynomial.coe_C] at he
    simpa using he
  · intro f₁ f₂ a₁ a₂ h
    have hdeg : ∀ a : O, (Polynomial.C a : Polynomial O).degree <
        ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map
          (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := fun a => by
      rw [order_X_sub_C_mod_eq_one I c hc]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by simp)
    have := H.eq_of_mul_add_eq_mul_add (q := f₁) (q' := f₂) (hdeg a₁) (hdeg a₂)
      (by rw [coe_X_sub_C_polynomial_powerSeries, Polynomial.coe_C, Polynomial.coe_C]; exact h)
    exact ⟨this.1, Polynomial.C_injective this.2⟩

/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Use `(linear_division_holds O I c hc).2 y 0 0 b (by rw [← hy]; simp)` as an intermediate fact. Conclude with `this.2.symm`.
-/
theorem eq_zero_of_X_sub_C_dvd_C {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
    (hc : c ∈ I) (b : O) (h : (X - C c : O⟦X⟧) ∣ C b) : b = 0 := by
  obtain ⟨y, hy⟩ := h
  have := (linear_division_holds O I c hc).2 y 0 0 b (by rw [← hy]; simp)
  exact this.2.symm

/- English proof (translation)
Introduce `O _ _ I _ c hc`. Establish `hne : (X - C c : O⟦X⟧) ≠ 0`. Introduce `h`. Use `congrArg (coeff 1) h` as an intermediate fact. Simplify using `at this`.

Use `⟨hne, ?_, ?_⟩` and prove the remaining obligations. Introduce `hu`. Establish `: (X - C c : O⟦X⟧) ∣ C 1` using `hu.dvd`. Conclude with `one_ne_zero (eq_zero_of_X_sub_C_dvd_C I c hc 1 this)`. Introduce `f g hfg`.

Take `⟨f₁, a, hf⟩` from `(linear_division_holds O I c hc).1 f`. Take `⟨g₁, b, hg⟩` from `(linear_division_holds O I c hc).1 g`. Establish `h1 : (X - C c : O⟦X⟧) ∣ C (a * b)`. Establish `h2 : C (a * b) = f * g - (X - C c) * (f₁ * g + C a * g₁)`. Rewrite using `[map_mul]`.

Use `conv_rhs => rw [hf]`. Use `conv_rhs => rw [hg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `dvd_sub hfg (dvd_mul_right _ _)`.

Break down `mul_eq_zero.mp (eq_zero_of_X_sub_C_dvd_C I c hc _ h1) with h | h` into its components or cases. Use `left`. Rewrite using `[hf, h]`. Simplify using the standard rewrite rules. Use `right`.

Rewrite using `[hg, h]`. Simplify using the standard rewrite rules.
-/
theorem linear_prime_holds : LinPrime := by
  intro O _ _ I _ c hc
  have hne : (X - C c : O⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    simp at this
  refine ⟨hne, ?_, ?_⟩
  · intro hu
    have : (X - C c : O⟦X⟧) ∣ C 1 := hu.dvd
    exact one_ne_zero (eq_zero_of_X_sub_C_dvd_C I c hc 1 this)
  · intro f g hfg
    obtain ⟨f₁, a, hf⟩ := (linear_division_holds O I c hc).1 f
    obtain ⟨g₁, b, hg⟩ := (linear_division_holds O I c hc).1 g
    have h1 : (X - C c : O⟦X⟧) ∣ C (a * b) := by
      have h2 : C (a * b) = f * g - (X - C c) * (f₁ * g + C a * g₁) := by
        rw [map_mul]
        conv_rhs => rw [hf]
        conv_rhs => rw [hg]
        ring
      rw [h2]
      exact dvd_sub hfg (dvd_mul_right _ _)
    rcases mul_eq_zero.mp (eq_zero_of_X_sub_C_dvd_C I c hc _ h1) with h | h
    · left; rw [hf, h]; simp
    · right; rw [hg, h]; simp

/- English proof (translation)
Introduce `O _ _ I _ s c S m hI hinj hdvd`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Establish `hs` using `ih (fun b hb => hI b (Finset.mem_insert_of_mem hb)) (hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)) (fun b hb => hdvd b (Finset.mem_insert_of_mem hb))`.

Take `⟨m', hm'⟩` from `hs`. Establish `hp` using `linear_prime_holds O I (c a) (hI a (Finset.mem_insert_self a s))`. Establish `hnd : ¬ (X - C (c a) : O⟦X⟧) ∣ (∏ b ∈ s, (X - C (c b))) ^ S`. Introduce `h`. Establish `h1` using `hp.dvd_of_dvd_pow h`.

Take `⟨b, hb, hb2⟩` from `(Prime.dvd_finsetProd_iff hp _).mp h1`. Establish `h3 : (X - C (c a) : O⟦X⟧) ∣ C (c a - c b)`. Establish `: (C (c a - c b) : O⟦X⟧) = (X - C (c b)) - (X - C (c a))` using `by rw [map_sub]; ring`. Rewrite using `[this]`. Conclude with `dvd_sub hb2 dvd_rfl`.

Establish `h4` using `eq_zero_of_X_sub_C_dvd_C I (c a) (hI a (Finset.mem_insert_self a s)) _ h3`. Establish `h5 : a = b` using `hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb) (sub_eq_zero.mp h4)`. Conclude with `ha (h5 ▸ hb)`. Establish `h6 : (X - C (c a) : O⟦X⟧) ^ S ∣ m'` using `hp.pow_dvd_of_dvd_mul_left S hnd (hm' ▸ hdvd a (Finset.mem_insert_self a s))`. Take `⟨m'', hm''⟩` from `h6`.

Use `⟨m'', ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha, hm', hm'', mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem roots_product_holds : RootsProduct := by
  intro O _ _ I _ s c S m hI hinj hdvd
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs := ih (fun b hb => hI b (Finset.mem_insert_of_mem hb))
      (hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx))
      (fun b hb => hdvd b (Finset.mem_insert_of_mem hb))
    obtain ⟨m', hm'⟩ := hs
    have hp := linear_prime_holds O I (c a) (hI a (Finset.mem_insert_self a s))
    have hnd : ¬ (X - C (c a) : O⟦X⟧) ∣ (∏ b ∈ s, (X - C (c b))) ^ S := by
      intro h
      have h1 := hp.dvd_of_dvd_pow h
      obtain ⟨b, hb, hb2⟩ := (Prime.dvd_finsetProd_iff hp _).mp h1
      have h3 : (X - C (c a) : O⟦X⟧) ∣ C (c a - c b) := by
        have : (C (c a - c b) : O⟦X⟧) = (X - C (c b)) - (X - C (c a)) := by rw [map_sub]; ring
        rw [this]; exact dvd_sub hb2 dvd_rfl
      have h4 := eq_zero_of_X_sub_C_dvd_C I (c a) (hI a (Finset.mem_insert_self a s)) _ h3
      have h5 : a = b := hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
        (sub_eq_zero.mp h4)
      exact ha (h5 ▸ hb)
    have h6 : (X - C (c a) : O⟦X⟧) ^ S ∣ m' :=
      hp.pow_dvd_of_dvd_mul_left S hnd (hm' ▸ hdvd a (Finset.mem_insert_self a s))
    obtain ⟨m'', hm''⟩ := h6
    refine ⟨m'', ?_⟩
    rw [Finset.prod_insert ha, hm', hm'', mul_pow]; ring

/- English proof (translation)
Introduce `l _ O _ _ _ I _ ζ hl hζ hI S m hdvd`. Establish `h1` using `roots_product_holds O I (Finset.Ioo 0 l) (fun b => ζ ^ b - 1) S (inc l O m) (fun b _ => by`. Take `⟨y, hy⟩` from `sub_dvd_pow_sub_pow ζ 1 b`. Rewrite `hy` using `[one_pow]`. Rewrite using `[hy]`.

Conclude with `I.mul_mem_right _ hI)`. Use the proof step `(by`. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_Ioo, Set.mem_Ioo] at ha hb`. Conclude with `hζ.pow_inj ha.2 hb.2 (by simpa using hab))`.

Use `hdvd`. Rewrite `h1` using `[← hr l O ζ hζ]`. Take `⟨y, hy⟩` from `h1`. Conclude with `h4 l O hl S m y hy`.
-/
theorem rootsDescent_of_roots_and_fourth_relation (hr : QRoots) (h4 : R4) : RootsDescent := by
  intro l _ O _ _ _ I _ ζ hl hζ hI S m hdvd
  have h1 := roots_product_holds O I (Finset.Ioo 0 l) (fun b => ζ ^ b - 1) S (inc l O m)
    (fun b _ => by
      obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow ζ 1 b
      rw [one_pow] at hy
      rw [hy]; exact I.mul_mem_right _ hI)
    (by
      intro a ha b hb hab
      simp only [Finset.coe_Ioo, Set.mem_Ioo] at ha hb
      exact hζ.pow_inj ha.2 hb.2 (by simpa using hab))
    hdvd
  rw [← hr l O ζ hζ] at h1
  obtain ⟨y, hy⟩ := h1
  exact h4 l O hl S m y hy

end PartG

section PartH

/- English proof (translation)
Introduce `l _ O _ _ hl n h P Q hPQ`. Establish `hs : HasSubst (pi0 l O)` using `HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)`. Take `⟨g, hg, -⟩` from `h3 l O hl`. Establish `hl1 : 0 < l - 1` using `by have := (Fact.out : l.Prime).two_le; omega`. Set `Φ : O⟦X⟧ →ₐ[O] O⟦X⟧` to `substAlgHom hs`.

Establish `hinc : ∀ a, inc l O a = Φ a` using `fun a => (congrFun (coe_substAlgHom hs) a).symm`. Establish `hΦX : Φ X = pi0 l O` using `by rw [← hinc]; exact subst_X hs`. Establish `hΦq : Φ ((X - C (l : O)) ^ h) = q0 l O ^ h`. Establish `hC : (C (l : O) : O⟦X⟧) = ((l : ℕ) : O⟦X⟧)` using `by simp`. Rewrite using `[map_pow, map_sub, hΦX, hC, map_natCast, q0, hC]`.

Use `choose G hG using fun a b => (hb l O hl ((g : O⟦X⟧) ^ h * Q a b)).exists`. Establish `key : ∀ a b, (fun j : Fin (l - 1) => ∑ c, P a c * G c b j) = (fun j : Fin (l - 1) => if j = ⟨0, hl1⟩ then (X - C (l : O)) ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b else 0)`. Introduce `a b`. Apply `(hb l O hl (q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b)).unique` to reduce the goal to its premises. Establish `e1 : q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b = (g : O⟦X⟧) ^ h * (P.map (inc l O) * Q) a b`.

Rewrite using `[hPQ, Matrix.smul_apply, smul_eq_mul, hg, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, Matrix.mul_apply, Finset.mul_sum]`. Simplify using `only [Matrix.map_apply]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← hG c b]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ j, inc l O (∑ c, P a c * G c b j) * X ^ (j : ℕ) := by`. Simplify using `only [hinc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring`. Rewrite using `[Finset.sum_eq_single (⟨0, hl1⟩ : Fin (l - 1))]`. Rewrite using `[if_pos rfl, hinc, map_mul, hΦq]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hab]`. Introduce `j _ hj`. Rewrite using `[if_neg hj, hinc, map_zero, zero_mul]`.

Introduce `hx`. Conclude with `absurd (Finset.mem_univ _) hx`. Use `⟨Matrix.of fun a b => G a b ⟨0, hl1⟩, ?_⟩` and prove the remaining obligations. Use `ext1 a b`. Use `congrFun (key a b) ⟨0, hl1⟩` as an intermediate fact.

Simplify using `only [if_pos] at this`. Rewrite using `[Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]`. Simplify using `using this`.
-/
theorem height_descent_of_r3_r2 (h3 : UnitFactorQ) (hb : PowerSeriesFreeBasis) : HeightDescent := by
  intro l _ O _ _ hl n h P Q hPQ
  have hs : HasSubst (pi0 l O) := HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)
  obtain ⟨g, hg, -⟩ := h3 l O hl
  have hl1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  let Φ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hs
  have hinc : ∀ a, inc l O a = Φ a := fun a => (congrFun (coe_substAlgHom hs) a).symm
  have hΦX : Φ X = pi0 l O := by rw [← hinc]; exact subst_X hs
  have hΦq : Φ ((X - C (l : O)) ^ h) = q0 l O ^ h := by
    have hC : (C (l : O) : O⟦X⟧) = ((l : ℕ) : O⟦X⟧) := by simp
    rw [map_pow, map_sub, hΦX, hC, map_natCast, q0, hC]
  choose G hG using fun a b => (hb l O hl ((g : O⟦X⟧) ^ h * Q a b)).exists
  have key : ∀ a b, (fun j : Fin (l - 1) => ∑ c, P a c * G c b j) =
      (fun j : Fin (l - 1) => if j = ⟨0, hl1⟩ then
        (X - C (l : O)) ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b else 0) := by
    intro a b
    apply (hb l O hl (q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b)).unique
    · have e1 : q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b =
          (g : O⟦X⟧) ^ h * (P.map (inc l O) * Q) a b := by
        rw [hPQ, Matrix.smul_apply, smul_eq_mul, hg, mul_pow]; ring
      rw [e1, Matrix.mul_apply, Finset.mul_sum]
      simp only [Matrix.map_apply]
      calc ∑ c, (g : O⟦X⟧) ^ h * (inc l O (P a c) * Q c b)
          = ∑ c, inc l O (P a c) * ∑ j, inc l O (G c b j) * X ^ (j : ℕ) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← hG c b]; ring
        _ = ∑ j, inc l O (∑ c, P a c * G c b j) * X ^ (j : ℕ) := by
            simp only [hinc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring
    · rw [Finset.sum_eq_single (⟨0, hl1⟩ : Fin (l - 1))]
      · rw [if_pos rfl, hinc, map_mul, hΦq]
        by_cases hab : a = b
        · subst hab; simp
        · simp [Matrix.one_apply_ne hab]
      · intro j _ hj
        rw [if_neg hj, hinc, map_zero, zero_mul]
      · intro hx; exact absurd (Finset.mem_univ _) hx
  refine ⟨Matrix.of fun a b => G a b ⟨0, hl1⟩, ?_⟩
  ext1 a b
  have := congrFun (key a b) ⟨0, hl1⟩
  simp only [if_pos] at this
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using this

end PartH

section PartC2

section HW

variable {k : Type} [CommRing k] {𝒰 : Type} [Ring 𝒰] [Algebra k 𝒰] {V : Type} [AddCommGroup V]
  [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `f c _`. Simplify using the standard rewrite rules.

Consider the case `succ N ih`. Introduce `f c h`. Rewrite using `[List.ofFn_succ, List.prod_cons, mul_smul, ih (fun j => f j.succ) (fun j => c j.succ) (fun j => h j.succ), Fin.prod_univ_succ]`. Rewrite using `[← algebraMap_smul 𝒰 (∏ j : Fin N, c j.succ) v, ← mul_smul, ← Algebra.commutes, mul_smul, h 0, algebraMap_smul, smul_smul, mul_comm]`.
-/
theorem orderedProd_smul_of_scalar_actions (v : V) : ∀ (N : ℕ) (f : Fin N → 𝒰) (c : Fin N → k),
    (∀ j, f j • v = c j • v) → (List.ofFn f).prod • v = (∏ j, c j) • v := by
  intro N
  induction N with
  | zero =>
    intro f c _
    simp
  | succ N ih =>
    intro f c h
    rw [List.ofFn_succ, List.prod_cons, mul_smul,
      ih (fun j => f j.succ) (fun j => c j.succ) (fun j => h j.succ), Fin.prod_univ_succ]
    rw [← algebraMap_smul 𝒰 (∏ j : Fin N, c j.succ) v, ← mul_smul, ← Algebra.commutes, mul_smul, h 0,
      algebraMap_smul, smul_smul, mul_comm]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `f c j0`. Conclude with `j0.elim0`.

Consider the case `succ N ih`. Introduce `f c j0 h0 hlater`. Rewrite using `[List.ofFn_succ, List.prod_cons, mul_smul]`. Break down `Fin.eq_zero_or_eq_succ j0 with rfl | ⟨j', rfl⟩` into its components or cases. Rewrite using `[orderedProd_smul_of_scalar_actions v N (fun j => f j.succ) (fun j => c j.succ) (fun j => hlater j.succ (Fin.succ_pos j))]`.

Rewrite using `[← algebraMap_smul 𝒰 _ v, ← mul_smul, ← Algebra.commutes, mul_smul, h0, smul_zero]`. Rewrite using `[ih (fun j => f j.succ) (fun j => c j.succ) j' h0 (fun j hj => hlater j.succ (Fin.succ_lt_succ_iff.mpr hj)), smul_zero]`.
-/
theorem orderedProd_smul_eq_zero (v : V) : ∀ (N : ℕ) (f : Fin N → 𝒰) (c : Fin N → k) (j0 : Fin N),
    f j0 • v = 0 → (∀ j, j0 < j → f j • v = c j • v) → (List.ofFn f).prod • v = 0 := by
  intro N
  induction N with
  | zero =>
    intro f c j0
    exact j0.elim0
  | succ N ih =>
    intro f c j0 h0 hlater
    rw [List.ofFn_succ, List.prod_cons, mul_smul]
    rcases Fin.eq_zero_or_eq_succ j0 with rfl | ⟨j', rfl⟩
    · rw [orderedProd_smul_of_scalar_actions v N (fun j => f j.succ) (fun j => c j.succ)
        (fun j => hlater j.succ (Fin.succ_pos j))]
      rw [← algebraMap_smul 𝒰 _ v, ← mul_smul, ← Algebra.commutes, mul_smul, h0, smul_zero]
    · rw [ih (fun j => f j.succ) (fun j => c j.succ) j' h0
        (fun j hj => hlater j.succ (Fin.succ_lt_succ_iff.mpr hj)), smul_zero]

end HW

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j1, hj1⟩ : ∃ j, σ j ≠ j := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hσ (Equiv.ext fun x => by simpa using h x)`. Use `set S := Finset.univ.filter fun j => σ j ≠ j with hSdef`.

Establish `hS : S.Nonempty` using `⟨j1, by simp [S, hj1]⟩`. Use `⟨S.max' hS, ?_, ?_⟩` and prove the remaining obligations. Establish `hm : σ (S.max' hS) ≠ S.max' hS` using `(Finset.mem_filter.mp (S.max'_mem hS)).2`. Break down `lt_or_gt_of_ne hm with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Establish `hfix : σ (σ (S.max' hS)) = σ (S.max' hS)`. Assume the negation of the conclusion as `hc`. Establish `: σ (S.max' hS) ∈ S` using `by simp [S, hc]`. Conclude with `absurd (S.le_max' _ this) (not_le.mpr h)`.

Conclude with `hm (σ.injective hfix)`. Introduce `j hj`. Assume the negation of the conclusion as `hc`. Establish `: j ∈ S` using `by simp [S, hc]`. Conclude with `absurd (S.le_max' _ this) (not_le.mpr hj)`.
-/
theorem exists_largest_moved_point {N : ℕ} (σ : Equiv.Perm (Fin N)) (hσ : σ ≠ 1) :
    ∃ j0, σ j0 < j0 ∧ ∀ j, j0 < j → σ j = j := by
  classical
  obtain ⟨j1, hj1⟩ : ∃ j, σ j ≠ j := by
    by_contra h
    push_neg at h
    exact hσ (Equiv.ext fun x => by simpa using h x)
  set S := Finset.univ.filter fun j => σ j ≠ j with hSdef
  have hS : S.Nonempty := ⟨j1, by simp [S, hj1]⟩
  refine ⟨S.max' hS, ?_, ?_⟩
  · have hm : σ (S.max' hS) ≠ S.max' hS := (Finset.mem_filter.mp (S.max'_mem hS)).2
    rcases lt_or_gt_of_ne hm with h | h
    · exact h
    · exfalso
      have hfix : σ (σ (S.max' hS)) = σ (S.max' hS) := by
        by_contra hc
        have : σ (S.max' hS) ∈ S := by simp [S, hc]
        exact absurd (S.le_max' _ this) (not_le.mpr h)
      exact hm (σ.injective hfix)
  · intro j hj
    by_contra hc
    have : j ∈ S := by simp [S, hc]
    exact absurd (S.le_max' _ this) (not_le.mpr hj)

/- English proof (translation)
Introduce `k _ 𝒰 _ _ V _ _ _ _ N E u lam v hup hdiag`. Establish `hscal : ∀ j : Fin N, capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) j j • v = (u + lam j - ((j : ℕ) : k)) • v`. Introduce `j`. Establish `hc : algebraMap k 𝒰 u - ((j : ℕ) : 𝒰) = algebraMap k 𝒰 (u - ((j : ℕ) : k))`. Rewrite using `[map_sub, map_natCast]`.

Rewrite using `[capA, if_pos rfl, hc, add_smul, hdiag, algebraMap_smul, ← add_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Unfold `capelli`. Rewrite using `[Finset.sum_smul, Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]`.

Rewrite using `[Equiv.Perm.sign_one, Units.val_one, one_smul]`. Conclude with `orderedProd_smul_of_scalar_actions v N _ _ (fun j => by simpa using hscal j)`. Introduce `σ _ hσ`. Take `⟨j0, hlt, hfix⟩` from `exists_largest_moved_point σ hσ`. Rewrite using `[smul_assoc, orderedProd_smul_eq_zero v N _ (fun j => u + lam j - ((j : ℕ) : k)) j0 ?_ ?_, smul_zero]`.

Use `show capA E (algebraMap k 𝒰 u - ((j0 : ℕ) : 𝒰)) (σ j0) j0 • v = 0`. Rewrite using `[capA, if_neg (ne_of_lt hlt), add_zero]`. Conclude with `hup _ _ hlt`. Introduce `j hj show capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) (σ j) j • v = _`. Rewrite using `[hfix j hj]`.

Conclude with `hscal j`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem c2_holds_alt : C2 := by
  intro k _ 𝒰 _ _ V _ _ _ _ N E u lam v hup hdiag
  have hscal : ∀ j : Fin N, capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) j j • v =
      (u + lam j - ((j : ℕ) : k)) • v := by
    intro j
    have hc : algebraMap k 𝒰 u - ((j : ℕ) : 𝒰) = algebraMap k 𝒰 (u - ((j : ℕ) : k)) := by
      rw [map_sub, map_natCast]
    rw [capA, if_pos rfl, hc, add_smul, hdiag, algebraMap_smul, ← add_smul]
    congr 1
    ring
  unfold capelli
  rw [Finset.sum_smul, Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · rw [Equiv.Perm.sign_one, Units.val_one, one_smul]
    exact orderedProd_smul_of_scalar_actions v N _ _ (fun j => by simpa using hscal j)
  · intro σ _ hσ
    obtain ⟨j0, hlt, hfix⟩ := exists_largest_moved_point σ hσ
    rw [smul_assoc, orderedProd_smul_eq_zero v N _ (fun j => u + lam j - ((j : ℕ) : k)) j0 ?_ ?_, smul_zero]
    · show capA E (algebraMap k 𝒰 u - ((j0 : ℕ) : 𝒰)) (σ j0) j0 • v = 0
      rw [capA, if_neg (ne_of_lt hlt), add_zero]
      exact hup _ _ hlt
    · intro j hj
      show capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) (σ j) j • v = _
      rw [hfix j hj]
      exact hscal j
  · intro h
    exact absurd (Finset.mem_univ _) h

attribute [local instance 100] LieRing.ofAssociativeRing

end PartC2

/- English proof (translation)
The claim follows from `r2_basis_of_r1 r1_holds general_basis_holds`.
-/
theorem r2_basis_holds : PowerSeriesFreeBasis := r2_basis_of_r1 r1_holds general_basis_holds

/- English proof (translation)
The claim follows from `fixed_relation_of_mu_and_inverse mu_facts_hold r1_holds r2_inverse_holds`.
-/
theorem fixed_relation_holds : RootsOfUnityInvariants := fixed_relation_of_mu_and_inverse mu_facts_hold r1_holds r2_inverse_holds

/- English proof (translation)
The claim follows from `r3_unit_of_laws action_laws_holds mu_facts_hold q_multiplicative_holds`.
-/
theorem r3_unit_holds : UnitFactorQ := r3_unit_of_laws action_laws_holds mu_facts_hold q_multiplicative_holds

/- English proof (translation)
The claim follows from `r3_divisibility_of_unit_roots r3_unit_holds q_roots_holds`.
-/
theorem r3_divisibility_holds : RootOfUnityRemainder := r3_divisibility_of_unit_roots r3_unit_holds q_roots_holds

/- English proof (translation)
The claim follows from `fourth_relation_of_unit_and_basis r3_unit_holds r2_basis_holds`.
-/
theorem fourth_relation_holds : R4 := fourth_relation_of_unit_and_basis r3_unit_holds r2_basis_holds

/- English proof (translation)
The claim follows from `sixth_relation_of_action_and_mu_laws action_laws_holds mu_facts_hold q_multiplicative_holds r2_inverse_holds fixed_relation_holds fourth_relation_holds`.
-/
theorem r6_holds : R6 := sixth_relation_of_action_and_mu_laws action_laws_holds mu_facts_hold q_multiplicative_holds r2_inverse_holds fixed_relation_holds fourth_relation_holds

/- English proof (translation)
The claim follows from `rootsDescent_of_roots_and_fourth_relation q_roots_holds fourth_relation_holds`.
-/
theorem roots_descent_holds : RootsDescent := rootsDescent_of_roots_and_fourth_relation q_roots_holds fourth_relation_holds

/- English proof (translation)
The claim follows from `height_descent_of_r3_r2 r3_unit_holds r2_basis_holds`.
-/
theorem height_descent_holds : HeightDescent := height_descent_of_r3_r2 r3_unit_holds r2_basis_holds

end Formalism.CohomologicalDescent.HeightDescentMinors
