import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open LaurentPolynomial

def lpScaleF (c : ℚˣ) : Multiplicative ℤ →* LaurentPolynomial ℚ where
  toFun m := ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, zpow_add, Units.val_mul, T_add, smul_mul_smul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma lpScaleF_apply (c : ℚˣ) (m : Multiplicative ℤ) :
    lpScaleF c m = ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd := rfl

def lpScale (c : ℚˣ) : LaurentPolynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ :=
  AddMonoidAlgebra.lift ℚ (LaurentPolynomial ℚ) ℤ (lpScaleF c)

/- English proof (translation)
Proceed by induction on `f using LaurentPolynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq, mul_add]`. Consider the case `C_mul_T n a`. Establish `h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n`.

Unfold `lpScale T`. Rewrite using `[AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]`. Both sides reduce to the same expression. Establish `h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n`. Rewrite using `[C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`.

Rewrite using `[h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h : n = m`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[h]`.
-/
lemma lpScale_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScale c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T n a =>
    have h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n := by
      unfold lpScale T
      rw [AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]
      rfl
    have h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n := by
      rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp [h]

def lpScaleE (c : ℚˣ) : LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ :=
  AlgEquiv.ofAlgHom (lpScale c) (lpScale c⁻¹)
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [inv_mul_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])

/- English proof (translation)
Use `show (lpScale c f).coeff m = _`. Rewrite using `[lpScale_coeff]`.
-/
lemma lpScaleE_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScaleE c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  show (lpScale c f).coeff m = _
  rw [lpScale_coeff]

def lpScaleHom : ℚˣ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) where
  toFun := lpScaleE
  map_one' := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by simp [lpScaleE_coeff]
  map_mul' c d := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by
    simp [lpScaleE_coeff, AlgEquiv.mul_apply, mul_zpow, mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma lpScaleHom_apply (c : ℚˣ) : lpScaleHom c = lpScaleE c := rfl

def lpTwo : ℚˣ := Units.mk0 2 (by norm_num)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma lpTwo_val : (lpTwo : ℚ) = 2 := rfl

/- English proof (translation)
Rewrite using `[Units.val_zpow_eq_zpow_val, lpTwo_val]`.
-/
@[simp] lemma lpTwo_zpow (m : ℤ) : ((lpTwo ^ m : ℚˣ) : ℚ) = (2 : ℚ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, lpTwo_val]

/- English proof (translation)
Use `LaurentPolynomial.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[← C_eq_algebraMap, C_apply]`. Distinguish the cases in `ha : a = 0`. Rewrite using `[if_pos ha, ha]`. Rewrite using `[if_neg ha]`.

Establish `h'` using `congrArg (fun g : LaurentPolynomial ℚ => g.coeff a) h`. Simplify using `only [lpScaleE_coeff, lpTwo_zpow] at h'`. Establish `h2 : (2 : ℚ) ^ a ≠ 1` using `fun h1 => ha ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1)`. Establish `h3 : ((2 : ℚ) ^ a - 1) * f.coeff a = 0` using `by rw [sub_mul, h', one_mul, sub_self]`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp h4) h2`. Conclude with `h4.symm`.
-/
lemma lpTwo_fix (f : LaurentPolynomial ℚ) (h : lpScaleE lpTwo f = f) :
    algebraMap ℚ (LaurentPolynomial ℚ) (f.coeff 0) = f := by
  refine LaurentPolynomial.ext fun a => ?_
  rw [← C_eq_algebraMap, C_apply]
  by_cases ha : a = 0
  · rw [if_pos ha, ha]
  · rw [if_neg ha]
    have h' := congrArg (fun g : LaurentPolynomial ℚ => g.coeff a) h
    simp only [lpScaleE_coeff, lpTwo_zpow] at h'
    have h2 : (2 : ℚ) ^ a ≠ 1 := fun h1 => ha ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1)
    have h3 : ((2 : ℚ) ^ a - 1) * f.coeff a = 0 := by rw [sub_mul, h', one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) h2
    · exact h4.symm

def lpFil (a : ℤ) : Submodule ℚ (LaurentPolynomial ℚ) where
  carrier := {f | ∀ m < a, f.coeff m = 0}
  add_mem' {x y} hx hy m hm := by simp [AddMonoidAlgebra.coeff_add, hx m hm, hy m hm]
  zero_mem' m _ := by simp
  smul_mem' c x hx m hm := by simp [hx m hm]

/- English proof (translation)
Introduce `m hm`. Rewrite using `[AddMonoidAlgebra.coeff_mul]`. Simplify using `only [Finsupp.sum]`. Use `Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce `hij`. Establish `hi' : ¬ i < a` using `fun h => (Finsupp.mem_support_iff.mp hi) (hx i h)`. Establish `hj' : ¬ j < b` using `fun h => (Finsupp.mem_support_iff.mp hj) (hy j h)`. Use linear arithmetic over natural numbers and integers.
-/
lemma lpFil_mul (a b : ℤ) (x y : LaurentPolynomial ℚ) (hx : x ∈ lpFil a) (hy : y ∈ lpFil b) :
    x * y ∈ lpFil (a + b) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg]
  intro hij
  have hi' : ¬ i < a := fun h => (Finsupp.mem_support_iff.mp hi) (hx i h)
  have hj' : ¬ j < b := fun h => (Finsupp.mem_support_iff.mp hj) (hy j h)
  omega

/- English proof (translation)
Set `χ : Multiplicative ℤ →* ℚˣ` to `zpowersHom ℚˣ lpTwo`. Set `act : Multiplicative ℤ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ)` to `lpScaleHom.comp χ`. Establish `hact : ∀ g (f : LaurentPolynomial ℚ) m, (act g f).coeff m = ((χ g ^ m : ℚˣ) : ℚ) * f.coeff m`. Introduce `g f m`. Conclude with `lpScaleE_coeff (χ g) f m`.

Establish `hone : act (Multiplicative.ofAdd 1) = lpScaleE lpTwo` using `by show lpScaleE (χ (Multiplicative.ofAdd 1)) = lpScaleE lpTwo`. Simplify using `[χ]`. Establish `hfix : ∀ f : LaurentPolynomial ℚ, (∀ g, act g f = f) → ∃ c : ℚ, algebraMap ℚ _ c = f`. Introduce `f hf`. Use `⟨f.coeff 0, lpTwo_fix f ?_⟩` and prove the remaining obligations.

Use `hf (Multiplicative.ofAdd 1)` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis. Conclude with `⟨{ p := 2 hp := Nat.prime_two finK₀ := inferInstance finK := inferInstance σ := AlgHom.id ℚ ℚ σ_bij := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩ actB := act invB := hfix φ := (lpScaleE lpTwo).toAlgHom φ_inj := (lpScaleE lpTwo).injective φ_K₀ := fun c => (lpScaleE lpTwo).toAlgHom.commut …`. Express the relevant statement in the definitionally equal form `(lpScaleE lpTwo (act g b)).coeff m = (act g (lpScaleE lpTwo b)).coeff m`. Rewrite using `[lpScaleE_coeff, hact, hact, lpScaleE_coeff]`.

Expand and normalize the polynomial expressions, which then agree. Use `actdR := act`. Use `invdR := hfix`. Use `ι := AlgHom.id ℚ _`. Use `ι_inj := fun _ _ h => h`.

Use `ι_comm := fun _ _ => rfl`. Use `Fil := lpFil`. Use `Fil_anti := fun a f hf m hm => hf m (by omega)`. Use `one_mem := fun m hm => by rw [← T_zero, T_apply, if_neg (by omega)]`. Use `Fil_mul := lpFil_mul`.

Use `Fil_exh := fun x => by`. Use `⟨-(∑ i ∈ x.coeff.support, |i|), fun m hm => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hm' : m ∈ x.coeff.support` using `Finsupp.mem_support_iff.mpr hne`. Establish `h1` using `Finset.single_le_sum (f := fun i : ℤ => |i|) (fun i _ => abs_nonneg i) hm'`.

Establish `h2` using `neg_abs_le m`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Fil_sep := fun x hx => LaurentPolynomial.ext fun m => by`. Rewrite using `[hx (m + 1) m (by omega)]`. Both sides reduce to the same expression.

Use `Fil_G := fun g a x hx m hm => by rw [hact, hx m hm, mul_zero]`. Use `χ := χ`. Use `t := T 1`. Use `t_unit := isUnit_T 1`. Use `t_act := fun g => LaurentPolynomial.ext fun m => by`.

Rewrite using `[hact, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul]`. Distinguish the cases in `h : (1 : ℤ) = m`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Use `t_φ := LaurentPolynomial.ext fun m => by`. Express the relevant statement in the definitionally equal form `(lpScaleE lpTwo (T 1)).coeff m = _`. Rewrite using `[lpScaleE_coeff, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, lpTwo_zpow]`. Distinguish the cases in `h : (1 : ℤ) = m`. Substitute `h` using the available equality.

Evaluate the numerical expressions. Simplify using `[h]`. Use `mem_filtration_one := fun m hm => by rw [AlgHom.id_apply, T_apply, if_neg (by omega)]`. Use `not_mem_filtration_two := fun h => by`. Establish `h1` using `h 1 (by norm_num)`.

Rewrite `h1` using `[AlgHom.id_apply, T_apply, if_pos rfl]`. Conclude with `one_ne_zero h1`. Use `fund := fun b hb _ => ⟨b.coeff 0, lpTwo_fix b hb⟩ }⟩`.
-/
theorem existsPeriodRingData_holds : ExPD := by
  let χ : Multiplicative ℤ →* ℚˣ := zpowersHom ℚˣ lpTwo
  let act : Multiplicative ℤ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) := lpScaleHom.comp χ
  have hact : ∀ g (f : LaurentPolynomial ℚ) m, (act g f).coeff m = ((χ g ^ m : ℚˣ) : ℚ) * f.coeff m := by
    intro g f m
    exact lpScaleE_coeff (χ g) f m
  have hone : act (Multiplicative.ofAdd 1) = lpScaleE lpTwo := by
    show lpScaleE (χ (Multiplicative.ofAdd 1)) = lpScaleE lpTwo
    simp [χ]
  have hfix : ∀ f : LaurentPolynomial ℚ, (∀ g, act g f = f) → ∃ c : ℚ, algebraMap ℚ _ c = f := by
    intro f hf
    refine ⟨f.coeff 0, lpTwo_fix f ?_⟩
    have := hf (Multiplicative.ofAdd 1)
    rwa [hone] at this
  exact ⟨{
    p := 2
    hp := Nat.prime_two
    finK₀ := inferInstance
    finK := inferInstance
    σ := AlgHom.id ℚ ℚ
    σ_bij := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
    actB := act
    invB := hfix
    φ := (lpScaleE lpTwo).toAlgHom
    φ_inj := (lpScaleE lpTwo).injective
    φ_K₀ := fun c => (lpScaleE lpTwo).toAlgHom.commutes c
    φ_comm := fun g b => LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (act g b)).coeff m = (act g (lpScaleE lpTwo b)).coeff m
      rw [lpScaleE_coeff, hact, hact, lpScaleE_coeff]
      ring
    actdR := act
    invdR := hfix
    ι := AlgHom.id ℚ _
    ι_inj := fun _ _ h => h
    ι_comm := fun _ _ => rfl
    Fil := lpFil
    Fil_anti := fun a f hf m hm => hf m (by omega)
    one_mem := fun m hm => by rw [← T_zero, T_apply, if_neg (by omega)]
    Fil_mul := lpFil_mul
    Fil_exh := fun x => by
      refine ⟨-(∑ i ∈ x.coeff.support, |i|), fun m hm => ?_⟩
      by_contra hne
      have hm' : m ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hne
      have h1 := Finset.single_le_sum (f := fun i : ℤ => |i|) (fun i _ => abs_nonneg i) hm'
      have h2 := neg_abs_le m
      linarith
    Fil_sep := fun x hx => LaurentPolynomial.ext fun m => by
      rw [hx (m + 1) m (by omega)]
      rfl
    Fil_G := fun g a x hx m hm => by rw [hact, hx m hm, mul_zero]
    χ := χ
    t := T 1
    t_unit := isUnit_T 1
    t_act := fun g => LaurentPolynomial.ext fun m => by
      rw [hact, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul]
      by_cases h : (1 : ℤ) = m
      · subst h
        simp
      · simp [h]
    t_φ := LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (T 1)).coeff m = _
      rw [lpScaleE_coeff, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, lpTwo_zpow]
      by_cases h : (1 : ℤ) = m
      · subst h
        norm_num
      · simp [h]
    mem_filtration_one := fun m hm => by rw [AlgHom.id_apply, T_apply, if_neg (by omega)]
    not_mem_filtration_two := fun h => by
      have h1 := h 1 (by norm_num)
      rw [AlgHom.id_apply, T_apply, if_pos rfl] at h1
      exact one_ne_zero h1
    fund := fun b hb _ => ⟨b.coeff 0, lpTwo_fix b hb⟩ }⟩

end Formalism.WeaklyAdmissibleFiltrations
