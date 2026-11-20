import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

abbrev cf (T : GoodSet K G) (s : T.S) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)

def phiS (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G where
  toFun X := ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x
  map_add' X Y := by
    simp only [mul_add, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring_nf

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma phiS_apply (T : GoodSet K G) (s : T.S) (X : Module.End K (T.W s)) :
    phiS T s X = ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x :=
  rfl

/- English proof (translation)
Simplify using `only [phiS_apply, mul_one, eS]`.
-/
lemma phiS_one (T : GoodSet K G) (s : T.S) : phiS T s 1 = eS T s := by
  simp only [phiS_apply, mul_one, eS]

/- English proof (translation)
Rewrite using `[eS, phiS_apply, Finset.mul_sum]`. Repeatedly rewrite using `[mul_smul_comm, ← map_mul]`. Use `Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => ?_)` and prove the remaining obligations. Establish `h : (y * x)⁻¹ * y = x⁻¹` using `by group`. Simplify using `only [Equiv.coe_mulLeft, h, cf]`.
-/
lemma of_mul_eS (T : GoodSet K G) (s : T.S) (y : G) :
    MonoidAlgebra.of K G y * eS T s = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.mul_sum]
  simp_rw [mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => ?_)
  have h : (y * x)⁻¹ * y = x⁻¹ := by group
  simp only [Equiv.coe_mulLeft, h, cf]

/- English proof (translation)
Rewrite using `[eS, phiS_apply, Finset.sum_mul]`. Repeatedly rewrite using `[smul_mul_assoc, ← map_mul]`. Use `Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => ?_)` and prove the remaining obligations. Establish `h : LinearMap.trace K (T.W s) (T.tau s ((x * y)⁻¹ * y)) = LinearMap.trace K (T.W s) (T.tau s x⁻¹)`. Rewrite using `[show (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y by group, (T.tau s).map_mul, (T.tau s).map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← (T.tau s).map_mul, mul_inv_cancel, (T.tau s).map_one, one_mul]`.

Simplify using `only [Equiv.coe_mulRight, h, cf]`.
-/
lemma eS_mul_of (T : GoodSet K G) (s : T.S) (y : G) :
    eS T s * MonoidAlgebra.of K G y = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.sum_mul]
  simp_rw [smul_mul_assoc, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => ?_)
  have h : LinearMap.trace K (T.W s) (T.tau s ((x * y)⁻¹ * y)) =
      LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
    rw [show (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y by group, (T.tau s).map_mul, (T.tau s).map_mul,
      LinearMap.trace_mul_comm, ← mul_assoc, ← (T.tau s).map_mul, mul_inv_cancel, (T.tau s).map_one, one_mul]
  simp only [Equiv.coe_mulRight, h, cf]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of y => rw [of_mul_eS, Representation.asAlgebraHom_of]`. Consider the case `add x y hx hy => rw [add_mul, hx, hy, map_add, map_add]`. Consider the case `smul r x hx => rw [smul_mul_assoc, hx, map_smul, map_smul]`.
-/
lemma mul_eS (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    a * eS T s = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [of_mul_eS, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, map_add]
  | smul r x hx => rw [smul_mul_assoc, hx, map_smul, map_smul]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of y => rw [eS_mul_of, Representation.asAlgebraHom_of]`. Consider the case `add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]`. Consider the case `smul r x hx => rw [mul_smul_comm, hx, map_smul, map_smul]`.
-/
lemma eS_mul (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [eS_mul_of, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]
  | smul r x hx => rw [mul_smul_comm, hx, map_smul, map_smul]

/- English proof (translation)
Rewrite using `[mul_eS, eS_mul]`.
-/
lemma eS_comm (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) : a * eS T s = eS T s * a := by
  rw [mul_eS, eS_mul]

/- English proof (translation)
Establish `hall : ∀ a : MonoidAlgebra K G, Z * (T.tau s).asAlgebraHom a = (T.tau s).asAlgebraHom a * Z`. Introduce `a`. Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of y => rw [Representation.asAlgebraHom_of, h]`. Consider the case `add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]`.

Consider the case `smul r x hx => rw [map_smul, mul_smul_comm, smul_mul_assoc, hx]`. Establish `hc : Z ∈ Set.center (Module.End K (T.W s))`. Rewrite using `[Semigroup.mem_center_iff]`. Introduce `Y`. Take `⟨a, rfl⟩` from `T.irr s Y`.

Conclude with `(hall a).symm`. Take `⟨α, hα, hZ⟩` from `Module.End.mem_center_iff.mp hc`. Use `⟨α, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hZ]`.

Simplify using the standard rewrite rules.
-/
lemma scalar_of_comm (T : GoodSet K G) (s : T.S) (Z : Module.End K (T.W s))
    (h : ∀ g, Z * T.tau s g = T.tau s g * Z) : ∃ c : K, Z = c • 1 := by
  have hall : ∀ a : MonoidAlgebra K G, Z * (T.tau s).asAlgebraHom a = (T.tau s).asAlgebraHom a * Z := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of, h]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
    | smul r x hx => rw [map_smul, mul_smul_comm, smul_mul_assoc, hx]
  have hc : Z ∈ Set.center (Module.End K (T.W s)) := by
    rw [Semigroup.mem_center_iff]
    intro Y
    obtain ⟨a, rfl⟩ := T.irr s Y
    exact (hall a).symm
  obtain ⟨α, hα, hZ⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨α, ?_⟩
  ext x
  rw [hZ]
  simp

/- English proof (translation)
Apply `scalar_of_comm` to reduce the goal to its premises. Introduce `g`. Rewrite using `[← Representation.asAlgebraHom_of, ← map_mul, ← map_mul, eS_comm]`.
-/
lemma tau_eS_scalar (T : GoodSet K G) (s t : T.S) : ∃ c : K, (T.tau t).asAlgebraHom (eS T s) = c • 1 := by
  apply scalar_of_comm
  intro g
  rw [← Representation.asAlgebraHom_of, ← map_mul, ← map_mul, eS_comm]

/- English proof (translation)
The claim follows from `Module.finrank_pos`.
-/
lemma finrank_pos' (T : GoodSet K G) (s : T.S) : 0 < Module.finrank K (T.W s) := Module.finrank_pos

/- English proof (translation)
Take `⟨c, hc⟩` from `tau_eS_scalar T s s`. Establish `hcomp : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) = c • LinearMap.id` using `by ext1 X`. Take `⟨a, rfl⟩` from `T.irr s X`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ← mul_eS, map_mul, hc, LinearMap.smul_apply, LinearMap.id_apply, mul_smul_comm, mul_one]`. Establish `hsum : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) = ∑ x : G, cf T s • ((LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulLeft K (T.tau s x⁻¹)).smulRight (T.tau s x))` using `by ext1 X`.

Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, phiS_apply, map_sum, map_smul, Representation.asAlgebraHom_of]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[smul_smul]`. Establish `htr` using `congrArg (LinearMap.trace K (Module.End K (T.W s))) hsum`.

Rewrite `htr` using `[hcomp, map_sum]`. Simplify using `only [map_smul, LinearMap.trace_smulRight, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, LinearMap.trace_id, Module.finrank_linearMap, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht …`. Establish `hd : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0`. Conclude with `(finrank_pos' T s).ne'` after adjusting the coercions. Establish `hG : ((Fintype.card G : ℕ) : K) ≠ 0`.

Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Establish `hc1 : c = 1`. Simplify using `only [cf, Nat.cast_mul] at htr`. Clear denominators, using `at htr` for the nonvanishing conditions. Conclude with `htr`.

Rewrite using `[hc, hc1, one_smul]`.
-/
lemma tau_eS (T : GoodSet K G) (s : T.S) : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s s

  have hcomp : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) = c • LinearMap.id := by
    ext1 X
    obtain ⟨a, rfl⟩ := T.irr s X
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ← mul_eS, map_mul, hc,
      LinearMap.smul_apply, LinearMap.id_apply, mul_smul_comm, mul_one]
  have hsum : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) =
      ∑ x : G, cf T s • ((LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulLeft K (T.tau s x⁻¹)).smulRight
        (T.tau s x)) := by
    ext1 X
    rw [LinearMap.sum_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, phiS_apply, map_sum,
      map_smul, Representation.asAlgebraHom_of]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [smul_smul]
  have htr := congrArg (LinearMap.trace K (Module.End K (T.W s))) hsum
  rw [hcomp, map_sum] at htr
  simp only [map_smul, LinearMap.trace_smulRight, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, LinearMap.trace_id,
    Module.finrank_linearMap, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (finrank_pos' T s).ne'
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc1 : c = 1 := by
    simp only [cf, Nat.cast_mul] at htr
    field_simp at htr
    exact htr
  rw [hc, hc1, one_smul]

/- English proof (translation)
Rewrite using `[mul_eS, tau_eS, phiS_one]`.
-/
lemma eS_idem (T : GoodSet K G) (s : T.S) : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, phiS_one]

/- English proof (translation)
Introduce `h`. Use `tau_eS T s` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`.
-/
lemma eS_ne_zero (T : GoodSet K G) (s : T.S) : eS T s ≠ 0 := by
  intro h
  have := tau_eS T s
  rw [h, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Take `⟨c, hc⟩` from `tau_eS_scalar T s t`. Conclude with `⟨c, by rw [mul_eS, hc, map_smul, phiS_one]⟩`.
-/
lemma eS_mul_eS_smul (T : GoodSet K G) (s t : T.S) : ∃ c : K, eS T s * eS T t = c • eS T t := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s t
  exact ⟨c, by rw [mul_eS, hc, map_smul, phiS_one]⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `eS_mul_eS_smul T s t`. Establish `hc0 : c ≠ 0` using `by rintro rfl; rw [zero_smul] at hc; exact h hc`. Establish `h2 : eS T s * (eS T s * eS T t) = eS T s * eS T t` using `by rw [← mul_assoc, eS_idem]`. Rewrite `h2` using `[hc, mul_smul_comm, hc, smul_smul]`. Establish `h3 : (c * c - c) • eS T t = 0` using `by rw [sub_smul, h2, sub_self]`.

Break down `smul_eq_zero.mp h3 with h4 | h4` into its components or cases. Establish `: c = 1`. Establish `: c * (c - 1) = 0` using `by linear_combination h4`. Break down `mul_eq_zero.mp this with h5 | h5` into its components or cases. Conclude with `absurd h5 hc0`.

Take the linear combination `h5`. Rewrite using `[hc, this, one_smul]`. Conclude with `absurd h4 (eS_ne_zero T t)`.
-/
lemma eS_mul_eS_of_ne_zero (T : GoodSet K G) (s t : T.S) (h : eS T s * eS T t ≠ 0) :
    eS T s * eS T t = eS T t := by
  obtain ⟨c, hc⟩ := eS_mul_eS_smul T s t
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact h hc
  have h2 : eS T s * (eS T s * eS T t) = eS T s * eS T t := by rw [← mul_assoc, eS_idem]
  rw [hc, mul_smul_comm, hc, smul_smul] at h2
  have h3 : (c * c - c) • eS T t = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have : c = 1 := by
      have : c * (c - 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hc0
      · linear_combination h5
    rw [hc, this, one_smul]
  · exact absurd h4 (eS_ne_zero T t)

/- English proof (translation)
Rewrite using `[eS, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_eq_single x]`. Simplify using `[MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, cf]`. Introduce `y _ hy`. Simplify using `[MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hy]`.

Simplify using the standard rewrite rules.
-/
lemma eS_apply (T : GoodSet K G) (s : T.S) (x : G) :
    (eS T s).coeff x = cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
  classical
  rw [eS, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, cf]
  · intro y _ hy; simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hy]
  · simp

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1` using `eS_mul_eS_of_ne_zero T s t h`. Establish `h' : eS T t * eS T s ≠ 0` using `by rw [← eS_comm]; exact h`. Establish `h2` using `eS_mul_eS_of_ne_zero T t s h'`. Establish `heq : eS T s = eS T t` using `by rw [← h2, ← eS_comm, h1]`.

Apply `hst` to reduce the goal to its premises. Apply `T.inj` to reduce the goal to its premises. Establish `hG : ((Fintype.card G : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `h1'` using `congrArg (fun f => MonoidAlgebra.coeff f 1) heq`. Simplify using `only [eS_apply, inv_one, map_one, LinearMap.trace_one, cf] at h1'`.

Establish `hd : Module.finrank K (T.W s) = Module.finrank K (T.W t)`. Clear denominators, using `at h1'` for the nonvanishing conditions. Establish `: ((Module.finrank K (T.W s) : ℕ) : K) ^ 2 = ((Module.finrank K (T.W t) : ℕ) : K) ^ 2`. Take the linear combination `h1'`. Establish `h2' : Module.finrank K (T.W s) ^ 2 = Module.finrank K (T.W t) ^ 2` using `by exact_mod_cast this`.

Conclude with `Nat.pow_left_injective (by norm_num) h2'`. Express the relevant statement in the definitionally equal form `(fun g => LinearMap.trace K (T.W s) (T.tau s g)) = (fun g => LinearMap.trace K (T.W t) (T.tau t g))`. Use function extensionality and compare the values at `g`. Establish `hx` using `congrArg (fun f => MonoidAlgebra.coeff f g⁻¹) heq`. Simplify using `only [eS_apply, inv_inv, cf, hd] at hx`.

Establish `hd0 : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0` using `by exact_mod_cast (finrank_pos' T t).ne'`. Establish `hne : ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0` using `div_ne_zero hd0 hG`. Conclude with `mul_left_cancel₀ hne hx`.
-/
lemma eS_orth (T : GoodSet K G) (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  by_contra h
  have h1 := eS_mul_eS_of_ne_zero T s t h
  have h' : eS T t * eS T s ≠ 0 := by rw [← eS_comm]; exact h
  have h2 := eS_mul_eS_of_ne_zero T t s h'
  have heq : eS T s = eS T t := by rw [← h2, ← eS_comm, h1]
  apply hst
  apply T.inj
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1' := congrArg (fun f => MonoidAlgebra.coeff f 1) heq
  simp only [eS_apply, inv_one, map_one, LinearMap.trace_one, cf] at h1'
  have hd : Module.finrank K (T.W s) = Module.finrank K (T.W t) := by
    field_simp at h1'
    have : ((Module.finrank K (T.W s) : ℕ) : K) ^ 2 = ((Module.finrank K (T.W t) : ℕ) : K) ^ 2 := by
      linear_combination h1'
    have h2' : Module.finrank K (T.W s) ^ 2 = Module.finrank K (T.W t) ^ 2 := by exact_mod_cast this
    exact Nat.pow_left_injective (by norm_num) h2'
  change (fun g => LinearMap.trace K (T.W s) (T.tau s g)) = (fun g => LinearMap.trace K (T.W t) (T.tau t g))
  funext g
  have hx := congrArg (fun f => MonoidAlgebra.coeff f g⁻¹) heq
  simp only [eS_apply, inv_inv, cf, hd] at hx
  have hd0 : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := by exact_mod_cast (finrank_pos' T t).ne'
  have hne : ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hd0 hG
  exact mul_left_cancel₀ hne hx

/- English proof (translation)
Rewrite using `[eG, Finset.sum_mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single t]`. Conclude with `eS_idem T t`.

Introduce `s _ hs`. Conclude with `eS_orth T s t hs`. Simplify using the standard rewrite rules.
-/
lemma eG_idem (T : GoodSet K G) : eG T * eG T = eG T := by
  classical
  rw [eG, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single t]
  · exact eS_idem T t
  · intro s _ hs; exact eS_orth T s t hs
  · simp

/- English proof (translation)
Rewrite using `[eG, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun s _ => eS_comm T s a`.
-/
lemma eG_comm (T : GoodSet K G) (a : MonoidAlgebra K G) : a * eG T = eG T * a := by
  rw [eG, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => eS_comm T s a

/- English proof (translation)
Use `set Z : Module.End K (T.W s) := ∑ x : G, (cf T s * LinearMap.trace K V (ρ x)) • T.tau s x⁻¹ with hZ`. Establish `hcomm : ∀ g, Z * T.tau s g = T.tau s g * Z`. Introduce `g`. Rewrite using `[hZ, Finset.sum_mul, Finset.mul_sum]`. Repeatedly rewrite using `[smul_mul_assoc, mul_smul_comm, ← map_mul]`.

Use `(Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)).symm` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Establish `h1 : LinearMap.trace K V (ρ (g * x * g⁻¹)) = LinearMap.trace K V (ρ x)`. Rewrite using `[ρ.map_mul, ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρ.map_mul, inv_mul_cancel, ρ.map_one, one_mul]`. Establish `h2 : (g * x * g⁻¹)⁻¹ * g = g * x⁻¹` using `by group`.

Rewrite using `[h1, h2]`. Take `⟨c, hc⟩` from `scalar_of_comm T s Z hcomm`. Use `⟨c, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_eS, phiS_apply, map_sum, map_sum]`. Simplify using `only [map_smul, Representation.asAlgebraHom_of, smul_eq_mul]`.

Establish `: LinearMap.trace K (T.W s) (Z * (T.tau s).asAlgebraHom a) = c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a)`. Rewrite using `[hc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]`. Rewrite using `[← this, hZ, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma trace_mul_eS (T : GoodSet K G) (s : T.S) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ c : K, ∀ a : MonoidAlgebra K G,
      LinearMap.trace K V (ρ.asAlgebraHom (a * eS T s)) = c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
  set Z : Module.End K (T.W s) := ∑ x : G, (cf T s * LinearMap.trace K V (ρ x)) • T.tau s x⁻¹ with hZ
  have hcomm : ∀ g, Z * T.tau s g = T.tau s g * Z := by
    intro g
    rw [hZ, Finset.sum_mul, Finset.mul_sum]
    simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)).symm
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    have h1 : LinearMap.trace K V (ρ (g * x * g⁻¹)) = LinearMap.trace K V (ρ x) := by
      rw [ρ.map_mul, ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρ.map_mul, inv_mul_cancel,
        ρ.map_one, one_mul]
    have h2 : (g * x * g⁻¹)⁻¹ * g = g * x⁻¹ := by group
    rw [h1, h2]
  obtain ⟨c, hc⟩ := scalar_of_comm T s Z hcomm
  refine ⟨c, fun a => ?_⟩
  rw [mul_eS, phiS_apply, map_sum, map_sum]
  simp only [map_smul, Representation.asAlgebraHom_of, smul_eq_mul]
  have : LinearMap.trace K (T.W s) (Z * (T.tau s).asAlgebraHom a) =
      c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
    rw [hc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  rw [← this, hZ, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  ring

end PI.Dv.Tr
