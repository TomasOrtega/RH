import Mathlib
import GroundTheory.LocalFields.FormalGroups.Basics

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section Helpers

variable {A : Type*} [CommRing A] {σ : Type*}

noncomputable def substEach (g : PowerSeries A) : σ → MvPowerSeries σ A :=
  fun i => PowerSeries.subst (X i : MvPowerSeries σ A) g

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem substEach_apply (g : PowerSeries A) (i : σ) :
    (substEach g i : MvPowerSeries σ A) = PowerSeries.subst (X i : MvPowerSeries σ A) g := rfl

/- English proof (translation)
The claim follows from `constantCoeff_powerSeries_subst (by simp) hg`.
-/
theorem constantCoeff_substEach {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0)
    (i : σ) : constantCoeff (substEach g i : MvPowerSeries σ A) = 0 :=
  constantCoeff_powerSeries_subst (by simp) hg

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero (constantCoeff_substEach hg)`.
-/
theorem hasSubst_substEach [Finite σ] {g : PowerSeries A}
    (hg : PowerSeries.constantCoeff g = 0) : HasSubst (substEach g : σ → MvPowerSeries σ A) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substEach hg)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `le_trans (le_min ha (by rwa [order_neg])) min_order_le_add`.
-/
theorem le_order_sub {n : ℕ∞} {a b : MvPowerSeries σ A} (ha : n ≤ order a) (hb : n ≤ order b) :
    n ≤ order (a - b) := by
  rw [sub_eq_add_neg]
  exact le_trans (le_min ha (by rwa [order_neg])) min_order_le_add

/- English proof (translation)
Establish `e : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2` using `by push_cast; ring`. Conclude with `(ENat.add_le_add_iff_right ENat.one_ne_top).1 (e ▸ h)`.
-/
theorem succ_le_of_add_two_le {n : ℕ} {x : ℕ∞} (h : (n : ℕ∞) + 2 ≤ x + 1) :
    ((n + 1 : ℕ) : ℕ∞) ≤ x := by
  have e : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (e ▸ h)

/- English proof (translation)
Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Establish `hd' : d = Finsupp.single () (d ())` using `by ext; simp`. Rewrite `hd`, the goal using `[hd']`. Rewrite `hd` using `[Finsupp.degree_single]`. Conclude with `h _ hd`.
-/
theorem le_order_of_coeff_eq_zero {f : PowerSeries A} {n : ℕ}
    (h : ∀ k < n, PowerSeries.coeff k f = 0) : (n : ℕ∞) ≤ order (f : MvPowerSeries Unit A) := by
  refine nat_le_order fun d hd => ?_
  have hd' : d = Finsupp.single () (d ()) := by ext; simp
  rw [hd'] at hd ⊢
  rw [Finsupp.degree_single] at hd
  exact h _ hd

/- English proof (translation)
Rewrite using `[PowerSeries.subst_mul ha, PowerSeries.subst_X ha, PowerSeries.subst_C]`.
-/
theorem powerSeries_subst_C_mul_X {τ : Type*} {a : MvPowerSeries τ A} (ha : PowerSeries.HasSubst a)
    (c : A) : PowerSeries.subst a (PowerSeries.C c * PowerSeries.X) = C c * a := by
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_X ha, PowerSeries.subst_C]

/- English proof (translation)
The claim follows from `le_order_of_coeff_eq_zero (n := 2) fun k hk => by interval_cases k · simp [hf0] · simp [hf1]`.
-/
theorem two_le_order_sub_C_mul_X {f : PowerSeries A} {c : A}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = c) :
    (2 : ℕ∞) ≤ order ((f - PowerSeries.C c * PowerSeries.X : PowerSeries A) : MvPowerSeries Unit A) :=
  le_order_of_coeff_eq_zero (n := 2) fun k hk => by
    interval_cases k
    · simp [hf0]
    · simp [hf1]

/- English proof (translation)
Use `set f₂ : PowerSeries A := f - PowerSeries.C c * PowerSeries.X with hf₂`. Establish `h2` using `two_le_order_sub_C_mul_X hf0 hf1`. Establish `hφs : PowerSeries.HasSubst φ` using `PowerSeries.HasSubst.of_constantCoeff_zero hφ`. Establish `hψs : PowerSeries.HasSubst ψ` using `PowerSeries.HasSubst.of_constantCoeff_zero hψ`. Establish `hdec : f = PowerSeries.C c * PowerSeries.X + f₂` using `by rw [hf₂]; ring`.

Establish `e : PowerSeries.subst φ f - PowerSeries.subst ψ f - C c * (φ - ψ) = PowerSeries.subst φ f₂ - PowerSeries.subst ψ f₂` using `by conv_lhs => rw [hdec]`. Rewrite using `[PowerSeries.subst_add hφs, PowerSeries.subst_add hψs, powerSeries_subst_C_mul_X hφs, powerSeries_subst_C_mul_X hψs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, PowerSeries.subst_def, PowerSeries.subst_def]`. Establish `hφ' : HasSubst (fun _ : Unit => φ)` using `(PowerSeries.hasSubst_iff).mp hφs`.

Establish `hψ' : HasSubst (fun _ : Unit => ψ)` using `(PowerSeries.hasSubst_iff).mp hψs`. Establish `key` using `add_le_order_subst_sub_subst hφ' hψ' (fun _ => hφ) (fun _ => hψ) (fun _ => h) h2`. Conclude with `succ_le_of_add_two_le key`.
-/
theorem le_order_subst_sub_subst_sub_C_mul {f : PowerSeries A} {c : A}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = c)
    {φ ψ : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0) {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      order (PowerSeries.subst φ f - PowerSeries.subst ψ f - C c * (φ - ψ)) := by
  set f₂ : PowerSeries A := f - PowerSeries.C c * PowerSeries.X with hf₂
  have h2 := two_le_order_sub_C_mul_X hf0 hf1
  have hφs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero hφ
  have hψs : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero hψ
  have hdec : f = PowerSeries.C c * PowerSeries.X + f₂ := by rw [hf₂]; ring
  have e : PowerSeries.subst φ f - PowerSeries.subst ψ f - C c * (φ - ψ) =
      PowerSeries.subst φ f₂ - PowerSeries.subst ψ f₂ := by
    conv_lhs => rw [hdec]
    rw [PowerSeries.subst_add hφs, PowerSeries.subst_add hψs, powerSeries_subst_C_mul_X hφs,
      powerSeries_subst_C_mul_X hψs]
    ring
  rw [e, PowerSeries.subst_def, PowerSeries.subst_def]
  have hφ' : HasSubst (fun _ : Unit => φ) := (PowerSeries.hasSubst_iff).mp hφs
  have hψ' : HasSubst (fun _ : Unit => ψ) := (PowerSeries.hasSubst_iff).mp hψs
  have key := add_le_order_subst_sub_subst hφ' hψ' (fun _ => hφ) (fun _ => hψ) (fun _ => h) h2
  exact succ_le_of_add_two_le key

/- English proof (translation)
Rewrite using `[coeff_rescale]`. Use `congr 1`. Simplify using `[Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]`.
-/
theorem coeff_rescale_const (c : A) (δ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    coeff e (rescale (Function.const σ c) δ) = c ^ e.degree * coeff e δ := by
  rw [coeff_rescale]
  congr 1
  simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/- English proof (translation)
Rewrite using `[rescale_eq_subst]`. Establish `hb : HasSubst (Function.const σ c • (X : σ → MvPowerSeries σ A))` using `HasSubst.smul_X _`. Establish `hab : ∀ i, (2 : ℕ∞) ≤ order (substEach g i - (Function.const σ c • (X : σ → MvPowerSeries σ A)) i)`. Introduce `i`. Establish `hXi : PowerSeries.HasSubst (X i : MvPowerSeries σ A)` using `PowerSeries.HasSubst.X i`.

Establish `e : (Function.const σ c • (X : σ → MvPowerSeries σ A)) i = PowerSeries.subst (X i : MvPowerSeries σ A) (PowerSeries.C c * PowerSeries.X)`. Rewrite using `[powerSeries_subst_C_mul_X hXi]`. Express the relevant statement in the definitionally equal form `Function.const σ c i • (X i : MvPowerSeries σ A) = _`. Rewrite using `[Function.const_apply, smul_eq_C_mul]`. Rewrite using `[e, substEach_apply, PowerSeries.subst_def, PowerSeries.subst_def]`.

Conclude with `le_order_subst_sub_subst ((PowerSeries.hasSubst_iff).mp hXi) (fun _ => by simp) (two_le_order_sub_C_mul_X hg0 hg1)`. Establish `key` using `add_le_order_subst_sub_subst (hasSubst_substEach hg0) hb (constantCoeff_substEach hg0) (fun i => by simp) hab h`. Rewrite `key` using `[add_comm]`. Conclude with `succ_le_of_add_two_le key`.
-/
theorem le_order_subst_substEach_sub_rescale [Finite σ] {g : PowerSeries A} {c : A}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = c)
    {δ : MvPowerSeries σ A} {n : ℕ} (h : (n : ℕ∞) ≤ order δ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (subst (substEach g) δ - rescale (Function.const σ c) δ) := by
  rw [rescale_eq_subst]
  have hb : HasSubst (Function.const σ c • (X : σ → MvPowerSeries σ A)) := HasSubst.smul_X _
  have hab : ∀ i, (2 : ℕ∞) ≤ order (substEach g i - (Function.const σ c • (X : σ → MvPowerSeries σ A)) i) := by
    intro i
    have hXi : PowerSeries.HasSubst (X i : MvPowerSeries σ A) := PowerSeries.HasSubst.X i
    have e : (Function.const σ c • (X : σ → MvPowerSeries σ A)) i =
        PowerSeries.subst (X i : MvPowerSeries σ A) (PowerSeries.C c * PowerSeries.X) := by
      rw [powerSeries_subst_C_mul_X hXi]
      change Function.const σ c i • (X i : MvPowerSeries σ A) = _
      rw [Function.const_apply, smul_eq_C_mul]
    rw [e, substEach_apply, PowerSeries.subst_def, PowerSeries.subst_def]
    exact le_order_subst_sub_subst ((PowerSeries.hasSubst_iff).mp hXi) (fun _ => by simp)
      (two_le_order_sub_C_mul_X hg0 hg1)
  have key := add_le_order_subst_sub_subst (hasSubst_substEach hg0) hb
    (constantCoeff_substEach hg0) (fun i => by simp) hab h
  rw [add_comm] at key
  exact succ_le_of_add_two_le key

/- English proof (translation)
Take `⟨p, hcp, n, hp, hcard⟩` from `FiniteField.card' k`. Use `hcp` as an intermediate fact. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `h` using `map_iterateFrobenius_expand p hp.ne_zero ψ n`. Establish `hid : iterateFrobenius k p n = RingHom.id k`.

Use extensionality with `x`. Rewrite using `[iterateFrobenius_def, ← hcard]`. Conclude with `FiniteField.pow_card x`. Rewrite `h` using `[hid, map_id]`. Rewrite using `[hcard]`.

Simplify `h` using `[expand, coe_substAlgHom]`.
-/
theorem subst_X_pow_card_eq_pow {k : Type*} [Field k] [Fintype k] (ψ : MvPowerSeries σ k) :
    subst (fun i => (X i : MvPowerSeries σ k) ^ Fintype.card k) ψ = ψ ^ Fintype.card k := by
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' k
  have := hcp
  have : Fact p.Prime := ⟨hp⟩
  have h := map_iterateFrobenius_expand p hp.ne_zero ψ n
  have hid : iterateFrobenius k p n = RingHom.id k := by
    ext x
    rw [iterateFrobenius_def, ← hcard]
    exact FiniteField.pow_card x
  rw [hid, map_id] at h
  rw [hcard]
  simpa [expand, coe_substAlgHom] using h

end Helpers

section Construction

variable {A : Type*} [CommRing A] {σ : Type*}

noncomputable def dropConst (φ : MvPowerSeries σ A) : MvPowerSeries σ A :=
  φ - C (constantCoeff φ)

/- English proof (translation)
Simplify using `[dropConst]`.
-/
theorem constantCoeff_dropConst (φ : MvPowerSeries σ A) : constantCoeff (dropConst φ) = 0 := by
  simp [dropConst]

/- English proof (translation)
Rewrite using `[dropConst, map_sub, coeff_C, if_neg he, sub_zero]`.
-/
theorem coeff_dropConst (φ : MvPowerSeries σ A) {e : σ →₀ ℕ} (he : e ≠ 0) :
    coeff e (dropConst φ) = coeff e φ := by
  classical
  rw [dropConst, map_sub, coeff_C, if_neg he, sub_zero]

/- English proof (translation)
Simplify using `[dropConst, h]`.
-/
theorem dropConst_of_constantCoeff_eq_zero {φ : MvPowerSeries σ A} (h : constantCoeff φ = 0) :
    dropConst φ = φ := by
  simp [dropConst, h]

noncomputable def defect (f g : PowerSeries A) (φ : MvPowerSeries σ A) : MvPowerSeries σ A :=
  subst (substEach g) (dropConst φ) - PowerSeries.subst (dropConst φ) f

open Classical in

noncomputable def divBy (c a : A) : A :=
  if h : c ∣ a then h.choose else 0

/- English proof (translation)
Rewrite using `[divBy, dif_pos h]`. Conclude with `h.choose_spec.symm`.
-/
theorem mul_divBy {c a : A} (h : c ∣ a) : c * divBy c a = a := by
  rw [divBy, dif_pos h]
  exact h.choose_spec.symm

noncomputable def step (π : A) (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) :
    MvPowerSeries σ A :=
  fun e => if e.degree ≤ 1 then coeff e ℓ else
    coeff e φ + Ring.inverse (1 - π ^ (e.degree - 1)) * divBy π (coeff e (defect f g φ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_step (π : A) (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    coeff e (step π f g ℓ φ) = if e.degree ≤ 1 then coeff e ℓ else
      coeff e φ + Ring.inverse (1 - π ^ (e.degree - 1)) * divBy π (coeff e (defect f g φ)) :=
  rfl

variable [Finite σ] {π : A} {f g : PowerSeries A}
  (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = π)
  (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = π)

include hf0 hf1 hg0 hg1 in

/- English proof (translation)
Establish `hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ)`. Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Distinguish the cases in `hd0 : d = 0`. Simplify using `[hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]`. Rewrite using `[map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]`.

Conclude with `coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)`. Establish `h1` using `le_order_subst_substEach_sub_rescale hg0 hg1 hδ`. Establish `h2` using `le_order_subst_sub_subst_sub_C_mul hf0 hf1 (constantCoeff_dropConst φ) (constantCoeff_dropConst ψ) hδ`. Establish `h3` using `le_order_sub h1 h2`. Establish `hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast Nat.lt_succ_of_le he`.

Establish `h0` using `coeff_of_lt_order (hlt.trans_le h3)`. Rewrite `h0` using `[subst_sub (hasSubst_substEach hg0)]`. Simplify using `only [defect, map_sub, coeff_rescale_const, coeff_C_mul] at h0 ⊢`. Take the linear combination `h0`.
-/
theorem coeff_defect_sub_defect {φ ψ : MvPowerSeries σ A} {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (defect f g φ) - coeff e (defect f g ψ) =
      (π ^ e.degree - π) * coeff e (dropConst φ - dropConst ψ) := by
  have hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ) := by
    refine nat_le_order fun d hd => ?_
    by_cases hd0 : d = 0
    · simp [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
    · rw [map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]
      exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  have h1 := le_order_subst_substEach_sub_rescale hg0 hg1 hδ
  have h2 := le_order_subst_sub_subst_sub_C_mul hf0 hf1 (constantCoeff_dropConst φ)
    (constantCoeff_dropConst ψ) hδ
  have h3 := le_order_sub h1 h2
  have hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le he
  have h0 := coeff_of_lt_order (hlt.trans_le h3)
  rw [subst_sub (hasSubst_substEach hg0)] at h0
  simp only [defect, map_sub, coeff_rescale_const, coeff_C_mul] at h0 ⊢
  linear_combination h0

variable (hreg : ∀ x : A, π * x = 0 → x = 0) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit (1 - π ^ n))
  (hdiv : ∀ (φ : MvPowerSeries σ A) (e : σ →₀ ℕ), π ∣ coeff e (defect f g φ))

include hf0 hf1 hg0 hg1 hreg hunit hdiv in
/- English proof (translation)
Use `nat_le_order fun e he => ?_` and prove the remaining obligations. Establish `he' : e.degree ≤ n` using `Nat.lt_succ_iff.1 he`. Rewrite using `[map_sub, coeff_step, coeff_step]`. Use `split_ifs with h1`. Conclude with `sub_self _`.

Use `replace h1 := not_le.1 h1`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h1`. Establish `hkey` using `coeff_defect_sub_defect hf0 hf1 hg0 hg1 h he'`.

Rewrite `hkey` using `[map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0]`. Take `⟨m, hm⟩ : ∃ m, e.degree = m + 1` from `⟨e.degree - 1, by omega⟩`. Rewrite using `[hm, Nat.add_sub_cancel]`. Rewrite `hkey` using `[hm]`. Establish `hdiff : divBy π (coeff e (defect f g φ)) - divBy π (coeff e (defect f g ψ)) = (π ^ m - 1) * (coeff e φ - coeff e ψ)`.

Rewrite using `[← sub_eq_zero]`. Apply `hreg` to reduce the goal to its premises. Rewrite using `[mul_sub, mul_sub, mul_divBy (hdiv φ e), mul_divBy (hdiv ψ e), hkey]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu` using `Ring.inverse_mul_cancel _ (hunit m (by omega))`.

Take the linear combination `Ring.inverse (1 - π ^ m) * hdiff - (coeff e φ - coeff e ψ) * hu`.
-/
theorem step_contract (ℓ φ ψ : MvPowerSeries σ A) (n : ℕ) (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (step π f g ℓ φ - step π f g ℓ ψ) := by
  refine nat_le_order fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.1 he
  rw [map_sub, coeff_step, coeff_step]
  split_ifs with h1
  · exact sub_self _
  · replace h1 := not_le.1 h1
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at h1
    have hkey := coeff_defect_sub_defect hf0 hf1 hg0 hg1 h he'
    rw [map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0] at hkey
    obtain ⟨m, hm⟩ : ∃ m, e.degree = m + 1 := ⟨e.degree - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm] at hkey
    have hdiff : divBy π (coeff e (defect f g φ)) - divBy π (coeff e (defect f g ψ)) =
        (π ^ m - 1) * (coeff e φ - coeff e ψ) := by
      rw [← sub_eq_zero]
      apply hreg
      rw [mul_sub, mul_sub, mul_divBy (hdiv φ e), mul_divBy (hdiv ψ e), hkey]
      ring
    have hu := Ring.inverse_mul_cancel _ (hunit m (by omega))
    linear_combination Ring.inverse (1 - π ^ m) * hdiff - (coeff e φ - coeff e ψ) * hu

include hf0 hg0 in
/- English proof (translation)
Establish `h0 : dropConst (0 : MvPowerSeries σ A) = 0` using `by simp [dropConst]`. Rewrite using `[defect, h0, ← coe_substAlgHom (hasSubst_substEach hg0), map_zero, PowerSeries.subst_zero_of_constantCoeff_zero hf0, sub_zero]`.
-/
theorem defect_zero : defect f g (0 : MvPowerSeries σ A) = 0 := by
  have h0 : dropConst (0 : MvPowerSeries σ A) = 0 := by simp [dropConst]
  rw [defect, h0, ← coe_substAlgHom (hasSubst_substEach hg0), map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero hf0, sub_zero]

include hf0 hf1 hg0 hg1 hreg hunit hdiv in

/- English proof (translation)
Establish `hdivBy0 : divBy π 0 = 0` using `hreg _ (mul_divBy (dvd_zero π))`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Establish `hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ`. Introduce `e he`.

Use `congrArg (coeff e) hs` as an intermediate fact. Rewrite `this` using `[coeff_step, if_pos he]`. Conclude with `this.symm`. Establish `hφ0 : constantCoeff φ = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp), coeff_zero_eq_constantCoeff_apply, hℓ]`.

Establish `hdef : defect f g φ = 0`. Use extensionality with `e`. Rewrite using `[map_zero]`. Distinguish the cases in `he : e.degree ≤ 1`. Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0)`.

Rewrite using `[sub_zero, Nat.cast_one]`. Conclude with `one_le_order_iff_constCoeff_eq_zero.2 hφ0`. Use `coeff_defect_sub_defect hf0 hf1 hg0 hg1 h1 he` as an intermediate fact. Rewrite `this` using `[defect_zero hf0 hg0, map_zero, sub_zero]`. Rewrite using `[this]`.

Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h` into its components or cases. Rewrite `h` using `[Finsupp.degree_eq_zero_iff]`. Substitute `h` using the available equality. Simplify using `[coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]`. Rewrite using `[h, pow_one, sub_self, zero_mul]`.

Use `congrArg (coeff e) hs` as an intermediate fact. Rewrite `this` using `[coeff_step, if_neg he, add_eq_left]`. Establish `hu` using `Ring.inverse_mul_cancel _ (hunit (e.degree - 1) (by omega))`. Establish `hq : divBy π (coeff e (defect f g φ)) = 0`. Take the linear combination `(1 - π ^ (e.degree - 1)) * this - divBy π (coeff e (defect f g φ)) * hu`.

Rewrite using `[← mul_divBy (hdiv φ e), hq, mul_zero]`. Establish `h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ)` using `nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]`. Use `⟨by exact_mod_cast h2, ?_⟩` and prove the remaining obligations. Rewrite `hdef` using `[defect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero]`. Conclude with `hdef.symm`.

Introduce and unpack `⟨h2, heq⟩`. Establish `hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ`. Introduce `e he`. Establish `he2 : (e.degree : ℕ∞) < 2`. Establish `: e.degree < 2` using `by omega`.

Conclude with `this` after adjusting the coercions. Use `coeff_of_lt_order (lt_of_lt_of_le he2 h2)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hφ0 : constantCoeff φ = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp), coeff_zero_eq_constantCoeff_apply, hℓ]`.

Establish `hdef : defect f g φ = 0`. Rewrite using `[defect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]`. Use extensionality with `e`. Rewrite using `[coeff_step]`. Use `split_ifs with he`.

Conclude with `(hlin e he).symm`. Rewrite using `[hdef, map_zero, hdivBy0, mul_zero, add_zero]`.
-/
theorem step_eq_self_iff {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0)
    (φ : MvPowerSeries σ A) :
    step π f g ℓ φ = φ ↔
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ := by
  have hdivBy0 : divBy π 0 = 0 := hreg _ (mul_divBy (dvd_zero π))
  constructor
  · intro hs
    have hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have := congrArg (coeff e) hs
      rw [coeff_step, if_pos he] at this
      exact this.symm
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : defect f g φ = 0 := by
      ext e
      rw [map_zero]
      by_cases he : e.degree ≤ 1
      · have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
          rw [sub_zero, Nat.cast_one]
          exact one_le_order_iff_constCoeff_eq_zero.2 hφ0
        have := coeff_defect_sub_defect hf0 hf1 hg0 hg1 h1 he
        rw [defect_zero hf0 hg0, map_zero, sub_zero] at this
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
        · rw [Finsupp.degree_eq_zero_iff] at h
          subst h
          simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
        · rw [h, pow_one, sub_self, zero_mul]
      · have := congrArg (coeff e) hs
        rw [coeff_step, if_neg he, add_eq_left] at this
        have hu := Ring.inverse_mul_cancel _ (hunit (e.degree - 1) (by omega))
        have hq : divBy π (coeff e (defect f g φ)) = 0 := by
          linear_combination (1 - π ^ (e.degree - 1)) * this -
            divBy π (coeff e (defect f g φ)) * hu
        rw [← mul_divBy (hdiv φ e), hq, mul_zero]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ) :=
      nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]
    refine ⟨by exact_mod_cast h2, ?_⟩
    · rw [defect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero] at hdef
      exact hdef.symm
  · rintro ⟨h2, heq⟩
    have hlin : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have he2 : (e.degree : ℕ∞) < 2 := by
        have : e.degree < 2 := by omega
        exact_mod_cast this
      have := coeff_of_lt_order (lt_of_lt_of_le he2 h2)
      rwa [map_sub, sub_eq_zero] at this
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : defect f g φ = 0 := by
      rw [defect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]
    ext e
    rw [coeff_step]
    split_ifs with he
    · exact (hlin e he).symm
    · rw [hdef, map_zero, hdivBy0, mul_zero, add_zero]

include hf0 hf1 hg0 hg1 hreg hunit hdiv in

/- English proof (translation)
Take `⟨φ, hφ, huniq⟩` from `existsUnique_fixedPoint (step π f g ℓ) (step_contract hf0 hf1 hg0 hg1 hreg hunit hdiv ℓ)`. Conclude with `⟨φ, (step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ φ).1 hφ, fun ψ hψ => huniq ψ ((step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ ψ).2 hψ)⟩`.
-/
theorem existsUnique_of_dvd_defect {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_fixedPoint (step π f g ℓ)
    (step_contract hf0 hf1 hg0 hg1 hreg hunit hdiv ℓ)
  exact ⟨φ, (step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ φ).1 hφ,
    fun ψ hψ => huniq ψ ((step_eq_self_iff hf0 hf1 hg0 hg1 hreg hunit hdiv hℓ ψ).2 hψ)⟩

end Construction

section LocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

structure IsLubinTateSeries (π : A) (f : PowerSeries A) : Prop where
  constantCoeff_eq_zero : PowerSeries.constantCoeff f = 0
  coeff_one : PowerSeries.coeff 1 f = π
  dvd_coeff_sub : ∀ n : ℕ,
    π ∣ PowerSeries.coeff n (f - PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A))

end LocalRing

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`.
-/
theorem residue_eq_zero_iff_dvd (hπ : Irreducible π) (a : A) :
    IsLocalRing.residue A a = 0 ↔ π ∣ a := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

/- English proof (translation)
The claim follows from `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu))`.
-/
theorem isUnit_one_sub_pow (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - π ^ n) :=
  IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu))

/- English proof (translation)
Use extensionality with `n`. Use `(residue_eq_zero_iff_dvd hπ _).2 (hf.dvd_coeff_sub n)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero, Nat.card_eq_fintype_card]`. Rewrite using `[PowerSeries.coeff_map, this, ← PowerSeries.coeff_map, map_pow, PowerSeries.map_X]`.
-/
theorem map_residue_of_isLubinTateSeries [Fintype (IsLocalRing.ResidueField A)]
    (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries.map (IsLocalRing.residue A) f =
      PowerSeries.X ^ Fintype.card (IsLocalRing.ResidueField A) := by
  ext n
  have := (residue_eq_zero_iff_dvd hπ _).2 (hf.dvd_coeff_sub n)
  rw [map_sub, map_sub, sub_eq_zero, Nat.card_eq_fintype_card] at this
  rw [PowerSeries.coeff_map, this, ← PowerSeries.coeff_map, map_pow, PowerSeries.map_X]

/- English proof (translation)
Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField A)`. Rewrite using `[← residue_eq_zero_iff_dvd hπ, ← coeff_map]`. Establish `hs : PowerSeries.HasSubst (dropConst φ)` using `PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)`. Establish `hE` using `hasSubst_substEach (σ := σ) hg.constantCoeff_eq_zero`. Establish `hmapE : (fun i => map (IsLocalRing.residue A) (substEach g i : MvPowerSeries σ A)) = fun i => X i ^ Fintype.card (IsLocalRing.ResidueField A)`.

Use function extensionality and compare the values at `i`. Rewrite using `[substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_residue_of_isLubinTateSeries hπ hg, map_X, PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]`. Establish `hs' : PowerSeries.HasSubst (map (IsLocalRing.residue A) (dropConst φ))` using `PowerSeries.HasSubst.of_constantCoeff_zero (by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst, map_zero])`. Rewrite using `[defect, map_sub, map_subst hE, PowerSeries.map_subst hs, map_residue_of_isLubinTateSeries hπ hf, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE, subst_X_pow_card_eq_pow, sub_self, map_zero]`.
-/
theorem dvd_coeff_defect [Finite (IsLocalRing.ResidueField A)] (hπ : Irreducible π)
    {σ : Type*} [Finite σ] {f g : PowerSeries A} (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (φ : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    π ∣ coeff e (defect f g φ) := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField A)
  rw [← residue_eq_zero_iff_dvd hπ, ← coeff_map]
  have hs : PowerSeries.HasSubst (dropConst φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)
  have hE := hasSubst_substEach (σ := σ) hg.constantCoeff_eq_zero
  have hmapE : (fun i => map (IsLocalRing.residue A) (substEach g i : MvPowerSeries σ A)) =
      fun i => X i ^ Fintype.card (IsLocalRing.ResidueField A) := by
    funext i
    rw [substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i),
      map_residue_of_isLubinTateSeries hπ hg, map_X,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have hs' : PowerSeries.HasSubst (map (IsLocalRing.residue A) (dropConst φ)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_dropConst, map_zero])
  rw [defect, map_sub, map_subst hE, PowerSeries.map_subst hs,
    map_residue_of_isLubinTateSeries hπ hf, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE,
    subst_X_pow_card_eq_pow, sub_self, map_zero]

noncomputable def sum₂ {σ : Type*} [Fintype σ] (a : σ → A) : MvPowerSeries σ A :=
  ∑ i, C (a i) * X i

/- English proof (translation)
Simplify using `[sum₂]`.
-/
theorem constantCoeff_linearForm {σ : Type*} [Fintype σ] (a : σ → A) :
    constantCoeff (sum₂ a) = 0 := by
  simp [sum₂]

/- English proof (translation)
Establish `he2 : (e.degree : ℕ∞) < 2`. Establish `: e.degree < 2` using `by omega`. Conclude with `this` after adjusting the coercions. Use `coeff_of_lt_order (lt_of_lt_of_le he2 h)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem coeff_eq_of_two_le_order_sub {σ : Type*} {φ ψ : MvPowerSeries σ A}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

variable [Finite (IsLocalRing.ResidueField A)] (hπ : Irreducible π) {f g : PowerSeries A}
include hπ

/- English proof (translation)
The claim follows from `existsUnique_of_dvd_defect hf.constantCoeff_eq_zero hf.coeff_one hg.constantCoeff_eq_zero hg.coeff_one (fun x hx => (mul_eq_zero.1 hx).resolve_left hπ.ne_zero) (fun _ hn => isUnit_one_sub_pow hπ hn) (dvd_coeff_defect hπ hf hg) hℓ`.
-/
theorem existsUnique_subst_eq {σ : Type*} [Finite σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) {ℓ : MvPowerSeries σ A} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ f = subst (substEach g) φ :=
  existsUnique_of_dvd_defect hf.constantCoeff_eq_zero hf.coeff_one hg.constantCoeff_eq_zero
    hg.coeff_one (fun x hx => (mul_eq_zero.1 hx).resolve_left hπ.ne_zero)
    (fun _ hn => isUnit_one_sub_pow hπ hn) (dvd_coeff_defect hπ hf hg) hℓ

/- English proof (translation)
The claim follows from `existsUnique_subst_eq hπ hf hg (constantCoeff_linearForm a)`.
-/
theorem existsUnique_subst_eq_linearForm {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) :
    ∃! φ : MvPowerSeries σ A,
      (2 : ℕ∞) ≤ order (φ - sum₂ a) ∧ PowerSeries.subst φ f = subst (substEach g) φ :=
  existsUnique_subst_eq hπ hf hg (constantCoeff_linearForm a)

noncomputable def lubinTateLift {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) : MvPowerSeries σ A :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose

variable {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
  (a : σ → A)

/- English proof (translation)
The claim follows from `(existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.1`.
-/
theorem two_le_order_lubinTateLift_sub :
    (2 : ℕ∞) ≤ order (lubinTateLift hπ hf hg a - sum₂ a) :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.1

/- English proof (translation)
The claim follows from `(existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.2`.
-/
theorem subst_lubinTateLift :
    PowerSeries.subst (lubinTateLift hπ hf hg a) f =
      subst (substEach g) (lubinTateLift hπ hf hg a) :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec.2

/- English proof (translation)
The claim follows from `(existsUnique_subst_eq_linearForm hπ hf hg a).unique ⟨h2, h⟩ (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec`.
-/
theorem eq_lubinTateLift {φ : MvPowerSeries σ A} (h2 : (2 : ℕ∞) ≤ order (φ - sum₂ a))
    (h : PowerSeries.subst φ f = subst (substEach g) φ) : φ = lubinTateLift hπ hf hg a :=
  (existsUnique_subst_eq_linearForm hπ hf hg a).unique ⟨h2, h⟩
    (existsUnique_subst_eq_linearForm hπ hf hg a).exists.choose_spec

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hg a) (by simp), coeff_zero_eq_constantCoeff_apply, constantCoeff_linearForm]`.
-/
theorem constantCoeff_lubinTateLift : constantCoeff (lubinTateLift hπ hf hg a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hg a) (by simp),
    coeff_zero_eq_constantCoeff_apply, constantCoeff_linearForm]

end DVR

end GroundTheory.LocalField.FormalGroup
