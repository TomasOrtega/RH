import Mathlib
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {ι : Type*}

/- English proof (translation)
Rewrite using `[substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]`.
-/
theorem map_substEach (g : PowerSeries A) (i : ι) :
    map φ (substEach g i : MvPowerSeries ι A) = substEach (PowerSeries.map φ g) i := by
  rw [substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]

/- English proof (translation)
Take `⟨h0, h2, he⟩` from `h`. Use `⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `h2.trans (le_order_map φ)`. Use `congrArg (MvPowerSeries.map φ) he` as an intermediate fact.

Rewrite `this` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), MvPowerSeries.map_subst (hasSubst_substEach hg0)]`. Rewrite using `[this]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_substEach φ g i`.
-/
theorem IsLubinTateLift.map [Finite ι] {f g : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) {ℓ Φ : MvPowerSeries ι A}
    (h : IsLubinTateLift f g ℓ Φ) :
    IsLubinTateLift (PowerSeries.map φ f) (PowerSeries.map φ g) (MvPowerSeries.map φ ℓ)
      (MvPowerSeries.map φ Φ) := by
  obtain ⟨h0, h2, he⟩ := h
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map φ)
  · have := congrArg (MvPowerSeries.map φ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
      MvPowerSeries.map_subst (hasSubst_substEach hg0)] at this
    rw [this]
    congr 1
    funext i
    exact map_substEach φ g i

end BaseChange

section Twisted

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι : Type*}

noncomputable def twistedDefect (g f : PowerSeries B) (φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  PowerSeries.subst (dropConst φ) g - subst (substEach f) (map σ (dropConst φ))

def twistOp (u π : B) (d : ℕ) (b : B) : B :=
  u * b - π ^ (d - 1) * σ b

noncomputable def twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  fun e => if e.degree ≤ 1 then coeff e ℓ else
    Function.invFun (twistOp σ u π e.degree)
      (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    coeff e (twistStep σ u π g f ℓ φ) = if e.degree ≤ 1 then coeff e ℓ else
      Function.invFun (twistOp σ u π e.degree)
        (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ))) :=
  rfl

def IsTwistedLift (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) : Prop :=
  constantCoeff φ = 0 ∧ (2 : ℕ∞) ≤ order (φ - ℓ) ∧
    PowerSeries.subst φ g = subst (substEach f) (map σ φ)

variable [Finite ι] {u π : B} {f g : PowerSeries B}
  (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = π)
  (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = u * π)

include hf0 hf1 hg0 hg1 in

/- English proof (translation)
Establish `hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ)`. Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Distinguish the cases in `hd0 : d = 0`. Simplify using `[hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]`. Rewrite using `[map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]`.

Conclude with `coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)`. Establish `hδσ : (n : ℕ∞) ≤ order (map σ (dropConst φ - dropConst ψ))` using `hδ.trans (le_order_map σ)`. Establish `h1` using `le_order_subst_substEach_sub_rescale hf0 hf1 hδσ`. Establish `h2` using `le_order_subst_sub_subst_sub_C_mul hg0 hg1 (constantCoeff_dropConst φ) (constantCoeff_dropConst ψ) hδ`. Establish `h3` using `le_order_sub h2 h1`.

Establish `hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast Nat.lt_succ_of_le he`. Establish `h0` using `coeff_of_lt_order (hlt.trans_le h3)`. Rewrite `h0` using `[map_sub (MvPowerSeries.map σ), subst_sub (hasSubst_substEach hf0)]`. Simplify using `only [twistedDefect, map_sub, coeff_rescale_const, coeff_C_mul, coeff_map] at h0 ⊢`. Take the linear combination `h0`.
-/
theorem coeff_twistedDefect_sub_twistedDefect {φ ψ : MvPowerSeries ι B} {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (twistedDefect σ g f φ) - coeff e (twistedDefect σ g f ψ) =
      u * π * coeff e (dropConst φ - dropConst ψ) -
        π ^ e.degree * σ (coeff e (dropConst φ - dropConst ψ)) := by
  have hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ) := by
    refine nat_le_order fun d hd => ?_
    by_cases hd0 : d = 0
    · simp [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
    · rw [map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]
      exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  have hδσ : (n : ℕ∞) ≤ order (map σ (dropConst φ - dropConst ψ)) := hδ.trans (le_order_map σ)
  have h1 := le_order_subst_substEach_sub_rescale hf0 hf1 hδσ
  have h2 := le_order_subst_sub_subst_sub_C_mul hg0 hg1 (constantCoeff_dropConst φ)
    (constantCoeff_dropConst ψ) hδ
  have h3 := le_order_sub h2 h1
  have hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le he
  have h0 := coeff_of_lt_order (hlt.trans_le h3)
  rw [map_sub (MvPowerSeries.map σ), subst_sub (hasSubst_substEach hf0)] at h0
  simp only [twistedDefect, map_sub, coeff_rescale_const, coeff_C_mul, coeff_map] at h0 ⊢
  linear_combination h0

variable (hreg : ∀ x : B, π * x = 0 → x = 0)
  (hT : ∀ d : ℕ, 2 ≤ d → Function.Bijective (twistOp σ u π d))
  (hdiv : ∀ (φ : MvPowerSeries ι B) (e : ι →₀ ℕ), π ∣ coeff e (twistedDefect σ g f φ))

include hf0 hf1 hg0 hg1 hreg hdiv in
/- English proof (translation)
Use `nat_le_order fun e he => ?_` and prove the remaining obligations. Establish `he' : e.degree ≤ n` using `Nat.lt_succ_iff.1 he`. Rewrite using `[map_sub, coeff_twistStep, coeff_twistStep]`. Use `split_ifs with h1`. Conclude with `sub_self _`.

Use `replace h1 := not_le.1 h1`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h1`. Establish `hkey` using `coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h he'`.

Rewrite `hkey` using `[map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0, map_sub]`. Establish `hd : π * π ^ (e.degree - 1) = π ^ e.degree`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `harg : twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)) = twistOp σ u π e.degree (coeff e ψ) - divBy π (coeff e (twistedDefect σ g f ψ))`. Rewrite using `[← sub_eq_zero]`. Apply `hreg` to reduce the goal to its premises. Establish `e1` using `mul_divBy (hdiv φ e)`. Establish `e2` using `mul_divBy (hdiv ψ e)`.

Simplify using `only [twistOp]`. Take the linear combination `(-1 : B) * hkey - (σ (coeff e φ) - σ (coeff e ψ)) * hd - e1 + e2`. Rewrite using `[harg, sub_self]`.
-/
theorem twistStep_contract (ℓ φ ψ : MvPowerSeries ι B) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (twistStep σ u π g f ℓ φ - twistStep σ u π g f ℓ ψ) := by
  refine nat_le_order fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.1 he
  rw [map_sub, coeff_twistStep, coeff_twistStep]
  split_ifs with h1
  · exact sub_self _
  · replace h1 := not_le.1 h1
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at h1
    have hkey := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h he'
    rw [map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0, map_sub] at hkey
    have hd : π * π ^ (e.degree - 1) = π ^ e.degree := by
      rw [← pow_succ']
      congr 1
      omega
    have harg : twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)) =
        twistOp σ u π e.degree (coeff e ψ) - divBy π (coeff e (twistedDefect σ g f ψ)) := by
      rw [← sub_eq_zero]
      apply hreg
      have e1 := mul_divBy (hdiv φ e)
      have e2 := mul_divBy (hdiv ψ e)
      simp only [twistOp]
      linear_combination (-1 : B) * hkey - (σ (coeff e φ) - σ (coeff e ψ)) * hd - e1 + e2
    rw [harg, sub_self]

include hf0 hg0 in
/- English proof (translation)
Establish `h0 : dropConst (0 : MvPowerSeries ι B) = 0` using `by simp [dropConst]`. Rewrite using `[twistedDefect, h0, map_zero, ← coe_substAlgHom (hasSubst_substEach hf0), map_zero, PowerSeries.subst_zero_of_constantCoeff_zero hg0, sub_zero]`.
-/
theorem twistedDefect_zero : twistedDefect σ g f (0 : MvPowerSeries ι B) = 0 := by
  have h0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [twistedDefect, h0, map_zero, ← coe_substAlgHom (hasSubst_substEach hf0), map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero hg0, sub_zero]

omit [Finite ι] in

/- English proof (translation)
Establish `he2 : (e.degree : ℕ∞) < 2`. Establish `: e.degree < 2` using `by omega`. Conclude with `this` after adjusting the coercions. Use `coeff_of_lt_order (lt_of_lt_of_le he2 h)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem eq_coeff_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

omit [Finite ι] in
/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← eq_coeff_of_two_le_order_sub h (by simp), coeff_zero_eq_constantCoeff_apply, hφ]`.
-/
theorem constantCoeff_eq_zero_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) (hφ : constantCoeff φ = 0) : constantCoeff ψ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← eq_coeff_of_two_le_order_sub h (by simp),
    coeff_zero_eq_constantCoeff_apply, hφ]

include hf0 hf1 hg0 hg1 hreg hT hdiv in

/- English proof (translation)
Establish `hdivBy0 : divBy π 0 = 0` using `hreg _ (mul_divBy (dvd_zero π))`. Establish `hd0 : dropConst (0 : MvPowerSeries ι B) = 0` using `by simp [dropConst]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Establish `hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ`.

Introduce `e he`. Use `congrArg (coeff e) hs` as an intermediate fact. Rewrite `this` using `[coeff_twistStep, if_pos he]`. Conclude with `this.symm`. Establish `hφ0 : constantCoeff φ = 0`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp), coeff_zero_eq_constantCoeff_apply, hℓ]`. Establish `hdef : twistedDefect σ g f φ = 0`. Use extensionality with `e`. Rewrite using `[map_zero]`. Distinguish the cases in `he : e.degree ≤ 1`.

Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0)`. Rewrite using `[sub_zero, Nat.cast_one]`. Conclude with `one_le_order_iff_constCoeff_eq_zero.2 hφ0`. Use `coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he` as an intermediate fact. Rewrite `this` using `[twistedDefect_zero σ hf0 hg0, map_zero, sub_zero]`.

Rewrite using `[this]`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h` into its components or cases. Rewrite `h` using `[Finsupp.degree_eq_zero_iff]`. Substitute `h` using the available equality. Simplify using `[coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]`.

Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Rewrite using `[hd0, sub_zero, coeff_dropConst _ he0, h, pow_one, hlin e (by omega), hℓ1 e h, sub_self]`. Use `congrArg (coeff e) hs` as an intermediate fact.

Rewrite `this` using `[coeff_twistStep, if_neg he]`. Establish `hT'` using `hT e.degree (by omega)`. Establish `h2` using `congrArg (twistOp σ u π e.degree) this`. Rewrite `h2` using `[Function.invFun_eq (hT'.2 _)]`. Establish `hq : divBy π (coeff e (twistedDefect σ g f φ)) = 0`.

Take the linear combination `-h2`. Rewrite using `[← mul_divBy (hdiv φ e), hq, mul_zero]`. Establish `h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ)` using `nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]`. Use `⟨by exact_mod_cast h2, ?_⟩` and prove the remaining obligations. Rewrite `hdef` using `[twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero]`.

Conclude with `hdef`. Introduce and unpack `⟨h2, heq⟩`. Establish `hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ` using `fun e he => eq_coeff_of_two_le_order_sub h2 he`. Establish `hφ0 : constantCoeff φ = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp), coeff_zero_eq_constantCoeff_apply, hℓ]`.

Establish `hdef : twistedDefect σ g f φ = 0`. Rewrite using `[twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]`. Use extensionality with `e`. Rewrite using `[coeff_twistStep]`. Use `split_ifs with he`.

Conclude with `(hlin e he).symm`. Rewrite using `[hdef, map_zero, hdivBy0, sub_zero]`. Conclude with `Function.leftInverse_invFun (hT e.degree (by omega)).1 _`.
-/
theorem twistStep_eq_self_iff {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ))
    (φ : MvPowerSeries ι B) :
    twistStep σ u π g f ℓ φ = φ ↔
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  have hdivBy0 : divBy π 0 = 0 := hreg _ (mul_divBy (dvd_zero π))
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  constructor
  · intro hs
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have := congrArg (coeff e) hs
      rw [coeff_twistStep, if_pos he] at this
      exact this.symm
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      ext e
      rw [map_zero]
      by_cases he : e.degree ≤ 1
      · have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
          rw [sub_zero, Nat.cast_one]
          exact one_le_order_iff_constCoeff_eq_zero.2 hφ0
        have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he
        rw [twistedDefect_zero σ hf0 hg0, map_zero, sub_zero] at this
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
        · rw [Finsupp.degree_eq_zero_iff] at h
          subst h
          simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
        · have he0 : e ≠ 0 := by
            rintro rfl
            simp at h
          rw [hd0, sub_zero, coeff_dropConst _ he0, h, pow_one, hlin e (by omega), hℓ1 e h,
            sub_self]
      · have := congrArg (coeff e) hs
        rw [coeff_twistStep, if_neg he] at this
        have hT' := hT e.degree (by omega)
        have h2 := congrArg (twistOp σ u π e.degree) this
        rw [Function.invFun_eq (hT'.2 _)] at h2
        have hq : divBy π (coeff e (twistedDefect σ g f φ)) = 0 := by
          linear_combination -h2
        rw [← mul_divBy (hdiv φ e), hq, mul_zero]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ) :=
      nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero] at hdef
    exact hdef
  · rintro ⟨h2, heq⟩
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ :=
      fun e he => eq_coeff_of_two_le_order_sub h2 he
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]
    ext e
    rw [coeff_twistStep]
    split_ifs with he
    · exact (hlin e he).symm
    · rw [hdef, map_zero, hdivBy0, sub_zero]
      exact Function.leftInverse_invFun (hT e.degree (by omega)).1 _

include hf0 hf1 hg0 hg1 hreg hT hdiv in

/- English proof (translation)
Take `⟨φ, hφ, huniq⟩` from `existsUnique_fixedPoint (twistStep σ u π g f ℓ) (twistStep_contract σ hf0 hf1 hg0 hg1 hreg hdiv ℓ)`. Conclude with `⟨φ, (twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 φ).1 hφ, fun ψ hψ => huniq ψ ((twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 ψ).2 hψ)⟩`.
-/
theorem existsUnique_twisted {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ)) :
    ∃! φ : MvPowerSeries ι B,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_fixedPoint (twistStep σ u π g f ℓ)
    (twistStep_contract σ hf0 hf1 hg0 hg1 hreg hdiv ℓ)
  exact ⟨φ, (twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 φ).1 hφ,
    fun ψ hψ => huniq ψ ((twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 ψ).2 hψ)⟩

include hf0 hf1 hg0 hg1 in

/- English proof (translation)
Take `⟨h0, h2, heq⟩` from `h`. Establish `hdef : twistedDefect σ g f φ = 0`. Rewrite using `[twistedDefect, dropConst_of_constantCoeff_eq_zero h0, heq, sub_self]`. Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0)`. Rewrite using `[sub_zero, Nat.cast_one]`.

Conclude with `one_le_order_iff_constCoeff_eq_zero.2 h0`. Use `coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he.le` as an intermediate fact. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at he`.

Establish `hd0 : dropConst (0 : MvPowerSeries ι B) = 0` using `by simp [dropConst]`. Rewrite `this` using `[hdef, twistedDefect_zero σ hf0 hg0, map_zero, sub_zero, hd0, sub_zero, coeff_dropConst _ he0, he, pow_one, eq_coeff_of_two_le_order_sub h2 he.le]`. Take the linear combination `-this`.
-/
theorem IsTwistedLift.linear {ℓ φ : MvPowerSeries ι B} (h : IsTwistedLift σ g f ℓ φ)
    (e : ι →₀ ℕ) (he : e.degree = 1) : u * π * coeff e ℓ = π * σ (coeff e ℓ) := by
  obtain ⟨h0, h2, heq⟩ := h
  have hdef : twistedDefect σ g f φ = 0 := by
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero h0, heq, sub_self]
  have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
    rw [sub_zero, Nat.cast_one]
    exact one_le_order_iff_constCoeff_eq_zero.2 h0
  have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he.le
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [hdef, twistedDefect_zero σ hf0 hg0, map_zero, sub_zero, hd0, sub_zero, coeff_dropConst _ he0,
    he, pow_one, eq_coeff_of_two_le_order_sub h2 he.le] at this
  linear_combination -this

include hf0 hf1 hg0 hg1 hreg hT hdiv in

/- English proof (translation)
The claim follows from `(existsUnique_twisted σ hf0 hf1 hg0 hg1 hreg hT hdiv (constantCoeff_eq_zero_of_two_le_order_sub hφ.2.1 hφ.1) (hφ.linear σ hf0 hf1 hg0 hg1)).unique ⟨hφ.2.1, hφ.2.2⟩ ⟨hψ.2.1, hψ.2.2⟩`.
-/
theorem IsTwistedLift.unique {ℓ φ ψ : MvPowerSeries ι B} (hφ : IsTwistedLift σ g f ℓ φ)
    (hψ : IsTwistedLift σ g f ℓ ψ) : φ = ψ :=
  (existsUnique_twisted σ hf0 hf1 hg0 hg1 hreg hT hdiv
    (constantCoeff_eq_zero_of_two_le_order_sub hφ.2.1 hφ.1)
    (hφ.linear σ hf0 hf1 hg0 hg1)).unique ⟨hφ.2.1, hφ.2.2⟩ ⟨hψ.2.1, hψ.2.2⟩

end Twisted

section Composition

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι τ : Type*} [Finite ι] [Finite τ]
  {f g h : PowerSeries B}

/- English proof (translation)
Take `⟨hΦ0, hΦ2, hΦe⟩` from `hΦ`. Establish `hu0 : ∀ j, constantCoeff (u j) = 0` using `fun j => (hu j).1`. Establish `hus : HasSubst u` using `hasSubst_of_constantCoeff_zero hu0`. Establish `hℓ0 : constantCoeff ℓ = 0` using `constantCoeff_eq_zero_of_two_le_order_sub hΦ2 hΦ0`. Establish `hv0 : ∀ j, constantCoeff (v j) = 0` using `fun j => constantCoeff_eq_zero_of_two_le_order_sub (hu j).2.1 (hu0 j)`.

Use `⟨constantCoeff_subst_eq_zero hus hu0 hΦ0, two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩` and prove the remaining obligations. Establish `hΦs : PowerSeries.HasSubst Φ` using `PowerSeries.HasSubst.of_constantCoeff_zero hΦ0`. Establish `hmu : (fun i => map σ (u i)) = u` using `funext hσu`. Rewrite using `[← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hf0) hus, map_subst hus, hmu, subst_comp_subst_apply hus (hasSubst_substEach hh0)]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]`. Conclude with `(hu j).2.2`.
-/
theorem IsTwistedLift.comp_lift (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Φ : MvPowerSeries τ B}
    (hΦ : IsTwistedLift σ g f ℓ Φ) {v u : τ → MvPowerSeries ι B}
    (hu : ∀ j, IsLubinTateLift f h (v j) (u j)) (hσu : ∀ j, map σ (u j) = u j) :
    IsTwistedLift σ g h (subst v ℓ) (subst u Φ) := by
  obtain ⟨hΦ0, hΦ2, hΦe⟩ := hΦ
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => (hu j).1
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΦ2 hΦ0
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hu j).2.1 (hu0 j)
  refine ⟨constantCoeff_subst_eq_zero hus hu0 hΦ0,
    two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  have hmu : (fun i => map σ (u i)) = u := funext hσu
  rw [← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hf0) hus,
    map_subst hus, hmu, subst_comp_subst_apply hus (hasSubst_substEach hh0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]
  exact (hu j).2.2

/- English proof (translation)
Take `⟨hΨ0, hΨ2, hΨe⟩` from `hΨ`. Establish `hv0 : ∀ j, constantCoeff (v j) = 0` using `fun j => (hv j).1`. Establish `hvs : HasSubst v` using `hasSubst_of_constantCoeff_zero hv0`. Establish `hℓ0 : constantCoeff ℓ = 0` using `constantCoeff_eq_zero_of_two_le_order_sub hΨ2 hΨ0`. Establish `hw0 : ∀ j, constantCoeff (w j) = 0` using `fun j => constantCoeff_eq_zero_of_two_le_order_sub (hv j).2.1 (hv0 j)`.

Use `⟨constantCoeff_subst_eq_zero hvs hv0 hΨ0, two_le_order_subst_sub_subst_of hΨ2 hℓ0 hv0 hw0 (fun j => (hv j).2.1), ?_⟩` and prove the remaining obligations. Establish `hΨs : PowerSeries.HasSubst Ψ` using `PowerSeries.HasSubst.of_constantCoeff_zero hΨ0`. Establish `hσvs : HasSubst (fun j => MvPowerSeries.map σ (v j))` using `hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_map, hv0 j, map_zero]`. Rewrite using `[← subst_powerSeries_subst hΨs hvs, hΨe, subst_comp_subst_apply (hasSubst_substEach hh0) hvs, map_subst hvs, hσΨ, subst_comp_subst_apply hσvs (hasSubst_substEach hf0)]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hvs, subst_X hvs]`. Conclude with `(hv j).2.2`.
-/
theorem IsLubinTateLift.comp_twisted (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Ψ : MvPowerSeries τ B}
    (hΨ : IsLubinTateLift g h ℓ Ψ) (hσΨ : MvPowerSeries.map σ Ψ = Ψ) {w v : τ → MvPowerSeries ι B}
    (hv : ∀ j, IsTwistedLift σ h f (w j) (v j)) :
    IsTwistedLift σ g f (subst w ℓ) (subst v Ψ) := by
  obtain ⟨hΨ0, hΨ2, hΨe⟩ := hΨ
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j => (hv j).1
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΨ2 hΨ0
  have hw0 : ∀ j, constantCoeff (w j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hv j).2.1 (hv0 j)
  refine ⟨constantCoeff_subst_eq_zero hvs hv0 hΨ0,
    two_le_order_subst_sub_subst_of hΨ2 hℓ0 hv0 hw0 (fun j => (hv j).2.1), ?_⟩
  have hΨs : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero hΨ0
  have hσvs : HasSubst (fun j => MvPowerSeries.map σ (v j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_map, hv0 j, map_zero]
  rw [← subst_powerSeries_subst hΨs hvs, hΨe, subst_comp_subst_apply (hasSubst_substEach hh0) hvs,
    map_subst hvs, hσΨ, subst_comp_subst_apply hσvs (hasSubst_substEach hf0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hvs, subst_X hvs]
  exact (hv j).2.2

/- English proof (translation)
Take `⟨h0, h2, he⟩` from `hφ`. Use `⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `h2.trans (le_order_map σ)`. Use `congrArg (MvPowerSeries.map σ) he` as an intermediate fact.

Rewrite `this` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), hσg, map_subst (hasSubst_substEach hf0)]`. Rewrite using `[this]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[map_substEach σ f i, hσf]`.
-/
theorem IsTwistedLift.map (hf0 : PowerSeries.constantCoeff f = 0)
    (hσf : PowerSeries.map σ f = f) (hσg : PowerSeries.map σ g = g) {ℓ φ : MvPowerSeries ι B}
    (hφ : IsTwistedLift σ g f ℓ φ) : IsTwistedLift σ g f (map σ ℓ) (map σ φ) := by
  obtain ⟨h0, h2, he⟩ := hφ
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map σ)
  · have := congrArg (MvPowerSeries.map σ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), hσg,
      map_subst (hasSubst_substEach hf0)] at this
    rw [this]
    congr 1
    funext i
    rw [map_substEach σ f i, hσf]

end Composition

end GroundTheory.LocalField.FormalGroup
