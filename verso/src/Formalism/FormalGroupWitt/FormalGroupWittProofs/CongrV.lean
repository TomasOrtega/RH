import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne

noncomputable section

universe u v w

namespace Formalism.FG.CongrVAux

open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux

section Local

variable {R : Type u} [CommRing R] {τ : Type w}

def Zd (d : τ →₀ ℕ) (x : MvPowerSeries τ R) : Prop := ∀ e ≤ d, coeff e x = 0

/- English proof (translation)
Introduce `_ _` and use `by simp`.
-/
theorem zd_zero (d : τ →₀ ℕ) : Zd d (0 : MvPowerSeries τ R) := fun _ _ => by simp

/- English proof (translation)
Introduce `e he` and use `by rw [map_add, hx e he, hy e he, add_zero]`.
-/
theorem zd_add {d : τ →₀ ℕ} {x y : MvPowerSeries τ R} (hx : Zd d x) (hy : Zd d y) :
    Zd d (x + y) := fun e he => by rw [map_add, hx e he, hy e he, add_zero]

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun z hz => ?_` and prove the remaining obligations. Rewrite `hz` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `: z.2 ≤ e` using `hz ▸ le_add_self`.

Rewrite using `[hy _ (this.trans he), mul_zero]`.
-/
theorem zd_mul_left {d : τ →₀ ℕ} (x : MvPowerSeries τ R) {y : MvPowerSeries τ R} (hy : Zd d y) :
    Zd d (x * y) := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
  have : z.2 ≤ e := hz ▸ le_add_self
  rw [hy _ (this.trans he), mul_zero]

/- English proof (translation)
Establish `e : a * b - a' * b' = b * (a - a') + a' * (b - b')` using `by ring`. Rewrite using `[e]`. Conclude with `zd_add (zd_mul_left _ ha) (zd_mul_left _ hb)`.
-/
theorem zd_mul_sub {d : τ →₀ ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Zd d (a - a'))
    (hb : Zd d (b - b')) : Zd d (a * b - a' * b') := by
  have e : a * b - a' * b' = b * (a - a') + a' * (b - b') := by ring
  rw [e]
  exact zd_add (zd_mul_left _ ha) (zd_mul_left _ hb)

/- English proof (translation)
Proceed by induction on `e using Finsupp.induction_linear with`. Consider the case `zero => rw [P_zero, P_zero, sub_self]`. Conclude with `zd_zero _`. Consider the case `add e₁ e₂ h₁ h₂`. Rewrite using `[P_add, P_add]`.

Conclude with `zd_mul_sub h₁ h₂`. Consider the case `single i n`. Rewrite using `[P_single, P_single]`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, sub_self]`.

Conclude with `zd_zero _`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `zd_mul_sub ih (hkk i)`.
-/
theorem prod_pow_sub_of_forall_sub {ι : Type v} {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hkk : ∀ i, Zd d (k i - k' i)) (e : ι →₀ ℕ) : Zd d (P k e - P k' e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, P_zero, sub_self]; exact zd_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, P_add]; exact zd_mul_sub h₁ h₂
  | single i n =>
    rw [P_single, P_single]
    induction n with
    | zero => rw [pow_zero, pow_zero, sub_self]; exact zd_zero _
    | succ n ih => rw [pow_succ, pow_succ]; exact zd_mul_sub ih (hkk i)

/- English proof (translation)
Rewrite using `[coeff_subst (hasSubst_of_constantCoeff_zero hk), coeff_subst (hasSubst_of_constantCoeff_zero hk')]`. Use `finsum_congr fun e => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hz : ∀ i, Zd d (k i - k' i)` using `fun i e he => by rw [map_sub, hkk i e he, sub_self]`. Use `prod_pow_sub_of_forall_sub hz e d le_rfl` as an intermediate fact.

Rewrite `this` using `[map_sub, sub_eq_zero]`. Simplify `this` using `only [P]`.
-/
theorem coeff_subst_local {ι : Type v} [Finite ι] {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, constantCoeff (k i) = 0) (hk' : ∀ i, constantCoeff (k' i) = 0)
    (hkk : ∀ i, ∀ e ≤ d, coeff e (k i) = coeff e (k' i)) (g : MvPowerSeries ι R) :
    coeff d (subst k g) = coeff d (subst k' g) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hk), coeff_subst (hasSubst_of_constantCoeff_zero hk')]
  refine finsum_congr fun e => ?_
  congr 1
  have hz : ∀ i, Zd d (k i - k' i) := fun i e he => by rw [map_sub, hkk i e he, sub_self]
  have := prod_pow_sub_of_forall_sub hz e d le_rfl
  rw [map_sub, sub_eq_zero] at this
  simpa only [P] using this

/- English proof (translation)
Use `set k' : ι → MvPowerSeries τ R := fun i => k i + monomial d (c i) with hk'def`. Establish `hm0 : ∀ i, constantCoeff (monomial d (c i) : MvPowerSeries τ R) = 0` using `fun i => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_monomial_ne (Ne.symm hd)]`. Establish `hk'0 : ∀ i, constantCoeff (k' i) = 0` using `fun i => by`. Simplify using `only [hk'def, map_add, hk i, hm0 i, add_zero]`.

Establish `hs` using `hasSubst_of_constantCoeff_zero hk`. Establish `hs'` using `hasSubst_of_constantCoeff_zero hk'0`. Establish `hdiff : ∀ i, k' i - k i = monomial d (c i)` using `fun i => by simp [hk'def]`. Establish `hlow : ∀ i, Low d.degree (k' i - k i)` using `fun i e he => by`. Rewrite using `[hdiff i, coeff_monomial_ne]`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ he`. Establish `hT : ∀ e : ι →₀ ℕ, coeff e g • coeff d (e.prod fun s n => k' s ^ n) - coeff e g • coeff d (e.prod fun s n => k s ^ n) = if e ∈ Finset.univ.image (fun i => Finsupp.single i 1) then coeff e g • coeff d (e.prod fun s n => k' s ^ n) - coeff e g • coeff d (e.prod fun s n => k s ^ n) e …`. Introduce `e`. Use `split_ifs with he`.

Both sides reduce to the same expression. Rewrite using `[← smul_sub, ← map_sub]`. Break down `Nat.lt_or_ge e.degree 2 with h2 | h2` into its components or cases. Break down `Nat.lt_or_ge e.degree 1 with h1 | h1` into its components or cases. Establish `: e = 0` using `(Finsupp.degree_eq_zero_iff e).1 (by omega)`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules. Take `⟨i, rfl⟩` from `degree_eq_one e (by omega)`. Conclude with `absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) he`. Use `low_pow_sub_succ (fun i => (low_one_iff _).2 (hk'0 i)) (fun i => (low_one_iff _).2 (hk i)) hlow e h2 d (by omega)` as an intermediate fact.

Simplify using `only [P] at this`. Rewrite using `[this, smul_zero]`. Establish `hsum : coeff d (subst k' g) - coeff d (subst k g) = ∑ i, coeff (Finsupp.single i 1) g * c i`. Rewrite using `[coeff_subst hs', coeff_subst hs, ← finsum_sub_distrib (coeff_subst_finite hs' g d) (coeff_subst_finite hs g d), finsum_congr hT, finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i => Finsupp.single i 1))]`. Rewrite using `[Finset.sum_ite_of_true (fun _ h => h), Finset.sum_image]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub, ← map_sub]`. Express the relevant statement in the definitionally equal form `coeff _ g • coeff d (P k' (Finsupp.single i 1) - P k (Finsupp.single i 1)) = _`. Rewrite using `[P_single, P_single, pow_one, pow_one, hdiff i, coeff_monomial_same, smul_eq_mul]`. Introduce `i _ j _ hij`.

Conclude with `Finsupp.single_left_injective one_ne_zero hij`. Introduce `e he`. Simplify using `only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at he`. Take `⟨h, _⟩` from `he`. Conclude with `h`.

Take the linear combination `hsum`.
-/
theorem coeff_subst_perturb {ι : Type v} [Fintype ι] {d : τ →₀ ℕ} (hd : d ≠ 0)
    {k : ι → MvPowerSeries τ R} (hk : ∀ i, constantCoeff (k i) = 0) (c : ι → R)
    (g : MvPowerSeries ι R) :
    coeff d (subst (fun i => k i + monomial d (c i)) g) =
      coeff d (subst k g) + ∑ i, coeff (Finsupp.single i 1) g * c i := by
  classical
  set k' : ι → MvPowerSeries τ R := fun i => k i + monomial d (c i) with hk'def
  have hm0 : ∀ i, constantCoeff (monomial d (c i) : MvPowerSeries τ R) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial_ne (Ne.symm hd)]
  have hk'0 : ∀ i, constantCoeff (k' i) = 0 := fun i => by
    simp only [hk'def, map_add, hk i, hm0 i, add_zero]
  have hs := hasSubst_of_constantCoeff_zero hk
  have hs' := hasSubst_of_constantCoeff_zero hk'0
  have hdiff : ∀ i, k' i - k i = monomial d (c i) := fun i => by simp [hk'def]
  have hlow : ∀ i, Low d.degree (k' i - k i) := fun i e he => by
    rw [hdiff i, coeff_monomial_ne]
    rintro rfl; exact lt_irrefl _ he
  have hT : ∀ e : ι →₀ ℕ, coeff e g • coeff d (e.prod fun s n => k' s ^ n) -
      coeff e g • coeff d (e.prod fun s n => k s ^ n) =
      if e ∈ Finset.univ.image (fun i => Finsupp.single i 1) then
        coeff e g • coeff d (e.prod fun s n => k' s ^ n) -
          coeff e g • coeff d (e.prod fun s n => k s ^ n) else 0 := by
    intro e
    split_ifs with he
    · rfl
    rw [← smul_sub, ← map_sub]
    rcases Nat.lt_or_ge e.degree 2 with h2 | h2
    · rcases Nat.lt_or_ge e.degree 1 with h1 | h1
      · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        subst this
        simp
      · obtain ⟨i, rfl⟩ := degree_eq_one e (by omega)
        exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) he
    · have := low_pow_sub_succ (fun i => (low_one_iff _).2 (hk'0 i)) (fun i => (low_one_iff _).2 (hk i))
        hlow e h2 d (by omega)
      simp only [P] at this
      rw [this, smul_zero]
  have hsum : coeff d (subst k' g) - coeff d (subst k g) =
      ∑ i, coeff (Finsupp.single i 1) g * c i := by
    rw [coeff_subst hs', coeff_subst hs,
      ← finsum_sub_distrib (coeff_subst_finite hs' g d) (coeff_subst_finite hs g d),
      finsum_congr hT, finsum_eq_sum_of_support_subset _
        (s := Finset.univ.image (fun i => Finsupp.single i 1))]
    · rw [Finset.sum_ite_of_true (fun _ h => h), Finset.sum_image]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← smul_sub, ← map_sub]
        change coeff _ g • coeff d (P k' (Finsupp.single i 1) - P k (Finsupp.single i 1)) = _
        rw [P_single, P_single, pow_one, pow_one, hdiff i, coeff_monomial_same, smul_eq_mul]
      · intro i _ j _ hij
        exact Finsupp.single_left_injective one_ne_zero hij
    · intro e he
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at he
      obtain ⟨h, _⟩ := he
      exact h
  linear_combination hsum

end Local

section Norm

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Simplify using `using IsUltrametricDist.norm_add_le_max a (-b)`.
-/
theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)

/- English proof (translation)
Distinguish the cases in `hg : (Function.support g).Finite`. Rewrite using `[finsum_eq_sum g hg]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun e _ => h e`. Rewrite using `[finsum_of_infinite_support hg, norm_zero]`. Conclude with `hC`.
-/
theorem norm_finsum_le {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (h : ∀ e, ‖g e‖ ≤ C) :
    ‖∑ᶠ e, g e‖ ≤ C := by
  by_cases hg : (Function.support g).Finite
  · rw [finsum_eq_sum g hg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun e _ => h e
  · rw [finsum_of_infinite_support hg, norm_zero]; exact hC

/- English proof (translation)
Establish `e : a * b - a' * b' = (a - a') * b + a' * (b - b')` using `by ring`. Introduce `d`. Rewrite using `[e, map_add]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Simplify using `using (Formalism.LT.CoeffP.Bd.mul hab hb (norm_nonneg c) zero_le_one) d`.

Simplify using `using (Formalism.LT.CoeffP.Bd.mul ha' hbb zero_le_one (norm_nonneg c)) d`.
-/
theorem divBy_mul_sub {c : K} {a a' b b' : MvPowerSeries τ K} (ha' : IntegralMv a')
    (hb : IntegralMv b) (hab : DivByMv c (a - a')) (hbb : DivByMv c (b - b')) :
    DivByMv c (a * b - a' * b') := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  intro d
  rw [e, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · simpa using (Formalism.LT.CoeffP.Bd.mul hab hb (norm_nonneg c) zero_le_one) d
  · simpa using (Formalism.LT.CoeffP.Bd.mul ha' hbb zero_le_one (norm_nonneg c)) d

/- English proof (translation)
The claim follows from `Finset.prod_induction _ (fun y => IntegralMv y) (fun _ _ h₁ h₂ => IntegralSubstitution.integral_mul h₁ h₂) IntegralSubstitution.integral_one (fun i _ => hx i)`.
-/
theorem integral_prod {ι : Type v} (s : Finset ι) (x : ι → MvPowerSeries τ K)
    (hx : ∀ i, IntegralMv (x i)) : IntegralMv (∏ i ∈ s, x i) :=
  Finset.prod_induction _ (fun y => IntegralMv y) (fun _ _ h₁ h₂ => IntegralSubstitution.integral_mul h₁ h₂)
    IntegralSubstitution.integral_one (fun i _ => hx i)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro d`. Simplify using the standard rewrite rules. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi]`.

Conclude with `divBy_mul_sub (IntegralSubstitution.integral_pow (hb i) _) (integral_prod s _ fun j => IntegralSubstitution.integral_pow (ha j) _) (h i) ih`.
-/
theorem divBy_prod_sub {ι : Type v} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, IntegralMv (a i)) (hb : ∀ i, IntegralMv (b i)) (n : ι → ℕ)
    (h : ∀ i, DivByMv c (a i ^ n i - b i ^ n i)) (s : Finset ι) :
    DivByMv c (∏ i ∈ s, a i ^ n i - ∏ i ∈ s, b i ^ n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro d; simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact divBy_mul_sub (IntegralSubstitution.integral_pow (hb i) _)
      (integral_prod s _ fun j => IntegralSubstitution.integral_pow (ha j) _) (h i) ih

/- English proof (translation)
Introduce `d`. Establish `hsα` using `hasSubst_of_constantCoeff_zero hα0`. Establish `hsβ` using `hasSubst_of_constantCoeff_zero hβ0`. Rewrite using `[map_sub, coeff_subst hsα, coeff_subst hsβ, ← finsum_sub_distrib (coeff_subst_finite hsα _ d) (coeff_subst_finite hsβ _ d)]`. Use `norm_finsum_le (norm_nonneg _) fun e => ?_` and prove the remaining obligations.

Rewrite using `[← smul_sub, ← map_sub, smul_eq_mul, norm_mul]`. Take `⟨k, hk, hkb⟩` from `coeff_bound_vector K p q hq σ hS ι M hM ι f hf0 hfe j e`. Take `⟨h, hh0, hqh⟩` from `hS.2.1`. Use `choose m hm using hk`. Establish `hp1 : ‖(p : K)‖ ≤ 1` using `hS.2.2.1.le`.

Establish `hpow : ∀ i, DivByMv ((p : K) ^ (r + h * k)) (α i ^ e i - β i ^ e i)`. Introduce `i`. Rewrite using `[hm i, hqh, ← pow_mul]`. Conclude with `PowCongr_valid K τ p hS.1 (α i) (β i) (hα i) (hβ i) r hr (hd i) (h * k) (m i)`. Establish `hpc` using `divBy_prod_sub hα hβ e hpow e.support d`.

Establish `hpc' : ‖coeff d ((e.prod fun s n => α s ^ n) - e.prod fun s n => β s ^ n)‖ ≤ ‖(p : K)‖ ^ (r + h * k)`. Simplify `hpc` using `only [Finsupp.prod, norm_pow]`. Establish `hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r`. Rewrite using `[pow_add, mul_comm]`. Apply `mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)` to reduce the goal to its premises.

Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fwd [CharZero K] {p q : ℕ} {hq : q ≠ 0} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ)
    {ι : Type v} [Fintype ι] {M : ι → ι → K} (hM : IntegralMat M) {f : ι → MvPowerSeries ι K}
    (hf0 : ∀ j, constantCoeff (f j) = 0) (hfe : IsFunEqTypeV p q hq σ M f)
    {α β : ι → MvPowerSeries τ K} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hβ0 : ∀ i, constantCoeff (β i) = 0) (hα : ∀ i, IntegralMv (α i)) (hβ : ∀ i, IntegralMv (β i))
    {r : ℕ} (hr : 1 ≤ r) (hd : ∀ i, DivByMv ((p : K) ^ r) (α i - β i)) (j : ι) :
    DivByMv ((p : K) ^ r) (subst α (f j) - subst β (f j)) := by
  intro d
  have hsα := hasSubst_of_constantCoeff_zero hα0
  have hsβ := hasSubst_of_constantCoeff_zero hβ0
  rw [map_sub, coeff_subst hsα, coeff_subst hsβ,
    ← finsum_sub_distrib (coeff_subst_finite hsα _ d) (coeff_subst_finite hsβ _ d)]
  refine norm_finsum_le (norm_nonneg _) fun e => ?_
  rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul]
  obtain ⟨k, hk, hkb⟩ := coeff_bound_vector K p q hq σ hS ι M hM ι f hf0 hfe j e
  obtain ⟨h, hh0, hqh⟩ := hS.2.1
  choose m hm using hk
  have hp1 : ‖(p : K)‖ ≤ 1 := hS.2.2.1.le
  have hpow : ∀ i, DivByMv ((p : K) ^ (r + h * k)) (α i ^ e i - β i ^ e i) := by
    intro i
    rw [hm i, hqh, ← pow_mul]
    exact PowCongr_valid K τ p hS.1 (α i) (β i) (hα i) (hβ i) r hr (hd i) (h * k) (m i)
  have hpc := divBy_prod_sub hα hβ e hpow e.support d
  have hpc' : ‖coeff d ((e.prod fun s n => α s ^ n) - e.prod fun s n => β s ^ n)‖ ≤
      ‖(p : K)‖ ^ (r + h * k) := by
    simpa only [Finsupp.prod, norm_pow] using hpc
  have hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r := by
    rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    exact pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)
  calc ‖coeff e (f j)‖ * ‖coeff d ((e.prod fun s n => α s ^ n) - e.prod fun s n => β s ^ n)‖
      ≤ ‖coeff e (f j)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hpc'.trans hkk) (norm_nonneg _)
    _ = (‖coeff e (f j)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ ^ r := by ring
    _ ≤ 1 * ‖(p : K)‖ ^ r := mul_le_mul_of_nonneg_right hkb (pow_nonneg (norm_nonneg _) _)
    _ = ‖(p : K) ^ r‖ := by rw [one_mul, norm_pow]

/- English proof (translation)
Establish `h2 : (d - e).degree ≠ 0`. Rewrite using `[Ne, Finsupp.degree_eq_zero_iff]`. Introduce `h`. Conclude with `hne (le_antisymm hle (tsub_eq_zero_iff_le.mp h))`. Establish `h3 : d.degree = e.degree + (d - e).degree` using `by conv_lhs => rw [← add_tsub_cancel_of_le hle]`.

Conclude with `map_add _ _ _`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_lt_of_le_of_ne {e d : τ →₀ ℕ} (hle : e ≤ d) (hne : e ≠ d) :
    e.degree < d.degree := by
  have h2 : (d - e).degree ≠ 0 := by
    rw [Ne, Finsupp.degree_eq_zero_iff]
    intro h
    exact hne (le_antisymm hle (tsub_eq_zero_iff_le.mp h))
  have h3 : d.degree = e.degree + (d - e).degree := by
    conv_lhs => rw [← add_tsub_cancel_of_le hle]
    exact map_add _ _ _
  omega

def ofFun (g : (τ →₀ ℕ) → K) : MvPowerSeries τ K := g

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_ofFun (g : (τ →₀ ℕ) → K) (e : τ →₀ ℕ) : coeff e (ofFun g) = g e := rfl

/- English proof (translation)
Establish `key : ∀ N : ℕ, ∀ d : τ →₀ ℕ, d.degree = N → ∀ i, ‖coeff d (α i - β i)‖ ≤ ‖(p : K) ^ r‖`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `d hdN`.

Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `: d = 0` using `(Finsupp.degree_eq_zero_iff d).1 hdN`. Substitute `this` using the available equality. Introduce `i`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]`.

Conclude with `norm_nonneg _`. Establish `hd0 : d ≠ 0` using `by rintro rfl; simp at hdN; omega`. Use `set c : ι → K := fun i => coeff d (α i - β i) with hc`. Establish `hc1 : ∀ i, ‖c i‖ ≤ 1` using `fun i => by`. Simplify using `only [hc, map_sub]`.

Conclude with `(norm_sub_le_max' _ _).trans (max_le (hα i d) (hβ i d))`. Use `set β₁ : ι → MvPowerSeries τ K := fun i => β i + monomial d (c i) with hβ₁`. Establish `hcβ₁ : ∀ i e, coeff e (β₁ i) = coeff e (β i) + if e = d then c i else 0`. Introduce `i e`. Simplify using `only [hβ₁, map_add, coeff_monomial]`.

Establish `hβ₁0 : ∀ i, constantCoeff (β₁ i) = 0` using `fun i => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hcβ₁, if_neg (Ne.symm hd0), add_zero, coeff_zero_eq_constantCoeff_apply, hβ0]`. Establish `hβ₁i : ∀ i, IntegralMv (β₁ i)` using `fun i e => by`. Rewrite using `[hcβ₁]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ i e) ?_)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hc1 i`. Simplify using the standard rewrite rules. Use `set α' : ι → MvPowerSeries τ K := fun i => ofFun fun e => if e ≤ d then coeff e (α i) else coeff e (β₁ i) with hα'`. Establish `hcα' : ∀ i e, coeff e (α' i) = if e ≤ d then coeff e (α i) else coeff e (β₁ i)` using `fun i e => coeff_ofFun _ e`.

Establish `hα'0 : ∀ i, constantCoeff (α' i) = 0` using `fun i => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hcα', if_pos zero_le, coeff_zero_eq_constantCoeff_apply, hα0]`. Establish `hα'i : ∀ i, IntegralMv (α' i)` using `fun i e => by`. Rewrite using `[hcα']`. Use `split_ifs`.

Conclude with `hα i e`. Conclude with `hβ₁i i e`. Establish `hdiv : ∀ i, DivByMv ((p : K) ^ r) (α' i - β₁ i)` using `fun i e => by`. Rewrite using `[map_sub, hcα']`. Use `split_ifs with hle`.

Rewrite using `[hcβ₁]`. Distinguish the cases in `hed : e = d`. Substitute `hed` using the available equality. Rewrite using `[if_pos rfl, hc]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hed, add_zero, ← map_sub]`. Conclude with `ih e.degree (hdN ▸ degree_lt_of_le_of_ne hle hed) e rfl i`. Simplify using the standard rewrite rules. Introduce `j`. Establish `hf'` using `fwd hS hM hf.1 hfe hα'0 hβ₁0 hα'i hβ₁i hr hdiv j d`.

Rewrite `hf'` using `[map_sub, coeff_subst_local hα'0 hα0 (fun i e he => by rw [hcα', if_pos he]) (f j)]`. Establish `hpert` using `coeff_subst_perturb hd0 hβ0 c (f j)`. Simplify using `only [hf.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hpert`. Rewrite `hpert` using `[← hβ₁]`. Rewrite `hf'` using `[hpert]`.

Establish `hA` using `hd j d`. Rewrite `hA` using `[map_sub]`. Establish `: coeff d (α j - β j) = (coeff d (subst α (f j)) - coeff d (subst β (f j))) - (coeff d (subst α (f j)) - (coeff d (subst β (f j)) + c j))`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `(norm_sub_le_max' _ _).trans (max_le hA hf')`. Introduce `i d`. Conclude with `key _ d rfl i`.
-/
theorem bwd [CharZero K] {p q : ℕ} {hq : q ≠ 0} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ)
    {ι : Type v} [Fintype ι] [DecidableEq ι] {M : ι → ι → K} (hM : IntegralMat M)
    {f : ι → MvPowerSeries ι K} (hf : IsIdMod2 f) (hfe : IsFunEqTypeV p q hq σ M f)
    {α β : ι → MvPowerSeries τ K} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hβ0 : ∀ i, constantCoeff (β i) = 0) (hα : ∀ i, IntegralMv (α i)) (hβ : ∀ i, IntegralMv (β i))
    {r : ℕ} (hr : 1 ≤ r) (hd : ∀ j, DivByMv ((p : K) ^ r) (subst α (f j) - subst β (f j))) :
    ∀ i, DivByMv ((p : K) ^ r) (α i - β i) := by
  classical
  have key : ∀ N : ℕ, ∀ d : τ →₀ ℕ, d.degree = N → ∀ i,
      ‖coeff d (α i - β i)‖ ≤ ‖(p : K) ^ r‖ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro d hdN
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 hdN
      subst this
      intro i
      rw [coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]
      exact norm_nonneg _
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdN; omega
    set c : ι → K := fun i => coeff d (α i - β i) with hc
    have hc1 : ∀ i, ‖c i‖ ≤ 1 := fun i => by
      simp only [hc, map_sub]; exact (norm_sub_le_max' _ _).trans (max_le (hα i d) (hβ i d))
    set β₁ : ι → MvPowerSeries τ K := fun i => β i + monomial d (c i) with hβ₁
    have hcβ₁ : ∀ i e, coeff e (β₁ i) = coeff e (β i) + if e = d then c i else 0 := by
      intro i e
      simp only [hβ₁, map_add, coeff_monomial]
    have hβ₁0 : ∀ i, constantCoeff (β₁ i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hcβ₁, if_neg (Ne.symm hd0), add_zero,
        coeff_zero_eq_constantCoeff_apply, hβ0]
    have hβ₁i : ∀ i, IntegralMv (β₁ i) := fun i e => by
      rw [hcβ₁]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ i e) ?_)
      split_ifs
      · exact hc1 i
      · simp
    set α' : ι → MvPowerSeries τ K :=
      fun i => ofFun fun e => if e ≤ d then coeff e (α i) else coeff e (β₁ i) with hα'
    have hcα' : ∀ i e, coeff e (α' i) = if e ≤ d then coeff e (α i) else coeff e (β₁ i) :=
      fun i e => coeff_ofFun _ e
    have hα'0 : ∀ i, constantCoeff (α' i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hcα', if_pos zero_le,
        coeff_zero_eq_constantCoeff_apply, hα0]
    have hα'i : ∀ i, IntegralMv (α' i) := fun i e => by
      rw [hcα']
      split_ifs
      · exact hα i e
      · exact hβ₁i i e
    have hdiv : ∀ i, DivByMv ((p : K) ^ r) (α' i - β₁ i) := fun i e => by
      rw [map_sub, hcα']
      split_ifs with hle
      · rw [hcβ₁]
        by_cases hed : e = d
        · subst hed
          rw [if_pos rfl, hc]
          simp
        · rw [if_neg hed, add_zero, ← map_sub]
          exact ih e.degree (hdN ▸ degree_lt_of_le_of_ne hle hed) e rfl i
      · simp
    intro j
    have hf' := fwd hS hM hf.1 hfe hα'0 hβ₁0 hα'i hβ₁i hr hdiv j d
    rw [map_sub, coeff_subst_local hα'0 hα0 (fun i e he => by rw [hcα', if_pos he]) (f j)] at hf'
    have hpert := coeff_subst_perturb hd0 hβ0 c (f j)
    simp only [hf.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hpert
    rw [← hβ₁] at hpert
    rw [hpert] at hf'
    have hA := hd j d
    rw [map_sub] at hA
    have : coeff d (α j - β j) = (coeff d (subst α (f j)) - coeff d (subst β (f j))) -
        (coeff d (subst α (f j)) - (coeff d (subst β (f j)) + c j)) := by
      rw [hc]; ring
    rw [this]
    exact (norm_sub_le_max' _ _).trans (max_le hA hf')
  intro i d
  exact key _ d rfl i

end Norm

end Formalism.FG.CongrVAux
