import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivCoeffOptionEquivLeft
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GaugeCoef

open scoped BigOperators
open Classical MvPowerSeries Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLaw.AddCurve GlobalTheory.CurveJet GlobalTheory.PlaceProj

variable {C : Type} [Field C]

/- English proof (translation)
Establish `hmul : ∀ f f' g g' : MvPowerSeries τ C, (∀ ν ∈ S, coeff ν f = coeff ν f') → (∀ ν ∈ S, coeff ν g = coeff ν g') → ∀ ν ∈ S, coeff ν (f * g) = coeff ν (f' * g')`. Introduce `f f' g g' hf hg ν hν`. Rewrite using `[coeff_mul, coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p.1 + p.2 = ν` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`.

Rewrite using `[hf p.1 (hS (hp' ▸ le_self_add) hν), hg p.2 (hS (hp' ▸ le_add_self) hν)]`. Establish `hpow : ∀ s n, ∀ ν ∈ S, coeff ν (a s ^ n) = coeff ν (b s ^ n)`. Introduce `s n`. Proceed by induction on `n with`. Consider the case `zero => intro ν _`.

Simplify using the standard rewrite rules. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `hmul _ _ _ _ ih (hab s)`. Introduce `ν hν`. Rewrite using `[coeff_subst (hasSubst_of_constantCoeff_zero ha), coeff_subst (hasSubst_of_constantCoeff_zero hb)]`.

Use `finsum_congr fun e => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `Finsupp.prod`. Use `revert ν`. Proceed by induction on `e.support using Finset.induction_on with`.

Consider the case `empty => intro ν _`. Simplify using the standard rewrite rules. Consider the case `insert s t hs ih`. Rewrite using `[Finset.prod_insert hs, Finset.prod_insert hs]`. Conclude with `hmul _ _ _ _ (hpow s _) ih`.
-/
theorem subst_congr {σ τ : Type} [Finite σ] {S : Set (τ →₀ ℕ)} (hS : IsLowerSet S) {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hab : ∀ s, ∀ ν ∈ S, coeff ν (a s) = coeff ν (b s)) (F : MvPowerSeries σ C) :
    ∀ ν ∈ S, coeff ν (subst a F) = coeff ν (subst b F) := by
  have hmul : ∀ f f' g g' : MvPowerSeries τ C, (∀ ν ∈ S, coeff ν f = coeff ν f') →
      (∀ ν ∈ S, coeff ν g = coeff ν g') → ∀ ν ∈ S, coeff ν (f * g) = coeff ν (f' * g') := by
    intro f f' g g' hf hg ν hν
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [hf p.1 (hS (hp' ▸ le_self_add) hν), hg p.2 (hS (hp' ▸ le_add_self) hν)]
  have hpow : ∀ s n, ∀ ν ∈ S, coeff ν (a s ^ n) = coeff ν (b s ^ n) := by
    intro s n
    induction n with
    | zero => intro ν _; simp
    | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih (hab s)
  intro ν hν
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha), coeff_subst (hasSubst_of_constantCoeff_zero hb)]
  refine finsum_congr fun e => ?_
  congr 1
  unfold Finsupp.prod
  revert ν
  induction e.support using Finset.induction_on with
  | empty => intro ν _; simp
  | insert s t hs ih =>
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact hmul _ _ _ _ (hpow s _) ih

/- English proof (translation)
Introduce `μ` and use `by rw [coeff_coeff_optionEquivLeft] exact hF _`.
-/
theorem intS_iff_coeff {V : VF C} {σ : Type} {F : MvPowerSeries (Option σ) C} (hF : IntS V F) (n : ℕ) :
    IntS V (PowerSeries.coeff n (optionEquivLeft σ C F)) := fun μ => by
  rw [coeff_coeff_optionEquivLeft]
  exact hF _

/- English proof (translation)
Introduce `μ` and use `by rw [map_sum] exact VF.Ge.sum fun i hi => h i hi μ`.
-/
theorem intS_sum {V : VF C} {σ ι : Type} {s : Finset ι} {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (f i)) :
    IntS V (∑ i ∈ s, f i) := fun μ => by
  rw [map_sum]
  exact VF.Ge.sum fun i hi => h i hi μ

/- English proof (translation)
Establish `h0 : V.v ((k.factorial : ℤ) : C) = 0`. Use `GlobalTheory.EmbSep.v_intCast_eq_zero V ?_` and prove the remaining obligations. Rewrite using `[Int.natCast_dvd_natCast, V.l_prime.dvd_factorial]`. Use linear arithmetic over natural numbers and integers. Rewrite `h0` using `[Int.cast_natCast]`.

Establish `hne : (k.factorial : C) ≠ 0`. Introduce `h`. Rewrite `h0` using `[h, V.v.map_zero]`. Conclude with `WithTop.top_ne_zero h0`. Use `ge_of_unit_mul h0 ?_` and prove the remaining obligations.

Rewrite using `[mul_div_cancel₀ _ hne]` and apply the resulting hypothesis.
-/
theorem ge_div_factorial (V : VF C) {k : ℕ} (hk : k < V.l) {x : C} (hx : V.Ge 0 x) :
    V.Ge 0 (x / (k.factorial : C)) := by
  have h0 : V.v ((k.factorial : ℤ) : C) = 0 := by
    refine GlobalTheory.EmbSep.v_intCast_eq_zero V ?_
    rw [Int.natCast_dvd_natCast, V.l_prime.dvd_factorial]
    omega
  rw [Int.cast_natCast] at h0
  have hne : (k.factorial : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at h0
    exact WithTop.top_ne_zero h0
  refine ge_of_unit_mul h0 ?_
  rwa [mul_div_cancel₀ _ hne]

/- English proof (translation)
Use `set g := optionEquivLeft σ C G with hg`. Establish `hz : IntS V (0 : MvPowerSeries σ C)` using `fun μ => by rw [map_zero]; exact VF.Ge.zero 0`. Establish `hdvd : ∀ k n, n < 2 * k → PowerSeries.coeff n (g ^ k) = 0` using `fun k => by`. Rewrite using `[← PowerSeries.X_pow_dvd_iff, pow_mul]`. Conclude with `pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 h2) k`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn`. Distinguish the cases in `hn2 : n < 2`.

Rewrite using `[h2 n hn2]`. Conclude with `hz`. Establish `hP : ∀ k, ∀ m < n, IntS V (PowerSeries.coeff m (g ^ k))`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `m _`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`. Use `split_ifs`. Use `exacts [intS_one, hz]`.

Consider the case `succ k ihk`. Introduce `m hm`. Rewrite using `[pow_succ, PowerSeries.coeff_mul]`. Use `intS_sum fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p.1 + p.2 = m` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`.

Conclude with `intS_mul (ihk _ (by omega)) (ih _ (by omega) (by omega))`. Establish `hQ : ∀ k, k ≠ 1 → IntS V (PowerSeries.coeff n (g ^ k))`. Introduce `k hk`. Break down `k with _ | _ | k` into its components or cases. Rewrite using `[pow_zero, PowerSeries.coeff_one, if_neg (by omega)]; exact hz`.

Conclude with `absurd rfl hk`. Rewrite using `[pow_succ, PowerSeries.coeff_mul]`. Use `intS_sum fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p.1 + p.2 = n` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Distinguish the cases in `h1 : p.1 = 0`.

Rewrite using `[hdvd (k + 1) p.1 (by omega), zero_mul]; exact hz`. Distinguish the cases in `h1' : p.2 = 0`. Rewrite using `[h2 p.2 (by omega), mul_zero]; exact hz`. Conclude with `intS_mul (hP _ _ (by omega)) (ih _ (by omega) (by omega))`. Introduce `μ`.

Establish `hEm` using `hE (μ.optionElim n)`. Establish `hdeg : n ≤ (μ.optionElim n).degree`. Simplify using `using Finsupp.le_degree none (μ.optionElim n)`. Establish `h1 : 1 ∈ Finset.range ((μ.optionElim n).degree + 1)` using `Finset.mem_range.2 (by omega)`. Express the relevant statement in the definitionally equal form `V.Ge 0 (∑ k ∈ Finset.range ((μ.optionElim n).degree + 1), coeff (μ.optionElim n) (G ^ k) / (k.factorial : C)) at hEm`.

Rewrite `hEm` using `[← Finset.add_sum_erase _ _ h1]`. Establish `hrest : V.Ge 0 (∑ k ∈ (Finset.range ((μ.optionElim n).degree + 1)).erase 1, coeff (μ.optionElim n) (G ^ k) / (k.factorial : C))`. Use `VF.Ge.sum fun k hk => ?_` and prove the remaining obligations. Rewrite using `[← coeff_coeff_optionEquivLeft, map_pow, ← hg]`. Distinguish the cases in `hk2 : n < 2 * k`.

Rewrite using `[hdvd k n hk2, map_zero, zero_div]`. Conclude with `VF.Ge.zero 0`. Conclude with `ge_div_factorial V (by omega) (hQ k (Finset.ne_of_mem_erase hk) μ)`. Use `hEm.sub hrest` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right, pow_one, Nat.factorial_one, Nat.cast_one, div_one]`.

Rewrite using `[hg, coeff_coeff_optionEquivLeft]` and apply the resulting hypothesis.
-/
theorem intS_coeff_of_exp {V : VF C} {σ : Type} {G : MvPowerSeries (Option σ) C}
    (h2 : ∀ n < 2, PowerSeries.coeff n (optionEquivLeft σ C G) = 0) (hE : IntS V (mvExp G)) :
    ∀ n ≤ V.l, IntS V (PowerSeries.coeff n (optionEquivLeft σ C G)) := by
  set g := optionEquivLeft σ C G with hg
  have hz : IntS V (0 : MvPowerSeries σ C) := fun μ => by rw [map_zero]; exact VF.Ge.zero 0
  have hdvd : ∀ k n, n < 2 * k → PowerSeries.coeff n (g ^ k) = 0 := fun k => by
    rw [← PowerSeries.X_pow_dvd_iff, pow_mul]
    exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 h2) k
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hn2 : n < 2
    · rw [h2 n hn2]; exact hz
    have hP : ∀ k, ∀ m < n, IntS V (PowerSeries.coeff m (g ^ k)) := by
      intro k
      induction k with
      | zero =>
        intro m _
        rw [pow_zero, PowerSeries.coeff_one]
        split_ifs
        exacts [intS_one, hz]
      | succ k ihk =>
        intro m hm
        rw [pow_succ, PowerSeries.coeff_mul]
        refine intS_sum fun p hp => ?_
        have hp' : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        exact intS_mul (ihk _ (by omega)) (ih _ (by omega) (by omega))
    have hQ : ∀ k, k ≠ 1 → IntS V (PowerSeries.coeff n (g ^ k)) := by
      intro k hk
      rcases k with _ | _ | k
      · rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]; exact hz
      · exact absurd rfl hk
      · rw [pow_succ, PowerSeries.coeff_mul]
        refine intS_sum fun p hp => ?_
        have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        by_cases h1 : p.1 = 0
        · rw [hdvd (k + 1) p.1 (by omega), zero_mul]; exact hz
        by_cases h1' : p.2 = 0
        · rw [h2 p.2 (by omega), mul_zero]; exact hz
        exact intS_mul (hP _ _ (by omega)) (ih _ (by omega) (by omega))
    intro μ
    have hEm := hE (μ.optionElim n)
    have hdeg : n ≤ (μ.optionElim n).degree := by
      simpa using Finsupp.le_degree none (μ.optionElim n)
    have h1 : 1 ∈ Finset.range ((μ.optionElim n).degree + 1) := Finset.mem_range.2 (by omega)
    change V.Ge 0 (∑ k ∈ Finset.range ((μ.optionElim n).degree + 1),
      coeff (μ.optionElim n) (G ^ k) / (k.factorial : C)) at hEm
    rw [← Finset.add_sum_erase _ _ h1] at hEm
    have hrest : V.Ge 0 (∑ k ∈ (Finset.range ((μ.optionElim n).degree + 1)).erase 1,
        coeff (μ.optionElim n) (G ^ k) / (k.factorial : C)) := by
      refine VF.Ge.sum fun k hk => ?_
      rw [← coeff_coeff_optionEquivLeft, map_pow, ← hg]
      by_cases hk2 : n < 2 * k
      · rw [hdvd k n hk2, map_zero, zero_div]; exact VF.Ge.zero 0
      · exact ge_div_factorial V (by omega) (hQ k (Finset.ne_of_mem_erase hk) μ)
    have := hEm.sub hrest
    rw [add_sub_cancel_right, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
    rwa [hg, coeff_coeff_optionEquivLeft]

/- English proof (translation)
Establish `hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.MM (f i)) → V.MM (∑ i ∈ s, f i)` using `fun s f hf => Finset.sum_induction f V.MM (fun _ _ => mm_add) mm_zero hf`. It suffices to establish `H : ∀ N, ∀ μ : κ →₀ ℕ, μ.degree = N → ∀ i, V.MM (coeff μ (D i)) from fun i μ => H _ μ rfl i`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`.

Introduce `μ hμ i`. Establish `e : D i = ∑ j, D j * M j i - ∑ j, D j * (M j i - if j = i then 1 else 0)`. Rewrite using `[← Finset.sum_sub_distrib]`. Simplify using `[mul_sub]`. Rewrite using `[e, map_sub]`.

Use `mm_sub (h i μ) ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `hsum _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `hsum _ _ fun p hp => ?_` and prove the remaining obligations.

Establish `hp' : p.1 + p.2 = μ` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Distinguish the cases in `h2 : p.2 = 0`. Establish `: coeff p.2 (M j i - if j = i then 1 else 0) = 0`. Rewrite using `[h2, coeff_zero_eq_constantCoeff_apply, map_sub, hM0]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[this, mul_zero]`. Conclude with `mm_zero`. Rewrite using `[mul_comm]`. Use `mm_mul ?_ (ih p.1.degree ?_ p.1 rfl j)` and prove the remaining obligations. Rewrite using `[map_sub]`.

Use `(hM j i _).sub ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `intS_one _`. Rewrite using `[map_zero]`. Conclude with `VF.Ge.zero 0`.

Establish `h3 : p.2.degree ≠ 0` using `by rwa [Ne, Finsupp.degree_eq_zero_iff]`. Rewrite using `[← hμ, ← hp', map_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mm_of_mul_matrix {V : VF C} {κ : Type} [Fintype κ] {D : κ → MvPowerSeries κ C}
    {M : κ → κ → MvPowerSeries κ C} (hM : ∀ j i, IntS V (M j i))
    (hM0 : ∀ j i, constantCoeff (M j i) = if j = i then 1 else 0)
    (h : ∀ i μ, V.MM (coeff μ (∑ j, D j * M j i))) : ∀ i μ, V.MM (coeff μ (D i)) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.MM (f i)) → V.MM (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f V.MM (fun _ _ => mm_add) mm_zero hf
  suffices H : ∀ N, ∀ μ : κ →₀ ℕ, μ.degree = N → ∀ i, V.MM (coeff μ (D i)) from fun i μ => H _ μ rfl i
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro μ hμ i
    have e : D i = ∑ j, D j * M j i - ∑ j, D j * (M j i - if j = i then 1 else 0) := by
      rw [← Finset.sum_sub_distrib]
      simp [mul_sub]
    rw [e, map_sub]
    refine mm_sub (h i μ) ?_
    rw [map_sum]
    refine hsum _ _ fun j _ => ?_
    rw [coeff_mul]
    refine hsum _ _ fun p hp => ?_
    have hp' : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : p.2 = 0
    · have : coeff p.2 (M j i - if j = i then 1 else 0) = 0 := by
        rw [h2, coeff_zero_eq_constantCoeff_apply, map_sub, hM0]
        split_ifs <;> simp
      rw [this, mul_zero]
      exact mm_zero
    · rw [mul_comm]
      refine mm_mul ?_ (ih p.1.degree ?_ p.1 rfl j)
      · rw [map_sub]
        refine (hM j i _).sub ?_
        split_ifs
        · exact intS_one _
        · rw [map_zero]; exact VF.Ge.zero 0
      · have h3 : p.2.degree ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
        rw [← hμ, ← hp', map_add]
        omega

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def hCv (X : RawChart C d I κ) (γ : κ → PowerSeries C) : MvPowerSeries (Option κ) C :=
  hAt X (fun x => inT κ (γ x)) (fun x => MvPowerSeries.X (some x))

/- English proof (translation)
Use extensionality with `μ`. Set `g : (κ →₀ ℕ) → (Fin 2 × κ →₀ ℕ)` to `fun ν => ν.mapDomain (fun x : κ => ((0 : Fin 2), x)) + μ.mapDomain (fun x : κ => ((1 : Fin 2), x))`. Establish `i0 : Function.Injective (fun x : κ => ((0 : Fin 2), x))` using `fun _ _ h => (Prod.ext_iff.1 h).2`. Establish `i1 : Function.Injective (fun x : κ => ((1 : Fin 2), x))` using `fun _ _ h => (Prod.ext_iff.1 h).2`. Establish `g0 : ∀ ν x, g ν (0, x) = ν x` using `fun ν x => by`.

Simplify using `only [g, Finsupp.add_apply]`. Rewrite using `[Finsupp.mapDomain_apply i0, Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]`. Establish `g1 : ∀ ν x, g ν (1, x) = μ x` using `fun ν x => by`. Simplify using `only [g, Finsupp.add_apply]`. Rewrite using `[Finsupp.mapDomain_apply i1, Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]`.

Establish `gi : Function.Injective g` using `fun ν ν' h => by`. Use extensionality with `x`. Rewrite using `[← g0 ν, h, g0]`. Establish `hP` using `pair_const (fun x => constantCoeff_inT κ (hγ x)) (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0))`. Establish `term : ∀ e : Fin 2 × κ →₀ ℕ, coeff (μ.optionElim n) (e.prod fun p m => (if p.1 = 0 then inT κ (γ p.2) else (MvPowerSeries.X (some p.2) : MvPowerSeries (Option κ) C)) ^ m) = if ∀ x, e (1, x) = μ x then PowerSeries.coeff n (∏ x, γ x ^ e (0, x)) else 0`.

Introduce `e`. Establish `hm : (∏ x, (MvPowerSeries.X x : MvPowerSeries κ C) ^ e (1, x)) = monomial (Finsupp.equivFunOnFinite.symm fun x => e (1, x)) 1`. Rewrite using `[monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Both sides reduce to the same expression. Rewrite using `[← coeff_coeff_optionEquivLeft, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]`.

Simplify using `only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, map_mul, map_prod, map_pow, optionEquivLeft_inT, optionEquivLeft_X_some]`. Simplify using `only [← map_pow, ← map_prod]`. Rewrite using `[PowerSeries.coeff_mul_C, PowerSeries.coeff_map, hm, coeff_C_mul, coeff_monomial]`. Distinguish the cases in `h : ∀ x, e (1, x) = μ x`. Rewrite using `[if_pos h, if_pos (by ext x; exact (h x).symm), mul_one]`.

Rewrite using `[if_neg h, if_neg (fun h' => h fun x => by rw [h']; rfl), mul_zero]`. Rewrite using `[coeff_coeff_optionEquivLeft]`. Unfold `hCv hAt`. Use `Eq.trans ?_ (coeff_subst (τ := Unit) (a := γ) (hasSubst_of_constantCoeff_zero hγ) (fun ν : κ →₀ ℕ => coeff (g ν) X.h) (Finsupp.single () n)).symm` and prove the remaining obligations. Rewrite using `[coeff_subst (hasSubst_of_constantCoeff_zero hP), ← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ (Set.range g), finsum_mem_range gi]`.

Use `finsum_congr fun ν => ?_` and prove the remaining obligations. Rewrite using `[term, if_pos (g1 ν), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [g0]`. Both sides reduce to the same expression. Use extensionality with `e`.

Simplify using `only [Set.mem_inter_iff, Set.mem_univ, true_and, Function.mem_support, iff_and_self]`. Introduce `he`. Rewrite `he` using `[term]`. Establish `h : ∀ x, e (1, x) = μ x`. Assume the negation of the conclusion as `h`.

Rewrite `he` using `[if_neg h, smul_zero]`. Conclude with `he rfl`. Use `⟨Finsupp.equivFunOnFinite.symm fun x => e (0, x), ?_⟩` and prove the remaining obligations. Use extensionality with `⟨j, x⟩`. Use `fin_cases j`.

Conclude with `g0 _ x`. Conclude with `(g1 _ x).trans (h x).symm`.
-/
theorem coeff_hCv (X : RawChart C d I κ) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (n : ℕ) : PowerSeries.coeff n (optionEquivLeft κ C (hCv X γ)) = hCoef X γ n := by
  ext μ
  let g : (κ →₀ ℕ) → (Fin 2 × κ →₀ ℕ) := fun ν =>
    ν.mapDomain (fun x : κ => ((0 : Fin 2), x)) + μ.mapDomain (fun x : κ => ((1 : Fin 2), x))
  have i0 : Function.Injective (fun x : κ => ((0 : Fin 2), x)) := fun _ _ h => (Prod.ext_iff.1 h).2
  have i1 : Function.Injective (fun x : κ => ((1 : Fin 2), x)) := fun _ _ h => (Prod.ext_iff.1 h).2
  have g0 : ∀ ν x, g ν (0, x) = ν x := fun ν x => by
    simp only [g, Finsupp.add_apply]
    rw [Finsupp.mapDomain_apply i0, Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
  have g1 : ∀ ν x, g ν (1, x) = μ x := fun ν x => by
    simp only [g, Finsupp.add_apply]
    rw [Finsupp.mapDomain_apply i1, Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
  have gi : Function.Injective g := fun ν ν' h => by
    ext x
    rw [← g0 ν, h, g0]
  have hP := pair_const (fun x => constantCoeff_inT κ (hγ x))
    (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0))
  have term : ∀ e : Fin 2 × κ →₀ ℕ, coeff (μ.optionElim n) (e.prod fun p m =>
      (if p.1 = 0 then inT κ (γ p.2) else (MvPowerSeries.X (some p.2) : MvPowerSeries (Option κ) C)) ^ m) =
      if ∀ x, e (1, x) = μ x then PowerSeries.coeff n (∏ x, γ x ^ e (0, x)) else 0 := by
    intro e
    have hm : (∏ x, (MvPowerSeries.X x : MvPowerSeries κ C) ^ e (1, x)) =
        monomial (Finsupp.equivFunOnFinite.symm fun x => e (1, x)) 1 := by
      rw [monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rfl
    rw [← coeff_coeff_optionEquivLeft, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Fin.prod_univ_two]
    simp only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, map_mul, map_prod, map_pow,
      optionEquivLeft_inT, optionEquivLeft_X_some]
    simp only [← map_pow, ← map_prod]
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_map, hm, coeff_C_mul, coeff_monomial]
    by_cases h : ∀ x, e (1, x) = μ x
    · rw [if_pos h, if_pos (by ext x; exact (h x).symm), mul_one]
    · rw [if_neg h, if_neg (fun h' => h fun x => by rw [h']; rfl), mul_zero]
  rw [coeff_coeff_optionEquivLeft]
  unfold hCv hAt
  refine Eq.trans ?_ (coeff_subst (τ := Unit) (a := γ) (hasSubst_of_constantCoeff_zero hγ)
    (fun ν : κ →₀ ℕ => coeff (g ν) X.h) (Finsupp.single () n)).symm
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hP), ← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ (Set.range g), finsum_mem_range gi]
  · refine finsum_congr fun ν => ?_
    rw [term, if_pos (g1 ν), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [g0]
    rfl
  · ext e
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Function.mem_support, iff_and_self]
    intro he
    rw [term] at he
    have h : ∀ x, e (1, x) = μ x := by
      by_contra h
      rw [if_neg h, smul_zero] at he
      exact he rfl
    refine ⟨Finsupp.equivFunOnFinite.symm fun x => e (0, x), ?_⟩
    ext ⟨j, x⟩
    fin_cases j
    · exact g0 _ x
    · exact (g1 _ x).trans (h x).symm

/- English proof (translation)
The claim follows from `GlobalTheory.RowVal.intS_X s`.
-/
theorem intS_X' {V : VF C} {σ : Type} (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) :=
  GlobalTheory.RowVal.intS_X s

/- English proof (translation)
The claim follows from `intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X' _) (intS_iff.2 hf)`.
-/
theorem intS_inT {V : VF C} {σ : Type} {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    IntS V (inT σ f) :=
  intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X' _) (intS_iff.2 hf)

/- English proof (translation)
The claim follows from `subst_comp_subst_apply (τ := Unit) (a := γ) (hasSubst_of_constantCoeff_zero hγ) (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) f`.
-/
theorem inT_alongCv (σ : Type) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (f : MvPowerSeries κ C) : inT σ (alongCv γ f) = subst (fun x => inT σ (γ x)) f :=
  subst_comp_subst_apply (τ := Unit) (a := γ) (hasSubst_of_constantCoeff_zero hγ)
    (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) f

/- English proof (translation)
Unfold `hAt`. Rewrite using `[subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (pair_const ha hb)) (hasSubst_of_constantCoeff_zero hc)]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem subst_hAt (X : RawChart C d I κ) {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (hAt X a b) = hAt X (fun y => subst c (a y)) (fun y => subst c (b y)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (pair_const ha hb)) (hasSubst_of_constantCoeff_zero hc)]
  congr 1
  funext p
  split_ifs <;> rfl

/- English proof (translation)
The claim follows from `constantCoeff_subst_zero (pair_const ha hb) (by rw [← coeff_zero_eq_constantCoeff_apply] exact h.axes 0 0 (by simp))`.
-/
theorem hAt_const {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) : constantCoeff (hAt X a b) = 0 :=
  constantCoeff_subst_zero (pair_const ha hb) (by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact h.axes 0 0 (by simp))

/- English proof (translation)
Use `haveI := h.charZero`. Set `c : Fin 3 × κ → MvPowerSeries τ C` to `fun p => if p.1 = 0 then a p.2 else if p.1 = 1 then b p.2 else z p.2`. Establish `hc : ∀ p, constantCoeff (c p) = 0` using `fun p => by`. Simplify using `only [c]`. Use `split_ifs`.

Use `exacts [ha _, hb _, hz _]`. Establish `hci : ∀ p, IntS V (c p)` using `fun p => by`. Simplify using `only [c]`. Use `split_ifs`. Use `exacts [hai _, hbi _, hzi _]`.

Establish `hS` using `hasSubst_of_constantCoeff_zero hc`. Establish `s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = a x` using `fun x => by simp [gp, subst_X hS, c]`. Establish `s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = b x` using `fun x => by simp [gp, subst_X hS, c]`. Establish `s2 : ∀ x, subst c (gp C κ (2 : Fin 3) x) = z x` using `fun x => by simp [gp, subst_X hS, c]`. Establish `sA : ∀ x, subst c (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = addP X a b x` using `fun x => by`.

Rewrite using `[subst_addP h (gp_const 0) (gp_const 1) hc]`. Simplify using `only [s0, s1]`. Establish `hAc` using `formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1)`. Establish `h1` using `intS_subst hc hci h.ph1`. Rewrite using `[GlobalTheory.RowVal.subst_mvExp hc (by`.

Rewrite using `[map_sub, map_add, hAt_const h (gp_const 0) (gp_const 2), hAt_const h (gp_const 1) (gp_const 2), hAt_const h hAc (gp_const 2)]`. Use the proof step `simp), subst_sub hS, subst_add hS, subst_hAt X (gp_const 0) (gp_const 2) hc,`. Use `subst_hAt X (gp_const 1) (gp_const 2) hc, subst_hAt X hAc (gp_const 2) hc] at h1`. Simplify `h1` using `only [s0, s1, s2, sA]`.
-/
theorem intS_defect {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b z : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (hz : ∀ s, constantCoeff (z s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (hzi : ∀ s, IntS V (z s)) :
    IntS V (mvExp (hAt X a z + hAt X b z - hAt X (addP X a b) z)) := by
  haveI := h.charZero
  let c : Fin 3 × κ → MvPowerSeries τ C := fun p => if p.1 = 0 then a p.2 else if p.1 = 1 then b p.2 else z p.2
  have hc : ∀ p, constantCoeff (c p) = 0 := fun p => by
    simp only [c]
    split_ifs
    exacts [ha _, hb _, hz _]
  have hci : ∀ p, IntS V (c p) := fun p => by
    simp only [c]
    split_ifs
    exacts [hai _, hbi _, hzi _]
  have hS := hasSubst_of_constantCoeff_zero hc
  have s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = a x := fun x => by simp [gp, subst_X hS, c]
  have s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = b x := fun x => by simp [gp, subst_X hS, c]
  have s2 : ∀ x, subst c (gp C κ (2 : Fin 3) x) = z x := fun x => by simp [gp, subst_X hS, c]
  have sA : ∀ x, subst c (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = addP X a b x := fun x => by
    rw [subst_addP h (gp_const 0) (gp_const 1) hc]
    simp only [s0, s1]
  have hAc := formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1)
  have h1 := intS_subst hc hci h.ph1
  rw [GlobalTheory.RowVal.subst_mvExp hc (by
    rw [map_sub, map_add, hAt_const h (gp_const 0) (gp_const 2), hAt_const h (gp_const 1) (gp_const 2),
      hAt_const h hAc (gp_const 2)]; simp), subst_sub hS, subst_add hS, subst_hAt X (gp_const 0) (gp_const 2) hc,
    subst_hAt X (gp_const 1) (gp_const 2) hc, subst_hAt X hAc (gp_const 2) hc] at h1
  simpa only [s0, s1, s2, sA] using h1

/- English proof (translation)
The claim follows from `hAt_const h (fun x => constantCoeff_inT κ (hγ x)) fun _ => constantCoeff_X _`.
-/
theorem hCv_const {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) : constantCoeff (hCv X γ) = 0 :=
  hAt_const h (fun x => constantCoeff_inT κ (hγ x)) fun _ => constantCoeff_X _

/- English proof (translation)
Use `haveI := h.charZero`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨γ, hγ, fun i => by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_add, Nat.cast_one, one_smul, sub_self, GlobalTheory.RowVal.mvExp_zero']`.

Conclude with `intS_one`. Consider the case `succ k ih`. Take `⟨δ, hδ, h1, h2⟩` from `ih`. Establish `ha : ∀ s, constantCoeff (σ` using `Unit) (δ s) = 0 := fun s => (hδ s).1`. Establish `hb : ∀ s, constantCoeff (σ` using `Unit) (γ s) = 0 := fun s => (hγ s).1`.

Establish `hai : ∀ s, IntS V (σ` using `Unit) (δ s) := fun s => intS_iff.2 (hδ s).2`. Establish `hbi : ∀ s, IntS V (σ` using `Unit) (γ s) := fun s => intS_iff.2 (hγ s).2`. Establish `hc : ∀ i, constantCoeff (addP X (τ` using `Unit) δ γ i) = 0 := formalAdd_const h ha hb`. Use `⟨addP X (τ := Unit) δ γ, fun i => ⟨hc i, intS_iff.1 (intS_addP h ha hb hai hbi i)⟩, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `lg_addP h ha hb i` as an intermediate fact.

Express the relevant statement in the definitionally equal form `alongCv _ _ = alongCv δ _ + alongCv γ _ at this`. Rewrite using `[this, h1, Nat.cast_succ (k + 1), add_smul, one_smul]`. Establish `h3` using `intS_defect h (fun x => constantCoeff_inT κ (ha x)) (fun x => constantCoeff_inT κ (hb x)) (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0)) (fun x => intS_inT (hδ x).2) (fun x => intS_inT (hγ x).2) (fun x => intS_X' _)`. Establish `e : addP X (fun x => inT κ (δ x)) (fun x => inT κ (γ x)) = fun x => inT κ (addP X (τ` using `Unit) δ γ x) :=`. Use function extensionality and compare the values at `fun x => (subst_addP h ha hb (fun _ => constantCoeff_X _) x).symm`.

Rewrite `h3` using `[e]`. Express the relevant statement in the definitionally equal form `IntS V (mvExp (hCv X δ + hCv X γ - hCv X (addP X (τ := Unit) δ γ))) at h3`. Establish `h4` using `intS_mul h2 h3`. Rewrite `h4` using `[← GlobalTheory.RowVal.mvExp_add (by rw [map_sub, constantCoeff_smul, hCv_const h hb, hCv_const h ha]; simp) (by rw [map_sub, map_add, hCv_const h hb, hCv_const h ha, hCv_const h hc]; simp)]`. Use `h4 using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[Nat.cast_succ (k + 1), add_smul, one_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_multiple {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C} (hγ : IsCv V γ)
    (k : ℕ) : ∃ δ : κ → PowerSeries C, IsCv V δ ∧ (∀ i, alongCv δ (X.lg i) = ((k + 1 : ℕ) : C) • alongCv γ (X.lg i)) ∧
      IntS V (mvExp (((k + 1 : ℕ) : C) • hCv X γ - hCv X δ)) := by
  haveI := h.charZero
  induction k with
  | zero =>
    refine ⟨γ, hγ, fun i => by simp, ?_⟩
    rw [zero_add, Nat.cast_one, one_smul, sub_self, GlobalTheory.RowVal.mvExp_zero']
    exact intS_one
  | succ k ih =>
    obtain ⟨δ, hδ, h1, h2⟩ := ih
    have ha : ∀ s, constantCoeff (σ := Unit) (δ s) = 0 := fun s => (hδ s).1
    have hb : ∀ s, constantCoeff (σ := Unit) (γ s) = 0 := fun s => (hγ s).1
    have hai : ∀ s, IntS V (σ := Unit) (δ s) := fun s => intS_iff.2 (hδ s).2
    have hbi : ∀ s, IntS V (σ := Unit) (γ s) := fun s => intS_iff.2 (hγ s).2
    have hc : ∀ i, constantCoeff (addP X (τ := Unit) δ γ i) = 0 := formalAdd_const h ha hb
    refine ⟨addP X (τ := Unit) δ γ, fun i => ⟨hc i, intS_iff.1 (intS_addP h ha hb hai hbi i)⟩, fun i => ?_, ?_⟩
    · have := lg_addP h ha hb i
      change alongCv _ _ = alongCv δ _ + alongCv γ _ at this
      rw [this, h1, Nat.cast_succ (k + 1), add_smul, one_smul]
    · have h3 := intS_defect h (fun x => constantCoeff_inT κ (ha x)) (fun x => constantCoeff_inT κ (hb x))
        (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0))
        (fun x => intS_inT (hδ x).2) (fun x => intS_inT (hγ x).2) (fun x => intS_X' _)
      have e : addP X (fun x => inT κ (δ x)) (fun x => inT κ (γ x)) = fun x => inT κ (addP X (τ := Unit) δ γ x) :=
        funext fun x => (subst_addP h ha hb (fun _ => constantCoeff_X _) x).symm
      rw [e] at h3
      change IntS V (mvExp (hCv X δ + hCv X γ - hCv X (addP X (τ := Unit) δ γ))) at h3
      have h4 := intS_mul h2 h3
      rw [← GlobalTheory.RowVal.mvExp_add (by rw [map_sub, constantCoeff_smul, hCv_const h hb, hCv_const h ha]; simp)
        (by rw [map_sub, map_add, hCv_const h hb, hCv_const h ha, hCv_const h hc]; simp)] at h4
      convert h4 using 2
      rw [Nat.cast_succ (k + 1), add_smul, one_smul]
      ring

/- English proof (translation)
Introduce `n hn`. Use `subst_congr (τ := Unit) (S := {ν | ν () < N}) (a := γ) (b := δ) (fun ν ν' hle (hν : ν () < N) => lt_of_le_of_lt (hle ()) hν) hγ hδ (fun s ν hν => ?_) f (Finsupp.single () n) (by simpa using hn)` and prove the remaining obligations. Rewrite using `[Finsupp.unique_single ν]`. Conclude with `h s _ hν`.
-/
theorem coeff_alongCv_congr {N : ℕ} {γ δ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0)
    (h : ∀ i, ∀ n < N, PowerSeries.coeff n (γ i) = PowerSeries.coeff n (δ i)) (f : MvPowerSeries κ C) :
    ∀ n < N, PowerSeries.coeff n (alongCv γ f) = PowerSeries.coeff n (alongCv δ f) := by
  intro n hn
  refine subst_congr (τ := Unit) (S := {ν | ν () < N}) (a := γ) (b := δ)
    (fun ν ν' hle (hν : ν () < N) => lt_of_le_of_lt (hle ()) hν) hγ hδ (fun s ν hν => ?_) f
    (Finsupp.single () n) (by simpa using hn)
  rw [Finsupp.unique_single ν]
  exact h s _ hν

/- English proof (translation)
Simplify using `only [PowerSeries.rescale_eq_subst]`. Conclude with `alongCv_repar hγ (by simp) f`.
-/
theorem alongCv_rescale {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (s : C)
    (f : MvPowerSeries κ C) :
    alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

/- English proof (translation)
Establish `hS` using `hasSubst_of_constantCoeff_zero (τ := Unit) (a := γ) hγ`. Use `subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const h)) hS (X.ex i)` as an intermediate fact. Rewrite `this` using `[h.exlg, subst_X hS]`. Conclude with `this.symm`.
-/
theorem alongCv_ex_lg {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    alongCv (fun x => alongCv γ (X.lg x)) (X.ex i) = γ i := by
  have hS := hasSubst_of_constantCoeff_zero (τ := Unit) (a := γ) hγ
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const h)) hS (X.ex i)
  rw [h.exlg, subst_X hS] at this
  exact this.symm

/- English proof (translation)
Establish `hr : ∀ i, PowerSeries.constantCoeff (PowerSeries.rescale s (γ i)) = 0` using `fun i => by`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ, mul_zero]`. Establish `hc : ∀ {ε : κ → PowerSeries C}, (∀ i, PowerSeries.constantCoeff (ε i) = 0) → ∀ i, PowerSeries.constantCoeff (alongCv ε (X.lg i)) = 0` using `fun {ε} hε i => constantCoeff_subst_zero (τ := Unit) (a := ε) hε (lg_const h i)`. Establish `key : ∀ i, ∀ m < N, PowerSeries.coeff m (δ i) = PowerSeries.coeff m (PowerSeries.rescale s (γ i))`. Introduce `i`.

Rewrite using `[← alongCv_ex_lg h hδ i, ← alongCv_ex_lg h hr i]`. Use `coeff_alongCv_congr (hc hδ) (hc hr) (fun x m hm => ?_) _` and prove the remaining obligations. Rewrite using `[hs, alongCv_rescale hγ, PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]`. Break down `m with _ | _ | m` into its components or cases. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hc hγ, mul_zero, mul_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[hl x _ (by omega) hm, mul_zero, mul_zero]`. Use extensionality with `μ`. Rewrite using `[coeff_smul]`. Use `(coeff_alongCv_congr hδ hr key _ n hn).trans ?_` and prove the remaining obligations.

Use `(congrArg (PowerSeries.coeff n) (alongCv_rescale hγ s _)).trans ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_rescale]`. Both sides reduce to the same expression.
-/
theorem hCoef_of_lg {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {N : ℕ} {γ δ : κ → PowerSeries C} {s : C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0)
    (hl : ∀ i n, 2 ≤ n → n < N → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0)
    (hs : ∀ i, alongCv δ (X.lg i) = s • alongCv γ (X.lg i)) {n : ℕ} (hn : n < N) :
    hCoef X δ n = s ^ n • hCoef X γ n := by
  have hr : ∀ i, PowerSeries.constantCoeff (PowerSeries.rescale s (γ i)) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ, mul_zero]
  have hc : ∀ {ε : κ → PowerSeries C}, (∀ i, PowerSeries.constantCoeff (ε i) = 0) → ∀ i,
      PowerSeries.constantCoeff (alongCv ε (X.lg i)) = 0 := fun {ε} hε i =>
    constantCoeff_subst_zero (τ := Unit) (a := ε) hε (lg_const h i)
  have key : ∀ i, ∀ m < N, PowerSeries.coeff m (δ i) = PowerSeries.coeff m (PowerSeries.rescale s (γ i)) := by
    intro i
    rw [← alongCv_ex_lg h hδ i, ← alongCv_ex_lg h hr i]
    refine coeff_alongCv_congr (hc hδ) (hc hr) (fun x m hm => ?_) _
    rw [hs, alongCv_rescale hγ, PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
    rcases m with _ | _ | m
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc hγ, mul_zero, mul_zero]
    · simp
    · rw [hl x _ (by omega) hm, mul_zero, mul_zero]
  ext μ
  rw [coeff_smul]
  refine (coeff_alongCv_congr hδ hr key _ n hn).trans ?_
  refine (congrArg (PowerSeries.coeff n) (alongCv_rescale hγ s _)).trans ?_
  rw [PowerSeries.coeff_rescale]
  rfl

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[map_zero]`. Use `(PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (constantCoeff_subst_zero (τ := Unit) (a := γ) hγ ?_)` and prove the remaining obligations. Use `h.axes 0 _ fun s hs => ?_` and prove the remaining obligations. Rewrite `hs` using `[Finsupp.mapDomain_zero, zero_add]`.

Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hs)`. Simplify using the standard rewrite rules.
-/
theorem hCoef_zero {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) : hCoef X γ 0 = 0 := by
  ext μ
  rw [map_zero]
  refine (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans
    (constantCoeff_subst_zero (τ := Unit) (a := γ) hγ ?_)
  refine h.axes 0 _ fun s hs => ?_
  rw [Finsupp.mapDomain_zero, zero_add] at hs
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hs)
  simp

/- English proof (translation)
Establish `h2` using `V.l_prime.two_le`. Take `⟨δ, hδ, h1, hE⟩` from `exists_multiple h hγ (V.l - 1)`. Rewrite `hE` using `[show V.l - 1 + 1 = V.l by omega]`. Simplify using `only [show V.l - 1 + 1 = V.l by omega] at h1`. Establish `hγ0` using `fun i => (hγ i).1`.

Establish `hδ0` using `fun i => (hδ i).1`. Establish `hco : ∀ n < V.l ^ 2, PowerSeries.coeff n (optionEquivLeft κ C ((V.l : C) • hCv X γ - hCv X δ)) = ((V.l : C) - (V.l : C) ^ n) • hCoef X γ n`. Introduce `n hn`. Rewrite using `[map_sub, map_smul, map_sub, PowerSeries.coeff_smul, coeff_hCv X hγ0, coeff_hCv X hδ0, hCoef_of_lg h hγ0 hδ0 hl h1 hn, sub_smul]`. Establish `hll : V.l < V.l ^ 2` using `by nlinarith`.

Establish `h3` using `intS_coeff_of_exp (fun n hn => by`. Rewrite using `[hco n (by omega)]`. Break down `n with _ | _ | n` into its components or cases. Rewrite using `[hCoef_zero h hγ0, smul_zero]`. Simplify using the standard rewrite rules.

Use the proof step `omega) hE V.l le_rfl`. Rewrite `h3` using `[hco _ hll]`. Introduce `μ`. Establish `hu : V.v (1 - (V.l : C) ^ (V.l - 1)) = 0`. Apply `v_eq_zero_of_mm_sub_one` to reduce the goal to its premises.

Rewrite using `[sub_sub_cancel_left, show V.l - 1 = V.l - 2 + 1 by omega, pow_succ']`. Conclude with `mm_neg (mm_l_mul ((VF.ge_natCast _).pow _))`. Use `ge_of_unit_mul hu ?_` and prove the remaining obligations. Use `h3 μ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[coeff_smul, coeff_smul, ← mul_assoc]`.

Use `congr 1`. Establish `: (V.l : C) ^ V.l = (V.l : C) ^ (V.l - 1) * V.l` using `by rw [← pow_succ, Nat.sub_add_cancel (by omega)]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intS_l_smul_hCoef {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C} (hγ : IsCv V γ)
    (hl : ∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) :
    IntS V ((V.l : C) • hCoef X γ V.l) := by
  have h2 := V.l_prime.two_le
  obtain ⟨δ, hδ, h1, hE⟩ := exists_multiple h hγ (V.l - 1)
  rw [show V.l - 1 + 1 = V.l by omega] at hE
  simp only [show V.l - 1 + 1 = V.l by omega] at h1
  have hγ0 := fun i => (hγ i).1
  have hδ0 := fun i => (hδ i).1
  have hco : ∀ n < V.l ^ 2, PowerSeries.coeff n (optionEquivLeft κ C ((V.l : C) • hCv X γ - hCv X δ)) =
      ((V.l : C) - (V.l : C) ^ n) • hCoef X γ n := by
    intro n hn
    rw [map_sub, map_smul, map_sub, PowerSeries.coeff_smul, coeff_hCv X hγ0, coeff_hCv X hδ0,
      hCoef_of_lg h hγ0 hδ0 hl h1 hn, sub_smul]
  have hll : V.l < V.l ^ 2 := by nlinarith
  have h3 := intS_coeff_of_exp (fun n hn => by
    rw [hco n (by omega)]
    rcases n with _ | _ | n
    · rw [hCoef_zero h hγ0, smul_zero]
    · simp
    · omega) hE V.l le_rfl
  rw [hco _ hll] at h3
  intro μ
  have hu : V.v (1 - (V.l : C) ^ (V.l - 1)) = 0 := by
    apply v_eq_zero_of_mm_sub_one
    rw [sub_sub_cancel_left, show V.l - 1 = V.l - 2 + 1 by omega, pow_succ']
    exact mm_neg (mm_l_mul ((VF.ge_natCast _).pow _))
  refine ge_of_unit_mul hu ?_
  convert h3 μ using 1
  rw [coeff_smul, coeff_smul, ← mul_assoc]
  congr 1
  have : (V.l : C) ^ V.l = (V.l : C) ^ (V.l - 1) * V.l := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [this]
  ring

/- English proof (translation)
Establish `hS` using `hasSubst_of_constantCoeff_zero ha`. Use `subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const h)) hS (X.ex x)` as an intermediate fact. Rewrite `this` using `[h.exlg, subst_X hS]`. Conclude with `this.symm`.
-/
theorem addP_zero {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) :
    subst (fun y => subst a (X.lg y)) (X.ex x) = a x := by
  have hS := hasSubst_of_constantCoeff_zero ha
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const h)) hS (X.ex x)
  rw [h.exlg, subst_X hS] at this
  exact this.symm

/- English proof (translation)
Introduce `_ _ hle hν w hw` and use `hν w (Finsupp.support_mono hle hw)`.
-/
theorem isLowerSet_avoid {τ : Type} (T : Set τ) : IsLowerSet {ν : τ →₀ ℕ | ∀ w ∈ ν.support, w ∉ T} :=
  fun _ _ hle hν w hw => hν w (Finsupp.support_mono hle hw)

/- English proof (translation)
Introduce `ν hν`. Unfold `gp`. Rewrite using `[coeff_X, if_neg]`. Introduce `e`. Conclude with `hν (2, x) (by rw [e]; simp) rfl`.
-/
theorem van_gp_two (x : κ) : Van {p : Fin 3 × κ | p.1 = 2} (gp C κ 2 x) := by
  intro ν hν
  unfold gp
  rw [coeff_X, if_neg]
  intro e
  exact hν (2, x) (by rw [e]; simp) rfl

/- English proof (translation)
Establish `hL` using `isLowerSet_avoid {p : Fin 3 × κ | p.1 = 2}`. Establish `h1 : Van {p : Fin 3 × κ | p.1 = 2} (hAt X (gp C κ 0) (gp C κ 2))`. Use `Van.subst {s : Fin 2 × κ | s.1 = 1} (pair_const (gp_const 0) (gp_const 2)) ?_ (h.axes 1)` and prove the remaining obligations. Introduce and unpack `⟨g, x⟩ (hg : g = 1)`. Substitute `hg` using the available equality.

Rewrite using `[if_neg (by simp)]`. Conclude with `van_gp_two x`. Establish `h2 : ∀ x, ∀ ν ∈ {ν : Fin 3 × κ →₀ ℕ | ∀ w ∈ ν.support, w ∉ {p : Fin 3 × κ | p.1 = 2}}, coeff ν (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) x) = coeff ν (gp C κ (1 : Fin 3) x)`. Introduce `x`. Rewrite using `[← addP_zero h (gp_const (1 : Fin 3)) x]`.

Use `subst_congr hL (sum_const h (gp_const 1) (gp_const 2)) (fun y => constantCoeff_subst_zero (gp_const 1) (lg_const h y)) (fun y ν hν => ?_) _` and prove the remaining obligations. Rewrite using `[map_add, Van.subst Set.univ (gp_const 2) (fun s _ => van_gp_two s) (van_univ (lg_const h y)) ν hν, add_zero]`. Introduce `ν hν`. Establish `h3` using `subst_congr hL (pair_const (gp_const (0 : Fin 3)) (formalAdd_const h (gp_const 1) (gp_const 2))) (pair_const (gp_const (0 : Fin 3)) (gp_const 1)) (fun p ν hν => by split_ifs`. Both sides reduce to the same expression.

Conclude with `h2 _ ν hν) X.h ν hν`. Rewrite using `[map_sub, map_add, h1 ν hν, add_zero, sub_eq_zero]`. Conclude with `h3.symm`.
-/
theorem van_defect {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) :
    Van {p : Fin 3 × κ | p.1 = 2} (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
      hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2))) := by
  have hL := isLowerSet_avoid {p : Fin 3 × κ | p.1 = 2}
  have h1 : Van {p : Fin 3 × κ | p.1 = 2} (hAt X (gp C κ 0) (gp C κ 2)) := by
    refine Van.subst {s : Fin 2 × κ | s.1 = 1} (pair_const (gp_const 0) (gp_const 2)) ?_ (h.axes 1)
    rintro ⟨g, x⟩ (hg : g = 1)
    subst hg
    rw [if_neg (by simp)]
    exact van_gp_two x
  have h2 : ∀ x, ∀ ν ∈ {ν : Fin 3 × κ →₀ ℕ | ∀ w ∈ ν.support, w ∉ {p : Fin 3 × κ | p.1 = 2}},
      coeff ν (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) x) = coeff ν (gp C κ (1 : Fin 3) x) := by
    intro x
    rw [← addP_zero h (gp_const (1 : Fin 3)) x]
    refine subst_congr hL (sum_const h (gp_const 1) (gp_const 2))
      (fun y => constantCoeff_subst_zero (gp_const 1) (lg_const h y)) (fun y ν hν => ?_) _
    rw [map_add, Van.subst Set.univ (gp_const 2) (fun s _ => van_gp_two s) (van_univ (lg_const h y)) ν hν, add_zero]
  intro ν hν
  have h3 := subst_congr hL (pair_const (gp_const (0 : Fin 3)) (formalAdd_const h (gp_const 1) (gp_const 2)))
    (pair_const (gp_const (0 : Fin 3)) (gp_const 1)) (fun p ν hν => by
      split_ifs
      · rfl
      · exact h2 _ ν hν) X.h ν hν
  rw [map_sub, map_add, h1 ν hν, add_zero, sub_eq_zero]
  exact h3.symm

def invM (X : RawChart C d I κ) (j i : κ) : MvPowerSeries κ C :=
  subst (fun p : Fin 2 × κ => if p.1 = 0 then (MvPowerSeries.X p.2 : MvPowerSeries κ C) else 0)
    (pderiv C ((1 : Fin 2), i) (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) j))

/- English proof (translation)
The claim follows from `pair_const (a := fun x => MvPowerSeries.X x) (b := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _) p`.
-/
theorem axis_const (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then (MvPowerSeries.X p.2 : MvPowerSeries κ C) else 0) = 0 :=
  pair_const (a := fun x => MvPowerSeries.X x) (b := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _) p

/- English proof (translation)
The claim follows from `intS_subst axis_const (fun p => by split_ifs exacts [intS_X' _, GlobalTheory.RowVal.intS_zero]) (intS_pderiv (h.addInt j) _)`.
-/
theorem intS_invM {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) (j i : κ) : IntS V (invM X j i) :=
  intS_subst axis_const (fun p => by
    split_ifs
    exacts [intS_X' _, GlobalTheory.RowVal.intS_zero]) (intS_pderiv (h.addInt j) _)

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, h.lin k _ (by rw [Finsupp.degree_single]), coeff_X]`. Distinguish the cases in `e : k = j`. Simplify using `[e]`. Rewrite using `[if_neg e, if_neg (fun h' => e (Finsupp.single_left_injective one_ne_zero h').symm), zero_mul]`.
-/
theorem const_pderiv_lg {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) (k j : κ) :
    constantCoeff (pderiv C j (X.lg k)) = if k = j then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, h.lin k _ (by rw [Finsupp.degree_single]), coeff_X]
  by_cases e : k = j
  · simp [e]
  · rw [if_neg e, if_neg (fun h' => e (Finsupp.single_left_injective one_ne_zero h').symm), zero_mul]

/- English proof (translation)
Establish `hA` using `formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const 1)`. Establish `e` using `congrArg (fun F => constantCoeff (pderiv C ((1 : Fin 2), i) F)) (lg_addP h (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const 1) j)`. Rewrite `e` using `[map_add, pderiv_subst_eq_zero (gp_const 0) (fun x => pderiv_X_of_ne (by simp)), zero_add, FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero hA), FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero (gp_const 1)), map_sum, map_sum]`. Simplify using `only [map_mul, GlobalTheory.RowVal.cc_subst hA, GlobalTheory.RowVal.cc_subst (gp_const (C := C) (κ := κ) (1 : Fin 2)), const_pderiv_lg h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at e`. Unfold `invM`.

Rewrite using `[GlobalTheory.RowVal.cc_subst axis_const, e]`. Unfold `gp`. Use `split_ifs with hji`. Rewrite using `[hji, pderiv_X_self, map_one]`. Rewrite using `[pderiv_X_of_ne (by simpa using hji), map_zero]`.
-/
theorem const_invM {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) (j i : κ) :
    constantCoeff (invM X j i) = if j = i then 1 else 0 := by
  have hA := formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const 1)
  have e := congrArg (fun F => constantCoeff (pderiv C ((1 : Fin 2), i) F))
    (lg_addP h (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const 1) j)
  rw [map_add, pderiv_subst_eq_zero (gp_const 0) (fun x => pderiv_X_of_ne (by simp)), zero_add,
    FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero hA),
    FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero (gp_const 1)), map_sum, map_sum] at e
  simp only [map_mul, GlobalTheory.RowVal.cc_subst hA, GlobalTheory.RowVal.cc_subst (gp_const (C := C) (κ := κ) (1 : Fin 2)),
    const_pderiv_lg h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
  unfold invM
  rw [GlobalTheory.RowVal.cc_subst axis_const, e]
  unfold gp
  split_ifs with hji
  · rw [hji, pderiv_X_self, map_one]
  · rw [pderiv_X_of_ne (by simpa using hji), map_zero]

/- English proof (translation)
Establish `hP` using `pair_const (fun x => constantCoeff_inT κ (hγ x)) (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0))`. Unfold `hCv hAt`. Rewrite using `[FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero hP), Fintype.sum_prod_type, Fin.sum_univ_two]`. Establish `h0 : ∀ x, pderiv C (some j) (inT κ (γ x)) = 0` using `fun x => pderiv_subst_eq_zero (fun _ => constantCoeff_X _) (fun _ => pderiv_X_of_ne (by simp)) _`. Simplify using `only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, h0, mul_zero, Finset.sum_const_zero, zero_add]`.

Rewrite using `[Finset.sum_eq_single j, pderiv_X_self, mul_one]`. Introduce `x _ hx`. Rewrite using `[pderiv_X_of_ne (by simpa using hx), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem pderiv_hCv (X : RawChart C d I κ) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (j : κ) : pderiv C (some j) (hCv X γ) =
      subst (fun p : Fin 2 × κ => if p.1 = 0 then inT κ (γ p.2) else MvPowerSeries.X (some p.2))
        (pderiv C ((1 : Fin 2), j) X.h) := by
  have hP := pair_const (fun x => constantCoeff_inT κ (hγ x))
    (fun x => (constantCoeff_X _ : constantCoeff (MvPowerSeries.X (some x) : MvPowerSeries (Option κ) C) = 0))
  unfold hCv hAt
  rw [FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero hP), Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : ∀ x, pderiv C (some j) (inT κ (γ x)) = 0 := fun x =>
    pderiv_subst_eq_zero (fun _ => constantCoeff_X _) (fun _ => pderiv_X_of_ne (by simp)) _
  simp only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, h0, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single j, pderiv_X_self, mul_one]
  · intro x _ hx
    rw [pderiv_X_of_ne (by simpa using hx), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hγ0` using `fun i => (hγ i).1`. Establish `hΓ` using `fun x => constantCoeff_inT κ (hγ0 x)`. Set `c : Fin 3 × κ → MvPowerSeries (Option κ) C` to `fun p => if p.1 = 0 then inT κ (γ p.2) else if p.1 = 1 then MvPowerSeries.X (some p.2) else 0`. Establish `hc : ∀ p, constantCoeff (c p) = 0` using `fun p => by`. Simplify using `only [c]`.

Use `split_ifs`. Use `exacts [hΓ _, constantCoeff_X _, map_zero _]`. Establish `hci : ∀ p, IntS V (c p)` using `fun p => by`. Simplify using `only [c]`. Use `split_ifs`.

Use `exacts [intS_inT (hγ _).2, intS_X' _, GlobalTheory.RowVal.intS_zero]`. Establish `hc2 : ∀ x, c (2, x) = 0` using `fun x => by simp [c]`. Establish `hS` using `hasSubst_of_constantCoeff_zero hc`. Establish `s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = inT κ (γ x)` using `fun x => by simp [gp, subst_X hS, c]`. Establish `s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = MvPowerSeries.X (some x)` using `fun x => by simp [gp, subst_X hS, c]`.

Establish `s2 : ∀ x, subst c (gp C κ (2 : Fin 3) x) = 0` using `fun x => by simp [gp, subst_X hS, c]`. Establish `hA` using `formalAdd_const h (gp_const (C := C) (κ := κ) (1 : Fin 3)) (gp_const 2)`. Establish `sA : ∀ x, subst c (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) x) = MvPowerSeries.X (some x)` using `fun x => by`. Rewrite using `[subst_addP h (gp_const 1) (gp_const 2) hc]`. Simplify using `only [s1, s2]`.

Unfold `addP`. Establish `z : ∀ y, subst (fun _ : κ => (0 : MvPowerSeries (Option κ) C)) (X.lg y) = 0` using `fun y => subst_eq_zero_of_van (T := Set.univ) (fun _ => map_zero _) (fun _ _ => rfl) (van_univ (lg_const h y))`. Simplify using `only [z, add_zero]`. Conclude with `addP_zero h (fun _ => constantCoeff_X _) x`. Establish `d0 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (0 : Fin 3) x) = 0` using `fun x => pderiv_X_of_ne (by simp)`.

Establish `d1 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (1 : Fin 3) x) = 0` using `fun x => pderiv_X_of_ne (by simp)`. Establish `sM : ∀ j, subst c (pderiv C ((2 : Fin 3), i) (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) j)) = rename some (invM X j i)` using `fun j => by`. Set `e : Fin 2 × κ → MvPowerSeries (Fin 3 × κ) C` to `fun p => if p.1 = 0 then gp C κ 1 p.2 else gp C κ 2 p.2`. Establish `he : ∀ p, constantCoeff (e p) = 0` using `pair_const (gp_const 1) (gp_const 2)`. Establish `hE` using `hasSubst_of_constantCoeff_zero he`.

Establish `e1 : addP X (gp C κ (1 : Fin 3)) (gp C κ 2) j = subst e (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) j)`. Rewrite using `[subst_addP h (gp_const 0) (gp_const 1) he]`. Apply the tactic sequence `congr 1 <;> funext y`. Conclude with `((subst_X hE ((0 : Fin 2), y)).trans (if_pos rfl)).symm`. Conclude with `((subst_X hE ((1 : Fin 2), y)).trans (if_neg (by simp))).symm`.

Rewrite using `[e1, FormalCalc.pderiv_subst hE, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `only [e, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, d1, mul_zero, Finset.sum_const_zero, zero_add]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[show pderiv C ((2 : Fin 3), i) (gp C κ (2 : Fin 3) i) = 1 from pderiv_X_self, mul_one, subst_comp_subst_apply hE hS, invM, rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero axis_const) (HasSubst.X_comp _)]`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Simplify using `only [e]`. Use `split_ifs`. Rewrite using `[s1, subst_X (HasSubst.X_comp _)]`. Both sides reduce to the same expression.

Rewrite using `[s2, ← coe_substAlgHom (HasSubst.X_comp _), map_zero]`. Introduce `x _ hx`. Rewrite using `[show pderiv C ((2 : Fin 3), i) (gp C κ (2 : Fin 3) x) = 0 from pderiv_X_of_ne (by simpa using hx), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `h1` using `intS_subst hc hci (intS_pderiv h.ph2 ((2 : Fin 3), i))`. Establish `h2` using `subst_eq_zero_of_van hc (fun s (hs : s.1 = 2) => by`. Rewrite using `[show s = (2, s.2) from Prod.ext hs rfl]`. Conclude with `hc2 _) (van_pderiv_mvExp (van_defect h) ((2 : Fin 3), i))`. Rewrite `h2` using `[subst_sub hS, sub_eq_zero]`.

Establish `t1 : pderiv C ((2 : Fin 3), i) (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1)) = 0` using `pderiv_subst_eq_zero (pair_const (gp_const 0) (gp_const 1)) (fun p => by split_ifs exacts [d0 _, d1 _]) _`. Establish `hP` using `hasSubst_of_constantCoeff_zero (pair_const (gp_const (C := C) (κ := κ) (0 : Fin 3)) hA)`. Establish `t3 : subst c (pderiv C ((2 : Fin 3), i) (hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2)))) = ∑ j, pderiv C (some j) (hCv X γ) * rename some (invM X j i)`. Unfold `hAt`. Rewrite using `[FormalCalc.pderiv_subst hP, Fintype.sum_prod_type, Fin.sum_univ_two]`.

Simplify using `only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, d0, mul_zero, Finset.sum_const_zero, zero_add]`. Rewrite using `[FormalCalc.subst_sum' hS]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[subst_mul hS, sM, pderiv_hCv X hγ0, subst_comp_subst_apply hP hS]`. Use `congr 2`.

Use function extensionality and compare the values at `p`. Use `split_ifs`. Use `exacts [s0 _, sA _]`. Rewrite `h1` using `[h2, map_sub, map_add, t1, zero_add, subst_sub hS, subst_pderiv_hAt X (gp_const 0) i d0 hc hc2, t3]`. Rewrite using `[inT_alongCv κ hγ0, subst_sg X _ hΓ, neg_neg, Finset.sum_eq_single i]`.

Simplify `h1` using `only [s0, Pi.single_eq_same, one_smul]`. Introduce `x _ hx`. Rewrite using `[Pi.single_eq_of_ne hx, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem intS_invDeriv {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C} (hγ : IsCv V γ)
    (i : κ) : IntS V (-inT κ (alongCv γ (X.sg (Pi.single i 1))) -
      ∑ j, pderiv C (some j) (hCv X γ) * rename some (invM X j i)) := by
  have hγ0 := fun i => (hγ i).1
  have hΓ := fun x => constantCoeff_inT κ (hγ0 x)
  let c : Fin 3 × κ → MvPowerSeries (Option κ) C := fun p =>
    if p.1 = 0 then inT κ (γ p.2) else if p.1 = 1 then MvPowerSeries.X (some p.2) else 0
  have hc : ∀ p, constantCoeff (c p) = 0 := fun p => by
    simp only [c]
    split_ifs
    exacts [hΓ _, constantCoeff_X _, map_zero _]
  have hci : ∀ p, IntS V (c p) := fun p => by
    simp only [c]
    split_ifs
    exacts [intS_inT (hγ _).2, intS_X' _, GlobalTheory.RowVal.intS_zero]
  have hc2 : ∀ x, c (2, x) = 0 := fun x => by simp [c]
  have hS := hasSubst_of_constantCoeff_zero hc
  have s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = inT κ (γ x) := fun x => by simp [gp, subst_X hS, c]
  have s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = MvPowerSeries.X (some x) := fun x => by simp [gp, subst_X hS, c]
  have s2 : ∀ x, subst c (gp C κ (2 : Fin 3) x) = 0 := fun x => by simp [gp, subst_X hS, c]
  have hA := formalAdd_const h (gp_const (C := C) (κ := κ) (1 : Fin 3)) (gp_const 2)
  have sA : ∀ x, subst c (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) x) = MvPowerSeries.X (some x) := fun x => by
    rw [subst_addP h (gp_const 1) (gp_const 2) hc]
    simp only [s1, s2]
    unfold addP
    have z : ∀ y, subst (fun _ : κ => (0 : MvPowerSeries (Option κ) C)) (X.lg y) = 0 := fun y =>
      subst_eq_zero_of_van (T := Set.univ) (fun _ => map_zero _) (fun _ _ => rfl) (van_univ (lg_const h y))
    simp only [z, add_zero]
    exact addP_zero h (fun _ => constantCoeff_X _) x
  have d0 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (0 : Fin 3) x) = 0 := fun x => pderiv_X_of_ne (by simp)
  have d1 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (1 : Fin 3) x) = 0 := fun x => pderiv_X_of_ne (by simp)
  have sM : ∀ j, subst c (pderiv C ((2 : Fin 3), i) (addP X (gp C κ (1 : Fin 3)) (gp C κ 2) j)) =
      rename some (invM X j i) := fun j => by
    let e : Fin 2 × κ → MvPowerSeries (Fin 3 × κ) C := fun p => if p.1 = 0 then gp C κ 1 p.2 else gp C κ 2 p.2
    have he : ∀ p, constantCoeff (e p) = 0 := pair_const (gp_const 1) (gp_const 2)
    have hE := hasSubst_of_constantCoeff_zero he
    have e1 : addP X (gp C κ (1 : Fin 3)) (gp C κ 2) j = subst e (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) j) := by
      rw [subst_addP h (gp_const 0) (gp_const 1) he]
      congr 1 <;> funext y
      · exact ((subst_X hE ((0 : Fin 2), y)).trans (if_pos rfl)).symm
      · exact ((subst_X hE ((1 : Fin 2), y)).trans (if_neg (by simp))).symm
    rw [e1, FormalCalc.pderiv_subst hE, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [e, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, d1, mul_zero, Finset.sum_const_zero,
      zero_add]
    rw [Finset.sum_eq_single i]
    · rw [show pderiv C ((2 : Fin 3), i) (gp C κ (2 : Fin 3) i) = 1 from pderiv_X_self, mul_one,
        subst_comp_subst_apply hE hS, invM, rename_eq_subst,
        subst_comp_subst_apply (hasSubst_of_constantCoeff_zero axis_const) (HasSubst.X_comp _)]
      congr 1
      funext p
      simp only [e]
      split_ifs
      · rw [s1, subst_X (HasSubst.X_comp _)]
        rfl
      · rw [s2, ← coe_substAlgHom (HasSubst.X_comp _), map_zero]
    · intro x _ hx
      rw [show pderiv C ((2 : Fin 3), i) (gp C κ (2 : Fin 3) x) = 0 from pderiv_X_of_ne (by simpa using hx), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h1 := intS_subst hc hci (intS_pderiv h.ph2 ((2 : Fin 3), i))
  have h2 := subst_eq_zero_of_van hc (fun s (hs : s.1 = 2) => by
    rw [show s = (2, s.2) from Prod.ext hs rfl]; exact hc2 _) (van_pderiv_mvExp (van_defect h) ((2 : Fin 3), i))
  rw [subst_sub hS, sub_eq_zero] at h2
  have t1 : pderiv C ((2 : Fin 3), i) (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1)) = 0 :=
    pderiv_subst_eq_zero (pair_const (gp_const 0) (gp_const 1)) (fun p => by
      split_ifs
      exacts [d0 _, d1 _]) _
  have hP := hasSubst_of_constantCoeff_zero (pair_const (gp_const (C := C) (κ := κ) (0 : Fin 3)) hA)
  have t3 : subst c (pderiv C ((2 : Fin 3), i) (hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2)))) =
      ∑ j, pderiv C (some j) (hCv X γ) * rename some (invM X j i) := by
    unfold hAt
    rw [FormalCalc.pderiv_subst hP, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, d0, mul_zero, Finset.sum_const_zero,
      zero_add]
    rw [FormalCalc.subst_sum' hS]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [subst_mul hS, sM, pderiv_hCv X hγ0, subst_comp_subst_apply hP hS]
    congr 2
    funext p
    split_ifs
    exacts [s0 _, sA _]
  rw [h2, map_sub, map_add, t1, zero_add, subst_sub hS, subst_pderiv_hAt X (gp_const 0) i d0 hc hc2, t3] at h1
  rw [inT_alongCv κ hγ0, subst_sg X _ hΓ, neg_neg, Finset.sum_eq_single i]
  · simpa only [s0, Pi.single_eq_same, one_smul] using h1
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `mm_of_mul_matrix (D := fun j => pderiv C j ((V.l : C) • hCoef X γ n)) (intS_invM h) (const_invM h) fun i μ => ?_` and prove the remaining obligations. Establish `h1` using `intS_iff_coeff (intS_invDeriv h hγ i) n μ`. Simplify using `only [map_sub, map_neg, map_sum, map_mul, optionEquivLeft_inT, optionEquivLeft_rename_some, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, ← pderiv_coeff_optionEquivLeft, coeff_hCv X fun i => (hγ i).1] at h1`. Establish `h2` using `hs (Pi.single i 1) fun j => by`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Use `exacts [VF.Ge.one, VF.Ge.zero 0]`. Establish `h3 : V.MM ((V.l : C) * coeff μ (MvPowerSeries.C (PowerSeries.coeff n (alongCv γ (X.sg (Pi.single i 1)))) : MvPowerSeries κ C))`. Rewrite using `[coeff_C]`. Use `split_ifs`.

Conclude with `h2`. Rewrite using `[mul_zero]`. Conclude with `mm_zero`. Establish `h4` using `mm_neg (mm_add (mm_l_mul h1) h3)`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Derivation.map_smul, smul_mul_assoc, map_sum, coeff_smul, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mm_pderiv_l_smul_hCoef {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {γ : κ → PowerSeries C}
    (hγ : IsCv V γ) (n : ℕ)
    (hs : ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff n (alongCv γ (X.sg v)))) :
    ∀ i μ, V.MM (coeff μ (pderiv C i ((V.l : C) • hCoef X γ n))) := by
  refine mm_of_mul_matrix (D := fun j => pderiv C j ((V.l : C) • hCoef X γ n)) (intS_invM h) (const_invM h)
    fun i μ => ?_
  have h1 := intS_iff_coeff (intS_invDeriv h hγ i) n μ
  simp only [map_sub, map_neg, map_sum, map_mul, optionEquivLeft_inT, optionEquivLeft_rename_some,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_map, ← pderiv_coeff_optionEquivLeft,
    coeff_hCv X fun i => (hγ i).1] at h1
  have h2 := hs (Pi.single i 1) fun j => by
    rw [Pi.single_apply]
    split_ifs
    exacts [VF.Ge.one, VF.Ge.zero 0]
  have h3 : V.MM ((V.l : C) * coeff μ
      (MvPowerSeries.C (PowerSeries.coeff n (alongCv γ (X.sg (Pi.single i 1)))) : MvPowerSeries κ C)) := by
    rw [coeff_C]
    split_ifs
    · exact h2
    · rw [mul_zero]; exact mm_zero
  have h4 := mm_neg (mm_add (mm_l_mul h1) h3)
  convert h4 using 1
  simp only [Derivation.map_smul, smul_mul_assoc, map_sum, coeff_smul, ← Finset.mul_sum]
  ring

end GlobalTheory.GaugeCoef

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ h _ hγ hl` and use `⟨GlobalTheory.GaugeCoef.intS_l_smul_hCoef h hγ hl, GlobalTheory.GaugeCoef.mm_pderiv_l_smul_hCoef h hγ _⟩`.
-/
theorem GlobalTheory.GaugeCoef.main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V ((V.l : C) • hCoef X γ V.l) ∧ ((∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg v)))) → ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i ((V.l : C) • hCoef X γ V.l)))) :=
  fun _ _ _ _ _ _ _ _ _ _ h _ hγ hl =>
    ⟨GlobalTheory.GaugeCoef.intS_l_smul_hCoef h hγ hl, GlobalTheory.GaugeCoef.mm_pderiv_l_smul_hCoef h hγ _⟩
