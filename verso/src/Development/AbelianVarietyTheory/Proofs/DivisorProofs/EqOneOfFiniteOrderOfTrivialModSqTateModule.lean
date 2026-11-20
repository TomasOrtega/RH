import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]`.
-/
theorem lev_nsmul (t : Tate l M) (n m : ℕ) : (n • t).lev m = t.lev m ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lev_neg (t : Tate l M) (m : ℕ) : (-t).lev m = (t.lev m)⁻¹ := rfl

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, Tate.lev_add, lev_neg]`.
-/
theorem lev_sub (s t : Tate l M) (m : ℕ) : (s - t).lev m = s.lev m * (t.lev m)⁻¹ := by
  rw [sub_eq_add_neg, Tate.lev_add, lev_neg]

def Dv (k : ℕ) (t : Tate l M) : Prop := ∃ s : Tate l M, t = (l ^ k) • s

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, (smul_zero _).symm⟩`.
-/
theorem dv_zero (k : ℕ) : Dv k (0 : Tate l M) := ⟨0, (smul_zero _).symm⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hs`. Take `⟨b, rfl⟩` from `ht`. Conclude with `⟨a + b, (smul_add _ _ _).symm⟩`.
-/
theorem dv_add {k : ℕ} {s t : Tate l M} (hs : Dv k s) (ht : Dv k t) : Dv k (s + t) := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  exact ⟨a + b, (smul_add _ _ _).symm⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `ht`. Conclude with `⟨-a, (smul_neg _ _).symm⟩`.
-/
theorem dv_neg {k : ℕ} {t : Tate l M} (ht : Dv k t) : Dv k (-t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨-a, (smul_neg _ _).symm⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `ht`. Conclude with `⟨n • a, smul_comm _ _ _⟩`.
-/
theorem dv_nsmul {k : ℕ} (n : ℕ) {t : Tate l M} (ht : Dv k t) : Dv k (n • t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨n • a, smul_comm _ _ _⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction f (Dv k) (fun _ _ => dv_add) (dv_zero k) h`.
-/
theorem dv_sum {k : ℕ} {Ix : Type} (s : Finset Ix) (f : Ix → Tate l M) (h : ∀ i ∈ s, Dv k (f i)) :
    Dv k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Dv k) (fun _ _ => dv_add) (dv_zero k) h

/- English proof (translation)
Take `⟨a, rfl⟩` from `ht`. Use `⟨l ^ (k' - k) • a, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← pow_add, Nat.add_sub_cancel' hk]`.
-/
theorem dv_mono {k k' : ℕ} (hk : k ≤ k') {t : Tate l M} (ht : Dv k' t) : Dv k t := by
  obtain ⟨a, rfl⟩ := ht
  refine ⟨l ^ (k' - k) • a, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hk]

/- English proof (translation)
Use extensionality with `m`. Use `show t.lev m = 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_nsmul {t : Tate l M} (h : l • t = 0) : t = 0 := by
  ext m
  show t.lev m = 1
  calc t.lev m = t.lev (m + 1) ^ l := (Tate.lev_succ t m).symm
    _ = (l • t).lev (m + 1) := (lev_nsmul t l (m + 1)).symm
    _ = 1 := by rw [h]; rfl

/- English proof (translation)
Proceed by induction on `a generalizing z with`. Consider the case `zero => simpa using h`. Consider the case `succ a ih => exact eq_zero_of_nsmul (ih (by rw [smul_smul, ← pow_succ]; exact h))`.
-/
theorem eq_zero_of_pow_nsmul (a : ℕ) {z : Tate l M} (h : (l ^ a) • z = 0) : z = 0 := by
  induction a generalizing z with
  | zero => simpa using h
  | succ a ih => exact eq_zero_of_nsmul (ih (by rw [smul_smul, ← pow_succ]; exact h))

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (eq_zero_of_pow_nsmul a (by rw [smul_sub, h, sub_self]))`.
-/
theorem pow_nsmul_cancel (a : ℕ) {x y : Tate l M} (h : (l ^ a) • x = (l ^ a) • y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_pow_nsmul a (by rw [smul_sub, h, sub_self]))

/- English proof (translation)
Take `⟨r, hr⟩` from `h`. Conclude with `⟨r, pow_nsmul_cancel a (by rw [hr, pow_add, smul_smul])⟩`.
-/
theorem dv_of_pow_nsmul {a b : ℕ} {s : Tate l M} (h : Dv (a + b) ((l ^ a) • s)) : Dv b s := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, pow_nsmul_cancel a (by rw [hr, pow_add, smul_smul])⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `h`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hq`. Use `⟨a • r + b • s, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[natCast_zsmul, natCast_zsmul, hr, pow_one, smul_add, smul_comm a l r, smul_comm b l s]`.
-/
theorem dv_one_of_nsmul {q : ℕ} (hq : Nat.Coprime q l) {s : Tate l M} (h : Dv 1 (q • s)) :
    Dv 1 s := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hq
  refine ⟨a • r + b • s, ?_⟩
  calc s = (a * (q : ℤ) + b * (l : ℤ)) • s := by rw [hab, one_smul]
    _ = a • ((q : ℤ) • s) + b • ((l : ℤ) • s) := by rw [add_smul, mul_smul, mul_smul]
    _ = l ^ 1 • (a • r + b • s) := by
      rw [natCast_zsmul, natCast_zsmul, hr, pow_one, smul_add, smul_comm a l r, smul_comm b l s]

/- English proof (translation)
Use extensionality with `k`. Use `show t.lev k = 1`. Take `⟨s, hs⟩` from `h k`. Rewrite using `[hs, lev_nsmul, Tate.lev_pow]`.
-/
theorem eq_zero_of_dv {t : Tate l M} (h : ∀ k, Dv k t) : t = 0 := by
  ext k
  show t.lev k = 1
  obtain ⟨s, hs⟩ := h k
  rw [hs, lev_nsmul, Tate.lev_pow]

/- English proof (translation)
Use `⟨Tate.mk (fun n => w.lev (n + 2)) fun n => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm, Tate.lev_add_pow, h]`. Conclude with `Tate.lev_succ w (n + 2)`. Use extensionality with `n`. Rewrite using `[lev_nsmul, Tate.lev_mk, Tate.lev_add_pow]`.
-/
theorem dv_two_of_lev {w : Tate l M} (h : w.lev 2 = 1) : Dv 2 w := by
  refine ⟨Tate.mk (fun n => w.lev (n + 2)) fun n => ⟨?_, ?_⟩, ?_⟩
  · rw [add_comm, Tate.lev_add_pow, h]
  · exact Tate.lev_succ w (n + 2)
  · ext n
    rw [lev_nsmul, Tate.lev_mk, Tate.lev_add_pow]

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

section Endo

variable {l : ℕ} [Fact l.Prime] {M : Type} [CommGroup M]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro t`. Rewrite using `[pow_zero, Module.End.one_apply, sub_self]`. Conclude with `dv_zero k`. Consider the case `succ n ih`.

Introduce `t`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `e : u ((u ^ n) t) - t = (u ((u ^ n) t) - (u ^ n) t) + ((u ^ n) t - t)` using `by abel`. Rewrite using `[e]`. Conclude with `dv_add (h _) (ih t)`.
-/
theorem dv_pow_sub (k : ℕ) {u : Module.End ℤ_[l] (Tate l M)} (h : ∀ t, Dv k (u t - t)) (n : ℕ) :
    ∀ t, Dv k ((u ^ n) t - t) := by
  induction n with
  | zero => intro t; rw [pow_zero, Module.End.one_apply, sub_self]; exact dv_zero k
  | succ n ih =>
    intro t
    rw [pow_succ', Module.End.mul_apply]
    have e : u ((u ^ n) t) - t = (u ((u ^ n) t) - (u ^ n) t) + ((u ^ n) t - t) := by abel
    rw [e]
    exact dv_add (h _) (ih t)

/- English proof (translation)
Use `set D := v - 1 with hD`. Establish `hDt : ∀ t, D t = v t - t` using `fun t => by`. Rewrite using `[hD, LinearMap.sub_apply, Module.End.one_apply]`. Establish `hmap : ∀ a t, Dv a t → Dv (a + k) (D t)`. Introduce and unpack `a _ ⟨s, rfl⟩`.

Take `⟨r, hr⟩` from `h s`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, hDt, hr, pow_add, smul_smul]`. Establish `hpow : ∀ j t, Dv (j * k) ((D ^ j) t)`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro t; exact ⟨t, by rw [pow_zero, Module.End.one_apply, zero_mul, pow_zero, one_smul]⟩`. Consider the case `succ j ih`. Introduce `t`. Rewrite using `[pow_succ', Module.End.mul_apply, Nat.succ_mul]`.

Conclude with `hmap _ _ (ih t)`. Take `⟨r, rfl⟩ : ∃ r, q = r + 1 + 1` from `⟨q - 2, by have := hq.two_le; omega⟩`. Establish `hvD : v = D + 1` using `by rw [hD, sub_add_cancel]`. Establish `key` using `congrArg (fun f : Module.End ℤ_[l] (Tate l M) => f t) hv`. Rewrite `key` using `[hvD, (Commute.one_right D).add_pow, Finset.sum_range_succ', Finset.sum_range_succ']`.

Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, one_pow, _root_.mul_one, Module.End.natCast_apply, map_nsmul, pow_zero, Nat.choose_zero_right, Nat.choose_one_right, pow_one, Module.End.one_apply, one_smul, zero_add, Nat.cast_one] at key`. Establish `hS : Dv (k + 2) (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t)` using `dv_sum _ _ fun x _ => dv_nsmul _ (dv_mono (by nlinarith) (hpow (x + 1 + 1) t))`. Establish `hqD : (r + 1 + 1) • D t = -(∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t)`. Combine the equalities or inequalities in the displayed calculation. Normalize the expressions using the abelian group laws.

Use `_ = t - t - (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by rw [key]`. Use `_ = _ := by abel`. Establish `hq2 : Dv (k + 2) ((r + 1 + 1) • D t)` using `hqD ▸ dv_neg hS`. Take `⟨s, hs⟩` from `h t`. Rewrite `hq2` using `[hDt, hs, smul_comm (r + 1 + 1) (l ^ k) s]`.

Establish `h2 : Dv 2 ((r + 1 + 1) • s)` using `dv_of_pow_nsmul hq2`. Establish `h1 : Dv 1 s`. Distinguish the cases in `hql : r + 1 + 1 = l`. Rewrite `h2` using `[hql]`. Conclude with `dv_of_pow_nsmul (a := 1) (b := 1) (by rw [pow_one]; exact h2)`.

Conclude with `dv_one_of_nsmul ((Nat.coprime_primes hq Fact.out).2 hql) (dv_mono (by norm_num) h2)`. Take `⟨r', hr'⟩` from `h1`. Conclude with `⟨r', by rw [hs, hr', pow_one, smul_smul, ← pow_succ]⟩`.
-/
theorem dv_succ_of_pow_eq_one {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)}
    (hv : v ^ q = 1) {k : ℕ} (hk : 2 ≤ k) (h : ∀ t, Dv k (v t - t)) (t : Tate l M) :
    Dv (k + 1) (v t - t) := by
  set D := v - 1 with hD
  have hDt : ∀ t, D t = v t - t := fun t => by
    rw [hD, LinearMap.sub_apply, Module.End.one_apply]
  have hmap : ∀ a t, Dv a t → Dv (a + k) (D t) := by
    rintro a _ ⟨s, rfl⟩
    obtain ⟨r, hr⟩ := h s
    refine ⟨r, ?_⟩
    rw [map_nsmul, hDt, hr, pow_add, smul_smul]
  have hpow : ∀ j t, Dv (j * k) ((D ^ j) t) := by
    intro j
    induction j with
    | zero => intro t; exact ⟨t, by rw [pow_zero, Module.End.one_apply, zero_mul, pow_zero, one_smul]⟩
    | succ j ih =>
      intro t
      rw [pow_succ', Module.End.mul_apply, Nat.succ_mul]
      exact hmap _ _ (ih t)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by have := hq.two_le; omega⟩
  have hvD : v = D + 1 := by rw [hD, sub_add_cancel]
  have key := congrArg (fun f : Module.End ℤ_[l] (Tate l M) => f t) hv
  rw [hvD, (Commute.one_right D).add_pow, Finset.sum_range_succ', Finset.sum_range_succ'] at key
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    one_pow, _root_.mul_one, Module.End.natCast_apply, map_nsmul, pow_zero, Nat.choose_zero_right,
    Nat.choose_one_right, pow_one, Module.End.one_apply, one_smul, zero_add, Nat.cast_one] at key
  have hS : Dv (k + 2) (∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) :=
    dv_sum _ _ fun x _ => dv_nsmul _ (dv_mono (by nlinarith) (hpow (x + 1 + 1) t))
  have hqD : (r + 1 + 1) • D t = -(∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
    calc (r + 1 + 1) • D t = ((∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) + (r + 1 + 1) • D t + t) - t -
          (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
          abel
      _ = t - t - (∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by rw [key]
      _ = _ := by abel
  have hq2 : Dv (k + 2) ((r + 1 + 1) • D t) := hqD ▸ dv_neg hS
  obtain ⟨s, hs⟩ := h t
  rw [hDt, hs, smul_comm (r + 1 + 1) (l ^ k) s] at hq2
  have h2 : Dv 2 ((r + 1 + 1) • s) := dv_of_pow_nsmul hq2
  have h1 : Dv 1 s := by
    by_cases hql : r + 1 + 1 = l
    · rw [hql] at h2
      exact dv_of_pow_nsmul (a := 1) (b := 1) (by rw [pow_one]; exact h2)
    · exact dv_one_of_nsmul ((Nat.coprime_primes hq Fact.out).2 hql) (dv_mono (by norm_num) h2)
  obtain ⟨r', hr'⟩ := h1
  exact ⟨r', by rw [hs, hr', pow_one, smul_smul, ← pow_succ]⟩

/- English proof (translation)
Establish `hall : ∀ k, 2 ≤ k → ∀ t, Dv k (v t - t)`. Introduce `k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact h`. Consider the case `succ k hk ih => exact dv_succ_of_pow_eq_one hq hv hk ih`.

Use `LinearMap.ext fun t => ?_` and prove the remaining obligations. Establish `h0 : v t - t = 0` using `eq_zero_of_dv fun k => dv_mono (le_max_left k 2) (hall _ (le_max_right k 2) t)`. Rewrite using `[Module.End.one_apply]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem eq_one_of_prime {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)} (hv : v ^ q = 1)
    (h : ∀ t, Dv 2 (v t - t)) : v = 1 := by
  have hall : ∀ k, 2 ≤ k → ∀ t, Dv k (v t - t) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k hk ih => exact dv_succ_of_pow_eq_one hq hv hk ih
  refine LinearMap.ext fun t => ?_
  have h0 : v t - t = 0 :=
    eq_zero_of_dv fun k => dv_mono (le_max_left k 2) (hall _ (le_max_right k 2) t)
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 h0

end Endo

end GlobalTheory.MinkowskiTate

/- English proof (translation)
Introduce `l _ M _ u E hE hu h2`. Establish `h : ∀ t, GlobalTheory.MinkowskiTate.Dv 2 (u t - t)` using `fun t => GlobalTheory.MinkowskiTate.dv_two_of_lev (by rw [GlobalTheory.MinkowskiTate.lev_sub, h2, mul_inv_cancel])`. Proceed by induction on `E using Nat.strong_induction_on with`. Consider the case `_ E ih`. Break down `Nat.lt_or_ge E 2 with hlt | hge` into its components or cases.

Take `rfl : E = 1` from `by omega`. Rewrite `hu` using `[pow_one]`. Then use the resulting hypothesis. Establish `hq : E.minFac.Prime` using `Nat.minFac_prime (by omega)`. Take `⟨E₁, hE₁⟩` from `Nat.minFac_dvd E`. Establish `hpos : 0 < E₁` using `Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hE₁; omega`.

Establish `hlt : E₁ < E`. Use `hq.two_le` as an intermediate fact. Rewrite using `[hE₁]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hv : (u ^ E₁) ^ E.minFac = 1` using `by rw [← pow_mul, mul_comm, ← hE₁, hu]`.

Conclude with `ih E₁ hlt hpos (GlobalTheory.MinkowskiTate.eq_one_of_prime hq hv (GlobalTheory.MinkowskiTate.dv_pow_sub 2 h E₁))`.
-/
theorem GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two : ∀ (l : ℕ) [Fact l.Prime] (M : Type)
    [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 →
    (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  intro l _ M _ u E hE hu h2
  have h : ∀ t, GlobalTheory.MinkowskiTate.Dv 2 (u t - t) := fun t =>
    GlobalTheory.MinkowskiTate.dv_two_of_lev (by rw [GlobalTheory.MinkowskiTate.lev_sub, h2, mul_inv_cancel])
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases Nat.lt_or_ge E 2 with hlt | hge
    · obtain rfl : E = 1 := by omega
      rwa [pow_one] at hu
    · have hq : E.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨E₁, hE₁⟩ := Nat.minFac_dvd E
      have hpos : 0 < E₁ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hE₁; omega
      have hlt : E₁ < E := by
        have := hq.two_le
        rw [hE₁]
        nlinarith
      have hv : (u ^ E₁) ^ E.minFac = 1 := by rw [← pow_mul, mul_comm, ← hE₁, hu]
      exact ih E₁ hlt hpos (GlobalTheory.MinkowskiTate.eq_one_of_prime hq hv
        (GlobalTheory.MinkowskiTate.dv_pow_sub 2 h E₁))
