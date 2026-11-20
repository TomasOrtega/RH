import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTopStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnitStatement

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumIdeal

/- English proof (translation)
Establish `hd : Nat.gcd a (p ^ n) ∣ p ^ n` using `Nat.gcd_dvd_right _ _`. Take `⟨v, hv, hv'⟩` from `(Nat.dvd_prime_pow hp).1 hd`. Establish `hvn : v ≠ n`. Introduce `h`. Apply `ha` to reduce the goal to its premises.

Rewrite using `[← h, ← hv']`. Conclude with `Nat.gcd_dvd_left _ _`. Establish `hlt : Nat.gcd a (p ^ n) < p ^ n`. Rewrite using `[hv']`. Conclude with `Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_ne hv hvn)`.

Take `⟨m, -, hm⟩` from `Nat.exists_mul_mod_eq_gcd hlt`. Use `⟨m * p ^ (n - 1 - v), ?_⟩` and prove the remaining obligations. Establish `e : p ^ (n - 1) = p ^ v * p ^ (n - 1 - v)` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[e, ← hv', ← hm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_mul_modEq_ppow {p : ℕ} (hp : p.Prime) {n a : ℕ} (hn : 1 ≤ n) (ha : ¬ p ^ n ∣ a) :
    ∃ k, k * a ≡ p ^ (n - 1) [MOD p ^ n] := by
  have hd : Nat.gcd a (p ^ n) ∣ p ^ n := Nat.gcd_dvd_right _ _
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hvn : v ≠ n := by
    intro h; apply ha; rw [← h, ← hv']; exact Nat.gcd_dvd_left _ _
  have hlt : Nat.gcd a (p ^ n) < p ^ n := by
    rw [hv']; exact Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_ne hv hvn)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
  refine ⟨m * p ^ (n - 1 - v), ?_⟩
  have e : p ^ (n - 1) = p ^ v * p ^ (n - 1 - v) := by rw [← pow_add]; congr 1; omega
  rw [e, ← hv', ← hm]
  calc m * p ^ (n - 1 - v) * a = (a * m) * p ^ (n - 1 - v) := by ring
    _ ≡ (a * m % p ^ n) * p ^ (n - 1 - v) [MOD p ^ n] := (Nat.mod_modEq _ _).symm.mul_right _

/- English proof (translation)
Introduce `p _ hp2 Ω _ _ hΩ T n r hr hK j hj g hg hgr`. Establish `hp : p.Prime` using `Fact.out`. Use `set C := FixI (Hfix T r) with hC`. Use `set I := Submodule.span C {y : Ω | ∃ x ∈ C, y = g x - x} with hI`. Establish `hr0 : r ≠ 0` using `by rintro rfl; exact hgr (map_zero g)`.

Take `⟨y, E, hy, hE, huniq, hsum⟩` from `GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one p hp2 Ω hΩ T {r} (by simpa using hr) j hj`. Establish `hE' : ∀ e ∈ E, e ∈ Hinf T` using `hE`. Establish `huniq' : ∀ h ∈ Hinf T, ∃! e, e ∈ E ∧ h y = e y ∧ h r = e r`. Introduce `h hh`. Simplify using `using huniq h hh`.

Establish `hex : ∀ k : Gal p Ω, ∃ e, k ∈ Hinf T → e ∈ E ∧ k y = e y ∧ k r = e r`. Introduce `k`. Distinguish the cases in `hk : k ∈ Hinf T`. Take `⟨e, he, -⟩` from `huniq' k hk`. Conclude with `⟨e, fun _ => he⟩`.

Conclude with `⟨1, fun h => absurd h hk⟩`. Use `choose rep hrep using hex`. Establish `runiq : ∀ k ∈ Hinf T, ∀ e ∈ E, k y = e y → k r = e r → rep k = e` using `fun k hk e he h1 h2 => (huniq' k hk).unique (hrep k hk) ⟨he, h1, h2⟩`. Establish `hinv : ∀ h : Gal p Ω, ∀ x, h⁻¹ (h x) = x` using `fun h x => by`. Rewrite using `[← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`.

Establish `hinv' : ∀ h : Gal p Ω, ∀ x, h (h⁻¹ x) = x` using `fun h x => by`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`. Set `Y : Ω → Ω` to `fun ρ => ∑ e ∈ E with e r = ρ, e y`. Establish `hYgal : ∀ h ∈ Hinf T, ∀ ρ, h (Y ρ) = Y (h ρ)`. Introduce `h hh ρ`.

Simplify using `only [Y, map_sum]`. Establish `hmem : ∀ k ∈ Hinf T, ∀ e ∈ E, k * e ∈ Hinf T` using `fun k hk e he => mul_mem hk (hE' e he)`. Use `Finset.sum_nbij' (fun e => rep (h * e)) (fun e => rep (h⁻¹ * e)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `e he`. Simplify using `only [Finset.mem_filter] at he ⊢`.

Take `⟨h1, -, h3⟩` from `hrep _ (hmem h hh e he.1)`. Conclude with `⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2]⟩`. Introduce `e he`. Simplify using `only [Finset.mem_filter] at he ⊢`. Take `⟨h1, -, h3⟩` from `hrep _ (hmem _ (inv_mem hh) e he.1)`.

Conclude with `⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2, hinv]⟩`. Introduce `e he`. Simplify using `only [Finset.mem_filter] at he`. Take `⟨h1, h2, h3⟩` from `hrep _ (hmem h hh e he.1)`. Use `runiq _ (hmem _ (inv_mem hh) _ h1) e he.1 ?_ ?_` and prove the remaining obligations.

Rewrite using `[AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv]`. Rewrite using `[AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv]`. Introduce `e he`. Simplify using `only [Finset.mem_filter] at he`. Take `⟨h1, h2, h3⟩` from `hrep _ (hmem _ (inv_mem hh) e he.1)`.

Use `runiq _ (hmem _ hh _ h1) e he.1 ?_ ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv']`. Rewrite using `[AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv']`. Introduce `e he`. Simplify using `only [Finset.mem_filter] at he`.

Conclude with `(hrep _ (hmem h hh e he.1)).2.1`. Establish `hzn` using `T.prim n`. Establish `hpos : 0 < p ^ n` using `pow_pos hp.pos n`. Establish `hζr : ∀ i : ℕ, T.ζ n ^ i = T.ζ n ^ (i % p ^ n)` using `fun i => by conv_lhs => rw [← Nat.mod_add_div i (p ^ n), pow_add, pow_mul, hzn.pow_eq_one, one_pow, mul_one]`. Set `Z : ℕ → Ω` to `fun i => Y (T.ζ n ^ i * r)`.

Establish `hZC : ∀ i, Z i ∈ C`. Introduce `i`. Use `⟨int_sum _ _ fun e _ => int_gal e hy, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[mem_Hfix]`. Use `show h (Y _) = Y _`.

Rewrite using `[hYgal h hh.1, map_mul, map_pow, (mem_Hinf.1 hh.1 n).1, hh.2]`. Establish `hZmod : ∀ i i', i ≡ i' [MOD p ^ n] → Z i = Z i'`. Introduce `i i' h`. Use `show Y _ = Y _`. Rewrite using `[(GlobalTheory.K5.Basic.zeta_pow_eq_iff T n i i').2 h]`.

Take `⟨a, ha⟩` from `hK g hg`. Establish `hZg : ∀ i, g (Z i) = Z (i + a)`. Introduce `i`. Use `show g (Y _) = Y _`. Rewrite using `[hYgal g hg, map_mul, map_pow, (mem_Hinf.1 hg n).1, ha, pow_add, mul_assoc]`.

Establish `hZa : ∀ i, Z (i + a) - Z i ∈ I` using `fun i => by`. Rewrite using `[← hZg]`. Conclude with `Submodule.subset_span ⟨Z i, hZC i, rfl⟩`. Establish `iter : ∀ b, (∀ i, Z (i + b) - Z i ∈ I) → ∀ t i, Z (i + t * b) - Z i ∈ I`. Introduce `b hb t`.

Proceed by induction on `t with`. Consider the case `zero => intro i`. Simplify using the standard rewrite rules. Consider the case `succ t ih`. Introduce `i`.

Establish `e : i + (t + 1) * b = (i + t * b) + b` using `by ring`. Rewrite using `[e]`. Use `I.add_mem (hb (i + t * b)) (ih i)` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hn : 1 ≤ n`.

Assume the negation of the conclusion as `h0`. Establish `hn0 : n = 0` using `by omega`. Apply `hgr` to reduce the goal to its premises. Rewrite using `[ha, hζr, hn0, pow_zero, Nat.mod_one, pow_zero, one_mul]`. Establish `hna : ¬ p ^ n ∣ a`.

Introduce `hd`. Apply `hgr` to reduce the goal to its premises. Rewrite using `[ha, hζr, Nat.eq_zero_of_dvd_of_lt ?_ (Nat.mod_lt a hpos), pow_zero, one_mul]`. Conclude with `(Nat.dvd_mod_iff dvd_rfl).2 hd`. Take `⟨k, hk⟩` from `exists_mul_modEq_ppow hp hn hna`.

Establish `hZd : ∀ i, Z (i + p ^ (n - 1)) - Z i ∈ I`. Introduce `i`. Rewrite using `[hZmod (i + p ^ (n - 1)) (i + k * a) (Nat.ModEq.add_left i hk.symm)]`. Conclude with `iter a hZa k i`. Use `set d := p ^ (n - 1) with hd`.

Use `set W := ∑ i ∈ Finset.range d, Z i with hW`. Establish `hWC : W ∈ C` using `Subalgebra.sum_mem _ fun i _ => hZC i`. Establish `hsumW : ∀ t : ℕ, ∑ i ∈ Finset.range (t * d), Z i - (t : Ω) * W ∈ I`. Introduce `t`. Proceed by induction on `t with`.

Consider the case `zero => simp`. Consider the case `succ t ih`. Establish `e : (t + 1) * d = t * d + d` using `by ring`. Rewrite using `[e, Finset.sum_range_add]`. Establish `h2 : ∑ x ∈ Finset.range d, Z (t * d + x) - W ∈ I`.

Rewrite using `[hW, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `iter d hZd t x`. Use `I.add_mem ih h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hNd : p * d = p ^ n`. Rewrite using `[hd, ← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hsumZ : ∑ i ∈ Finset.range (p ^ n), Z i = T.ζ j - 1`. Rewrite using `[← hsum]`. Establish `hinj : Set.InjOn (fun i => T.ζ n ^ i * r) (Finset.range (p ^ n) : Set ℕ)`.

Introduce `i hi i' hi' h`. Simplify using `only [Finset.coe_range, Set.mem_Iio] at hi hi'`. Conclude with `hzn.pow_inj hi hi' (mul_right_cancel₀ hr0 h)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := (Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)) (g := fun e : Gal p Ω => e r)]`. Rewrite using `[Finset.sum_image hinj]`.

Introduce `e he`. Take `⟨i, hi⟩` from `hK e (hE' e he)`. Rewrite using `[Finset.mem_image]`. Conclude with `⟨i % p ^ n, Finset.mem_range.2 (Nat.mod_lt _ hpos), by rw [← hζr, hi]⟩`. Establish `hτI : T.ζ j - 1 - (p : Ω) * W ∈ I`.

Use `hsumW p` as an intermediate fact. Rewrite `this` using `[hNd, hsumZ]`. Then use the resulting hypothesis. Establish `hτ0 : T.ζ j - 1 ≠ 0` using `sub_ne_zero.2 ((T.prim j).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))`. Take `⟨hu0, huint⟩` from `GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit p hp2 Ω hΩ T j hj W hWC.1`. Establish `huC : (1 - (p : Ω) / (T.ζ j - 1) * W)⁻¹ ∈ C`.

Use `⟨huint, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[mem_Hfix]`. Rewrite using `[map_inv₀, map_sub, map_one, map_mul, map_div₀, map_sub, map_one, map_natCast, (mem_Hinf.1 hh.1 j).1, hWC.2 h (by rw [mem_Hfix]; exact hh)]`. Use `I.smul_mem (⟨_, huC⟩ : C) hτI` as an intermediate fact. Rewrite `this` using `[Subalgebra.smul_def, smul_eq_mul]`.

Establish `key : T.ζ j - 1 - (p : Ω) * W = (1 - (p : Ω) / (T.ζ j - 1) * W) * (T.ζ j - 1)`. Establish `e2 : (p : Ω) / (T.ζ j - 1) * W * (T.ζ j - 1) = (p : Ω) * W`. Rewrite using `[div_mul_eq_mul_div, div_mul_cancel₀ _ hτ0]`. Rewrite using `[sub_mul, one_mul, e2]`. Rewrite `this` using `[key, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]`.

Conclude with `this`.
-/
theorem zeta_sub_one_mem_span : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  intro p _ hp2 Ω _ _ hΩ T n r hr hK j hj g hg hgr
  classical
  have hp : p.Prime := Fact.out
  set C := FixI (Hfix T r) with hC
  set I := Submodule.span C {y : Ω | ∃ x ∈ C, y = g x - x} with hI
  have hr0 : r ≠ 0 := by rintro rfl; exact hgr (map_zero g)
  obtain ⟨y, E, hy, hE, huniq, hsum⟩ :=
    GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one p hp2 Ω hΩ T {r} (by simpa using hr) j hj
  have hE' : ∀ e ∈ E, e ∈ Hinf T := hE
  have huniq' : ∀ h ∈ Hinf T, ∃! e, e ∈ E ∧ h y = e y ∧ h r = e r := by
    intro h hh; simpa using huniq h hh
  have hex : ∀ k : Gal p Ω, ∃ e, k ∈ Hinf T → e ∈ E ∧ k y = e y ∧ k r = e r := by
    intro k
    by_cases hk : k ∈ Hinf T
    · obtain ⟨e, he, -⟩ := huniq' k hk; exact ⟨e, fun _ => he⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose rep hrep using hex
  have runiq : ∀ k ∈ Hinf T, ∀ e ∈ E, k y = e y → k r = e r → rep k = e := fun k hk e he h1 h2 =>
    (huniq' k hk).unique (hrep k hk) ⟨he, h1, h2⟩
  have hinv : ∀ h : Gal p Ω, ∀ x, h⁻¹ (h x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hinv' : ∀ h : Gal p Ω, ∀ x, h (h⁻¹ x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let Y : Ω → Ω := fun ρ => ∑ e ∈ E with e r = ρ, e y
  have hYgal : ∀ h ∈ Hinf T, ∀ ρ, h (Y ρ) = Y (h ρ) := by
    intro h hh ρ
    simp only [Y, map_sum]
    have hmem : ∀ k ∈ Hinf T, ∀ e ∈ E, k * e ∈ Hinf T := fun k hk e he => mul_mem hk (hE' e he)
    refine Finset.sum_nbij' (fun e => rep (h * e)) (fun e => rep (h⁻¹ * e)) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem h hh e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2]⟩
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2, hinv]⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem h hh e he.1)
      refine runiq _ (hmem _ (inv_mem hh) _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv]
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv]
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      refine runiq _ (hmem _ hh _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv']
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv']
    · intro e he
      simp only [Finset.mem_filter] at he
      exact (hrep _ (hmem h hh e he.1)).2.1

  have hzn := T.prim n
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have hζr : ∀ i : ℕ, T.ζ n ^ i = T.ζ n ^ (i % p ^ n) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i (p ^ n), pow_add, pow_mul, hzn.pow_eq_one, one_pow, mul_one]
  let Z : ℕ → Ω := fun i => Y (T.ζ n ^ i * r)
  have hZC : ∀ i, Z i ∈ C := by
    intro i
    refine ⟨int_sum _ _ fun e _ => int_gal e hy, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    show h (Y _) = Y _
    rw [hYgal h hh.1, map_mul, map_pow, (mem_Hinf.1 hh.1 n).1, hh.2]
  have hZmod : ∀ i i', i ≡ i' [MOD p ^ n] → Z i = Z i' := by
    intro i i' h
    show Y _ = Y _
    rw [(GlobalTheory.K5.Basic.zeta_pow_eq_iff T n i i').2 h]
  obtain ⟨a, ha⟩ := hK g hg
  have hZg : ∀ i, g (Z i) = Z (i + a) := by
    intro i
    show g (Y _) = Y _
    rw [hYgal g hg, map_mul, map_pow, (mem_Hinf.1 hg n).1, ha, pow_add, mul_assoc]
  have hZa : ∀ i, Z (i + a) - Z i ∈ I := fun i => by
    rw [← hZg]; exact Submodule.subset_span ⟨Z i, hZC i, rfl⟩
  have iter : ∀ b, (∀ i, Z (i + b) - Z i ∈ I) → ∀ t i, Z (i + t * b) - Z i ∈ I := by
    intro b hb t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have e : i + (t + 1) * b = (i + t * b) + b := by ring
      rw [e]
      have := I.add_mem (hb (i + t * b)) (ih i)
      rwa [sub_add_sub_cancel] at this
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    apply hgr
    rw [ha, hζr, hn0, pow_zero, Nat.mod_one, pow_zero, one_mul]
  have hna : ¬ p ^ n ∣ a := by
    intro hd
    apply hgr
    rw [ha, hζr, Nat.eq_zero_of_dvd_of_lt ?_ (Nat.mod_lt a hpos), pow_zero, one_mul]
    exact (Nat.dvd_mod_iff dvd_rfl).2 hd
  obtain ⟨k, hk⟩ := exists_mul_modEq_ppow hp hn hna
  have hZd : ∀ i, Z (i + p ^ (n - 1)) - Z i ∈ I := by
    intro i
    rw [hZmod (i + p ^ (n - 1)) (i + k * a) (Nat.ModEq.add_left i hk.symm)]
    exact iter a hZa k i
  set d := p ^ (n - 1) with hd
  set W := ∑ i ∈ Finset.range d, Z i with hW
  have hWC : W ∈ C := Subalgebra.sum_mem _ fun i _ => hZC i
  have hsumW : ∀ t : ℕ, ∑ i ∈ Finset.range (t * d), Z i - (t : Ω) * W ∈ I := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e : (t + 1) * d = t * d + d := by ring
      rw [e, Finset.sum_range_add]
      have h2 : ∑ x ∈ Finset.range d, Z (t * d + x) - W ∈ I := by
        rw [hW, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun x _ => ?_
        rw [add_comm]; exact iter d hZd t x
      have := I.add_mem ih h2
      convert this using 1
      push_cast; ring
  have hNd : p * d = p ^ n := by
    rw [hd, ← pow_succ']; congr 1; omega
  have hsumZ : ∑ i ∈ Finset.range (p ^ n), Z i = T.ζ j - 1 := by
    rw [← hsum]
    have hinj : Set.InjOn (fun i => T.ζ n ^ i * r) (Finset.range (p ^ n) : Set ℕ) := by
      intro i hi i' hi' h
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      exact hzn.pow_inj hi hi' (mul_right_cancel₀ hr0 h)
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r))
      (g := fun e : Gal p Ω => e r)]
    · rw [Finset.sum_image hinj]
    · intro e he
      obtain ⟨i, hi⟩ := hK e (hE' e he)
      rw [Finset.mem_image]
      exact ⟨i % p ^ n, Finset.mem_range.2 (Nat.mod_lt _ hpos), by rw [← hζr, hi]⟩
  have hτI : T.ζ j - 1 - (p : Ω) * W ∈ I := by
    have := hsumW p
    rwa [hNd, hsumZ] at this
  have hτ0 : T.ζ j - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim j).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))
  obtain ⟨hu0, huint⟩ := GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit p hp2 Ω hΩ T j hj W hWC.1
  have huC : (1 - (p : Ω) / (T.ζ j - 1) * W)⁻¹ ∈ C := by
    refine ⟨huint, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    rw [map_inv₀, map_sub, map_one, map_mul, map_div₀, map_sub, map_one, map_natCast,
      (mem_Hinf.1 hh.1 j).1, hWC.2 h (by rw [mem_Hfix]; exact hh)]
  have := I.smul_mem (⟨_, huC⟩ : C) hτI
  rw [Subalgebra.smul_def, smul_eq_mul] at this
  have key : T.ζ j - 1 - (p : Ω) * W = (1 - (p : Ω) / (T.ζ j - 1) * W) * (T.ζ j - 1) := by
    have e2 : (p : Ω) / (T.ζ j - 1) * W * (T.ζ j - 1) = (p : Ω) * W := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hτ0]
    rw [sub_mul, one_mul, e2]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at this
  exact this

end GlobalTheory.KumIdeal
