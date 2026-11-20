import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `h` using `I.add n 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)`. Consider the case `succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]`.
-/
theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

/- English proof (translation)
Use `⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `(I.onto n hn hnp z).1 hz`. Establish `h` using `I.isom n hn hnp w v`. Take `⟨t, ht⟩` from `hw v`. Rewrite `h` using `[ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow]`.

Conclude with `h`.
-/
theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

/- English proof (translation)
Introduce `p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x`. Establish `hp : p.Prime` using `Fact.out`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)`. Establish `hm : k ^ 2 / c * c = k ^ 2` using `Nat.div_mul_cancel hck`. Establish `key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v'`.

Introduce `v`. Take `⟨v', hv'⟩` from `hsurj v`. Use `⟨v', ?_⟩` and prove the remaining obligations. Establish `h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v` using `by rw [hv', map_nsmul, nsmul_eq_mul]`. Establish `h2` using `hEF x v'`.

Establish `hcZ : (c : ℤ) ≠ 0` using `by exact_mod_cast hc0`. Establish `hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2` using `by exact_mod_cast hm`. Apply `mul_left_cancel₀ hcZ` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k → (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1`.

Introduce `n j hn hnp hd`. Rewrite using `[← ev_nsmul]`. Use `pair_one I n hn hnp _ (fun v => ?_)` and prove the remaining obligations. Take `⟨v', hv'⟩` from `key v`. Establish `: 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v'`.

Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `hd.mul_right _`. Distinguish the cases in `hp2 : p = 2`.

Substitute `hp2` using the available equality. Take `⟨r, hr⟩ : Odd k` from `Nat.odd_iff.2 (by`. Break down `Nat.mod_two_eq_zero_or_one k with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h2 : 2 ∣ Nat.gcd k 2` using `Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl`.

Rewrite `h2` using `[hk]`. Use linear arithmetic over natural numbers and integers. Conclude with `h)`. Establish `hnp : (N * k).Coprime 2` using `Nat.Coprime.mul hNp hk`. Establish `hn : 0 < N * k` using `Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)`.

Use `⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul, smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]`. Conclude with `core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩`. Establish `h2p : (2 : ℕ).Coprime p` using `(Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)`. Establish `hnp : (N * k * 2).Coprime p` using `Nat.Coprime.mul (Nat.Coprime.mul hNp hk) h2p`.

Establish `hnk : 0 < N * k` using `Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)`. Use `⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩` and prove the remaining obligations. Use `core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩` as an intermediate fact. Simplify `this` using `only [one_smul]`.
-/
theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
