import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp a ha`. Use `Fact.mk hp` as an intermediate fact. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod p)ˣ)`. Establish `hgn : orderOf g = Nat.card (ZMod p)ˣ` using `orderOf_eq_card_of_forall_mem_zpowers hg`. Establish `hn0 : 0 < Nat.card (ZMod p)ˣ` using `Nat.card_pos`.

Establish `gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤` using `fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])`. Establish `hdn : orderOf a ∣ Nat.card (ZMod p)ˣ` using `orderOf_dvd_natCard a`. Establish `hd0 : 0 < orderOf a` using `orderOf_pos a`. Establish `key : orderOf (g ^ 2) ∣ orderOf (a ^ 2)` using `orderOf_dvd_of_mem_zpowers (ha g)`. Rewrite `key` using `[orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn]`.

Generalize the expression as in `Nat.card (ZMod p)ˣ = n at *`. Generalize the expression as in `hd : orderOf a = d at *`. Break down `Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd` into its components or cases. Break down `Nat.even_or_odd d with ⟨e, he⟩ | hd_odd` into its components or cases. Use `⟨a, gen a ?_, rfl⟩` and prove the remaining obligations.

Establish `h1 : n.gcd 2 = 2` using `Nat.gcd_eq_right ⟨m, by omega⟩`. Establish `h2 : d.gcd 2 = 2` using `Nat.gcd_eq_right ⟨e, by omega⟩`. Rewrite `key` using `[h1, h2, show n / 2 = m by omega, show d / 2 = e by omega]`. Establish `h3 : e ∣ m`. Rewrite `hdn` using `[he, hm, ← two_mul, ← two_mul]`.

Conclude with `Nat.dvd_of_mul_dvd_mul_left two_pos hdn`. Use `Nat.dvd_antisymm key h3` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hcop : d.Coprime 2` using `Nat.coprime_two_right.mpr hd_odd`. Establish `h1 : n.gcd 2 = 2` using `Nat.gcd_eq_right ⟨m, by omega⟩`.

Rewrite `key` using `[h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega]`. Establish `h3 : d ∣ m` using `hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])`. Establish `hdm : d = m` using `Nat.dvd_antisymm h3 key`. Establish `hgm : orderOf (g ^ m) = 2`. Use `orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)` as an intermediate fact.

Rewrite `this` using `[show orderOf g / 2 = m by omega]`. Then use the resulting hypothesis. Use `⟨a * g ^ m, gen _ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]`. Use linear arithmetic over natural numbers and integers. Establish `hg1 : g ^ n = 1` using `hgn ▸ pow_orderOf_eq_one g`.

Rewrite using `[mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]`. Establish `hd_odd : Odd d` using `hn_odd.of_dvd_nat hdn`. Use `⟨a, gen a ?_, rfl⟩` and prove the remaining obligations. Rewrite `key` using `[(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one, Nat.div_one, Nat.div_one]`. Rewrite using `[hd]`.

Conclude with `Nat.dvd_antisymm hdn key`.
-/
theorem exists_generator_sq_eq_of_sq_mem_zpowers :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by
  intro p hp a ha
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgn : orderOf g = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : 0 < Nat.card (ZMod p)ˣ := Nat.card_pos
  have gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤ :=
    fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])
  have hdn : orderOf a ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard a
  have hd0 : 0 < orderOf a := orderOf_pos a
  have key : orderOf (g ^ 2) ∣ orderOf (a ^ 2) := orderOf_dvd_of_mem_zpowers (ha g)
  rw [orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn] at key
  generalize Nat.card (ZMod p)ˣ = n at *
  generalize hd : orderOf a = d at *
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd
  · rcases Nat.even_or_odd d with ⟨e, he⟩ | hd_odd
    · refine ⟨a, gen a ?_, rfl⟩
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      have h2 : d.gcd 2 = 2 := Nat.gcd_eq_right ⟨e, by omega⟩
      rw [h1, h2, show n / 2 = m by omega, show d / 2 = e by omega] at key
      have h3 : e ∣ m := by
        rw [he, hm, ← two_mul, ← two_mul] at hdn
        exact Nat.dvd_of_mul_dvd_mul_left two_pos hdn
      have := Nat.dvd_antisymm key h3
      omega
    · have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hd_odd
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      rw [h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega] at key
      have h3 : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])
      have hdm : d = m := Nat.dvd_antisymm h3 key
      have hgm : orderOf (g ^ m) = 2 := by
        have := orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)
        rwa [show orderOf g / 2 = m by omega] at this
      refine ⟨a * g ^ m, gen _ ?_, ?_⟩
      · rw [(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]
        omega
      · have hg1 : g ^ n = 1 := hgn ▸ pow_orderOf_eq_one g
        rw [mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]
  · have hd_odd : Odd d := hn_odd.of_dvd_nat hdn
    refine ⟨a, gen a ?_, rfl⟩
    rw [(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one,
      Nat.div_one, Nat.div_one] at key
    rw [hd]
    exact Nat.dvd_antisymm hdn key

end GlobalTheory
