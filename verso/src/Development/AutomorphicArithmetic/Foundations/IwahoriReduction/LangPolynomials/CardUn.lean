import Mathlib.RingTheory.ZMod.UnitsCyclic
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

namespace UpperTheory.Kd.C7

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hgl : (g : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`. Conclude with `hg`. Establish `hf : (l : ℤ) ∣ (g : ℤ) ^ (l - 1) - 1`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card_sub_one_eq_one hgl, sub_self]`. Take `⟨a, ha⟩` from `hf`. Establish `han : ¬ (l : ℤ) ∣ a`.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `hnd ⟨b, by rw [ha]; ring⟩`. Establish `hga : (g : ℤ) ^ (l - 1) = 1 + l * a`. Rewrite using `[← ha]`. Expand and normalize the polynomial expressions, which then agree.

Break down `r with _ | n` into its components or cases. Establish `: Subsingleton (ZMod (l ^ 0))ˣ`. Rewrite using `[pow_zero]`. Use `infer_instance`. Rewrite using `[Subsingleton.elim x 1]`.

Conclude with `Subgroup.one_mem _`. Use `set u := un g hg (n + 1) with hu`. Establish `hcast : (u : ZMod (l ^ (n + 1))) = (g : ZMod (l ^ (n + 1)))`. Simplify using `[hu, un]`. Establish `h1 : orderOf (u ^ (l - 1)) = l ^ n`.

Rewrite using `[← orderOf_units, Units.val_pow_eq_pow_val, hcast]`. Establish `e : (g : ZMod (l ^ (n + 1))) ^ (l - 1) = 1 + (l : ZMod (l ^ (n + 1))) * (a : ZMod (l ^ (n + 1)))`. Use `congrArg (Int.cast : ℤ → ZMod (l ^ (n + 1))) hga` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Rewrite using `[e]`. Conclude with `ZMod.orderOf_one_add_mul_prime hp hl2 a han n`. Establish `hm : l ∣ l ^ (n + 1)` using `dvd_pow_self l (Nat.succ_ne_zero n)`. Establish `h2 : l - 1 ∣ orderOf u`. Establish `h3 : orderOf (ZMod.unitsMap hm u) = l - 1`.

Rewrite using `[← orderOf_units]`. Establish `: ((ZMod.unitsMap hm u : (ZMod l)ˣ) : ZMod l) = (g : ZMod l)`. Simplify using `[ZMod.unitsMap, hcast]`. Rewrite using `[this, ho]`. Rewrite using `[← h3]`.

Conclude with `orderOf_map_dvd _ u`. Establish `h4 : l ^ n ∣ orderOf u` using `h1 ▸ orderOf_pow_dvd _`. Establish `hcard : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1)`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]`. Establish `hcop : Nat.Coprime (l ^ n) (l - 1)`.

Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_self_sub_right hp.pos]`. Simplify using the standard rewrite rules. Establish `h5 : orderOf u = Nat.card (ZMod (l ^ (n + 1)))ˣ`. Apply `Nat.dvd_antisymm` to reduce the goal to its premises.

Conclude with `orderOf_dvd_natCard u`. Rewrite using `[hcard]`. Conclude with `hcop.mul_dvd_of_dvd_of_dvd h4 h2`. Establish `htop : Subgroup.zpowers u = ⊤`. Apply `Subgroup.eq_top_of_card_eq` to reduce the goal to its premises.

Rewrite using `[Nat.card_zpowers, h5]`. Rewrite using `[htop]`. Conclude with `Subgroup.mem_top x`.
-/
private theorem mem_zpowers_un_of_primitive_root_mod_sq {l : ℕ} [Fact (Nat.Prime l)] (hl2 : l ≠ 2) (g : ℕ) (hg : ¬ l ∣ g)
    (ho : orderOf (g : ZMod l) = l - 1) (hnd : ¬ ((l : ℤ) ^ 2 ∣ (g : ℤ) ^ (l - 1) - 1))
    (r : ℕ) (x : (ZMod (l ^ r))ˣ) : x ∈ Subgroup.zpowers (un g hg r) := by
  have hp : l.Prime := Fact.out
  have hgl : (g : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hg
  have hf : (l : ℤ) ∣ (g : ℤ) ^ (l - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hgl, sub_self]
  obtain ⟨a, ha⟩ := hf
  have han : ¬ (l : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    exact hnd ⟨b, by rw [ha]; ring⟩
  have hga : (g : ℤ) ^ (l - 1) = 1 + l * a := by
    rw [← ha]; ring
  rcases r with _ | n
  · have : Subsingleton (ZMod (l ^ 0))ˣ := by
      rw [pow_zero]; infer_instance
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  set u := un g hg (n + 1) with hu
  have hcast : (u : ZMod (l ^ (n + 1))) = (g : ZMod (l ^ (n + 1))) := by
    simp [hu, un]
  have h1 : orderOf (u ^ (l - 1)) = l ^ n := by
    rw [← orderOf_units, Units.val_pow_eq_pow_val, hcast]
    have e : (g : ZMod (l ^ (n + 1))) ^ (l - 1) = 1 + (l : ZMod (l ^ (n + 1))) * (a : ZMod (l ^ (n + 1))) := by
      have := congrArg (Int.cast : ℤ → ZMod (l ^ (n + 1))) hga
      push_cast at this
      exact this
    rw [e]
    exact ZMod.orderOf_one_add_mul_prime hp hl2 a han n
  have hm : l ∣ l ^ (n + 1) := dvd_pow_self l (Nat.succ_ne_zero n)
  have h2 : l - 1 ∣ orderOf u := by
    have h3 : orderOf (ZMod.unitsMap hm u) = l - 1 := by
      rw [← orderOf_units]
      have : ((ZMod.unitsMap hm u : (ZMod l)ˣ) : ZMod l) = (g : ZMod l) := by
        simp [ZMod.unitsMap, hcast]
      rw [this, ho]
    rw [← h3]
    exact orderOf_map_dvd _ u
  have h4 : l ^ n ∣ orderOf u := h1 ▸ orderOf_pow_dvd _
  have hcard : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcop : Nat.Coprime (l ^ n) (l - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_self_sub_right hp.pos]
    simp
  have h5 : orderOf u = Nat.card (ZMod (l ^ (n + 1)))ˣ := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_natCard u
    · rw [hcard]
      exact hcop.mul_dvd_of_dvd_of_dvd h4 h2
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h5]
  rw [htop]
  exact Subgroup.mem_top x

/- English proof (translation)
Introduce `l _ hl2`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨c, hc⟩` from `isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)`. Rewrite `hc` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `hc0 : (((c : ZMod l).val : ℕ) : ZMod l) = c` using `ZMod.natCast_zmod_val _`.

Use `set c0 : ℕ := (c : ZMod l).val with hc0def`. Establish `hnd0 : ¬ l ∣ c0`. Introduce `h`. Establish `h'` using `(ZMod.natCast_eq_zero_iff c0 l).mpr h`. Rewrite `h'` using `[hc0]`.

Conclude with `c.ne_zero h'`. Establish `hord : ∀ k : ℕ, orderOf ((c0 + l * k : ℕ) : ZMod l) = l - 1`. Introduce `k`. Use `push_cast`. Rewrite using `[ZMod.natCast_self, zero_mul, add_zero, hc0, orderOf_units, hc]`.

Establish `hndk : ∀ k : ℕ, ¬ l ∣ c0 + l * k`. Introduce `k h`. Conclude with `hnd0 ((Nat.dvd_add_left (dvd_mul_right l k)).mp h)`. Establish `hc2 : 2 ≤ c0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Establish `h01 : c0 = 0 ∨ c0 = 1` using `by omega`. Break down `h01 with h0 | h1` into its components or cases. Conclude with `hnd0 (h0 ▸ dvd_zero l)`. Establish `h1' : (c : ZMod l) = 1`.

Rewrite using `[← hc0, h1, Nat.cast_one]`. Establish `hc1 : c = 1` using `Units.ext h1'`. Rewrite `hc` using `[hc1, orderOf_one]`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `hsq : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1) - 1`. Establish `hnd1 : ¬ ((l : ℤ) ^ 2 ∣ ((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1)`. Introduce `hB`. Establish `key` using `sq_dvd_add_pow_sub_sub (l : ℤ) (c0 : ℤ) (l - 1)`. Establish `hsum : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)`.

Establish `e : (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) = (((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1) - (((c0 : ℤ) + l) ^ (l - 1) - (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) - (c0 : ℤ) ^ (l - 1)) - ((c0 : ℤ) ^ (l - 1) - 1)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_sub (dvd_sub hB key) hsq`.

Establish `h6 : (l : ℤ) ∣ (c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ)`. Establish `hl0 : (l : ℤ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Rewrite using `[← mul_dvd_mul_iff_left hl0]`. Establish `e2 : (l : ℤ) * ((c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ)) = (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)` using `by ring`. Rewrite using `[e2, ← sq]`.

Conclude with `hsum`. Establish `h7 : l ∣ c0 ^ (l - 1 - 1) * (l - 1)` using `by exact_mod_cast h6`. Break down `(Nat.Prime.dvd_mul hp).mp h7 with h8 | h8` into its components or cases. Conclude with `hnd0 (hp.dvd_of_dvd_pow h8)`. Use `hp.two_le` as an intermediate fact.

Use `Nat.le_of_dvd (by omega) h8` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `⟨c0 + l * 1, hndk 1, by omega, mem_zpowers_un_of_primitive_root_mod_sq hl2 _ (hndk 1) (hord 1) hnd1⟩`. Establish `h0` using `hord 0`. Simplify using `only [mul_zero, add_zero] at h0`.

Conclude with `⟨c0, hnd0, hc2, mem_zpowers_un_of_primitive_root_mod_sq hl2 c0 hnd0 h0 hsq⟩`.
-/
theorem pGenEx : SGenEx := by
  intro l _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  have hc0 : (((c : ZMod l).val : ℕ) : ZMod l) = c := ZMod.natCast_zmod_val _
  set c0 : ℕ := (c : ZMod l).val with hc0def
  have hnd0 : ¬ l ∣ c0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff c0 l).mpr h
    rw [hc0] at h'
    exact c.ne_zero h'
  have hord : ∀ k : ℕ, orderOf ((c0 + l * k : ℕ) : ZMod l) = l - 1 := by
    intro k
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, hc0, orderOf_units, hc]
  have hndk : ∀ k : ℕ, ¬ l ∣ c0 + l * k := by
    intro k h
    exact hnd0 ((Nat.dvd_add_left (dvd_mul_right l k)).mp h)
  have hc2 : 2 ≤ c0 := by
    by_contra h
    push_neg at h
    have h01 : c0 = 0 ∨ c0 = 1 := by omega
    rcases h01 with h0 | h1
    · exact hnd0 (h0 ▸ dvd_zero l)
    · have h1' : (c : ZMod l) = 1 := by
        rw [← hc0, h1, Nat.cast_one]
      have hc1 : c = 1 := Units.ext h1'
      rw [hc1, orderOf_one] at hc
      have := hp.two_le
      omega
  by_cases hsq : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1) - 1
  · have hnd1 : ¬ ((l : ℤ) ^ 2 ∣ ((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1) := by
      intro hB
      have key := sq_dvd_add_pow_sub_sub (l : ℤ) (c0 : ℤ) (l - 1)
      have hsum : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by
        have e : (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) =
            (((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1)
              - (((c0 : ℤ) + l) ^ (l - 1) - (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)
                - (c0 : ℤ) ^ (l - 1))
              - ((c0 : ℤ) ^ (l - 1) - 1) := by
          push_cast
          ring
        rw [e]
        exact dvd_sub (dvd_sub hB key) hsq
      have h6 : (l : ℤ) ∣ (c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ) := by
        have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [← mul_dvd_mul_iff_left hl0]
        have e2 : (l : ℤ) * ((c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ))
            = (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by ring
        rw [e2, ← sq]
        exact hsum
      have h7 : l ∣ c0 ^ (l - 1 - 1) * (l - 1) := by exact_mod_cast h6
      rcases (Nat.Prime.dvd_mul hp).mp h7 with h8 | h8
      · exact hnd0 (hp.dvd_of_dvd_pow h8)
      · have := hp.two_le
        have := Nat.le_of_dvd (by omega) h8
        omega
    exact ⟨c0 + l * 1, hndk 1, by omega, mem_zpowers_un_of_primitive_root_mod_sq hl2 _ (hndk 1) (hord 1) hnd1⟩
  · have h0 := hord 0
    simp only [mul_zero, add_zero] at h0
    exact ⟨c0, hnd0, hc2, mem_zpowers_un_of_primitive_root_mod_sq hl2 c0 hnd0 h0 hsq⟩

end UpperTheory.Kd.C7
