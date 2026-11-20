import Mathlib
import Formalism.TameInertiaTowers.StatementGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic

namespace Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Introduce `H _ N hN h2 z hz`. Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`. Distinguish the cases in `hz1 : z = 1`. Simplify using `[hz1]`.

Establish `hc : g * z * g⁻¹ ∈ N` using `hN.conj_mem z hz g`. Take `⟨y, hy, huniq⟩` from `(Nat.card_eq_two_iff' (1 : N)).mp h2`. Establish `e1 : (⟨g * z * g⁻¹, hc⟩ : N) = y` using `huniq _ (by`. Introduce `h`. Apply `hz1` to reduce the goal to its premises.

Establish `h' : g * z * g⁻¹ = 1` using `congrArg Subtype.val h`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (⟨z, hz⟩ : N) = y` using `huniq _ (by`. Introduce `h`. Conclude with `hz1 (congrArg Subtype.val h))`.

Establish `: g * z * g⁻¹ = z` using `congrArg Subtype.val (e1.trans e2.symm)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem normalOrderTwoCentral : NormalOrderTwoCentral := by
  intro H _ N hN h2 z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · simp [hz1]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h2
  have e1 : (⟨g * z * g⁻¹, hc⟩ : N) = y := huniq _ (by
    intro h; apply hz1
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have e2 : (⟨z, hz⟩ : N) = y := huniq _ (by
    intro h; exact hz1 (congrArg Subtype.val h))
  have : g * z * g⁻¹ = z := congrArg Subtype.val (e1.trans e2.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [this]

/- English proof (translation)
Establish `: ((5 : ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ)` using `by norm_num`. Rewrite using `[this, padicValInt.of_nat, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]`.
-/
lemma v24 : padicValInt 2 ((5 : ℤ) ^ 2 - 1) = 3 := by
  have : ((5 : ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

/- English proof (translation)
Establish `: ((5 : ℤ) - 1) = ((2 ^ 2 : ℕ) : ℤ)` using `by norm_num`. Rewrite using `[this, padicValInt.of_nat, padicValNat.prime_pow]`.
-/
lemma v4 : padicValInt 2 ((5 : ℤ) - 1) = 2 := by
  have : ((5 : ℤ) - 1) = ((2 ^ 2 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/- English proof (translation)
Introduce `s e he`. Establish `h5 : Odd (5 : ℤ)` using `by decide`. Establish `h52 : (5 : ℤ) ^ 2 ≠ 1` using `by norm_num`. Establish `hpos : 0 < 2 ^ s * e` using `Nat.mul_pos (Nat.two_pow_pos s) he`. Establish `key` using `(twoAdicVal 5 h5 h52 (2 ^ s * e) hpos).1`.

Rewrite using `[key]`. Use `split_ifs with hev`. Rewrite using `[v24, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[v4]`.

Establish `hs : s = 0`. Break down `Nat.eq_zero_or_pos s with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `hev` to reduce the goal to its premises.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_lt h`. Conclude with `⟨2 ^ k * e, by ring⟩`. Substitute `hs` using the available equality. Establish `he' : ¬ 2 ∣ e`. Introduce `hd`.

Apply `hev` to reduce the goal to its premises. Simplify using `using (even_iff_two_dvd.mpr hd)`. Rewrite using `[padicValNat.eq_zero_of_not_dvd he']`.
-/
theorem twistVal : TwistVal := by
  intro s e he
  have h5 : Odd (5 : ℤ) := by decide
  have h52 : (5 : ℤ) ^ 2 ≠ 1 := by norm_num
  have hpos : 0 < 2 ^ s * e := Nat.mul_pos (Nat.two_pow_pos s) he
  have key := (twoAdicVal 5 h5 h52 (2 ^ s * e) hpos).1
  rw [key]
  split_ifs with hev
  · rw [v24, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
    omega
  · rw [v4]
    have hs : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · exfalso; apply hev
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
        exact ⟨2 ^ k * e, by ring⟩
    subst hs
    have he' : ¬ 2 ∣ e := by
      intro hd; apply hev; simpa using (even_iff_two_dvd.mpr hd)
    rw [padicValNat.eq_zero_of_not_dvd he']

/- English proof (translation)
Establish `hp : Nat.Prime 2` using `Nat.prime_two`. Take `⟨v, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk 2 (by norm_num)`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`. Establish `hv : padicValNat 2 (2 ^ v * m) = v`. Rewrite using `[padicValNat.mul (by positivity) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]`.

Rewrite using `[hv]`. Establish `hcop : Nat.Coprime m (2 ^ N)`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Conclude with `(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))`. Rewrite using `[Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]`.

Break down `le_total N v with h | h` into its components or cases. Rewrite using `[min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]`. Rewrite using `[min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]`.
-/
lemma gcd_two_pow (N k : ℕ) (hk : k ≠ 0) : Nat.gcd (2 ^ N) k = 2 ^ min N (padicValNat 2 k) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv : padicValNat 2 (2 ^ v * m) = v := by
    rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [hv]
  have hcop : Nat.Coprime m (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]
  rcases le_total N v with h | h
  · rw [min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]

/- English proof (translation)
Introduce `N u _ hu1`. Use `set k := (u - 1).natAbs with hkdef`. Establish `hk : k ≠ 0`. Rewrite using `[hkdef]`. Introduce `h`.

Apply `hu1` to reduce the goal to its premises. Use `Int.natAbs_eq_zero.mp h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N)) = AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))`. Break down `Int.natAbs_eq (u - 1) with h | h` into its components or cases.

Rewrite using `[h]`. Simplify using `[hkdef]`. Rewrite using `[h]`. Simplify using `[hkdef]`. Rewrite using `[hsub]`.

Establish `hN : (2 ^ N : ℕ) ≠ 0` using `by positivity`. Establish `hc` using `AddSubgroup.card_mul_index (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)))`. Rewrite `hc` using `[Nat.card_zmultiples, ZMod.addOrderOf_coe _ hN, Nat.card_zmod]`. Establish `hidx : (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))).index = Nat.gcd (2 ^ N) k`. Establish `hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N` using `Nat.gcd_dvd_left _ _`.

Establish `hgpos : 0 < Nat.gcd (2 ^ N) k` using `Nat.gcd_pos_of_pos_left _ (by positivity)`. Establish `hd : 2 ^ N / Nat.gcd (2 ^ N) k * Nat.gcd (2 ^ N) k = 2 ^ N` using `Nat.div_mul_cancel hg`. Establish `hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k` using `Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos`. Conclude with `Nat.eq_of_mul_eq_mul_left hdpos (hc.trans hd.symm)`. Rewrite using `[← AddSubgroup.index, hidx, gcd_two_pow N k hk]`.

Both sides reduce to the same expression.
-/
theorem coinvLength : CoinvLength := by
  intro N u _ hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hsub : AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N)) =
      AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)) := by
    rcases Int.natAbs_eq (u - 1) with h | h
    · rw [h]; simp [hkdef]
    · rw [h]; simp [hkdef]
  rw [hsub]
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have hc := AddSubgroup.card_mul_index (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)))
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hN, Nat.card_zmod] at hc
  have hidx : (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))).index = Nat.gcd (2 ^ N) k := by
    have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
    have hd : 2 ^ N / Nat.gcd (2 ^ N) k * Nat.gcd (2 ^ N) k = 2 ^ N := Nat.div_mul_cancel hg
    have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
      Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
    exact Nat.eq_of_mul_eq_mul_left hdpos (hc.trans hd.symm)
  rw [← AddSubgroup.index, hidx, gcd_two_pow N k hk]
  rfl

/- English proof (translation)
Introduce `G _ _ A B C hsup hcard a ha b hb c hc habc`. Set `f : A × B × C →* G` to `A.subtype.coprod (B.subtype.coprod C.subtype)`. Establish `hf : ∀ x : A × B × C, f x = (x.1 : G) * ((x.2.1 : G) * (x.2.2 : G))` using `fun x => rfl`. Establish `hsurj : Function.Surjective f`. Rewrite using `[← MonoidHom.range_eq_top, eq_top_iff, ← hsup]`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Introduce `x hx; exact ⟨(⟨x, hx⟩, 1, 1), by simp [hf]⟩`. Introduce `x hx; exact ⟨(1, ⟨x, hx⟩, 1), by simp [hf]⟩`. Introduce `x hx; exact ⟨(1, 1, ⟨x, hx⟩), by simp [hf]⟩`. Establish `hbij : Function.Bijective f`.

Apply `hsurj.bijective_of_nat_card_le` to reduce the goal to its premises. Rewrite using `[Nat.card_prod, Nat.card_prod, hcard, mul_assoc]`. Establish `h1 : f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) = f 1`. Rewrite using `[hf, map_one]`. Simplify `habc` using `[mul_assoc]`.

Establish `h2` using `hbij.1 h1`. Simplify using `only [Prod.mk_eq_one, Subgroup.mk_eq_one] at h2`. Conclude with `⟨h2.1, h2.2.1, h2.2.2⟩`.
-/
theorem genusAbelian : GenusAbelian := by
  intro G _ _ A B C hsup hcard a ha b hb c hc habc
  let f : A × B × C →* G := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hf : ∀ x : A × B × C, f x = (x.1 : G) * ((x.2.1 : G) * (x.2.2 : G)) := fun x => rfl
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hsup]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx; exact ⟨(⟨x, hx⟩, 1, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, ⟨x, hx⟩, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, 1, ⟨x, hx⟩), by simp [hf]⟩
  have hbij : Function.Bijective f := by
    apply hsurj.bijective_of_nat_card_le
    rw [Nat.card_prod, Nat.card_prod, hcard, mul_assoc]
  have h1 : f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) = f 1 := by
    rw [hf, map_one]; simpa [mul_assoc] using habc
  have h2 := hbij.1 h1
  simp only [Prod.mk_eq_one, Subgroup.mk_eq_one] at h2
  exact ⟨h2.1, h2.2.1, h2.2.2⟩

/- English proof (translation)
Introduce `p _ H _ _ hP S hS`. Assume the negation of the conclusion as `hne`. Take `⟨Mx, hMx, hle⟩` from `(eq_top_or_exists_le_coatom (Subgroup.closure S)).resolve_left hne`. Use `hP.isNilpotent` as an intermediate fact. Establish `hMn : Mx.Normal` using `Subgroup.NormalizerCondition.normal_of_coatom Mx (Group.normalizerCondition_of_isNilpotent) hMx`.

Establish `: Subgroup.normalClosure S ≤ Mx` using `Subgroup.normalClosure_le_normal (fun x hx => hle (Subgroup.subset_closure hx))`. Rewrite `this` using `[hS]`. Conclude with `hMx.1 (top_le_iff.mp this)`.
-/
theorem pGroupGen : PGroupGen := by
  intro p _ H _ _ hP S hS
  by_contra hne
  obtain ⟨Mx, hMx, hle⟩ := (eq_top_or_exists_le_coatom (Subgroup.closure S)).resolve_left hne
  have := hP.isNilpotent
  have hMn : Mx.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Mx (Group.normalizerCondition_of_isNilpotent) hMx
  have : Subgroup.normalClosure S ≤ Mx :=
    Subgroup.normalClosure_le_normal (fun x hx => hle (Subgroup.subset_closure hx))
  rw [hS] at this
  exact hMx.1 (top_le_iff.mp this)

end Formalism.TwoAdicCyclotomicDecomposition
