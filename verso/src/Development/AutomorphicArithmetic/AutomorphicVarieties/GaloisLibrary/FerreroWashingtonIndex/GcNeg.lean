import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Establish `hdm` using `Nat.div_add_mod a M`. Establish `hrl` using `Nat.mod_lt a hM`. Generalize the expression as in `a / M = k at hdm ⊢`. Generalize the expression as in `a % M = r at hdm hrl hr`. Substitute `hdm` using the available equality.

Establish `hkc : k < c`. Assume the negation of the conclusion as `hck`. Use `push_neg at hck`. Establish `: M * c ≤ M * k` using `Nat.mul_le_mul_left M hck`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨j, rfl⟩ : ∃ j, c = k + 1 + j` from `⟨c - k - 1, by omega⟩`. Establish `e1 : (k + 1 + j) * M = M * k + M + j * M` using `by ring`. Establish `hq : ((k + 1 + j) * M - (M * k + r)) / M = j`. Apply `Nat.div_eq_of_lt_le` to reduce the goal to its premises. Rewrite using `[e1]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, Nat.add_mul, Nat.one_mul]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hq]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem div_sub_add_div_add_one_eq (c M a : ℕ) (hM : 0 < M) (hr : a % M ≠ 0) (ha : a < c * M) :
    (c * M - a) / M + a / M + 1 = c := by
  have hdm := Nat.div_add_mod a M
  have hrl := Nat.mod_lt a hM
  generalize a / M = k at hdm ⊢
  generalize a % M = r at hdm hrl hr
  subst hdm
  have hkc : k < c := by
    by_contra hck
    push_neg at hck
    have : M * c ≤ M * k := Nat.mul_le_mul_left M hck
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, c = k + 1 + j := ⟨c - k - 1, by omega⟩
  have e1 : (k + 1 + j) * M = M * k + M + j * M := by ring
  have hq : ((k + 1 + j) * M - (M * k + r)) / M = j := by
    apply Nat.div_eq_of_lt_le
    · rw [e1]
      omega
    · rw [e1, Nat.add_mul, Nat.one_mul]
      omega
  rw [hq]
  omega

/- English proof (translation)
Introduce `M c _ s hc hodd hs`. Unfold `gc`. Establish `hcu : IsUnit (c : ZMod M)` using `(ZMod.isUnit_iff_coprime c M).mpr hc`. Establish `ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s)` using `by ring`. Establish `ht0 : (c : ZMod M)⁻¹ * s ≠ 0`.

Introduce `h0`. Apply `hs` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩`. Rewrite using `[ht, ZMod.val_neg_of_ne_zero]`.

Establish `hv0 : 0 < ((c : ZMod M)⁻¹ * s).val` using `ZMod.val_pos.mpr ht0`. Establish `hvM : ((c : ZMod M)⁻¹ * s).val < M` using `ZMod.val_lt _`. Generalize the expression as in `((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢`. Establish `hMpos : 0 < M` using `by omega`. Establish `hcpos : 0 < c` using `hodd.pos`.

Establish `hndvd : (c * v) % M ≠ 0`. Introduce `h0`. Establish `h1 : M ∣ c * v` using `Nat.dvd_of_mod_eq_zero h0`. Establish `h2 : M ∣ v` using `(Nat.Coprime.dvd_mul_left hc.symm).mp h1`. Use `Nat.le_of_dvd hv0 h2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hlt : c * v < c * M` using `Nat.mul_lt_mul_of_pos_left hvM hcpos`. Establish `key` using `div_sub_add_div_add_one_eq c M (c * v) hMpos hndvd hlt`. Rewrite using `[mul_tsub]`. Take `⟨m, rfl⟩` from `hodd`.

Establish `hm : (2 * m + 1 - 1) / 2 = m` using `by omega`. Rewrite using `[hm]`. Generalize the expression as in `((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢`. Generalize the expression as in `(2 * m + 1) * v / M = Q at key ⊢`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.FW.gcNeg :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → Odd c → s ≠ 0 → gc M c (-s) = -gc M c s := by
  intro M c _ s hc hodd hs
  unfold gc
  have hcu : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).mpr hc
  have ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s) := by ring
  have ht0 : (c : ZMod M)⁻¹ * s ≠ 0 := by
    intro h0
    apply hs
    calc s = ((c : ZMod M) * (c : ZMod M)⁻¹) * s := by rw [ZMod.mul_inv_of_unit _ hcu, one_mul]
      _ = (c : ZMod M) * ((c : ZMod M)⁻¹ * s) := by ring
      _ = 0 := by rw [h0, mul_zero]
  haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩
  rw [ht, ZMod.val_neg_of_ne_zero]
  have hv0 : 0 < ((c : ZMod M)⁻¹ * s).val := ZMod.val_pos.mpr ht0
  have hvM : ((c : ZMod M)⁻¹ * s).val < M := ZMod.val_lt _
  generalize ((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢
  have hMpos : 0 < M := by omega
  have hcpos : 0 < c := hodd.pos
  have hndvd : (c * v) % M ≠ 0 := by
    intro h0
    have h1 : M ∣ c * v := Nat.dvd_of_mod_eq_zero h0
    have h2 : M ∣ v := (Nat.Coprime.dvd_mul_left hc.symm).mp h1
    have := Nat.le_of_dvd hv0 h2
    omega
  have hlt : c * v < c * M := Nat.mul_lt_mul_of_pos_left hvM hcpos
  have key := div_sub_add_div_add_one_eq c M (c * v) hMpos hndvd hlt
  rw [mul_tsub]
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  generalize ((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢
  generalize (2 * m + 1) * v / M = Q at key ⊢
  push_cast
  omega
