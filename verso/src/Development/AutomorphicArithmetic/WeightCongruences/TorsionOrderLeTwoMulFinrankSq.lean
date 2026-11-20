import Mathlib

open NumberField

/- English proof (translation)
Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp hk`. Rewrite using `[Nat.totient_prime_pow hp hk]`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality.

Establish `he : Even (2 ^ k)` using `(Nat.even_pow.2 ⟨even_two, hk.ne'⟩)`. Rewrite using `[if_pos he]`. Establish `: 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2`. Rewrite using `[← pow_mul, ← pow_succ']`. Conclude with `Nat.pow_le_pow_right (by norm_num) (by omega)`.

Simplify using `using this`. Establish `hodd : ¬ Even (p ^ k)`. Rewrite using `[Nat.even_pow]`. Introduce and unpack `⟨he, -⟩`. Conclude with `h2 ((Nat.Prime.even_iff hp).1 he)`.

Rewrite using `[if_neg hodd, one_mul]`. Establish `hp3 : 3 ≤ p`. Use `hp.two_le` as an intermediate fact. Break down `Nat.lt_or_ge p 3 with h | h` into its components or cases. Apply the tactic sequence `interval_cases p <;> simp_all`.

Conclude with `h`. Establish `hsq : p ≤ (p - 1) ^ 2`. Take `⟨q, rfl⟩ : ∃ q, p = q + 3` from `⟨p - 3, by omega⟩`. Rewrite using `[show q + 3 - 1 = q + 2 by omega]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `coprime a b _ _ hab iha ihb`. Rewrite using `[Nat.totient_mul hab]`.

Establish `hc : (if Even (a * b) then 2 else 1) = (if Even a then 2 else 1) * (if Even b then 2 else 1)`. Apply the tactic sequence `by_cases ha : Even a <;> by_cases hb : Even b`. It suffices to derive a contradiction. Establish `h2a : 2 ∣ a` using `even_iff_two_dvd.1 ha`. Establish `h2b : 2 ∣ b` using `even_iff_two_dvd.1 hb`.

Establish `h` using `Nat.dvd_gcd h2a h2b`. Rewrite `h` using `[Nat.Coprime.gcd_eq_one hab]`. Use linear arithmetic over natural numbers and integers. Simplify using `[ha, hb, Nat.even_mul]`. Simplify using `[ha, hb, Nat.even_mul]`.

Establish `: ¬ Even (a * b)` using `by rw [Nat.even_mul]; tauto`. Simplify using `[ha, hb, this]`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    by_cases h2 : p = 2
    · subst h2
      have he : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
      rw [if_pos he]
      have : 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    · have hodd : ¬ Even (p ^ k) := by
        rw [Nat.even_pow]; rintro ⟨he, -⟩
        exact h2 ((Nat.Prime.even_iff hp).1 he)
      rw [if_neg hodd, one_mul]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases Nat.lt_or_ge p 3 with h | h
        · interval_cases p <;> simp_all
        · exact h
      have hsq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
        rw [show q + 3 - 1 = q + 2 by omega]
        nlinarith
      calc p ^ k ≤ p ^ (2 * (k - 1) + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        _ = (p ^ (k - 1)) ^ 2 * p := by rw [pow_succ, pow_mul, ← pow_mul, mul_comm 2]; ring
        _ ≤ (p ^ (k - 1)) ^ 2 * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hsq
        _ = (p ^ (k - 1) * (p - 1)) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b _ _ hab iha ihb =>
    rw [Nat.totient_mul hab]
    have hc : (if Even (a * b) then 2 else 1) = (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ha : Even a <;> by_cases hb : Even b
      · exfalso
        have h2a : 2 ∣ a := even_iff_two_dvd.1 ha
        have h2b : 2 ∣ b := even_iff_two_dvd.1 hb
        have h := Nat.dvd_gcd h2a h2b
        rw [Nat.Coprime.gcd_eq_one hab] at h
        omega
      · simp [ha, hb, Nat.even_mul]
      · simp [ha, hb, Nat.even_mul]
      · have : ¬ Even (a * b) := by rw [Nat.even_mul]; tauto
        simp [ha, hb, this]
    rw [hc]
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) * ((if Even b then 2 else 1) * b.totient ^ 2) :=
          Nat.mul_le_mul iha ihb
      _ = _ := by ring

/- English proof (translation)
Establish `h` using `le_mul_totient_sq n`. Apply the tactic sequence `have hc : (if Even n then 2 else 1) ≤ 2 := by split_ifs <;> norm_num`. Conclude with `h.trans (Nat.mul_le_mul_right _ hc)`.
-/
private theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have h := le_mul_totient_sq n
  have hc : (if Even n then 2 else 1) ≤ 2 := by split_ifs <;> norm_num
  exact h.trans (Nat.mul_le_mul_right _ hc)

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := Units.torsion E)`. Establish `hord : orderOf g = Units.torsionOrder E`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg]`. Both sides reduce to the same expression. Establish `hpos : 0 < Units.torsionOrder E` using `Units.torsionOrder_pos E`.

Set `ζ : E` to `algebraMap (𝓞 E) E (((g : (𝓞 E)ˣ) : 𝓞 E))`. Establish `hprim : IsPrimitiveRoot ζ (Units.torsionOrder E)`. Establish `h1 : IsPrimitiveRoot g (orderOf g)` using `IsPrimitiveRoot.orderOf g`. Rewrite `h1` using `[hord]`. Establish `h2` using `h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective`.

Establish `h3` using `h2.map_of_injective (f := Units.coeHom (𝓞 E)) (fun a b h => Units.ext h)`. Conclude with `h3.map_of_injective (f := algebraMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective _ _)`. Establish `: NeZero (Units.torsionOrder E)` using `⟨hpos.ne'⟩`. Establish `hmin : minpoly ℚ ζ = Polynomial.cyclotomic (Units.torsionOrder E) ℚ` using `(hprim.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hpos)).symm`. Establish `hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E`.

Rewrite using `[← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ, ← hmin]`. Conclude with `minpoly.natDegree_le ζ`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem torsion_order_le_two_mul_finrank_sq (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := Units.torsionOrder_pos E

  let ζ : E := algebraMap (𝓞 E) E (((g : (𝓞 E)ˣ) : 𝓞 E))
  have hprim : IsPrimitiveRoot ζ (Units.torsionOrder E) := by
    have h1 : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
    rw [hord] at h1
    have h2 := h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective
    have h3 := h2.map_of_injective (f := Units.coeHom (𝓞 E)) (fun a b h => Units.ext h)
    exact h3.map_of_injective (f := algebraMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective _ _)
  have : NeZero (Units.torsionOrder E) := ⟨hpos.ne'⟩
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic (Units.torsionOrder E) ℚ :=
    (hprim.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hpos)).symm
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ, ← hmin]
    exact minpoly.natDegree_le ζ
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdeg 2)

/- English proof (translation)
Introduce `E _ _`. Conclude with `torsion_order_le_two_mul_finrank_sq E`.
-/
theorem UpperTheory.torsionOrder_le_two_mul_finrank_sq :
    ∀ (E : Type) [Field E] [NumberField E], NumberField.Units.torsionOrder E ≤ 2 * Module.finrank ℚ E ^ 2 := by
  intro E _ _
  exact torsion_order_le_two_mul_finrank_sq E
