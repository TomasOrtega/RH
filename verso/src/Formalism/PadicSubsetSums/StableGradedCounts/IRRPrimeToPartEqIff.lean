import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Rewrite using `[pow_add, pow_mul, pow_mul, h]`.
-/
theorem pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]

/- English proof (translation)
Distinguish the cases in `h1 : orderOf u * orderOf w = 1`. Establish `hu1 : orderOf u = 1` using `Nat.eq_one_of_mul_eq_one_right h1`. Establish `hw1 : orderOf w = 1` using `Nat.eq_one_of_mul_eq_one_left h1`. Rewrite using `[orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]`. Establish `hpos : 0 < orderOf u * orderOf w` using `Nat.mul_pos hu hw`.

Establish `hlt : 1 < orderOf u * orderOf w` using `by omega`. Take `⟨s, -, hs⟩` from `Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt`. Establish `hmod : r * s ≡ 1 [MOD orderOf u * orderOf w]`. Unfold `Nat.ModEq`. Rewrite using `[hs, Nat.mod_eq_of_lt hlt]`.

Establish `hm1 : r * s ≡ 1 [MOD orderOf u]` using `Nat.ModEq.of_mul_right (orderOf w) hmod`. Establish `hm2 : r * s ≡ 1 [MOD orderOf w]` using `Nat.ModEq.of_mul_left (orderOf u) hmod`. Establish `hu' : u ^ (r * s) = u`. Rewrite using `[← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf, pow_one]`. Establish `hw' : w ^ (r * s) = w`.

Rewrite using `[← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf, pow_one]`. Rewrite using `[← hu', ← hw', pow_mul, pow_mul, h]`.
-/
theorem eq_of_pow_eq_of_coprime_order {M : Type*} [Monoid M] {r : ℕ} {u w : M}
    (hu : 0 < orderOf u) (hw : 0 < orderOf w) (hcu : Nat.Coprime r (orderOf u))
    (hcw : Nat.Coprime r (orderOf w)) (h : u ^ r = w ^ r) : u = w := by
  by_cases h1 : orderOf u * orderOf w = 1
  · have hu1 : orderOf u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hw1 : orderOf w = 1 := Nat.eq_one_of_mul_eq_one_left h1
    rw [orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]
  · have hpos : 0 < orderOf u * orderOf w := Nat.mul_pos hu hw
    have hlt : 1 < orderOf u * orderOf w := by omega
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt
    have hmod : r * s ≡ 1 [MOD orderOf u * orderOf w] := by
      unfold Nat.ModEq
      rw [hs, Nat.mod_eq_of_lt hlt]
    have hm1 : r * s ≡ 1 [MOD orderOf u] := Nat.ModEq.of_mul_right (orderOf w) hmod
    have hm2 : r * s ≡ 1 [MOD orderOf w] := Nat.ModEq.of_mul_left (orderOf u) hmod
    have hu' : u ^ (r * s) = u := by
      rw [← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf,
        pow_one]
    have hw' : w ^ (r * s) = w := by
      rw [← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf,
        pow_one]
    rw [← hu', ← hw', pow_mul, pow_mul, h]

/- English proof (translation)
Introduce `M _ l x y hl hx hy`. Take `⟨hox, a, ha⟩` from `prime_to_part_spec M l x hl hx`. Take `⟨hoy, b, hb⟩` from `prime_to_part_spec M l y hl hy`. Establish `hnx : orderOf x ≠ 0` using `(orderOf_pos_iff.mpr hx).ne'`. Establish `hny : orderOf y ≠ 0` using `(orderOf_pos_iff.mpr hy).ne'`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]`. Introduce and unpack `⟨c, hc⟩`.

Establish `e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c)))` using `(pow_lpow_add ha _).symm`. Establish `e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c)))` using `(pow_lpow_add hb _).symm`. Establish `e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b)))` using `pow_lpow_add hc _`. Establish `s1 : a + (b + c) = c + (a + b)` using `by omega`. Establish `s2 : b + (a + c) = c + (a + b)` using `by omega`.

Rewrite `e1` using `[s1]`. Rewrite `e2` using `[s2]`. Use `eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])` and prove the remaining obligations. Rewrite using `[hox]`. Conclude with `Nat.ordCompl_pos l hnx`.

Rewrite using `[hoy]`. Conclude with `Nat.ordCompl_pos l hny`. Rewrite using `[hox]`. Conclude with `Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)`. Rewrite using `[hoy]`.

Conclude with `Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)`.
-/
theorem prime_to_part_eq_iff : PrimeToPartEqIff := by
  intro M _ l x y hl hx hy
  obtain ⟨hox, a, ha⟩ := prime_to_part_spec M l x hl hx
  obtain ⟨hoy, b, hb⟩ := prime_to_part_spec M l y hl hy
  have hnx : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  have hny : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  constructor
  · intro h
    refine ⟨a + b, ?_⟩
    rw [pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]
  · rintro ⟨c, hc⟩
    have e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c))) :=
      (pow_lpow_add ha _).symm
    have e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c))) :=
      (pow_lpow_add hb _).symm
    have e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b))) := pow_lpow_add hc _
    have s1 : a + (b + c) = c + (a + b) := by omega
    have s2 : b + (a + c) = c + (a + b) := by omega
    rw [s1] at e1
    rw [s2] at e2
    refine eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])
    · rw [hox]; exact Nat.ordCompl_pos l hnx
    · rw [hoy]; exact Nat.ordCompl_pos l hny
    · rw [hox]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)
    · rw [hoy]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
