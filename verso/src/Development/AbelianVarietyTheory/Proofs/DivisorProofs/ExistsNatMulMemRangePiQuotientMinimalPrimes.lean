import Mathlib

namespace GlobalTheory.CokerMinimalPrimes

/- English proof (translation)
Establish `hQm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) Q` using `hQ`. Establish `hPm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P` using `hP`. Establish `hnle : ¬ P ≤ Q` using `fun h => hPQ (hQm.eq_of_le hPm.1 h)`. Use `haveI : Q.IsPrime := hQm.1.1`. Take `⟨p, hpP, hpQ⟩` from `Set.not_subset.mp hnle`.

Establish `hx : Ideal.Quotient.mk Q p ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Establish `hxI : Ideal.Quotient.mk Q p ∈ Ideal.map (Ideal.Quotient.mk Q) P` using `Ideal.mem_map_of_mem _ hpP`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx hxI (Algebra.IsIntegral.isIntegral _)`. Take `⟨k, hk, hk0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Rewrite `hk` using `[Ideal.mem_comap, eq_intCast, ← map_intCast (Ideal.Quotient.mk Q), Ideal.mem_quotient_iff_mem_sup]`. Use `⟨k.natAbs, by simpa using hk0, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq k with h | h` into its components or cases. Rewrite `hk` using `[h, Int.cast_natCast]`. Conclude with `hk`.

Rewrite `hk` using `[h, Int.cast_neg, Int.cast_natCast]`. Simplify using `using (P ⊔ Q).neg_mem hk`.
-/
theorem exists_nat_mem_sup (B : Type) [CommRing B] [Module.Finite ℤ B]
    {P Q : Ideal B} (hP : P ∈ minimalPrimes B) (hQ : Q ∈ minimalPrimes B) (hPQ : P ≠ Q) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : B) ∈ P ⊔ Q := by
  have hQm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) Q := hQ
  have hPm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P := hP
  have hnle : ¬ P ≤ Q := fun h => hPQ (hQm.eq_of_le hPm.1 h)
  haveI : Q.IsPrime := hQm.1.1
  obtain ⟨p, hpP, hpQ⟩ := Set.not_subset.mp hnle
  have hx : Ideal.Quotient.mk Q p ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hxI : Ideal.Quotient.mk Q p ∈ Ideal.map (Ideal.Quotient.mk Q) P :=
    Ideal.mem_map_of_mem _ hpP
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx hxI
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, eq_intCast, ← map_intCast (Ideal.Quotient.mk Q),
    Ideal.mem_quotient_iff_mem_sup] at hk
  refine ⟨k.natAbs, by simpa using hk0, ?_⟩
  rcases Int.natAbs_eq k with h | h
  · rw [h, Int.cast_natCast] at hk; exact hk
  · rw [h, Int.cast_neg, Int.cast_natCast] at hk; simpa using (P ⊔ Q).neg_mem hk

/- English proof (translation)
Establish `hq : ∀ i j, ∃ q : B, i ≠ j → q ∈ I j ∧ m - q ∈ I i`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Conclude with `⟨0, fun h => (h hij).elim⟩`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp (hm i j hij)`.

Conclude with `⟨z, fun _ => ⟨hz, by rw [← hyz]; simpa using hy⟩⟩`. Use `choose q hq using hq`. Set `e : ι → B` to `fun i => ∏ j ∈ Finset.univ.erase i, q i j`. Establish `he_mem : ∀ i j, i ≠ j → e i ∈ I j`. Introduce `i j hij`.

Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (q i) (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)`. Express the relevant statement in the definitionally equal form `∏ j ∈ Finset.univ.erase i, q i j ∈ I j`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ (hq i j hij).1`. Establish `he_mod : ∀ i, Ideal.Quotient.mk (I i) (e i) = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1)`.

Introduce `i`. Simplify using `only [e, map_prod]`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => Ideal.Quotient.mk (I i) m), Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]`. Introduce `j hj`. Establish `hij : i ≠ j` using `Ne.symm (Finset.mem_erase.mp hj).1`.

Conclude with `(Ideal.Quotient.eq.mpr (hq i j hij).2).symm`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I i) (b' i)`. Use `⟨∑ i, e i * c i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_eq_single i]`. Rewrite using `[map_mul, he_mod, hc]`.

Introduce `j _ hji`. Rewrite using `[map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (he_mem j i hji), zero_mul]`. Introduce `h`. Conclude with `(h (Finset.mem_univ i)).elim`.
-/
theorem exists_pow_mul_mem_range {B : Type} [CommRing B] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal B) (m : B) (hm : ∀ i j, i ≠ j → m ∈ I i ⊔ I j)
    (b' : (i : ι) → B ⧸ I i) :
    ∃ a : B, ∀ i, Ideal.Quotient.mk (I i) a
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) * b' i := by

  have hq : ∀ i j, ∃ q : B, i ≠ j → q ∈ I j ∧ m - q ∈ I i := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hm i j hij)
    exact ⟨z, fun _ => ⟨hz, by rw [← hyz]; simpa using hy⟩⟩
  choose q hq using hq
  let e : ι → B := fun i => ∏ j ∈ Finset.univ.erase i, q i j
  have he_mem : ∀ i j, i ≠ j → e i ∈ I j := by
    intro i j hij
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (q i) (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    change ∏ j ∈ Finset.univ.erase i, q i j ∈ I j
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hq i j hij).1
  have he_mod : ∀ i, Ideal.Quotient.mk (I i) (e i)
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) := by
    intro i
    simp only [e, map_prod]
    rw [Finset.prod_congr rfl (g := fun _ => Ideal.Quotient.mk (I i) m), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    exact (Ideal.Quotient.eq.mpr (hq i j hij).2).symm
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I i) (b' i)
  refine ⟨∑ i, e i * c i, fun i => ?_⟩
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_mul, he_mod, hc]
  · intro j _ hji
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (he_mem j i hji), zero_mul]
  · intro h; exact (h (Finset.mem_univ i)).elim

/- English proof (translation)
Introduce `B _ _`. Use `haveI : IsNoetherian ℤ B := isNoetherian_of_isNoetherianRing_of_finite ℤ B`. Use `haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance`. Use `haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype`. Use `letI : Fintype (minimalPrimes B) := Fintype.ofFinite _`.

Establish `hpair : ∀ P Q : minimalPrimes B, ∃ m : ℕ, m ≠ 0 ∧ (P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q)`. Introduce `P Q`. Distinguish the cases in `h : P = Q`. Conclude with `⟨1, one_ne_zero, fun h' => (h' h).elim⟩`. Take `⟨m, hm0, hm⟩` from `exists_nat_mem_sup B P.2 Q.2 (fun e => h (Subtype.ext e))`.

Conclude with `⟨m, hm0, fun _ => hm⟩`. Use `choose f hf0 hf using hpair`. Set `m : ℕ` to `∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2`. Establish `hm0 : m ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p.1 p.2`. Establish `hm : ∀ P Q : minimalPrimes B, P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q`.

Introduce `P Q hPQ`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun p : minimalPrimes B × minimalPrimes B => f p.1 p.2) (Finset.mem_univ (P, Q))`. Express the relevant statement in the definitionally equal form `((∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2 : ℕ) : B) ∈ _`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (hf P Q hPQ)`.

Use `⟨m ^ (Fintype.card (minimalPrimes B) - 1), pow_ne_zero _ hm0, fun b' => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_pow_mul_mem_range (fun P : minimalPrimes B => (P : Ideal B)) (m : B) hm b'`. Use `⟨a, funext fun P => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (P : Ideal B) a = _`. Rewrite using `[ha P, Pi.mul_apply, Pi.natCast_apply, map_natCast]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem exists_nat_mul_mem_range_pi_quotient_minimalPrimes : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧
    ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)),
      (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈
        (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  intro B _ _
  classical
  haveI : IsNoetherian ℤ B := isNoetherian_of_isNoetherianRing_of_finite ℤ B
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  letI : Fintype (minimalPrimes B) := Fintype.ofFinite _
  have hpair : ∀ P Q : minimalPrimes B, ∃ m : ℕ, m ≠ 0 ∧ (P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q) := by
    intro P Q
    by_cases h : P = Q
    · exact ⟨1, one_ne_zero, fun h' => (h' h).elim⟩
    obtain ⟨m, hm0, hm⟩ := exists_nat_mem_sup B P.2 Q.2 (fun e => h (Subtype.ext e))
    exact ⟨m, hm0, fun _ => hm⟩
  choose f hf0 hf using hpair
  let m : ℕ := ∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p.1 p.2
  have hm : ∀ P Q : minimalPrimes B, P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q := by
    intro P Q hPQ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : minimalPrimes B × minimalPrimes B => f p.1 p.2)
      (Finset.mem_univ (P, Q))
    change ((∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2 : ℕ) : B) ∈ _
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hf P Q hPQ)
  refine ⟨m ^ (Fintype.card (minimalPrimes B) - 1), pow_ne_zero _ hm0, fun b' => ?_⟩
  obtain ⟨a, ha⟩ := exists_pow_mul_mem_range (fun P : minimalPrimes B => (P : Ideal B)) (m : B) hm b'
  refine ⟨a, funext fun P => ?_⟩
  change Ideal.Quotient.mk (P : Ideal B) a = _
  rw [ha P, Pi.mul_apply, Pi.natCast_apply, map_natCast]
  push_cast
  rfl

end GlobalTheory.CokerMinimalPrimes
