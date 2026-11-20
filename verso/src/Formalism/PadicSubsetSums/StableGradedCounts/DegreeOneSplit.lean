import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact

open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `F E _ _ _ _ _ h2 P _ hP hf he`. Use `set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp`. Establish `hfin : (p.primesOver (𝓞 E)).Finite` using `Algebra.QuasiFinite.finite_primesOver p`. Set `_ : Fintype (p.primesOver (𝓞 E))` to `hfin.fintype`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)`.

Establish `hrank : Module.finrank (𝓞 F) (𝓞 E) = 2`. Rewrite using `[← h2]`. Conclude with `(IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm`. Rewrite `hsum` using `[hrank]`. Establish `hf1 : P.inertiaDeg (𝓞 F) = 1`.

Use `Ideal.inertiaDeg_tower (R := ℤ) p P` as an intermediate fact. Rewrite `this` using `[hf]`. Conclude with `Nat.eq_one_of_mul_eq_one_left this.symm`. Establish `hPmem : P ∈ p.primesOver (𝓞 E)` using `⟨inferInstance, ⟨rfl⟩⟩`. Establish `hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)`.

Introduce `q`. Establish `: q.1.IsPrime` using `q.2.1`. Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos q.1 (𝓞 F)) (Ideal.inertiaDeg_pos q.1 (𝓞 F))`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))]`. Simplify using `only [he, hf1, mul_one] at hsum`.

Establish `hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1` using `by omega`. Establish `hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[Finset.card_eq_zero]`. Rewrite `hrest` using `[h0]`. Simplify using `at hrest`. Rewrite `hle`, `hge` using `[Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`. Establish `key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2` using `by omega`.

Rewrite using `[← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]`. Conclude with `key`.
-/
theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : P.inertiaDeg (𝓞 F) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, ⟨rfl⟩⟩
  have hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have : q.1.IsPrime := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 (𝓞 F)) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))] at hsum
  simp only [he, hf1, mul_one] at hsum
  have hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1 := by omega
  have hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1 := by
    calc _ = ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hpos q
      _ = 1 := hrest
  have hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hrest
    simp at hrest
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hle hge
  have key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact key

end Formalism.IrreducibleCountingLemmas.Z
