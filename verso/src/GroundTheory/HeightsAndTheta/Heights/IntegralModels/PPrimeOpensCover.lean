import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry TopologicalSpace

namespace PrimeOpensCover

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
lemma not_mem_of_isCoprime {P : Ideal ℤ} (hP : P ≠ ⊤) {a b : ℤ} (h : IsCoprime a b)
    (ha : a ∈ P) : b ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ := h
  exact hP ((Ideal.eq_top_iff_one P).mpr (huv ▸ P.add_mem (P.mul_mem_left u ha) (P.mul_mem_left v hb)))

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
lemma mem_of_dvd_mem {P : Ideal ℤ} {a b : ℤ} (h : a ∣ b) (ha : a ∈ P) : b ∈ P := by
  obtain ⟨c, rfl⟩ := h
  exact P.mul_mem_right c ha

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma exists_mem_of_primeProd_mem {P : Ideal ℤ} [P.IsPrime] {S : Finset Nat.Primes}
    (h : primeProd S ∈ P) : ∃ r ∈ S, ((r : ℕ) : ℤ) ∈ P :=
  Ideal.IsPrime.prod_mem_iff.mp h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

A detailed English derivation is pending.
-/
theorem proof : PrimeOpensCover.Statement := by
  intro X f S mp hcop hdvd
  refine ⟨?_, fun p hp q hq hpq => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    let P : Ideal ℤ := (f.base x).asIdeal
    have : P.IsPrime := (f.base x).isPrime
    rw [Opens.mem_sup]
    by_cases hm : primeProd S ∈ P
    · obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem hm
      right
      rw [Opens.mem_iSup]
      refine ⟨r, ?_⟩
      rw [Opens.mem_iSup]
      refine ⟨hr, ?_⟩
      rw [mem_invOpen]
      exact not_mem_of_isCoprime (Ideal.IsPrime.ne_top ‹_›)
        ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp r.2)).mpr (hcop r hr)) hrP
    · left
      exact hm
  · have hm : ∀ x : X, x ∈ invOpen f (mp p) ⊓ invOpen f (mp q) → x ∈ invOpen f (primeProd S) := by
      intro x hx
      obtain ⟨hxp, hxq⟩ := hx
      replace hxp : mp p ∉ (f.base x).asIdeal := hxp
      replace hxq : mp q ∉ (f.base x).asIdeal := hxq
      rw [mem_invOpen]
      let P : Ideal ℤ := (f.base x).asIdeal
      have : P.IsPrime := (f.base x).isPrime
      intro hmem
      obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem (P := P) hmem
      by_cases hrp : r = p
      · subst hrp
        exact hxq (mem_of_dvd_mem (hdvd q hq r hr hpq) hrP)
      · exact hxp (mem_of_dvd_mem (hdvd p hp r hr hrp) hrP)
    refine ⟨fun x hx => hm x hx, fun x hx => ?_⟩
    have h1 := hm x hx
    obtain ⟨hxp, _⟩ := hx
    replace hxp : mp p ∉ (f.base x).asIdeal := hxp
    rw [mem_invOpen] at h1 ⊢
    have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
    intro hmul
    rcases Ideal.IsPrime.mem_or_mem ‹_› hmul with h | h
    · exact h1 h
    · exact hxp h

end PrimeOpensCover

end GroundTheory.Heights₂.Heights.Model
