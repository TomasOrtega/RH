import Formalism.CMTypeGalois.StatementField

open NumberField Ideal

noncomputable section

namespace Formalism.Q3

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hostFrob_val (hF : MQFrob) (hK : KroneckerMeaning) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) [Fact p.Prime] (hpq : ∀ i, p ≠ q i)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (H : IsArithFrobAt ℤ σ P) (i : Fin 3) :
    ((galSign α σ i : ℤˣ) : ℤ) = chiQ (q i) p := by
  have hp : p.Prime := Fact.out
  obtain ⟨hqi, hq4⟩ := hq.1 i
  have hne : ∀ j, (-(q j : ℤ)) ≠ 0 := fun j => by
    have := (hq.1 j).1.pos
    omega
  have h := hF 3 E (fun j => -(q j : ℤ)) α hα hne p P σ H i
  by_cases h2 : p = 2
  · subst h2
    have hmod4 : (-(q i : ℤ)) % 4 = 1 := by omega
    have h8 := h.2 rfl hmod4
    have hchi := (hK (q i) hqi hq4).2.1
    have hcop : Int.gcd 2 (q i : ℤ) = 1 := by
      have hodd : Odd (q i) := Nat.odd_iff.mpr (by omega)
      have : Int.gcd ((2 : ℕ) : ℤ) (q i : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_two_left.mpr hodd
      exact_mod_cast this
    have hpm : chiQ (q i) 2 = 1 ∨ chiQ (q i) 2 = -1 := by
      unfold chiQ
      exact jacobiSym.eq_one_or_neg_one hcop
    have hc2 : ((2 : ℕ) : ℤ) = 2 := by norm_num
    rw [hc2]
    rcases Int.units_eq_one_or (galSign α σ i) with hs | hs
    · have h7 : q i % 8 = 7 := by
        have := h8.mp hs
        omega
      rw [hs, hchi.mpr h7]
      rfl
    · have h7 : ¬ q i % 8 = 7 := by
        intro h7
        have : galSign α σ i = 1 := h8.mpr (by omega)
        rw [hs] at this
        exact absurd this (by decide)
      have hc : chiQ (q i) 2 = -1 := by
        rcases hpm with hpm | hpm
        · exact absurd (hchi.mp hpm) h7
        · exact hpm
      rw [hs, hc]
      rfl
  · have hnd : ¬ (p : ℤ) ∣ 2 * -(q i : ℤ) := by
      intro hd
      have hd' : p ∣ 2 * q i := by
        have : (p : ℤ) ∣ ((2 * q i : ℕ) : ℤ) := by
          push_cast
          rw [← dvd_neg]
          simpa [mul_neg] using hd
        exact_mod_cast this
      rcases (Nat.Prime.dvd_mul hp).mp hd' with h' | h'
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact hpq i ((Nat.prime_dvd_prime_iff_eq hp hqi).mp h')
    rw [h.1 hnd]
    exact ((hK (q i) hqi hq4).1 p hp h2 (hpq i)).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. A detailed English derivation is pending.
-/
theorem hostFrob_of (hF : MQFrob) (hH : HostGalois) (hK : KroneckerMeaning) : HostFrob := by
  intro q hq E _ _ α hα p _ hpq P _ _
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have : Finite (𝓞 E ⧸ P) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) P
  refine ⟨⟨τ, hτ⟩, fun σ => ⟨fun H i => hostFrob_val hF hK q hq E α hα p hpq P σ H i,
    fun h => ?_⟩⟩
  have hτv := hostFrob_val hF hK q hq E α hα p hpq P τ hτ
  have : σ = τ := hGal.2.2.1.1 (funext fun i => Units.ext ((h i).trans (hτv i).symm))
  subst this
  exact hτ

end Formalism.Q3
