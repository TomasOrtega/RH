import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffEKSupp
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.HF.half_supp :
    ∀ {φ : Frame} (H : HostAx φ) (𝔟 : Ideal (𝓞 H.E)), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → 𝔟 ⊔ H.conj • 𝔟 = ⊤ → (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], ((P ∣ 𝔟 ∨ H.conj • P ∣ 𝔟) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ ¬ (P ∣ 𝔟 ∧ H.conj • P ∣ 𝔟) ∧ (P ∣ 𝔟 → multiplicity P 𝔟 = multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)))) ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ differentIdeal ℤ (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) * span {s} := by
  intro φ H B hD hcop
  have mono : ∀ {I J : Ideal (𝓞 H.E)}, I ≤ J → H.conj • I ≤ H.conj • J := by
    intro I J h
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    exact Ideal.map_mono h
  have inv : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := by
    intro I
    rw [smul_smul, H.conj_mul_conj, one_smul]
  have sw : ∀ {I J : Ideal (𝓞 H.E)}, H.conj • I ≤ J ↔ I ≤ H.conj • J := by
    intro I J
    constructor
    · intro h
      simpa only [inv] using mono h
    · intro h
      simpa only [inv] using mono h
  refine ⟨fun P hP => ?_, ?_⟩
  · have hsupp := (UpperTheory.HF.diff_EK_supp H).2.1 P
    have notboth : ¬ (B ≤ P ∧ B ≤ H.conj • P) := by
      rintro ⟨h1, h2⟩
      apply hP.ne_top
      rw [eq_top_iff, ← hcop]
      exact sup_le h1 (sw.2 h2)
    have hncB : P ∣ B → ¬ P ∣ H.conj • B := by
      intro h1 h2
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, sw.1 h2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsupp, hD]
      constructor
      · rintro (h | h)
        · exact dvd_mul_of_dvd_left h _
        · rw [Ideal.dvd_iff_le] at h ⊢
          exact le_trans Ideal.mul_le_right (sw.2 h)
      · intro h
        rw [Ideal.dvd_iff_le] at h
        rcases hP.mul_le.1 h with h1 | h1
        · exact Or.inl (Ideal.dvd_iff_le.2 h1)
        · exact Or.inr (Ideal.dvd_iff_le.2 (sw.1 h1))
    · rintro ⟨h1, h2⟩
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, h2⟩
    · intro h1
      have hP0 : P ≠ ⊥ := by
        rintro rfl
        rw [Ideal.dvd_iff_le, le_bot_iff] at h1
        have hle : B ⊔ H.conj • B ≤ ⊥ := sup_le h1.le (sw.2 (by rw [h1]; exact bot_le))
        rw [hcop] at hle
        exact hP.ne_top (eq_top_iff.2 hle)
      have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
      unfold multiplicity
      rw [hD, emultiplicity_mul hpr, emultiplicity_eq_zero.2 (hncB h1), add_zero]
  · obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
    exact ⟨s, hs, hdiff.trans (by rw [hD])⟩
