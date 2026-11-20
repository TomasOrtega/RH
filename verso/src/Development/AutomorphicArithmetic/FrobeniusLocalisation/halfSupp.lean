import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffEKSupp
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `φ H B hD hcop`. Establish `mono : ∀ {I J : Ideal (𝓞 H.E)}, I ≤ J → H.conj • I ≤ H.conj • J`. Introduce `I J h`. Rewrite using `[Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]`. Conclude with `Ideal.map_mono h`.

Establish `inv : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I`. Introduce `I`. Rewrite using `[smul_smul, H.conj_mul_conj, one_smul]`. Establish `sw : ∀ {I J : Ideal (𝓞 H.E)}, H.conj • I ≤ J ↔ I ≤ H.conj • J`. Introduce `I J`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `mono h` using `only [inv]`. Introduce `h`. Simplify `mono h` using `only [inv]`.

Use `⟨fun P hP => ?_, ?_⟩` and prove the remaining obligations. Establish `hsupp` using `(UpperTheory.HF.diff_EK_supp H).2.1 P`. Establish `notboth : ¬ (B ≤ P ∧ B ≤ H.conj • P)`. Introduce and unpack `⟨h1, h2⟩`. Apply `hP.ne_top` to reduce the goal to its premises.

Rewrite using `[eq_top_iff, ← hcop]`. Conclude with `sup_le h1 (sw.2 h2)`. Establish `hncB : P ∣ B → ¬ P ∣ H.conj • B`. Introduce `h1 h2`. Rewrite `h1`, `h2` using `[Ideal.dvd_iff_le]`.

Conclude with `notboth ⟨h1, sw.1 h2⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsupp, hD]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`.

Conclude with `dvd_mul_of_dvd_left h _`. Rewrite `h`, the goal using `[Ideal.dvd_iff_le]`. Conclude with `le_trans Ideal.mul_le_right (sw.2 h)`. Introduce `h`. Rewrite `h` using `[Ideal.dvd_iff_le]`.

Break down `hP.mul_le.1 h with h1 | h1` into its components or cases. Conclude with `Or.inl (Ideal.dvd_iff_le.2 h1)`. Conclude with `Or.inr (Ideal.dvd_iff_le.2 (sw.1 h1))`. Introduce and unpack `⟨h1, h2⟩`. Rewrite `h1`, `h2` using `[Ideal.dvd_iff_le]`.

Conclude with `notboth ⟨h1, h2⟩`. Introduce `h1`. Establish `hP0 : P ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `h1` using `[Ideal.dvd_iff_le, le_bot_iff]`.

Establish `hle : B ⊔ H.conj • B ≤ ⊥` using `sup_le h1.le (sw.2 (by rw [h1]; exact bot_le))`. Rewrite `hle` using `[hcop]`. Conclude with `hP.ne_top (eq_top_iff.2 hle)`. Establish `hpr : Prime P` using `Ideal.prime_of_isPrime hP0 hP`. Unfold `multiplicity`.

Rewrite using `[hD, emultiplicity_mul hpr, emultiplicity_eq_zero.2 (hncB h1), add_zero]`. Take `⟨-, s, hs, -, hdiff⟩` from `discr_K H`. Conclude with `⟨s, hs, hdiff.trans (by rw [hD])⟩`.
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
