import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal

def RamPart (D : D7) : Prop :=
  ∀ p : ℕ, p.Prime →
    (1 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) ↔ p ∣ D.host.condN)

/- English proof (translation)
Rewrite using `[D.host.der.finrank_E]`. Use `show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem deg_part (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)
  ring

/- English proof (translation)
Use `haveI := D.host.der.cm`. Use `haveI := D.host.galois`. Use `haveI := h𝔭.isMaximal h0`. Use `haveI : IsGalois D.host.F D.host.E := by first`. Consider the case `infer_instance`.

Consider the case `exact IsGalois.tower_top_of_isGalois ℚ D.host.F D.host.E`. Establish `h3 : Module.finrank D.host.F D.host.E = 2` using `by first`. Consider the case `exact IsQuadraticExtension.finrank_eq_two _ _`. Consider the case `(have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E; have h5 : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos; rw [D.host.der.finrank_E] at h4; rw [D.host.der.finrank_F] at h4 h5; exact Nat.eq_of_mul_eq_mul_left h5 (by linarith))`. Establish `h2 : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2` using `by first`.

Consider the case `rw [IsGalois.card_aut_eq_finrank, h3]`. Consider the case `rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h3]`. Establish `h1` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭 (𝓞 D.host.E) (D.host.E ≃ₐ[D.host.F] D.host.E)`. Rewrite `h1` using `[h2]`. Break down `D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, hf⟩` into its components or cases.

Rewrite `h1` using `[h]`. Establish `h6 : 𝔭.ramificationIdxIn (𝓞 D.host.E) * 𝔭.inertiaDegIn (𝓞 D.host.E) = 1`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Nat.eq_one_of_mul_eq_one_right h6`. Rewrite `h1` using `[h, hf]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem unram_part (D : D7) (𝔭 : Ideal (𝓞 D.host.F)) (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) :
    𝔭.ramificationIdxIn (𝓞 D.host.E) = 1 := by

  haveI := D.host.der.cm
  haveI := D.host.galois
  haveI := h𝔭.isMaximal h0
  haveI : IsGalois D.host.F D.host.E := by
    first
    | infer_instance
    | exact IsGalois.tower_top_of_isGalois ℚ D.host.F D.host.E
  have h3 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | exact IsQuadraticExtension.finrank_eq_two _ _
    | (have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E; have h5 : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos; rw [D.host.der.finrank_E] at h4; rw [D.host.der.finrank_F] at h4 h5; exact Nat.eq_of_mul_eq_mul_left h5 (by linarith))
  have h2 : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    first
    | rw [IsGalois.card_aut_eq_finrank, h3]
    | rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h3]
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭 (𝓞 D.host.E)
    (D.host.E ≃ₐ[D.host.F] D.host.E)
  rw [h2] at h1
  rcases D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, hf⟩
  · rw [h] at h1
    have h6 : 𝔭.ramificationIdxIn (𝓞 D.host.E) * 𝔭.inertiaDegIn (𝓞 D.host.E) = 1 := by
      linarith
    exact Nat.eq_one_of_mul_eq_one_right h6
  · rw [h, hf] at h1
    omega

/- English proof (translation)
Establish `h0 : 𝔭 ≠ ⊥`. Introduce and unpack `rfl`. Establish `h2 : span {(p : ℤ)} = ⊥`. Rewrite using `[hlo.over]`. Conclude with `Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 D.host.F)).injective_int`.

Rewrite `h2` using `[Ideal.span_singleton_eq_bot]`. Conclude with `hpp.ne_zero (by exact_mod_cast h2)`. Break down `D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, -⟩` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Take `⟨P, hP⟩` from `Set.ncard_eq_one.mp h`. Establish `hPm : P ∈ primesOver 𝔭 (𝓞 D.host.E)`. Rewrite using `[hP]`. Conclude with `Set.mem_singleton P`. Use `haveI : P.IsPrime := hPm.1`.

Use `haveI : P.LiesOver 𝔭 := hPm.2`. Use `haveI : Fact p.Prime := ⟨hpp⟩`. Use `haveI : P.LiesOver (span {(p : ℤ)}) := by first`. Consider the case `exact Ideal.LiesOver.trans P 𝔭 (span {(p : ℤ)})`. Consider the case `infer_instance`.

Establish `h1` using `D.host.der.eta.2.2 p hp P`. Establish `hc : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭` using `(Ideal.LiesOver.over (P := P) (p := 𝔭)).symm`. Rewrite `h1` using `[hc]`. Simplify using `[Formalism.HC.HostRaw.etaF, h] at h1`.
-/
private theorem split_part (D : D7) (p : ℕ) (hpp : p.Prime) (hp : p ∣ D.host.condN)
    (𝔭 : Ideal (𝓞 D.host.F)) (h𝔭 : 𝔭.IsPrime) (hlo : 𝔭.LiesOver (span {(p : ℤ)})) :
    (primesOver 𝔭 (𝓞 D.host.E)).ncard = 2 := by
  have h0 : 𝔭 ≠ ⊥ := by
    rintro rfl
    have h2 : span {(p : ℤ)} = ⊥ := by
      rw [hlo.over]
      exact Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 D.host.F)).injective_int
    rw [Ideal.span_singleton_eq_bot] at h2
    exact hpp.ne_zero (by exact_mod_cast h2)
  rcases D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, -⟩
  · exact h
  ·
    exfalso
    obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp h
    have hPm : P ∈ primesOver 𝔭 (𝓞 D.host.E) := by
      rw [hP]
      exact Set.mem_singleton P
    haveI : P.IsPrime := hPm.1
    haveI : P.LiesOver 𝔭 := hPm.2
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : P.LiesOver (span {(p : ℤ)}) := by
      first
      | exact Ideal.LiesOver.trans P 𝔭 (span {(p : ℤ)})
      | infer_instance
    have h1 := D.host.der.eta.2.2 p hp P
    have hc : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭 :=
      (Ideal.LiesOver.over (P := P) (p := 𝔭)).symm
    rw [hc] at h1
    simp [Formalism.HC.HostRaw.etaF, h] at h1

/- English proof (translation)
Unfold `Formalism.MainNotions.GlobalTheoryTheory.rdF Formalism.BasicNotions.Host.rdE`. Rewrite using `[D.host.der.discr_sq, D.host.der.finrank_E, D.host.der.finrank_F]`. Use `push_cast`. Rewrite using `[abs_pow, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem rd_part (D : D7) : rdF D = D.host.rdE := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.rdF Formalism.BasicNotions.Host.rdE
  rw [D.host.der.discr_sq, D.host.der.finrank_E, D.host.der.finrank_F]
  push_cast
  rw [abs_pow, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

/- English proof (translation)
Unfold `Conclusion1`. Conclude with `⟨D.host.der.cm, deg_part D, hRam, D.host.der.norm_mu, fun 𝔭 h𝔭 h0 => unram_part D 𝔭 h𝔭 h0, fun p hpp hp 𝔭 h𝔭 hlo => split_part D p hpp hp 𝔭 h𝔭 hlo, rd_part D⟩`.
-/
theorem lemma_one_one_of_ramified (D : D7) (hRam : RamPart D) : Conclusion1 D := by
  unfold Conclusion1
  exact ⟨D.host.der.cm, deg_part D, hRam, D.host.der.norm_mu,
    fun 𝔭 h𝔭 h0 => unram_part D 𝔭 h𝔭 h0,
    fun p hpp hp 𝔭 h𝔭 hlo => split_part D p hpp hp 𝔭 h𝔭 hlo, rd_part D⟩

/- English proof (translation)
The claim follows from `lemma_one_one_of_ramified D (fun p hp => SlopeTestRemainingChoices.ram_iff D p hp)`.
-/
theorem ramification_two_and_conjugation_at_q_and_d (D : D7) : Conclusion1 D :=
  lemma_one_one_of_ramified D (fun p hp => SlopeTestRemainingChoices.ram_iff D p hp)

end Formalism.MainNotions.UnusedSlot33

end
