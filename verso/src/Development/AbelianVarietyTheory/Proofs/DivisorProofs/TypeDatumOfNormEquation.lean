import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeDatumRefactor

variable {E : Type} [Field E] [NumberField E] [StarRing E]

noncomputable def cjEquiv (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E ≃+* 𝓞 E :=
  RingEquiv.ofRingHom (SumWCompare.cj E) (SumWCompare.cj E) (RingHom.ext SumWCompare.cj_cj) (RingHom.ext SumWCompare.cj_cj)

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (by simpa [SumWCompare.cj_coe] using hn)`.
-/
theorem mul_cj {g : ℕ} {p : 𝓞 E} (hn : (p : E) * star (p : E) = (g : E)) : p * SumWCompare.cj E p = (g : 𝓞 E) :=
  RingOfIntegers.ext (by simpa [SumWCompare.cj_coe] using hn)

/- English proof (translation)
Use `⟨h.deg1 i w hw, fun hg => ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[← mul_cj (h.norm i), mul_comm]`. Use `w.isPrime` as an intermediate fact. Break down `Ideal.IsPrime.mul_mem_pow w.asIdeal hg with h1 | h1` into its components or cases. Conclude with `h.split i w hw _ (SumWCompare.cj_coe _) h1`.

Conclude with `h.unram i w hw h1`.
-/
theorem key_of_mem {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) (i : Fin 2) (w : Pl E)
    (hw : pb i ∈ w.asIdeal) : Nat.card (kP w) = gp i ∧ ((gp i : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  refine ⟨h.deg1 i w hw, fun hg => ?_⟩
  rw [← mul_cj (h.norm i), mul_comm] at hg
  have := w.isPrime
  rcases Ideal.IsPrime.mul_mem_pow w.asIdeal hg with h1 | h1
  · exact h.split i w hw _ (SumWCompare.cj_coe _) h1
  · exact h.unram i w hw h1

/- English proof (translation)
Rewrite `hw` using `[← mul_cj (h.norm i)]`. Break down `w.isPrime.mem_or_mem hw with h1 | h1` into its components or cases. Conclude with `key_of_mem h i w h1`. Use `w.isPrime` as an intermediate fact. Establish `hmap : (w.asIdeal.comap (SumWCompare.cj E)).map (cjEquiv E : 𝓞 E →+* 𝓞 E) = w.asIdeal` using `Ideal.map_comap_of_surjective (SumWCompare.cj E) (cjEquiv E).surjective _`.

Set `w' : Pl E` to `⟨w.asIdeal.comap (SumWCompare.cj E), Ideal.comap_isPrime _ _, fun h0 => by`. Rewrite `hmap` using `[h0, Ideal.map_bot]`. Conclude with `w.ne_bot hmap.symm⟩`. Take `⟨h2, h3⟩` from `key_of_mem h i w' h1`. Use `⟨?_, fun hg => h3 ?_⟩` and prove the remaining obligations.

Rewrite using `[← h2]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv w'.asIdeal w.asIdeal (cjEquiv E) hmap.symm).toEquiv).symm`. Establish `h4` using `Ideal.mem_map_of_mem (SumWCompare.cj E) hg`. Rewrite `h4` using `[map_natCast, Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ 2 h4` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `SumWCompare.cj E (SumWCompare.cj E x) ∈ w.asIdeal`. Rewrite using `[SumWCompare.cj_cj]` and apply the resulting hypothesis.
-/
theorem key {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) (i : Fin 2) (w : Pl E)
    (hw : ((gp i : ℕ) : 𝓞 E) ∈ w.asIdeal) : Nat.card (kP w) = gp i ∧ ((gp i : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  rw [← mul_cj (h.norm i)] at hw
  rcases w.isPrime.mem_or_mem hw with h1 | h1
  · exact key_of_mem h i w h1
  · have := w.isPrime
    have hmap : (w.asIdeal.comap (SumWCompare.cj E)).map (cjEquiv E : 𝓞 E →+* 𝓞 E) = w.asIdeal :=
      Ideal.map_comap_of_surjective (SumWCompare.cj E) (cjEquiv E).surjective _
    let w' : Pl E := ⟨w.asIdeal.comap (SumWCompare.cj E), Ideal.comap_isPrime _ _, fun h0 => by
      rw [h0, Ideal.map_bot] at hmap
      exact w.ne_bot hmap.symm⟩
    obtain ⟨h2, h3⟩ := key_of_mem h i w' h1
    refine ⟨?_, fun hg => h3 ?_⟩
    · rw [← h2]
      exact (Nat.card_congr (Ideal.quotientEquiv w'.asIdeal w.asIdeal (cjEquiv E) hmap.symm).toEquiv).symm
    · have h4 := Ideal.mem_map_of_mem (SumWCompare.cj E) hg
      rw [map_natCast, Ideal.map_pow] at h4
      refine Ideal.pow_right_mono ?_ 2 h4
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change SumWCompare.cj E (SumWCompare.cj E x) ∈ w.asIdeal
      rwa [SumWCompare.cj_cj]

/- English proof (translation)
Introduce `E _ _ _ gp pb π h hn`. Establish `hg : ∀ i (w : Pl E), π i ∈ w.asIdeal → ((gp i : ℕ) : 𝓞 E) ∈ w.asIdeal` using `fun i w hw => by`. Rewrite using `[← mul_cj (hn i)]`. Conclude with `w.asIdeal.mul_mem_right _ hw`. Use `⟨h.prime, h.ne, hn, fun i w hw => (key h i w (hg i w hw)).1, fun i w hw h2 => ?_, fun i w hw c hc h2 => ?_⟩` and prove the remaining obligations.

Use `(key h i w (hg i w hw)).2 ?_` and prove the remaining obligations. Rewrite using `[← mul_cj (hn i)]`. Conclude with `Ideal.mul_mem_right _ _ h2`. Use `(key h i w (hg i w hw)).2 ?_` and prove the remaining obligations. Take `rfl : c = SumWCompare.cj E (π i)` from `RingOfIntegers.ext hc`.

Rewrite using `[← mul_cj (hn i), sq]`. Conclude with `Ideal.mul_mem_mul hw h2`.
-/
theorem isTypeDatum_of_norm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) (pb π : Fin 2 → 𝓞 E), IsTypeDatum gp pb → (∀ i, (π i : E) * star (π i : E) = (gp i : E)) → IsTypeDatum gp π := by
  intro E _ _ _ gp pb π h hn
  have hg : ∀ i (w : Pl E), π i ∈ w.asIdeal → ((gp i : ℕ) : 𝓞 E) ∈ w.asIdeal := fun i w hw => by
    rw [← mul_cj (hn i)]; exact w.asIdeal.mul_mem_right _ hw
  refine ⟨h.prime, h.ne, hn, fun i w hw => (key h i w (hg i w hw)).1, fun i w hw h2 => ?_, fun i w hw c hc h2 => ?_⟩
  · refine (key h i w (hg i w hw)).2 ?_
    rw [← mul_cj (hn i)]; exact Ideal.mul_mem_right _ _ h2
  · refine (key h i w (hg i w hw)).2 ?_
    obtain rfl : c = SumWCompare.cj E (π i) := RingOfIntegers.ext hc
    rw [← mul_cj (hn i), sq]; exact Ideal.mul_mem_mul hw h2

end GlobalTheory.TypeDatumRefactor
