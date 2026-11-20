import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.RgEisBInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥` using `(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))`. Take `⟨Q, -, hQ, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E)) (hker.le.trans bot_le)`. Establish `hne : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[← hQv]`. Conclude with `hker`. Conclude with `⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩`.
-/
theorem exists_below_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 E), below F w = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (hker.le.trans bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact hker
  exact ⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩

/- English proof (translation)
Establish `key : ∀ w : HeightOneSpectrum (𝓞 E), finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔ finEval (below F w) x ∈ (below F w).adicCompletionIntegers F`. Introduce `w`. Use `haveI := liesOver_below (K := F) w`. Use `haveI := w.isPrime`. Establish `h1 : finEval w (adeleMap F E x) = SemiLocal.completionMap (below F w) w (finEval (below F w) x)` using `finiteAdeleMap_apply x.2 w`.

Rewrite using `[h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, SemiLocal.valued_completionMap]`. Conclude with `pow_le_one_iff (Ideal.ramificationIdx_pos w.asIdeal (𝓞 F)).ne'`. Simplify using `only [intAd, Subring.mem_iInf, Subring.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`.

Take `⟨w, rfl⟩` from `exists_below_eq (E := E) v`. Conclude with `(key w).1 (h w)`. Introduce `h w`. Conclude with `(key w).2 (h _)`.
-/
theorem adeleMap_mem_intAd_iff (x : 𝔸[F]) : adeleMap F E x ∈ intAd E ↔ x ∈ intAd F := by
  have key : ∀ w : HeightOneSpectrum (𝓞 E),
      finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔
        finEval (below F w) x ∈ (below F w).adicCompletionIntegers F := by
    intro w
    haveI := liesOver_below (K := F) w
    haveI := w.isPrime
    have h1 : finEval w (adeleMap F E x) =
        SemiLocal.completionMap (below F w) w (finEval (below F w) x) :=
      finiteAdeleMap_apply x.2 w
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      SemiLocal.valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos w.asIdeal (𝓞 F)).ne'
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := exists_below_eq (E := E) v
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 (h _)

/- English proof (translation)
Establish `h` using `(GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x`. Conclude with `h`.
-/
theorem nuCM_eqv (x : 𝔸[F]) : eqv F E (nuCM F E x) = adeleMap F E x := by
  have h := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x
  exact h

/- English proof (translation)
Unfold `BInt ForCM`. Introduce `F E _ _ _ _ _ σ χ c _ _ _ _ x`. Simplify using `only [adCM, Subring.mem_comap]`. Express the relevant statement in the definitionally equal form `eqv F E (nuCM F E x) ∈ intAd E ↔ _`. Rewrite using `[nuCM_eqv, adeleMap_mem_intAd_iff]`.
-/
theorem bInt : BInt := by
  unfold BInt ForCM
  intro F E _ _ _ _ _ σ χ c _ _ _ _ x
  simp only [adCM, Subring.mem_comap]
  change eqv F E (nuCM F E x) ∈ intAd E ↔ _
  rw [nuCM_eqv, adeleMap_mem_intAd_iff]

end GlobalTheory.CompanionTheory.RgEisBInt
