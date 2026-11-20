import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace PositivityTheory.RgJS.PrimeSumConvergence

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `GroundTheory.Global.two_le_absNorm_of_prime w.1.prime`.
-/
theorem two_le (S : Finset (HeightOneSpectrum (𝓞 E))) (w : Off E S) : 2 ≤ nq w :=
  GroundTheory.Global.two_le_absNorm_of_prime w.1.prime

/- English proof (translation)
The claim follows from `(GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hσ).subtype {w | w ∉ S}`.
-/
theorem conv (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : ℝ) (hσ : 1 < σ) :
    Summable fun w : Off E S => (nq w : ℝ) ^ (-σ) :=
  (GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hσ).subtype {w | w ∉ S}

/- English proof (translation)
Introduce `h`. Establish `ht` using `GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop E`. Use `set C : ℝ := ∑' w : (Set.univ : Set (HeightOneSpectrum (𝓞 E))), (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ with hC`. Establish `hb : ∀ s : ℝ, 1 < s → (Set.univ : Set (HeightOneSpectrum (𝓞 E))).primeIdealZetaSum s ≤ C`. Introduce `s hs`.

Rewrite using `[Set.primeIdealZetaSum_def]`. Use `Summable.tsum_le_tsum (fun w => ?_) ((GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hs).subtype _) (h.subtype _)` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ Ideal.absNorm w.1.asIdeal` using `by exact_mod_cast GroundTheory.Global.one_le_absNorm w.1`. Use `show (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹`. Rewrite using `[← Real.rpow_neg_one]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le h1 (by linarith)`. Take `⟨s, hlt, hs⟩` from `((ht.eventually (eventually_gt_atTop C)).and self_mem_nhdsWithin).exists`. Conclude with `absurd (hb s hs) (not_le.2 hlt)`.
-/
theorem not_summable_all : ¬ Summable fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
  intro h
  have ht := GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop E
  set C : ℝ := ∑' w : (Set.univ : Set (HeightOneSpectrum (𝓞 E))), (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ with hC
  have hb : ∀ s : ℝ, 1 < s → (Set.univ : Set (HeightOneSpectrum (𝓞 E))).primeIdealZetaSum s ≤ C := by
    intro s hs
    rw [Set.primeIdealZetaSum_def]
    refine Summable.tsum_le_tsum (fun w => ?_)
      ((GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hs).subtype _) (h.subtype _)
    have h1 : (1 : ℝ) ≤ Ideal.absNorm w.1.asIdeal := by exact_mod_cast GroundTheory.Global.one_le_absNorm w.1
    show (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  obtain ⟨s, hlt, hs⟩ := ((ht.eventually (eventually_gt_atTop C)).and self_mem_nhdsWithin).exists
  exact absurd (hb s hs) (not_le.2 hlt)

/- English proof (translation)
Introduce `h`. Apply `not_summable_all (E := E)` to reduce the goal to its premises. Establish `h' : Summable fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ (S : Set (HeightOneSpectrum (𝓞 E)))} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹` using `h`. Establish `hf : Summable fun w : (S : Set (HeightOneSpectrum (𝓞 E))) => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹` using `S.finite_toSet.summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹)`. Conclude with `(summable_subtype_and_compl (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) (s := (S : Set (HeightOneSpectrum (𝓞 E))))).1 ⟨hf, h'⟩`.
-/
theorem div (S : Finset (HeightOneSpectrum (𝓞 E))) : ¬ Summable fun w : Off E S => (nq w : ℝ)⁻¹ := by
  intro h
  apply not_summable_all (E := E)
  have h' : Summable fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ (S : Set (HeightOneSpectrum (𝓞 E)))} =>
      (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ := h
  have hf : Summable fun w : (S : Set (HeightOneSpectrum (𝓞 E))) => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ :=
    S.finite_toSet.summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹)
  exact (summable_subtype_and_compl (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹)
    (s := (S : Set (HeightOneSpectrum (𝓞 E))))).1 ⟨hf, h'⟩

end PositivityTheory.RgJS.PrimeSumConvergence

namespace PositivityTheory.RgJS

/- English proof (translation)
Introduce `_ _ _ S` and use `⟨PrimeSumConvergence.two_le S, PrimeSumConvergence.conv S, PrimeSumConvergence.div S⟩`.
-/
theorem prime_sum_converges_and_diverges : PrimeOff := fun _ _ _ S =>
  ⟨PrimeSumConvergence.two_le S, PrimeSumConvergence.conv S, PrimeSumConvergence.div S⟩

end PositivityTheory.RgJS
