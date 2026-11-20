import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace PositivityTheory.RgJS.PrimeSumConvergence

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem two_le (S : Finset (HeightOneSpectrum (𝓞 E))) (w : Off E S) : 2 ≤ nq w :=
  GroundTheory.Global.two_le_absNorm_of_prime w.1.prime

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conv (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : ℝ) (hσ : 1 < σ) :
    Summable fun w : Off E S => (nq w : ℝ) ^ (-σ) :=
  (GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hσ).subtype {w | w ∉ S}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem prime_sum_converges_and_diverges : PrimeOff := fun _ _ _ S =>
  ⟨PrimeSumConvergence.two_le S, PrimeSumConvergence.conv S, PrimeSumConvergence.div S⟩

end PositivityTheory.RgJS
