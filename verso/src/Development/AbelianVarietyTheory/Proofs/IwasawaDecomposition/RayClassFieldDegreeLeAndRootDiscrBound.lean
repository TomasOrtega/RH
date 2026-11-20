import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.RaySize

/- English proof (translation)
Use `⟨fun ψ => ?_⟩` and prove the remaining obligations. Establish `h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ))` using `⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h`.
-/
theorem isEmpty_realEmb (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : IsEmpty (E →+* ℝ) := by
  refine ⟨fun ψ => ?_⟩
  have h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ)) :=
    ⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h

/- English proof (translation)
Introduce `E _ _ _ φ N M h hN`. Use `haveI : NumberField M := h.numberField`. Use `letI := algOf φ M h.emb_mem`. Establish `hR : IsRayField E M (natIdeal E N)` using `h.isRayField`. Use `haveI : IsAbelianGalois E M := hR.1`.

Establish `hdeg : degOver φ M h.emb_mem = Module.finrank E M` using `rfl`. Establish `hfin` using `finrank_mul_degOver φ M h.emb_mem`. Rewrite `hfin`, the goal using `[hdeg]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2 haveI := isEmpty_realEmb E`.

Rewrite `h1` using `[Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Then use the resulting hypothesis. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfin]`. Establish `: (0 : ℝ) < Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`. Establish `: (0 : ℝ) < Module.finrank E M` using `by exact_mod_cast Module.finrank_pos`.

Rewrite using `[Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]`. Establish `hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭` using `fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))`. Establish `hmem` using `GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun`. Establish `h2` using `GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M) (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero hN`.

Establish `hd : (0 : ℝ) < Module.finrank E M` using `by exact_mod_cast Module.finrank_pos`. Rewrite `h2` using `[Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc]`. Conclude with `h2`.
-/
theorem degOver_le_and_sz : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  intro E _ _ _ φ N M h hN
  haveI : NumberField M := h.numberField
  letI := algOf φ M h.emb_mem
  have hR : IsRayField E M (natIdeal E N) := h.isRayField
  haveI : IsAbelianGalois E M := hR.1
  have hdeg : degOver φ M h.emb_mem = Module.finrank E M := rfl
  have hfin := finrank_mul_degOver φ M h.emb_mem
  rw [hdeg] at hfin ⊢
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2
    haveI := isEmpty_realEmb E
    rwa [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [← hfin]
      have : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
      have : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    · have hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭 :=
        fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))
      have hmem := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun
      have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M)
        (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem
      have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hd : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc] at h2
      exact h2

end GlobalTheory.Mem.Fld.RaySize
