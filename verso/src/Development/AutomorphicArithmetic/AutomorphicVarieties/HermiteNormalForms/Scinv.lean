import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ N A hA`. Use `⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hA), ?_⟩` and prove the remaining obligations. Establish `hmem : ((Ideal.absNorm (Ideal.span {A.det}) : ℕ) : 𝓞 L) ∈ Ideal.span {A.det}` using `Ideal.absNorm_mem _`. Rewrite `hmem` using `[Ideal.absNorm_span_singleton, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hmem`.

Establish `hc' : ((nrmDet A : ℕ) : 𝓞 L) = A.det * c` using `hc`. Use `⟨c • A.adjugate, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc', mul_comm]`. Rewrite using `[Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hc', mul_comm]`.
-/
theorem UpperTheory.V.KT.scinv :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    0 < nrmDet A ∧ ∃ B : Matrix (Fin N) (Fin N) (𝓞 L), A * B = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) ∧
      B * A = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) := by
  intro L _ _ N A hA
  refine ⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hA), ?_⟩
  have hmem : ((Ideal.absNorm (Ideal.span {A.det}) : ℕ) : 𝓞 L) ∈ Ideal.span {A.det} :=
    Ideal.absNorm_mem _
  rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((nrmDet A : ℕ) : 𝓞 L) = A.det * c := hc
  refine ⟨c • A.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc', mul_comm]
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hc', mul_comm]
