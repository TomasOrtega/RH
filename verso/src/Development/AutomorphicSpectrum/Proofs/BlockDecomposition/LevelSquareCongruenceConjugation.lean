import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.Twist

/- English proof (translation)
Substitute `hw` using the available equality. Rewrite using `[fromBlocks_map, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>`. Apply the tactic sequence `simp [smul_eq_mul] <;> simp [Algebra.smul_def]`.
-/
theorem block_twist {O L : Type} [CommRing O] [Field L] [Algebra O L] {n : ℕ} (ϖ : O) (w : L)
    (hw : w = algebraMap O L ϖ) (A B C D : Matrix (Fin n) (Fin n) O) :
    (fromBlocks A B (ϖ • C) D).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) *
        (fromBlocks A (ϖ • B) C D).map (algebraMap O L) := by
  subst hw
  rw [fromBlocks_map, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [smul_eq_mul] <;> simp [Algebra.smul_def]

/- English proof (translation)
Introduce `O L _ _ _ _ _ _ n ϖ hϖ w hw γ hγ`. Establish `hγ' : ∀ i j, (γ : Matrix (Ix n) (Ix n) O) i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ Ideal.span {ϖ ^ 2}`. Introduce `i j`. Rewrite using `[← Ideal.Quotient.eq]`. Use `congrArg (fun u : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => u.1 i j) (MonoidHom.mem_ker.1 hγ)` as an intermediate fact.

Simplify `this` using `[Matrix.one_apply, apply_ite]`. Establish `hϖm : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit`. Establish `hm : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O` using `(Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ϖ two_ne_zero)).trans ((Ideal.span_singleton_le_iff_mem _).2 hϖm)`. Establish `hC : ∀ i j, ∃ c, (γ : Matrix (Ix n) (Ix n) O) (Sum.inr i) (Sum.inl j) = ϖ * (ϖ * c)`. Introduce `i j`.

Establish `h0` using `hγ' (Sum.inr i) (Sum.inl j)`. Simplify using `only [Matrix.one_apply, reduceCtorEq, if_false, sub_zero] at h0`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 h0`. Conclude with `⟨c, by rw [← hc]; ring⟩`. Use `choose C hCe using hC`.

Take `⟨M, hM⟩ : ∃ M : Matrix (Ix n) (Ix n) O, M = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁ (ϖ • (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂) (ϖ • Matrix.of C) (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂` from `⟨_, rfl⟩`. Establish `hγM : (γ : Matrix (Ix n) (Ix n) O) = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁ (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂ (ϖ • (ϖ • Matrix.of C)) (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hCe]`.

Establish `hsc : Matrix.scalar (Fin n) (w : L) = (w : L) • (1 : Matrix (Fin n) (Fin n) L)`. Rewrite using `[Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]`. Establish `hrel : (γ : Matrix (Ix n) (Ix n) O).map (algebraMap O L) * fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) = fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) * M.map (algebraMap O L)`. Rewrite using `[hsc, hM]`. Use `conv_lhs => rw [hγM]`.

Conclude with `block_twist ϖ (w : L) hw _ _ _ _`. Establish `hτ : (fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L))).det ≠ 0`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, hsc, Matrix.det_smul, Matrix.det_one]`. Simplify using the standard rewrite rules. Establish `hdetM : M.det = (γ : Matrix (Ix n) (Ix n) O).det`.

Establish `h1` using `congrArg Matrix.det hrel`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, mul_comm]`. Establish `h2` using `mul_left_cancel₀ hτ h1`. Rewrite `h2` using `[← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det]`. Conclude with `(IsFractionRing.injective O L h2).symm`.

Establish `hdet : IsUnit M.det`. Rewrite using `[hdetM]`. Conclude with `Matrix.isUnits_det_units γ`. Establish `hMm : ∀ i j, M i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ IsLocalRing.maximalIdeal O`. Introduce `i j`.

Rewrite using `[hM]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify `hm (hγ' (Sum.inl i) (Sum.inl j))` using `[Matrix.toBlocks₁₁]`. Simplify using `using Ideal.mul_mem_right _ _ hϖm`. Simplify using `using Ideal.mul_mem_right _ _ hϖm`.

Simplify `hm (hγ' (Sum.inr i) (Sum.inr j))` using `[Matrix.toBlocks₂₂]`. Use `⟨Matrix.nonsingInvUnit M hdet, Units.ext ?_, Units.ext ?_⟩` and prove the remaining obligations. Conclude with `hrel`. Establish `h3 : M.map (IsLocalRing.residue O) = (1 : Matrix (Ix n) (Ix n) O).map (IsLocalRing.residue O)`. Use extensionality with `i j`.

Conclude with `Ideal.Quotient.eq.2 (hMm i j)`. Rewrite `h3` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h3`.
-/
theorem twist_gam : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw γ hγ
  have hγ' : ∀ i j, (γ : Matrix (Ix n) (Ix n) O) i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈
      Ideal.span {ϖ ^ 2} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => u.1 i j)
      (MonoidHom.mem_ker.1 hγ)
    simpa [Matrix.one_apply, apply_ite] using this
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hm : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ϖ two_ne_zero)).trans
      ((Ideal.span_singleton_le_iff_mem _).2 hϖm)
  have hC : ∀ i j, ∃ c, (γ : Matrix (Ix n) (Ix n) O) (Sum.inr i) (Sum.inl j) = ϖ * (ϖ * c) := by
    intro i j
    have h0 := hγ' (Sum.inr i) (Sum.inl j)
    simp only [Matrix.one_apply, reduceCtorEq, if_false, sub_zero] at h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h0
    exact ⟨c, by rw [← hc]; ring⟩
  choose C hCe using hC
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Ix n) (Ix n) O, M = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (ϖ • (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂) (ϖ • Matrix.of C)
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := ⟨_, rfl⟩
  have hγM : (γ : Matrix (Ix n) (Ix n) O) = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂ (ϖ • (ϖ • Matrix.of C))
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hCe]
  have hsc : Matrix.scalar (Fin n) (w : L) = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hrel : (γ : Matrix (Ix n) (Ix n) O).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) *
        M.map (algebraMap O L) := by
    rw [hsc, hM]
    conv_lhs => rw [hγM]
    exact block_twist ϖ (w : L) hw _ _ _ _
  have hτ : (fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L))).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, hsc, Matrix.det_smul, Matrix.det_one]
    simp
  have hdetM : M.det = (γ : Matrix (Ix n) (Ix n) O).det := by
    have h1 := congrArg Matrix.det hrel
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h1
    have h2 := mul_left_cancel₀ hτ h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.map_det] at h2
    exact (IsFractionRing.injective O L h2).symm
  have hdet : IsUnit M.det := by
    rw [hdetM]
    exact Matrix.isUnits_det_units γ
  have hMm : ∀ i j, M i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [hM]
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.toBlocks₁₁] using hm (hγ' (Sum.inl i) (Sum.inl j))
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa [Matrix.toBlocks₂₂] using hm (hγ' (Sum.inr i) (Sum.inr j))
  refine ⟨Matrix.nonsingInvUnit M hdet, Units.ext ?_, Units.ext ?_⟩
  · exact hrel
  · have h3 : M.map (IsLocalRing.residue O) = (1 : Matrix (Ix n) (Ix n) O).map (IsLocalRing.residue O) := by
      ext i j
      exact Ideal.Quotient.eq.2 (hMm i j)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

end GlobalTheory.CompanionTheory.Jp.Twist
