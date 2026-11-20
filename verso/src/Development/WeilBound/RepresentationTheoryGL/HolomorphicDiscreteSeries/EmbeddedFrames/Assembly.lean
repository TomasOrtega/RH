import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSignsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement

noncomputable section

open Finset Matrix Formalism.REAL

namespace PositivityTheory.RgHe.FrameA

open PositivityTheory.RgHe.Frame PositivityTheory.UnitaryDecomposition

variable {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity`.
-/
theorem hs_nonneg' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/- English proof (translation)
Establish `h1 : emb e a - 1 = Matrix.reindex e e (Matrix.fromBlocks (a - 1) 0 0 0)`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [emb, Matrix.one_apply, e.injective.eq_iff]`.

Rewrite using `[h1]`. Unfold `hs`. Rewrite using `[← e.sum_comp, Fintype.sum_sum_type]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]`. Simplify using `[← e.sum_comp, Fintype.sum_sum_type]`.
-/
theorem hs_emb_sub (a : Matrix (Fin n) (Fin n) ℂ) : hs (emb e a - 1) = hs (a - 1) := by
  have h1 : emb e a - 1 = Matrix.reindex e e (Matrix.fromBlocks (a - 1) 0 0 0) := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [emb, Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  unfold hs
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp [← e.sum_comp, Fintype.sum_sum_type]

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Matrix.mulVec_single_one]`. Take `⟨i, rfl⟩` from `e.surjective i`. Apply the tactic sequence `rcases i with i | i <;> simp [emb]`.
-/
theorem emb_mulVec_alt (a : Matrix (Fin n) (Fin n) ℂ) :
    emb e a *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ) = Pi.single (e (Sum.inr ())) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with i | i <;> simp [emb]

/- English proof (translation)
Introduce `n ε d ε' d' e hF hinj hW`. Take `⟨hs1, hs2⟩` from `GlobalTheory.T.interlacing_signature_parity n ε d ε' d' e hF hinj hW`. Take `⟨ps1, ps2⟩` from `GlobalTheory.T.partial_fraction_coefficient_signs d d' hinj`. Establish `hD : ∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i` using `fun i => by`. Establish `h` using `ps1 i`.

Distinguish the cases in `hi : ε i = true`. Rewrite using `[if_pos hi, one_mul]`. Rewrite `h` using `[((hs1 i).1 hi).neg_one_pow, one_mul]`. Then use the resulting hypothesis. Rewrite using `[if_neg hi]`. Establish `ho : ¬ Even (above d d' (d i))` using `fun h' => hi ((hs1 i).2 h')`.

Rewrite `h` using `[(Nat.not_even_iff_odd.1 ho).neg_one_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : ∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)` using `fun j => by`. Establish `h` using `ps2 j`. Distinguish the cases in `hj : ε' j = true`.

Rewrite using `[if_pos hj]`. Rewrite `h` using `[(Nat.not_even_iff_odd.1 ((hs2 j).1 hj)).neg_one_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hj]`. Establish `he : Even (above d d' (d' j))`.

Assume the negation of the conclusion as `h'`. Conclude with `hj ((hs2 j).2 h')`. Rewrite `h` using `[he.neg_one_pow, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨g, X, hgU, hXg, hblk, hβ⟩` from `GlobalTheory.T.exists_unitary_interlacing_realization n ε d ε' d' e hF.1 hF.2 hinj hD hR`.

Use `set J := Jm ε with hJ`. Establish `hJJ : J * J = 1` using `Jm_mul_self ε`. Establish `h2 : (J * gᴴ * J) * g = 1`. Establish `: (J * gᴴ * J) * g = J * (gᴴ * J * g)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hgU, hJJ]`.

Establish `hinv : g⁻¹ = J * gᴴ * J` using `Matrix.inv_eq_left_inv h2`. Establish `hdet : IsUnit g.det` using `Matrix.isUnit_det_of_left_inverse h2`. Establish `h1 : g * (J * gᴴ * J) = 1` using `by rw [← hinv]; exact Matrix.mul_nonsing_inv g hdet`. Set `gu : UJ ε` to `⟨⟨g, J * gᴴ * J, h1, h2⟩, hgU⟩`. Establish `hgu : um gu = g` using `rfl`.

Establish `hgu' : um gu⁻¹ = g⁻¹`. Rewrite using `[hinv]`. Both sides reduce to the same expression. Use `⟨gu, fun Y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hgu, hgu']`.

Conclude with `GlobalTheory.T.trace_diagonal_block_conjugate_formula n e d d' g X hdet hXg hblk Y`. Use `set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hDd`. Establish `hX : X = g * D * g⁻¹`. Rewrite using `[hXg.symm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]`. Use `set v : Fin (n + 1) → ℂ := Pi.single (e (Sum.inr ())) 1 with hv`.

Establish `hdi : Function.Injective fun i => ((d i : ℝ) : ℂ)` using `fun i j h => Sum.inl_injective (hinj (by simpa using h))`. Establish `hcyc : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0`. Introduce `A hA hAv`. Rewrite `hA` using `[hX]`. Conclude with `GlobalTheory.T.commutant_annihilating_vector_zero g _ v hdet hdi (fun i => by rw [hinv]; exact hβ i) A hA hAv`.

Take `⟨c, hc, hAc⟩` from `GlobalTheory.T.commutator_coercive_on_annihilator X v hcyc`. Use `⟨c * hs g * hs g⁻¹ + 1, by have := hs_nonneg' g; have := hs_nonneg' g⁻¹; positivity, fun h => ?_⟩` and prove the remaining obligations. Use `set B := emb e (um h) with hB`. Use `set B' := emb e (um h⁻¹) with hB'`. Establish `hBB : B * B' = 1`.

Rewrite using `[hB, hB', ← emb_mul, ← emb_one (e := e)]`. Use `congr 1`. Conclude with `Units.mul_inv h.1`. Establish `hBB' : B' * B = 1`. Rewrite using `[hB, hB', ← emb_mul, ← emb_one (e := e)]`.

Use `congr 1`. Conclude with `Units.inv_mul h.1`. Use `set δ := dg d - (um gu⁻¹ * B' * um gu) * dg d * (um gu⁻¹ * B * um gu) with hδ`. Establish `hdg : dg d = D` using `rfl`. Establish `key : (B - 1) * X - X * (B - 1) = B * (g * δ * g⁻¹)`.

Rewrite using `[hδ, hgu, hgu', hdg, hX]`. Establish `e1 : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul _ hdet`. Establish `e2 : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`. Establish `e3 : B * (g * (g⁻¹ * (B' * (g * (D * (g⁻¹ * (B * (g * g⁻¹)))))))) = g * (D * (g⁻¹ * B))`.

Rewrite using `[e2, Matrix.mul_one, ← Matrix.mul_assoc g g⁻¹, e2, Matrix.one_mul, ← Matrix.mul_assoc B B', hBB, Matrix.one_mul]`. Rewrite using `[e3]`. Normalize the expressions using the abelian group laws. Establish `hAv : (B - 1) *ᵥ v = 0`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, hB, emb_mulVec_alt, sub_self]`.

Establish `i1` using `hAc (B - 1) hAv`. Rewrite `i1` using `[key]`. Establish `i2 : hs (B * (g * δ * g⁻¹)) ≤ hs B * (hs g * hs δ * hs g⁻¹)`. Use `(GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_left ?_ (hs_nonneg' _))` and prove the remaining obligations. Use `(GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _) (hs_nonneg' _))` and prove the remaining obligations.

Establish `i3 : hs (um h - 1) = hs (B - 1)` using `(hs_emb_sub (e := e) (um h)).symm`. Rewrite using `[i3]`. Use `hs_nonneg' B` as an intermediate fact. Use `hs_nonneg' δ` as an intermediate fact. Use `hs_nonneg' g` as an intermediate fact.

Use `hs_nonneg' g⁻¹` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frame : PositivityTheory.RgHe.Frame := by
  intro n ε d ε' d' e hF hinj hW
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.interlacing_signature_parity n ε d ε' d' e hF hinj hW
  obtain ⟨ps1, ps2⟩ := GlobalTheory.T.partial_fraction_coefficient_signs d d' hinj
  have hD : ∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i := fun i => by
    have h := ps1 i
    by_cases hi : ε i = true
    · rw [if_pos hi, one_mul]
      rwa [((hs1 i).1 hi).neg_one_pow, one_mul] at h
    · rw [if_neg hi]
      have ho : ¬ Even (above d d' (d i)) := fun h' => hi ((hs1 i).2 h')
      rw [(Nat.not_even_iff_odd.1 ho).neg_one_pow] at h
      linarith
  have hR : ∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j) := fun j => by
    have h := ps2 j
    by_cases hj : ε' j = true
    · rw [if_pos hj]
      rw [(Nat.not_even_iff_odd.1 ((hs2 j).1 hj)).neg_one_pow] at h
      linarith
    · rw [if_neg hj]
      have he : Even (above d d' (d' j)) := by
        by_contra h'
        exact hj ((hs2 j).2 h')
      rw [he.neg_one_pow, one_mul] at h
      linarith
  obtain ⟨g, X, hgU, hXg, hblk, hβ⟩ := GlobalTheory.T.exists_unitary_interlacing_realization n ε d ε' d' e hF.1 hF.2 hinj hD hR
  set J := Jm ε with hJ
  have hJJ : J * J = 1 := Jm_mul_self ε
  have h2 : (J * gᴴ * J) * g = 1 := by
    have : (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [this, hgU, hJJ]
  have hinv : g⁻¹ = J * gᴴ * J := Matrix.inv_eq_left_inv h2
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h2
  have h1 : g * (J * gᴴ * J) = 1 := by rw [← hinv]; exact Matrix.mul_nonsing_inv g hdet
  let gu : UJ ε := ⟨⟨g, J * gᴴ * J, h1, h2⟩, hgU⟩
  have hgu : um gu = g := rfl
  have hgu' : um gu⁻¹ = g⁻¹ := by
    rw [hinv]; rfl
  refine ⟨gu, fun Y => ?_, ?_⟩
  · rw [hgu, hgu']
    exact GlobalTheory.T.trace_diagonal_block_conjugate_formula n e d d' g X hdet hXg hblk Y
  · set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hDd
    have hX : X = g * D * g⁻¹ := by
      rw [hXg.symm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    set v : Fin (n + 1) → ℂ := Pi.single (e (Sum.inr ())) 1 with hv
    have hdi : Function.Injective fun i => ((d i : ℝ) : ℂ) := fun i j h =>
      Sum.inl_injective (hinj (by simpa using h))
    have hcyc : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0 := by
      intro A hA hAv
      rw [hX] at hA
      exact GlobalTheory.T.commutant_annihilating_vector_zero g _ v hdet hdi (fun i => by rw [hinv]; exact hβ i) A hA hAv
    obtain ⟨c, hc, hAc⟩ := GlobalTheory.T.commutator_coercive_on_annihilator X v hcyc
    refine ⟨c * hs g * hs g⁻¹ + 1, by have := hs_nonneg' g; have := hs_nonneg' g⁻¹; positivity, fun h => ?_⟩
    set B := emb e (um h) with hB
    set B' := emb e (um h⁻¹) with hB'
    have hBB : B * B' = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.mul_inv h.1
    have hBB' : B' * B = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.inv_mul h.1
    set δ := dg d - (um gu⁻¹ * B' * um gu) * dg d * (um gu⁻¹ * B * um gu) with hδ
    have hdg : dg d = D := rfl
    have key : (B - 1) * X - X * (B - 1) = B * (g * δ * g⁻¹) := by
      rw [hδ, hgu, hgu', hdg, hX]
      have e1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hdet
      have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      have e3 : B * (g * (g⁻¹ * (B' * (g * (D * (g⁻¹ * (B * (g * g⁻¹)))))))) = g * (D * (g⁻¹ * B)) := by
        rw [e2, Matrix.mul_one, ← Matrix.mul_assoc g g⁻¹, e2, Matrix.one_mul, ← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
      rw [e3]
      abel
    have hAv : (B - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hB, emb_mulVec_alt, sub_self]
    have i1 := hAc (B - 1) hAv
    rw [key] at i1
    have i2 : hs (B * (g * δ * g⁻¹)) ≤ hs B * (hs g * hs δ * hs g⁻¹) := by
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_left ?_ (hs_nonneg' _))
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _) (hs_nonneg' _))
    have i3 : hs (um h - 1) = hs (B - 1) := (hs_emb_sub (e := e) (um h)).symm
    rw [i3]
    have := hs_nonneg' B; have := hs_nonneg' δ; have := hs_nonneg' g; have := hs_nonneg' g⁻¹
    calc hs (B - 1) ≤ c * (hs B * (hs g * hs δ * hs g⁻¹)) := i1.trans (mul_le_mul_of_nonneg_left i2 hc.le)
      _ = (c * hs g * hs g⁻¹) * hs B * hs δ := by ring
      _ ≤ (c * hs g * hs g⁻¹ + 1) * hs B * hs δ := by gcongr; linarith

end PositivityTheory.RgHe.FrameA
