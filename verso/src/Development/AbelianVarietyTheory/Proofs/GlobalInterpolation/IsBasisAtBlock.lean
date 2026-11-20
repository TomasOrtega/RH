import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchBasis

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_sumLat {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 K) (Fin n → K)) (t : K)
    (x : Fin N → K) :
    x ∈ Br.sumLat hN M t ↔ (fun a => x (Br.iC hN a)) ∈ M ∧ ∃ c : 𝓞 K, x (Br.iL hN) = (c : K) * t := Iff.rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
theorem mem_colLat {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, ∀ a, ∑ j, (c j : K) * (B : Matrix (Fin n) (Fin n) K) a j = x a := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]

/- English proof (translation)
Extract witnesses or component facts from the available result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem colLat_block {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (t : K) (B : GL (Fin n) K)
    (B' : GL (Fin N) K) (h : IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t) :
    colLat B' = Br.sumLat hN (colLat B) t := by
  obtain ⟨h1, h2, h3⟩ := h
  ext x
  rw [mem_sumLat, mem_colLat, mem_colLat]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun j => c (Br.iC hN j), fun a => ?_⟩, c (Br.iL hN), ?_⟩
    · rw [← hc, sum_split hN]
      simp only [h1, (h2 _).1, mul_zero, add_zero]
    · rw [← hc, sum_split hN]
      simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add]
  · rintro ⟨⟨c, hc⟩, d, hd⟩
    refine ⟨fun j => if hj : j.val < n then c ⟨j.val, hj⟩ else d, fun a => ?_⟩
    rw [sum_split hN]
    have e1 : ∀ j : Fin n, (if hj : (Br.iC hN j).val < n then c ⟨(Br.iC hN j).val, hj⟩ else d) = c j :=
      fun j => dif_pos j.2
    have e2 : (if hj : (Br.iL hN).val < n then c ⟨(Br.iL hN).val, hj⟩ else d) = d := dif_neg (lt_irrefl n)
    simp only [e1, e2]
    rcases cases_idx hN a with rfl | ⟨a, rfl⟩
    · simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add, hd]
    · simp only [h1, (h2 _).1, mul_zero, add_zero]
      exact hc a

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem localization_sumLat_le {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K))
    (M M₂ : Submodule (𝓞 K) (Fin n → K)) (t : K) (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M₂) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M t) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M₂ t) := by
  rintro x ⟨s, hs, hx1, c, hc⟩
  have h0 : (fun a => (s • x) (Br.iC hN a)) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx1⟩
  obtain ⟨u, hu, hux⟩ := h h0
  refine ⟨u * s, Submonoid.mul_mem _ hu hs, ?_⟩
  rw [mul_smul, mem_sumLat]
  refine ⟨hux, u * c, ?_⟩
  rw [Pi.smul_apply, hc, Algebra.smul_def]
  push_cast
  exact (mul_assoc _ _ _).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isBasisAt_block : ∀ (K : Type) [Field K] [NumberField K] (N n : ℕ) (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (t : K) (B : GL (Fin n) K) (B' : GL (Fin N) K), IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t → IsBasisAt w M B → IsBasisAt w (Br.sumLat hN M t) B' := by
  intro K _ _ N n hN w M t B B' hB h
  unfold IsBasisAt at h ⊢
  rw [colLat_block hN t B B' hB]
  exact le_antisymm (localization_sumLat_le hN w _ _ t h.le) (localization_sumLat_le hN w _ _ t h.ge)

end GlobalTheory.BranchBasis
