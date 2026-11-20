import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem exists_trace_ne_zero {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hE.basis
  have h1 := hcon 1
  have h2 := hcon u
  simp only [one_mul, map_mul] at h1 h2
  have hta : τ a = -a := by linear_combination h1
  rw [hta] at h2
  obtain ⟨w', hw'⟩ := hu.exists_left_inv
  apply ha
  linear_combination w' * h2 - a * hw'

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_unit_norm (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V)
    (hV : Nontrivial V) : ∃ w : V, IsUnit (B.h w w) := by
  have key : ∀ w : V, B.h w w ≠ 0 → IsUnit (B.h w w) := fun w hw =>
    hE.fixedUnit _ (B.self_fixed hE.inv w) hw
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hex : ∃ w, B.h v w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (B.nondeg v hcon)
  obtain ⟨w, hvw⟩ := hex
  obtain ⟨c, hc⟩ := exists_trace_ne_zero hE hvw
  by_cases hww : B.h w w = 0
  · by_cases hvv : B.h v v = 0
    · refine ⟨w + c • v, key _ ?_⟩
      have expand : B.h (w + c • v) (w + c • v) = c * B.h v w + τ (c * B.h v w) := by
        rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_left, B.smul_right,
          B.smul_right, hww, hvv, B.symm v w, map_mul]
        ring
      rw [expand]
      exact hc
    · exact ⟨v, key v hvv⟩
  · exact ⟨w, key w hww⟩

end GlobalTheory.CompanionTheory.UnrDens
