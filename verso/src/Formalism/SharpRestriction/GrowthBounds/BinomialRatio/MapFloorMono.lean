import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SrcHalf

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
