import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutLieLast

/- English proof (translation)
Unfold `RestTerms.smallPowerSum`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `he : restLastEquiv j k ⟨j + b.val, by have` using `b.isLt; omega⟩ = Sum.inr b := by`. Establish `: (finCongr (Nat.add_comm k j)) ⟨j + b.val, by have` using `b.isLt; omega⟩ = Fin.natAdd j b := Fin.ext rfl`.

Simplify using `only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]`. Simplify using `[restTransport, restRename, RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, he]`.
-/
theorem transport_smallPowerSum (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallPowerSum f k j .last m τ) =
      ∑ b : Fin k, X (τ, Sum.inr b) ^ m := by
  unfold RestTerms.smallPowerSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he : restLastEquiv j k ⟨j + b.val, by have := b.isLt; omega⟩ = Sum.inr b := by
    have : (finCongr (Nat.add_comm k j)) ⟨j + b.val, by have := b.isLt; omega⟩ = Fin.natAdd j b :=
      Fin.ext rfl
    simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]
  simp [restTransport, restRename, RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign,
    he]

end RestCutLieLast

/- English proof (translation)
Introduce `f j k _ m σ`. Take `⟨τ, b⟩` from `σ`. Consider the cases of `b with`. Consider the case `true`. Use `⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩` and prove the remaining obligations.

Rewrite using `[RestCutLieLast.transport_smallPowerSum]`. Simplify using `[lieClass]`. Consider the case `false`. Use `⟨-1, 1, Or.inr rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[RestCutLieLast.transport_smallPowerSum]`.

Simplify using `only [lieClass, rootPsum, Fintype.sum_sum_type, map_one, one_mul]`. Simplify using the standard rewrite rules.
-/
theorem RestCutLieLast.proof : RestCutLieLast.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  cases b with
  | true =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp [lieClass]
  | false =>
    refine ⟨-1, 1, Or.inr rfl, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type, map_one, one_mul]
    simp

end

end GroundTheory.Heights₂.Heights
