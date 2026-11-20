import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgmPinvEq

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem upper_qbar {q : FreeE w} (hu : upperM w q) : ¬ selfP w (qbar w q) ∧ ¬ upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : qbar w q = q := h.symm
    rw [this] at hu; exact lt_irrefl _ hu
  · exact lt_asymm hu h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem lower_qbar {q : FreeE w} (hs : ¬ selfP w q) (hu : ¬ upperM w q) : upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  rcases lt_or_eq_of_le (not_lt.1 hu) with h | h
  · exact h
  · exfalso; apply hs
    apply Subtype.ext
    have h2 : pinv w q.1.2 = q.1.1 := h.symm
    have h3 : q.1.2 = pinv w q.1.1 := by rw [← h2, pinv_pinv]
    simp only [qbar]
    rw [h2, ← h3]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem hgt_le (q : FreeE w) : hgt w q ≤ D.R.rS := by
  unfold hgt; have := q.1.2.isLt; omega

section Main

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgq_cases (q : FreeE w) : sgq w q = (1 : D.host.E) ∨ sgq w q = -1 := sgm_cases q.1.1 q.1.2

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sgq_sq (q : FreeE w) : sgq w q * sgq w q = (1 : D.host.E) := by
  rcases sgq_cases w q with e | e <;> rw [e] <;> ring

include hA in
/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sg_dd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ ddPow D h) :
    sgq w q * D.conjF x ∈ ddPow D h := by
  have := dd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

include hA in
/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sg_qd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ qdPow D h) :
    sgq w q * D.conjF x ∈ qdPow D h := by
  have := qd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gS_mul_qd (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : ((gS D : ℕ) : D.host.E) * x ∈ qdPow D h := by
  rw [qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]; exact hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nat_mul_mem (I : FI D) (m : ℕ) {x : D.host.E} (hx : x ∈ I) : (m : D.host.E) * x ∈ I := by
  rw [← nsmul_eq_mul]; exact (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m

/- English proof (translation)
Substitute using the available equality. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem self_id (s y c E : D.host.E) (m : ℕ) (hs : s * s = 1) (hsc : D.conjF s = s)
    (hE : E = y - s * D.conjF (c - y)) :
    (y - (m : D.host.E) * c) + s * D.conjF (y - (m : D.host.E) * c) =
      E + (s * D.conjF E - E) - (m : D.host.E) * (s * D.conjF E - E) + (1 - 2 * (m : D.host.E)) * c := by
  subst hE
  simp only [map_sub, map_mul, map_natCast, Formalism.MainNotions.BridgeLemma.conjF_inv, hsc]
  linear_combination (1 - (m : D.host.E)) * (c - y) * hs

end Main

end Formalism.L2.SG.Pf.StabIntLat
