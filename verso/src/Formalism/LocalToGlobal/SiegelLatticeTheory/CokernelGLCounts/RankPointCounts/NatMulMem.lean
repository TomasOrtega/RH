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
Unfold `selfP upperM at *`. Rewrite using `[qbar_qbar]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `: qbar w q = q` using `h.symm`. Rewrite `hu` using `[this]`.

Conclude with `lt_irrefl _ hu`. Conclude with `lt_asymm hu h`.
-/
theorem upper_qbar {q : FreeE w} (hu : upperM w q) : ¬ selfP w (qbar w q) ∧ ¬ upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : qbar w q = q := h.symm
    rw [this] at hu; exact lt_irrefl _ hu
  · exact lt_asymm hu h

/- English proof (translation)
Unfold `selfP upperM at *`. Rewrite using `[qbar_qbar]`. Break down `lt_or_eq_of_le (not_lt.1 hu) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Apply `hs` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2 : pinv w q.1.2 = q.1.1` using `h.symm`. Establish `h3 : q.1.2 = pinv w q.1.1` using `by rw [← h2, pinv_pinv]`. Simplify using `only [qbar]`.

Rewrite using `[h2, ← h3]`.
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
Unfold `hgt`. Use `q.1.2.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem hgt_le (q : FreeE w) : hgt w q ≤ D.R.rS := by
  unfold hgt; have := q.1.2.isLt; omega

section Main

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

/- English proof (translation)
The claim follows from `sgm_cases q.1.1 q.1.2`.
-/
theorem sgq_cases (q : FreeE w) : sgq w q = (1 : D.host.E) ∨ sgq w q = -1 := sgm_cases q.1.1 q.1.2

/- English proof (translation)
Apply the tactic sequence `rcases sgq_cases w q with e | e <;> rw [e] <;> ring`.
-/
theorem sgq_sq (q : FreeE w) : sgq w q * sgq w q = (1 : D.host.E) := by
  rcases sgq_cases w q with e | e <;> rw [e] <;> ring

include hA in
/- English proof (translation)
Use `dd_conj δ M hA hk hx` as an intermediate fact. Break down `sgq_cases w q with e | e` into its components or cases. Rewrite using `[e, one_mul]`. Conclude with `this`. Rewrite using `[e, neg_one_mul]`.

Conclude with `(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this`.
-/
theorem sg_dd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ ddPow D h) :
    sgq w q * D.conjF x ∈ ddPow D h := by
  have := dd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

include hA in
/- English proof (translation)
Use `qd_conj δ M hA hk hx` as an intermediate fact. Break down `sgq_cases w q with e | e` into its components or cases. Rewrite using `[e, one_mul]`. Conclude with `this`. Rewrite using `[e, neg_one_mul]`.

Conclude with `(qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this`.
-/
theorem sg_qd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ qdPow D h) :
    sgq w q * D.conjF x ∈ qdPow D h := by
  have := qd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

/- English proof (translation)
Rewrite using `[qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]`. Conclude with `hx`.
-/
theorem gS_mul_qd (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : ((gS D : ℕ) : D.host.E) * x ∈ qdPow D h := by
  rw [qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]; exact hx

/- English proof (translation)
Rewrite using `[← nsmul_eq_mul]`. Conclude with `(I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m`.
-/
theorem nat_mul_mem (I : FI D) (m : ℕ) {x : D.host.E} (hx : x ∈ I) : (m : D.host.E) * x ∈ I := by
  rw [← nsmul_eq_mul]; exact (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m

/- English proof (translation)
Substitute `hE` using the available equality. Simplify using `only [map_sub, map_mul, map_natCast, Formalism.MainNotions.BridgeLemma.conjF_inv, hsc]`. Take the linear combination `(1 - (m : D.host.E)) * (c - y) * hs`.
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
