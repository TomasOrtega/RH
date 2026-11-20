import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PosH (φ : V → V → ℂ) : Prop where
  add : ∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂
  smul : ∀ v w (r : ℂ), φ v (r • w) = r * φ v w
  herm : ∀ v w, φ w v = star (φ v w)
  pos : ∀ v, v ≠ 0 → 0 < (φ v v).re

variable {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

/- English proof (translation)
Use `h.smul v 0 0` as an intermediate fact. Simplify using `using this`.
-/
theorem zero_right (v : V) : φ v 0 = 0 := by
  have := h.smul v 0 0
  simpa using this

/- English proof (translation)
Rewrite using `[h.herm v 0, h.zero_right, star_zero]`.
-/
theorem zero_left (v : V) : φ 0 v = 0 := by
  rw [h.herm v 0, h.zero_right, star_zero]

/- English proof (translation)
Rewrite using `[h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]`.
-/
theorem add_left (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by
  rw [h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]

/- English proof (translation)
Rewrite using `[h.herm w (r • v), h.smul, star_mul', ← h.herm w v]`.
-/
theorem smul_left (v w : V) (r : ℂ) : φ (r • v) w = star r * φ v w := by
  rw [h.herm w (r • v), h.smul, star_mul', ← h.herm w v]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h.zero_left]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]`.
-/
theorem sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `h.pos v hne` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `at this`.
-/
theorem definite (v : V) (hv : φ v v = 0) : v = 0 := by
  by_contra hne
  have := h.pos v hne
  rw [hv] at this
  simp at this

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using `[h.zero_right]`. Conclude with `(h.pos v hv).le`.
-/
theorem re_nonneg (v : V) : 0 ≤ (φ v v).re := by
  by_cases hv : v = 0
  · subst hv; simp [h.zero_right]
  · exact (h.pos v hv).le

def perp (W : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ w ∈ W, φ w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [h.add, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => h.zero_right w
  smul_mem' := by
    intro r v hv w hw
    rw [h.smul, hv w hw, mul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_perp (W : Submodule ℂ V) (v : V) : v ∈ h.perp W ↔ ∀ w ∈ W, φ w v = 0 := Iff.rfl

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Break down `Submodule.mem_inf.1 hv with ⟨h1, h2⟩` into its components or cases. Conclude with `(Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))`.
-/
theorem inf_perp (W : Submodule ℂ V) : W ⊓ h.perp W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases Submodule.mem_inf.1 hv with ⟨h1, h2⟩
  exact (Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))

end PosH

end CoreA

end PositivityTheory.Rg.Sw.LC
