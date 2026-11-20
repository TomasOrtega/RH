import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pin4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

include hU in

/- English proof (translation)
Rewrite using `[hPP Xo c σ r U hU k x W Wu hu a]`. Take `⟨n, hn⟩ : ∃ n : ℤ, n = (W.F.Di (W.ik k)).EF a (H.w0 • a)` from `⟨_, rfl⟩`. Rewrite using `[← hn]`. Establish `hv` using `(W.φ k a).2`. Establish `hsm : ((H.w0 : E) • ((W.φ k a : (U.X k).Λ) : Fin r → E)) = ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E)`.

Rewrite using `[LinearEquiv.map_smul, Submodule.coe_smul]`. Both sides reduce to the same expression. Establish `he` using `A.eps_eq _ hv`. Rewrite `he` using `[hw, hsm, A.im_eq _ hv _ (W.φ k (H.w0 • a)).2]`. Take `⟨q, hq⟩ : ∃ q : ℚ, q = Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E) ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E))` from `⟨_, rfl⟩`.

Rewrite `he` using `[← hq]`. Establish `hi` using `W.isom k a (H.w0 • a)`. Rewrite `hi` using `[neg_mul, map_neg, ← hq, ← hn]`. Establish `hqr : (q : ℝ) = -(n : ℝ)`. Use `congrArg (fun t : ℚ => (t : ℝ)) hi` as an intermediate fact.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : Real.cos (Real.pi * (A.sg * (q : ℝ))) = (-1 : ℝ) ^ n`. Rewrite using `[hqr]`. Apply the tactic sequence `rcases A.sg_pm with h | h <;> rw [h]`.

Rewrite using `[show Real.pi * (1 * -(n : ℝ)) = -((n : ℝ) * Real.pi) by ring, Real.cos_neg, Real.cos_int_mul_pi]`. Rewrite using `[show Real.pi * (-1 * -(n : ℝ)) = (n : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]`. Rewrite `he` using `[hc]`. Establish `hC` using `congrArg (fun t : ℝ => (t : ℂ)) he`. Move the coercions through the operations in `at hC`.

Conclude with `hC`.
-/
theorem pin4 (hPP : PPSemicharSt) (Wu : UnitAt W) (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1)
    (hw : A.w0 = H.w0) (a : (W.F.Di (W.ik k)).La) :
    ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a) := by
  rw [hPP Xo c σ r U hU k x W Wu hu a]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (W.F.Di (W.ik k)).EF a (H.w0 • a) := ⟨_, rfl⟩
  rw [← hn]
  have hv := (W.φ k a).2
  have hsm : ((H.w0 : E) • ((W.φ k a : (U.X k).Λ) : Fin r → E)) =
      ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E) := by
    rw [LinearEquiv.map_smul, Submodule.coe_smul]
    rfl
  have he := A.eps_eq _ hv
  rw [hw, hsm, A.im_eq _ hv _ (W.φ k (H.w0 • a)).2] at he
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm
      ((W.φ k a : (U.X k).Λ) : Fin r → E) ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E)) := ⟨_, rfl⟩
  rw [← hq] at he
  have hi := W.isom k a (H.w0 • a)
  rw [neg_mul, map_neg, ← hq, ← hn] at hi
  have hqr : (q : ℝ) = -(n : ℝ) := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hi
    push_cast at this
    linarith
  have hc : Real.cos (Real.pi * (A.sg * (q : ℝ))) = (-1 : ℝ) ^ n := by
    rw [hqr]
    rcases A.sg_pm with h | h <;> rw [h]
    · rw [show Real.pi * (1 * -(n : ℝ)) = -((n : ℝ) * Real.pi) by ring, Real.cos_neg, Real.cos_int_mul_pi]
    · rw [show Real.pi * (-1 * -(n : ℝ)) = (n : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]
  rw [hc] at he
  have hC := congrArg (fun t : ℝ => (t : ℂ)) he
  push_cast at hC
  exact hC

end Pin4

end ReciprocityTheory.ChartRestriction.G.PullbackSections
