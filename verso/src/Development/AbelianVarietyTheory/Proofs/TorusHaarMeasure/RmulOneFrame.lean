import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ProperDiscontinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) (τ : Ψ) : mat (oneFrame Ψ r) τ = 1 := rfl

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Introduce `τ`. Use `⟨by rw [mat_oneFrame]; simp, fun a c h => ?_⟩` and prove the remaining obligations. Conclude with `Matrix.one_apply_ne (ne_of_gt h)`.
-/
theorem oneFrame_mem (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneFrame Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨by rw [mat_oneFrame]; simp, fun a c h => ?_⟩
  exact Matrix.one_apply_ne (ne_of_gt h)

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show mat x τ * mat (oneFrame Ψ r) τ = _`. Rewrite using `[mat_oneFrame, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem rmul_oneFrame {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    rmul x (oneFrame Ψ r) = x := by
  funext τ
  show mat x τ * mat (oneFrame Ψ r) τ = _
  rw [mat_oneFrame, Matrix.mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = _`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem lact_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = _
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

/- English proof (translation)
Introduce `hinv hbd hfin r X x hx x' hx'`. Establish `hO` using `FourierCoefficientDomain.isOpen_dom X`. Take `⟨K, hK, hKd, hKc⟩` from `local_compact_nhds (hO.mem_nhds hx)`. Take `⟨K', hK', hKd', hKc'⟩` from `local_compact_nhds (hO.mem_nhds hx')`. Take `⟨c, C, hc, hb⟩` from `hbd r X (K ∪ K') (hKc.union hKc') (Set.union_subset hKd hKd')`.

Use `⟨K, hK, K', hK', (hfin r X (Real.sqrt (C / c))).subset ?_⟩` and prove the remaining obligations. Introduce and unpack `γ ⟨hγ, u, hu, u', hu', b, hbB, he⟩`. Use `⟨X.Γ_stab γ hγ, fun τ i j => ?_⟩` and prove the remaining obligations. Use `set M : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hM`. Use `set v : Fin r → ℂ := Pi.single j 1 with hv`.

Establish `h1` using `(hinv r X γ (X.Γ_stab γ hγ) u (hKd hu) _ (oneFrame_mem X.Ψ r)).2 τ v`. Rewrite `h1` using `[rmul_oneFrame, he]`. Establish `h2` using `(hinv r X 1 (X.Γ_stab 1 X.Γ.one_mem) u' (hKd' hu') b hbB).2 τ (M.mulVec v)`. Rewrite `h2` using `[lact_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Establish `h3` using `(hb u' (Or.inr hu') τ (M.mulVec v)).1`.

Establish `h4` using `(hb u (Or.inl hu) τ v).2`. Establish `hv1 : ‖v‖ = 1` using `by rw [hv, Pi.norm_single, norm_one]`. Rewrite `h4` using `[hv1]`. Establish `h5 : c * ‖M.mulVec v‖ ^ 2 ≤ C`. Establish `: X.maj u' τ (M.mulVec v) = X.maj u τ v` using `h2.symm.trans h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : ‖M.mulVec v‖ ≤ Real.sqrt (C / c)`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Rewrite using `[le_div_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h7 : M.mulVec v i = τ.1 ((γ : Matrix (Fin r) (Fin r) E) i j)`. Simplify using `[hv, hM]`. Rewrite using `[← h7]`. Conclude with `(norm_le_pi_norm _ i).trans h6`.
-/
theorem propDisc :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2) → (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite) → (∀ (r : ℕ) (X : Data E r), PropDisc X) := by
  intro hinv hbd hfin r X x hx x' hx'
  have hO := FourierCoefficientDomain.isOpen_dom X
  obtain ⟨K, hK, hKd, hKc⟩ := local_compact_nhds (hO.mem_nhds hx)
  obtain ⟨K', hK', hKd', hKc'⟩ := local_compact_nhds (hO.mem_nhds hx')
  obtain ⟨c, C, hc, hb⟩ := hbd r X (K ∪ K') (hKc.union hKc') (Set.union_subset hKd hKd')
  refine ⟨K, hK, K', hK', (hfin r X (Real.sqrt (C / c))).subset ?_⟩
  rintro γ ⟨hγ, u, hu, u', hu', b, hbB, he⟩
  refine ⟨X.Γ_stab γ hγ, fun τ i j => ?_⟩
  set M : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hM
  set v : Fin r → ℂ := Pi.single j 1 with hv
  have h1 := (hinv r X γ (X.Γ_stab γ hγ) u (hKd hu) _ (oneFrame_mem X.Ψ r)).2 τ v
  rw [rmul_oneFrame, he] at h1
  have h2 := (hinv r X 1 (X.Γ_stab 1 X.Γ.one_mem) u' (hKd' hu') b hbB).2 τ (M.mulVec v)
  rw [lact_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h2
  have h3 := (hb u' (Or.inr hu') τ (M.mulVec v)).1
  have h4 := (hb u (Or.inl hu) τ v).2
  have hv1 : ‖v‖ = 1 := by rw [hv, Pi.norm_single, norm_one]
  rw [hv1] at h4
  have h5 : c * ‖M.mulVec v‖ ^ 2 ≤ C := by
    have : X.maj u' τ (M.mulVec v) = X.maj u τ v := h2.symm.trans h1
    linarith
  have h6 : ‖M.mulVec v‖ ≤ Real.sqrt (C / c) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    linarith
  have h7 : M.mulVec v i = τ.1 ((γ : Matrix (Fin r) (Fin r) E) i j) := by
    simp [hv, hM]
  rw [← h7]
  exact (norm_le_pi_norm _ i).trans h6

end GlobalTheory.ProperDiscontinuity
