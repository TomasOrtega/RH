import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ)` to `{ toFun := fun M => Matrix.of.symm M map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Conclude with `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`.
-/
theorem hasDerivAt_exp_entries (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (Matrix.of.symm X) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun M => Matrix.of.symm M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/- English proof (translation)
Establish `hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) = fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X)))`. Use function extensionality and compare the values at `t`. Establish `hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G`. Simplify using `using hX t`. Simplify using `using hFG _ hmem`.

Rewrite using `[hfun]`. Establish `hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X)))` using `(hF.differentiable (by simp)) _`. Establish `h` using `hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero]`. Conclude with `h`.
-/
theorem hasDerivAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    {F : (Fin n → Fin n → ℂ) → H} (hF : ContDiff ℝ ∞ F) (hFG : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) (Matrix.of.symm X)) 0 := by
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
      fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X))) := by
    funext t
    have hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G := by
      simpa using hX t
    simpa using hFG _ hmem
  rw [hfun]
  have hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X))) :=
    (hF.differentiable (by simp)) _
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)
  rw [zero_smul, NormedSpace.exp_zero] at h
  exact h

/- English proof (translation)
Take `⟨F, hF, hFG⟩` from `hv`. Conclude with `(hasDerivAt_orbit hF hFG hX).differentiableAt`.
-/
theorem differentiableAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
  obtain ⟨F, hF, hFG⟩ := hv
  exact (hasDerivAt_orbit hF hFG hX).differentiableAt

/- English proof (translation)
Introduce `n G H _ _ π hG _hrep u v hu hv X Y hX hY`. Establish `hXY : X + Y ∈ HCSS.lieOf G` using `(lieOf_isLieSubalgebra hG).1 X Y hX hY`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨F, hF, hFG⟩` from `hv`. Simplify using `only [dRep]`.

Rewrite using `[(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv, (hasDerivAt_orbit hF hFG hY).deriv]`. Conclude with `(fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add (Matrix.of.symm X) (Matrix.of.symm Y)`. Simplify using `only [dRep, map_add]`. Conclude with `deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)`. Introduce `c`.

Simplify using `only [dRep, map_smul]`. Conclude with `deriv_const_smul c (differentiableAt_orbit hv hX)`.
-/
theorem dRep_linear : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G),
    dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧
      ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  intro n G H _ _ π hG _hrep u v hu hv X Y hX hY
  have hXY : X + Y ∈ HCSS.lieOf G := (lieOf_isLieSubalgebra hG).1 X Y hX hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF, hFG⟩ := hv
    simp only [dRep]
    rw [(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv,
      (hasDerivAt_orbit hF hFG hY).deriv]
    exact (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add
      (Matrix.of.symm X) (Matrix.of.symm Y)
  · simp only [dRep, map_add]
    exact deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)
  · intro c
    simp only [dRep, map_smul]
    exact deriv_const_smul c (differentiableAt_orbit hv hX)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

end
