import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

/- English proof (translation)
Set `_ : NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Establish `hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X s`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ)` to `LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap`. Conclude with `(L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt`.
-/
theorem differentiableAt_entries_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)) s := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt

/- English proof (translation)
Introduce `n G H _ _ π hG hrep v hv X hX g hg`. Take `⟨F, hF, hFv⟩` from `hv`. Establish `hu : IsUnit g` using `hG.isUnit g hg`. Establish `hgi : g⁻¹ ∈ G` using `hG.inv_mem g hg`. Establish `hinv : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)`.

Establish `hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0`. Establish `he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) = F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)`. Use function extensionality and compare the values at `t`. Conclude with `hFv _ (hX t)`. Rewrite using `[he]`.

Conclude with `(hF.differentiable (by simp)).differentiableAt.comp 0 (differentiableAt_entries_exp_smul X 0)`. Establish `key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) = π g (π (NormedSpace.exp (t • X)) v)`. Introduce `t`. Establish `hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹`. Establish `: t • (g * X * g⁻¹) = g * (t • X) * g⁻¹`.

Simplify using `[Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[this, Matrix.exp_conj _ _ hu]`. Establish `hge : g * NormedSpace.exp (t • X) ∈ G` using `hG.mul_mem _ hg _ (hX t)`. Establish `h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) = (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g)` using `hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg`. Establish `h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X)`.

Rewrite using `[Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]`. Establish `h3` using `hrep.2 _ hg _ (hX t)`. Rewrite using `[hconj]`. Rewrite `h1` using `[h2, h3]`. Conclude with `(DFunLike.congr_fun h1 v).symm`.

Establish `h2` using `((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt`. Establish `h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 = π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0)`. Rewrite using `[funext key]`. Conclude with `h2.deriv`. Conclude with `h3.symm`.
-/
theorem dRep_equivariant : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  intro n G H _ _ π hG hrep v hv X hX g hg
  obtain ⟨F, hF, hFv⟩ := hv
  have hu : IsUnit g := hG.isUnit g hg
  have hgi : g⁻¹ ∈ G := hG.inv_mem g hg
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
    have he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
        F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ) := by
      funext t
      exact hFv _ (hX t)
    rw [he]
    exact (hF.differentiable (by simp)).differentiableAt.comp 0
      (differentiableAt_entries_exp_smul X 0)
  have key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) =
      π g (π (NormedSpace.exp (t • X)) v) := by
    intro t
    have hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹ := by
      have : t • (g * X * g⁻¹) = g * (t • X) * g⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, Matrix.exp_conj _ _ hu]
    have hge : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hg _ (hX t)
    have h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) =
        (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g) :=
      hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg
    have h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X) := by
      rw [Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]
    have h3 := hrep.2 _ hg _ (hX t)
    rw [hconj]
    rw [h2, h3] at h1
    exact (DFunLike.congr_fun h1 v).symm
  have h2 := ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 =
      π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0) := by
    rw [funext key]
    exact h2.deriv
  exact h3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
