import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem reindex_finCongr_self {n : ℕ} {α : Type} (h : n = n) (A : Matrix (Fin n) (Fin n) α) :
    Matrix.reindex (finCongr h) (finCongr h) A = A := by
  ext a b
  rfl

/- English proof (translation)
Introduce `D H Dw l Xo c σ V r C hC h k`. Establish `hr` using `C.hr`. Substitute `hr` using the available equality. Take `⟨hA, -, hL⟩` from `GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf`. Establish `hG : (C.M.X k).Gm = -V.gramᵀ`.

Rewrite using `[(hC.modelW k).1, reindex_finCongr_self]`. Establish `hfr : ∀ u (τ : (C.M.X k).Ψ), mat (C.fr u k) τ = archM V (C.θ τ.1) u * C.x₀ τ.1` using `fun u τ => rfl`. Establish `hext : ∀ x y : Frame (C.M.X k).Ψ V.rank, (∀ τ, mat x τ = mat y τ) → x = y` using `fun x y hxy => funext fun τ => hxy τ`. Take `⟨-, h2, h3⟩` from `GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm`. Take `⟨-, h4⟩` from `GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm`.

Establish `horth : ∀ u (τ : (C.M.X k).Ψ), gram τ.1 (C.M.X k).Gm (mat (C.fr u k) τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)`. Introduce `u τ`. Rewrite using `[hfr, h3 τ.1 _ _ (by rw [hG]; exact (hA τ.1).2.2.2.2 u)]`. Conclude with `hC.orth k τ.1 τ.2`. Use `⟨horth h, (h2 _ (horth h)).1, (h2 _ (horth h)).2, ?_, fun u hu => ?_, fun u => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Conclude with `(hA τ.1).2.2.2.1.matrix_mul (continuous_const (y := C.x₀ τ.1))`. Use `hext _ _ fun τ => ?_` and prove the remaining obligations. Rewrite using `[hfr, hfr, (hA τ.1).2.1, (hA τ.1).2.2.1 u hu, mul_one]`. Use `hext _ _ fun τ => ?_` and prove the remaining obligations.

Establish `hd : IsUnit (C.x₀ τ.1).det`. Use `((h2 _ (horth 1)).1 τ).1` as an intermediate fact. Rewrite `this` using `[hfr, (hA τ.1).1, one_mul]`. Conclude with `isUnit_iff_ne_zero.2 this`. Use `show _ = mat (C.fr h k) τ * ((mat (C.fr 1 k) τ)⁻¹ * archM V (C.θ τ.1) u * mat (C.fr 1 k) τ)`.

Rewrite using `[hfr, hfr, hfr, (hA τ.1).2.1, (hA τ.1).1, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]`. Establish `hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ (C.M.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD`. Introduce `τ`. Rewrite using `[(hC.base.type k).2 τ, hC.iota.rt, hC.iota.rt0]`. Establish `hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (C.M.X k).Ψ, uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x ⟨τ, hτ⟩ = u * C.x₀ τ`.

Introduce `τ`. Distinguish the cases in `hτ : τ ∈ (C.M.X k).Ψ`. Take `⟨u, hu⟩` from `h4 τ (C.x₀ τ) (mat x ⟨τ, hτ⟩) (hC.orth k τ hτ) ((hx ⟨τ, hτ⟩).trans (hC.orth k τ hτ).symm)`. Rewrite `hu` using `[hG]`. Conclude with `⟨u, fun _ => hu⟩`.

Conclude with `⟨1, fun h' => absurd h' hτ⟩`. Use `choose u hu using hex`. Take `⟨a, ha, hau⟩` from `hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1`. Use `⟨a, ha, hext _ _ fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[hfr, hau τ.1 ((hmem τ.1).1 τ.2)]`.

Conclude with `((hu τ.1 τ.2).2).symm`.
-/
theorem fr_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  intro D H Dw l Xo c σ V r C hC h k
  have hr := C.hr
  subst hr
  obtain ⟨hA, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf
  have hG : (C.M.X k).Gm = -V.gramᵀ := by
    rw [(hC.modelW k).1, reindex_finCongr_self]
  have hfr : ∀ u (τ : (C.M.X k).Ψ), mat (C.fr u k) τ = archM V (C.θ τ.1) u * C.x₀ τ.1 := fun u τ => rfl
  have hext : ∀ x y : Frame (C.M.X k).Ψ V.rank, (∀ τ, mat x τ = mat y τ) → x = y :=
    fun x y hxy => funext fun τ => hxy τ
  obtain ⟨-, h2, h3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  have horth : ∀ u (τ : (C.M.X k).Ψ), gram τ.1 (C.M.X k).Gm (mat (C.fr u k) τ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ) := by
    intro u τ
    rw [hfr, h3 τ.1 _ _ (by rw [hG]; exact (hA τ.1).2.2.2.2 u)]
    exact hC.orth k τ.1 τ.2
  refine ⟨horth h, (h2 _ (horth h)).1, (h2 _ (horth h)).2, ?_, fun u hu => ?_, fun u => ?_, fun x hx => ?_⟩
  · refine continuous_pi fun τ => ?_
    exact (hA τ.1).2.2.2.1.matrix_mul (continuous_const (y := C.x₀ τ.1))
  · refine hext _ _ fun τ => ?_
    rw [hfr, hfr, (hA τ.1).2.1, (hA τ.1).2.2.1 u hu, mul_one]
  · refine hext _ _ fun τ => ?_
    have hd : IsUnit (C.x₀ τ.1).det := by
      have := ((h2 _ (horth 1)).1 τ).1
      rw [hfr, (hA τ.1).1, one_mul] at this
      exact isUnit_iff_ne_zero.2 this
    show _ = mat (C.fr h k) τ * ((mat (C.fr 1 k) τ)⁻¹ * archM V (C.θ τ.1) u * mat (C.fr 1 k) τ)
    rw [hfr, hfr, hfr, (hA τ.1).2.1, (hA τ.1).1, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ (C.M.X k).Ψ ↔
        τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
      intro τ
      rw [(hC.base.type k).2 τ, hC.iota.rt, hC.iota.rt0]
    have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (C.M.X k).Ψ,
        uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x ⟨τ, hτ⟩ = u * C.x₀ τ := by
      intro τ
      by_cases hτ : τ ∈ (C.M.X k).Ψ
      · obtain ⟨u, hu⟩ := h4 τ (C.x₀ τ) (mat x ⟨τ, hτ⟩) (hC.orth k τ hτ)
          ((hx ⟨τ, hτ⟩).trans (hC.orth k τ hτ).symm)
        rw [hG] at hu
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' hτ⟩
    choose u hu using hex
    obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1
    refine ⟨a, ha, hext _ _ fun τ => ?_⟩
    rw [hfr, hau τ.1 ((hmem τ.1).1 τ.2)]
    exact ((hu τ.1 τ.2).2).symm

end GlobalTheory.Member
