import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
import GroundTheory.GlobalFields.TateThesis.LatticePoisson
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace PGaussPoissonBound

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]`. Simplify using `[dotProduct, sq]`.
-/
theorem norm_toLp_sq {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

end PGaussPoissonBound

open PGaussPoissonBound in

/- English proof (translation)
Introduce `g B hB a`. Take `⟨hdisc, hlat⟩` from `hL g B hB`. Establish `: DiscreteTopology (gaussLattice B)` using `hdisc`. Establish `: IsZLattice ℝ (gaussLattice B)` using `hlat`. Take `⟨hmem, hsurj, hinj⟩` from `hK g B hB`.

Set `E` to `EuclideanSpace ℝ (Fin g)`. Set `L` to `gaussLattice B`. Set `φ : (Fin g → ℤ) ≃ L` to `Equiv.ofBijective (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩) ⟨fun k k' h => hinj (by`. Use `congrArg (fun x : L => WithLp.ofLp (x : E)) h` as an intermediate fact. Simplify using `using this),`.

Use `fun x => by`. Take `⟨k, hk⟩` from `hsurj x x.2`. Conclude with `⟨k, Subtype.ext hk.symm⟩⟩`. Set `G` to `GroundTheory.Global.gaussianSchwartz E`. Set `a' : E` to `WithLp.toLp 2 (B *ᵥ a)`.

Set `f : (Fin g → ℤ) → ℝ` to `fun k => Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))`. Establish `hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ)` using `fun k => by`. Establish `h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a))`. Rewrite using `[Matrix.mulVec_add]`. Both sides reduce to the same expression.

Rewrite using `[h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]`. Establish `hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k` using `fun k => by`. Rewrite using `[hG, Complex.norm_of_nonneg (Real.exp_pos _).le]`. Establish `hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun x => GroundTheory.Global.gaussianSchwartz_apply x`.

Establish `hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ)` using `fun μ => by`. Rewrite using `[hGfun]`. Conclude with `hF g μ`. Establish `hnD : ∀ μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2)` using `fun μ => by`. Rewrite using `[norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]`.

Establish `hsumf : Summable f`. Establish `h` using `(φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2 (GroundTheory.Global.lattice_summable_norm L G a')`. Conclude with `h.congr fun k => hnG k`. Establish `hsumD` using `GroundTheory.Global.dualLattice_summable_norm L G a'`. Establish `hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2)` using `hsumD.congr hnD`.

Use `⟨hsumf, hsumE, ?_⟩` and prove the remaining obligations. Establish `hP` using `GroundTheory.Global.lattice_poisson_summation L G a'`. Establish `hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ)`. Rewrite using `[← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]`. Conclude with `tsum_congr fun k => hG k`.

Rewrite `hP` using `[hlhs]`. Establish `hcov : ZLattice.covolume L = |B.det|` using `hV g B hB`. Establish `hcpos : 0 < ZLattice.covolume L` using `ZLattice.covolume_pos L volume`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]`.

Use `_ ≤ (ZLattice.covolume L)⁻¹ * ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le`. Use `_ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B), Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by`. Rewrite using `[hcov]`. Conclude with `congrArg _ (tsum_congr hnD)`.
-/
theorem GaussPoissonBound.proof (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by
  intro g B hB a
  obtain ⟨hdisc, hlat⟩ := hL g B hB
  have : DiscreteTopology (gaussLattice B) := hdisc
  have : IsZLattice ℝ (gaussLattice B) := hlat
  obtain ⟨hmem, hsurj, hinj⟩ := hK g B hB
  let E := EuclideanSpace ℝ (Fin g)
  let L := gaussLattice B
  let φ : (Fin g → ℤ) ≃ L := Equiv.ofBijective
    (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩)
    ⟨fun k k' h => hinj (by
        have := congrArg (fun x : L => WithLp.ofLp (x : E)) h
        simpa using this),
      fun x => by
        obtain ⟨k, hk⟩ := hsurj x x.2
        exact ⟨k, Subtype.ext hk.symm⟩⟩
  let G := GroundTheory.Global.gaussianSchwartz E
  let a' : E := WithLp.toLp 2 (B *ᵥ a)
  let f : (Fin g → ℤ) → ℝ := fun k =>
    Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))
  have hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ) := fun k => by
    have h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a)) := by
      rw [Matrix.mulVec_add]; rfl
    rw [h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]
  have hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k := fun k => by
    rw [hG, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
    funext fun x => GroundTheory.Global.gaussianSchwartz_apply x
  have hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ) := fun μ => by
    rw [hGfun]; exact hF g μ
  have hnD : ∀ μ : GroundTheory.Global.dualLattice L,
      ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2) := fun μ => by
    rw [norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]

  have hsumf : Summable f := by
    have h := (φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2
      (GroundTheory.Global.lattice_summable_norm L G a')
    exact h.congr fun k => hnG k

  have hsumD := GroundTheory.Global.dualLattice_summable_norm L G a'
  have hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2) :=
    hsumD.congr hnD
  refine ⟨hsumf, hsumE, ?_⟩

  have hP := GroundTheory.Global.lattice_poisson_summation L G a'
  have hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ) := by
    rw [← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]
    exact tsum_congr fun k => hG k
  rw [hlhs] at hP
  have hcov : ZLattice.covolume L = |B.det| := hV g B hB
  have hcpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  calc ∑' k, f k = ‖((∑' k, f k : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le)).symm
    _ = (ZLattice.covolume L)⁻¹ *
          ‖∑' μ : GroundTheory.Global.dualLattice L, 𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := by
        rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    _ ≤ (ZLattice.covolume L)⁻¹ *
          ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le
    _ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by
        rw [hcov]; exact congrArg _ (tsum_congr hnD)

end

end GroundTheory.Heights₂.Heights
