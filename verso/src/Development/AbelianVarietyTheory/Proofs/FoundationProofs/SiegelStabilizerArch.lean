import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
open scoped ComplexConjugate Matrix NNReal TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.UG GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.HgtArch

namespace GlobalTheory.Core.Rk.GraphGram

open Matrix

section Complex

variable {n : ℕ}

/- English proof (translation)
Use `set W := c * Z * cinv with hWdef`. Establish `hcc' : cinv * c = 1` using `mul_eq_one_comm.1 hcc`. Establish `hdc : c.det * cinv.det = 1` using `by rw [← det_mul, hcc, det_one]`. Establish `hWdet : W.det = Z.det`. Rewrite using `[hWdef, det_mul, det_mul]`.

Take the linear combination `Z.det * hdc`. Establish `hWc : W * c = c * Z` using `by rw [hWdef, Matrix.mul_assoc, hcc', Matrix.mul_one]`. Establish `e : aᴴ * cᴴ * (1 + Wᴴ * W) * c * a = cᴴ * c + cᴴ * c`. Rewrite using `[← e0]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = (Z * a)ᴴ * (cᴴ * c) * (Z * a) + aᴴ * (cᴴ * c) * a := by`. Rewrite using `[hWc, add_comm]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Establish `hd` using `congrArg det e`.

Rewrite `hd` using `[← two_smul ℂ (cᴴ * c), det_smul, det_mul, det_mul, det_mul, det_mul, det_mul, det_conjTranspose, det_conjTranspose]`. Simplify using `only [Fintype.card_fin] at hd`. Establish `hn` using `congrArg norm hd`. Simplify using `only [norm_mul, norm_star, norm_pow, RCLike.norm_ofNat] at hn`. Establish `hc0 : c.det ≠ 0` using `left_ne_zero_of_mul_eq_one hdc`.

Establish `hq : 0 < ‖c.det‖` using `norm_pos_iff.2 hc0`. Establish `h1 : ‖a.det‖ ^ 2 * ‖(1 + Wᴴ * W).det‖ = 2 ^ n`. Establish `: ‖a.det‖ ^ 2 * ‖(1 + Wᴴ * W).det‖ * (‖c.det‖ * ‖c.det‖) = 2 ^ n * (‖c.det‖ * ‖c.det‖)`. Rewrite using `[← hn]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_right_cancel₀ (by positivity) this`. Establish `hWh' : W * h = 1` using `hWh`. Establish `e2 : hᴴ * (1 + Wᴴ * W) * h = 1 + hᴴ * h`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = 1 + hᴴ * h := by rw [hWh', conjTranspose_one, Matrix.mul_one, add_comm]`. Establish `hdh : ‖h.det‖ = 1`. Use `congrArg (fun X => ‖X.det‖) hWh'` as an intermediate fact. Simplify using `only [det_mul, norm_mul, hWdet, hZ, one_mul, det_one, norm_one] at this`. Conclude with `this`.

Establish `e3` using `congrArg (fun X => ‖X.det‖) e2`. Simplify using `only [det_mul, det_conjTranspose, norm_mul, norm_star, hdh, one_mul, mul_one] at e3`. Rewrite using `[det_smul, norm_mul, norm_pow, norm_inv, Fintype.card_fin, det_one_add_mul_comm, ← e3, RCLike.norm_ofNat]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_det_sq_mul_gram (a Z c cinv h : Matrix (Fin n) (Fin n) ℂ) (hcc : c * cinv = 1) (hZ : ‖Z.det‖ = 1)
    (hWh : c * Z * cinv * h = 1)
    (e0 : (Z * a)ᴴ * (cᴴ * c) * (Z * a) + aᴴ * (cᴴ * c) * a = cᴴ * c + cᴴ * c) :
    ‖a.det‖ ^ 2 * ‖((2 : ℂ)⁻¹ • (1 + h * hᴴ)).det‖ = 1 := by
  set W := c * Z * cinv with hWdef
  have hcc' : cinv * c = 1 := mul_eq_one_comm.1 hcc
  have hdc : c.det * cinv.det = 1 := by rw [← det_mul, hcc, det_one]
  have hWdet : W.det = Z.det := by
    rw [hWdef, det_mul, det_mul]; linear_combination Z.det * hdc
  have hWc : W * c = c * Z := by rw [hWdef, Matrix.mul_assoc, hcc', Matrix.mul_one]
  have e : aᴴ * cᴴ * (1 + Wᴴ * W) * c * a = cᴴ * c + cᴴ * c := by
    rw [← e0]
    calc aᴴ * cᴴ * (1 + Wᴴ * W) * c * a = aᴴ * (cᴴ * c) * a + (W * c * a)ᴴ * (W * c * a) := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = (Z * a)ᴴ * (cᴴ * c) * (Z * a) + aᴴ * (cᴴ * c) * a := by
          rw [hWc, add_comm]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hd := congrArg det e
  rw [← two_smul ℂ (cᴴ * c), det_smul, det_mul, det_mul, det_mul, det_mul, det_mul, det_conjTranspose,
    det_conjTranspose] at hd
  simp only [Fintype.card_fin] at hd
  have hn := congrArg norm hd
  simp only [norm_mul, norm_star, norm_pow, RCLike.norm_ofNat] at hn
  have hc0 : c.det ≠ 0 := left_ne_zero_of_mul_eq_one hdc
  have hq : 0 < ‖c.det‖ := norm_pos_iff.2 hc0
  have h1 : ‖a.det‖ ^ 2 * ‖(1 + Wᴴ * W).det‖ = 2 ^ n := by
    have : ‖a.det‖ ^ 2 * ‖(1 + Wᴴ * W).det‖ * (‖c.det‖ * ‖c.det‖) = 2 ^ n * (‖c.det‖ * ‖c.det‖) := by
      rw [← hn]; ring
    exact mul_right_cancel₀ (by positivity) this
  have hWh' : W * h = 1 := hWh
  have e2 : hᴴ * (1 + Wᴴ * W) * h = 1 + hᴴ * h := by
    calc hᴴ * (1 + Wᴴ * W) * h = hᴴ * h + (W * h)ᴴ * (W * h) := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 + hᴴ * h := by rw [hWh', conjTranspose_one, Matrix.mul_one, add_comm]
  have hdh : ‖h.det‖ = 1 := by
    have := congrArg (fun X => ‖X.det‖) hWh'
    simp only [det_mul, norm_mul, hWdet, hZ, one_mul, det_one, norm_one] at this
    exact this
  have e3 := congrArg (fun X => ‖X.det‖) e2
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star, hdh, one_mul, mul_one] at e3
  rw [det_smul, norm_mul, norm_pow, norm_inv, Fintype.card_fin, det_one_add_mul_comm, ← e3, RCLike.norm_ofNat]
  calc ‖a.det‖ ^ 2 * ((2 : ℝ)⁻¹ ^ n * ‖(1 + Wᴴ * W).det‖)
      = (‖a.det‖ ^ 2 * ‖(1 + Wᴴ * W).det‖) * (2 : ℝ)⁻¹ ^ n := by ring
    _ = 1 := by rw [h1, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]

end Complex

section Place

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hc n J hJ Q h w τ b y p k hk e`. Establish `e' : k⁻¹ = ioH _ σ h (y⁻¹, 1) * p`. Establish `: k = (p : GArch σ Q w)⁻¹ * ioH _ σ h (y, 1)` using `by rw [e, inv_mul_cancel_left]`. Rewrite using `[this, _root_.mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]`. Establish `hk' : k⁻¹ ∈ KArch σ Q w b` using `inv_mem hk`.

Rewrite `hk'` using `[KArch, mem_stabArch]`. Use `set ρ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ`. Use `set P := (AdelicU.matHom w.Completion σ Q p).1`. Use `set Z := (AdelicU.matHom w.Completion σ J y⁻¹).1`. Use `set e2 := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))`.

Establish `hU : Formalism.UG.cT ρ (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) * (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) = 1`. Establish `h1 : Formalism.UG.cT ρ ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 * 1 * ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 = 1` using `hk'`. Rewrite `h1` using `[Matrix.mul_one, e', map_mul, matHom_ioH, ← map_inv, Prod.inv_mk]`. Simplify `h1` using `only [Units.val_mul, val_blkGL, map_one, Units.val_one, Subgroup.coe_mul]`. Establish `hU2` using `congrArg (fun X => X.submatrix e2 e2) hU`.

Simplify using `only [submatrix_mul_self_equiv, cT_submatrix, submatrix_blkMat, submatrix_one_equiv] at hU2`. Establish `hKD : KeepsDiag e2 P` using `mem_siegelOf.1 p.2`. Establish `key` using `diag_identity ρ Z b.1 (b⁻¹).1 (P.submatrix e2 e2) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hKD (by simpa [submatrix_mul_self_equiv, Matrix.mul_assoc] using hU2)`. Take `⟨φ, hφ⟩ : ∃ φ' : w.Completion ⊗[F] E →+* ℂ, φ' = infEmb τ` from `⟨_, rfl⟩`. Establish `hmd : ∀ X : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E), (X.map φ).det = φ X.det` using `fun X => (RingHom.map_det φ X).symm`.

Establish `key2` using `map_identity ρ φ (fun x => by rw [hφ]; exact (infEmb_sigR hc τ x).symm) _ _ _ key`. Use `set α := (P.submatrix e2 e2).toBlocks₁₁ + (P.submatrix e2 e2).toBlocks₁₂ with hα`. Establish `hZ : ‖(Z.map φ).det‖ = 1`. Establish `h1` using `abs_detH (ν := absEw F E w) (absEw_conjUnit σ w) hJ y⁻¹`. Rewrite `h1` using `[absEw_eq_sq hc τ, val_detH, ← hφ]`.

Establish `h2` using `congrArg (fun x : ℝ≥0 => (x : ℝ)) h1`. Simplify using `only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one] at h2`. Rewrite using `[hmd]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2`. Establish `hcc : (b⁻¹).1.map φ * b.1.map φ = 1`.

Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `hWh : (b⁻¹).1.map φ * Z.map φ * b.1.map φ * inFrame σ J τ b y = 1`. Rewrite using `[inFrame, ← hφ, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]`. Establish `hin : (b⁻¹).1 * Z * b.1 * (b⁻¹ * AdelicU.matHom w.Completion σ J y * b).1 = 1`. Establish `: (b⁻¹ * AdelicU.matHom w.Completion σ J y⁻¹ * b * (b⁻¹ * AdelicU.matHom w.Completion σ J y * b)) = 1`.

Rewrite using `[map_inv]`. Use `group`. Simplify `congrArg Units.val this` using `only [Units.val_mul, Units.val_one]`. Rewrite using `[hin, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `hmain` using `norm_det_sq_mul_gram (α.map φ) (Z.map φ) ((b⁻¹).1.map φ) (b.1.map φ) (inFrame σ J τ b y) hcc hZ hWh key2`.

Rewrite using `[val_aOf, ← hφ]`. Express the relevant statement in the definitionally equal form `‖φ α.det‖ ^ 2 * _ = 1`. Rewrite using `[← hmd]`. Conclude with `hmain`.
-/
theorem normSq_aH_mul_gramDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (h : Q = dblGram finSumFinEquiv J) (w : InfinitePlace F)
      (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) (p : siegelH w.Completion σ Q)
      (k : GArch σ Q w), k ∈ KArch σ Q w b → ioH w.Completion σ h (g, 1) = p * k →
      ‖infEmb τ (aH w.Completion σ Q p).1‖ ^ 2 *
        ‖((2 : ℂ)⁻¹ • (1 + inFrame σ J τ b g * (inFrame σ J τ b g)ᴴ)).det‖ = 1 := by
  intro F E _ _ _ _ _ σ hc n J hJ Q h w τ b y p k hk e
  classical
  have e' : k⁻¹ = ioH _ σ h (y⁻¹, 1) * p := by
    have : k = (p : GArch σ Q w)⁻¹ * ioH _ σ h (y, 1) := by rw [e, inv_mul_cancel_left]
    rw [this, _root_.mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have hk' : k⁻¹ ∈ KArch σ Q w b := inv_mem hk
  rw [KArch, mem_stabArch] at hk'
  set ρ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ
  set P := (AdelicU.matHom w.Completion σ Q p).1
  set Z := (AdelicU.matHom w.Completion σ J y⁻¹).1
  set e2 := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
  have hU : Formalism.UG.cT ρ (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) *
      (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) = 1 := by
    have h1 : Formalism.UG.cT ρ ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 * 1 *
        ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 = 1 := hk'
    rw [Matrix.mul_one, e', map_mul, matHom_ioH, ← map_inv, Prod.inv_mk] at h1
    simpa only [Units.val_mul, val_blkGL, map_one, Units.val_one, Subgroup.coe_mul] using h1
  have hU2 := congrArg (fun X => X.submatrix e2 e2) hU
  simp only [submatrix_mul_self_equiv, cT_submatrix, submatrix_blkMat, submatrix_one_equiv] at hU2
  have hKD : KeepsDiag e2 P := mem_siegelOf.1 p.2
  have key := diag_identity ρ Z b.1 (b⁻¹).1 (P.submatrix e2 e2) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    hKD (by simpa [submatrix_mul_self_equiv, Matrix.mul_assoc] using hU2)
  obtain ⟨φ, hφ⟩ : ∃ φ' : w.Completion ⊗[F] E →+* ℂ, φ' = infEmb τ := ⟨_, rfl⟩
  have hmd : ∀ X : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E), (X.map φ).det = φ X.det :=
    fun X => (RingHom.map_det φ X).symm
  have key2 := map_identity ρ φ (fun x => by rw [hφ]; exact (infEmb_sigR hc τ x).symm) _ _ _ key
  set α := (P.submatrix e2 e2).toBlocks₁₁ + (P.submatrix e2 e2).toBlocks₁₂ with hα
  have hZ : ‖(Z.map φ).det‖ = 1 := by
    have h1 := abs_detH (ν := absEw F E w) (absEw_conjUnit σ w) hJ y⁻¹
    rw [absEw_eq_sq hc τ, val_detH, ← hφ] at h1
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
    simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one] at h2
    rw [hmd]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hcc : (b⁻¹).1.map φ * b.1.map φ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hWh : (b⁻¹).1.map φ * Z.map φ * b.1.map φ * inFrame σ J τ b y = 1 := by
    rw [inFrame, ← hφ, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    have hin : (b⁻¹).1 * Z * b.1 * (b⁻¹ * AdelicU.matHom w.Completion σ J y * b).1 = 1 := by
      have : (b⁻¹ * AdelicU.matHom w.Completion σ J y⁻¹ * b * (b⁻¹ * AdelicU.matHom w.Completion σ J y * b)) = 1 := by
        rw [map_inv]; group
      simpa only [Units.val_mul, Units.val_one] using congrArg Units.val this
    rw [hin, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hmain := norm_det_sq_mul_gram (α.map φ) (Z.map φ) ((b⁻¹).1.map φ) (b.1.map φ) (inFrame σ J τ b y) hcc hZ hWh key2
  rw [val_aOf, ← hφ]
  change ‖φ α.det‖ ^ 2 * _ = 1
  rw [← hmd]
  exact hmain

end Place

end GlobalTheory.Core.Rk.GraphGram
