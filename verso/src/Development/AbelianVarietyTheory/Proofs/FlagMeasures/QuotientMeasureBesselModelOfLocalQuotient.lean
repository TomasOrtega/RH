import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotTransport

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext a; split_ifs <;> norm_num`.
-/
lemma jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

/- English proof (translation)
Establish `hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1` using `jm_mul_self ε`. Establish `hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1`. Establish `: H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1`. Rewrite using `[← h3]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]`. Use `_ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`. Conclude with `mul_eq_one_comm.mp this`. Establish `hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hy, hHi]`. Establish `hdet : IsUnit y.det` using `Matrix.isUnit_det_of_left_inverse hl`. Establish `hyr : y * y⁻¹ = 1` using `Matrix.mul_nonsing_inv y hdet`. Establish `hyl : y⁻¹ * y = 1` using `Matrix.nonsing_inv_mul y hdet`.

Establish `hy' : (y⁻¹)ᴴ * H * y⁻¹ = H`. Combine the equalities or inequalities in the displayed calculation. Set `u : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨Q * y⁻¹ * Qi, Q * y * Qi, by`. Combine the equalities or inequalities in the displayed calculation. Use `by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu : u ∈ Formalism.REAL.UJ ε` using `by show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)`. Unfold `Formalism.REAL.inUJ`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']`. Use `_ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.

Conclude with `⟨⟨u, hu⟩, rfl⟩`.
-/
lemma exists_unit {n m : ℕ} (ε : Fin n → Bool) (H : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (h3 : Qᴴ * Formalism.REAL.Jm ε * Q = H)
    (y : Matrix (Fin m) (Fin m) ℂ) (hy : yᴴ * H * y = H) :
    ∃ g : Formalism.REAL.UJ ε, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Q * y⁻¹ * Qi := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := jm_mul_self ε
  have hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1 := by
    have : H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1 := by
      rw [← h3]
      calc Qᴴ * Formalism.REAL.Jm ε * Q * (Qi * Formalism.REAL.Jm ε * Qiᴴ)
          = Qᴴ * Formalism.REAL.Jm ε * (Q * Qi) * Formalism.REAL.Jm ε * Qiᴴ := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * Qiᴴ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    exact mul_eq_one_comm.mp this
  have hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1 := by
    calc (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = (Qi * Formalism.REAL.Jm ε * Qiᴴ) * (yᴴ * H * y) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, hHi]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  have hyr : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hdet
  have hyl : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hdet
  have hy' : (y⁻¹)ᴴ * H * y⁻¹ = H := by
    calc (y⁻¹)ᴴ * H * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * H * y) * y⁻¹ := by rw [hy]
      _ = (y * y⁻¹)ᴴ * H * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hyr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨Q * y⁻¹ * Qi, Q * y * Qi, by
      calc Q * y⁻¹ * Qi * (Q * y * Qi) = Q * (y⁻¹ * (Qi * Q) * y) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyl, Matrix.mul_one, h2],
     by
      calc Q * y * Qi * (Q * y⁻¹ * Qi) = Q * (y * (Qi * Q) * y⁻¹) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyr, Matrix.mul_one, h2]⟩
  have hu : u ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)
    unfold Formalism.REAL.inUJ
    calc (Q * y⁻¹ * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * y⁻¹ * Qi)
        = Qiᴴ * ((y⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * y⁻¹) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']
      _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨⟨u, hu⟩, rfl⟩

end GlobalTheory.QuotTransport

namespace GlobalTheory

open GlobalTheory.QuotTransport in

/- English proof (translation)
Introduce `D X θ C τ γ μ ν hμ hq f hf`. Use `haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩`. Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Take `⟨g, hg⟩` from `exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)`. Establish `h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M`.

Introduce `M`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Establish `hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I …`. Introduce `M`. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.one_mul]`.

Establish `hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h → ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ) (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ), Continuous (fun w => (Matrix.of.symm (A * uMat (h …` using `fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const`. Establish `hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))` using `(hcM (continuous_mul_left γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))`. Use `set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ`. Use `set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα`.

Use `set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ`. Establish `hφm : Measurable φ` using `(hcM continuous_id _ _).measurable`. Establish `hαm : Measurable α` using `(hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable`. Establish `hβm : Measurable β` using `hcβ.measurable`. Establish `hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)))` using `Continuous.matrix_mul continuous_snd continuous_fst`.

Establish `hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j))` using `hf.comp hpc.measurable`. Establish `hA : ∀ w, φ (w * g) = β (γ * w)`. Introduce `w`. Use `show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) = Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)`. Rewrite using `[inv_mul_cancel_left]`.

Use `congr 1`. Simplify using `only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j`. Introduce `y z`. Simplify using `only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, h2', hγ]`.

Both sides reduce to the same expression. Use `show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)`. Rewrite using `[lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun z => ?_` and prove the remaining obligations.

Establish `hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => f (fun i j => (Matrix.of s * Matrix.of (β z)) i j))` using `hj.comp measurable_prodMk_left`. Rewrite using `[lintegral_map hmz hαm]`. Simplify using `only [hB]`.
-/
theorem quotMeas_besselModel_of_quotLoc : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  intro D X θ C τ γ μ ν hμ hq f hf
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨g, hg⟩ := exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)
  have h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := by
    intro M; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul]
  have hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h →
      ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ)
        (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ),
      Continuous (fun w => (Matrix.of.symm (A * uMat (h w) * B) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const
  have hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (hcM (continuous_mul_left γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))
  set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ
  set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα
  set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ
  have hφm : Measurable φ := (hcM continuous_id _ _).measurable
  have hαm : Measurable α := (hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable
  have hβm : Measurable β := hcβ.measurable
  have hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))) :=
    Continuous.matrix_mul continuous_snd continuous_fst
  have hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j)) :=
    hf.comp hpc.measurable
  have hA : ∀ w, φ (w * g) = β (γ * w) := by
    intro w
    show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)
    rw [inv_mul_cancel_left]
    congr 1
    simp only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j := by
    intro y z
    simp only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc, h2', hγ]
    rfl
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s,
    f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)
  rw [lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]
  calc ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ)
      = ∫⁻ w, f (φ w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_map hf hφm
    _ = ∫⁻ w, f (φ (w * g)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        (lintegral_mul_right_eq_self (fun w => f (φ w)) g).symm
    _ = ∫⁻ w, f (β (γ * w)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by simp only [hA]
    _ = ∫⁻ w, f (β w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_mul_left_eq_self (fun w => f (β w)) γ
    _ = ∫⁻ z, ∫⁻ y, f (β (y * z)) ∂μ ∂ν := hq _ (hf.comp hβm)
    _ = ∫⁻ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (β z)) i j) ∂(μ.map α) ∂ν := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
            f (fun i j => (Matrix.of s * Matrix.of (β z)) i j)) := hj.comp measurable_prodMk_left
        rw [lintegral_map hmz hαm]
        simp only [hB]

end GlobalTheory
