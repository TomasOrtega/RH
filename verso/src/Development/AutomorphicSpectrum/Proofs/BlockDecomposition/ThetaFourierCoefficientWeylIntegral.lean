import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.RCellInv

variable {D : D7} {t ρ : ℕ}

/- English proof (translation)
Simplify using `only [blk4]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem block_matrix_mul {n : ℕ} (a b c d a' b' c' d' : Mx D n n) :
    (blk4 a b c d * blk4 a' b' c' d' : Mx D (n + n) (n + n)) =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `only [mat, map_mul, Units.val_mul]`.
-/
theorem mat_mul_mat {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

/- English proof (translation)
Rewrite using `[adj, Matrix.trace_transpose]`. Conclude with `(AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm`.
-/
theorem trace_adj_eq {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  rw [adj, Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun b₀.2 i) j`. Simplify using `only [adj, Matrix.transpose_apply, Matrix.map_apply] at h ⊢`. Rewrite using `[GlobalTheory.DualPairCheck.cA_incA]`. Conclude with `congrArg (incA D) h`.
-/
theorem adj_gram (b₀ : HermE D ρ) : adj (b₀.1.map (incA D)) = b₀.1.map (incA D) := by
  ext i j
  have h := congrFun (congrFun b₀.2 i) j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply] at h ⊢
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg (incA D) h

/- English proof (translation)
Simplify using `only [pr, adj_mul, adj_adj, adj_gram, Matrix.mul_assoc]`.
-/
theorem adj_pr (b₀ : HermE D ρ) (x y : Mx D ρ t) : adj (pr b₀ x y) = pr b₀ y x := by
  simp only [pr, adj_mul, adj_adj, adj_gram, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [pr, adj_neg, Matrix.neg_mul]`.
-/
theorem pr_neg_left (b₀ : HermE D ρ) (x y : Mx D ρ t) : pr b₀ (-x) y = -pr b₀ x y := by
  simp only [pr, adj_neg, Matrix.neg_mul]

/- English proof (translation)
Rewrite using `[← adj_pr b₀ x y, trace_adj_eq]`. Conclude with `GlobalTheory.DualPairCheck.trace_cA _`.
-/
theorem trA_trace_pr_swap (b₀ : HermE D ρ) (x y : Mx D ρ t) :
    trA (Matrix.trace (pr b₀ y x)) = trA (Matrix.trace (pr b₀ x y)) := by
  rw [← adj_pr b₀ x y, trace_adj_eq]
  exact GlobalTheory.DualPairCheck.trace_cA _

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]`.
-/
theorem conj_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

/- English proof (translation)
Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]`.
-/
theorem det_neg_one (t : ℕ) :
    Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D)) =
      Units.map (incA D).toMonoidHom ((-1 : (D.host.E)ˣ) ^ t) := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]

/- English proof (translation)
Establish `h : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) ^ 2 = 1`. Rewrite using `[← map_pow, ← map_pow, neg_one_sq, map_one, map_one]`. Conclude with `(pow_eq_one_iff.1 h).resolve_right two_ne_zero`.
-/
theorem absA_det_neg_one (t : ℕ) : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) = 1 := by
  have h : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, neg_one_sq, map_one, map_one]
  exact (pow_eq_one_iff.1 h).resolve_right two_ne_zero

/- English proof (translation)
Establish `hm : mat (w * w) = blk4 (-1 : GL (Fin t) (AE D)).1 0 0 (adj ((-1 : GL (Fin t) (AE D))⁻¹).1)`. Establish `hi : ((-1 : GL (Fin t) (AE D))⁻¹) = -1`. Rewrite using `[inv_eq_iff_mul_eq_one]`. Simplify using the standard rewrite rules. Establish `ha : adj (-1 : Mx D t t) = -1`.

Rewrite using `[adj_neg, adj_one]`. Rewrite using `[hi, mat_mul_mat, show mat w = _ from hw, block_matrix_mul]`. Simplify using `[ha]`. Establish `hl` using `hΩ.levi (w * w) (-1) hm h y`. Establish `hc : (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) : ℂ) = 1`.

Rewrite using `[det_neg_one]`. Use `hχ.2 ((-1 : (D.host.E)ˣ) ^ t)` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[← mul_assoc, hl, hc, absA_det_neg_one]`.

Simplify using `[npow]`.
-/
theorem weyl_sq {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D}
    {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω)
    {w : G D t} (hw : IsW w) (h : G D t) (y : Mx D ρ t) : Ω (w * (w * h)) y = Ω h (-y) := by
  have hm : mat (w * w) = blk4 (-1 : GL (Fin t) (AE D)).1 0 0 (adj ((-1 : GL (Fin t) (AE D))⁻¹).1) := by
    have hi : ((-1 : GL (Fin t) (AE D))⁻¹) = -1 := by
      rw [inv_eq_iff_mul_eq_one]
      simp
    have ha : adj (-1 : Mx D t t) = -1 := by
      rw [adj_neg, adj_one]
    rw [hi, mat_mul_mat, show mat w = _ from hw, block_matrix_mul]
    simp [ha]
  have hl := hΩ.levi (w * w) (-1) hm h y
  have hc : (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) : ℂ) = 1 := by
    rw [det_neg_one]
    have := hχ.2 ((-1 : (D.host.E)ˣ) ^ t)
    rw [this]
    simp
  rw [← mul_assoc, hl, hc, absA_det_neg_one]
  simp [npow]

end GlobalTheory.CompanionTheory.RCellInv

open GlobalTheory.CompanionTheory.RCellInv in

/- English proof (translation)
Introduce `D t ρ ψ hψ χ hχ θ b₀ μ Ω hΩ nb hnb w hw b y₀`. Establish `hint : ∀ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) = conj (Ω (w * nb b) y * ψ (trA (Matrix.trace (pr b₀ (-y₀) y))))`. Introduce `y`. Establish `hneg : -trA (Matrix.trace (pr b₀ (-y₀) y)) = trA (Matrix.trace (pr b₀ y y₀))`. Rewrite using `[pr_neg_left, Matrix.trace_neg, trA_trace_pr_swap b₀ y₀ y]`.

Simplify using `only [trA, map_neg, neg_neg]`. Rewrite using `[map_mul, conj_char hψ, hneg, mul_comm]`. Establish `hu` using `hΩ.unip (nb b) b.1 (hnb b) 1 y₀`. Rewrite `hu` using `[mul_one]`. Simplify using `only [hint]`.

Rewrite using `[integral_conj, ← hΩ.weyl w hw (w * nb b) (-y₀), weyl_sq hχ hΩ hw, neg_neg, hu]`.
-/
theorem GlobalTheory.CompanionTheory.RCellInv.fourier_inv : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  intro D t ρ ψ hψ χ hχ θ b₀ μ Ω hΩ nb hnb w hw b y₀
  have hint : ∀ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) =
      conj (Ω (w * nb b) y * ψ (trA (Matrix.trace (pr b₀ (-y₀) y)))) := by
    intro y
    have hneg : -trA (Matrix.trace (pr b₀ (-y₀) y)) = trA (Matrix.trace (pr b₀ y y₀)) := by
      rw [pr_neg_left, Matrix.trace_neg, trA_trace_pr_swap b₀ y₀ y]
      simp only [trA, map_neg, neg_neg]
    rw [map_mul, conj_char hψ, hneg, mul_comm]
  have hu := hΩ.unip (nb b) b.1 (hnb b) 1 y₀
  rw [mul_one] at hu
  simp only [hint]
  rw [integral_conj, ← hΩ.weyl w hw (w * nb b) (-y₀), weyl_sq hχ hΩ hw, neg_neg, hu]
