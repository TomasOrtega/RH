import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv

noncomputable section

namespace PI.AprimeInfW

open Matrix

section Gen

variable {A : Type} [CommRing A] (σ : A →+* A) {m M : Type} [Fintype m] [DecidableEq m] [Fintype M] [DecidableEq M]

/- English proof (translation)
Use `set Ys := Y.map σ with hYs`. Use `set G := Ys * K * Yᵀ with hG`. Establish `cT_add : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P + Q) = Formalism.UG.cT σ P + Formalism.UG.cT σ Q`. Introduce `p q P Q`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT]`. Establish `cT_sub : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P - Q) = Formalism.UG.cT σ P - Formalism.UG.cT σ Q`. Introduce `p q P Q`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.

Establish `cTYs : Formalism.UG.cT σ Ys = Yᵀ` using `by ext i j; simp [Formalism.UG.cT, hYs, hσ]`. Establish `cTYt : Formalism.UG.cT σ Yᵀ = Ys` using `by ext i j; simp [Formalism.UG.cT, hYs]`. Establish `hGh : Formalism.UG.cT σ G = G`. Rewrite using `[hG, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTYt, hK, cTYs, Matrix.mul_assoc]`. Establish `hGih : Formalism.UG.cT σ Gi = Gi`.

Establish `h1 : Formalism.UG.cT σ Gi * G = 1`. Rewrite using `[← hGh, ← Formalism.UG.cT_mul, hGi2, Formalism.UG.cT_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hGiGx : ∀ x : Matrix m m A, Gi * (G * x) = x` using `fun x => by rw [← Matrix.mul_assoc, hGi1, Matrix.one_mul]`. Use `set ei := Gi * Formalism.UG.cT σ e * G with hei`.

Establish `hei1 : ei * e = 1`. Rewrite using `[hei, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ e), he, hGi1]`. Establish `hei2 : e * ei = 1` using `mul_eq_one_comm.1 hei1`. Establish `keyprod : ∀ C D : Matrix m m A, (Yᵀ * C * (Ys * K)) * (Yᵀ * D * (Ys * K)) = Yᵀ * (C * G * D) * (Ys * K)`. Introduce `C D`.

Simplify using `only [hG, Matrix.mul_assoc]`. Establish `E1 : ∀ C D : Matrix m m A, (1 + Yᵀ * C * (Ys * K)) * (1 + Yᵀ * D * (Ys * K)) = 1 + Yᵀ * (C + D + C * G * D) * (Ys * K)`. Introduce `C D`. Rewrite using `[show Yᵀ * (C + D + C * G * D) * (Ys * K) = Yᵀ * C * (Ys * K) + Yᵀ * D * (Ys * K) + Yᵀ * (C * G * D) * (Ys * K) by simp only [Matrix.mul_add, Matrix.add_mul], ← keyprod]`. Use `noncomm_ring`.

Establish `inner : ∀ x y : Matrix m m A, x * y = 1 → (x - 1) * Gi + (y - 1) * Gi + (x - 1) * Gi * G * ((y - 1) * Gi) = 0`. Introduce `x y hxy`. Establish `h1 : (x - 1) * Gi * G * ((y - 1) * Gi) = (x - 1) * (y - 1) * Gi`. Rewrite using `[Matrix.mul_assoc (x - 1) Gi G, hGi1, Matrix.mul_one, Matrix.mul_assoc]`. Establish `h2 : (x - 1) * (y - 1) = x * y - x - y + 1` using `by noncomm_ring`.

Rewrite using `[h1, h2, hxy]`. Use `noncomm_ring`. Use `⟨1 + Yᵀ * ((e - 1) * Gi) * (Ys * K), 1 + Yᵀ * ((ei - 1) * Gi) * (Ys * K), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[E1, inner e ei hei2]`. Simplify using the standard rewrite rules.

Rewrite using `[E1, inner ei e hei1]`. Simplify using the standard rewrite rules. Establish `hcT : Formalism.UG.cT σ (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) = 1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys`. Rewrite using `[cT_add, Formalism.UG.cT_one]`. Use `congr 1`.

Simplify using `only [Formalism.UG.cT_mul, cT_sub, Formalism.UG.cT_one, hK, cTYs, cTYt, hGih, Matrix.mul_assoc]`. Rewrite using `[hcT]`. Establish `hin : (e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) + Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) = 0`. Establish `h1 : Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) = Gi * (Formalism.UG.cT σ e * G * e) * Gi - Gi * Formalism.UG.cT σ e * (G * Gi) - Gi * (G * (e * Gi)) + Gi * (G * Gi)` using `by noncomm_ring`. Rewrite using `[h1, he]`.

Simplify using `only [hGi1, hGi2, hGiGx, Matrix.one_mul, Matrix.mul_one]`. Use `noncomm_ring`. Establish `expand : (1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys) * K * (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) = K + K * (Yᵀ * ((e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) + Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi)) * (Ys * K))`. Simplify using `only [hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Rewrite using `[expand, hin]`. Simplify using the standard rewrite rules. Establish `h1 : ((e - 1) * Gi * G)ᵀ = (e - 1)ᵀ` using `by rw [Matrix.mul_assoc, hGi1, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hG, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_one, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Use `_ = eᵀ * Y := by`. Rewrite using `[h1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem witt_span (hσ : ∀ x, σ (σ x) = x) (K : Matrix M M A) (hK : Formalism.UG.cT σ K = K) (Y : Matrix m M A)
    (Gi : Matrix m m A) (hGi1 : Gi * (Y.map σ * K * Yᵀ) = 1) (hGi2 : (Y.map σ * K * Yᵀ) * Gi = 1)
    (e : Matrix m m A) (he : Formalism.UG.cT σ e * (Y.map σ * K * Yᵀ) * e = Y.map σ * K * Yᵀ) :
    ∃ h h' : Matrix M M A, h * h' = 1 ∧ h' * h = 1 ∧ Formalism.UG.cT σ h * K * h = K ∧ Y * hᵀ = eᵀ * Y := by
  set Ys := Y.map σ with hYs
  set G := Ys * K * Yᵀ with hG
  have cT_add : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P + Q) = Formalism.UG.cT σ P + Formalism.UG.cT σ Q := by
    intro p q P Q; ext i j; simp [Formalism.UG.cT]
  have cT_sub : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P - Q) = Formalism.UG.cT σ P - Formalism.UG.cT σ Q := by
    intro p q P Q; ext i j; simp [Formalism.UG.cT]
  have cTYs : Formalism.UG.cT σ Ys = Yᵀ := by ext i j; simp [Formalism.UG.cT, hYs, hσ]
  have cTYt : Formalism.UG.cT σ Yᵀ = Ys := by ext i j; simp [Formalism.UG.cT, hYs]
  have hGh : Formalism.UG.cT σ G = G := by
    rw [hG, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTYt, hK, cTYs, Matrix.mul_assoc]
  have hGih : Formalism.UG.cT σ Gi = Gi := by
    have h1 : Formalism.UG.cT σ Gi * G = 1 := by
      rw [← hGh, ← Formalism.UG.cT_mul, hGi2, Formalism.UG.cT_one]
    calc Formalism.UG.cT σ Gi = Formalism.UG.cT σ Gi * (G * Gi) := by rw [hGi2, Matrix.mul_one]
      _ = Gi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hGiGx : ∀ x : Matrix m m A, Gi * (G * x) = x := fun x => by rw [← Matrix.mul_assoc, hGi1, Matrix.one_mul]

  set ei := Gi * Formalism.UG.cT σ e * G with hei
  have hei1 : ei * e = 1 := by
    rw [hei, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ e), he, hGi1]
  have hei2 : e * ei = 1 := mul_eq_one_comm.1 hei1

  have keyprod : ∀ C D : Matrix m m A, (Yᵀ * C * (Ys * K)) * (Yᵀ * D * (Ys * K)) = Yᵀ * (C * G * D) * (Ys * K) := by
    intro C D; simp only [hG, Matrix.mul_assoc]
  have E1 : ∀ C D : Matrix m m A, (1 + Yᵀ * C * (Ys * K)) * (1 + Yᵀ * D * (Ys * K)) =
      1 + Yᵀ * (C + D + C * G * D) * (Ys * K) := by
    intro C D
    rw [show Yᵀ * (C + D + C * G * D) * (Ys * K) = Yᵀ * C * (Ys * K) + Yᵀ * D * (Ys * K) +
        Yᵀ * (C * G * D) * (Ys * K) by simp only [Matrix.mul_add, Matrix.add_mul], ← keyprod]
    noncomm_ring
  have inner : ∀ x y : Matrix m m A, x * y = 1 →
      (x - 1) * Gi + (y - 1) * Gi + (x - 1) * Gi * G * ((y - 1) * Gi) = 0 := by
    intro x y hxy
    have h1 : (x - 1) * Gi * G * ((y - 1) * Gi) = (x - 1) * (y - 1) * Gi := by
      rw [Matrix.mul_assoc (x - 1) Gi G, hGi1, Matrix.mul_one, Matrix.mul_assoc]
    have h2 : (x - 1) * (y - 1) = x * y - x - y + 1 := by noncomm_ring
    rw [h1, h2, hxy]; noncomm_ring
  refine ⟨1 + Yᵀ * ((e - 1) * Gi) * (Ys * K), 1 + Yᵀ * ((ei - 1) * Gi) * (Ys * K), ?_, ?_, ?_, ?_⟩
  · rw [E1, inner e ei hei2]; simp
  · rw [E1, inner ei e hei1]; simp
  · have hcT : Formalism.UG.cT σ (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) =
        1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys := by
      rw [cT_add, Formalism.UG.cT_one]
      congr 1
      simp only [Formalism.UG.cT_mul, cT_sub, Formalism.UG.cT_one, hK, cTYs, cTYt, hGih, Matrix.mul_assoc]
    rw [hcT]
    have hin : (e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) + Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) = 0 := by
      have h1 : Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) =
          Gi * (Formalism.UG.cT σ e * G * e) * Gi - Gi * Formalism.UG.cT σ e * (G * Gi) - Gi * (G * (e * Gi)) +
            Gi * (G * Gi) := by noncomm_ring
      rw [h1, he]
      simp only [hGi1, hGi2, hGiGx, Matrix.one_mul, Matrix.mul_one]
      noncomm_ring
    have expand : (1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys) * K * (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) =
        K + K * (Yᵀ * ((e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) +
          Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi)) * (Ys * K)) := by
      simp only [hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [expand, hin]; simp
  · have h1 : ((e - 1) * Gi * G)ᵀ = (e - 1)ᵀ := by rw [Matrix.mul_assoc, hGi1, Matrix.mul_one]
    calc Y * (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K))ᵀ = Y + ((e - 1) * Gi * G)ᵀ * Y := by
          simp only [hG, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_one,
            Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = eᵀ * Y := by
          rw [h1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul]; abel

end Gen

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTΩ hU`. Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Use `set R := Ainf X.B.I.F`. Use `set σ := sigR (F := X.B.I.F) (E := X.B.I.E) R X.B.I.cm.sig with hσdef`. Establish `hσ : ∀ x, σ (σ x) = x` using `sq_sig_inv R X.B.I.cm.sig (sig_invI X)`.

Use `set K := JR (F := X.B.I.F) R X.B.I.J with hKdef`. Establish `hK : Formalism.UG.cT σ K = K`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hKdef, JR, hσdef]`. Rewrite using `[← J_hermI X i j]`.

Simplify using `[sigR, inclR]`. Use `set Y : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E) := Y0 X u' with hY`. Use `set G0 := gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) with hG0`. Establish `hdet` using `detNZ_holds X u' ψ hT μinf νinf fibInf hP`. Establish `hu : IsUnit G0.det` using `isUnit_iff_ne_zero.2 hdet`.

Establish `hGY : Y.map σ * K * Yᵀ = G0.map (inclR R)`. Rewrite using `[← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]`. Conclude with `gramR_ratTup R X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))`. Use `set Gi := G0⁻¹.map (inclR (F := X.B.I.F) (E := X.B.I.E) R) with hGi`. Establish `hGi1 : Gi * (Y.map σ * K * Yᵀ) = 1`.

Rewrite using `[hGY, hGi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hGi2 : (Y.map σ * K * Yᵀ) * Gi = 1`. Rewrite using `[hGY, hGi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]`. Take `⟨w, hw⟩` from `hU`. Use `set e : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (R ⊗[X.B.I.F] X.B.I.E) := a T * (↑w⁻¹ : MfI X) with he_def`.

Establish `hgr : ∀ b : MfI X, gramR R X.B.I.cm.sig X.B.I.J (rmulT X b (Y0 X u')) = Formalism.UG.cT σ b * (Y.map σ * K * Yᵀ) * b`. Introduce `b`. Rewrite using `[← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]`. Conclude with `sq_gramR_rmul R X.B.I.cm.sig X.B.I.J b Y`. Establish `hTa : Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) * a T = Formalism.UG.cT σ (a₂ T) * (Y.map σ * K * Yᵀ) * a₂ T`.

Rewrite using `[← hgr, ← hgr, hC.2.2.2 T hTΩ.1, hC₂.2.2.2 T hTΩ.2]`. Establish `hww : Formalism.UG.cT σ (↑w⁻¹ : MfI X) * Formalism.UG.cT σ (↑w : MfI X) = 1`. Rewrite using `[← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]`. Establish `he : Formalism.UG.cT σ e * (Y.map σ * K * Yᵀ) * e = Y.map σ * K * Yᵀ`. Rewrite using `[he_def, Formalism.UG.cT_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[hTa, ← hw]`. Simplify using `only [← Matrix.mul_assoc]`.

Rewrite using `[hww, Matrix.one_mul, Matrix.mul_assoc _ (↑w : MfI X), Units.mul_inv, Matrix.mul_one]`. Take `⟨h, h', hh1, hh2, hhu, hhY⟩` from `witt_span σ hσ K hK Y Gi hGi1 hGi2 e he`. Set `gl : GL (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E)` to `⟨h, h', hh1, hh2⟩`. Establish `hmem : gl ∈ HR R X.B.I.cm.sig X.B.I.J` using `hhu`. Use `⟨⟨gl, hmem⟩, ?_⟩` and prove the remaining obligations.

Establish `key : (a₂ T)ᵀ * Y * hᵀ = (a T)ᵀ * Y`. Rewrite using `[Matrix.mul_assoc, hhY, ← Matrix.mul_assoc, ← Matrix.transpose_mul, he_def, Matrix.mul_assoc, ← hw, Units.inv_mul, Matrix.mul_one]`. Use function extensionality and compare the values at `b i`. Express the relevant statement in the definitionally equal form `rmulT X (a T) (Y0 X u') b i = Matrix.mulVec h (rmulT X (a₂ T) (Y0 X u') b) i`. Establish `k2` using `congrFun (congrFun key b) i`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply] at k2`. Simplify using `only [rmulT, Matrix.mulVec, dotProduct]`. Rewrite using `[← k2]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [mul_comm]`.
-/
theorem wittNear_span : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTΩ hU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  set R := Ainf X.B.I.F
  set σ := sigR (F := X.B.I.F) (E := X.B.I.E) R X.B.I.cm.sig with hσdef
  have hσ : ∀ x, σ (σ x) = x := sq_sig_inv R X.B.I.cm.sig (sig_invI X)
  set K := JR (F := X.B.I.F) R X.B.I.J with hKdef
  have hK : Formalism.UG.cT σ K = K := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hKdef, JR, hσdef]
    rw [← J_hermI X i j]
    simp [sigR, inclR]
  set Y : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E) := Y0 X u' with hY
  set G0 := gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) with hG0
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hu : IsUnit G0.det := isUnit_iff_ne_zero.2 hdet
  have hGY : Y.map σ * K * Yᵀ = G0.map (inclR R) := by
    rw [← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]
    exact gramR_ratTup R X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  set Gi := G0⁻¹.map (inclR (F := X.B.I.F) (E := X.B.I.E) R) with hGi
  have hGi1 : Gi * (Y.map σ * K * Yᵀ) = 1 := by
    rw [hGY, hGi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGi2 : (Y.map σ * K * Yᵀ) * Gi = 1 := by
    rw [hGY, hGi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨w, hw⟩ := hU
  set e : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (R ⊗[X.B.I.F] X.B.I.E) :=
    a T * (↑w⁻¹ : MfI X) with he_def
  have hgr : ∀ b : MfI X, gramR R X.B.I.cm.sig X.B.I.J (rmulT X b (Y0 X u')) =
      Formalism.UG.cT σ b * (Y.map σ * K * Yᵀ) * b := by
    intro b
    rw [← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]
    exact sq_gramR_rmul R X.B.I.cm.sig X.B.I.J b Y
  have hTa : Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) * a T =
      Formalism.UG.cT σ (a₂ T) * (Y.map σ * K * Yᵀ) * a₂ T := by
    rw [← hgr, ← hgr, hC.2.2.2 T hTΩ.1, hC₂.2.2.2 T hTΩ.2]
  have hww : Formalism.UG.cT σ (↑w⁻¹ : MfI X) * Formalism.UG.cT σ (↑w : MfI X) = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have he : Formalism.UG.cT σ e * (Y.map σ * K * Yᵀ) * e = Y.map σ * K * Yᵀ := by
    rw [he_def, Formalism.UG.cT_mul]
    calc Formalism.UG.cT σ (↑w⁻¹ : MfI X) * Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) *
          (a T * (↑w⁻¹ : MfI X))
        = Formalism.UG.cT σ (↑w⁻¹ : MfI X) *
          (Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) * a T) * (↑w⁻¹ : MfI X) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hTa, ← hw]
          simp only [← Matrix.mul_assoc]
          rw [hww, Matrix.one_mul, Matrix.mul_assoc _ (↑w : MfI X), Units.mul_inv, Matrix.mul_one]
  obtain ⟨h, h', hh1, hh2, hhu, hhY⟩ := witt_span σ hσ K hK Y Gi hGi1 hGi2 e he
  let gl : GL (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E) := ⟨h, h', hh1, hh2⟩
  have hmem : gl ∈ HR R X.B.I.cm.sig X.B.I.J := hhu
  refine ⟨⟨gl, hmem⟩, ?_⟩
  have key : (a₂ T)ᵀ * Y * hᵀ = (a T)ᵀ * Y := by
    rw [Matrix.mul_assoc, hhY, ← Matrix.mul_assoc, ← Matrix.transpose_mul, he_def, Matrix.mul_assoc, ← hw,
      Units.inv_mul, Matrix.mul_one]
  funext b i
  change rmulT X (a T) (Y0 X u') b i = Matrix.mulVec h (rmulT X (a₂ T) (Y0 X u') b) i
  have k2 := congrFun (congrFun key b) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at k2
  simp only [rmulT, Matrix.mulVec, dotProduct]
  rw [← k2]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/- English proof (translation)
The claim follows from `jacOne_of_charts hK hU wittNear_span hG`.
-/
theorem jacOne_of_good (hK : KPos) (hU : UnimodInf) (hG : GoodChartEx) : JacOne :=
  jacOne_of_charts hK hU wittNear_span hG

end PI.AprimeInfW
