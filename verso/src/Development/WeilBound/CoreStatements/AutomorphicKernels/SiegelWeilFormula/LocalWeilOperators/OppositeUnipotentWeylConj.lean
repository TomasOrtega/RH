import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.IsLocOpOfOk
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ExistsInsW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.WeylCubeConjUnipotent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.
-/
theorem intUnit_sq {R : Type} [Ring R] (ε : ℤˣ) : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

/- English proof (translation)
Apply `d.inFrame_inj` to reduce the goal to its premises. Establish `hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E)` using `h`. Rewrite using `[d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]`.
-/
theorem w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := by
  apply d.inFrame_inj
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]

/- English proof (translation)
Establish `hζ0 : R.ζ ≠ 0` using `Krd.zeta_ne R.hζ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]`. Use `_ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]`.
-/
theorem cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]

/- English proof (translation)
Establish `hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E)` using `h`. Rewrite using `[hW]`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [SD.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [SD.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp

/- English proof (translation)
Break down `R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩` into its components or cases. Rewrite using `[he, hz]`. Simplify using the standard rewrite rules. Rewrite using `[he, hz]`. Simplify using `[Complex.inv_I]`.
-/
theorem zeta_rel : R.ζ⁻¹ = ((R.ε : ℤ) : ℂ) * -R.ζ := by
  rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩
  · rw [he, hz]; simp
  · rw [he, hz]; simp [Complex.inv_I]

def nUpt (x : Matrix (Fin d.n) (Fin d.n) ℂ) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one],
    by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩,
    by
      show InG (nU x)
      simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hx]⟩

/- English proof (translation)
Introduce `y c hc hy`. Establish `hζ0 : R.ζ ≠ 0` using `Krd.zeta_ne R.hζ`. Establish `he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1` using `intUnit_sq ε`. Establish `hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹`. Break down `R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩` into its components or cases.

Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[hz]`. Simplify using `[Complex.inv_I]`. Use `set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef`.

Establish `hx : xᴴ = x` using `by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]`. Use `⟨nUpt x hx, x, hx, rfl, ?_⟩` and prove the remaining obligations. Apply `d.inFrame_inj` to reduce the goal to its premises. Simplify using `only [d.inFrame_mul]`. Apply `Place.cw_ext d` to reduce the goal to its premises.

Introduce `w'`. Simplify using `only [Krd.cw_mul d, RD.cw_wM h]`. Distinguish the cases in `hw : w' = w`. Rewrite using `[hw, R.cw_iota_pf w y, R.cw_iota_pf w (nUpt x hx), hy]`. Establish `e1 : mR (nUpt x hx) = nU x` using `rfl`.

Rewrite using `[e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]`. Use `congr 1`. Rewrite using `[hxdef, smul_smul, smul_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[he, mul_inv_cancel₀ hζ0]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by ring`. Rewrite using `[R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]`. Establish `hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E)` using `h`.

Rewrite using `[R.off_f w y]`. Simplify using `only [Krd.fin_mul, R.off_f w]`. Simplify using `only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]`.
-/
theorem nbar_conj_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨nUpt x hx, x, hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply Place.cw_ext d
  · intro w'
    simp only [Krd.cw_mul d, RD.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (nUpt x hx), hy]
      have e1 : mR (nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]

/- English proof (translation)
Introduce `y c hc hy`. Establish `hζ0 : R.ζ ≠ 0` using `Krd.zeta_ne R.hζ`. Establish `he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1` using `intUnit_sq ε`. Establish `hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹`. Break down `R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩` into its components or cases.

Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[hz]`. Simplify using `[Complex.inv_I]`. Use `set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef`.

Establish `hx : xᴴ = x` using `by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]`. Use `⟨nUpt x hx, rfl, ?_⟩` and prove the remaining obligations. Apply `d.inFrame_inj` to reduce the goal to its premises. Simplify using `only [d.inFrame_mul]`. Apply `Place.cw_ext d` to reduce the goal to its premises.

Introduce `w'`. Simplify using `only [Krd.cw_mul d, RD.cw_wM h]`. Distinguish the cases in `hw : w' = w`. Rewrite using `[hw, R.cw_iota_pf w y, R.cw_iota_pf w (nUpt x hx), hy]`. Establish `e1 : mR (nUpt x hx) = nU x` using `rfl`.

Rewrite using `[e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]`. Use `congr 1`. Rewrite using `[hxdef, smul_smul, smul_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[he, mul_inv_cancel₀ hζ0]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by ring`. Rewrite using `[R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]`. Establish `hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E)` using `h`.

Rewrite using `[R.off_f w y]`. Simplify using `only [Krd.fin_mul, R.off_f w]`. Simplify using `only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]`.
-/
theorem oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨nUpt x hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply Place.cw_ext d
  · intro w'
    simp only [Krd.cw_mul d, RD.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (nUpt x hx), hy]
      have e1 : mR (nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]

end RD

end PositivityTheory.SiegelWeilFormula

end
