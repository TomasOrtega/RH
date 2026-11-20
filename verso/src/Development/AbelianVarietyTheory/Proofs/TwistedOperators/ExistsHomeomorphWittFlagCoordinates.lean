import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def flagCoordMap (d : HypDec S S₀ ρ) (p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ)) : flagN d :=
  ⟨d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2),
    ((flag_jacobi_structure D S S₀ ρ d).1 _).2 ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩

/- English proof (translation)
Use `⟨fun p q h => ?_, fun n => ?_⟩` and prove the remaining obligations. Establish `h'` using `(flag_jacobi_structure D S S₀ ρ d).2.2.2.2.2.2 _ _ _ _ _ _ (congrArg Subtype.val h)`. Take `⟨h1, h2, h3⟩` from `h'`. Conclude with `Prod.ext (Subtype.ext h1) (Prod.ext h2 h3)`. Take `⟨u, hu, b, c, hn⟩` from `((flag_jacobi_structure D S S₀ ρ d).1 n.1).1 n.2`.

Conclude with `⟨(⟨u, hu⟩, b, c), Subtype.ext hn.symm⟩`.
-/
theorem flagCoordMap_bijective (d : HypDec S S₀ ρ) : Function.Bijective (flagCoordMap d) := by
  refine ⟨fun p q h => ?_, fun n => ?_⟩
  · have h' := (flag_jacobi_structure D S S₀ ρ d).2.2.2.2.2.2 _ _ _ _ _ _ (congrArg Subtype.val h)
    obtain ⟨h1, h2, h3⟩ := h'
    exact Prod.ext (Subtype.ext h1) (Prod.ext h2 h3)
  · obtain ⟨u, hu, b, c, hn⟩ := ((flag_jacobi_structure D S S₀ ρ d).1 n.1).1 n.2
    exact ⟨(⟨u, hu⟩, b, c), Subtype.ext hn.symm⟩

/- English proof (translation)
Rewrite using `[mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]`. Use `congr 1`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]`.
-/
theorem pX_mt_flagCoord (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX ⬝ Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) =
      u.1 ⬝ (d.pX + c.1 ⬝ d.pY + b ⬝ d.p0 - (half D • (b ⬝ plus S₀ b)) ⬝ d.pY) := by
  rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
  congr 1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, pX_mt_flagCoord]`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero, Matrix.mul_one, add_zero, sub_zero]`.
-/
theorem flagCoord_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX) = u.1 := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, pX_mt_flagCoord]`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero, Matrix.mul_one, add_zero, sub_zero, zero_add]`.
-/
theorem flagCoordinate_at_base (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0) = u.1 ⬝ b := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero, zero_add]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, pX_mt_flagCoord]`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]`.
-/
theorem flagCoord_jY (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.jY) =
      u.1 ⬝ (c.1 - half D • (b ⬝ plus S₀ b)) := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]

/- English proof (translation)
Use `set g := d.levi u * (d.nB b * d.nC c)`. Establish `h1 : Formalism.L2.Theta.mt S g ⬝ d.jX = d.jX ⬝ u.1`. Simplify using `only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]`. Establish `h2 : Formalism.L2.Theta.mt S g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Use `_ = d.jX ⬝ (u⁻¹).1 := by`. Rewrite using `[← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]`. Rewrite using `[h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`.
-/
theorem flagCoord_inv_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c))⁻¹ ⬝ d.jX) = (u⁻¹).1 := by
  set g := d.levi u * (d.nB b * d.nC c)
  have h1 : Formalism.L2.Theta.mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
    simp only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc Formalism.L2.Theta.mt S g⁻¹ ⬝ d.jX = Formalism.L2.Theta.mt S g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by
          rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  rw [h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

/- English proof (translation)
Rewrite using `[flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem flagCoord_b (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0)) = b := by
  rw [flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]`.
-/
theorem flagCoord_c (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.jY)) + half D • (b ⬝ plus S₀ b) = c.1 := by
  rw [flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

/- English proof (translation)
Introduce `D S S₀ ρ d`. Use `(lattice_Mx D ρ ρ).1` as an intermediate fact. Set `e0` to `Equiv.ofBijective _ (flagCoordMap_bijective d)`. Establish `key : ∀ n : flagN d, (n : GA D S) = d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2)` using `fun n => congrArg Subtype.val (e0.apply_symm_apply n).symm`. Establish `hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)` using `(continuous_mt S).comp continuous_subtype_val`.

Establish `hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹` using `(continuous_mt S).comp continuous_subtype_val.inv`. Establish `hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.jX)`. Introduce `n`. Rewrite using `[key n, flagCoord_jX]`. Establish `hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val = d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX)`.

Introduce `n`. Rewrite using `[key n, flagCoord_inv_jX]`. Establish `hB : ∀ n : flagN d, (e0.symm n).2.1 = d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.j0))`. Introduce `n`. Rewrite using `[← hUi n]`.

Use `conv_rhs => rw [key n]`. Conclude with `(flagCoord_b d _ _ _).symm`. Establish `hC : ∀ n : flagN d, ((e0.symm n).2.2).val = d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.jY)) + half D • ((e0.symm n).2.1 ⬝ plus S₀ (e0.symm n).2.1)`. Introduce `n`. Rewrite using `[← hUi n]`.

Use `conv_rhs => rw [key n]`. Conclude with `(flagCoord_c d _ _ _).symm`. Establish `cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val`. Simplify using `only [hU]`. Conclude with `continuous_const.matrix_mul (hM.matrix_mul continuous_const)`.

Establish `cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val`. Simplify using `only [hUi]`. Conclude with `continuous_const.matrix_mul (hMi.matrix_mul continuous_const)`. Establish `cB : Continuous fun n : flagN d => (e0.symm n).2.1`. Simplify using `only [hB]`.

Conclude with `(continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul (continuous_const.matrix_mul (hM.matrix_mul continuous_const))`. Establish `cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val`. Establish `hp : Continuous fun n : flagN d => (e0.symm n).2.1 ⬝ plus S₀ (e0.symm n).2.1` using `cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))`. Simplify using `only [hC]`. Conclude with `((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))`.

Use `⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩` and prove the remaining obligations. Use `show Continuous (flagCoordMap d)`. Conclude with `Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _`. Use `Continuous.prodMk ?_ (Continuous.prodMk cB ?_)` and prove the remaining obligations. Conclude with `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)`.

Conclude with `continuous_induced_rng.2 cC`.
-/
theorem flagCoord_homeo : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d,
      ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  intro D S S₀ ρ d
  have := (lattice_Mx D ρ ρ).1
  let e0 := Equiv.ofBijective _ (flagCoordMap_bijective d)
  have key : ∀ n : flagN d, (n : GA D S) =
      d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2) := fun n =>
    congrArg Subtype.val (e0.apply_symm_apply n).symm
  have hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S) :=
    (continuous_mt S).comp continuous_subtype_val
  have hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹ :=
    (continuous_mt S).comp continuous_subtype_val.inv
  have hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.jX) := by
    intro n; rw [key n, flagCoord_jX]
  have hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val =
      d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX) := by
    intro n; rw [key n, flagCoord_inv_jX]
  have hB : ∀ n : flagN d, (e0.symm n).2.1 =
      d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.j0)) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_b d _ _ _).symm
  have hC : ∀ n : flagN d, ((e0.symm n).2.2).val =
      d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ (Formalism.L2.Theta.mt S (n : GA D S) ⬝ d.jY)) +
        half D • ((e0.symm n).2.1 ⬝ plus S₀ (e0.symm n).2.1) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_c d _ _ _).symm
  have cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val := by
    simp only [hU]; exact continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  have cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val := by
    simp only [hUi]; exact continuous_const.matrix_mul (hMi.matrix_mul continuous_const)
  have cB : Continuous fun n : flagN d => (e0.symm n).2.1 := by
    simp only [hB]
    exact (continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))
  have cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val := by
    have hp : Continuous fun n : flagN d => (e0.symm n).2.1 ⬝ plus S₀ (e0.symm n).2.1 :=
      cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))
    simp only [hC]
    exact ((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))
  refine ⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩
  · show Continuous (flagCoordMap d)
    exact Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul
        (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _
  · refine Continuous.prodMk ?_ (Continuous.prodMk cB ?_)
    · exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)
    · exact continuous_induced_rng.2 cC

end GlobalTheory.MixPer
