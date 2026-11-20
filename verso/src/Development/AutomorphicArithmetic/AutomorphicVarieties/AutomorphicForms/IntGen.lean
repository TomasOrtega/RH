import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CrysSlopes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.IntGen

/- English proof (translation)
Establish `hev : Module.End.HasEigenvalue (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)) x`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']`. Conclude with `hx`. Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`. Establish `hgv : (r g : Matrix (Fin n) (Fin n) k).mulVec v = x • v` using `hv.apply_eq_smul`.

Take `⟨i, hi⟩` from `Function.ne_iff.1 hv.2`. Establish `hi' : 0 < ‖v i‖` using `norm_pos_iff.2 hi`. Establish `hc : Continuous fun s => ‖(r s : Matrix (Fin n) (Fin n) k).mulVec v i‖` using `((continuous_apply i).comp ((Units.continuous_val.comp hr).matrix_mulVec continuous_const)).norm`. Take `⟨C, hC⟩` from `(isCompact_range hc).bddAbove`. Establish `le : ∀ (s : Γ) (y : k), (r s : Matrix (Fin n) (Fin n) k).mulVec v = y • v → ‖y‖ ≤ 1` using `fun s y hy => by`.

Establish `hp : ∀ N : ℕ, (r (s ^ N) : Matrix (Fin n) (Fin n) k).mulVec v = y ^ N • v` using `fun N => by`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih => rw [pow_succ, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, ih, smul_smul, pow_succ']`. Assume the negation of the conclusion as `hlt`.

Take `⟨N, hN⟩` from `pow_unbounded_of_one_lt (C / ‖v i‖) (not_le.1 hlt)`. Use `hC ⟨s ^ N, rfl⟩` as an intermediate fact. Simplify using `only [hp, Pi.smul_apply, norm_smul, norm_pow] at this`. Rewrite `hN` using `[div_lt_iff₀ hi']`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : x • (r g⁻¹ : Matrix (Fin n) (Fin n) k).mulVec v = v`. Rewrite using `[← Matrix.mulVec_smul, ← hgv, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hx0 : x ≠ 0` using `fun h0 => hv.2 (by rw [← e, h0, zero_smul])`. Establish `h2` using `le g⁻¹ x⁻¹ (by rw [eq_inv_smul_iff₀ hx0, e])`.

Rewrite `h2` using `[norm_inv]`. Conclude with `le_antisymm (le g x hgv) ((inv_le_one₀ (norm_pos_iff.2 hx0)).1 h2)`.
-/
private theorem norm_root {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (hr : Continuous r) (g : Γ) (x : k) (hx : (r g : Matrix (Fin n) (Fin n) k).charpoly.IsRoot x) :
    ‖x‖ = 1 := by
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)) x := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hx
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hgv : (r g : Matrix (Fin n) (Fin n) k).mulVec v = x • v := hv.apply_eq_smul
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv.2
  have hi' : 0 < ‖v i‖ := norm_pos_iff.2 hi
  have hc : Continuous fun s => ‖(r s : Matrix (Fin n) (Fin n) k).mulVec v i‖ :=
    ((continuous_apply i).comp ((Units.continuous_val.comp hr).matrix_mulVec continuous_const)).norm
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  have le : ∀ (s : Γ) (y : k), (r s : Matrix (Fin n) (Fin n) k).mulVec v = y • v → ‖y‖ ≤ 1 := fun s y hy => by
    have hp : ∀ N : ℕ, (r (s ^ N) : Matrix (Fin n) (Fin n) k).mulVec v = y ^ N • v := fun N => by
      induction N with
      | zero => simp
      | succ N ih => rw [pow_succ, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    by_contra hlt
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (C / ‖v i‖) (not_le.1 hlt)
    have := hC ⟨s ^ N, rfl⟩
    simp only [hp, Pi.smul_apply, norm_smul, norm_pow] at this
    rw [div_lt_iff₀ hi'] at hN
    linarith
  have e : x • (r g⁻¹ : Matrix (Fin n) (Fin n) k).mulVec v = v := by
    rw [← Matrix.mulVec_smul, ← hgv, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]; simp
  have hx0 : x ≠ 0 := fun h0 => hv.2 (by rw [← e, h0, zero_smul])
  have h2 := le g⁻¹ x⁻¹ (by rw [eq_inv_smul_iff₀ hx0, e])
  rw [norm_inv] at h2
  exact le_antisymm (le g x hgv) ((inv_le_one₀ (norm_pos_iff.2 hx0)).1 h2)

end UpperTheory.V.Af.IntGen
