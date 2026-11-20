import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupTorsion

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

def pointCongr {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem pointCongr_some {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x y : F}
    (hxy : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

end Congr

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem isUnit_natCast_iff_residue_ne_zero (n : ℕ) : IsUnit (n : 𝒪) ↔ (n : ResidueField 𝒪) ≠ 0 := by
  rw [← map_natCast (residue 𝒪) n, ne_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_not]

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_zero_of_reduceHom_eq_zero {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) (P : E0 K W)
    (hnP : n • P = 0) (hP : reduceHom K W P = 0) : P = 0 := by
  have h1 := (reduceHom_eq_zero_iff K W P).mp hP
  have h2 : n • (P : (curveK K W).Point) = 0 := by
    rw [← AddSubgroup.coe_nsmul, hnP, AddSubgroup.coe_zero]
  exact Subtype.ext (eq_zero_of_mem_E1_of_nsmul_eq_zero K W
    ((isUnit_natCast_iff_residue_ne_zero n).mpr hn) h1 h2)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem reduceHom_injOn_torsion {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) {P Q : E0 K W}
    (hP : n • P = 0) (hQ : n • Q = 0) (h : reduceHom K W P = reduceHom K W Q) : P = Q := by
  have := eq_zero_of_reduceHom_eq_zero K W hn (P - Q) (by rw [nsmul_sub, hP, hQ, sub_zero])
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp this

def reduceTorsionHom (n : ℕ) :
    AddSubgroup.torsionBy (E0 K W) n →+ AddSubgroup.torsionBy (curveRed W).Point n :=
  ((reduceHom K W).comp (AddSubgroup.torsionBy (E0 K W) n).subtype).codRestrict _ fun P => by
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
      AddSubgroup.subtype_apply, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_reduceTorsionHom_apply (n : ℕ) (P : AddSubgroup.torsionBy (E0 K W) n) :
    (reduceTorsionHom K W n P : (curveRed W).Point) = reduceHom K W P :=
  rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem reduceTorsionHom_bijective {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) :
    Function.Bijective (reduceTorsionHom K W n) := by
  have hu := (isUnit_natCast_iff_residue_ne_zero n).mpr hn
  refine ⟨fun P Q h => ?_, fun R => ?_⟩
  · have h' := congrArg Subtype.val h
    rw [coe_reduceTorsionHom_apply, coe_reduceTorsionHom_apply] at h'
    exact Subtype.ext (reduceHom_injOn_torsion K W hn (AddSubgroup.torsionBy.nsmul_iff.mp P.2)
      (AddSubgroup.torsionBy.nsmul_iff.mp Q.2) h')
  · obtain ⟨P, hP⟩ := reduceHom_surjective K W (R : (curveRed W).Point)
    have hnP : (((n • P : E0 K W)) : (curveK K W).Point) ∈ E1 K W := by
      rw [← reduceHom_eq_zero_iff, map_nsmul, hP, AddSubgroup.torsionBy.nsmul_iff.mp R.2]
    obtain ⟨T, hT⟩ := (E1_nsmul_bijective K W hu).2 ⟨_, hnP⟩
    have hT0 : (T : (curveK K W).Point) ∈ E0 K W := E1_le_E0 K W T.2
    have hT' : n • (T : (curveK K W).Point) = ((n • P : E0 K W) : (curveK K W).Point) := by
      have := congrArg Subtype.val hT
      simpa using this
    set T' : E0 K W := ⟨T, hT0⟩
    have hTred : reduceHom K W T' = 0 := (reduceHom_eq_zero_iff K W T').mpr T.2
    refine ⟨⟨P - T', ?_⟩, Subtype.ext ?_⟩
    · rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, sub_eq_zero]
      exact Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_nsmul]; exact hT'.symm)
    · rw [coe_reduceTorsionHom_apply]
      change reduceHom K W (P - T') = _
      rw [map_sub, hP, hTred, sub_zero]

def e0TorsionEquiv {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) :
    AddSubgroup.torsionBy (E0 K W) n ≃+ AddSubgroup.torsionBy (curveRed W).Point n :=
  AddEquiv.ofBijective (reduceTorsionHom K W n) (reduceTorsionHom_bijective K W hn)

section Good

end Good

end

end GroundTheory.Arith.Abelian
