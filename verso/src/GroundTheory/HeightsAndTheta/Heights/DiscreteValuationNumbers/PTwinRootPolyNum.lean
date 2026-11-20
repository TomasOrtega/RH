import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace RootPolynomialNumber

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hQ : rename Sum.inl G * rename Sum.inr Q = ∑ μ ∈ Q.support, Q.coeff μ • (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ))` using `by conv_lhs => rw [Q.as_sum]`. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `classNumAddHom (Sum.elim x L) [] W _ = _`. Rewrite using `[hQ, map_sum]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, smul_eq_mul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `classNum (Sum.elim x L) _ [] W = _`. Rewrite using `[plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective, classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]`.
-/
theorem classNum_rename_mul {N q : ℕ} (x : Fin N → K → ℤ) (L : Fin q → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x L) (rename Sum.inl G * rename Sum.inr Q) [] W =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
  classical
  have hQ : rename Sum.inl G * rename Sum.inr Q =
      ∑ μ ∈ Q.support, Q.coeff μ •
        (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ)) := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]
    ring
  change classNumAddHom (Sum.elim x L) [] W _ = _
  rw [hQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, smul_eq_mul]
  congr 1
  change classNum (Sum.elim x L) _ [] W = _
  rw [plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective,
    classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]

end RootPolynomialNumber

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a`. Establish `hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d`. Establish `h` using `(hG.rename_isHomogeneous (f := Fin.castAdd q)).mul (hQ.rename_isHomogeneous (f := Fin.natAdd N))`. Rewrite `h` using `[show c + (d - c) = d by omega]`. Then use the resulting hypothesis. Establish `hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) = Fin.append x L`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `induction i using Fin.addCases <;> simp`. Establish `hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) = rename Sum.inl G * rename Sum.inr Q`. Establish `e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Establish `e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[map_mul, rename_rename, rename_rename, e1, e2]`.

Establish `hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a)`. Use function extensionality and compare the values at `W`. Simplify using `[FlagTypings.divCycle_eq]`. Establish `hW : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) = ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (class …`. Introduce `W`.

Rewrite using `[BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W, hren, RootPolynomialNumber.classNum_rename_mul]`. Rewrite using `[BundleExamples.vEval_eq, hZ]`. Simplify using `only [hW]`. Establish `hfin : (Function.support (divCycle P (C a))).Finite`. Rewrite using `[← hZ, Finsupp.fun_support_eq]`.

Conclude with `Finset.finite_toSet _`. Rewrite using `[cycEval_eq_sum hfin]`. Simplify using `only [cycEval_eq_sum hfin, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem RootPolynomialNumber.proof : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  classical
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d := by
    have h := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h
  have hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) =
      Fin.append x L := by
    funext i
    induction i using Fin.addCases <;> simp
  have hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        rename Sum.inl G * rename Sum.inr Q := by
    have e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl := by
      funext i
      simp
    have e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr := by
      funext i
      simp
    rw [map_mul, rename_rename, rename_rename, e1, e2]
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hW : ∀ W : Ideal (MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
                                (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W,
      hren, RootPolynomialNumber.classNum_rename_mul]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [hW]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ, Finsupp.fun_support_eq]
    exact Finset.finite_toSet _
  rw [cycEval_eq_sum hfin]
  simp only [cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

end GroundTheory.Heights₂.Heights.NumbersDVR
