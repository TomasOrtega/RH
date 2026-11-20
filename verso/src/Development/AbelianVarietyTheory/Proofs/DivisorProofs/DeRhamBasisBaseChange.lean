import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

/- English proof (translation)
Introduce `hAb E _ _ _ c 𝔠 R X₀ X p cm hpull n eH`. Establish `h : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p` using `hpull.grp`. Establish `hm : (GlobalTheory.Published.AbelianDeRham.bcMor h).IsBC` using `(hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p h).1`. Take `⟨hfin, hproj, -⟩` from `GlobalTheory.Published.AbelianDeRham.Free.prim hAb.1 X₀.ab X₀.dim`. Set `b : Module.Basis (Fin n) R (HdR X₀.A)` to `Module.Basis.ofEquivFun eH`.

Set `cb : Module.Basis (Fin n) R (primDR X₀.A)` to `b.dualBasis.map (Module.evalEquiv R (primDR X₀.A)).symm`. Establish `hcb : ∀ i j, b i (cb j) = if j = i then 1 else 0`. Introduce `i j`. Simplify using `[cb, Finsupp.single_apply, eq_comm]`. Set `L : ℂ ⊗[R] primDR X₀.A ≃ₗ[ℂ] primDR X.A` to `LinearEquiv.ofBijective _ hm`.

Set `c' : Module.Basis (Fin n) ℂ (primDR X.A)` to `(Algebra.TensorProduct.basis ℂ cb).map L`. Establish `hc' : ∀ j, c' j = (GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j)` using `fun j ↦ by`. Rewrite using `[Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]`. Conclude with `one_smul ℂ ((GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j))`. Set `B` to `c'.dualBasis`.

Establish `hB : ∀ i, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (b i) (B i)`. Introduce `i x`. Rewrite using `[← cb.sum_repr x]`. Simplify using `only [map_sum, map_smulₛₗ, ← hc', B, Module.Basis.dualBasis_apply_self, hcb, smul_eq_mul]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hb : ∀ i, b i = eH.symm (Pi.single i 1)` using `fun i ↦ by simp [b]`. Establish `hsum : ∀ v : Fin n → R, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (∑ k, v k • b k) (∑ k, ((v k : R) : ℂ) • B k)`. Introduce `v x`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, hB _, map_sum, smul_eq_mul, map_mul]`.

Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[hB k x]`. Both sides reduce to the same expression. Use `⟨B, fun a α _ hα i ↦ ?_⟩` and prove the remaining obligations. Use `haveI := cm.hom a`.

Establish `e1` using `GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor h) (cm.act a) α hα.symm (hB i)`. Use `set v := (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) with hv`. Establish `e2 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = ∑ k, v k • b k`. Establish `e3 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = eH.symm v` using `by show act (dp0 R) (𝟙 _) cm a (b i) = _`. Rewrite using `[hv, hb i]`.

Simplify using the standard rewrite rules. Rewrite using `[e3, ← b.sum_equivFun (eH.symm v)]`. Simplify using `[b]`. Rewrite `e1` using `[e2]`. Conclude with `hm.unique e1 (hsum v)`.
-/
theorem exists_basis_push_eq_sum : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  intro hAb E _ _ _ c 𝔠 R X₀ X p cm hpull n eH
  have h : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  have hm : (GlobalTheory.Published.AbelianDeRham.bcMor h).IsBC := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p h).1
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hAb.1 X₀.ab X₀.dim
  let b : Module.Basis (Fin n) R (HdR X₀.A) := Module.Basis.ofEquivFun eH
  let cb : Module.Basis (Fin n) R (primDR X₀.A) :=
    b.dualBasis.map (Module.evalEquiv R (primDR X₀.A)).symm
  have hcb : ∀ i j, b i (cb j) = if j = i then 1 else 0 := by
    intro i j
    simp [cb, Finsupp.single_apply, eq_comm]
  let L : ℂ ⊗[R] primDR X₀.A ≃ₗ[ℂ] primDR X.A := LinearEquiv.ofBijective _ hm
  let c' : Module.Basis (Fin n) ℂ (primDR X.A) := (Algebra.TensorProduct.basis ℂ cb).map L
  have hc' : ∀ j, c' j = (GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j) := fun j ↦ by
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact one_smul ℂ ((GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j))
  let B := c'.dualBasis
  have hB : ∀ i, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (b i) (B i) := by
    intro i x
    rw [← cb.sum_repr x]
    simp only [map_sum, map_smulₛₗ, ← hc', B, Module.Basis.dualBasis_apply_self, hcb, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp
  have hb : ∀ i, b i = eH.symm (Pi.single i 1) := fun i ↦ by simp [b]
  have hsum : ∀ v : Fin n → R, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (∑ k, v k • b k)
      (∑ k, ((v k : R) : ℂ) • B k) := by
    intro v x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hB _, map_sum, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hB k x]
    rfl
  refine ⟨B, fun a α _ hα i ↦ ?_⟩
  haveI := cm.hom a
  have e1 := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor h) (cm.act a) α hα.symm (hB i)
  set v := (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) with hv
  have e2 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = ∑ k, v k • b k := by
    have e3 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = eH.symm v := by
      show act (dp0 R) (𝟙 _) cm a (b i) = _
      rw [hv, hb i]
      simp
    rw [e3, ← b.sum_equivFun (eH.symm v)]
    simp [b]
  rw [e2] at e1
  exact hm.unique e1 (hsum v)

end GlobalTheory.DRLine
