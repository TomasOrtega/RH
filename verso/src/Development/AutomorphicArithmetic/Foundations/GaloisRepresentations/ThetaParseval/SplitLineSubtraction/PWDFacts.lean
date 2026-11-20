import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]`.
-/
private theorem scaleRoots_X_sub_C' (a d : ℂ) : (X - C a : ℂ[X]).scaleRoots d = X - C (a * d) := by
  rw [sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]

/- English proof (translation)
Unfold `unrPol`. Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a S ih`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, scaleRoots_X_sub_C', mul_zpow]`.
-/
private theorem scaleRoots_unrPol (S : Multiset ℂ) (m : ℤ) (c : ℂ) :
    (unrPol S m).scaleRoots (c ^ (-m)) = unrPol (S.map (· * c)) m := by
  unfold unrPol
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih,
      scaleRoots_X_sub_C', mul_zpow]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h x y`. Proceed by induction on `x using WD.ind with | _ n a => ?_`. Proceed by induction on `y using WD.ind with | _ m b => ?_`. Use `⟨?_, fun g => WD.charPol_lpSum _ _ g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WD.lpSum_mk, WD.unr_mk, WD.unr_mk]`.

Unfold `WDRep.Unr`. Simplify using `only [WDRep.sum]`. Introduce and unpack `⟨hN, hρ⟩`. Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Establish `hv` using `congrArg (fun f => (f (v, 0)).1) hN`. Simplify using `using hv`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Establish `hv` using `congrArg (fun f => (f (v, 0)).1) (hρ σ)`. Simplify `hv` using `[Representation.prod]`. Rewrite using `[WD.lpChar_mk, WD.unr_mk, WD.unr_mk, WD.unr_mk]`. Unfold `WDRep.Unr`. Simplify using `only [WDRep.tensor]`.

Introduce and unpack `⟨ha, ha'⟩ ⟨hb, hb'⟩`. Use `⟨by simp [ha, hb], fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[Representation.tprod_apply, ha' σ, hb' σ]`. Simplify using the standard rewrite rules. Introduce `g S c hx hy`.

Rewrite `hx`, `hy` using `[WD.charPol_mk]`. Rewrite using `[WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ]`. Establish `hm : m = 1`. Establish `hd` using `congrArg Polynomial.natDegree hy`. Rewrite `hd` using `[LinearMap.charpoly_natDegree]`.

Unfold `unrPol at hd`. Simplify using `using hd`. Substitute `hm` using the available equality. Establish `hb : b.ρ g = c ^ (-deg g) • (1 : Module.End ℂ (Fin 1 → ℂ))`. Establish `hct` using `LinearMap.aeval_self_charpoly (b.ρ g)`.

Rewrite `hct` using `[hy]`. Unfold `unrPol at hct`. Simplify using `only [Multiset.map_singleton, Multiset.prod_singleton, map_sub, aeval_X, aeval_C] at hct`. Rewrite `hct` using `[sub_eq_zero]`. Rewrite using `[hct, Algebra.algebraMap_eq_smul_one]`.

Establish `ht : c ^ (-deg g) ≠ 0`. Introduce `ht0`. Establish `h0 : b.ρ g = 0`. Rewrite using `[hb, ht0, zero_smul]`. Establish `h1 : b.ρ (g * g⁻¹) = 1`.

Rewrite using `[mul_inv_cancel, map_one]`. Rewrite `h1` using `[map_mul, h0, zero_mul]`. Conclude with `zero_ne_one h1`. Rewrite using `[hb, TensorProduct.map_smul_right, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_smul_eq_scaleRoots _ ht, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_map_one (by simp), hx, scaleRoots_unrPol]`.
-/
theorem UpperTheory.Gal.TP.Sub.wDFacts_holds :
    WDFacts := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with | _ n a => ?_
  induction y using WD.ind with | _ m b => ?_
  refine ⟨?_, fun g => WD.charPol_lpSum _ _ g, ?_, ?_⟩
  · rw [WD.lpSum_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.sum]
    rintro ⟨hN, hρ⟩
    refine ⟨?_, fun σ => ?_⟩
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) hN
      simpa using hv
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) (hρ σ)
      simpa [Representation.prod] using hv
  · rw [WD.lpChar_mk, WD.unr_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.tensor]
    rintro ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], fun σ => ?_⟩
    rw [Representation.tprod_apply, ha' σ, hb' σ]
    simp
  · intro g S c hx hy
    rw [WD.charPol_mk] at hx hy
    rw [WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ]
    have hm : m = 1 := by
      have hd := congrArg Polynomial.natDegree hy
      rw [LinearMap.charpoly_natDegree] at hd
      unfold unrPol at hd
      simpa using hd
    subst hm
    have hb : b.ρ g = c ^ (-deg g) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
      have hct := LinearMap.aeval_self_charpoly (b.ρ g)
      rw [hy] at hct
      unfold unrPol at hct
      simp only [Multiset.map_singleton, Multiset.prod_singleton, map_sub, aeval_X, aeval_C] at hct
      rw [sub_eq_zero] at hct
      rw [hct, Algebra.algebraMap_eq_smul_one]
    have ht : c ^ (-deg g) ≠ 0 := by
      intro ht0
      have h0 : b.ρ g = 0 := by
        rw [hb, ht0, zero_smul]
      have h1 : b.ρ (g * g⁻¹) = 1 := by
        rw [mul_inv_cancel, map_one]
      rw [map_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    rw [hb, TensorProduct.map_smul_right, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_smul_eq_scaleRoots _ ht,
      GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_map_one (by simp), hx, scaleRoots_unrPol]
