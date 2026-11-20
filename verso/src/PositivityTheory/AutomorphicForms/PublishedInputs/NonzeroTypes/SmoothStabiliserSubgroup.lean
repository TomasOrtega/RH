import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace SmoothStabiliserSubgroup

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rightReg_apply' {K : Type} [Group K] (k' : K) (φ : K → ℂ) (g : K) :
    rightReg ℂ K ℂ k' φ g = φ (g * k') := rfl

def stab {K : Type} [Group K] (φ : K → ℂ) : Subgroup K where
  carrier := {k' | rightReg ℂ K ℂ k' φ = φ}
  one_mem' := by
    show rightReg ℂ K ℂ 1 φ = φ
    funext g
    rw [rightReg_apply', mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    have hb' : rightReg ℂ K ℂ b φ = φ := hb
    show rightReg ℂ K ℂ (a * b) φ = φ
    funext g
    have h1 := congrFun hb' (g * a)
    have h2 := congrFun ha' g
    rw [rightReg_apply'] at h1 h2 ⊢
    rw [← mul_assoc, h1, h2]
  inv_mem' := by
    intro a ha
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    show rightReg ℂ K ℂ a⁻¹ φ = φ
    funext g
    have h1 := congrFun ha' (g * a⁻¹)
    rw [rightReg_apply', inv_mul_cancel_right] at h1
    rw [rightReg_apply']
    exact h1.symm

end SmoothStabiliserSubgroup

/- English proof (translation)
Introduce `k _ _ _ _ n G hKC h1 φ hφ`. Establish `hU : IsOpen ((Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev)` using `hKC.preimage continuous_subtype_val`. Establish `hsub : (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev ⊆ (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n)))`. Introduce `u hu`. Use `show rightReg ℂ ↥(KO k (Fin n)) ℂ u φ = φ`.

Use function extensionality and compare the values at `g`. Rewrite using `[SmoothStabiliserSubgroup.rightReg_apply']`. Conclude with `hφ.2 g u hu`. Establish `h1mem : (1 : ↥(KO k (Fin n))) ∈ (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev` using `h1`. Establish `hn : (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) ∈ nhds (1 : ↥(KO k (Fin n)))` using `Filter.mem_of_superset (hU.mem_nhds h1mem) hsub`.

Conclude with `(SmoothStabiliserSubgroup.stab φ).isOpen_of_mem_nhds hn`.
-/
theorem smoothVectorsFixed_holds : SmoothVectorsFixedByCongruence := by
  intro k _ _ _ _ n G hKC h1 φ hφ
  have hU : IsOpen ((Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev) :=
    hKC.preimage continuous_subtype_val
  have hsub : (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev ⊆
      (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) := by
    intro u hu
    show rightReg ℂ ↥(KO k (Fin n)) ℂ u φ = φ
    funext g
    rw [SmoothStabiliserSubgroup.rightReg_apply']
    exact hφ.2 g u hu
  have h1mem : (1 : ↥(KO k (Fin n))) ∈ (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev := h1
  have hn : (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) ∈ nhds (1 : ↥(KO k (Fin n))) :=
    Filter.mem_of_superset (hU.mem_nhds h1mem) hsub
  exact (SmoothStabiliserSubgroup.stab φ).isOpen_of_mem_nhds hn

end UpperTheory.NonzeroTypeTheory
