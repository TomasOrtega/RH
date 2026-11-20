import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `A _ L₀ L _ hidx`. Set `H : AddSubgroup L` to `L₀.addSubgroupOf L`. Use `haveI : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero hidx`. Set `r : L ⧸ H → A` to `fun q => ((Quotient.out q : L) : A)`. Establish `hr : Function.Injective r` using `Subtype.coe_injective.comp Quotient.out_injective`.

Use `⟨Finset.univ.image r, Finset.univ_nonempty.image r, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(Quotient.out q).2`. Introduce `χ hχ ⟨x, hxL, hx⟩`.

Establish `hχeq : ∀ a b : L, (a : L ⧸ H) = b → χ a = χ b`. Introduce `a b hab`. Establish `hm : -a + b ∈ H` using `QuotientAddGroup.eq.mp hab`. Establish `hm' : ((-a + b : L) : A) ∈ L₀` using `AddSubgroup.mem_addSubgroupOf.mp hm`. Establish `h1 : χ ((-a + b : L) : A) = 1` using `hχ _ hm'`.

Establish `h2 : (b : A) = a + ((-a + b : L) : A)` using `by simp`. Rewrite using `[h2, AddChar.map_add_eq_mul, h1, mul_one]`. Rewrite using `[Finset.sum_image (fun q _ q' _ h => hr h)]`. Set `xL : L` to `⟨x, hxL⟩`. Establish `hshift : ∀ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) = χ (r q) * χ x`.

Introduce `q`. Establish `h3 : ((Quotient.out (q + (xL : L ⧸ H)) : L) : L ⧸ H) = ((Quotient.out q + xL : L) : L ⧸ H)`. Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']`. Establish `h4` using `hχeq _ _ h3`. Simplify using `only [r]`.

Rewrite using `[h4, AddSubgroup.coe_add, AddChar.map_add_eq_mul]`. Establish `hS : ∑ q : L ⧸ H, χ (r q) = (∑ q : L ⧸ H, χ (r q)) * χ x`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : (∑ q : L ⧸ H, χ (r q)) * (χ x - 1) = 0`. Rewrite using `[mul_sub, mul_one, ← hS, sub_self]`.

Break down `mul_eq_zero.mp h5 with h6 | h6` into its components or cases. Conclude with `h6`. Conclude with `absurd (sub_eq_zero.mp h6) hx`.
-/
theorem UpperTheory.V.Af.Smo.avgChar :
    UpperTheory.V.Af.Smo.AvgChar := by
  intro A _ L₀ L _ hidx
  classical
  let H : AddSubgroup L := L₀.addSubgroupOf L
  haveI : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero hidx
  let r : L ⧸ H → A := fun q => ((Quotient.out q : L) : A)
  have hr : Function.Injective r := Subtype.coe_injective.comp Quotient.out_injective
  refine ⟨Finset.univ.image r, Finset.univ_nonempty.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro χ hχ ⟨x, hxL, hx⟩
    have hχeq : ∀ a b : L, (a : L ⧸ H) = b → χ a = χ b := by
      intro a b hab
      have hm : -a + b ∈ H := QuotientAddGroup.eq.mp hab
      have hm' : ((-a + b : L) : A) ∈ L₀ := AddSubgroup.mem_addSubgroupOf.mp hm
      have h1 : χ ((-a + b : L) : A) = 1 := hχ _ hm'
      have h2 : (b : A) = a + ((-a + b : L) : A) := by simp
      rw [h2, AddChar.map_add_eq_mul, h1, mul_one]
    rw [Finset.sum_image (fun q _ q' _ h => hr h)]
    let xL : L := ⟨x, hxL⟩
    have hshift : ∀ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) = χ (r q) * χ x := by
      intro q
      have h3 : ((Quotient.out (q + (xL : L ⧸ H)) : L) : L ⧸ H) = ((Quotient.out q + xL : L) : L ⧸ H) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have h4 := hχeq _ _ h3
      simp only [r]
      rw [h4, AddSubgroup.coe_add, AddChar.map_add_eq_mul]
    have hS : ∑ q : L ⧸ H, χ (r q) = (∑ q : L ⧸ H, χ (r q)) * χ x := by
      calc ∑ q : L ⧸ H, χ (r q) = ∑ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) :=
            (Equiv.sum_comp (Equiv.addRight (xL : L ⧸ H)) (fun q => χ (r q))).symm
        _ = ∑ q : L ⧸ H, χ (r q) * χ x := Finset.sum_congr rfl (fun q _ => hshift q)
        _ = (∑ q : L ⧸ H, χ (r q)) * χ x := (Finset.sum_mul _ _ _).symm
    have h5 : (∑ q : L ⧸ H, χ (r q)) * (χ x - 1) = 0 := by
      rw [mul_sub, mul_one, ← hS, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h6
    · exact absurd (sub_eq_zero.mp h6) hx
