import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `hW hS E _ _ _ n π hc`. Establish `nice : ∀ φ ∈ π.V, Nice φ.1`. Introduce `φ hφ`. Establish `hl` using `(π.cusp φ hφ).1.level`. Rewrite `hφ` using `[← Fb.map_carrier]`.

Take `⟨ψ, hψ, rfl⟩` from `hφ`. Use `⟨ψ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms (Fb.carrier_le_central π hc hψ), ψ.2.1.isLeftInvariant, ψ.2.2, ?_⟩` and prove the remaining obligations. Set `V : Subgroup (GL (Fin n) (Af E))` to `{ carrier := {k | TR.finRep E n k (Fb.ofCusp E n ψ) = Fb.ofCusp E n ψ} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`.

Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Conclude with `⟨⟨V, hl⟩, fun g v hv => congrFun (congrArg Subtype.val hv) g⟩`.

Use `⟨nice, ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Establish `N` using `nice φ hφ`. Establish `hg : ∃ g, whittaker φ.1 g ≠ 0`. Assume the negation of the conclusion as `h`.

Use `h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_ fun g => not_not.1 fun h' => h ⟨g, h'⟩))` and prove the remaining obligations. Rewrite using `[Fb.finEmb_eq]`. Conclude with `N.level`. Take `⟨g, hg⟩` from `hg`. Rewrite `hg` using `[← TR.infGL_mul_finGL g]`.

Generalize the expression as in `GeneralLinearGroup.map (pInf E) g = y at hg`. Generalize the expression as in `GeneralLinearGroup.map (pFin E) g = k at hg`. Establish `hφ'` using `π.stable (.fin k) φ hφ`. Use `⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩` and prove the remaining obligations. Establish `e : (TR.act (.fin k) φ).1 = fun x => φ.1 (x * finGL E n k)` using `rfl`.

Rewrite using `[e]`. Simplify `hg` using `only [whittaker, mul_assoc]`.
-/
theorem UpperTheory.V.Af.Smo.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.SeedConv → UpperTheory.V.Af.Smo.Seed := by
  intro hW hS E _ _ _ n π hc
  have nice : ∀ φ ∈ π.V, Nice φ.1 := by
    intro φ hφ
    have hl := (π.cusp φ hφ).1.level
    rw [← Fb.map_carrier] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    refine ⟨ψ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms (Fb.carrier_le_central π hc hψ),
      ψ.2.1.isLeftInvariant, ψ.2.2, ?_⟩
    let V : Subgroup (GL (Fin n) (Af E)) :=
      { carrier := {k | TR.finRep E n k (Fb.ofCusp E n ψ) = Fb.ofCusp E n ψ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact ⟨⟨V, hl⟩, fun g v hv => congrFun (congrArg Subtype.val hv) g⟩
  refine ⟨nice, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← TR.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := π.stable (.fin k) φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (TR.act (.fin k) φ).1 = fun x => φ.1 (x * finGL E n k) := rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
