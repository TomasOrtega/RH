import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `Z Y g _ V _ _ _ y`. Establish `hP : IsProper g` using `inferInstance`. Establish `hV : ValuativeCriterion g`. Rewrite `hP` using `[IsProper.eq_valuativeCriterion]`. Conclude with `hP.1.1.1`.

Set `e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V)` to `Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz show (e ≫ z) ≫ g = e ≫ y`. Rewrite using `[Category.assoc, show z ≫ g = y from hz]`. Introduce `z₁ hz₁ z₂ hz₂ h`.

Establish `h₁ : z₁ ≫ g = y` using `hz₁`. Establish `h₂ : z₂ ≫ g = y` using `hz₂`. Establish `h' : e ≫ z₁ = e ≫ z₂` using `h`. Set `S : ValuativeCommSq g` to `⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩`. Establish `hu` using `ValuativeCriterion.uniqueness hV S`.

Use `@Subsingleton.elim _ hu ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩` as an intermediate fact. Conclude with `congrArg CommSq.LiftStruct.l this`. Introduce `x hx`. Establish `hx' : x ≫ g = e ≫ y` using `hx`. Set `S : ValuativeCommSq g` to `⟨V, FractionRing V, x, y, ⟨hx'⟩⟩`.

Take `⟨⟨l⟩⟩` from `ValuativeCriterion.existence hV S`. Conclude with `⟨l.l, l.fac_right, l.fac_left⟩`.
-/
theorem UpperTheory.Gal.Mod.secGen :
    SecGen := by
  intro Z Y g _ V _ _ _ y
  have hP : IsProper g := inferInstance
  have hV : ValuativeCriterion g := by
    rw [IsProper.eq_valuativeCriterion] at hP
    exact hP.1.1.1
  let e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    show (e ≫ z) ≫ g = e ≫ y
    rw [Category.assoc, show z ≫ g = y from hz]
  · intro z₁ hz₁ z₂ hz₂ h
    have h₁ : z₁ ≫ g = y := hz₁
    have h₂ : z₂ ≫ g = y := hz₂
    have h' : e ≫ z₁ = e ≫ z₂ := h
    let S : ValuativeCommSq g :=
      ⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩
    have hu := ValuativeCriterion.uniqueness hV S
    have := @Subsingleton.elim _ hu
      ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩
    exact congrArg CommSq.LiftStruct.l this
  · intro x hx
    have hx' : x ≫ g = e ≫ y := hx
    let S : ValuativeCommSq g := ⟨V, FractionRing V, x, y, ⟨hx'⟩⟩
    obtain ⟨⟨l⟩⟩ := ValuativeCriterion.existence hV S
    exact ⟨l.l, l.fac_right, l.fac_left⟩
