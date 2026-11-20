import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

/- English proof (translation)
Introduce `N`. Establish `h1 : IsLocallyConstant (fun g => Units.map (Ideal.Quotient.mk (I ^ N) : R →+* R ⧸ I ^ N).toMonoidHom (Ψ g))` using `IsLocallyConstant.desc _ (fun u : (R ⧸ I ^ N)ˣ => (u : R ⧸ I ^ N)) (by simpa [Function.comp_def] using h N) (fun a b hab => Units.ext hab)`. Establish `h2` using `h1.comp (fun u => ((u ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Simplify using `only [Function.comp_apply, ← map_zpow, Units.coe_map]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Loc.adicCont_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  intro N
  have h1 : IsLocallyConstant (fun g => Units.map (Ideal.Quotient.mk (I ^ N) : R →+* R ⧸ I ^ N).toMonoidHom (Ψ g)) :=
    IsLocallyConstant.desc _ (fun u : (R ⧸ I ^ N)ˣ => (u : R ⧸ I ^ N)) (by simpa [Function.comp_def] using h N)
      (fun a b hab => Units.ext hab)
  have h2 := h1.comp (fun u => ((u ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N))
  convert h2 using 1
  funext g
  simp only [Function.comp_apply, ← map_zpow, Units.coe_map]
  rfl

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ D U`. Establish `hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((D.Ψ g ^ j : Oˣ) : O)` using `fun j => adicCont_zpow _ _ D.Ψ_cont j`. Take `⟨f, hf, hu⟩` from `(U.rep O).2 (baseLift O D.η D.Ψ hΨ) trivial`. Use `⟨f, congrArg GLift.hom hf, fun y hy => hu y (GLift.ext hy)⟩` and prove the remaining obligations.
-/
theorem UpperTheory.V.Loc.univEx :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), ∃! x, IsBase D.η D.Ψ U.r.hom x := by
  intro l _ O _ _ _ _ _ _ _ D U
  have hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((D.Ψ g ^ j : Oˣ) : O) :=
    fun j => adicCont_zpow _ _ D.Ψ_cont j
  obtain ⟨f, hf, hu⟩ := (U.rep O).2 (baseLift O D.η D.Ψ hΨ) trivial
  refine ⟨f, congrArg GLift.hom hf, fun y hy => hu y (GLift.ext hy)⟩
