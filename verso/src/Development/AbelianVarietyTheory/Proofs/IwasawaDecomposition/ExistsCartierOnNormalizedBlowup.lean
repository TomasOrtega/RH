import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

/- English proof (translation)
Introduce `i`. Use `isRegularFn_iff_germ.2 fun y hy => ?_` and prove the remaining obligations. Use `haveI := hN y`. Use `mem_nonZeroDivisors_of_ne_zero fun h0 => ?_` and prove the remaining obligations. Establish `e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) = (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0` using `by rw [h0, map_zero]`.

Take `⟨W, hW, i₁, i₂, e'⟩` from `N.presheaf.germ_eq y hy hy _ _ e`. Take `⟨z, hzW, hzO⟩` from `hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩`. Use `haveI := hN z`. Establish `hzU : z ∈ ν ⁻¹ᵁ D.U i` using `i₁.le hzW`. Establish `hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0`.

Use `congrArg (N.presheaf.germ W z hzW).hom e'` as an intermediate fact. Simplify using `using this`. Establish `hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i))`. Establish `h1 : ν z ∈ X'.basicOpen (D.f i)`. Assume the negation of the conclusion as `h`.

Conclude with `hzO ((D.mem_support_iff i hzU).2 h)`. Conclude with `(X'.mem_basicOpen _ _ hzU).1 h1`. Establish `hu` using `hunit.map (ν.stalkMap z).hom`. Rewrite `hu` using `[← EffCartierData.germ_app ν (D.f i) z hzU, hz0]`. Conclude with `not_isUnit_zero hu`.
-/
theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

/- English proof (translation)
Introduce `_ _ hbl _ hN _ hd`. Take `⟨D, hD⟩` from `EffCartierData.exists_idealSheaf_eq hbl.1`. Establish `hK : D.KeepsRegular ν`. Use `D.keepsRegular_of_dense ν (fun y => (hN y).1) (hd.mono fun z hz => ?_)` and prove the remaining obligations. Use `show ν z ∉ D.idealSheaf.support`.

Rewrite using `[hD, Scheme.IdealSheafData.support_comap]`. Conclude with `hz`. Use `⟨D.pull ν hK, ?_⟩` and prove the remaining obligations. Rewrite using `[EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]`.
-/
theorem effCartier_comap_blowup_normal (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0})
    (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') :
    IsProjOver s → Dense ((J.support : Set X)ᶜ) → FinalTheorems.Blowup b J → IsFinite ν →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsIso (ν ∣_ (b ⁻¹ᵁ J.support.compl)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ J.support.compl) : N.Opens) : Set N) →
    ∃ EX : GlobalTheory.EffCartierData N, EX.idealSheaf = J.comap (ν ≫ b) := by
  intro _ _ hbl _ hN _ hd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hbl.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hN y).1) (hd.mono fun z hz => ?_)
    show ν z ∉ D.idealSheaf.support
    rw [hD, Scheme.IdealSheafData.support_comap]
    exact hz
  refine ⟨D.pull ν hK, ?_⟩
  rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]

end GlobalTheory
