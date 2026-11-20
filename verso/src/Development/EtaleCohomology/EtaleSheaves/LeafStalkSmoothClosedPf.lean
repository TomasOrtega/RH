import Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order

namespace LateralTheory.E.LeafStalkSmoothClosedPf

/- English proof (translation)
Set `` to `specializationOrder X`. Establish `h` using `coheight_le_krullDim (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)`. Rewrite `h` using `[coheight_orderIso]`. Then use the resulting hypothesis.
-/
theorem coheight_le_topDim {X : Scheme.{0}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rwa [coheight_orderIso] at h

/- English proof (translation)
Introduce `hF`. Set `` to `hF.toField`. Establish `h0 : ringKrullDim (X.presheaf.stalk y) = 0` using `ringKrullDim_eq_zero_of_field _`. Rewrite `h0` using `[ringKrullDim_stalk_eq_coheight]`. Establish `hc : coheight y = 0` using `by exact_mod_cast h0`.

Rewrite `hc` using `[coheight_eq_zero]`. Establish `h1 : y ≤ genericPoint X` using `genericPoint_specializes y`. Establish `h2 : genericPoint X ≤ y` using `hc h1`. Conclude with `hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq`.
-/
theorem stalk_not_isField {X : Scheme.{0}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk y) := by
  intro hF
  let := hF.toField
  have h0 : ringKrullDim (X.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  rw [coheight_eq_zero] at hc
  have h1 : y ≤ genericPoint X := genericPoint_specializes y
  have h2 : genericPoint X ≤ y := hc h1
  exact hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq

/- English proof (translation)
Establish `hc : coheight y ≤ 1`. Use `(coheight_le_topDim y).trans hd.le` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `: Ring.KrullDimLE 1 (X.presheaf.stalk y)` using `krullDimLE_of_coheight_le hc`. Establish `: Ring.DimensionLEOne (X.presheaf.stalk y)` using `⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩`.

Establish `: IsDedekindDomain (X.presheaf.stalk y)` using `{}`. Conclude with `((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 2 0).mp this`.
-/
theorem stalk_dvr {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (y : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk y)) (hd : topologicalKrullDim X = 1)
    (hy : y ≠ genericPoint X) : IsDiscreteValuationRing (X.presheaf.stalk y) := by
  have hc : coheight y ≤ 1 := by
    have := (coheight_le_topDim y).trans hd.le
    exact_mod_cast this
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hc
  have : Ring.DimensionLEOne (X.presheaf.stalk y) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk y) := {}
  exact ((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 2 0).mp this

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `Ω _ _ C c _ hc hn hd y hy`. Establish `: IsLocallyNoetherian C` using `LocallyOfFiniteType.isLocallyNoetherian c`. Use `hn y` as an intermediate fact. Establish `: IsDiscreteValuationRing (C.presheaf.stalk y)` using `stalk_dvr y (hn y) hd hy`. Establish `hE` using `LocallyOfFiniteType.stalkMap c y`.

Use `algebraize [(c.stalkMap y).hom]`. Set `p : Spec (CommRingCat.of Ω)` to `c y`. Set `K'` to `(Spec.structureSheaf Ω).presheaf.stalk p`. Set `e : Ω ≃ₐ[Ω] K'` to `IsLocalization.atUnits _ p.asIdeal.primeCompl (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))`. Establish `: Algebra.IsAlgebraic Ω K'` using `.of_injective e.symm.toAlgHom e.symm.injective`.

Set `: Field K'` to `(e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField`. Set `: Field ((Sp Ω).presheaf.stalk (c y))` to `this`. Establish `: PerfectField ((Sp Ω).presheaf.stalk (c y))` using `Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)`. Conclude with `GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _`.
-/
theorem LeafStalkSmoothClosed_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := by
  intro Ω _ _ C c _ hc hn hd y hy
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have := hn y
  have : IsDiscreteValuationRing (C.presheaf.stalk y) := stalk_dvr y (hn y) hd hy
  have hE := LocallyOfFiniteType.stalkMap c y
  algebraize [(c.stalkMap y).hom]
  let p : Spec (CommRingCat.of Ω) := c y
  let K' := (Spec.structureSheaf Ω).presheaf.stalk p
  let e : Ω ≃ₐ[Ω] K' := IsLocalization.atUnits _ p.asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic Ω K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField
  let : Field ((Sp Ω).presheaf.stalk (c y)) := this
  have : PerfectField ((Sp Ω).presheaf.stalk (c y)) :=
    Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)
  exact GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _

end LateralTheory.E.LeafStalkSmoothClosedPf
