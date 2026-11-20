import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.GenFibre

/- English proof (translation)
Establish `: Ring.KrullDimLE 1 R` using `Ring.krullDimLE_iff.2 hR.le`. Establish `hrad` using `(Ideal.isRadical_iff_quotient_reduced _).2 hred`. Use `le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ha')` and prove the remaining obligations. Rewrite using `[← hrad.radical, Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations.

Introduce and unpack `P ⟨hP, hPp⟩`. Establish `hne : P ≠ ⊥` using `fun h => ha (by`. Use `hP (Ideal.mem_span_singleton_self a)` as an intermediate fact. Rewrite using `[h, Ideal.mem_bot] at this)` and apply the resulting hypothesis. Conclude with `(IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hne)).ge`.
-/
theorem maximalIdeal_eq_span_of_isReduced {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) {a : R} (ha : a ≠ 0) (ha' : a ∈ maximalIdeal R)
    (hred : _root_.IsReduced (R ⧸ Ideal.span {a})) : maximalIdeal R = Ideal.span {a} := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 hR.le
  have hrad := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ha')
  rw [← hrad.radical, Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP, hPp⟩
  have hne : P ≠ ⊥ := fun h => ha (by
    have := hP (Ideal.mem_span_singleton_self a)
    rwa [h, Ideal.mem_bot] at this)
  exact (IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hne)).ge

/- English proof (translation)
Take `⟨b, z, rfl⟩ : ∃ (b : B) (z : π.fiber b), π.fiberι b z = y` from `⟨π y, π.asFiber y, π.fiberι_asFiber y⟩`. Establish `: Smooth (π.fiberToSpecResidueField b)` using `MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›`. Establish `: IsReduced (π.fiber b)` using `GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)`. Take `⟨e⟩` from `GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber B X π b z`. Conclude with `isReduced_of_injective e.toRingHom e.injective`.
-/
theorem isReduced_quot_of_smooth {X B : Scheme.{0}} (π : X ⟶ B) [Smooth π] (y : X) :
    _root_.IsReduced (X.presheaf.stalk y ⧸
      (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  obtain ⟨b, z, rfl⟩ : ∃ (b : B) (z : π.fiber b), π.fiberι b z = y := ⟨π y, π.asFiber y, π.fiberι_asFiber y⟩
  have : Smooth (π.fiberToSpecResidueField b) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›
  have : IsReduced (π.fiber b) := GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)
  obtain ⟨e⟩ := GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber B X π b z
  exact isReduced_of_injective e.toRingHom e.injective

/- English proof (translation)
Introduce `T _ _ _ H _ _ hH y hy hdim ϖ hϖ`. Establish `hsm : Smooth H.hom` using `hH.smooth`. Set `S` to `(Sp T).presheaf.stalk (H.hom y)`. Use `letI : Algebra T S := StructureSheaf.stalkAlgebra T (H.hom y)`. Use `haveI : (H.hom y).asIdeal.IsPrime := PrimeSpectrum.isPrime _`.

Use `haveI : IsLocalization.AtPrime S (H.hom y).asIdeal := StructureSheaf.IsLocalization.to_stalk T _`. Establish `hb : (H.hom y).asIdeal = maximalIdeal T` using `by rw [hy]; rfl`. Establish `hmS : maximalIdeal S = Ideal.span {algebraMap T S ϖ}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (H.hom y).asIdeal S, hb, hϖ, Ideal.map_span, Set.image_singleton]`. Set `O` to `H.left.presheaf.stalk y`.

Set `a₀ : O` to `(H.hom.stalkMap y).hom (algebraMap T S ϖ)`. Establish `hcst : cst H.hom ϖ = algebraMap O H.left.functionField a₀`. Establish `e₁` using `algebraMap_germ (X := H.left) (x := y) (U := ⊤) trivial (H.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ))`. Establish `e₂` using `Scheme.Hom.germ_stalkMap_apply H.hom ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ)`. Use `e₁.symm.trans ?_` and prove the remaining obligations.

Use `congrArg _ (e₂.symm.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Conclude with `IsDiscreteValuationRing.not_a_field T (by rw [hϖ, Ideal.span_singleton_eq_bot.2 rfl])`.

Use `haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _ (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hs0 : algebraMap T S ϖ ≠ 0` using `fun h => hϖ0 ((IsLocalization.injective S (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))`. Establish `ha₀ : a₀ ≠ 0`. Use `letI : Algebra S O := (H.hom.stalkMap y).hom.toAlgebra`. Use `haveI : Module.Flat S O := Flat.stalkMap H.hom y`.

Establish `hr : IsSMulRegular O (algebraMap T S ϖ)` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs0)`. Introduce `h`. Establish `h1 : (algebraMap T S ϖ) • (1 : O) = (algebraMap T S ϖ) • (0 : O)`. Rewrite using `[smul_zero, Algebra.smul_def, _root_.mul_one]`. Conclude with `h`.

Conclude with `one_ne_zero (hr h1)`. Establish `ha₀m : a₀ ∈ maximalIdeal O` using `map_nonunit (H.hom.stalkMap y).hom _ (hmS ▸ Ideal.mem_span_singleton_self _)`. Establish `hred` using `isReduced_quot_of_smooth H.hom y`. Rewrite `hred` using `[hmS, Ideal.map_span, Set.image_singleton]`. Establish `hm : maximalIdeal O = Ideal.span {a₀}` using `maximalIdeal_eq_span_of_isReduced hdim ha₀ ha₀m hred`.

Use `haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom`. Establish `hnf : ¬ IsField O` using `fun h => ha₀ (by`. Use `(IsLocalRing.isField_iff_maximalIdeal_eq.1 h) ▸ ha₀m` as an intermediate fact. Rewrite using `[Ideal.mem_bot] at this)` and apply the resulting hypothesis. Establish `hpr : Submodule.IsPrincipal (maximalIdeal O)` using `⟨⟨a₀, hm⟩⟩`.

Use `haveI : IsDiscreteValuationRing O := ((IsDiscreteValuationRing.TFAE O hnf).out 0 4).2 hpr`. Establish `hirr : Irreducible a₀` using `IsDiscreteValuationRing.irreducible_iff_uniformizer a₀ |>.2 hm`. Establish `hc : cst H.hom ϖ ≠ 0`. Rewrite using `[hcst]`. Conclude with `fun h => ha₀ (IsFractionRing.injective O H.left.functionField (h.trans (map_zero _).symm))`.

Use `⟨hc, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨x, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := O) u`. Establish `hx : x ≠ 0` using `by rintro rfl; simp at hu`. Take `⟨m, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hirr`. Take `⟨n, v', rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hirr`.

Establish `hv' : algebraMap O H.left.functionField (v' : O) ≠ 0` using `(v'.isUnit.map (algebraMap O H.left.functionField)).ne_zero`. Use `⟨(m : ℤ) - n, algebraMap O _ (v : O) * (algebraMap O _ (v' : O))⁻¹, UnitAt.mul ⟨_, v.isUnit, rfl⟩ (UnitAt.inv ⟨_, v'.isUnit, rfl⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[hcst, zpow_sub₀ (fun h => hc (hcst.trans h)), zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]`. Establish `hc' : algebraMap O H.left.functionField a₀ ≠ 0` using `hcst ▸ hc`. Clear the denominators using the available nonvanishing facts.
-/
theorem unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H]
    [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T →
    ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} →
    GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField),
      GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  intro T _ _ _ H _ _ hH y hy hdim ϖ hϖ
  have hsm : Smooth H.hom := hH.smooth
  let S := (Sp T).presheaf.stalk (H.hom y)
  letI : Algebra T S := StructureSheaf.stalkAlgebra T (H.hom y)
  haveI : (H.hom y).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  haveI : IsLocalization.AtPrime S (H.hom y).asIdeal := StructureSheaf.IsLocalization.to_stalk T _
  have hb : (H.hom y).asIdeal = maximalIdeal T := by rw [hy]; rfl
  have hmS : maximalIdeal S = Ideal.span {algebraMap T S ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (H.hom y).asIdeal S, hb, hϖ, Ideal.map_span,
      Set.image_singleton]
  let O := H.left.presheaf.stalk y
  let a₀ : O := (H.hom.stalkMap y).hom (algebraMap T S ϖ)

  have hcst : cst H.hom ϖ = algebraMap O H.left.functionField a₀ := by
    have e₁ := algebraMap_germ (X := H.left) (x := y) (U := ⊤) trivial
      (H.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ))
    have e₂ := Scheme.Hom.germ_stalkMap_apply H.hom ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ)
    refine e₁.symm.trans ?_
    refine congrArg _ (e₂.symm.trans ?_)
    rfl

  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field T (by rw [hϖ, Ideal.span_singleton_eq_bot.2 rfl])
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors
  have hs0 : algebraMap T S ϖ ≠ 0 := fun h => hϖ0 ((IsLocalization.injective S
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))
  have ha₀ : a₀ ≠ 0 := by
    letI : Algebra S O := (H.hom.stalkMap y).hom.toAlgebra
    haveI : Module.Flat S O := Flat.stalkMap H.hom y
    have hr : IsSMulRegular O (algebraMap T S ϖ) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs0)
    intro h
    have h1 : (algebraMap T S ϖ) • (1 : O) = (algebraMap T S ϖ) • (0 : O) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one]
      exact h
    exact one_ne_zero (hr h1)
  have ha₀m : a₀ ∈ maximalIdeal O := map_nonunit (H.hom.stalkMap y).hom _
    (hmS ▸ Ideal.mem_span_singleton_self _)

  have hred := isReduced_quot_of_smooth H.hom y
  rw [hmS, Ideal.map_span, Set.image_singleton] at hred
  have hm : maximalIdeal O = Ideal.span {a₀} :=
    maximalIdeal_eq_span_of_isReduced hdim ha₀ ha₀m hred

  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hnf : ¬ IsField O := fun h => ha₀ (by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.1 h) ▸ ha₀m
    rwa [Ideal.mem_bot] at this)
  have hpr : Submodule.IsPrincipal (maximalIdeal O) := ⟨⟨a₀, hm⟩⟩
  haveI : IsDiscreteValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O hnf).out 0 4).2 hpr
  have hirr : Irreducible a₀ := IsDiscreteValuationRing.irreducible_iff_uniformizer a₀ |>.2 hm
  have hc : cst H.hom ϖ ≠ 0 := by
    rw [hcst]
    exact fun h => ha₀ (IsFractionRing.injective O H.left.functionField (h.trans (map_zero _).symm))
  refine ⟨hc, fun u hu => ?_⟩
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) u
  have hx : x ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hirr
  obtain ⟨n, v', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hirr
  have hv' : algebraMap O H.left.functionField (v' : O) ≠ 0 :=
    (v'.isUnit.map (algebraMap O H.left.functionField)).ne_zero
  refine ⟨(m : ℤ) - n, algebraMap O _ (v : O) * (algebraMap O _ (v' : O))⁻¹,
    UnitAt.mul ⟨_, v.isUnit, rfl⟩ (UnitAt.inv ⟨_, v'.isUnit, rfl⟩), ?_⟩
  rw [hcst, zpow_sub₀ (fun h => hc (hcst.trans h)), zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
  have hc' : algebraMap O H.left.functionField a₀ ≠ 0 := hcst ▸ hc
  field_simp

end GlobalTheory.Desc.GenFibre
