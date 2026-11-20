import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRelAlgClosureFinite
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ConstClosure

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

/- English proof (translation)
Set `η : Cpt ξ` to `⟨genPt ξ, specializes_rfl⟩`. Take `⟨c, hc⟩` from `h.cover η`. Use `⟨c, hc.1, fun ω => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hmem⟩` from `h.affine c hc.1`. Establish `hη : genPt ξ ∈ U` using `(hmem _).2 ⟨specializes_rfl, hc⟩`.

Establish `key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Introduce `r`. Use `(h.ring c hc.1 _).2 fun p hp => ?_` and prove the remaining obligations. Establish `hpU : p.1 ∈ U` using `(hmem p.1).2 ⟨p.2, hp⟩`. Conclude with `⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩`.

Take `⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω` from `h.gen.bij.2 ω`. Take `⟨r, t, hrt, hunit⟩` from `stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b`. Use `replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt`. Use `replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit`. Establish `hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0` using `(hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero`.

Use `⟨_, _, key r, key t, hne, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hne]`. Conclude with `((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)`.
-/
theorem exists_chart_div (h : CoordTie ℤ ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b := by
  let η : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover η
  refine ⟨c, hc.1, fun ω => ?_⟩
  obtain ⟨U, hU, hmem⟩ := h.affine c hc.1
  have hη : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (h.ring c hc.1 _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω := h.gen.bij.2 ω
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨_, _, key r, key t, hne, ?_⟩
  rw [eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem t ht => obtain ⟨j, rfl⟩ := ht`. Conclude with `h j`. Consider the case `algebraMap n => simpa using intCast_mem F n`. Consider the case `add s t _ _ hs ht => exact add_mem hs ht`.

Consider the case `mul s t _ _ hs ht => exact mul_mem hs ht`.
-/
theorem adjoin_le_subfield (F : Subfield Ω) {c : κ} (h : ∀ j, x j / x c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h j
  | algebraMap n => simpa using intCast_mem F n
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

/- English proof (translation)
Use `eq_top_iff.2 fun ω _ => ?_` and prove the remaining obligations. Take `⟨a, b, ha, hb, -, rfl⟩` from `hc ω`. Conclude with `div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)`.
-/
theorem subfield_eq_top {c : κ} (hc : ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b)
    (F : Subfield Ω) (h : ∀ j, x j / x c ∈ F) : F = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hc ω
  exact div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)

end Chart

section Field

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Take `⟨-, -, hH, -⟩` from `h`. Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J)`. Rewrite using `[Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]`. Establish `e : mConeMap y (C (n : ℤ)) = C (n : Ω)`.

Simplify using `[mConeMap, aeval_C]`. Rewrite using `[e, hn, map_zero]`. Rewrite `hmem` using `[show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH]`. Simplify using `using hmem`.
-/
theorem charZero_of_isArithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {n : ℕ} (h : IsArithVar (mCoordIdeal y) n) : CharZero Ω := by
  obtain ⟨-, -, hH, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : mConeMap y (C (n : ℤ)) = C (n : Ω) := by
      simp [mConeMap, aeval_C]
    rw [e, hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH] at hmem
  simpa using hmem

/- English proof (translation)
Set `L` to `algebraicClosure ℚ Ω`. Establish `hmem : ∀ a : A, algebraMap A Ω a ∈ L` using `fun a => mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top`. Use `letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra`. Establish `hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a` using `fun _ => rfl`. Use `haveI : IsScalarTower ℤ A L := inferInstance`.

Use `haveI : NumberField L := ⟨⟩`. Use `haveI : IsIntegralClosure A ℤ L := by`. Use `⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩` and prove the remaining obligations. Rewrite using `[← hcoe, ← hcoe, hab]`. Rewrite using `[← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) (algebraMap L Ω).injective]`.

Rewrite using `[IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, Subtype.ext ha⟩`. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a, rfl⟩`. Use `haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _`. Conclude with `⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩`.
-/
theorem dedekind_finite_of_finite [CharZero Ω] (hf : FiniteDimensional ℚ (algebraicClosure ℚ Ω))
    (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] :
    IsDedekindDomain A ∧ Module.Finite ℤ A := by
  let L := algebraicClosure ℚ Ω
  have hmem : ∀ a : A, algebraMap A Ω a ∈ L := fun a =>
    mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top
  letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra
  have hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a := fun _ => rfl
  haveI : IsScalarTower ℤ A L := inferInstance
  haveI : NumberField L := ⟨⟩
  haveI : IsIntegralClosure A ℤ L := by
    refine ⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩
    · rw [← hcoe, ← hcoe, hab]
    · rw [← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) (algebraMap L Ω).injective]
      rw [IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
  haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _
  exact ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩

end Field

section Local

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hA` using `IsIntegralClosure.algebraMap_injective A ℤ Ω`. Establish `hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0` using `fun s h0 => s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)`. Use `isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun o ho => ?_` and prove the remaining obligations. Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj m.primeCompl o`.

Establish `e'` using `congrArg (algebraMap O Ω) e`. Simplify using `only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'`. Establish `ha : a = 0` using `hA (e'.symm.trans (map_zero _).symm)`. Rewrite `e` using `[ha, map_zero]`. Conclude with `(IsLocalization.map_units O s).mul_left_eq_zero.1 e`.

Take `⟨s, hsw⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω`. Establish `hz : IsIntegral ℤ (s • w)` using `isIntegral_trans _ hsw`. Take `⟨a, ha⟩` from `(IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz`. Use `⟨IsLocalization.mk' O a s, ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a`.

Rewrite using `[IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]`. Establish `h2 : algebraMap A Ω a = algebraMap A Ω s * w`. Rewrite using `[ha, Submonoid.smul_def, Algebra.smul_def]`. Conclude with `mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])`.
-/
theorem isIntegrallyClosedIn_of_atPrime (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] : IsIntegrallyClosedIn O Ω := by
  have hA := IsIntegralClosure.algebraMap_injective A ℤ Ω
  have hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0 := fun s h0 =>
    s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)
  refine isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun o ho => ?_
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj m.primeCompl o
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'
    have ha : a = 0 := hA (e'.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units O s).mul_left_eq_zero.1 e
  · obtain ⟨s, hsw⟩ := IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw
    haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω
    have hz : IsIntegral ℤ (s • w) := isIntegral_trans _ hsw
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz
    refine ⟨IsLocalization.mk' O a s, ?_⟩
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap A Ω a = algebraMap A Ω s * w := by
      rw [ha, Submonoid.smul_def, Algebra.smul_def]
    exact mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])

end Local

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _`. Use `haveI : CharZero Ω := charZero_of_isArithVar hV`. Take `⟨c₀, -, hdiv⟩` from `exists_chart_div 𝔐.tie`. Establish `hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω)`. Use `GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_` and prove the remaining obligations.

Establish `htop` using `subfield_eq_top hdiv (IntermediateField.adjoin ℚ ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield fun j => IntermediateField.subset_adjoin _ _ (by simp)`. Use `eq_top_iff.2 fun ω _ => ?_` and prove the remaining obligations. Establish `hω : ω ∈ (⊤ : Subfield Ω)` using `Subfield.mem_top ω`. Rewrite `hω` using `[← htop]`. Conclude with `hω`.

Establish `hconst : HasConstants ℤ A y` using `fun c' hc' a => (𝔐.tie.ring c' hc' _).2 fun p _ => IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal p.1).2 _ ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)`. Take `⟨hd, hfA⟩` from `dedekind_finite_of_finite hfin A`. Use `⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩` and prove the remaining obligations. Introduce `m _ O _ _ _ _ _ _ _`. Use `⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩` and prove the remaining obligations.

Use `show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)`.
-/
theorem const_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _
  classical
  haveI : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨c₀, -, hdiv⟩ := exists_chart_div 𝔐.tie
  have hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω) := by
    refine GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω
      (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_
    have htop := subfield_eq_top hdiv (IntermediateField.adjoin ℚ
      ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield
      fun j => IntermediateField.subset_adjoin _ _ (by simp)
    refine eq_top_iff.2 fun ω _ => ?_
    have hω : ω ∈ (⊤ : Subfield Ω) := Subfield.mem_top ω
    rw [← htop] at hω
    exact hω
  have hconst : HasConstants ℤ A y := fun c' hc' a =>
    (𝔐.tie.ring c' hc' _).2 fun p _ =>
      IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal p.1).2 _
        ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  obtain ⟨hd, hfA⟩ := dedekind_finite_of_finite hfin A
  refine ⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩
  intro m _ O _ _ _ _ _ _ _
  refine ⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩
  show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Num.ConstClosure
