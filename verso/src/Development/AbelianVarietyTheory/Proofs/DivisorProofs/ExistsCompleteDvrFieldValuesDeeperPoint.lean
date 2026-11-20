import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValField

/- English proof (translation)
Use `set z := y (closedPoint K) with hz`. Take `⟨U, hU, hzU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := M.Z) (x := z) (U := ⊤) trivial`. Establish `hne : (U : Set M.Z).Nonempty` using `⟨z, hzU⟩`. Establish `hr : Set.range y = {z}` using `RatModel.range_eq_singleton y _`. Set `φ : M.O z →+* K` to `RatModel.valHom y z hr`.

Set `y₀ : Γ(M.Z, U) →+* K` to `φ.comp ((Subalgebra.inclusion (RatModel.ringOn_le_O (M := M) hzU)).toRingHom.comp (M.sectionsEquiv U hne).toRingHom)`. Establish `hy₀ : ∀ f, y₀ f = φ ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩` using `fun f => by show φ _ = φ _`. Use `congr 1`. Conclude with `Subtype.ext (RatModel.coe_sectionsEquiv U hne f)`. Establish `hft : Algebra.FiniteType ℤ Γ(M.Z, U)`.

Establish `h1 : (M.s.appLE ⊤ U (by simp)).hom.FiniteType` using `M.lft.finiteType_appLE (isAffineOpen_top _) hU _`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of o)).commRingCatIsoToRingEquiv.symm.surjective`. Establish `h3 : (algebraMap ℤ o).FiniteType` using `RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω))`. Establish `h4` using `(h1.comp h2).comp h3`. Rewrite using `[← RingHom.finiteType_algebraMap]`.

Use `h4` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`. Use `⟨Γ(M.Z, U), inferInstance, hft, y₀, fun E hE a ha => ?_⟩` and prove the remaining obligations. Set `Wo : M.Z.Opens` to `⟨{w | a ∈ M.O w}, M.isOpen_setOf_mem_O a⟩`. Take `⟨f, hfW, hzf⟩` from `hU.exists_basicOpen_le (V := Wo) ⟨z, ha⟩ hzU`.

Establish `hnef : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty` using `⟨z, hzf⟩`. Establish `har : a ∈ M.ringOn (M.Z.basicOpen f)` using `RatModel.mem_ringOn.2 fun w hw => hfW hw`. Take `⟨s, hs⟩` from `(RatModel.mem_ringOn_iff_exists hnef).1 har`. Use `letI := hU.isLocalization_basicOpen f`. Take `⟨n, r, hrn⟩` from `IsLocalization.Away.surj f s`.

Establish `halg : ∀ g : Γ(M.Z, U), algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen f) g = resG M.Z (M.Z.basicOpen_le f) g` using `fun _ => rfl`. Establish `he` using `congrArg (M.res _ hnef) hrn`. Rewrite `he` using `[map_mul, map_pow, halg, halg, RatModel.res_resG, RatModel.res_resG, RatModel.res_apply, hs, RatModel.res_apply, RatModel.res_apply]`. Establish `hO : (⟨a, ha⟩ : M.O z) * ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ ^ n = ⟨valF M.pt U r, RatModel.valF_mem_O hzU r⟩` using `Subtype.ext (by simpa using he)`. Establish `hφ` using `congrArg φ hO`.

Rewrite `hφ` using `[map_mul, map_pow, ← hy₀, ← hy₀]`. Establish `hf0 : y₀ f ≠ 0`. Rewrite using `[hy₀]`. Conclude with `(RatModel.val_ne_zero_iff hr _).2 ((RatModel.isUnit_valF_iff hzU f).2 hzf)`. Establish `hval : M.val y a = y₀ r / y₀ f ^ n`.

Rewrite using `[← hφ, mul_div_cancel_right₀ _ (pow_ne_zero _ hf0)]`. Both sides reduce to the same expression. Rewrite using `[hval]`. Conclude with `div_mem (hE r) (pow_mem (hE f) n)`.
-/
theorem exists_fg_values {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (y₀ : R →+* K),
      ∀ E : Subfield K, (∀ r, y₀ r ∈ E) → ∀ a ∈ M.O (y (closedPoint K)), M.val y a ∈ E := by
  set z := y (closedPoint K) with hz
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := z) (U := ⊤) trivial
  have hne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  have hr : Set.range y = {z} := RatModel.range_eq_singleton y _
  let φ : M.O z →+* K := RatModel.valHom y z hr
  let y₀ : Γ(M.Z, U) →+* K :=
    φ.comp ((Subalgebra.inclusion (RatModel.ringOn_le_O (M := M) hzU)).toRingHom.comp
      (M.sectionsEquiv U hne).toRingHom)
  have hy₀ : ∀ f, y₀ f = φ ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ := fun f => by
    show φ _ = φ _
    congr 1
    exact Subtype.ext (RatModel.coe_sectionsEquiv U hne f)
  have hft : Algebra.FiniteType ℤ Γ(M.Z, U) := by
    have h1 : (M.s.appLE ⊤ U (by simp)).hom.FiniteType :=
      M.lft.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of o)).commRingCatIsoToRingEquiv.symm.surjective
    have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω))
    have h4 := (h1.comp h2).comp h3
    rw [← RingHom.finiteType_algebraMap]
    convert h4
    exact Subsingleton.elim _ _
  refine ⟨Γ(M.Z, U), inferInstance, hft, y₀, fun E hE a ha => ?_⟩
  let Wo : M.Z.Opens := ⟨{w | a ∈ M.O w}, M.isOpen_setOf_mem_O a⟩
  obtain ⟨f, hfW, hzf⟩ := hU.exists_basicOpen_le (V := Wo) ⟨z, ha⟩ hzU
  have hnef : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzf⟩
  have har : a ∈ M.ringOn (M.Z.basicOpen f) := RatModel.mem_ringOn.2 fun w hw => hfW hw
  obtain ⟨s, hs⟩ := (RatModel.mem_ringOn_iff_exists hnef).1 har
  letI := hU.isLocalization_basicOpen f
  obtain ⟨n, r, hrn⟩ := IsLocalization.Away.surj f s
  have halg : ∀ g : Γ(M.Z, U), algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen f) g = resG M.Z (M.Z.basicOpen_le f) g :=
    fun _ => rfl
  have he := congrArg (M.res _ hnef) hrn
  rw [map_mul, map_pow, halg, halg, RatModel.res_resG, RatModel.res_resG, RatModel.res_apply, hs,
    RatModel.res_apply, RatModel.res_apply] at he

  have hO : (⟨a, ha⟩ : M.O z) * ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ ^ n =
      ⟨valF M.pt U r, RatModel.valF_mem_O hzU r⟩ := Subtype.ext (by simpa using he)
  have hφ := congrArg φ hO
  rw [map_mul, map_pow, ← hy₀, ← hy₀] at hφ
  have hf0 : y₀ f ≠ 0 := by
    rw [hy₀]
    exact (RatModel.val_ne_zero_iff hr _).2 ((RatModel.isUnit_valF_iff hzU f).2 hzf)
  have hval : M.val y a = y₀ r / y₀ f ^ n := by
    rw [← hφ, mul_div_cancel_right₀ _ (pow_ne_zero _ hf0)]
    rfl
  rw [hval]
  exact div_mem (hE r) (pow_mem (hE f) n)

end GlobalTheory.ValField

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h V _ _ _ _ hc hV`. Take `⟨R, _, hR, y₀, hval⟩` from `GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)`. Set `κ : FractionRing V →+* PadicAlgCl p` to `algebraMap (FractionRing V) (PadicAlgCl p)`. Use `haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))`. Establish `hQ` using `GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV`.

Take `⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩` from `GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀`. Use `letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra`. Use `⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩` and prove the remaining obligations. Establish `hm` using `hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha`. Take `⟨x, hx⟩` from `hm`.

Conclude with `⟨x, hx⟩`.
-/
theorem exists_complete_dvr_values : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h V _ _ _ _ hc hV
  obtain ⟨R, _, hR, y₀, hval⟩ := GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)
  let κ : FractionRing V →+* PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p)
  haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  obtain ⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀
  letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra
  refine ⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩
  have hm := hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, hx⟩

end GlobalTheory.Poinc
