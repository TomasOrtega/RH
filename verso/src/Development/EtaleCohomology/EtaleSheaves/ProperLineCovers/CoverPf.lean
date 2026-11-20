import Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut.CoverPf

open LateralTheory.E.E4

/- English proof (translation)
Take `⟨_, hP, _⟩` from `hc`. Establish `: IsSeparated c` using `inferInstance`. Establish `: IsSeparated (terminal.from C)`. Rewrite using `[show terminal.from C = c ≫ terminal.from _ from Subsingleton.elim _ _]`. Use `infer_instance`.

Conclude with `hU.inf hV`.
-/
theorem inf_affine {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    {U V : C.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  obtain ⟨_, hP, _⟩ := hc
  have : IsSeparated c := inferInstance
  have : IsSeparated (terminal.from C) := by
    rw [show terminal.from C = c ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  exact hU.inf hV

/- English proof (translation)
Take `⟨hI, _, _⟩` from `hc`. Use `hI` as an intermediate fact. Simplify using `using nonempty_preirreducible_inter U.isOpen V.isOpen hU hV`.
-/
theorem inf_nonempty {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    {U V : C.Opens} (hU : (U : Set C).Nonempty) (hV : (V : Set C).Nonempty) : ((U ⊓ V : C.Opens) : Set C).Nonempty := by
  obtain ⟨hI, _, _⟩ := hc
  have := hI
  simpa using nonempty_preirreducible_inter U.isOpen V.isOpen hU hV

def LeafAffCover : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ U V : C.Opens, U ⊔ V = ⊤ ∧ IsAffineOpen U ∧ IsAffineOpen V ∧ (U : Set C).Nonempty ∧ (V : Set C).Nonempty

def LeafDedOpen : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDedekindDomain B) (_ : Algebra Ω B) (_ : Algebra.FiniteType Ω B),
      Nonempty (W.toScheme ≅ Sp B)

/- English proof (translation)
Introduce `Ω _ _ C c hc`. Take `⟨U, V, hUV, hU, hV, hUn, hVn⟩` from `hA Ω c hc`. Use `⟨U, V, hUV, ?_⟩` and prove the remaining obligations. Introduce `W hW`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW`.

Break down `hW with rfl | rfl | rfl` into its components or cases. Conclude with `hD Ω c hc _ hU hUn`. Conclude with `hD Ω c hc _ hV hVn`. Conclude with `hD Ω c hc _ (inf_affine c hc hU hV) (inf_nonempty c hc hUn hVn)`.
-/
theorem LeafCover_of (hA : LeafAffCover) (hD : LeafDedOpen) : LeafCover := by
  intro Ω _ _ C c hc
  obtain ⟨U, V, hUV, hU, hV, hUn, hVn⟩ := hA Ω c hc
  refine ⟨U, V, hUV, ?_⟩
  intro W hW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl
  · exact hD Ω c hc _ hU hUn
  · exact hD Ω c hc _ hV hVn
  · exact hD Ω c hc _ (inf_affine c hc hU hV) (inf_nonempty c hc hUn hVn)

def LeafDedRing : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W)

/- English proof (translation)
Introduce `Ω _ _ C c hc W hW hWn`. Establish `hD` using `hR Ω c hc W hW hWn`. Take `⟨_, _, hS⟩` from `hc`. Establish `hL : LocallyOfFiniteType c` using `inferInstance`. Set `φ : Ω →+* Γ(C, W)` to `(c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom`.

Use `letI : Algebra Ω Γ(C, W) := φ.toAlgebra`. Establish `hφ : φ.FiniteType`. Establish `h1 : (c.appLE ⊤ W le_top).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)`. Conclude with `h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)`. Conclude with `⟨Γ(C, W), inferInstance, hD, inferInstance, hφ, ⟨hW.isoSpec⟩⟩`.
-/
theorem LeafDedOpen_of (hR : LeafDedRing) : LeafDedOpen := by
  intro Ω _ _ C c hc W hW hWn
  have hD := hR Ω c hc W hW hWn
  obtain ⟨_, _, hS⟩ := hc
  have hL : LocallyOfFiniteType c := inferInstance
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : (c.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)
  exact ⟨Γ(C, W), inferInstance, hD, inferInstance, hφ, ⟨hW.isoSpec⟩⟩

def LeafTwoPts : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ p p' : C, p ≠ p' ∧ IsClosed ({p} : Set C) ∧ IsClosed ({p'} : Set C)

def LeafComplAffine : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ (p : C) (hp : IsClosed ({p} : Set C)), IsAffineOpen (⟨{p}ᶜ, hp.isOpen_compl⟩ : C.Opens)

/- English proof (translation)
Introduce `Ω _ _ C c hc`. Take `⟨p, p', hne, hp, hp'⟩` from `h2 Ω c hc`. Use `⟨⟨{p}ᶜ, hp.isOpen_compl⟩, ⟨{p'}ᶜ, hp'.isOpen_compl⟩, ?_, hA Ω c hc p hp, hA Ω c hc p' hp', ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]`.

Distinguish the cases in `h : x = p`. Use `right`. Substitute `h` using the available equality. Use `show x ∈ ({p'}ᶜ : Set C)`. Simplify using `using hne`.

Use `left show x ∈ ({p}ᶜ : Set C)`. Simplify using `using h`. Conclude with `⟨p', by simpa using hne.symm⟩`. Conclude with `⟨p, by simpa using hne⟩`.
-/
theorem LeafAffCover_of (h2 : LeafTwoPts) (hA : LeafComplAffine) : LeafAffCover := by
  intro Ω _ _ C c hc
  obtain ⟨p, p', hne, hp, hp'⟩ := h2 Ω c hc
  refine ⟨⟨{p}ᶜ, hp.isOpen_compl⟩, ⟨{p'}ᶜ, hp'.isOpen_compl⟩, ?_, hA Ω c hc p hp, hA Ω c hc p' hp', ?_, ?_⟩
  · ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : x = p
    · right
      subst h
      show x ∈ ({p'}ᶜ : Set C)
      simpa using hne
    · left
      show x ∈ ({p}ᶜ : Set C)
      simpa using h
  · exact ⟨p', by simpa using hne.symm⟩
  · exact ⟨p, by simpa using hne⟩

def LeafDim1 : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → Ring.DimensionLEOne Γ(C, W)

def LeafNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsIntegrallyClosed Γ(C, W)

/- English proof (translation)
Introduce `Ω _ _ C c hc W hW hWn`. Take `⟨hI, _, hS⟩` from `hc`. Establish `: Nonempty W` using `hWn.to_subtype`. Establish `hSm : Smooth c` using `SmoothOfRelativeDimension.smooth 1 c`. Set `φ : Ω →+* Γ(C, W)` to `(c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom`.

Use `letI : Algebra Ω Γ(C, W) := φ.toAlgebra`. Establish `hφ : φ.Smooth`. Establish `h1 : (c.appLE ⊤ W le_top).hom.Smooth` using `HasRingHomProperty.appLE @Smooth c hSm ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)`. Conclude with `RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.bijective) h1`. Establish `: Algebra.Smooth Ω Γ(C, W)` using `hφ`.

Conclude with `GlobalTheory.isIntegrallyClosed_of_smooth Ω Γ(C, W)`.
-/
theorem leafNormal : LeafNormal := by
  intro Ω _ _ C c hc W hW hWn
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hSm : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.Smooth := by
    have h1 : (c.appLE ⊤ W le_top).hom.Smooth :=
      HasRingHomProperty.appLE @Smooth c hSm ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.bijective) h1
  have : Algebra.Smooth Ω Γ(C, W) := hφ
  exact GlobalTheory.isIntegrallyClosed_of_smooth Ω Γ(C, W)

/- English proof (translation)
Establish `hI0 : IsIntegral C` using `hc.1`. Establish `: Nonempty W` using `hWn.to_subtype`. Establish `: IsDomain Γ(C, W)` using `inferInstance`. Take `⟨hI, _, hS⟩` from `hc`. Establish `: Nonempty W` using `hWn.to_subtype`.

Establish `hL : LocallyOfFiniteType c` using `inferInstance`. Set `e : Ω ≃+* Γ(Sp Ω, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm`. Set `ψ` to `(c.appLE ⊤ W le_top).hom`. Set `φ : Ω →+* Γ(C, W)` to `ψ.comp (e : Ω →+* Γ(Sp Ω, ⊤))`. Use `letI : Algebra Ω Γ(C, W) := φ.toAlgebra`.

Establish `hφ : φ.FiniteType`. Establish `h1 : ψ.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)`. Conclude with `h1.comp (RingHom.FiniteType.of_surjective _ e.surjective)`. Establish `: Algebra.FiniteType Ω Γ(C, W)` using `hφ`. Establish `hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) c hS ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)`.

Take `⟨s, hs, hst⟩` from `hloc`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, ht0⟩ : ∃ t ∈ s, t ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hle : Ideal.span s ≤ ⊥` using `Ideal.span_le.mpr (fun x hx => by simp [h x hx])`.

Rewrite `hle` using `[hs]`. Conclude with `one_ne_zero (Ideal.mem_bot.mp (hle (Submodule.mem_top : (1 : Γ(C, W)) ∈ ⊤)))`. Establish `h1 : ((algebraMap Γ(C, W) (Localization.Away t)).comp φ).IsStandardSmoothOfRelativeDimension 1` using `(hst t ht).comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e)`. Establish `hs0 : Submonoid.powers t ≤ nonZeroDivisors Γ(C, W)` using `powers_le_nonZeroDivisors_of_noZeroDivisors ht0`. Establish `: IsDomain (Localization.Away t)` using `IsLocalization.isDomain_localization hs0`.

Establish `hEq : algebraMap Ω (Localization.Away t) = (algebraMap Γ(C, W) (Localization.Away t)).comp φ` using `IsScalarTower.algebraMap_eq _ _ _`. Rewrite `h1` using `[← hEq]`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away t)` using `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mp h1`. Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 Ω (Localization.Away t)`. Establish `h2` using `GlobalTheory.AffinePoints.trdeg_eq_of_etale g hg`.

Establish `: FaithfulSMul Γ(C, W) (Localization.Away t)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)`. Establish `: Algebra.IsAlgebraic Γ(C, W) (Localization.Away t)` using `IsLocalization.isAlgebraic _ (Submonoid.powers t)`. Rewrite `h2` using `[GlobalTheory.trdeg_eq_of_isAlgebraic_top Ω Γ(C, W) (Localization.Away t)]`. Conclude with `GlobalTheory.ringKrullDim_eq_of_trdeg_eq Ω Γ(C, W) h2`.
-/
theorem krullDim_eq_one {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) :
    ringKrullDim Γ(C, W) = ((1 : ℕ) : WithBot ℕ∞) := by
  have hI0 : IsIntegral C := hc.1
  have : Nonempty W := hWn.to_subtype
  have : IsDomain Γ(C, W) := inferInstance
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hL : LocallyOfFiniteType c := inferInstance
  let e : Ω ≃+* Γ(Sp Ω, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  let ψ := (c.appLE ⊤ W le_top).hom
  let φ : Ω →+* Γ(C, W) := ψ.comp (e : Ω →+* Γ(Sp Ω, ⊤))
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : ψ.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ e.surjective)
  have : Algebra.FiniteType Ω Γ(C, W) := hφ
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) c hS ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
  obtain ⟨s, hs, hst⟩ := hloc
  obtain ⟨t, ht, ht0⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ ⊥ := Ideal.span_le.mpr (fun x hx => by simp [h x hx])
    rw [hs] at hle
    exact one_ne_zero (Ideal.mem_bot.mp (hle (Submodule.mem_top : (1 : Γ(C, W)) ∈ ⊤)))
  have h1 : ((algebraMap Γ(C, W) (Localization.Away t)).comp φ).IsStandardSmoothOfRelativeDimension 1 :=
    (hst t ht).comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e)
  have hs0 : Submonoid.powers t ≤ nonZeroDivisors Γ(C, W) := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hs0
  have hEq : algebraMap Ω (Localization.Away t) = (algebraMap Γ(C, W) (Localization.Away t)).comp φ :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [← hEq] at h1
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away t) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mp h1
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 Ω (Localization.Away t)
  have h2 := GlobalTheory.AffinePoints.trdeg_eq_of_etale g hg
  have : FaithfulSMul Γ(C, W) (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  have : Algebra.IsAlgebraic Γ(C, W) (Localization.Away t) := IsLocalization.isAlgebraic _ (Submonoid.powers t)
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top Ω Γ(C, W) (Localization.Away t)] at h2
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq Ω Γ(C, W) h2

/- English proof (translation)
Introduce `Ω _ _ C c hc W hW hWn`. Establish `h3` using `krullDim_eq_one c hc W hW hWn`. Establish `hI0 : IsIntegral C` using `hc.1`. Establish `: Nonempty W` using `hWn.to_subtype`. Establish `: IsDomain Γ(C, W)` using `inferInstance`.

Establish `hK : Ring.KrullDimLE 1 Γ(C, W)` using `Ring.krullDimLE_iff.mpr (by rw [h3])`. Conclude with `⟨fun {P} hne hP => hP.isMaximal_of_ne_bot hne⟩`.
-/
theorem leafDim1 : LeafDim1 := by
  intro Ω _ _ C c hc W hW hWn
  have h3 := krullDim_eq_one c hc W hW hWn
  have hI0 : IsIntegral C := hc.1
  have : Nonempty W := hWn.to_subtype
  have : IsDomain Γ(C, W) := inferInstance
  have hK : Ring.KrullDimLE 1 Γ(C, W) := Ring.krullDimLE_iff.mpr (by rw [h3])
  exact ⟨fun {P} hne hP => hP.isMaximal_of_ne_bot hne⟩

/- English proof (translation)
Introduce `Ω _ _ C c hc W hW hWn`. Establish `h1` using `hd Ω c hc W hW hWn`. Establish `h2` using `hn Ω c hc W hW hWn`. Take `⟨hI, _, hS⟩` from `hc`. Establish `: Nonempty W` using `hWn.to_subtype`.

Establish `hL : LocallyOfFiniteType c` using `inferInstance`. Set `φ : Ω →+* Γ(C, W)` to `(c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom`. Use `letI : Algebra Ω Γ(C, W) := φ.toAlgebra`. Establish `hφ : φ.FiniteType`. Establish `h1 : (c.appLE ⊤ W le_top).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)`.

Conclude with `h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)`. Establish `: Algebra.FiniteType Ω Γ(C, W)` using `hφ`. Establish `: IsNoetherianRing Γ(C, W)` using `Algebra.FiniteType.isNoetherianRing Ω _`. Conclude with `{ }`.
-/
theorem LeafDedRing_of (hd : LeafDim1) (hn : LeafNormal) : LeafDedRing := by
  intro Ω _ _ C c hc W hW hWn
  have h1 := hd Ω c hc W hW hWn
  have h2 := hn Ω c hc W hW hWn
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hL : LocallyOfFiniteType c := inferInstance
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : (c.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType Ω Γ(C, W) := hφ
  have : IsNoetherianRing Γ(C, W) := Algebra.FiniteType.isNoetherianRing Ω _
  exact { }

/- English proof (translation)
The claim follows from `LeafCover_of hA (LeafDedOpen_of hR)`.
-/
theorem LeafCover_of' (hA : LeafAffCover) (hR : LeafDedRing) : LeafCover :=
  LeafCover_of hA (LeafDedOpen_of hR)

/- English proof (translation)
The claim follows from `LeafCover_of' (LeafAffCover_of h2 hA) (LeafDedRing_of hd hn)`.
-/
theorem LeafCover_of_four (h2 : LeafTwoPts) (hA : LeafComplAffine) (hd : LeafDim1) (hn : LeafNormal) : LeafCover :=
  LeafCover_of' (LeafAffCover_of h2 hA) (LeafDedRing_of hd hn)

/- English proof (translation)
The claim follows from `LeafCover_of_four h2 hA hd leafNormal`.
-/
theorem LeafCover_of_three (h2 : LeafTwoPts) (hA : LeafComplAffine) (hd : LeafDim1) : LeafCover :=
  LeafCover_of_four h2 hA hd leafNormal

/- English proof (translation)
Introduce `Ω _ _ C c hc`. Establish `hc'` using `hc`. Take `⟨hI, hP, hS⟩` from `hc`. Establish `hL : LocallyOfFiniteType c` using `inferInstance`. Establish `: JacobsonSpace C` using `LocallyOfFiniteType.jacobsonSpace c`.

Assume the negation of the conclusion as `hne`. Establish `hsub' : (closedPoints C).Subsingleton` using `fun p hp p' hp' => by`. Assume the negation of the conclusion as `h`. Conclude with `hne ⟨p, p', h, hp, hp'⟩`. Establish `hcl : closure (closedPoints C) = Set.univ` using `closure_closedPoints`.

Establish `hsub : Subsingleton C`. Break down `hsub'.eq_empty_or_singleton with h | ⟨p, h⟩` into its components or cases. Rewrite `hcl` using `[h, closure_empty]`. Conclude with `⟨fun x _ => by`. Establish `hx : x ∈ (∅ : Set C)` using `hcl ▸ Set.mem_univ x`.

Conclude with `absurd hx (Set.notMem_empty x)⟩`. Establish `hp : IsClosed ({p} : Set C)`. Establish `: p ∈ closedPoints C` using `by rw [h]; rfl`. Conclude with `this`. Rewrite `hcl` using `[h, hp.closure_eq]`.

Conclude with `⟨fun x y => by`. Establish `hx : x ∈ ({p} : Set C)` using `hcl ▸ Set.mem_univ x`. Establish `hy : y ∈ ({p} : Set C)` using `hcl ▸ Set.mem_univ y`. Rewrite `hx`, `hy` using `[Set.mem_singleton_iff]`. Rewrite using `[hx, hy]⟩`.

Take `⟨x⟩ : Nonempty C` from `inferInstance`. Take `⟨_, ⟨W, hW, rfl⟩, hx, -⟩` from `C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `h1` using `krullDim_eq_one c hc' W hW ⟨x, hx⟩`. Establish `hsW : Subsingleton W` using `⟨fun a b => Subtype.ext (hsub.elim _ _)⟩`. Establish `hsP : Subsingleton (PrimeSpectrum Γ(C, W))`.

Use `hsW` as an intermediate fact. Conclude with `hW.isoSpec.inv.isOpenEmbedding.injective.subsingleton`. Establish `hK0 : Ring.KrullDimLE 0 Γ(C, W)` using `Ring.KrullDimLE.mk₀ fun I hI => by`. Take `⟨M, hM, hIM⟩` from `I.exists_le_maximal hI.ne_top`. Establish `h' : (⟨I, hI⟩ : PrimeSpectrum Γ(C, W)) = ⟨M, hM.isPrime⟩` using `Subsingleton.elim _ _`.

Establish `hIM' : I = M` using `congrArg PrimeSpectrum.asIdeal h'`. Rewrite using `[hIM']`. Conclude with `hM`. Use `(Ring.krullDimLE_iff (n := 0)).mp hK0` as an intermediate fact. Rewrite `this` using `[h1]`.

Evaluate the numerical expressions using `at this`.
-/
theorem leafTwoPts : LeafTwoPts := by
  intro Ω _ _ C c hc
  have hc' := hc
  obtain ⟨hI, hP, hS⟩ := hc
  have hL : LocallyOfFiniteType c := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  by_contra hne
  have hsub' : (closedPoints C).Subsingleton := fun p hp p' hp' => by
    by_contra h
    exact hne ⟨p, p', h, hp, hp'⟩
  have hcl : closure (closedPoints C) = Set.univ := closure_closedPoints
  have hsub : Subsingleton C := by
    rcases hsub'.eq_empty_or_singleton with h | ⟨p, h⟩
    · rw [h, closure_empty] at hcl
      exact ⟨fun x _ => by
        have hx : x ∈ (∅ : Set C) := hcl ▸ Set.mem_univ x
        exact absurd hx (Set.notMem_empty x)⟩
    · have hp : IsClosed ({p} : Set C) := by
        have : p ∈ closedPoints C := by rw [h]; rfl
        exact this
      rw [h, hp.closure_eq] at hcl
      exact ⟨fun x y => by
        have hx : x ∈ ({p} : Set C) := hcl ▸ Set.mem_univ x
        have hy : y ∈ ({p} : Set C) := hcl ▸ Set.mem_univ y
        rw [Set.mem_singleton_iff] at hx hy
        rw [hx, hy]⟩
  obtain ⟨x⟩ : Nonempty C := inferInstance
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h1 := krullDim_eq_one c hc' W hW ⟨x, hx⟩
  have hsW : Subsingleton W := ⟨fun a b => Subtype.ext (hsub.elim _ _)⟩
  have hsP : Subsingleton (PrimeSpectrum Γ(C, W)) := by
    have := hsW
    exact hW.isoSpec.inv.isOpenEmbedding.injective.subsingleton
  have hK0 : Ring.KrullDimLE 0 Γ(C, W) := Ring.KrullDimLE.mk₀ fun I hI => by
    obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
    have h' : (⟨I, hI⟩ : PrimeSpectrum Γ(C, W)) = ⟨M, hM.isPrime⟩ := Subsingleton.elim _ _
    have hIM' : I = M := congrArg PrimeSpectrum.asIdeal h'
    rw [hIM']
    exact hM
  have := (Ring.krullDimLE_iff (n := 0)).mp hK0
  rw [h1] at this
  norm_num at this

/- English proof (translation)
The claim follows from `LeafCover_of_three h2 hA leafDim1`.
-/
theorem LeafCover_of_two (h2 : LeafTwoPts) (hA : LeafComplAffine) : LeafCover :=
  LeafCover_of_three h2 hA leafDim1

/- English proof (translation)
The claim follows from `LeafCover_of_two leafTwoPts hA`.
-/
theorem LeafCover_of_one (hA : LeafComplAffine) : LeafCover :=
  LeafCover_of_two leafTwoPts hA

end LateralTheory.E.E4.CurveCut.CoverPf
