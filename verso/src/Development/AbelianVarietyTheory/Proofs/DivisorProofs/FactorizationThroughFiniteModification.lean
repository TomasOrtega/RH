import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ M M' h hh e Z a c hac`. Use `haveI := M'.integral`. Establish `cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)), (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x)` using `fun f g x => by`. Rewrite using `[Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.

Establish `hsub : Subsingleton (Sp (FractionRing R))` using `inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))`. Set `pt : Sp (FractionRing R)` to `(default : PrimeSpectrum (FractionRing R))`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial`. Establish `hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U` using `fun y => by rwa [Subsingleton.elim y pt]`. Establish `hV : IsAffineOpen (h ⁻¹ᵁ U)` using `hU.preimage h`.

Establish `ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `show h (a z) ∈ U`. Rewrite using `[← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]`.

Conclude with `hgU _`. Establish `hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `show h (M'.gp z) ∈ U`.

Rewrite using `[← Scheme.Hom.comp_apply, e]`. Conclude with `hgU _`. Take `⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a` from `⟨_, IsOpenImmersion.lift_fac _ _ ha⟩`. Take `⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp` from `⟨_, IsOpenImmersion.lift_fac _ _ hg⟩`. It suffices to establish `key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]`.

Use `haveI : IsAffine (h ⁻¹ᵁ U) := hV`. Establish `hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R`. Rewrite using `[reassoc_of% fa, reassoc_of% hac, M.gp_π]`. Establish `hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R`. Rewrite using `[reassoc_of% fg, reassoc_of% e, M.gp_π]`.

Establish `hinj : Function.Injective g₀.appTop.hom` using `by haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx0`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`.

Take `⟨y, hy⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne`. Take `⟨z, hz⟩` from `g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩`. Establish `hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x` using `hz`. Establish `hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0` using `hx0`. Rewrite `hz'` using `[Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero]`.

Conclude with `hz'`. Establish `hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤), IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r`. Introduce `x`. Establish `nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s)` using `fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))`. Establish `inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom` using `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective`.

Take `⟨r', t', ht', hx'⟩` from `IsFractionRing.div_surjective (A := R) ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)`. Establish `ht0 : algebraMap R (FractionRing R) t' ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t')))`. Rewrite using `[nat]`.

Simplify using `using ht0`. Use `hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom` as an intermediate fact. Simplify using `using this`. Apply `inj` to reduce the goal to its premises. Rewrite using `[map_mul, nat, nat]`.

Establish `hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s` using `fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id`. Rewrite using `[hi, hi, ← hx']`. Conclude with `div_mul_cancel₀ _ ht0`. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.comp_appTop]`.

Use extensionality with `b`. Take `⟨r, t, ht, hx⟩` from `hfrac (g₀.appTop.hom b)`. Establish `e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, ← cA, ← cA, hq2, hx]`.

Establish `e2` using `congrArg a₀.appTop.hom e1`. Rewrite `e2` using `[map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul]`. Conclude with `(IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2`.
-/
theorem finite_modif_eq_gp : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h →
    M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp →
    a = c ≫ M'.gp := by
  intro R _ _ M M' h hh e Z a c hac
  haveI := M'.integral
  have cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)),
      (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hsub : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let pt : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial
  have hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U := fun y => by rwa [Subsingleton.elim y pt]
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (a z) ∈ U
    rw [← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]; exact hgU _
  have hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (M'.gp z) ∈ U
    rw [← Scheme.Hom.comp_apply, e]; exact hgU _
  obtain ⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a := ⟨_, IsOpenImmersion.lift_fac _ _ ha⟩
  obtain ⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  suffices key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]
  haveI : IsAffine (h ⁻¹ᵁ U) := hV
  have hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R := by
    rw [reassoc_of% fa, reassoc_of% hac, M.gp_π]
  have hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R := by
    rw [reassoc_of% fg, reassoc_of% e, M.gp_π]
  have hinj : Function.Injective g₀.appTop.hom := by
    haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant
    haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι
    rw [injective_iff_map_eq_zero]
    intro x hx0
    apply eq_zero_of_basicOpen_eq_bot
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨z, hz⟩ := g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩
    have hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x := hz
    have hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0 := hx0
    rw [Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero] at hz'
    exact hz'
  have hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤),
      IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r := by
    intro x
    have nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := fun s =>
      congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r', t', ht', hx'⟩ := IsFractionRing.div_surjective (A := R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)
    have ht0 : algebraMap R (FractionRing R) t' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩
    · have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
          ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t'))) := by
        rw [nat]; simpa using ht0
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      simpa using this
    · apply inj
      rw [map_mul, nat, nat]
      have hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s :=
        fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
      rw [hi, hi, ← hx']
      exact div_mul_cancel₀ _ ht0
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  obtain ⟨r, t, ht, hx⟩ := hfrac (g₀.appTop.hom b)
  have e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r := by
    apply hinj
    rw [map_mul, ← cA, ← cA, hq2, hx]
  have e2 := congrArg a₀.appTop.hom e1
  rw [map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul] at e2
  exact (IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2

end GlobalTheory.Mum
