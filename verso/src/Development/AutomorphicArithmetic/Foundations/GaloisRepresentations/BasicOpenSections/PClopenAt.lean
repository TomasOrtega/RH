import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Establish `hsum : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤`. Apply `le_antisymm le_top` to reduce the goal to its premises. Establish `h` using `X.basicOpen_add_le e (1 - e)`. Rewrite `h` using `[add_sub_cancel, Scheme.basicOpen_one]`. Then use the resulting hypothesis. Establish `hprod : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥`.

Rewrite using `[← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]`. Establish `hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx hx'`.

Establish `hin : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e)` using `TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩`. Rewrite `hin` using `[hprod]`. Simplify using `using hin`. Introduce `hx`. Establish `hin : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e)`.

Rewrite using `[hsum]`. Discharge the goal by the elementary cases of `trivial`. Break down `TopologicalSpace.Opens.mem_sup.mp hin with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hx`.

Use `⟨?_, (X.basicOpen e).isOpen⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `(X.basicOpen (1 - e)).isOpen.isClosed_compl`.
-/
private lemma clopen_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hsum : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤ := by
    apply le_antisymm le_top
    have h := X.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, Scheme.basicOpen_one] at h
  have hprod : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]
  have hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro hx hx'
      have hin : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      rw [hprod] at hin
      simpa using hin
    · intro hx
      have hin : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by
        rw [hsum]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hin with h | h
      · exact h
      · exact absurd h hx
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  rw [hc]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

private noncomputable def rho {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) : Γ(W, ⊤) →+* κ :=
  (z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom

/- English proof (translation)
Establish `h1 : pt z ∈ W.basicOpen e ↔ IsLocalRing.closedPoint κ ∈ (gp κ).basicOpen (z.appTop e)`. Rewrite using `[← Scheme.preimage_basicOpen_top]`. Both sides reduce to the same expression. Rewrite using `[h1, basicOpen_eq_of_affine']`. Use `(PrimeSpectrum.mem_basicOpen _ _).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ ∉ IsLocalRing.maximalIdeal κ ↔ _`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]`. Both sides reduce to the same expression.
-/
private lemma mem_basicOpen_iff {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) (e : Γ(W, ⊤)) :
    pt z ∈ W.basicOpen e ↔ rho z e ≠ 0 := by
  have h1 : pt z ∈ W.basicOpen e ↔ IsLocalRing.closedPoint κ ∈ (gp κ).basicOpen (z.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [h1, basicOpen_eq_of_affine']
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  change _ ∉ IsLocalRing.maximalIdeal κ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]
  rfl

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Establish `: z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom = z'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom` using `CommRingCat.hom_ext h`. Conclude with `(cancel_mono _).mp this`.
-/
private lemma rho_inj {κ : Type} [Field κ] {W : Scheme.{0}} [IsAffine W] {z z' : gp κ ⟶ W}
    (h : rho z = rho z') : z = z' := by
  apply ext_of_isAffine
  have : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom = z'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).mp this

/- English proof (translation)
Establish `key : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (z ≫ g).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField V))).hom = CommRingCat.ofHom (IsLocalRing.residue V)`. Rewrite using `[hz, resPt, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Establish `h2` using `congrArg CommRingCat.Hom.hom key`. Conclude with `h2`.
-/
private lemma rho_comp (V : Type) [CommRing V] [IsLocalRing V] {W : Scheme.{0}}
    (g : W ⟶ Spec (CommRingCat.of V)) (z : gp (IsLocalRing.ResidueField V) ⟶ W) (hz : z ≫ g = resPt V) :
    (rho z).comp ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom = IsLocalRing.residue V := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (z ≫ g).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField V))).hom =
      CommRingCat.ofHom (IsLocalRing.residue V) := by
    rw [hz, resPt, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h2 := congrArg CommRingCat.Hom.hom key
  exact h2

/- English proof (translation)
Introduce `_ hHS V _ _ _ _ W g _ z₀ hz₀`. Use `haveI : IsAffine W := isAffine_of_isAffineHom g`. Use `set φ : V →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom with hφ`. Establish `hfin : φ.Finite`. Establish `h1` using `g.finite_appTop`.

Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Finite` using `RingHom.Finite.of_surjective _ (fun a => ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom a, by simp⟩)`. Conclude with `h1.comp h2`. Use `letI : Algebra V Γ(W, ⊤) := φ.toAlgebra`. Use `haveI : Module.Finite V Γ(W, ⊤) := hfin`. Establish `hc : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V → ∀ v : V, rho z (φ v) = IsLocalRing.residue V v`.

Introduce `z hz v`. Conclude with `RingHom.congr_fun (rho_comp V g z hz) v`. Establish `hsurj : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V → Function.Surjective (rho z)`. Introduce `z hz r`. Take `⟨v, hv⟩` from `IsLocalRing.residue_surjective r`.

Conclude with `⟨φ v, by rw [hc z hz v, hv]⟩`. Establish `hmax : (RingHom.ker (rho z₀)).IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (hsurj z₀ hz₀)`. Take `⟨e, he, hem, hoth⟩` from `hHS V Γ(W, ⊤) (RingHom.ker (rho z₀)) hmax`. Use `⟨W.basicOpen e, clopen_basicOpen he, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Rewrite using `[SetLike.mem_coe, mem_basicOpen_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hne`. Establish `hk : RingHom.ker (rho z) = RingHom.ker (rho z₀)`. Assume the negation of the conclusion as `hk`.

Conclude with `hne (RingHom.mem_ker.mp (hoth _ (RingHom.ker_isMaximal_of_surjective _ (hsurj z hz)) hk))`. Apply `rho_inj` to reduce the goal to its premises. Use extensionality with `a`. Take `⟨v, hv⟩` from `IsLocalRing.residue_surjective (rho z₀ a)`. Establish `hmem : a - φ v ∈ RingHom.ker (rho z₀)`.

Rewrite using `[RingHom.mem_ker, map_sub, hc z₀ hz₀ v, hv, sub_self]`. Rewrite `hmem` using `[← hk, RingHom.mem_ker, map_sub, sub_eq_zero, hc z hz v, hv]`. Conclude with `hmem`. Introduce and unpack `rfl`. Conclude with `fun h => hem (RingHom.mem_ker.mpr h)`.
-/
theorem UpperTheory.Gal.Mod.clopenAt :
    ResClosed → HensSplit → ClopenAt := by
  intro _ hHS V _ _ _ _ W g _ z₀ hz₀
  haveI : IsAffine W := isAffine_of_isAffineHom g
  set φ : V →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom with hφ
  have hfin : φ.Finite := by
    have h1 := g.finite_appTop
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (fun a => ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom a, by simp⟩)
    exact h1.comp h2
  letI : Algebra V Γ(W, ⊤) := φ.toAlgebra
  haveI : Module.Finite V Γ(W, ⊤) := hfin
  have hc : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      ∀ v : V, rho z (φ v) = IsLocalRing.residue V v := by
    intro z hz v
    exact RingHom.congr_fun (rho_comp V g z hz) v
  have hsurj : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      Function.Surjective (rho z) := by
    intro z hz r
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective r
    exact ⟨φ v, by rw [hc z hz v, hv]⟩
  have hmax : (RingHom.ker (rho z₀)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hsurj z₀ hz₀)
  obtain ⟨e, he, hem, hoth⟩ := hHS V Γ(W, ⊤) (RingHom.ker (rho z₀)) hmax
  refine ⟨W.basicOpen e, clopen_basicOpen he, ?_⟩
  intro z hz
  rw [SetLike.mem_coe, mem_basicOpen_iff]
  constructor
  · intro hne
    have hk : RingHom.ker (rho z) = RingHom.ker (rho z₀) := by
      by_contra hk
      exact hne (RingHom.mem_ker.mp
        (hoth _ (RingHom.ker_isMaximal_of_surjective _ (hsurj z hz)) hk))
    apply rho_inj
    ext a
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective (rho z₀ a)
    have hmem : a - φ v ∈ RingHom.ker (rho z₀) := by
      rw [RingHom.mem_ker, map_sub, hc z₀ hz₀ v, hv, sub_self]
    rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero, hc z hz v, hv] at hmem
    exact hmem
  · rintro rfl
    exact fun h => hem (RingHom.mem_ker.mpr h)
