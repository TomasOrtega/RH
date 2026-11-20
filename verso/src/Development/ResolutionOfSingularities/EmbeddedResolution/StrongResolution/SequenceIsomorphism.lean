import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_specMap_asIdeal {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    (q : PrimeSpectrum B) (a : A) :
    a ∈ ((Spec.map ψ) q).asIdeal ↔ (ConcreteCategory.hom ψ) a ∈ q.asIdeal := Iff.rfl

/- English proof (translation)
Establish `hinv : ∀ p : PrimeSpectrum (A : Type u), ((Spec.map φ) ((Spec.map (inv φ)) p) : PrimeSpectrum (A : Type u)) = p`. Introduce `p`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Apply `Ideal.ext` to reduce the goal to its premises. Introduce `a`.

Prove the components needed by the constructor for the conclusion. Introduce `hmem`. Establish `h1 : (ConcreteCategory.hom (inv φ)) ((ConcreteCategory.hom φ) a) ∈ p.asIdeal` using `(mem_specMap_asIdeal (inv φ) p _).mp ((mem_specMap_asIdeal φ _ a).mp hmem)`. Rewrite `h1` using `[IsIso.hom_inv_id_apply]`. Then use the resulting hypothesis. Introduce `hmem`.

Use `(mem_specMap_asIdeal φ _ a).mpr ?_` and prove the remaining obligations. Use `(mem_specMap_asIdeal (inv φ) p _).mpr ?_` and prove the remaining obligations. Rewrite using `[IsIso.hom_inv_id_apply]`. Conclude with `hmem`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `a ha`. Rewrite `ha` using `[PrimeSpectrum.mem_vanishingIdeal]`. Establish `hmem : (ConcreteCategory.hom (inv φ)) a ∈ PrimeSpectrum.vanishingIdeal W`. Rewrite using `[PrimeSpectrum.mem_vanishingIdeal]`. Introduce `p hp`.

Establish `h1 : (Spec.map φ) ((Spec.map (inv φ)) p) ∈ W` using `cast (congrArg (fun x : PrimeSpectrum (A : Type u) => x ∈ W) (hinv p)).symm hp`. Conclude with `(mem_specMap_asIdeal (inv φ) p a).mp (ha _ h1)`. Establish `h3 : (ConcreteCategory.hom φ) ((ConcreteCategory.hom (inv φ)) a) = a`. Rewrite using `[IsIso.inv_hom_id_apply]`. Establish `h5` using `Ideal.mem_map_of_mem (ConcreteCategory.hom φ) hmem`.

Rewrite `h5` using `[h3]`. Then use the resulting hypothesis. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite `ha` using `[PrimeSpectrum.mem_vanishingIdeal]`. Rewrite using `[Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal]`.

Introduce `q hq`. Conclude with `(mem_specMap_asIdeal φ q a).mp (ha _ hq)`.
-/
private theorem vanishingIdeal_preimage_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsIso φ]
    (W : Set (PrimeSpectrum A)) :
    PrimeSpectrum.vanishingIdeal (⇑(Spec.map φ) ⁻¹' W)
      = Ideal.map (ConcreteCategory.hom φ) (PrimeSpectrum.vanishingIdeal W) := by
  have hinv : ∀ p : PrimeSpectrum (A : Type u),
      ((Spec.map φ) ((Spec.map (inv φ)) p) : PrimeSpectrum (A : Type u)) = p := by
    intro p
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    constructor
    · intro hmem
      have h1 : (ConcreteCategory.hom (inv φ)) ((ConcreteCategory.hom φ) a) ∈ p.asIdeal :=
        (mem_specMap_asIdeal (inv φ) p _).mp ((mem_specMap_asIdeal φ _ a).mp hmem)
      rwa [IsIso.hom_inv_id_apply] at h1
    · intro hmem
      refine (mem_specMap_asIdeal φ _ a).mpr ?_
      refine (mem_specMap_asIdeal (inv φ) p _).mpr ?_
      rw [IsIso.hom_inv_id_apply]
      exact hmem
  apply le_antisymm
  · intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    have hmem : (ConcreteCategory.hom (inv φ)) a ∈ PrimeSpectrum.vanishingIdeal W := by
      rw [PrimeSpectrum.mem_vanishingIdeal]
      intro p hp
      have h1 : (Spec.map φ) ((Spec.map (inv φ)) p) ∈ W :=
        cast (congrArg (fun x : PrimeSpectrum (A : Type u) => x ∈ W) (hinv p)).symm hp
      exact (mem_specMap_asIdeal (inv φ) p a).mp (ha _ h1)
    have h3 : (ConcreteCategory.hom φ) ((ConcreteCategory.hom (inv φ)) a) = a := by
      rw [IsIso.inv_hom_id_apply]
    have h5 := Ideal.mem_map_of_mem (ConcreteCategory.hom φ) hmem
    rwa [h3] at h5
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    rw [Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    exact (mem_specMap_asIdeal φ q a).mp (ha _ hq)

/- English proof (translation)
Establish `: IsIso (ψ.app (U : Y.Opens))` using `inferInstance`. Establish `hU : IsAffineOpen (U : Y.Opens)` using `U.2`. Establish `happ : ψ.appLE (U : Y.Opens) (ψ ⁻¹ᵁ (U : Y.Opens)) le_rfl = ψ.app (U : Y.Opens)`. Simplify using `[Scheme.Hom.appLE]`. Establish `hsq : Spec.map (ψ.app (U : Y.Opens)) ≫ hU.fromSpec = hV.fromSpec ≫ ψ`.

Rewrite using `[← happ]`. Conclude with `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ψ hU hV le_rfl`. Establish `hpt : ∀ z, ψ (hV.fromSpec z) = hU.fromSpec ((Spec.map (ψ.app (U : Y.Opens))) z)`. Introduce `z`. Establish `h` using `congrArg (fun m : Spec Γ(Y', ψ ⁻¹ᵁ (U : Y.Opens)) ⟶ Y => ⇑m z) hsq`.

Simplify using `using h.symm`. Use `Eq.trans ?_ (vanishingIdeal_preimage_specMap (ψ.app (U : Y.Opens)) (⇑hU.fromSpec ⁻¹' T))` and prove the remaining obligations. Conclude with `congrArg PrimeSpectrum.vanishingIdeal (Set.ext fun z => iff_of_eq (congrArg (fun y => y ∈ T) (hpt z)))`.
-/
private theorem vanishingIdeal_preimage_fromSpec_of_isIso {Y Y' : Scheme.{u}} (ψ : Y' ⟶ Y) [IsIso ψ]
    (T : Set Y) (U : Y.affineOpens) (hV : IsAffineOpen (ψ ⁻¹ᵁ (U : Y.Opens))) :
    PrimeSpectrum.vanishingIdeal (⇑hV.fromSpec ⁻¹' (⇑ψ ⁻¹' T))
      = Ideal.map (ConcreteCategory.hom (ψ.app (U : Y.Opens)))
          (PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' T)) := by
  have : IsIso (ψ.app (U : Y.Opens)) := inferInstance
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have happ : ψ.appLE (U : Y.Opens) (ψ ⁻¹ᵁ (U : Y.Opens)) le_rfl = ψ.app (U : Y.Opens) := by
    simp [Scheme.Hom.appLE]
  have hsq : Spec.map (ψ.app (U : Y.Opens)) ≫ hU.fromSpec = hV.fromSpec ≫ ψ := by
    rw [← happ]
    exact AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ψ hU hV le_rfl
  have hpt : ∀ z, ψ (hV.fromSpec z) = hU.fromSpec ((Spec.map (ψ.app (U : Y.Opens))) z) := by
    intro z
    have h := congrArg
      (fun m : Spec Γ(Y', ψ ⁻¹ᵁ (U : Y.Opens)) ⟶ Y => ⇑m z) hsq
    simpa using h.symm
  refine Eq.trans ?_ (vanishingIdeal_preimage_specMap (ψ.app (U : Y.Opens)) (⇑hU.fromSpec ⁻¹' T))
  exact congrArg PrimeSpectrum.vanishingIdeal
    (Set.ext fun z => iff_of_eq (congrArg (fun y => y ∈ T) (hpt z)))

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Rewrite `h` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `h (by simpa using hu.map (e.symm : S →+* R))`.
-/
private theorem map_mem_maximalIdeal_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {a : R}
    (h : a ∈ IsLocalRing.maximalIdeal R) : e a ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  intro hu
  exact h (by simpa using hu.map (e.symm : S →+* R))

/- English proof (translation)
Take `⟨hspan, hdim⟩` from `h`. Establish `hle : Ideal.span (Set.range fun i => e (x i)) ≤ IsLocalRing.maximalIdeal S`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨i, rfl⟩`. Use `show e (x i) ∈ IsLocalRing.maximalIdeal S`.

Use `map_mem_maximalIdeal_ringEquiv e ?_` and prove the remaining obligations. Rewrite using `[← hspan]`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`. Establish `hge : IsLocalRing.maximalIdeal S ≤ Ideal.span (Set.range fun i => e (x i))`. Introduce `y hy`.

Establish `h1 : Ideal.span (Set.range x) ≤ Ideal.comap (e : R →+* S) (Ideal.span (Set.range fun i => e (x i)))`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨i, rfl⟩`. Simplify using `only [SetLike.mem_coe, Ideal.mem_comap, RingHom.coe_coe]`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`.

Establish `h2 : e.symm y ∈ IsLocalRing.maximalIdeal R` using `map_mem_maximalIdeal_ringEquiv e.symm hy`. Establish `h3 : e.symm y ∈ Ideal.span (Set.range x)` using `by rw [hspan]; exact h2`. Establish `h4` using `h1 h3`. Rewrite `h4` using `[Ideal.mem_comap]`. Simplify using `using h4`.

Conclude with `⟨le_antisymm hle hge, hdim.trans (ringKrullDim_eq_of_ringEquiv e)⟩`.
-/
private theorem isRegularParameterSystem_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  obtain ⟨hspan, hdim⟩ := h
  have hle : Ideal.span (Set.range fun i => e (x i)) ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.span_le]
    rintro z ⟨i, rfl⟩
    show e (x i) ∈ IsLocalRing.maximalIdeal S
    refine map_mem_maximalIdeal_ringEquiv e ?_
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hge : IsLocalRing.maximalIdeal S ≤ Ideal.span (Set.range fun i => e (x i)) := by
    intro y hy
    have h1 : Ideal.span (Set.range x)
        ≤ Ideal.comap (e : R →+* S) (Ideal.span (Set.range fun i => e (x i))) := by
      rw [Ideal.span_le]
      rintro z ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.coe_coe]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h2 : e.symm y ∈ IsLocalRing.maximalIdeal R := map_mem_maximalIdeal_ringEquiv e.symm hy
    have h3 : e.symm y ∈ Ideal.span (Set.range x) := by rw [hspan]; exact h2
    have h4 := h1 h3
    rw [Ideal.mem_comap] at h4
    simpa using h4
  exact ⟨le_antisymm hle hge, hdim.trans (ringKrullDim_eq_of_ringEquiv e)⟩

/- English proof (translation)
Establish `hxy : x = y` using `funext h`. Rewrite using `[hxy]`. Conclude with `hy`.
-/
private theorem isRegularParameterSystem_congr {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) {x y : Fin n → R} (h : ∀ i, x i = y i) (hy : IsRegularParameterSystem R n y) :
    IsRegularParameterSystem R n x := by
  have hxy : x = y := funext h
  rw [hxy]
  exact hy

/- English proof (translation)
Rewrite using `[Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
private theorem iso_inv_comp_eq_comp_inv {W Y Z T : Scheme.{u}} (a : W ≅ Y) (b : Z ≅ T)
    (p : W ⟶ Z) (q : Y ⟶ T) (hw : a.hom ≫ q = p ≫ b.hom) :
    a.inv ≫ p = q ≫ b.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Substitute `hij` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem eqToIso_hom_comp_projectionToBase_of_eq {X : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i = j) : (eqToIso (congrArg s.schemeAt hij)).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst hij
  simp

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Rewrite using `[B'.projectionToBase_zero, B.projectionToBase_zero]`.

Conclude with `h0`. Consider the case `succ n ih`. Introduce `hi`. Establish `hn : n < B.length` using `hi`. Rewrite using `[B'.projectionToBase_succ, B.projectionToBase_succ, ← Category.assoc]`.

Use `show ((e (n + 1) hn).hom ≫ B'.transitionMapSucc n) ≫ B'.projectionToBase n = B.transitionMapSucc n ≫ B.projectionToBase n`. Rewrite using `[hstep n hn, Category.assoc, ih hn.le]`.
-/
private theorem iso_hom_comp_projectionToBase_of_commute_blowupMorphism {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i))
    (h0 : (e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom)
    (hstep : ∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ (i : ℕ) (hi : i ≤ B.length), (e i hi).hom ≫ B'.projectionToBase i = B.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [B'.projectionToBase_zero, B.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    rw [B'.projectionToBase_succ, B.projectionToBase_succ, ← Category.assoc]
    show ((e (n + 1) hn).hom ≫ B'.transitionMapSucc n) ≫ B'.projectionToBase n
      = B.transitionMapSucc n ≫ B.projectionToBase n
    rw [hstep n hn, Category.assoc, ih hn.le]

/- English proof (translation)
Establish `h` using `Scheme.IdealSheafData.support_comap I g`. Rewrite `hx` using `[h]`. Conclude with `hx`.
-/
private theorem mem_support_of_mem_support_comap {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (I : Z.IdealSheafData) {x : Y} (hx : x ∈ (I.comap g).support) : g x ∈ I.support := by
  have h := Scheme.IdealSheafData.support_comap I g
  rw [h] at hx
  exact hx

/- English proof (translation)
Establish `hI : (I.comap g.hom).comap g.inv = I`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]`. Establish `hx' : x ∈ ((I.comap g.hom).comap g.inv).support` using `by rw [hI]; exact hx`. Conclude with `mem_support_of_mem_support_comap g.inv (I.comap g.hom) hx'`.
-/
private theorem inv_mem_support_comap_of_iso {Y Z : Scheme.{u}} (g : Y ≅ Z) (I : Z.IdealSheafData)
    {x : Z} (hx : x ∈ I.support) : g.inv x ∈ (I.comap g.hom).support := by
  have hI : (I.comap g.hom).comap g.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hx' : x ∈ ((I.comap g.hom).comap g.inv).support := by rw [hI]; exact hx
  exact mem_support_of_mem_support_comap g.inv (I.comap g.hom) hx'

/- English proof (translation)
Substitute `hf` using the available equality. Conclude with `h`.
-/
private theorem isIso_restrict_of_eq {Y Z : Scheme.{u}} {f₁ f₂ : Y ⟶ Z} (hf : f₁ = f₂)
    (U : Z.Opens) (h : IsIso (f₁ ∣_ U)) : IsIso (f₂ ∣_ U) := by
  subst hf
  exact h

/- English proof (translation)
The claim follows from `(Scheme.homeoOfIso g).isOpenMap`.
-/
private theorem isOpenMap_iso_hom {Y Z : Scheme.{u}} (g : Y ≅ Z) : IsOpenMap (⇑g.hom) :=
  (Scheme.homeoOfIso g).isOpenMap

/- English proof (translation)
Introduce `y'`. Take `⟨hreg, U, hy, n, fs, J, hrsp, hideal⟩` from `hS (g.inv.base y')`. Establish `hsi : IsIso (g.inv.stalkMap y')` using `inferInstance`. Establish `hV : IsAffineOpen (g.inv ⁻¹ᵁ (U : Y.Opens))` using `U.2.preimage_of_isIso g.inv`. Establish `he : ∀ t, (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv t = (ConcreteCategory.hom (g.inv.stalkMap y')) t` using `fun _ => rfl`.

Establish `hnat : ∀ s : Γ(Y, (U : Y.Opens)), (ConcreteCategory.hom (Y'.presheaf.germ (g.inv ⁻¹ᵁ (U : Y.Opens)) y' hy)) ((ConcreteCategory.hom (g.inv.app (U : Y.Opens))) s) = (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv ((ConcreteCategory.hom (Y.presheaf.germ (U : Y.Opens) (g.inv.ba …`. Introduce `s`. Rewrite using `[he]`. Simplify using the standard rewrite rules. Use `⟨?_, ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩, hy, n, fun i => (ConcreteCategory.hom (g.inv.app (U : Y.Opens))) (fs i), J, ?_, ?_⟩` and prove the remaining obligations.

Use `hreg` as an intermediate fact. Conclude with `IsRegularLocalRing.of_ringEquiv (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv`. Use `isRegularParameterSystem_congr n (fun i => hnat (fs i)) ?_` and prove the remaining obligations. Conclude with `isRegularParameterSystem_ringEquiv (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv n (fun i => (ConcreteCategory.hom (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) (fs i)) hrsp`. Establish `h1 : (reducedInverseImage (g.inv ≫ p) S).ideal ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩ = PrimeSpectrum.vanishingIdeal (⇑hV.fromSpec ⁻¹' (⇑(g.inv ≫ p) ⁻¹' (S : Set X)))`.

Simplify using `[reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]`. Establish `h2 : (reducedInverseImage p S).ideal U = PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' (⇑p ⁻¹' (S : Set X)))`. Simplify using `[reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]`. Establish `hcomp : (⇑(g.inv ≫ p) ⁻¹' (S : Set X)) = ⇑g.inv ⁻¹' (⇑p ⁻¹' (S : Set X))`. Use extensionality with `z`.

Simplify using the standard rewrite rules. Rewrite using `[h1, hcomp, vanishingIdeal_preimage_fromSpec_of_isIso g.inv (⇑p ⁻¹' (S : Set X)) U hV, ← h2, hideal, Ideal.map_span]`. Simplify using `[map_prod]`.
-/
private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp {Y Y' X : Scheme.{u}} (g : Y ≅ Y') (p : Y ⟶ X)
    (S : TopologicalSpace.Closeds X) (hS : IsStrictNormalCrossingsDivisor (reducedInverseImage p S)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (g.inv ≫ p) S) := by
  intro y'
  obtain ⟨hreg, U, hy, n, fs, J, hrsp, hideal⟩ := hS (g.inv.base y')
  have hsi : IsIso (g.inv.stalkMap y') := inferInstance
  have hV : IsAffineOpen (g.inv ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage_of_isIso g.inv
  have he : ∀ t, (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv t
      = (ConcreteCategory.hom (g.inv.stalkMap y')) t := fun _ => rfl
  have hnat : ∀ s : Γ(Y, (U : Y.Opens)),
      (ConcreteCategory.hom (Y'.presheaf.germ (g.inv ⁻¹ᵁ (U : Y.Opens)) y' hy))
          ((ConcreteCategory.hom (g.inv.app (U : Y.Opens))) s)
        = (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
            ((ConcreteCategory.hom (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) s) := by
    intro s
    rw [he]
    simp
  refine ⟨?_, ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩, hy, n,
    fun i => (ConcreteCategory.hom (g.inv.app (U : Y.Opens))) (fs i), J, ?_, ?_⟩
  · have := hreg
    exact IsRegularLocalRing.of_ringEquiv (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
  · refine isRegularParameterSystem_congr n (fun i => hnat (fs i)) ?_
    exact isRegularParameterSystem_ringEquiv
      (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv n
      (fun i => (ConcreteCategory.hom
        (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) (fs i)) hrsp
  · have h1 : (reducedInverseImage (g.inv ≫ p) S).ideal ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩
        = PrimeSpectrum.vanishingIdeal
            (⇑hV.fromSpec ⁻¹' (⇑(g.inv ≫ p) ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have h2 : (reducedInverseImage p S).ideal U
        = PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' (⇑p ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have hcomp : (⇑(g.inv ≫ p) ⁻¹' (S : Set X)) = ⇑g.inv ⁻¹' (⇑p ⁻¹' (S : Set X)) := by
      ext z
      simp
    rw [h1, hcomp, vanishingIdeal_preimage_fromSpec_of_isIso g.inv (⇑p ⁻¹' (S : Set X)) U hV, ← h2, hideal,
      Ideal.map_span]
    simp [map_prod]

/- English proof (translation)
Take `⟨hL, e, h0, hstep, hcen⟩` from `h`. Establish `p1 : (e 0 (Nat.zero_le _)).inv ≫ B.isoZero.hom = B'.isoZero.hom`. Rewrite using `[Iso.inv_comp_eq]`. Conclude with `h0.symm`. Establish `p2 : ∀ (i : ℕ) (hi : i < B'.length), (e (i + 1) (by omega)).inv ≫ B.transitionMapSucc i = B'.transitionMapSucc i ≫ (e i (by omega)).inv`.

Introduce `i hi`. Establish `hi' : i < B.length` using `by omega`. Conclude with `iso_inv_comp_eq_comp_inv (e (i + 1) hi') (e i hi'.le) (B.transitionMapSucc i) (B'.transitionMapSucc i) (hstep i hi')`. Establish `p3 : ∀ (i : ℕ) (hi : i < B'.length), (B.center i).comap (e i (by omega)).inv = B'.center i`. Introduce `i hi`.

Establish `hi' : i < B.length` using `by omega`. Rewrite using `[← hcen i hi', ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]`. Conclude with `⟨hL.symm, fun i hi => (e i (by omega)).symm, p1, p2, p3⟩`.
-/
theorem SequenceOfBlowups.Isomorphic.symm {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : B'.Isomorphic B := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  have p1 : (e 0 (Nat.zero_le _)).inv ≫ B.isoZero.hom = B'.isoZero.hom := by
    rw [Iso.inv_comp_eq]
    exact h0.symm
  have p2 : ∀ (i : ℕ) (hi : i < B'.length),
      (e (i + 1) (by omega)).inv ≫ B.transitionMapSucc i
        = B'.transitionMapSucc i ≫ (e i (by omega)).inv := by
    intro i hi
    have hi' : i < B.length := by omega
    exact iso_inv_comp_eq_comp_inv (e (i + 1) hi') (e i hi'.le) (B.transitionMapSucc i)
      (B'.transitionMapSucc i) (hstep i hi')
  have p3 : ∀ (i : ℕ) (hi : i < B'.length),
      (B.center i).comap (e i (by omega)).inv = B'.center i := by
    intro i hi
    have hi' : i < B.length := by omega
    rw [← hcen i hi', ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  exact ⟨hL.symm, fun i hi => (e i (by omega)).symm, p1, p2, p3⟩

/- English proof (translation)
Take `⟨hL, e, h0, hstep, hcen⟩` from `h`. Take `⟨hL', g, g0, gstep, gcen⟩` from `h'`. Establish `p1 : ((e 0 (Nat.zero_le _)).hom ≫ (g 0 (Nat.zero_le _)).hom) ≫ B''.isoZero.hom = B.isoZero.hom`. Rewrite using `[Category.assoc, g0, h0]`. Establish `p2 : ∀ (i : ℕ) (hi : i < B.length), ((e (i + 1) hi).hom ≫ (g (i + 1) (by omega)).hom) ≫ B''.transitionMapSucc i = B.transitionMapSucc i ≫ ((e i hi.le).hom ≫ (g i (by omega)).hom)`.

Introduce `i hi`. Establish `hi' : i < B'.length` using `by omega`. Rewrite using `[Category.assoc, gstep i hi', ← Category.assoc, hstep i hi, Category.assoc]`. Establish `p3 : ∀ (i : ℕ) (hi : i < B.length), (B''.center i).comap ((e i hi.le).hom ≫ (g i (by omega)).hom) = B.center i`. Introduce `i hi`.

Establish `hi' : i < B'.length` using `by omega`. Rewrite using `[Scheme.IdealSheafData.comap_comp, gcen i hi', hcen i hi]`. Conclude with `⟨hL.trans hL', fun i hi => (e i hi) ≪≫ (g i (by omega)), p1, p2, p3⟩`.
-/
theorem SequenceOfBlowups.Isomorphic.trans {X : Scheme.{u}} {B B' B'' : SequenceOfBlowups X}
    (h : B.Isomorphic B') (h' : B'.Isomorphic B'') : B.Isomorphic B'' := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  obtain ⟨hL', g, g0, gstep, gcen⟩ := h'
  have p1 : ((e 0 (Nat.zero_le _)).hom ≫ (g 0 (Nat.zero_le _)).hom) ≫ B''.isoZero.hom
      = B.isoZero.hom := by
    rw [Category.assoc, g0, h0]
  have p2 : ∀ (i : ℕ) (hi : i < B.length),
      ((e (i + 1) hi).hom ≫ (g (i + 1) (by omega)).hom) ≫ B''.transitionMapSucc i
        = B.transitionMapSucc i ≫ ((e i hi.le).hom ≫ (g i (by omega)).hom) := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Category.assoc, gstep i hi', ← Category.assoc, hstep i hi, Category.assoc]
  have p3 : ∀ (i : ℕ) (hi : i < B.length),
      (B''.center i).comap ((e i hi.le).hom ≫ (g i (by omega)).hom) = B.center i := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Scheme.IdealSheafData.comap_comp, gcen i hi', hcen i hi]
  exact ⟨hL.trans hL', fun i hi => (e i hi) ≪≫ (g i (by omega)), p1, p2, p3⟩

/- English proof (translation)
Take `⟨hL, e, h0, hstep, _⟩` from `h`. Use `⟨e B.length le_rfl ≪≫ eqToIso (congrArg B'.schemeAt hL), ?_⟩` and prove the remaining obligations. Rewrite using `[SequenceOfBlowups.lastStructMap_eq_projectionToBase, SequenceOfBlowups.lastStructMap_eq_projectionToBase, Iso.trans_hom, Category.assoc, eqToIso_hom_comp_projectionToBase_of_eq B' hL]`. Conclude with `iso_hom_comp_projectionToBase_of_commute_blowupMorphism e h0 hstep B.length le_rfl`.
-/
theorem SequenceOfBlowups.Isomorphic.exists_lastObjIso {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') :
    ∃ e : B.lastObj ≅ B'.lastObj, e.hom ≫ B'.lastStructMap = B.lastStructMap := by
  obtain ⟨hL, e, h0, hstep, _⟩ := h
  refine ⟨e B.length le_rfl ≪≫ eqToIso (congrArg B'.schemeAt hL), ?_⟩
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase, SequenceOfBlowups.lastStructMap_eq_projectionToBase, Iso.trans_hom,
    Category.assoc, eqToIso_hom_comp_projectionToBase_of_eq B' hL]
  exact iso_hom_comp_projectionToBase_of_commute_blowupMorphism e h0 hstep B.length le_rfl

/- English proof (translation)
Take `⟨ε, hε⟩` from `h.exists_lastObjIso`. Take `⟨hs, hp, hiso, hd, hc, hsnc⟩` from `hB`. Establish `hmap : B'.lastStructMap = ε.inv ≫ B.lastStructMap`. Rewrite using `[← hε, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]`. Establish `q1 : AlgebraicGeometry.Smooth (B'.lastStructMap ≫ f)`.

Use `hs` as an intermediate fact. Rewrite using `[hmap, Category.assoc]`. Use `infer_instance`. Establish `q2 : AlgebraicGeometry.IsProper B'.lastStructMap`. Use `hp` as an intermediate fact.

Rewrite using `[hmap]`. Use `infer_instance`. Establish `q3 : CategoryTheory.IsIso (AlgebraicGeometry.morphismRestrict B'.lastStructMap f.smoothLocus)`. Establish `hres : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus))` using `inferInstance`. Establish `hA : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus) ≫ B'.lastStructMap ∣_ f.smoothLocus)`.

Establish `h0 : IsIso ((ε.hom ≫ B'.lastStructMap) ∣_ f.smoothLocus)` using `isIso_restrict_of_eq hε.symm f.smoothLocus hiso`. Rewrite `h0` using `[AlgebraicGeometry.morphismRestrict_comp]`. Conclude with `h0`. Conclude with `IsIso.of_isIso_comp_left (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus)) (B'.lastStructMap ∣_ f.smoothLocus)`. Establish `q4 : Dense (⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X))`.

Establish `hpre : ⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X) = ⇑ε.inv ⁻¹' (⇑B.lastStructMap ⁻¹' (f.smoothLocus : Set X))`. Rewrite using `[hmap]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hpre]`.

Conclude with `hd.preimage (isOpenMap_iso_hom ε.symm)`. Establish `q5 : B'.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)`. Take `⟨hL, eiso, h0, hstep, hcen⟩` from `h`. Introduce `i hi x hx`. Establish `hi' : i < B.length` using `by omega`.

Establish `hy` using `inv_mem_support_comap_of_iso (eiso i hi'.le) (B'.center i) hx`. Rewrite `hy` using `[hcen i hi']`. Establish `hpt` using `hc i hi' _ hy`. Establish `hkey : (eiso i hi'.le).hom ≫ B'.projectionToBase i = B.projectionToBase i` using `iso_hom_comp_projectionToBase_of_commute_blowupMorphism eiso h0 hstep i hi'.le`. Establish `hinv : (eiso i hi'.le).inv ≫ B.projectionToBase i = B'.projectionToBase i`.

Rewrite using `[← hkey, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]`. Establish `hval : B'.projectionToBase i x = B.projectionToBase i ((eiso i hi'.le).inv x)`. Rewrite using `[← hinv]`. Simplify using the standard rewrite rules. Rewrite using `[hval]`.

Conclude with `hpt`. Establish `q6 : IsStrictNormalCrossingsDivisor (reducedInverseImage B'.lastStructMap (smoothLocusComplement f))`. Rewrite using `[hmap]`. Conclude with `isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp ε B.lastStructMap (smoothLocusComplement f) hsnc`. Conclude with `⟨q1, q2, q3, q4, q5, q6⟩`.
-/
theorem IsStrongResolution.of_isomorphic (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    {B B' : SequenceOfBlowups X} (h : B.Isomorphic B') (hB : IsStrongResolution k X f B) :
    IsStrongResolution k X f B' := by
  obtain ⟨ε, hε⟩ := h.exists_lastObjIso
  obtain ⟨hs, hp, hiso, hd, hc, hsnc⟩ := hB
  have hmap : B'.lastStructMap = ε.inv ≫ B.lastStructMap := by
    rw [← hε, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have q1 : AlgebraicGeometry.Smooth (B'.lastStructMap ≫ f) := by
    have := hs
    rw [hmap, Category.assoc]
    infer_instance
  have q2 : AlgebraicGeometry.IsProper B'.lastStructMap := by
    have := hp
    rw [hmap]
    infer_instance
  have q3 : CategoryTheory.IsIso
      (AlgebraicGeometry.morphismRestrict B'.lastStructMap f.smoothLocus) := by
    have hres : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus)) := inferInstance
    have hA : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus) ≫ B'.lastStructMap ∣_ f.smoothLocus) := by
      have h0 : IsIso ((ε.hom ≫ B'.lastStructMap) ∣_ f.smoothLocus) :=
        isIso_restrict_of_eq hε.symm f.smoothLocus hiso
      rw [AlgebraicGeometry.morphismRestrict_comp] at h0
      exact h0
    exact IsIso.of_isIso_comp_left (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus))
      (B'.lastStructMap ∣_ f.smoothLocus)
  have q4 : Dense (⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
    have hpre : ⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)
        = ⇑ε.inv ⁻¹' (⇑B.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
      rw [hmap]
      ext x
      simp
    rw [hpre]
    exact hd.preimage (isOpenMap_iso_hom ε.symm)
  have q5 : B'.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) := by
    obtain ⟨hL, eiso, h0, hstep, hcen⟩ := h
    intro i hi x hx
    have hi' : i < B.length := by omega
    have hy := inv_mem_support_comap_of_iso (eiso i hi'.le) (B'.center i) hx
    rw [hcen i hi'] at hy
    have hpt := hc i hi' _ hy
    have hkey : (eiso i hi'.le).hom ≫ B'.projectionToBase i = B.projectionToBase i :=
      iso_hom_comp_projectionToBase_of_commute_blowupMorphism eiso h0 hstep i hi'.le
    have hinv : (eiso i hi'.le).inv ≫ B.projectionToBase i = B'.projectionToBase i := by
      rw [← hkey, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have hval : B'.projectionToBase i x = B.projectionToBase i ((eiso i hi'.le).inv x) := by
      rw [← hinv]
      simp
    rw [hval]
    exact hpt
  have q6 : IsStrictNormalCrossingsDivisor (reducedInverseImage B'.lastStructMap (smoothLocusComplement f)) := by
    rw [hmap]
    exact isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp ε B.lastStructMap (smoothLocusComplement f) hsnc
  exact ⟨q1, q2, q3, q4, q5, q6⟩

end FunctorialResolution.EmbeddedResolution

end
