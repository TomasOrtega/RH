import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.FlatModel

/- English proof (translation)
Introduce `hTop hPt E _ _ _ H Dw l l' Xo Xo' c c' hle hIrr hIrr' r h hfin het hsurj Z`. Use `set sF := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) with hsF`. Use `set g := spMap (IntermediateField.inclusion hle).toRingHom with hg`. Use `set r' := pullback.lift r _ h with hr'`. Take `⟨U₀, hU₀, hU₀irr⟩` from `hIrr Z`.

Establish `hirrB : IrreducibleSpace ↑(pullback (U₀.ι ≫ sF) g)` using `hU₀irr c'.F (IntermediateField.inclusion hle).toRingHom`. Establish `hZc_eq : Set.range (pullback.snd U₀.ι (pullback.fst sF g)) = pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))`. Rewrite using `[IsOpenImmersion.range_pullbackSnd]`. Use extensionality with `w`. Simplify using `only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι, hU₀]`.

Establish `hZc_irr : IsIrreducible (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)))`. Establish `hr : Set.range ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) = Set.range (pullback.snd U₀.ι (pullback.fst sF g))`. Rewrite using `[show ⇑((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) = ⇑(pullback.snd U₀.ι (pullback.fst sF g)) ∘ ⇑(pullbackRightPullbackFstIso sF g U₀.ι).inv from rfl, Set.range_comp, ((pullbackRightPullbackFstIso sF g U₀.ι).inv).surjective.range_eq, Set. …`. Rewrite using `[← hZc_eq, ← hr, ← Set.image_univ]`. Conclude with `IrreducibleSpace.isIrreducible_univ _ |>.image _ ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)).continuous.continuousOn`.

Establish `hZclosed : IsClosed (Z : Set (Xo.XF c))` using `isClosed_of_mem_irreducibleComponents _ Z.2`. Establish `hZopen : IsOpen (Z : Set (Xo.XF c))` using `by rw [← hU₀]; exact U₀.2`. Establish `hZc_clopen : IsClopen (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)))` using `⟨hZclosed.preimage (pullback.fst sF g).continuous, hZopen.preimage (pullback.fst sF g).continuous⟩`. Establish `hr'open : IsOpenMap r'` using `r'.isOpenMap`. Establish `hr'closed : IsClosedMap r'` using `r'.isClosedMap`.

Establish `hcompOpen : ∀ C ∈ irreducibleComponents (Xo'.XF c'), IsOpen C`. Introduce `C hC`. Take `⟨U, hU, -⟩` from `hIrr' ⟨C, hC⟩`. Rewrite using `[show C = (U : Set _) from hU.symm]`. Conclude with `U.2`.

Take `⟨z, hz⟩` from `(Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty`. Take `⟨b, hb⟩` from `(pullback.fst sF g).surjective z`. Take `⟨a, ha⟩` from `r'.surjective b`. Establish `haZ : r' a ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))`. Simplify using `only [Set.mem_preimage]`.

Rewrite using `[ha, hb]`. Conclude with `hz`. Take `⟨C, hC, haC, hCim⟩` from `hTop r' r'.continuous hr'open hr'closed hcompOpen _ hZc_clopen (IsIrreducible.isConnected hZc_irr).isPreconnected a haZ`. Take `⟨U, hU, hUirr⟩` from `hIrr' ⟨C, hC⟩`. Establish `hUC : (U : Set (Xo'.XF c')) = C` using `hU`.

Establish `hr'fst : r' ≫ pullback.fst sF g = r` using `pullback.lift_fst _ _ _`. Establish `hr'snd : r' ≫ pullback.snd sF g = pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)` using `pullback.lift_snd _ _ _`. Use `⟨U, ?_, hUirr, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `hw' : r' w ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))`.

Rewrite using `[← hCim]`. Conclude with `⟨w, hUC ▸ hw, rfl⟩`. Establish `: r w = pullback.fst sF g (r' w)` using `by rw [← hr'fst]; rfl`. Rewrite using `[this]`. Conclude with `hw'`.

Introduce `k _ _ fK x hx hxZ`. Establish `hcomm : x ≫ sF = spMap fK ≫ g`. Rewrite using `[hx, hg]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `set x' := pullback.lift x (spMap fK) hcomm with hx'`.

Establish `hx'fst : x' ≫ pullback.fst sF g = x` using `pullback.lift_fst _ _ _`. Establish `hx'snd : x' ≫ pullback.snd sF g = spMap fK` using `pullback.lift_snd _ _ _`. Establish `hrange : Set.range x' ⊆ Set.range (U.ι ≫ r')`. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `hq : x' q ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))`.

Simplify using `only [Set.mem_preimage]`. Establish `: pullback.fst sF g (x' q) = x q` using `by rw [← hx'fst]; rfl`. Rewrite using `[this]`. Conclude with `hxZ ⟨q, rfl⟩`. Rewrite `hq` using `[← hCim]`.

Take `⟨w, hwC, hw⟩` from `hq`. Establish `hwU : w ∈ Set.range U.ι` using `by rw [Scheme.Opens.range_ι, hUC]; exact hwC`. Take `⟨u, rfl⟩` from `hwU`. Conclude with `⟨u, by rw [← hw]; rfl⟩`. Take `⟨yy₀, hyy₀⟩` from `hPt (U.ι ≫ r') k x' hrange`.

Use `⟨yy₀ ≫ U.ι, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr'snd, ← hx'snd, ← hyy₀]`. Simplify using `only [Category.assoc]`. Rewrite using `[← hr'fst, ← hx'fst, ← hyy₀]`. Simplify using `only [Category.assoc]`.

Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[← Scheme.Opens.range_ι U]`. Conclude with `⟨yy₀ q, rfl⟩`.
-/
theorem exists_comp_cover_lift : (∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S) → (∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    (∀ Z : Comp Xo c, ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f))) →
    (∀ Z : Comp Xo' c', ∃ U : (Xo'.XF c').Opens, (U : Set (Xo'.XF c')) = Z ∧ ∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∀ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom),
      IsFinite (pullback.lift r _ h) → Etale (pullback.lift r _ h) → Surjective (pullback.lift r _ h) →
    ∀ Z : Comp Xo c, ∃ U : (Xo'.XF c').Opens, (∀ z ∈ U, r z ∈ (Z : Set (Xo.XF c))) ∧
      (∀ (k : Type) [Field k] (f : c'.F →+* k),
        IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
        x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
        Set.range x ⊆ (Z : Set (Xo.XF c)) →
        ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range yy ⊆ (U : Set (Xo'.XF c')) := by
  intro hTop hPt E _ _ _ H Dw l l' Xo Xo' c c' hle hIrr hIrr' r h hfin het hsurj Z
  set sF := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) with hsF
  set g := spMap (IntermediateField.inclusion hle).toRingHom with hg
  set r' := pullback.lift r _ h with hr'
  obtain ⟨U₀, hU₀, hU₀irr⟩ := hIrr Z

  have hirrB : IrreducibleSpace ↑(pullback (U₀.ι ≫ sF) g) := hU₀irr c'.F (IntermediateField.inclusion hle).toRingHom
  have hZc_eq : Set.range (pullback.snd U₀.ι (pullback.fst sF g)) = pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    ext w
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι, hU₀]
  have hZc_irr : IsIrreducible (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))) := by
    have hr : Set.range ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) =
        Set.range (pullback.snd U₀.ι (pullback.fst sF g)) := by
      rw [show ⇑((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) =
          ⇑(pullback.snd U₀.ι (pullback.fst sF g)) ∘ ⇑(pullbackRightPullbackFstIso sF g U₀.ι).inv from rfl, Set.range_comp, ((pullbackRightPullbackFstIso sF g U₀.ι).inv).surjective.range_eq,
        Set.image_univ]
    rw [← hZc_eq, ← hr, ← Set.image_univ]
    exact IrreducibleSpace.isIrreducible_univ _ |>.image _
      ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)).continuous.continuousOn
  have hZclosed : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hZopen : IsOpen (Z : Set (Xo.XF c)) := by rw [← hU₀]; exact U₀.2
  have hZc_clopen : IsClopen (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))) :=
    ⟨hZclosed.preimage (pullback.fst sF g).continuous, hZopen.preimage (pullback.fst sF g).continuous⟩
  have hr'open : IsOpenMap r' := r'.isOpenMap
  have hr'closed : IsClosedMap r' := r'.isClosedMap
  have hcompOpen : ∀ C ∈ irreducibleComponents (Xo'.XF c'), IsOpen C := by
    intro C hC
    obtain ⟨U, hU, -⟩ := hIrr' ⟨C, hC⟩
    rw [show C = (U : Set _) from hU.symm]; exact U.2
  obtain ⟨z, hz⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  obtain ⟨b, hb⟩ := (pullback.fst sF g).surjective z
  obtain ⟨a, ha⟩ := r'.surjective b
  have haZ : r' a ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
    simp only [Set.mem_preimage]; rw [ha, hb]; exact hz
  obtain ⟨C, hC, haC, hCim⟩ := hTop r' r'.continuous hr'open hr'closed hcompOpen _ hZc_clopen
    (IsIrreducible.isConnected hZc_irr).isPreconnected a haZ
  obtain ⟨U, hU, hUirr⟩ := hIrr' ⟨C, hC⟩
  have hUC : (U : Set (Xo'.XF c')) = C := hU
  have hr'fst : r' ≫ pullback.fst sF g = r := pullback.lift_fst _ _ _
  have hr'snd : r' ≫ pullback.snd sF g = pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) :=
    pullback.lift_snd _ _ _
  refine ⟨U, ?_, hUirr, ?_⟩
  · intro w hw
    have hw' : r' w ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
      rw [← hCim]; exact ⟨w, hUC ▸ hw, rfl⟩
    have : r w = pullback.fst sF g (r' w) := by rw [← hr'fst]; rfl
    rw [this]; exact hw'
  · intro k _ _ fK x hx hxZ
    have hcomm : x ≫ sF = spMap fK ≫ g := by
      rw [hx, hg]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    set x' := pullback.lift x (spMap fK) hcomm with hx'
    have hx'fst : x' ≫ pullback.fst sF g = x := pullback.lift_fst _ _ _
    have hx'snd : x' ≫ pullback.snd sF g = spMap fK := pullback.lift_snd _ _ _
    have hrange : Set.range x' ⊆ Set.range (U.ι ≫ r') := by
      rintro _ ⟨q, rfl⟩
      have hq : x' q ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
        simp only [Set.mem_preimage]
        have : pullback.fst sF g (x' q) = x q := by rw [← hx'fst]; rfl
        rw [this]; exact hxZ ⟨q, rfl⟩
      rw [← hCim] at hq
      obtain ⟨w, hwC, hw⟩ := hq
      have hwU : w ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι, hUC]; exact hwC
      obtain ⟨u, rfl⟩ := hwU
      exact ⟨u, by rw [← hw]; rfl⟩
    obtain ⟨yy₀, hyy₀⟩ := hPt (U.ι ≫ r') k x' hrange
    refine ⟨yy₀ ≫ U.ι, ?_, ?_, ?_⟩
    · rw [← hr'snd, ← hx'snd, ← hyy₀]; simp only [Category.assoc]
    · rw [← hr'fst, ← hx'fst, ← hyy₀]; simp only [Category.assoc]
    · rintro _ ⟨q, rfl⟩
      rw [← Scheme.Opens.range_ι U]
      exact ⟨yy₀ q, rfl⟩

end GlobalTheory.FlatModel
