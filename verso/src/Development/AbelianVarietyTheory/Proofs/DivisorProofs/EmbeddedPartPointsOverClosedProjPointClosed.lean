import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibClosed

/- English proof (translation)
Set `m : F ⟶ pullback g q` to `pullback.lift φ p h`. Establish `hm : m ≫ pullback.snd g q = p` using `pullback.lift_snd _ _ _`. Establish `: IsProper (m ≫ pullback.snd g q)` using `by rw [hm]; infer_instance`. Establish `: IsProper m` using `IsProper.of_comp m (pullback.snd g q)`. Establish `hcl : IsClosed (Set.range m)` using `m.isClosedMap.isClosed_range`.

Establish `hemb : Topology.IsEmbedding (pullback.fst g q)` using `(pullback.fst g q).isEmbedding`. Take `⟨C, hC, hCe⟩` from `hemb.isInducing.isClosed_iff.1 hcl`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hCe, ← Set.range_comp]`. Use `congr 1`.

Use extensionality with `x`. Use `show (m ≫ pullback.fst g q) x = φ x`. Rewrite using `[pullback.lift_fst]`.
-/
theorem closed_in_preimage {F X P B : Scheme.{0}} (p : F ⟶ B) (q : B ⟶ P) (φ : F ⟶ X) (g : X ⟶ P) [IsProper p]
    [IsPreimmersion q] [IsSeparated g] (h : φ ≫ g = p ≫ q) :
    ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' Set.range q = Set.range φ := by
  let m : F ⟶ pullback g q := pullback.lift φ p h
  have hm : m ≫ pullback.snd g q = p := pullback.lift_snd _ _ _
  have : IsProper (m ≫ pullback.snd g q) := by rw [hm]; infer_instance
  have : IsProper m := IsProper.of_comp m (pullback.snd g q)
  have hcl : IsClosed (Set.range m) := m.isClosedMap.isClosed_range
  have hemb : Topology.IsEmbedding (pullback.fst g q) := (pullback.fst g q).isEmbedding
  obtain ⟨C, hC, hCe⟩ := hemb.isInducing.isClosed_iff.1 hcl
  refine ⟨C, hC, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hCe, ← Set.range_comp]
  congr 1
  ext x
  show (m ≫ pullback.fst g q) x = φ x
  rw [pullback.lift_fst]

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

/- English proof (translation)
Establish `hcp : IsClosed ({closedPoint R} : Set (Sp R))` using `isClosed_singleton_closedPoint R`. Set `Z : TopologicalSpace.Closeds S` to `⟨π ⁻¹' {closedPoint R}, hcp.preimage π.continuous⟩`. Set `Z₀ : TopologicalSpace.Closeds (Sp R)` to `⟨{closedPoint R}, hcp⟩`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal Z`. Set `t` to `I.subschemeι`.

Establish `hrt : Set.range t = π ⁻¹' {closedPoint R}`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Both sides reduce to the same expression. Establish `: IsReduced I.subscheme` using `GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z`. Establish `: IsLocallyNoetherian S` using `LocallyOfFiniteType.isLocallyNoetherian π`.

Establish `: IsLocallyNoetherian I.subscheme` using `LocallyOfFiniteType.isLocallyNoetherian t`. Establish `: IsClosedImmersion (spMap (residue R))` using `IsClosedImmersion.spec_of_surjective _ residue_surjective`. Establish `hr : Set.range (t ≫ π) ⊆ (Z₀ : Set (Sp R))`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: t x ∈ Set.range t` using `⟨x, rfl⟩`.

Rewrite `this` using `[hrt]`. Conclude with `this`. Establish `h1 : Scheme.IdealSheafData.vanishingIdeal Z₀ ≤ (t ≫ π).ker` using `GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker (t ≫ π) Z₀ hr`. Establish `h2 : (spMap (residue R)).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z₀`. Rewrite using `[← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]`.

Introduce `x hx`. Establish `hx' : x = closedPoint R` using `hx`. Rewrite using `[← SetLike.mem_coe, Scheme.Hom.support_ker]`. Use `subset_closure ⟨closedPoint (ResidueField R), ?_⟩` and prove the remaining obligations. Rewrite using `[hx']`.

Conclude with `IsLocalRing.comap_closedPoint (residue R)`. Set `k` to `IsClosedImmersion.lift (spMap (residue R)) (t ≫ π) (h2.trans h1)`. Establish `hk : k ≫ spMap (residue R) = t ≫ π` using `IsClosedImmersion.lift_fac _ _ _`. Establish `: IsProper (k ≫ spMap (residue R))` using `by rw [hk]; infer_instance`. Establish `: IsProper k` using `IsProper.of_comp k (spMap (residue R))`.

Conclude with `⟨I.subscheme, t, k, inferInstance, inferInstance, inferInstance, hk.symm, hrt⟩`.
-/
theorem exists_redFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    [IsProper π] : ∃ (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T ∧ IsReduced T ∧
      IsProper k ∧ t ≫ π = k ≫ spMap (residue R) ∧ Set.range t = π ⁻¹' {closedPoint R} := by
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  let Z : TopologicalSpace.Closeds S := ⟨π ⁻¹' {closedPoint R}, hcp.preimage π.continuous⟩
  let Z₀ : TopologicalSpace.Closeds (Sp R) := ⟨{closedPoint R}, hcp⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let t := I.subschemeι
  have hrt : Set.range t = π ⁻¹' {closedPoint R} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  have hr : Set.range (t ≫ π) ⊆ (Z₀ : Set (Sp R)) := by
    rintro _ ⟨x, rfl⟩
    have : t x ∈ Set.range t := ⟨x, rfl⟩
    rw [hrt] at this
    exact this
  have h1 : Scheme.IdealSheafData.vanishingIdeal Z₀ ≤ (t ≫ π).ker :=
    GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker (t ≫ π) Z₀ hr
  have h2 : (spMap (residue R)).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z₀ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x = closedPoint R := hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    refine subset_closure ⟨closedPoint (ResidueField R), ?_⟩
    rw [hx']
    exact IsLocalRing.comap_closedPoint (residue R)
  let k := IsClosedImmersion.lift (spMap (residue R)) (t ≫ π) (h2.trans h1)
  have hk : k ≫ spMap (residue R) = t ≫ π := IsClosedImmersion.lift_fac _ _ _
  have : IsProper (k ≫ spMap (residue R)) := by rw [hk]; infer_instance
  have : IsProper k := IsProper.of_comp k (spMap (residue R))
  exact ⟨I.subscheme, t, k, inferInstance, inferInstance, inferInstance, hk.symm, hrt⟩

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

/- English proof (translation)
The claim follows from `h ▸ rfl`.
-/
theorem ap {A B : Scheme.{0}} {f f' : A ⟶ B} (h : f = f') (x : A) : f x = f' x := h ▸ rfl

/- English proof (translation)
Introduce `R _ _ _ S π hπ G' _ hG E H' X o g hg hog hH' w hw`. Use `haveI := hπ`. Use `haveI := hg`. Take `⟨T, t, k, hTn, hTr, hk, htk, hrt⟩` from `exists_redFibre R S π`. Take `⟨e, l, -, hl, hlf⟩` from `GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t k hTn hTr htk`.

Establish `hover : ∀ p, π (G'.hom (E.H.ι (l p))) = closedPoint R`. Introduce `p`. Establish `h1 : E.H.ι (l p) = pullback.fst G'.hom t p`. Rewrite using `[← ap hl p, Scheme.Hom.comp_apply]`. Establish `h2 : G'.hom (pullback.fst G'.hom t p) = t (pullback.snd G'.hom t p)`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Establish `h3 : t (pullback.snd G'.hom t p) ∈ Set.range t` using `⟨_, rfl⟩`. Rewrite `h3` using `[hrt]`. Rewrite using `[h1, h2]`. Conclude with `h3`.

Establish `hrl : Set.range l ⊆ Set.range H'.ι`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hH' _ (hover p)`. Set `l'` to `IsOpenImmersion.lift H'.ι l hrl`.

Establish `hl' : l' ≫ H'.ι = l` using `IsOpenImmersion.lift_fac _ _ _`. Establish `key : ∀ z : H'.toScheme, g (o z) = w → ∃ p, l' p = z ∧ E.j (pullback.fst E.Y.hom k (e.hom p)) = w`. Introduce `z hz`. Establish `hfz : E.f (H'.ι z) = w`. Rewrite using `[← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hog]`.

Establish `hcl : π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R`. Use `ap E.f_over (H'.ι z)` as an intermediate fact. Simplify using `only [Scheme.Hom.comp_apply] at this`. Rewrite using `[← this, hfz, hw]`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : E.H.ι (H'.ι z) ∈ Set.range (pullback.fst G'.hom t) := by`.

Rewrite using `[Scheme.Pullback.range_fst]`. Use `show G'.hom _ ∈ Set.range t`. Rewrite using `[hrt]`. Conclude with `hcl`. Establish `hlp : l p = H'.ι z` using `E.H.ι.isOpenEmbedding.injective (by`.

Rewrite using `[← hp, ← ap hl p, Scheme.Hom.comp_apply])`. Use `⟨p, H'.ι.isOpenEmbedding.injective (by rw [← hlp, ← ap hl' p, Scheme.Hom.comp_apply]), ?_⟩` and prove the remaining obligations. Rewrite using `[← hfz, ← hlp]`. Establish `h` using `ap hlf p`. Simplify using `only [Scheme.Hom.comp_apply] at h`.

Conclude with `h.symm`. Distinguish the cases in `hy : ∃ y, E.j y = w`. Take `⟨y, rfl⟩` from `hy haveI := E.imm`. Set `F` to `pullback (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)`. Set `φ : F ⟶ X` to `pullback.fst _ _ ≫ e.inv ≫ l' ≫ o`.

Establish `hφ : φ ≫ g = pullback.snd _ _ ≫ (E.Y.left.fromSpecResidueField y ≫ E.j)`. Simplify using `only [φ, Category.assoc, hog]`. Rewrite using `[reassoc_of% hl', hlf, Iso.inv_hom_id_assoc, pullback.condition_assoc]`. Take `⟨C, hC, hCe⟩` from `closed_in_preimage (pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)) _ φ g hφ`. Establish `hrange : Set.range (E.Y.left.fromSpecResidueField y ≫ E.j) = {E.j y}`.

Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `: E.Y.left.fromSpecResidueField y a ∈ Set.range (E.Y.left.fromSpecResidueField y)` using `⟨a, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Rewrite using `[this]`. Introduce and unpack `rfl`. Establish `: y ∈ Set.range (E.Y.left.fromSpecResidueField y)`. Rewrite using `[Scheme.range_fromSpecResidueField]`.

Both sides reduce to the same expression. Take `⟨a, ha⟩` from `this`. Conclude with `⟨a, by rw [ha]⟩`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrange, hCe]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨⟨(pullback.fst _ _ ≫ e.inv ≫ l') a, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show o _ = φ a`.

Simplify using `only [φ, Scheme.Hom.comp_apply]`. Rewrite using `[Set.mem_preimage, ← Scheme.Hom.comp_apply, hφ]`. Conclude with `⟨pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y) a, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Introduce and unpack `⟨⟨z, rfl⟩, hz⟩`. Rewrite `hz` using `[hrange]`.

Take `⟨p, hp, hpj⟩` from `key z hz`. Establish `hyp : pullback.fst E.Y.hom k (e.hom p) = y` using `E.j.isEmbedding.injective hpj`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : e.hom p ∈ Set.range (pullback.fst (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)) := by`. Rewrite using `[Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]`. Conclude with `hyp`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [φ, Scheme.Hom.comp_apply]`. Establish `h` using `ap e.hom_inv_id p`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Rewrite using `[ha, h]`.

Conclude with `congrArg o hp`. Use `⟨∅, isClosed_empty, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.empty_inter, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff, false_iff, not_and]`. Introduce and unpack `⟨z, rfl⟩ hz`.

Take `⟨p, -, hpj⟩` from `key z hz`. Conclude with `hy ⟨_, hpj⟩`.
-/
theorem range_inter_fibre_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  intro R _ _ _ S π hπ G' _ hG E H' X o g hg hog hH' w hw
  haveI := hπ
  haveI := hg
  obtain ⟨T, t, k, hTn, hTr, hk, htk, hrt⟩ := exists_redFibre R S π
  obtain ⟨e, l, -, hl, hlf⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t k hTn hTr htk
  have hover : ∀ p, π (G'.hom (E.H.ι (l p))) = closedPoint R := by
    intro p
    have h1 : E.H.ι (l p) = pullback.fst G'.hom t p := by
      rw [← ap hl p, Scheme.Hom.comp_apply]
    have h2 : G'.hom (pullback.fst G'.hom t p) = t (pullback.snd G'.hom t p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have h3 : t (pullback.snd G'.hom t p) ∈ Set.range t := ⟨_, rfl⟩
    rw [hrt] at h3
    rw [h1, h2]; exact h3
  have hrl : Set.range l ⊆ Set.range H'.ι := by
    rintro _ ⟨p, rfl⟩; rw [Scheme.Opens.range_ι]; exact hH' _ (hover p)
  let l' := IsOpenImmersion.lift H'.ι l hrl
  have hl' : l' ≫ H'.ι = l := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ z : H'.toScheme, g (o z) = w →
      ∃ p, l' p = z ∧ E.j (pullback.fst E.Y.hom k (e.hom p)) = w := by
    intro z hz
    have hfz : E.f (H'.ι z) = w := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hog]
    have hcl : π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R := by
      have := ap E.f_over (H'.ι z)
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hfz, hw]
    obtain ⟨p, hp⟩ : E.H.ι (H'.ι z) ∈ Set.range (pullback.fst G'.hom t) := by
      rw [Scheme.Pullback.range_fst]
      show G'.hom _ ∈ Set.range t
      rw [hrt]; exact hcl
    have hlp : l p = H'.ι z := E.H.ι.isOpenEmbedding.injective (by
      rw [← hp, ← ap hl p, Scheme.Hom.comp_apply])
    refine ⟨p, H'.ι.isOpenEmbedding.injective (by rw [← hlp, ← ap hl' p, Scheme.Hom.comp_apply]), ?_⟩
    rw [← hfz, ← hlp]
    have h := ap hlf p
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  by_cases hy : ∃ y, E.j y = w
  · obtain ⟨y, rfl⟩ := hy
    haveI := E.imm
    let F := pullback (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)
    let φ : F ⟶ X := pullback.fst _ _ ≫ e.inv ≫ l' ≫ o
    have hφ : φ ≫ g = pullback.snd _ _ ≫ (E.Y.left.fromSpecResidueField y ≫ E.j) := by
      simp only [φ, Category.assoc, hog]
      rw [reassoc_of% hl', hlf, Iso.inv_hom_id_assoc, pullback.condition_assoc]
    obtain ⟨C, hC, hCe⟩ := closed_in_preimage (pullback.snd (pullback.fst E.Y.hom k)
      (E.Y.left.fromSpecResidueField y)) _ φ g hφ
    have hrange : Set.range (E.Y.left.fromSpecResidueField y ≫ E.j) = {E.j y} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        have : E.Y.left.fromSpecResidueField y a ∈ Set.range (E.Y.left.fromSpecResidueField y) := ⟨a, rfl⟩
        rw [Scheme.range_fromSpecResidueField] at this
        rw [this]
      · rintro rfl
        have : y ∈ Set.range (E.Y.left.fromSpecResidueField y) := by
          rw [Scheme.range_fromSpecResidueField]; rfl
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [ha]⟩
    refine ⟨C, hC, ?_⟩
    rw [← hrange, hCe]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨(pullback.fst _ _ ≫ e.inv ≫ l') a, ?_⟩, ?_⟩
      · show o _ = φ a
        simp only [φ, Scheme.Hom.comp_apply]
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hφ]
        exact ⟨pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y) a,
          (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      rw [hrange] at hz
      obtain ⟨p, hp, hpj⟩ := key z hz
      have hyp : pullback.fst E.Y.hom k (e.hom p) = y := E.j.isEmbedding.injective hpj
      obtain ⟨a, ha⟩ : e.hom p ∈ Set.range (pullback.fst (pullback.fst E.Y.hom k)
          (E.Y.left.fromSpecResidueField y)) := by
        rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
        exact hyp
      refine ⟨a, ?_⟩
      simp only [φ, Scheme.Hom.comp_apply]
      have h := ap e.hom_inv_id p
      simp only [Scheme.Hom.comp_apply] at h
      rw [ha, h]
      exact congrArg o hp
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    simp only [Set.empty_inter, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff, false_iff, not_and]
    rintro ⟨z, rfl⟩ hz
    obtain ⟨p, -, hpj⟩ := key z hz
    exact hy ⟨_, hpj⟩

end GlobalTheory.Mum.FibClosed
