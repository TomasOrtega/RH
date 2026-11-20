import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FiniteTypeApprox

/- English proof (translation)
Rewrite using `[← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ε.naturality, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]`.
-/
theorem nat_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ε.naturality, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

/- English proof (translation)
Rewrite using `[← ConcreteCategory.comp_apply, ← φ.comm, ConcreteCategory.comp_apply]`.
-/
theorem comm_apply {K L : AbCx} (φ : K ⟶ L) (i j : ℤ) (x : K.X i) :
    φ.f j (K.d i j x) = L.d i j (φ.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← φ.comm, ConcreteCategory.comp_apply]

/- English proof (translation)
Rewrite using `[Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]`.
-/
theorem map_comp_apply (N : CommRingCat.{0} ⥤ AbCx) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : (N.obj A).X n) : (N.map (f ≫ g)).f n x = (N.map g).f n ((N.map f).f n x) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_id_apply (N : CommRingCat.{0} ⥤ AbCx) (A : CommRingCat.{0}) (n : ℤ) (x : (N.obj A).X n) :
    (N.map (𝟙 A)).f n x = x := by
  simp

/- English proof (translation)
The claim follows from `(ConcreteCategory.bijective_of_isIso f).1 h`.
-/
theorem inj_of_iso {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] {x y : X} (h : f x = f y) : x = y :=
  (ConcreteCategory.bijective_of_isIso f).1 h

/- English proof (translation)
Rewrite using `[← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]`.
-/
theorem inv_apply_eq {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] (y : Y) : f (inv f y) = y := by
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/- English proof (translation)
Use `(AddCommGrpCat.isZero_iff_subsingleton.1 h)` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem eq_zero_of_isZero {X : AddCommGrpCat.{1}} (h : IsZero X) (x : X) : x = 0 := by
  have := (AddCommGrpCat.isZero_iff_subsingleton.1 h)
  exact Subsingleton.elim _ _

/- English proof (translation)
The claim follows from `(inferInstance : IsIso ((HomologicalComplex.eval _ _ n).map φ))`.
-/
theorem isIso_f {K L : AbCx} (φ : K ⟶ L) [IsIso φ] (n : ℤ) : IsIso (φ.f n) :=
  (inferInstance : IsIso ((HomologicalComplex.eval _ _ n).map φ))

/- English proof (translation)
Introduce `N M ε F0 ι hF0 hι hMneg hMpos hN hε`. Introduce `n A c hc hy`. Take `⟨y, hy⟩` from `hy`. Take `⟨J, _, _, D, ιD, ⟨hcol⟩, hft⟩` from `GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A`. Take `⟨-, hN2⟩` from `GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN`.

Take `⟨⟨hmul, hcob, -⟩, -, hftB⟩` from `GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties`. Take `⟨j, w, y', hw, hwc⟩` from `(hN2 J D (Cocone.mk A ιD) hcol n).1 c hc`. Express the relevant statement in the definitionally equal form `(N.map (ιD.app j)).f n w = c + (N.obj A).d (n - 1) n y' at hwc`. Establish `hwv : (M.obj (D.obj j)).d n (n + 1) ((ε.app (D.obj j)).f n w) = 0`. Rewrite using `[← comm_apply, hw, map_zero]`.

Establish `fin : (N.map (ιD.app j)).f n w = 0 → ∃ (V : CommRingCat.{0}) (g : A ⟶ V), EtFF g ∧ ∃ b : (N.obj V).X (n - 1), (N.obj V).d (n - 1) n b = (N.map g).f n c`. Introduce `h0`. Use `⟨A, 𝟙 A, MorphismProperty.id_mem EtFF A, -y', ?_⟩` and prove the remaining obligations. Rewrite using `[map_id_apply, map_neg]`. Rewrite `hwc` using `[h0]`.

Conclude with `(eq_neg_of_add_eq_zero_left hwc.symm).symm`. Break down `lt_trichotomy n 0 with hn | hn | hn` into its components or cases. Apply `fin` to reduce the goal to its premises. Use `haveI := hε _ (hft j)`. Use `haveI := isIso_f (ε.app (D.obj j)) n`.

Establish `: w = 0` using `inj_of_iso ((ε.app (D.obj j)).f n) ((eq_zero_of_isZero (hMneg n hn _) _).trans (map_zero _).symm)`. Rewrite using `[this, map_zero]`. Substitute `hn` using the available equality. Apply `fin` to reduce the goal to its premises. Establish `hy0 : y = 0` using `eq_zero_of_isZero (hMneg _ (by norm_num) _) y`.

Rewrite `hy` using `[hy0, map_zero]`. Take `⟨x0, hx0⟩` from `((hι (D.obj j)).2 _).1 hwv`. Establish `hιnat : ∀ {B C : CommRingCat.{0}} (g : B ⟶ C) (x : F0.obj B), ι.app C (F0.map g x) = (M.map g).f 0 (ι.app B x)`. Introduce `B C g x`. Rewrite using `[← ConcreteCategory.comp_apply, ι.naturality, ConcreteCategory.comp_apply]`.

Both sides reduce to the same expression. Establish `hdie : F0.map (ιD.app j) x0 = 0`. Apply `(hι A).1` to reduce the goal to its premises. Rewrite using `[hιnat, hx0, ← nat_apply, hwc, map_add, hy, comm_apply, eq_zero_of_isZero (hMneg _ (by norm_num) _) ((ε.app A).f (0 - 1) y'), map_zero, add_zero]`. Conclude with `(map_zero _).symm`.

Take `⟨-, hF0inj⟩` from `(GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A ιD) hcol`. Take `⟨k, f, hk⟩` from `hF0inj j x0 hdie`. Use `haveI := hε _ (hft k)`. Use `haveI := isIso_f (ε.app (D.obj k)) 0`. Establish `hwk : (N.map (D.map f)).f 0 w = 0`.

Apply `inj_of_iso ((ε.app (D.obj k)).f 0)` to reduce the goal to its premises. Rewrite using `[nat_apply, ← hx0, ← hιnat, hk, map_zero, map_zero]`. Both sides reduce to the same expression. Establish `hcw : ιD.app j = D.map f ≫ ιD.app k`. Use `ιD.naturality f` as an intermediate fact.

Simplify using `only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this`. Conclude with `this.symm`. Rewrite using `[hcw, map_comp_apply, hwk, map_zero]`. Take `⟨B0, g0, hg0, y0, hy0⟩` from `hMpos n hn _ _ hwv`. Establish `hB0` using `hftB _ _ g0 hg0 (hft j)`.

Use `haveI := hε _ hB0`. Use `haveI := isIso_f (ε.app B0) n`. Use `haveI := isIso_f (ε.app B0) (n - 1)`. Use `set b0 := inv ((ε.app B0).f (n - 1)) y0 with hb0`. Establish `hdb0 : (N.obj B0).d (n - 1) n b0 = (N.map g0).f n w`.

Apply `inj_of_iso ((ε.app B0).f n)` to reduce the goal to its premises. Rewrite using `[comm_apply, hb0, inv_apply_eq, hy0, nat_apply]`. Use `haveI := hcob`. Establish `hg : EtFF (pushout.inr g0 (ιD.app j))` using `MorphismProperty.pushout_inr _ _ hg0`. Use `⟨pushout g0 (ιD.app j), pushout.inr g0 (ιD.app j), hg, (N.map (pushout.inl g0 (ιD.app j))).f (n - 1) b0 - (N.map (pushout.inr g0 (ιD.app j))).f (n - 1) y', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, ← comm_apply, ← comm_apply, hdb0, ← map_comp_apply, pushout.condition, map_comp_apply, hwc, map_add]`. Conclude with `add_sub_cancel_right _ _`.
-/
theorem locInj_of_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  intro N M ε F0 ι hF0 hι hMneg hMpos hN hε
  intro n A c hc hy
  obtain ⟨y, hy⟩ := hy
  obtain ⟨J, _, _, D, ιD, ⟨hcol⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨-, hN2⟩ := GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN
  obtain ⟨⟨hmul, hcob, -⟩, -, hftB⟩ := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties
  obtain ⟨j, w, y', hw, hwc⟩ := (hN2 J D (Cocone.mk A ιD) hcol n).1 c hc
  change (N.map (ιD.app j)).f n w = c + (N.obj A).d (n - 1) n y' at hwc
  have hwv : (M.obj (D.obj j)).d n (n + 1) ((ε.app (D.obj j)).f n w) = 0 := by
    rw [← comm_apply, hw, map_zero]

  have fin : (N.map (ιD.app j)).f n w = 0 → ∃ (V : CommRingCat.{0}) (g : A ⟶ V), EtFF g ∧
      ∃ b : (N.obj V).X (n - 1), (N.obj V).d (n - 1) n b = (N.map g).f n c := by
    intro h0
    refine ⟨A, 𝟙 A, MorphismProperty.id_mem EtFF A, -y', ?_⟩
    rw [map_id_apply, map_neg]
    rw [h0] at hwc
    exact (eq_neg_of_add_eq_zero_left hwc.symm).symm
  rcases lt_trichotomy n 0 with hn | hn | hn
  ·
    apply fin
    haveI := hε _ (hft j)
    haveI := isIso_f (ε.app (D.obj j)) n
    have : w = 0 := inj_of_iso ((ε.app (D.obj j)).f n)
      ((eq_zero_of_isZero (hMneg n hn _) _).trans (map_zero _).symm)
    rw [this, map_zero]
  ·
    subst hn
    apply fin
    have hy0 : y = 0 := eq_zero_of_isZero (hMneg _ (by norm_num) _) y
    rw [hy0, map_zero] at hy
    obtain ⟨x0, hx0⟩ := ((hι (D.obj j)).2 _).1 hwv
    have hιnat : ∀ {B C : CommRingCat.{0}} (g : B ⟶ C) (x : F0.obj B),
        ι.app C (F0.map g x) = (M.map g).f 0 (ι.app B x) := by
      intro B C g x
      rw [← ConcreteCategory.comp_apply, ι.naturality, ConcreteCategory.comp_apply]
      rfl
    have hdie : F0.map (ιD.app j) x0 = 0 := by
      apply (hι A).1
      rw [hιnat, hx0, ← nat_apply, hwc, map_add, hy, comm_apply,
        eq_zero_of_isZero (hMneg _ (by norm_num) _) ((ε.app A).f (0 - 1) y'), map_zero, add_zero]
      exact (map_zero _).symm
    obtain ⟨-, hF0inj⟩ := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A ιD) hcol
    obtain ⟨k, f, hk⟩ := hF0inj j x0 hdie
    haveI := hε _ (hft k)
    haveI := isIso_f (ε.app (D.obj k)) 0
    have hwk : (N.map (D.map f)).f 0 w = 0 := by
      apply inj_of_iso ((ε.app (D.obj k)).f 0)
      rw [nat_apply, ← hx0, ← hιnat, hk, map_zero, map_zero]
      rfl
    have hcw : ιD.app j = D.map f ≫ ιD.app k := by
      have := ιD.naturality f
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this.symm
    rw [hcw, map_comp_apply, hwk, map_zero]
  ·
    obtain ⟨B0, g0, hg0, y0, hy0⟩ := hMpos n hn _ _ hwv
    have hB0 := hftB _ _ g0 hg0 (hft j)
    haveI := hε _ hB0
    haveI := isIso_f (ε.app B0) n
    haveI := isIso_f (ε.app B0) (n - 1)
    set b0 := inv ((ε.app B0).f (n - 1)) y0 with hb0
    have hdb0 : (N.obj B0).d (n - 1) n b0 = (N.map g0).f n w := by
      apply inj_of_iso ((ε.app B0).f n)
      rw [comm_apply, hb0, inv_apply_eq, hy0, nat_apply]
    haveI := hcob
    have hg : EtFF (pushout.inr g0 (ιD.app j)) := MorphismProperty.pushout_inr _ _ hg0
    refine ⟨pushout g0 (ιD.app j), pushout.inr g0 (ιD.app j), hg,
      (N.map (pushout.inl g0 (ιD.app j))).f (n - 1) b0 - (N.map (pushout.inr g0 (ιD.app j))).f (n - 1) y', ?_⟩
    rw [map_sub, ← comm_apply, ← comm_apply, hdb0, ← map_comp_apply, pushout.condition, map_comp_apply, hwc,
      map_add]
    exact add_sub_cancel_right _ _
end GlobalTheory.EtC.FiniteTypeApprox
