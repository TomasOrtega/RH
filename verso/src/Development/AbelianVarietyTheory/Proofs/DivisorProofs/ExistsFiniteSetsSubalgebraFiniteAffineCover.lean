import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

/- English proof (translation)
Use `letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra`. Use `haveI := isLocalizationAway F α hα hU h`. Take `⟨n, a, e⟩` from `IsLocalization.Away.surj ((α.app (op U)).hom h) z`. Use `⟨a, n, ?_⟩` and prove the remaining obligations. Establish `nat` using `congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)`.

Simplify using `only [CommRingCat.comp_apply] at nat`. Rewrite using `[nat]`. Conclude with `e`.
-/
theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

/- English proof (translation)
Establish `hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)` using `X.toRingedSpace.isUnit_res_basicOpen h`. Take `⟨u, hu⟩` from `hu0`. Establish `key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) * (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1`. Rewrite using `[← map_mul, ← hu, Units.mul_inv, map_one]`. Establish `hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a * ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n`.

Rewrite using `[← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]`. Rewrite using `[hz]`. Conclude with `mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)`.
-/
theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

/- English proof (translation)
Introduce `X hX F α hα ι _ V hV S hS`. Use `choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)`. Establish `hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i`. Introduce `i j h hh`. Take `⟨r, hr⟩` from `hs1 i j h hh`.

Rewrite using `[hr]`. Conclude with `X.basicOpen_le r`. Use `haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype`. Use `choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) => GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1 ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)`. Use `⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩` and prove the remaining obligations.

Introduce `i x hx`. Rewrite using `[SetLike.mem_coe, mem_sub]`. Introduce `j W' hW' hWi hWj`. Apply `GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj` to reduce the goal to its premises. Introduce `y hy`.

Establish `hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X)` using `⟨hy.2, hy.1⟩`. Use `hs2 i j hy'` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨h, hh, hyh⟩` from `this`. Use `⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _ (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)`.
-/
theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
