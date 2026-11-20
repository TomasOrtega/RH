import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Set `C : Fin m → Fin m → Set X.left` to `fun i j => closure (Set.range (equalizer.ι (s i) (s j)).left)`. Establish `hopen : IsOpen (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ)` using `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl`. Use `⟨⟨_, hopen⟩, ?_, ?_⟩` and prove the remaining obligations. Use `⟨genericPoint X.left, ?_⟩ show genericPoint X.left ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left)` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_compl_iff]`.

Introduce `i j hij hmem`. Apply `hij` to reduce the goal to its premises. Apply `hs` to reduce the goal to its premises. Establish `hg : closure ({genericPoint X.left} : Set X.left) = Set.univ` using `genericPoint_spec X.left`. Establish `huniv : C i j = Set.univ`.

Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Rewrite using `[← hg]`. Conclude with `closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure`. Establish `: IsDominant (equalizer.ι (s i) (s j)).left` using `⟨by`. Rewrite using `[DenseRange, dense_iff_closure_eq]`.

Conclude with `huniv⟩`. Use `ext1`. Conclude with `ext_of_isDominant_of_isSeparated G.hom (by simp) (equalizer.ι (s i) (s j)).left (by rw [← Over.comp_left, equalizer.condition, Over.comp_left])`. Introduce `T _ y hy i j hij`. Assume the negation of the conclusion as `hne`.

Take `⟨t⟩` from `‹Nonempty T.left›`. Establish `ht : y.left t ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left)` using `hy (Set.mem_univ t)`. Simplify using `only [Set.mem_iInter, Set.mem_compl_iff] at ht`. Apply `ht i j hne` to reduce the goal to its premises. Apply `subset_closure` to reduce the goal to its premises.

Use `⟨(equalizer.lift y hij).left t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]`.
-/
theorem exists_open_injective {S : Scheme.{0}} {X G : Over S} [IsIntegral X.left] [IsSeparated G.hom] {m : ℕ}
    (s : Fin m → (X ⟶ G)) (hs : Function.Injective s) :
    ∃ W : X.left.Opens, (W : Set X.left).Nonempty ∧ ∀ (T : Over S) [Nonempty T.left] (y : T ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ W → Function.Injective fun i => y ≫ s i := by
  classical
  let C : Fin m → Fin m → Set X.left := fun i j =>
    closure (Set.range (equalizer.ι (s i) (s j)).left)
  have hopen : IsOpen (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl
  refine ⟨⟨_, hopen⟩, ?_, ?_⟩
  · refine ⟨genericPoint X.left, ?_⟩
    show genericPoint X.left ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left)
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro i j hij hmem
    apply hij
    apply hs
    have hg : closure ({genericPoint X.left} : Set X.left) = Set.univ := genericPoint_spec X.left
    have huniv : C i j = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hg]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    have : IsDominant (equalizer.ι (s i) (s j)).left := ⟨by
      rw [DenseRange, dense_iff_closure_eq]; exact huniv⟩
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by simp) (equalizer.ι (s i) (s j)).left
      (by rw [← Over.comp_left, equalizer.condition, Over.comp_left])
  · intro T _ y hy i j hij
    by_contra hne
    obtain ⟨t⟩ := ‹Nonempty T.left›
    have ht : y.left t ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left) := hy (Set.mem_univ t)
    simp only [Set.mem_iInter, Set.mem_compl_iff] at ht
    apply ht i j hne
    apply subset_closure
    refine ⟨(equalizer.lift y hij).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]

/- English proof (translation)
Establish `hr` using `GlobalTheory.IsGenericPointHom.range_eq hj`. Take `⟨e, he⟩` from `hj`. Establish `hφ : ∀ i, (e.inv ≫ (P i).left) ≫ G.hom = Z.fromSpecStalk (genericPoint Z) ≫ c`. Introduce `i`. Rewrite using `[Category.assoc, Over.w (P i)]`.

Simplify using `[← he]`. Use `choose U hU f hf₁ hf₂ using fun i => spread_out_of_isGermInjective' c G.hom (e.inv ≫ (P i).left) (hφ i)`. Establish `hopen : IsOpen (⋂ i, (U i : Set Z))` using `isOpen_iInter_of_finite fun i => (U i).isOpen`. Set `V : Z.Opens` to `⟨_, hopen⟩`. Establish `hηV : genericPoint Z ∈ V` using `Set.mem_iInter.mpr hU`.

Establish `hle : ∀ i, V ≤ U i` using `fun i => Set.iInter_subset _ i`. Establish `hres : ∀ i, V.fromSpecStalkOfMem _ hηV ≫ Z.homOfLE (hle i) = (U i).fromSpecStalkOfMem _ (hU i)`. Introduce `i`. Rewrite using `[← cancel_mono (U i).ι]`. Simplify using `[Scheme.Opens.fromSpecStalkOfMem_ι]`.

Use `⟨V, hηV, Over.homMk (e.hom ≫ V.fromSpecStalkOfMem _ hηV) ?_, ?_, fun i => Over.homMk (Z.homOfLE (hle i) ≫ f i) ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Scheme.Opens.fromSpecStalkOfMem_ι_assoc, ← he]`. Use `show IsDominant (e.hom ≫ V.fromSpecStalkOfMem _ hηV)`. Rewrite using `[isDominant_iff, DenseRange, dense_iff_inter_open]`. Introduce and unpack `W hW ⟨w, hw⟩`.

Establish `h1 : IsOpen (V.ι '' W)` using `V.ι.isOpenEmbedding.isOpenMap _ hW`. Take `⟨v, hvW, hv⟩` from `((genericPoint_spec Z).mem_open_set_iff h1).mpr ⟨_, trivial, w, hw, rfl⟩`. Establish `hη : genericPoint Z ∈ Set.range j` using `by rw [hr]; rfl`. Take `⟨y, hy⟩` from `hη`. Use `⟨v, hvW, y, ?_⟩` and prove the remaining obligations.

Apply `V.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, he, hy, hv]`. Rewrite using `[Category.assoc, hf₂, Scheme.homOfLE_ι_assoc]`. Both sides reduce to the same expression. Introduce `i ext1`.

Simplify using `only [Over.comp_left, Over.homMk_left, Category.assoc]`. Rewrite using `[reassoc_of% (hres i), ← hf₁, Iso.hom_inv_id_assoc]`.
-/
theorem exists_spread {Z S Y : Scheme.{0}} [IsIntegral Z] (c : Z ⟶ S) (G : Over S) [LocallyOfFiniteType G.hom]
    (j : Y ⟶ Z) (hj : GlobalTheory.IsGenericPointHom j) {m : ℕ} (P : Fin m → (Over.mk (j ≫ c) ⟶ G)) :
    ∃ (U : Z.Opens) (_ : genericPoint Z ∈ U) (k : Over.mk (j ≫ c) ⟶ Over.mk (U.ι ≫ c)) (_ : IsDominant k.left)
      (s : Fin m → (Over.mk (U.ι ≫ c) ⟶ G)), ∀ i, k ≫ s i = P i := by
  classical
  have hr := GlobalTheory.IsGenericPointHom.range_eq hj
  obtain ⟨e, he⟩ := hj
  have hφ : ∀ i, (e.inv ≫ (P i).left) ≫ G.hom = Z.fromSpecStalk (genericPoint Z) ≫ c := by
    intro i
    rw [Category.assoc, Over.w (P i)]
    simp [← he]
  choose U hU f hf₁ hf₂ using fun i =>
    spread_out_of_isGermInjective' c G.hom (e.inv ≫ (P i).left) (hφ i)
  have hopen : IsOpen (⋂ i, (U i : Set Z)) := isOpen_iInter_of_finite fun i => (U i).isOpen
  let V : Z.Opens := ⟨_, hopen⟩
  have hηV : genericPoint Z ∈ V := Set.mem_iInter.mpr hU
  have hle : ∀ i, V ≤ U i := fun i => Set.iInter_subset _ i
  have hres : ∀ i, V.fromSpecStalkOfMem _ hηV ≫ Z.homOfLE (hle i) =
      (U i).fromSpecStalkOfMem _ (hU i) := by
    intro i
    rw [← cancel_mono (U i).ι]
    simp [Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨V, hηV, Over.homMk (e.hom ≫ V.fromSpecStalkOfMem _ hηV) ?_, ?_,
    fun i => Over.homMk (Z.homOfLE (hle i) ≫ f i) ?_, ?_⟩
  · simp [Scheme.Opens.fromSpecStalkOfMem_ι_assoc, ← he]
  · show IsDominant (e.hom ≫ V.fromSpecStalkOfMem _ hηV)
    rw [isDominant_iff, DenseRange, dense_iff_inter_open]
    rintro W hW ⟨w, hw⟩
    have h1 : IsOpen (V.ι '' W) := V.ι.isOpenEmbedding.isOpenMap _ hW
    obtain ⟨v, hvW, hv⟩ :=
      ((genericPoint_spec Z).mem_open_set_iff h1).mpr ⟨_, trivial, w, hw, rfl⟩
    have hη : genericPoint Z ∈ Set.range j := by rw [hr]; rfl
    obtain ⟨y, hy⟩ := hη
    refine ⟨v, hvW, y, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, he, hy, hv]
  · rw [Category.assoc, hf₂, Scheme.homOfLE_ι_assoc]
    rfl
  · intro i
    ext1
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [reassoc_of% (hres i), ← hf₁, Iso.hom_inv_id_assoc]

end PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `Z' S _ c G _ _ _ L' _ j hj m P hP hP2`. Take `⟨U, hηU, k, hk, s, hs⟩` from `PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_spread c G j hj P`. Use `haveI : Nonempty U := ⟨⟨_, hηU⟩⟩`. Use `haveI : IsIntegral (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsIntegral U.toScheme)`. Use `haveI : IsReduced (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsReduced U.toScheme)`.

Establish `hsinj : Function.Injective s` using `fun a b hab => hP (by rw [← hs a, ← hs b, hab])`. Establish `hs2 : ∀ i, s i ^ 2 = 1`. Introduce `i`. Establish `h1 : k ≫ s i ^ 2 = k ≫ 1`. Rewrite using `[pow_two, MonObj.comp_mul, ← pow_two, hs i, hP2 i]`.

Simplify using the standard rewrite rules. Use `ext1`. Conclude with `ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w, Over.w]) k.left (by rw [← Over.comp_left, h1, Over.comp_left])`. Take `⟨W, hWne, hW⟩` from `PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_open_injective (X := Over.mk (U.ι ≫ c)) s hsinj`. Take `⟨w, hw⟩` from `hWne`.

Use `⟨U.ι ''ᵁ W, ⟨U.ι w, w, hw, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `K _ x hx`. Establish `hxW : ∀ t, ∃ w ∈ W, U.ι w = x t`. Introduce `t`. Take `⟨w, hw, hwt⟩` from `hx (Set.mem_univ t)`.

Conclude with `⟨w, hw, hwt⟩`. Set `x'` to `IsOpenImmersion.lift U.ι x (by`. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨w, -, h⟩` from `hxW t`. Conclude with `⟨w, h⟩)`.

Set `y : Over.mk (x ≫ c) ⟶ Over.mk (U.ι ≫ c)` to `Over.homMk x' (by`. Simplify using `only [Over.mk_hom]`. Rewrite using `[IsOpenImmersion.lift_fac_assoc])`. Use `haveI : Nonempty (Over.mk (x ≫ c)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))`. Use `⟨fun i => y ≫ s i, hW (Over.mk (x ≫ c)) y ?_, fun i => ?_⟩` and prove the remaining obligations.

Introduce `t _ show x' t ∈ W`. Take `⟨w, hw, hwt⟩` from `hxW t`. Establish `: x' t = w` using `U.ι.isOpenEmbedding.injective (by`. Rewrite using `[← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hwt])`. Rewrite using `[this]`.

Conclude with `hw`. Use `show (y ≫ s i) ^ 2 = 1`. Rewrite using `[pow_two, ← MonObj.comp_mul, ← pow_two, hs2 i]`. Simplify using the standard rewrite rules.
-/
theorem PositivityTheory.Xgn.two_torsion_points_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  intro Z' S _ c G _ _ _ L' _ j hj m P hP hP2
  obtain ⟨U, hηU, k, hk, s, hs⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_spread c G j hj P
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsIntegral (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsIntegral U.toScheme)
  haveI : IsReduced (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsReduced U.toScheme)
  have hsinj : Function.Injective s := fun a b hab => hP (by rw [← hs a, ← hs b, hab])
  have hs2 : ∀ i, s i ^ 2 = 1 := by
    intro i
    have h1 : k ≫ s i ^ 2 = k ≫ 1 := by
      rw [pow_two, MonObj.comp_mul, ← pow_two, hs i, hP2 i]
      simp
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w, Over.w]) k.left
      (by rw [← Over.comp_left, h1, Over.comp_left])
  obtain ⟨W, hWne, hW⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_open_injective (X := Over.mk (U.ι ≫ c)) s hsinj
  obtain ⟨w, hw⟩ := hWne
  refine ⟨U.ι ''ᵁ W, ⟨U.ι w, w, hw, rfl⟩, ?_⟩
  intro K _ x hx
  have hxW : ∀ t, ∃ w ∈ W, U.ι w = x t := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hx (Set.mem_univ t)
    exact ⟨w, hw, hwt⟩
  let x' := IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, -, h⟩ := hxW t
    exact ⟨w, h⟩)
  let y : Over.mk (x ≫ c) ⟶ Over.mk (U.ι ≫ c) := Over.homMk x' (by
    simp only [Over.mk_hom]
    rw [IsOpenImmersion.lift_fac_assoc])
  haveI : Nonempty (Over.mk (x ≫ c)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  refine ⟨fun i => y ≫ s i, hW (Over.mk (x ≫ c)) y ?_, fun i => ?_⟩
  · intro t _
    show x' t ∈ W
    obtain ⟨w, hw, hwt⟩ := hxW t
    have : x' t = w := U.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hwt])
    rw [this]
    exact hw
  · show (y ≫ s i) ^ 2 = 1
    rw [pow_two, ← MonObj.comp_mul, ← pow_two, hs2 i]
    simp
