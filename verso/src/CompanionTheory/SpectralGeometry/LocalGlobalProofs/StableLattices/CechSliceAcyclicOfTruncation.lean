import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

open GlobalTheory.Cube in

/- English proof (translation)
Establish `hsub : ∀ u, u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}} → u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1}`. Introduce `u hu`. Use `⟨hu.1, ?_⟩` and prove the remaining obligations. Establish `: part (inrEmb ν κ) u = {j}` using `hu.2`. Simplify using `[this]`.

Establish `heq : ∀ {a b : Finset κ}, a ⊆ b → a = {j} → b.card = 1 → b = {j}`. Introduce and unpack `a b hab rfl hb`. Take `⟨c, rfl⟩` from `Finset.card_eq_one.1 hb`. Rewrite using `[Finset.singleton_subset_singleton.1 hab]`. Establish `heq' : ∀ {a b : Finset κ}, a ⊆ b → a.card = 1 → b = {j} → a = {j}`.

Introduce and unpack `a b hab ha rfl`. Take `⟨c, rfl⟩` from `Finset.card_eq_one.1 ha`. Rewrite using `[Finset.singleton_subset_singleton.1 hab]`. Set `i : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}}) (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) ⟶ supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₁)` to `suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true ⟨ht.1, heq (monotone_part _ hst) hs.2 ht.2⟩ (hsub s hs)`. Set `r : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₁) ⟶ supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}}) (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton)` to `suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true (hsub t ht) ⟨hs.1, heq' (monotone_part _ hst) hs.2 ht.2⟩`.

Establish `hir : i ≫ r = 𝟙 _`. Use extensionality with `s x`. Use `supp_ext fun hs => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `suppEquiv A _ hs (suppMapApp (𝟙 A) _ _ s (suppMapApp (𝟙 A) _ _ s x)) = suppEquiv A _ hs x`. Rewrite using `[suppEquiv_suppMapApp _ (hsub s hs) hs, suppEquiv_suppMapApp _ hs (hsub s hs)]`.

Both sides reduce to the same expression. Rewrite using `[Limits.IsZero.iff_id_eq_zero]`. Establish `hc : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n ≫ HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map r) n = 𝟙 _`. Rewrite using `[← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]`. Establish `hz : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n = 0` using `h.eq_of_tgt _ _`.

Rewrite `hc` using `[hz, Limits.zero_comp]`. Conclude with `hc.symm`.
-/
theorem isZero_homology_supp_singleton {ν κ : Type} [LinearOrder ν] [LinearOrder κ] {R : Type}
    [CommRing R] (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R) {Q : Set (Finset ν)} (hQ : Q.OrdConnected)
    (hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1}) (j : κ) (n : ℕ)
    (h : Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q
      {t : Finset κ | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₁))).homology n)) :
    Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology n) := by
  have hsub : ∀ u, u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}} →
      u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1} := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have : part (inrEmb ν κ) u = {j} := hu.2
    simp [this]
  have heq : ∀ {a b : Finset κ}, a ⊆ b → a = {j} → b.card = 1 → b = {j} := by
    rintro a b hab rfl hb
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hb
    rw [Finset.singleton_subset_singleton.1 hab]
  have heq' : ∀ {a b : Finset κ}, a ⊆ b → a.card = 1 → b = {j} → a = {j} := by
    rintro a b hab ha rfl
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 ha
    rw [Finset.singleton_subset_singleton.1 hab]
  let i : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) :=
    suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true
      ⟨ht.1, heq (monotone_part _ hst) hs.2 ht.2⟩ (hsub s hs)
  let r : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) :=
    suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true (hsub t ht)
      ⟨hs.1, heq' (monotone_part _ hst) hs.2 ht.2⟩
  have hir : i ≫ r = 𝟙 _ := by
    ext s x
    refine supp_ext fun hs => ?_
    change suppEquiv A _ hs (suppMapApp (𝟙 A) _ _ s (suppMapApp (𝟙 A) _ _ s x)) =
      suppEquiv A _ hs x
    rw [suppEquiv_suppMapApp _ (hsub s hs) hs, suppEquiv_suppMapApp _ hs (hsub s hs)]
    rfl
  rw [Limits.IsZero.iff_id_eq_zero]
  have hc : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n ≫
      HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map r) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hz : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n = 0 :=
    h.eq_of_tgt _ _
  rw [hz, Limits.zero_comp] at hc
  exact hc.symm

open GlobalTheory.Cube in

/- English proof (translation)
Introduce `ν κ _ _ _ _ R _ A hA hT j`. Establish `hcompl` using `isCompl_range_inlEmb_inrEmb ν κ`. Establish `hQ : Set.OrdConnected {s : Finset ν | s.Nonempty}` using `ordConnected_nonempty`. Establish `hU₂ : IsUpperSet {t : Finset κ | 2 ≤ t.card}` using `fun _ _ hst ht => le_trans ht (Finset.card_le_card hst)`. Establish `hT₂` using `hU₂.ordConnected`.

Establish `hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1}`. Use `⟨fun a ha b hb c hc => ?_⟩` and prove the remaining obligations. Establish `h1` using `Finset.card_le_card hc.1`. Establish `h2` using `Finset.card_le_card hc.2`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hS` using `GlobalTheory.cubeFunctor_shortExact _ (suppSequence_shortExact A (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂) (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ ordConnected_nonempty) (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₁) (fun u => by`. Establish `hc : (part (inrEmb ν κ) u).Nonempty ↔ 2 ≤ (part (inrEmb ν κ) u).card ∨ (part (inrEmb ν κ) u).card = 1`. Rewrite using `[← Finset.card_pos]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [mem_partsIn, Set.mem_setOf_eq]`. Use the proof step `tauto)`. Use the proof step `(fun u hu hu' => by`. Establish `h1 : 2 ≤ (part (inrEmb ν κ) u).card` using `hu.2`. Establish `h2 : (part (inrEmb ν κ) u).card = 1` using `hu'.2`.

Use the proof step `omega)`. Use the proof step `(fun _ _ hst hs ht => ⟨ht.1, hU₂ (monotone_part _ hst) hs.2⟩))`. Establish `h₁ : (GlobalTheory.cubeComplex (supp A _ (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂))).Acyclic`. Rewrite using `[supp_partsIn_comm hQ hT₂ A]`. Use `GlobalTheory.cubeComplex_supp_partsIn_acyclic hcompl.symm hT₂ hQ A fun t ht => ?_` and prove the remaining obligations.

Use `(GlobalTheory.cubeComplex_trunc₁_acyclic_iff _).2 ?_` and prove the remaining obligations. Rewrite using `[← sliceFst_eq_slice]`. Conclude with `hA t ht`. Establish `hzero : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) {s : Finset ν | s.Nonempty} {{j}}) (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology (n + 2))` using `fun n => by`. Use `isZero_homology_supp_singleton A hQ hT₁ j (n + 2) ?_` and prove the remaining obligations.

Use `GlobalTheory.isIso_homologyMap_g_of_acyclic hS h₁ (n + 2)` as an intermediate fact. Conclude with `(hT n).of_iso (@asIso _ _ _ _ _ this).symm`. Introduce `n`. Rewrite using `[HomologicalComplex.exactAt_iff_isZero_homology]`. Use `((hzero n).of_iso (GlobalTheory.suppSingletonHomologyIso hcompl hQ j A (n + 1)).symm).of_iso (GlobalTheory.cechHomologyMapIso (eqToIso (sliceFst_eq_slice A {j})) n ≪≫ (GlobalTheory.truncHomologyIso _ n).symm)` and prove the remaining obligations.
-/
theorem cechComplex_sliceFst_singleton_acyclic_of_trunc₂ : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  intro ν κ _ _ _ _ R _ A hA hT j
  have hcompl := isCompl_range_inlEmb_inrEmb ν κ
  have hQ : Set.OrdConnected {s : Finset ν | s.Nonempty} := ordConnected_nonempty
  have hU₂ : IsUpperSet {t : Finset κ | 2 ≤ t.card} :=
    fun _ _ hst ht => le_trans ht (Finset.card_le_card hst)
  have hT₂ := hU₂.ordConnected
  have hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1} := by
    refine ⟨fun a ha b hb c hc => ?_⟩
    have h1 := Finset.card_le_card hc.1
    have h2 := Finset.card_le_card hc.2
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    omega
  have hS := GlobalTheory.cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂)
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ ordConnected_nonempty)
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₁)
    (fun u => by
      have hc : (part (inrEmb ν κ) u).Nonempty ↔
          2 ≤ (part (inrEmb ν κ) u).card ∨ (part (inrEmb ν κ) u).card = 1 := by
        rw [← Finset.card_pos]
        omega
      simp only [mem_partsIn, Set.mem_setOf_eq]
      tauto)
    (fun u hu hu' => by
      have h1 : 2 ≤ (part (inrEmb ν κ) u).card := hu.2
      have h2 : (part (inrEmb ν κ) u).card = 1 := hu'.2
      omega)
    (fun _ _ hst hs ht => ⟨ht.1, hU₂ (monotone_part _ hst) hs.2⟩))
  have h₁ : (GlobalTheory.cubeComplex (supp A _ (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂))).Acyclic := by
    rw [supp_partsIn_comm hQ hT₂ A]
    refine GlobalTheory.cubeComplex_supp_partsIn_acyclic hcompl.symm hT₂ hQ A fun t ht => ?_
    refine (GlobalTheory.cubeComplex_trunc₁_acyclic_iff _).2 ?_
    rw [← sliceFst_eq_slice]
    exact hA t ht
  have hzero : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ)
      {s : Finset ν | s.Nonempty} {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology (n + 2)) := fun n => by
    refine isZero_homology_supp_singleton A hQ hT₁ j (n + 2) ?_
    have := GlobalTheory.isIso_homologyMap_g_of_acyclic hS h₁ (n + 2)
    exact (hT n).of_iso (@asIso _ _ _ _ _ this).symm
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine ((hzero n).of_iso
    (GlobalTheory.suppSingletonHomologyIso hcompl hQ j A (n + 1)).symm).of_iso
    (GlobalTheory.cechHomologyMapIso (eqToIso (sliceFst_eq_slice A {j})) n ≪≫
      (GlobalTheory.truncHomologyIso _ n).symm)

end GlobalTheory.CompanionTheory.PointSurjectivity
