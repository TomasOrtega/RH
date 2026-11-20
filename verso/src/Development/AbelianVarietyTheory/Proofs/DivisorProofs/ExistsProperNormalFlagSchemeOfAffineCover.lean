import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCellsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

/- English proof (translation)
Introduce `K _ X s T _ m M B _ V α c D hP hN hC hV`. Take `⟨P, p0, p, h, hPlk⟩` from `GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base K K (RingHom.id K) X s T m M B V α c D hP hC`. Take `⟨F, f, i, hf, hi, hif, hcov⟩` from `GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct K K (RingHom.id K) X s T m M B V α c D P p0 p h hP hN hC hPlk`. Establish `hXn : IsLocallyNoetherian X`. Take `⟨N, ι, _, rfl⟩` from `hP`.

Conclude with `LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str K N)`. Take `⟨hFc, hFn, hFnoe⟩` from `GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov`. Establish `hPp : IsProper (p0 ≫ s)`. Take `⟨N, ι, hι, e⟩` from `hPlk.proj`. Use `isProper_str K N` as an intermediate fact.

Rewrite using `[← e]`. Use `infer_instance`. Establish `hsp : IsProper s`. Take `⟨N, ι, hι, rfl⟩` from `hP`. Use `isProper_str K N` as an intermediate fact.

Use `infer_instance`. Establish `hp0 : IsProper p0` using `IsProper.of_comp p0 s`. Establish `: LocallyOfFiniteType (f ≫ p0 ≫ s)` using `inferInstance`. Establish `: IsLocallyNoetherian F` using `LocallyOfFiniteType.isLocallyNoetherian (f ≫ p0 ≫ s)`. Establish `: IsNoetherian F` using `{}`.

Establish `hqc : QuasiCompact f` using `inferInstance`. Establish `hsep : IsSeparated (f.imageι ≫ p0)` using `inferInstance`. Establish `hpre` using `GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells K K (RingHom.id K) X s T m M B V α c D P p0 p h hC hPlk F f.image f i f.toImage f.imageι hf hi hif hcov inferInstance f.toImage_imageι f.toImage.denseRange hFnoe hsep`. Establish `huniv : (⋃ b, ((V b).1 : Set X)) = Set.univ`. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations.

Take `⟨b, hb⟩` from `hV x`. Conclude with `Set.mem_iUnion.2 ⟨b, hb⟩`. Establish `hsurj : Function.Surjective f.toImage`. Rewrite using `[← Set.range_eq_univ, ← hpre, huniv, Set.preimage_univ]`. Establish `: Surjective f.toImage` using `⟨hsurj⟩`.

Establish `: IsIso f.toImage` using `IsOpenImmersion.isIso f.toImage`. Establish `hfc : IsClosedImmersion f`. Rewrite using `[← f.toImage_imageι]`. Use `infer_instance`. Use `⟨F, f ≫ p0, fun en => f ≫ p en, i, inferInstance, hFn, ⟨?_, ?_⟩, hi, hcov, ?_⟩` and prove the remaining obligations.

Introduce `b w`. Rewrite using `[← Category.assoc, hif, hPlk.base]`. Introduce `b w en`. Take `⟨hu, e⟩` from `hPlk.plk b w en`. Conclude with `⟨hu, by rw [← Category.assoc, hif, e]⟩`.

Introduce `W a a' e1 e2`. Establish `key : a ≫ f = a' ≫ f`. Use `hPlk.ext _ _ _ ?_ fun en => ?_` and prove the remaining obligations. Simplify `e1` using `only [Category.assoc]`. Simplify `e2 en` using `only [Category.assoc]`.

Conclude with `(cancel_mono f).1 key`.
-/
theorem exists_properFlag : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  intro K _ X s T _ m M B _ V α c D hP hN hC hV
  obtain ⟨P, p0, p, h, hPlk⟩ := GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base K K (RingHom.id K) X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct K K (RingHom.id K) X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str K N)
  obtain ⟨hFc, hFn, hFnoe⟩ := GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov
  have hPp : IsProper (p0 ≫ s) := by
    obtain ⟨N, ι, hι, e⟩ := hPlk.proj
    have := isProper_str K N
    rw [← e]
    infer_instance
  have hsp : IsProper s := by
    obtain ⟨N, ι, hι, rfl⟩ := hP
    have := isProper_str K N
    infer_instance
  have hp0 : IsProper p0 := IsProper.of_comp p0 s
  have : LocallyOfFiniteType (f ≫ p0 ≫ s) := inferInstance
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p0 ≫ s)
  have : IsNoetherian F := {}
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated (f.imageι ≫ p0) := inferInstance
  have hpre := GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells K K (RingHom.id K) X s T m M B V α c D P p0 p h hC hPlk F f.image f i f.toImage f.imageι
    hf hi hif hcov inferInstance f.toImage_imageι f.toImage.denseRange hFnoe hsep
  have huniv : (⋃ b, ((V b).1 : Set X)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨b, hb⟩ := hV x
    exact Set.mem_iUnion.2 ⟨b, hb⟩
  have hsurj : Function.Surjective f.toImage := by
    rw [← Set.range_eq_univ, ← hpre, huniv, Set.preimage_univ]
  have : Surjective f.toImage := ⟨hsurj⟩
  have : IsIso f.toImage := IsOpenImmersion.isIso f.toImage
  have hfc : IsClosedImmersion f := by
    rw [← f.toImage_imageι]
    infer_instance
  refine ⟨F, f ≫ p0, fun en => f ≫ p en, i, inferInstance, hFn, ⟨?_, ?_⟩, hi, hcov, ?_⟩
  · intro b w
    rw [← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [← Category.assoc, hif, e]⟩
  · intro W a a' e1 e2
    have key : a ≫ f = a' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc] using e2 en
    exact (cancel_mono f).1 key

end GlobalTheory.FlagMod.FieldFlag
