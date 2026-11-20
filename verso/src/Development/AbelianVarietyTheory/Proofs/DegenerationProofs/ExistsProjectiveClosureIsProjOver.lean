import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points GlobalTheory.ProjSpace GlobalTheory.TuplePoint

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω}

/- English proof (translation)
Establish `hle : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤ Subfield.closure ((Algebra.adjoin o (Set.range fun j => t j / t i)).toSubring : Set Ω)`. Use `Subfield.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨k, j, rfl⟩)`. Conclude with `Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)`. Rewrite using `[← div_div_div_cancel_right₀ hi]`.

Conclude with `div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩)) (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))`. Establish `hx` using `hle (h ▸ Subfield.mem_top x)`. Rewrite `hx` using `[Subfield.mem_closure_iff, Subring.closure_eq]`. Then use the resulting hypothesis.
-/
theorem exists_div_of_closure_ratios_eq_top
    (h : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤) {i : Fin (n + 1)}
    (hi : t i ≠ 0) (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i),
      ∃ b ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a / b = x := by
  have hle : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure ((Algebra.adjoin o (Set.range fun j => t j / t i)).toSubring : Set Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
    · rw [← div_div_div_cancel_right₀ hi]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hx := hle (h ▸ Subfield.mem_top x)
  rwa [Subfield.mem_closure_iff, Subring.closure_eq] at hx

section Closed

variable {ht : t ≠ 0} {Z : Scheme.{0}} {ξ : Sp Ω ⟶ Z} {π : Z ⟶ PSpace o n} (hπ : ξ ≫ π = point o t ht)

include hπ

/- English proof (translation)
Establish `h` using `(le_point_preimage_iff (o := o) (ht := ht) i).2 hi`. Establish `key : ∀ g, valF ξ _ ((π.app (chart o n i)).hom g) = (valMap (point o t ht) _ h).hom g` using `fun g => by`. Rewrite using `[← valR_eq, ← hπ]`. Conclude with `(valR_comp ξ π _ g).symm`. Rewrite using `[← SetLike.mem_coe, ← range_valMap_point h]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, rfl⟩`. Take `⟨g, rfl⟩` from `π.app_surjective _ (isAffineOpen_chart o n i) f`. Conclude with `⟨g, (key g).symm⟩`. Introduce and unpack `⟨g, rfl⟩`.

Conclude with `⟨_, key g⟩`.
-/
theorem exists_valF_preimage_chart_iff [IsClosedImmersion π] {i : Fin (n + 1)} (hi : t i ≠ 0) (x : Ω) :
    (∃ f : Γ(Z, π ⁻¹ᵁ chart o n i), valF ξ _ f = x) ↔ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i) := by
  have h := (le_point_preimage_iff (o := o) (ht := ht) i).2 hi
  have key : ∀ g, valF ξ _ ((π.app (chart o n i)).hom g) = (valMap (point o t ht) _ h).hom g := fun g => by
    rw [← valR_eq, ← hπ]
    exact (valR_comp ξ π _ g).symm
  rw [← SetLike.mem_coe, ← range_valMap_point h]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := π.app_surjective _ (isAffineOpen_chart o n i) f
    exact ⟨g, (key g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, key g⟩

end Closed

/- English proof (translation)
Establish `hle : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b` using `(le_preimage_basicOpen_iff _ hU b).2 (isUnit_iff_ne_zero.2 hb)`. Establish `hu : IsUnit (resG _ (Z.basicOpen_le b) b)` using `RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace b`. Take `⟨c, hc⟩` from `hu.exists_right_inv`. Establish `h1 : valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) b * c) = 1` using `(congrArg _ hc).trans (valR_one _ _ hle)`. Rewrite `h1` using `[valR_mul _ _ hle]`.

Establish `h2 : ∀ s, valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) s) = valF ξ U s` using `fun s => valR_res _ _ hle _`. Use `⟨hle, resG _ (Z.basicOpen_le b) a * c, (valR_mul _ _ hle _ _).trans ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[h2 b]`. Rewrite using `[h2 a, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]`.
-/
theorem exists_valF_eq_div {Z : Scheme.{0}} (ξ : Sp Ω ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (a b : Γ(Z, U))
    (hb : valF ξ U b ≠ 0) : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b ∧
      ∃ f : Γ(Z, Z.basicOpen b), valF ξ _ f = valF ξ U a / valF ξ U b := by
  have hle : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b := (le_preimage_basicOpen_iff _ hU b).2 (isUnit_iff_ne_zero.2 hb)
  have hu : IsUnit (resG _ (Z.basicOpen_le b) b) :=
    RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace b
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have h1 : valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) b * c) = 1 :=
    (congrArg _ hc).trans (valR_one _ _ hle)
  rw [valR_mul _ _ hle] at h1
  have h2 : ∀ s, valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) s) = valF ξ U s :=
    fun s => valR_res _ _ hle _
  refine ⟨hle, resG _ (Z.basicOpen_le b) a * c, (valR_mul _ _ hle _ _).trans ?_⟩
  rw [h2 b] at h1
  rw [h2 a, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]

/- English proof (translation)
Establish `h1 : ∀ (k : Fin (n + 1)) (z : M.Z), z ∈ π ⁻¹ᵁ chart o n k → M.Div t k z` using `fun k z hz =>`. Establish `hW` using `M.top_le_preimage_pt ⟨z, hz⟩`. Use the proof step `⟨ne_zero_of_le hπ hW le_rfl, fun j => ⟨_, pullRatio π _ k le_rfl j, hz, valR_pullRatio hπ hW le_rfl j⟩⟩`. Establish `h2 : ∀ (i : Fin (n + 1)) (z : M.Z), M.Div t i z → z ∈ π ⁻¹ᵁ chart o n i` using `fun i z hz => by`. Take `⟨k, hk⟩` from `exists_mem_chart o n (π z)`.

Establish `hk' : z ∈ π ⁻¹ᵁ chart o n k` using `hk`. Establish `hu` using `((h1 k z hk').div_iff_isUnit i).1 hz`. Establish `e : (⟨t i / t k, (h1 k z hk').2 i⟩ : M.O z) = ⟨_, RatModel.valF_mem_O hk' (pullRatio π _ k le_rfl i)⟩` using `Subtype.ext (valR_pullRatio hπ (M.top_le_preimage_pt ⟨z, hk'⟩) le_rfl i).symm`. Rewrite `hu` using `[e, RatModel.isUnit_valF_iff hk', basicOpen_pullRatio]`. Conclude with `hu.2`.

Use `⟨fun z => (exists_mem_chart o n (π z)).imp fun k hk => h1 k z hk, fun i hi => ?_⟩` and prove the remaining obligations. Use `⟨π ⁻¹ᵁ chart o n i, (isAffineOpen_chart o n i).preimage π, Set.ext fun z => ⟨h1 i z, h2 i z⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[RatModel.mem_ringOn_iff_exists ⟨_, h2 i _ (RatModel.div_genericPoint hi)⟩, exists_valF_preimage_chart_iff hπ hi]`.
-/
theorem RatModel.isCl_of_isClosedImmersion (M : RatModel o Ω) {ht : t ≠ 0} (π : M.Z ⟶ PSpace o n)
    [IsClosedImmersion π] (hπ : M.pt ≫ π = point o t ht) : M.IsCl t := by
  have h1 : ∀ (k : Fin (n + 1)) (z : M.Z), z ∈ π ⁻¹ᵁ chart o n k → M.Div t k z := fun k z hz =>
    have hW := M.top_le_preimage_pt ⟨z, hz⟩
    ⟨ne_zero_of_le hπ hW le_rfl, fun j => ⟨_, pullRatio π _ k le_rfl j, hz, valR_pullRatio hπ hW le_rfl j⟩⟩
  have h2 : ∀ (i : Fin (n + 1)) (z : M.Z), M.Div t i z → z ∈ π ⁻¹ᵁ chart o n i := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_mem_chart o n (π z)
    have hk' : z ∈ π ⁻¹ᵁ chart o n k := hk
    have hu := ((h1 k z hk').div_iff_isUnit i).1 hz
    have e : (⟨t i / t k, (h1 k z hk').2 i⟩ : M.O z) =
        ⟨_, RatModel.valF_mem_O hk' (pullRatio π _ k le_rfl i)⟩ :=
      Subtype.ext (valR_pullRatio hπ (M.top_le_preimage_pt ⟨z, hk'⟩) le_rfl i).symm
    rw [e, RatModel.isUnit_valF_iff hk', basicOpen_pullRatio] at hu
    exact hu.2
  refine ⟨fun z => (exists_mem_chart o n (π z)).imp fun k hk => h1 k z hk, fun i hi => ?_⟩
  refine ⟨π ⁻¹ᵁ chart o n i, (isAffineOpen_chart o n i).preimage π,
    Set.ext fun z => ⟨h1 i z, h2 i z⟩, ?_⟩
  ext x
  rw [RatModel.mem_ringOn_iff_exists ⟨_, h2 i _ (RatModel.div_genericPoint hi)⟩,
    exists_valF_preimage_chart_iff hπ hi]

/- English proof (translation)
Introduce `o Ω _ _ _ _ n t ⟨i, hi⟩ h`. Establish `ht : t ≠ 0` using `Function.ne_iff.2 ⟨i, hi⟩`. Set `φ` to `point o t ht`. Establish `hsep : IsProper (PSpace.str o n)` using `projProper o _ _ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩`. Establish `hqc : QuasiCompact φ`.

Establish `: QuasiCompact (φ ≫ PSpace.str o n)`. Rewrite using `[point_str]`. Use `infer_instance`. Conclude with `QuasiCompact.of_comp φ (PSpace.str o n)`. Establish `hπ : φ.toImage ≫ φ.imageι = point o t ht` using `φ.toImage_imageι`.

Establish `hW` using `le_preimage_chart hπ hi`. Set `M : RatModel o Ω` to `{ Z := φ.image s := φ.imageι ≫ PSpace.str o n sep := inferInstance lft := inferInstance qc := inferInstance pt := φ.toImage pt_s := by rw [← Category.assoc, hπ, point_str] gen := by`. Establish `e : Set.range φ.toImage = {φ.toImage (IsLocalRing.closedPoint Ω)}` using `Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Subsingleton.elim w (IsLocalRing.closedPoint Ω)]⟩`.

Establish `hd : IsGenericPoint (φ.toImage (IsLocalRing.closedPoint Ω)) Set.univ`. Rewrite using `[isGenericPoint_def, ← e]`. Conclude with `φ.toImage.denseRange.closure_range`. Rewrite using `[e, hd.eq (genericPoint_spec _)]`. Use `onto := fun x => by`.

Take `⟨_, ha, _, hb, rfl⟩` from `exists_div_of_closure_ratios_eq_top h hi x`. Take `⟨a, rfl⟩` from `(exists_valF_preimage_chart_iff hπ hi _).2 ha`. Take `⟨b, rfl⟩` from `(exists_valF_preimage_chart_iff hπ hi _).2 hb`. Distinguish the cases in `h0 : valF φ.toImage _ b = 0`. Conclude with `⟨_, b, ⟨_, hW (x := IsLocalRing.closedPoint Ω) trivial⟩, by rw [h0, div_zero]⟩`.

Take `⟨hle, f, hf⟩` from `exists_valF_eq_div _ hW a b h0`. Conclude with `⟨_, f, ⟨_, hle (x := IsLocalRing.closedPoint Ω) trivial⟩, hf⟩ }`. Conclude with `⟨M, M.isCl_of_isClosedImmersion φ.imageι hπ, n, φ.imageι, inferInstance, rfl⟩`.
-/
theorem exists_isCl_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ n t ⟨i, hi⟩ h
  have ht : t ≠ 0 := Function.ne_iff.2 ⟨i, hi⟩
  let φ := point o t ht
  have hsep : IsProper (PSpace.str o n) :=
    projProper o _ _ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hqc : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ PSpace.str o n) := by
      rw [point_str]
      infer_instance
    exact QuasiCompact.of_comp φ (PSpace.str o n)
  have hπ : φ.toImage ≫ φ.imageι = point o t ht := φ.toImage_imageι
  have hW := le_preimage_chart hπ hi
  let M : RatModel o Ω :=
    { Z := φ.image
      s := φ.imageι ≫ PSpace.str o n
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := φ.toImage
      pt_s := by rw [← Category.assoc, hπ, point_str]
      gen := by
        have e : Set.range φ.toImage = {φ.toImage (IsLocalRing.closedPoint Ω)} :=
          Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
            rintro _ ⟨w, rfl⟩
            rw [Subsingleton.elim w (IsLocalRing.closedPoint Ω)]⟩
        have hd : IsGenericPoint (φ.toImage (IsLocalRing.closedPoint Ω)) Set.univ := by
          rw [isGenericPoint_def, ← e]
          exact φ.toImage.denseRange.closure_range
        rw [e, hd.eq (genericPoint_spec _)]
      onto := fun x => by
        obtain ⟨_, ha, _, hb, rfl⟩ := exists_div_of_closure_ratios_eq_top h hi x
        obtain ⟨a, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 ha
        obtain ⟨b, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 hb
        by_cases h0 : valF φ.toImage _ b = 0
        · exact ⟨_, b, ⟨_, hW (x := IsLocalRing.closedPoint Ω) trivial⟩, by rw [h0, div_zero]⟩
        · obtain ⟨hle, f, hf⟩ := exists_valF_eq_div _ hW a b h0
          exact ⟨_, f, ⟨_, hle (x := IsLocalRing.closedPoint Ω) trivial⟩, hf⟩ }
  exact ⟨M, M.isCl_of_isClosedImmersion φ.imageι hπ, n, φ.imageι, inferInstance, rfl⟩

end GlobalTheory.ZH
end
