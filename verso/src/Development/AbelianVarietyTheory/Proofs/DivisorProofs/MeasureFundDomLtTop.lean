import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `hd`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hd`. Establish `h1` using `h.2.2 (star v) (by simpa using hv)`. Rewrite `h1` using `[star_star, hMv, dotProduct_zero]`. Simplify using `at h1`.
-/
theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, hσ]`. Conclude with `(h.herm j i).symm`. Establish `hJ : X.J.det ≠ 0`. Take `⟨w⟩ : Nonempty (NumberField.InfinitePlace F)` from `inferInstance`.

Introduce `hz`. Apply `det_ne_zero_of_isCartan (h.cartan w)` to reduce the goal to its premises. Rewrite using `[show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]`. Rewrite using `[show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 hJ`.
-/
theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

/- English proof (translation)
Use `haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective`. Use `haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j) fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)`. Use `haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype`. Conclude with `Function.Injective.countable (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ : Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))))) fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))`.
-/
theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

/- English proof (translation)
Establish `hσ` using `GlobalTheory.SiegelSet.sigma_sigma hcm`. Establish `heq : UG (cA σ) (incM F J) = HR (AF F) σ (J.map σ)`. Establish `h` using `GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ one_ne_zero`. Rewrite `h` using `[one_smul]`. Conclude with `h`.

Set `e : UA σ J ≃* GAd σ (J.map σ)` to `MulEquiv.subgroupCongr heq`. Establish `he : Continuous e` using `continuous_subtype_val.subtype_mk _`. Establish `he' : Continuous e.symm` using `continuous_subtype_val.subtype_mk _`. Take `⟨S, hSc, hcov, -, hfin, -⟩` from `GlobalTheory.SiegelSet.exists_cover hP hcm hJ`. Use `haveI : BorelSpace (UA σ J) := ⟨rfl⟩`.

Use `haveI : ContinuousMul (UA σ J) := ⟨by`. Establish `h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2)`. Use function extensionality and compare the values at `fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]`. Rewrite using `[h3]`. Conclude with `he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩`.

Establish `hH : (μ.map e).IsHaarMeasure` using `MulEquiv.isHaarMeasure_map μ e he he'`. Establish `h1 : μ (e ⁻¹' S) < ⊤`. Establish `h2` using `hfin _ hH`. Rewrite `h2` using `[Measure.map_apply he.measurable hSc.measurableSet]`. Then use the resulting hypothesis. Use `haveI := countable_ratU σ J`.

Use `haveI : MeasurableMul (UA σ J) := ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩`. Use `haveI : MeasurableConstSMul (ratU σ J) (UA σ J) := ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩`. Use `haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩`. Establish `hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D`. Introduce `x hx`.

Take `⟨γ, hγ, s, hs, hxs⟩` from `hcov (e x)`. Take `⟨u, -, hu⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)`. Establish `hr : e.symm γ ∈ ratU σ J` using `Subgroup.mem_subgroupOf.2 ⟨u, hu⟩`. Use `Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e.symm γ * e.symm s = x`.

Rewrite using `[← map_mul, ← hxs, MulEquiv.symm_apply_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_fundDom_lt_top (hP : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ (J.map σ)) {μ : Measure (UA σ J)} [μ.IsHaarMeasure]
    {D : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) : μ D < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : UA σ J ≃* GAd σ (J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨S, hSc, hcov, -, hfin, -⟩ := GlobalTheory.SiegelSet.exists_cover hP hcm hJ
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have h1 : μ (e ⁻¹' S) < ⊤ := by
    have h2 := hfin _ hH
    rwa [Measure.map_apply he.measurable hSc.measurableSet] at h2
  haveI := countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, s, hs, hxs⟩ := hcov (e x)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩
    change e.symm γ * e.symm s = x
    rw [← map_mul, ← hxs, MulEquiv.symm_apply_apply]
  calc μ D ≤ μ (⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D) := measure_mono hcov'
    _ ≤ ∑' γ : ratU σ J, μ (γ • (e ⁻¹' S) ∩ D) := measure_iUnion_le _
    _ = μ (e ⁻¹' S) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hP hT`. Use `haveI := hT.geo.hM'.haar`. Conclude with `measure_fundDom_lt_top hP hT.base.cm (isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hT.base.cm) hT.geo.hV') hT.geo.hM'.dom`.
-/
theorem measure_dom_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), GlobalTheory.Published.SiegelSetUnitary → IsTriple B G X om om' → G.M'.μ G.M'.dom < ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hP hT
  haveI := hT.geo.hM'.haar
  exact measure_fundDom_lt_top hP hT.base.cm
    (isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hT.base.cm) hT.geo.hV') hT.geo.hM'.dom

end GlobalTheory.UnitaryVol
