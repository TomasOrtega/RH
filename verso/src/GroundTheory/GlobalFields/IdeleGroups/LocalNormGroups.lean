import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.UnramifiedNorms
import GroundTheory.GlobalFields.CompletionAtPlace.Integers

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Use `ext`. Rewrite using `[coe_finiteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by`. Rewrite using `[Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,`. Use the proof step `LocalField.coe_normUnits]`.
-/
theorem finiteLocalNorm_mulSingle (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (PlacesOver L v)]
    (w : PlacesOver L v) (z : (w.1.adicCompletion L)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w z) =
      LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) z := by
  ext
  rw [coe_finiteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    LocalField.coe_normUnits]

omit [NumberField K] in
open scoped Classical in

/- English proof (translation)
Use `ext`. Rewrite using `[coe_infiniteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by`. Rewrite using `[Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,`. Use the proof step `LocalField.coe_normUnits]`.
-/
theorem infiniteLocalNorm_mulSingle (v : InfinitePlace K) (w : v.placesOver L)
    (z : ((w : InfinitePlace L).Completion)ˣ) :
    infiniteLocalNorm L v (Pi.mulSingle w z) =
      LocalField.normUnits v.Completion (w : InfinitePlace L).Completion z := by
  ext
  rw [coe_infiniteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    LocalField.coe_normUnits]

variable (L) in

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v` from `InfinitePlace.comap_surjective v`. Substitute `hw` using the available equality. Conclude with `⟨⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩⟩`.
-/
theorem nonempty_infinitePlacesOver (v : InfinitePlace K) : Nonempty (v.placesOver L) := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v :=
    InfinitePlace.comap_surjective v
  subst hw
  exact ⟨⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩⟩

/- English proof (translation)
Take `⟨w⟩` from `nonempty_placesOver L v`. Use `Subgroup.isOpen_mono ?_ (LocalField.isOpen_range_normUnits (v.adicCompletion K) (w.1.adicCompletion L))` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨Pi.mulSingle w z, finiteLocalNorm_mulSingle v w z⟩`.
-/
theorem isOpen_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((finiteLocalNorm L v).range : Set (v.adicCompletion K)ˣ) := by
  classical
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine Subgroup.isOpen_mono ?_
    (LocalField.isOpen_range_normUnits (v.adicCompletion K) (w.1.adicCompletion L))
  rintro _ ⟨z, rfl⟩
  exact ⟨Pi.mulSingle w z, finiteLocalNorm_mulSingle v w z⟩

/- English proof (translation)
Establish `: CharZero v.Completion` using `charZero_of_injective_algebraMap (algebraMap K v.Completion).injective`. Establish `h` using `(hasStrictDerivAt_pow d (1 : v.Completion)).map_nhds_eq (by simpa using hd)`. Rewrite `h` using `[one_pow]`. Rewrite using `[← h, Filter.mem_map]`. Use `filter_upwards [compl_singleton_mem_nhds (one_ne_zero' v.Completion)] with a ha`.

Conclude with `⟨a, ha, rfl⟩`.
-/
theorem pow_mem_nhds_one (v : InfinitePlace K) {d : ℕ} (hd : d ≠ 0) :
    {u : v.Completion | ∃ a : v.Completion, a ≠ 0 ∧ a ^ d = u} ∈ 𝓝 (1 : v.Completion) := by
  have : CharZero v.Completion :=
    charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
  have h := (hasStrictDerivAt_pow d (1 : v.Completion)).map_nhds_eq (by simpa using hd)
  rw [one_pow] at h
  rw [← h, Filter.mem_map]
  filter_upwards [compl_singleton_mem_nhds (one_ne_zero' v.Completion)] with a ha
  exact ⟨a, ha, rfl⟩

/- English proof (translation)
Take `⟨w⟩` from `nonempty_infinitePlacesOver L v`. Establish `hd : Module.finrank v.Completion (w : InfinitePlace L).Completion ≠ 0` using `Module.finrank_pos.ne'`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Establish `h` using `(Units.continuous_val (M := v.Completion)).tendsto 1`. Rewrite `h` using `[Units.val_one]`.

Use `Filter.mem_of_superset (h (pow_mem_nhds_one v hd)) fun u hu ↦ ?_` and prove the remaining obligations. Take `⟨a, ha, hau⟩` from `hu`. Use `⟨Pi.mulSingle w (Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion : v.Completion →* (w : InfinitePlace L).Completion) (Units.mk0 a ha)), ?_⟩` and prove the remaining obligations. Rewrite using `[infiniteLocalNorm_mulSingle]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[LocalField.coe_normUnits, Units.coe_map, Units.val_mk0]`. Conclude with `(Algebra.norm_algebraMap a).trans hau`.
-/
theorem isOpen_range_infiniteLocalNorm (v : InfinitePlace K) :
    IsOpen ((infiniteLocalNorm L v).range : Set (v.Completion)ˣ) := by
  classical
  obtain ⟨w⟩ := nonempty_infinitePlacesOver L v
  have hd : Module.finrank v.Completion (w : InfinitePlace L).Completion ≠ 0 :=
    Module.finrank_pos.ne'
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := (Units.continuous_val (M := v.Completion)).tendsto 1
  rw [Units.val_one] at h
  refine Filter.mem_of_superset (h (pow_mem_nhds_one v hd)) fun u hu ↦ ?_
  obtain ⟨a, ha, hau⟩ := hu
  refine ⟨Pi.mulSingle w (Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion :
    v.Completion →* (w : InfinitePlace L).Completion) (Units.mk0 a ha)), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  rw [LocalField.coe_normUnits, Units.coe_map, Units.val_mk0]
  exact (Algebra.norm_algebraMap a).trans hau

/- English proof (translation)
Rewrite using `[coe_finiteLocalNorm]`. Use `prod_mem fun w _ ↦ ?_` and prove the remaining obligations. Establish `h` using `(Submonoid.mem_units_iff _ _).1 (mem_integerUnitsOver.1 hy w)`. Rewrite using `[← mem_valuationInteger_iff]`. Conclude with `LocalField.norm_mem_integer ((mem_valuationInteger_iff w.1 _).2 h.1)`.
-/
theorem finiteLocalNorm_mem_integers {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} (hy : y ∈ integerUnitsOver L v) :
    (finiteLocalNorm L v y : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [coe_finiteLocalNorm]
  refine prod_mem fun w _ ↦ ?_
  have h := (Submonoid.mem_units_iff _ _).1 (mem_integerUnitsOver.1 hy w)
  rw [← mem_valuationInteger_iff]
  exact LocalField.norm_mem_integer ((mem_valuationInteger_iff w.1 _).2 h.1)

/- English proof (translation)
Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `(Submonoid.mem_units_iff _ _).2 ⟨finiteLocalNorm_mem_integers hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `finiteLocalNorm_mem_integers (inv_mem hy)`.
-/
theorem map_integerUnitsOver_le (v : HeightOneSpectrum (𝓞 K)) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) ≤
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rintro _ ⟨y, hy, rfl⟩
  refine (Submonoid.mem_units_iff _ _).2 ⟨finiteLocalNorm_mem_integers hy, ?_⟩
  rw [← map_inv]
  exact finiteLocalNorm_mem_integers (inv_mem hy)

/- English proof (translation)
Rewrite using `[finiteLocalNorm_mulSingle]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[LocalField.coe_normUnits, Units.coe_map, Units.val_pow_eq_pow_val]`. Conclude with `Algebra.norm_algebraMap (S := w.1.adicCompletion L) (a : v.adicCompletion K)`.
-/
theorem finiteLocalNorm_mulSingle_algebraMap (v : HeightOneSpectrum (𝓞 K))
    [DecidableEq (PlacesOver L v)] (w : PlacesOver L v) (a : (v.adicCompletion K)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w (Units.map (algebraMap (v.adicCompletion K)
      (w.1.adicCompletion L) : v.adicCompletion K →* w.1.adicCompletion L) a)) =
        a ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [finiteLocalNorm_mulSingle]
  apply Units.ext
  rw [LocalField.coe_normUnits, Units.coe_map, Units.val_pow_eq_pow_val]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (a : v.adicCompletion K)

/- English proof (translation)
Establish `hw` using `(splitsCompletely_iff_forall_finrank v).1 ((splitsCompletely_iff_isFiniteSplit v).2 h)`. Take `⟨w⟩` from `nonempty_placesOver L v`. Use `eq_top_iff.2 fun a _ ↦ ⟨_, finiteLocalNorm_mulSingle_algebraMap v w a |>.trans ?_⟩` and prove the remaining obligations. Rewrite using `[hw w, pow_one]`.
-/
theorem range_finiteLocalNorm_eq_top_of_isFiniteSplit (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)) :
    (finiteLocalNorm L v).range = ⊤ := by
  classical
  have hw := (splitsCompletely_iff_forall_finrank v).1 ((splitsCompletely_iff_isFiniteSplit v).2 h)
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine eq_top_iff.2 fun a _ ↦ ⟨_, finiteLocalNorm_mulSingle_algebraMap v w a |>.trans ?_⟩
  rw [hw w, pow_one]

/- English proof (translation)
Establish `: LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L)` using `⟨(ramificationIdx_integer v w).trans he⟩`. Rewrite `hu` using `[Submonoid.mem_units_iff]`. Set `u' : 𝒪[v.adicCompletion K]ˣ` to `⟨⟨u, (mem_valuationInteger_iff v _).2 hu.1⟩, ⟨_, (mem_valuationInteger_iff v _).2 hu.2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩`. Take `⟨g, hg⟩` from `LocalField.normIntegerUnits_surjective (K := v.adicCompletion K) (L := w.adicCompletion L) u'`. Use `⟨LocalField.unitsIncl _ g, (Submonoid.mem_units_iff _ _).2 ⟨(mem_valuationInteger_iff w _).1 (g : 𝒪[w.adicCompletion L]).2, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv, LocalField.coe_unitsIncl]`. Conclude with `(mem_valuationInteger_iff w _).1 ((g⁻¹ : 𝒪[w.adicCompletion L]ˣ) : 𝒪[w.adicCompletion L]).2`. Rewrite using `[LocalField.coe_unitsIncl, ← LocalField.coe_normIntegerUnits, hg]`.
-/
theorem exists_norm_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ∃ y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units,
      Algebra.norm (v.adicCompletion K) (y : w.adicCompletion L) = u := by
  have : LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
    ⟨(ramificationIdx_integer v w).trans he⟩
  rw [Submonoid.mem_units_iff] at hu
  let u' : 𝒪[v.adicCompletion K]ˣ :=
    ⟨⟨u, (mem_valuationInteger_iff v _).2 hu.1⟩, ⟨_, (mem_valuationInteger_iff v _).2 hu.2⟩,
      Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  obtain ⟨g, hg⟩ := LocalField.normIntegerUnits_surjective
    (K := v.adicCompletion K) (L := w.adicCompletion L) u'
  refine ⟨LocalField.unitsIncl _ g, (Submonoid.mem_units_iff _ _).2
    ⟨(mem_valuationInteger_iff w _).1 (g : 𝒪[w.adicCompletion L]).2, ?_⟩, ?_⟩
  · rw [← map_inv, LocalField.coe_unitsIncl]
    exact (mem_valuationInteger_iff w _).1 ((g⁻¹ : 𝒪[w.adicCompletion L]ˣ) :
      𝒪[w.adicCompletion L]).2
  · rw [LocalField.coe_unitsIncl, ← LocalField.coe_normIntegerUnits, hg]

end IdeleNorm

end

end GroundTheory.Global
