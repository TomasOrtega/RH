import Mathlib
import GroundTheory.FunctionField.PlaceBasic

namespace GroundTheory.FunctionField

namespace Place

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

def LiesOver (w : Place k K') (v : Place k K) : Prop :=
  w.ring.comap (algebraMap K K') = v.ring

omit [IsScalarTower k K K'] in
/- English proof (translation)
Rewrite using `[← ValuationSubring.mem_comap, h]`.
-/
theorem LiesOver.mem_iff {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K} :
    algebraMap K K' x ∈ w.ring ↔ x ∈ v.ring := by
  rw [← ValuationSubring.mem_comap, h]

omit [IsScalarTower k K K'] in
/- English proof (translation)
The claim follows from `h.mem_iff.2 hx`.
-/
theorem LiesOver.algebraMap_mem {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K}
    (hx : x ∈ v.ring) : algebraMap K K' x ∈ w.ring :=
  h.mem_iff.2 hx

def comap [Algebra.IsAlgebraic K K'] (w : Place k K') : Place k K where
  ring := w.ring.comap (algebraMap K K')
  ne_top := by
    intro htop
    apply w.ne_top
    have hK : ∀ a : K, algebraMap K K' a ∈ w.ring := fun a =>
      ValuationSubring.mem_comap.1 (htop ▸ ValuationSubring.mem_top a)
    let : Algebra K w.ring := (RingHom.codRestrict (algebraMap K K') w.ring hK).toAlgebra
    have : IsScalarTower K w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine eq_top_iff.2 fun z _ => ?_
    have hz : IsIntegral w.ring z := (Algebra.IsIntegral.isIntegral (R := K) z).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz
    rw [← hy]
    exact y.2
  algebraMap_mem c := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liesOver_comap [Algebra.IsAlgebraic K K'] (w : Place k K') : w.LiesOver (w.comap (K := K)) :=
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Place.ext h, fun h => congrArg Place.ring h⟩`.
-/
theorem liesOver_iff_comap_eq [Algebra.IsAlgebraic K K'] {w : Place k K'} {v : Place k K} :
    w.LiesOver v ↔ w.comap = v :=
  ⟨fun h => Place.ext h, fun h => congrArg Place.ring h⟩

/- English proof (translation)
Use `Place.eq_of_le (v := v) (w := w.comap) fun x hx => ValuationSubring.mem_comap.2 (h x hx)` as an intermediate fact. Conclude with `liesOver_iff_comap_eq.2 this.symm`.
-/
theorem liesOver_of_le [IsFunctionField k K] [Algebra.IsAlgebraic K K'] {w : Place k K'}
    {v : Place k K} (h : ∀ x ∈ v.ring, algebraMap K K' x ∈ w.ring) : w.LiesOver v := by
  have := Place.eq_of_le (v := v) (w := w.comap) fun x hx => ValuationSubring.mem_comap.2 (h x hx)
  exact liesOver_iff_comap_eq.2 this.symm

/- English proof (translation)
Set `f : v.ring →+* K'` to `(algebraMap K K').comp v.ring.subtype`. Establish `hf : Function.Injective f` using `(algebraMap K K').injective.comp Subtype.val_injective`. Set `g : v.ring →+* f.range` to `f.rangeRestrict`. Establish `hg : Function.Bijective g` using `⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩`. Set `I : Ideal f.range` to `(IsLocalRing.maximalIdeal v.ring).map g`.

Establish `hI : I ≠ ⊤` using `fun h => (IsLocalRing.maximalIdeal.isMaximal v.ring).ne_top ((Ideal.map_eq_top_of_bijective g hg).1 h)`. Take `⟨B, hAB, hIB⟩` from `Ideal.image_subset_nonunits_valuationSubring I hI`. Establish `hmem : ∀ a : v.ring, a ∈ IsLocalRing.maximalIdeal v.ring → f a ∈ B.nonunits` using `fun a ha => hIB ⟨g a, Ideal.mem_map_of_mem g ha, rfl⟩`. Establish `hAB' : ∀ a : v.ring, f a ∈ B` using `fun a => hAB (RingHom.mem_range_self f a)`. Take `⟨x, hx0, hx⟩` from `v.exists_valuation_lt_one_ne_zero`.

Establish `hxO : x ∈ v.ring` using `(v.ring.valuation_le_one_iff x).1 hx.le`. Establish `hfx : algebraMap K K' x ∈ B.nonunits` using `hmem ⟨x, hxO⟩ ((v.ring.valuation_lt_one_iff _).2 hx)`. Use `⟨⟨B, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `htop`. Break down `B.mem_nonunits_iff_or.1 hfx with h | h` into its components or cases.

Conclude with `hx0 ((algebraMap K K').injective (h.trans (map_zero _).symm))`. Conclude with `h (htop ▸ ValuationSubring.mem_top _)`. Introduce `c`. Rewrite using `[IsScalarTower.algebraMap_apply k K K']`. Conclude with `hAB' ⟨_, v.algebraMap_mem c⟩`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[ValuationSubring.mem_comap]`. Assume the negation of the conclusion as `hyv`. Establish `hy0 : y ≠ 0` using `fun h => hyv (h ▸ v.ring.zero_mem)`.

Establish `hinv : y⁻¹ ∈ v.ring.nonunits` using `v.ring.inv_mem_nonunits_iff.2 (Or.inr hyv)`. Take `⟨hr, hrm⟩` from `v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv`. Establish `h1 : algebraMap K K' y⁻¹ ∈ B.nonunits` using `hmem _ hrm`. Rewrite `h1` using `[map_inv₀]`. Break down `B.inv_mem_nonunits_iff.1 h1 with h | h` into its components or cases.

Conclude with `hy0 ((algebraMap K K').injective (h.trans (map_zero _).symm))`. Conclude with `h hy`. Introduce `y hy`. Conclude with `ValuationSubring.mem_comap.2 (hAB' ⟨y, hy⟩)`.
-/
theorem exists_liesOver (v : Place k K) : ∃ w : Place k K', w.LiesOver v := by
  let f : v.ring →+* K' := (algebraMap K K').comp v.ring.subtype
  have hf : Function.Injective f := (algebraMap K K').injective.comp Subtype.val_injective
  let g : v.ring →+* f.range := f.rangeRestrict
  have hg : Function.Bijective g :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := (IsLocalRing.maximalIdeal v.ring).map g
  have hI : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal v.ring).ne_top ((Ideal.map_eq_top_of_bijective g hg).1 h)
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ a : v.ring, a ∈ IsLocalRing.maximalIdeal v.ring → f a ∈ B.nonunits := fun a ha =>
    hIB ⟨g a, Ideal.mem_map_of_mem g ha, rfl⟩
  have hAB' : ∀ a : v.ring, f a ∈ B := fun a => hAB (RingHom.mem_range_self f a)
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  have hfx : algebraMap K K' x ∈ B.nonunits := hmem ⟨x, hxO⟩ ((v.ring.valuation_lt_one_iff _).2 hx)
  refine ⟨⟨B, ?_, ?_⟩, ?_⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hfx with h | h
    · exact hx0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
    · exact h (htop ▸ ValuationSubring.mem_top _)
  · intro c
    rw [IsScalarTower.algebraMap_apply k K K']
    exact hAB' ⟨_, v.algebraMap_mem c⟩
  · apply le_antisymm
    · intro y hy
      rw [ValuationSubring.mem_comap] at hy
      by_contra hyv
      have hy0 : y ≠ 0 := fun h => hyv (h ▸ v.ring.zero_mem)
      have hinv : y⁻¹ ∈ v.ring.nonunits := v.ring.inv_mem_nonunits_iff.2 (Or.inr hyv)
      obtain ⟨hr, hrm⟩ := v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv
      have h1 : algebraMap K K' y⁻¹ ∈ B.nonunits := hmem _ hrm
      rw [map_inv₀] at h1
      rcases B.inv_mem_nonunits_iff.1 h1 with h | h
      · exact hy0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
      · exact h hy
    · intro y hy
      exact ValuationSubring.mem_comap.2 (hAB' ⟨y, hy⟩)

abbrev LiesOver.algebra {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    Algebra v.ring w.ring :=
  (RingHom.codRestrict ((algebraMap K K').comp v.ring.subtype) w.ring
    fun a => h.algebraMap_mem a.2).toAlgebra

omit [IsScalarTower k K K'] in
/- English proof (translation)
Set `` to `h.algebra`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Rewrite `ha`, the goal using `[ValuationSubring.valuation_eq_one_iff]`. Establish `hw : w.ring.valuation (algebraMap K K' (a : K)) = 1` using `ha`. Establish `ha0 : (a : K) ≠ 0`.

Introduce `h0`. Rewrite `hw` using `[h0, map_zero, map_zero]`. Conclude with `zero_ne_one hw`. Establish `hinv : (a : K)⁻¹ ∈ v.ring`. Rewrite using `[← h.mem_iff, ← w.ring.valuation_le_one_iff, map_inv₀, map_inv₀, hw, inv_one]`.

Establish `h1` using `(v.ring.valuation_le_one_iff _).2 hinv`. Rewrite `h1` using `[map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))]`. Conclude with `le_antisymm (v.ring.valuation_le_one a) h1`.
-/
theorem LiesOver.isLocalHom {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsLocalHom (algebraMap v.ring w.ring) := by
  let := h.algebra
  refine ⟨fun a ha => ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  have hw : w.ring.valuation (algebraMap K K' (a : K)) = 1 := ha
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hw
    exact zero_ne_one hw
  have hinv : (a : K)⁻¹ ∈ v.ring := by
    rw [← h.mem_iff, ← w.ring.valuation_le_one_iff, map_inv₀, map_inv₀, hw, inv_one]
  have h1 := (v.ring.valuation_le_one_iff _).2 hinv
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))] at h1
  exact le_antisymm (v.ring.valuation_le_one a) h1

/- English proof (translation)
Set `` to `h.algebra`. Conclude with `IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply k K K' c)`.
-/
theorem LiesOver.isScalarTower {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsScalarTower k v.ring w.ring := by
  let := h.algebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k K K' c)

/- English proof (translation)
Take `⟨y, hy, hfin⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Establish `hb` using `(isTranscendenceBasis_singleton hy hfin).algebraMap_comp (A := K')`. Establish `hr : Set.range (⇑(algebraMap K K') ∘ ((↑) : ({y} : Set K) → K)) = {algebraMap K K' y}`. Rewrite using `[Set.range_comp, Subtype.range_coe, Set.image_singleton]`. Establish `halg` using `hb.isAlgebraic_field`.

Rewrite `halg` using `[hr]`. Use `essFiniteType (k := k) (K := K)` as an intermediate fact. Establish `: Algebra.EssFiniteType k K'` using `Algebra.EssFiniteType.comp k K K'`. Establish `: Algebra.EssFiniteType (IntermediateField.adjoin k {algebraMap K K' y}) K'` using `Algebra.EssFiniteType.of_comp k _ K'`. Conclude with `⟨⟨algebraMap K K' y, (algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).1 hb.1, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩`.
-/
theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional [IsFunctionField k K]
    [FiniteDimensional K K'] : IsFunctionField k K' := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hb := (isTranscendenceBasis_singleton hy hfin).algebraMap_comp (A := K')
  have hr : Set.range (⇑(algebraMap K K') ∘ ((↑) : ({y} : Set K) → K)) = {algebraMap K K' y} := by
    rw [Set.range_comp, Subtype.range_coe, Set.image_singleton]
  have halg := hb.isAlgebraic_field
  rw [hr] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {algebraMap K K' y}) K' :=
    Algebra.EssFiniteType.of_comp k _ K'
  exact ⟨⟨algebraMap K K' y,
    (algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).1 hb.1,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

section Degree

variable [IsFunctionField k K]

noncomputable def uniformizer (v : Place k K) : K :=
  Classical.choose v.exists_ord_eq_one

/- English proof (translation)
The claim follows from `Classical.choose_spec v.exists_ord_eq_one`.
-/
theorem ord_uniformizer (v : Place k K) : v.ord v.uniformizer = 1 :=
  Classical.choose_spec v.exists_ord_eq_one

/- English proof (translation)
Introduce `h` and use `by have h1 := v.ord_uniformizer rw [h, ord_zero] at h1 exact zero_ne_one h1`.
-/
theorem uniformizer_ne_zero (v : Place k K) : v.uniformizer ≠ 0 := fun h => by
  have h1 := v.ord_uniformizer
  rw [h, ord_zero] at h1
  exact zero_ne_one h1

variable [IsFunctionField k K']

noncomputable def ramificationIdx (w : Place k K') (v : Place k K) : ℕ :=
  (w.ord (algebraMap K K' v.uniformizer)).toNat

noncomputable def inertiaDeg (w : Place k K') (v : Place k K) : ℕ :=
  w.deg / v.deg

omit [IsFunctionField k K] [IsFunctionField k K'] [IsScalarTower k K K'] in
/- English proof (translation)
Set `` to `h.algebra`. Conclude with `Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab => Subtype.ext ((algebraMap K K').injective (congrArg Subtype.val hab))`.
-/
theorem LiesOver.isTorsionFree {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    Module.IsTorsionFree v.ring w.ring := by
  let := h.algebra
  exact Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab =>
    Subtype.ext ((algebraMap K K').injective (congrArg Subtype.val hab))

omit [IsScalarTower k K K'] in

/- English proof (translation)
Set `` to `h.algebra`. Use `h.isLocalHom` as an intermediate fact. Use `h.isTorsionFree` as an intermediate fact. Set `: Algebra v.ring K'` to `((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra`. Establish `: IsScalarTower v.ring K K'` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `: IsScalarTower v.ring w.ring K'` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: w.heightOneSpectrum.asIdeal.LiesOver v.heightOneSpectrum.asIdeal` using `inferInstanceAs ((IsLocalRing.maximalIdeal w.ring).LiesOver (IsLocalRing.maximalIdeal v.ring))`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum w.heightOneSpectrum x`.
-/
theorem LiesOver.valuation_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    letI := h.algebra
    v.valuation x ^ (IsLocalRing.maximalIdeal v.ring).ramificationIdx'
        (IsLocalRing.maximalIdeal w.ring) =
      w.valuation (algebraMap K K' x) := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isTorsionFree
  let : Algebra v.ring K' := ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra
  have : IsScalarTower v.ring K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : w.heightOneSpectrum.asIdeal.LiesOver v.heightOneSpectrum.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal w.ring).LiesOver (IsLocalRing.maximalIdeal v.ring))
  exact IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum
    w.heightOneSpectrum x

/- English proof (translation)
Set `` to `h.algebra`. Establish `h1` using `h.valuation_algebraMap v.uniformizer`. Establish `hπ : algebraMap K K' v.uniformizer ≠ 0` using `(map_ne_zero _).2 v.uniformizer_ne_zero`. Rewrite `h1` using `[v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer, w.valuation_eq_exp_neg_ord hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul]`. Rewrite using `[ramificationIdx]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem LiesOver.ramificationIdx'_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    (IsLocalRing.maximalIdeal v.ring).ramificationIdx' (IsLocalRing.maximalIdeal w.ring) =
      w.ramificationIdx v := by
  let := h.algebra
  have h1 := h.valuation_algebraMap v.uniformizer
  have hπ : algebraMap K K' v.uniformizer ≠ 0 := (map_ne_zero _).2 v.uniformizer_ne_zero
  rw [v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    w.valuation_eq_exp_neg_ord hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
  rw [ramificationIdx]
  omega

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Set `` to `h.algebra`. Establish `h1` using `h.valuation_algebraMap x`. Establish `hx' : algebraMap K K' x ≠ 0` using `(map_ne_zero _).2 hx`.

Rewrite `h1` using `[v.valuation_eq_exp_neg_ord hx, w.valuation_eq_exp_neg_ord hx', ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, h.ramificationIdx'_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LiesOver.ord_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    w.ord (algebraMap K K' x) = w.ramificationIdx v * v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  let := h.algebra
  have h1 := h.valuation_algebraMap x
  have hx' : algebraMap K K' x ≠ 0 := (map_ne_zero _).2 hx
  rw [v.valuation_eq_exp_neg_ord hx, w.valuation_eq_exp_neg_ord hx', ← WithZero.exp_nsmul,
    WithZero.exp_inj, nsmul_eq_mul, h.ramificationIdx'_eq] at h1
  linarith

omit [IsFunctionField k K'] in

/- English proof (translation)
Set `` to `h.algebra`. Use `h.isLocalHom` as an intermediate fact. Use `h.isScalarTower` as an intermediate fact. Conclude with `Module.finrank_mul_finrank k v.ResidueField w.ResidueField`.
-/
theorem LiesOver.deg_mul_finrank {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    v.deg * Module.finrank v.ResidueField w.ResidueField = w.deg := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isScalarTower
  exact Module.finrank_mul_finrank k v.ResidueField w.ResidueField

omit [IsFunctionField k K'] in

/- English proof (translation)
Set `` to `h.algebra`. Use `h.isLocalHom` as an intermediate fact. Rewrite using `[inertiaDeg, ← h.deg_mul_finrank, Nat.mul_div_cancel_left _ v.deg_pos]`.
-/
theorem LiesOver.finrank_residueField {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    Module.finrank v.ResidueField w.ResidueField = w.inertiaDeg v := by
  let := h.algebra
  have := h.isLocalHom
  rw [inertiaDeg, ← h.deg_mul_finrank, Nat.mul_div_cancel_left _ v.deg_pos]

/- English proof (translation)
Set `` to `h.algebra`. Use `h.isLocalHom` as an intermediate fact. Rewrite using `[← h.finrank_residueField, ← h.deg_mul_finrank, mul_comm]`.
-/
theorem LiesOver.deg_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    w.deg = w.inertiaDeg v * v.deg := by
  let := h.algebra
  have := h.isLocalHom
  rw [← h.finrank_residueField, ← h.deg_mul_finrank, mul_comm]

end Degree

end Place

end GroundTheory.FunctionField
