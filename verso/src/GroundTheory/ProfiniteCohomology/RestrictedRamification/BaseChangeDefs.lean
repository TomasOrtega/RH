import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

universe u

noncomputable section

section Abstract

variable {F L Ω : Type u} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)

include h in
/- English proof (translation)
Rewrite using `[← h]`. Conclude with `hx`.
-/
theorem mem_of_restrictScalars_eq {x : Ω} (hx : x ∈ E') : x ∈ E := by
  rw [← h]
  exact hx

include h in
/- English proof (translation)
Rewrite `hx` using `[← h]`. Conclude with `hx`.
-/
theorem mem_of_restrictScalars_eq' {x : Ω} (hx : x ∈ E) : x ∈ E' := by
  rw [← h] at hx
  exact hx

def fieldEquivOfRestrictScalarsEq : E ≃ₐ[F] E' where
  toFun x := ⟨x.1, mem_of_restrictScalars_eq' h x.2⟩
  invFun y := ⟨y.1, mem_of_restrictScalars_eq h y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_fieldEquivOfRestrictScalarsEq (x : E) :
    ((fieldEquivOfRestrictScalarsEq h x : E') : Ω) = x :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_fieldEquivOfRestrictScalarsEq_symm (y : E') :
    (((fieldEquivOfRestrictScalarsEq h).symm y : E) : Ω) = y :=
  rfl

def embeddingOfRestrictScalarsEq : L →ₐ[F] E :=
  (IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra fun x =>
    mem_of_restrictScalars_eq h (E'.algebraMap_mem x)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_embeddingOfRestrictScalarsEq (x : L) :
    ((embeddingOfRestrictScalarsEq h x : E) : Ω) = algebraMap L Ω x :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fieldEquivOfRestrictScalarsEq_embedding (x : L) :
    fieldEquivOfRestrictScalarsEq h (embeddingOfRestrictScalarsEq h x) = algebraMap L E' x :=
  rfl

def fixingOfRestrictScalarsEq : Subgroup Gal(E/F) :=
  (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup

/- English proof (translation)
Express the relevant statement in the definitionally equal form `σ ∈ (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup ↔ _`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hσ x`. Conclude with `hσ _ ⟨x, rfl⟩`.

Introduce and unpack `hσ _ ⟨x, rfl⟩`. Conclude with `hσ x`.
-/
theorem mem_fixingOfRestrictScalarsEq_iff (σ : Gal(E/F)) :
    σ ∈ fixingOfRestrictScalarsEq h ↔
      ∀ x : L, σ (embeddingOfRestrictScalarsEq h x) = embeddingOfRestrictScalarsEq h x := by
  change σ ∈ (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup ↔ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x
    exact hσ _ ⟨x, rfl⟩
  · rintro hσ _ ⟨x, rfl⟩
    exact hσ x

def autOfRestrictScalarsEq (σ : Gal(E/F)) (hσ : σ ∈ fixingOfRestrictScalarsEq h) : Gal(E'/L) :=
  AlgEquiv.ofRingEquiv (f := ((fieldEquivOfRestrictScalarsEq h).symm.toRingEquiv.trans
      σ.toRingEquiv).trans (fieldEquivOfRestrictScalarsEq h).toRingEquiv) fun x => by
    change fieldEquivOfRestrictScalarsEq h (σ (embeddingOfRestrictScalarsEq h x)) = _
    rw [(mem_fixingOfRestrictScalarsEq_iff h σ).1 hσ x]
    rfl

def autOfRestrictScalarsEqInv (τ : Gal(E'/L)) : Gal(E/F) :=
  (fieldEquivOfRestrictScalarsEq h).trans ((τ.restrictScalars F).trans
    (fieldEquivOfRestrictScalarsEq h).symm)

/- English proof (translation)
Rewrite using `[mem_fixingOfRestrictScalarsEq_iff]`. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((τ (algebraMap L E' x) : E') : Ω) = algebraMap L Ω x`. Rewrite using `[τ.commutes]`.

Both sides reduce to the same expression.
-/
theorem autOfRestrictScalarsEqInv_mem (τ : Gal(E'/L)) :
    autOfRestrictScalarsEqInv h τ ∈ fixingOfRestrictScalarsEq h := by
  rw [mem_fixingOfRestrictScalarsEq_iff]
  intro x
  apply Subtype.ext
  change ((τ (algebraMap L E' x) : E') : Ω) = algebraMap L Ω x
  rw [τ.commutes]
  rfl

def fixingMulEquivOfRestrictScalarsEq : fixingOfRestrictScalarsEq h ≃* Gal(E'/L) where
  toFun σ := autOfRestrictScalarsEq h σ.1 σ.2
  invFun τ := ⟨autOfRestrictScalarsEqInv h τ, autOfRestrictScalarsEqInv_mem h τ⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_fixingMulEquivOfRestrictScalarsEq_apply (σ : fixingOfRestrictScalarsEq h) (x : E') :
    ((fixingMulEquivOfRestrictScalarsEq h σ x : E') : Ω) =
      ((σ : Gal(E/F)) ((fieldEquivOfRestrictScalarsEq h).symm x) : Ω) :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fieldEquivOfRestrictScalarsEq_apply_apply (σ : fixingOfRestrictScalarsEq h) (x : E) :
    fieldEquivOfRestrictScalarsEq h ((σ : Gal(E/F)) x) =
      fixingMulEquivOfRestrictScalarsEq h σ (fieldEquivOfRestrictScalarsEq h x) :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_fixingMulEquivOfRestrictScalarsEq_symm_apply (τ : Gal(E'/L)) (x : E) :
    (((((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) x :
      E) : Ω) = (τ (fieldEquivOfRestrictScalarsEq h x) : Ω) :=
  rfl

/- English proof (translation)
Set `f : Gal(E'/L) →* Gal(E/F)` to `(fixingOfRestrictScalarsEq h).subtype.comp (fixingMulEquivOfRestrictScalarsEq h).symm.toMonoidHom`. Express the relevant statement in the definitionally equal form `Continuous f`. Use `continuous_of_continuousAt_one f ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`.

Take `⟨K, hK, hKs⟩` from `(krullTopology_mem_nhds_one_iff F E s).1 hs`. Set `b` to `Module.finBasis F K`. Set `K' : IntermediateField L E'` to `IntermediateField.adjoin L (Set.range fun i => fieldEquivOfRestrictScalarsEq h (b i : E))`. Establish `hK' : FiniteDimensional L K'` using `IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y`. Rewrite using `[Filter.mem_map]`.

Use `Filter.mem_of_superset ((krullTopology_mem_nhds_one_iff L E' _).2 ⟨K', hK', le_rfl⟩) fun τ hτ => hKs ?_` and prove the remaining obligations. Rewrite `hτ`, the goal using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Establish `hb : ∀ i, f τ (b i : E) = b i` using `fun i => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((τ (fieldEquivOfRestrictScalarsEq h (b i : E)) : E') : Ω) = _`.

Rewrite using `[hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]`. Both sides reduce to the same expression. Introduce `y hy`. Establish `hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E)`. Use `congrArg K.val (b.sum_repr ⟨y, hy⟩)` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul] at this`. Conclude with `this.symm`. Rewrite using `[hy', map_sum]`. Simplify using `only [map_smul, hb]`.
-/
theorem continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm [Algebra.IsIntegral L E'] :
    Continuous fun τ : Gal(E'/L) =>
      (((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) := by
  let f : Gal(E'/L) →* Gal(E/F) :=
    (fixingOfRestrictScalarsEq h).subtype.comp (fixingMulEquivOfRestrictScalarsEq h).symm.toMonoidHom
  change Continuous f
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff F E s).1 hs
  classical
  let b := Module.finBasis F K
  let K' : IntermediateField L E' :=
    IntermediateField.adjoin L (Set.range fun i => fieldEquivOfRestrictScalarsEq h (b i : E))
  have hK' : FiniteDimensional L K' :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((krullTopology_mem_nhds_one_iff L E' _).2 ⟨K', hK', le_rfl⟩) fun τ hτ => hKs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  have hb : ∀ i, f τ (b i : E) = b i := fun i => by
    apply Subtype.ext
    change ((τ (fieldEquivOfRestrictScalarsEq h (b i : E)) : E') : Ω) = _
    rw [hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]
    rfl
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg K.val (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hy', map_sum]
  simp only [map_smul, hb]

end Abstract

section Fields

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable [IsGalois F Ω]

/- English proof (translation)
Set `b` to `Module.finBasis F L`. Take `⟨E, hf, hu, hE⟩` from `exists_subset_of_subset_maxUnramifiedOutside S (Finset.univ.image fun i => algebraMap L Ω (b i)) fun x hx => by`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hL (b i)`. Use `⟨E, hf, hu, fun x => ?_⟩` and prove the remaining obligations.

Establish `hx : algebraMap L Ω x = ∑ i, b.repr x i • algebraMap L Ω (b i)` using `by conv_lhs => rw [← b.sum_repr x]`. Express the relevant statement in the definitionally equal form `IsScalarTower.toAlgHom F L Ω _ = _`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Both sides reduce to the same expression.

Rewrite using `[hx]`. Conclude with `sum_mem fun i _ => E.smul_mem (hE _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`.
-/
theorem exists_le_of_algebraMap_mem (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
      ∀ x : L, algebraMap L Ω x ∈ E := by
  classical
  let b := Module.finBasis F L
  obtain ⟨E, hf, hu, hE⟩ := exists_subset_of_subset_maxUnramifiedOutside S
    (Finset.univ.image fun i => algebraMap L Ω (b i)) fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact hL (b i)
  refine ⟨E, hf, hu, fun x => ?_⟩
  have hx : algebraMap L Ω x = ∑ i, b.repr x i • algebraMap L Ω (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    change IsScalarTower.toAlgHom F L Ω _ = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hx]
  exact sum_mem fun i _ => E.smul_mem (hE _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

/- English proof (translation)
Take `⟨E, hf, hu, hE⟩` from `exists_le_of_algebraMap_mem S hL`. Set `j : L →ₐ[F] E` to `(IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra hE`. Set `_ : Algebra L E` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower F L E` using `IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`. Use `NumberField.of_module_finite F E` as an intermediate fact.

Introduce `v hv P hP hPv`. Take `⟨⟨Q, hQ, hQP⟩⟩` from `(inferInstance : Nonempty (P.primesOver (𝓞 E)))`. Establish `: Q.LiesOver v.asIdeal` using `Ideal.LiesOver.trans Q P v.asIdeal`. Establish `h` using `((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hu v hv Q hQ this)).1`. Establish `e : P = Q.under (𝓞 L)` using `Ideal.over_def Q P`.

Substitute `e` using the available equality. Conclude with `h`.
-/
theorem isUnramifiedIn_of_algebraMap_mem
    (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  obtain ⟨E, hf, hu, hE⟩ := exists_le_of_algebraMap_mem S hL
  let j : L →ₐ[F] E := (IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra hE
  let _ : Algebra L E := j.toRingHom.toAlgebra
  have : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have := NumberField.of_module_finite F E
  intro v hv P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 E)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have h := ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hu v hv Q hQ this)).1
  have e : P = Q.under (𝓞 L) := Ideal.over_def Q P
  subst e
  exact h

omit [IsGalois F Ω] in

/- English proof (translation)
Establish `: FiniteDimensional F M` using `FiniteDimensional.trans F L M`. Use `NumberField.of_module_finite L M` as an intermediate fact. Express the relevant statement in the definitionally equal form `(∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hM w hw Q hQ hQw`.

Establish `hv0 : w.asIdeal.under (𝓞 F) ≠ ⊥` using `Ideal.under_ne_bot (𝓞 F) w.ne_bot`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨w.asIdeal.under (𝓞 F), inferInstance, hv0⟩`. Establish `hwv : w.asIdeal.LiesOver v.asIdeal` using `⟨rfl⟩`. Establish `hv : v ∉ S` using `fun hvS => hw ⟨v, hvS, hwv⟩`. Establish `: Q.LiesOver v.asIdeal` using `Ideal.LiesOver.trans Q w.asIdeal v.asIdeal`.

Conclude with `((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hM v hv Q hQ this)).2`. Introduce `hM v hv Q hQ hQv`. Establish `hP0 : Q.under (𝓞 L) ≠ ⊥`. Establish `: (Q.under (𝓞 L)).LiesOver v.asIdeal` using `⟨by rw [Ideal.under_under]; exact hQv.over⟩`. Conclude with `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (Q.under (𝓞 L))`.

Set `w : HeightOneSpectrum (𝓞 L)` to `⟨Q.under (𝓞 L), inferInstance, hP0⟩`. Establish `hwv : w.asIdeal.LiesOver v.asIdeal` using `⟨by`. Express the relevant statement in the definitionally equal form `v.asIdeal = (Q.under (𝓞 L)).under (𝓞 F)`. Rewrite using `[Ideal.under_under]`. Conclude with `hQv.over⟩`.

Establish `hw : w ∉ placesOver S`. Introduce and unpack `⟨u, huS, hwu⟩`. Establish `huv : u = v` using `HeightOneSpectrum.ext (hwu.over.trans hwv.over.symm)`. Conclude with `hv (huv ▸ huS)`. Establish `h1` using `hM w hw Q hQ ⟨rfl⟩`.

Establish `h2` using `hL v hv (Q.under (𝓞 L)) inferInstance hwv`. Conclude with `(isUnramifiedAt_tower_iff (F := F) (L := L) Q).2 ⟨h2, h1⟩`.
-/
theorem isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn
    (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) (M : IntermediateField L Ω)
    [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔ IsUnramifiedOutside (placesOver S) M := by
  have : FiniteDimensional F M := FiniteDimensional.trans F L M
  have := NumberField.of_module_finite L M
  change (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) ↔ _
  constructor
  · intro hM w hw Q hQ hQw
    have hv0 : w.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) w.ne_bot
    let v : HeightOneSpectrum (𝓞 F) := ⟨w.asIdeal.under (𝓞 F), inferInstance, hv0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hv : v ∉ S := fun hvS => hw ⟨v, hvS, hwv⟩
    have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal
    exact ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hM v hv Q hQ this)).2
  · intro hM v hv Q hQ hQv
    have hP0 : Q.under (𝓞 L) ≠ ⊥ := by
      have : (Q.under (𝓞 L)).LiesOver v.asIdeal :=
        ⟨by rw [Ideal.under_under]; exact hQv.over⟩
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (Q.under (𝓞 L))
    let w : HeightOneSpectrum (𝓞 L) := ⟨Q.under (𝓞 L), inferInstance, hP0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by
      change v.asIdeal = (Q.under (𝓞 L)).under (𝓞 F)
      rw [Ideal.under_under]; exact hQv.over⟩
    have hw : w ∉ placesOver S := by
      rintro ⟨u, huS, hwu⟩
      have huv : u = v := HeightOneSpectrum.ext (hwu.over.trans hwv.over.symm)
      exact hv (huv ▸ huS)
    have h1 := hM w hw Q hQ ⟨rfl⟩
    have h2 := hL v hv (Q.under (𝓞 L)) inferInstance hwv
    exact (isUnramifiedAt_tower_iff (F := F) (L := L) Q).2 ⟨h2, h1⟩

/- English proof (translation)
Establish `hLu` using `isUnramifiedIn_of_algebraMap_mem S hL`. Establish `: IsGalois L Ω` using `IsGalois.tower_top_of_isGalois F L Ω`. Use extensionality with `x`. Rewrite using `[IntermediateField.mem_restrictScalars]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨M, hf, hu, hxM⟩` from `(mem_maxUnramifiedOutside_iff (placesOver S)).1 hx`. Establish `: FiniteDimensional F (M.restrictScalars F)` using `FiniteDimensional.trans F L M`. Conclude with `le_maxUnramifiedOutside S ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).2 hu) hxM`. Introduce `hx`.

Take `⟨E, hf, hu, hxE⟩` from `(mem_maxUnramifiedOutside_iff S).1 hx`. Take `⟨E₀, hf₀, hu₀, hE₀⟩` from `exists_le_of_algebraMap_mem S hL`. Set `E' : IntermediateField F Ω` to `E₀ ⊔ E`. Establish `hE' : ∀ y : L, algebraMap L Ω y ∈ E'.toSubfield` using `fun y => le_sup_left (α := IntermediateField F Ω) (hE₀ y)`. Set `M : IntermediateField L Ω` to `E'.toSubfield.toIntermediateField hE'`.

Establish `hMF : M.restrictScalars F = E'`. Use extensionality with `y`. Conclude with `Iff.rfl`. Establish `: FiniteDimensional F M` using `(inferInstance : FiniteDimensional F E')`. Establish `: FiniteDimensional L M` using `Module.Finite.of_restrictScalars_finite F L M`.

Establish `hMu : IsUnramifiedOutside S (M.restrictScalars F)`. Rewrite using `[hMF]`. Conclude with `hu₀.sup hu`. Conclude with `le_maxUnramifiedOutside (placesOver S) ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).1 hMu) (le_sup_right (α := IntermediateField F Ω) hxE)`.
-/
theorem restrictScalars_maxUnramifiedOutside_eq
    (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    (maxUnramifiedOutside L Ω (placesOver S)).restrictScalars F = maxUnramifiedOutside F Ω S := by
  have hLu := isUnramifiedIn_of_algebraMap_mem S hL
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  ext x
  rw [IntermediateField.mem_restrictScalars]
  constructor
  · intro hx
    obtain ⟨M, hf, hu, hxM⟩ := (mem_maxUnramifiedOutside_iff (placesOver S)).1 hx
    have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
    exact le_maxUnramifiedOutside S
      ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).2 hu) hxM
  · intro hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maxUnramifiedOutside_iff S).1 hx
    obtain ⟨E₀, hf₀, hu₀, hE₀⟩ := exists_le_of_algebraMap_mem S hL
    let E' : IntermediateField F Ω := E₀ ⊔ E
    have hE' : ∀ y : L, algebraMap L Ω y ∈ E'.toSubfield := fun y =>
      le_sup_left (α := IntermediateField F Ω) (hE₀ y)
    let M : IntermediateField L Ω := E'.toSubfield.toIntermediateField hE'
    have hMF : M.restrictScalars F = E' := by
      ext y
      exact Iff.rfl
    have : FiniteDimensional F M := (inferInstance : FiniteDimensional F E')
    have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
    have hMu : IsUnramifiedOutside S (M.restrictScalars F) := by
      rw [hMF]
      exact hu₀.sup hu
    exact le_maxUnramifiedOutside (placesOver S)
      ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).1 hMu)
      (le_sup_right (α := IntermediateField F Ω) hxE)

variable {S} (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

abbrev gsFieldEquiv :
    maxUnramifiedOutside F Ω S ≃ₐ[F] maxUnramifiedOutside L Ω (placesOver S) :=
  fieldEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)

abbrev gsEmbedding : L →ₐ[F] maxUnramifiedOutside F Ω S :=
  embeddingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)

end Fields

section Groups

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

instance finiteDimensional_fieldRange_gsEmbedding :
    FiniteDimensional F (gsEmbedding (S := S) hL).fieldRange := by
  exact LinearEquiv.finiteDimensional (gsEmbedding hL).equivFieldRange.toLinearEquiv

def gsOpenSubgroup : OpenSubgroup (galUnramifiedOutside F Ω S) :=
  ⟨fixingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL),
    (gsEmbedding (S := S) hL).fieldRange.fixingSubgroup_isOpen⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_gsOpenSubgroup : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) =
    fixingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) :=
  rfl

/- English proof (translation)
The claim follows from `mem_fixingOfRestrictScalarsEq_iff _ σ`.
-/
theorem mem_gsOpenSubgroup_iff (σ : galUnramifiedOutside F Ω S) :
    σ ∈ gsOpenSubgroup S hL ↔ ∀ x : L, σ (gsEmbedding hL x) = gsEmbedding hL x :=
  mem_fixingOfRestrictScalarsEq_iff _ σ

def gsBaseChange : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) ≃ₜ*
    galUnramifiedOutside L Ω (placesOver S) :=
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  have : CompactSpace (galUnramifiedOutside L Ω (placesOver S)) :=
    (galUnramifiedOutside_isProfinite (placesOver S)).1
  have : T2Space (galUnramifiedOutside F Ω S) := (galUnramifiedOutside_isProfinite S).2.1
  have hc : Continuous (fixingMulEquivOfRestrictScalarsEq
      (restrictScalars_maxUnramifiedOutside_eq S hL)).symm :=
    (continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm _).subtype_mk _
  let e := hc.homeoOfEquivCompactToT2
    (f := (fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)).symm.toEquiv)
  { fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) with
    continuous_toFun := e.symm.continuous
    continuous_invFun := hc }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gsBaseChange_toMulEquiv : (gsBaseChange S hL).toMulEquiv =
    fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) :=
  rfl

variable {S}

/- English proof (translation)
The claim follows from `coe_fixingMulEquivOfRestrictScalarsEq_apply _ σ x`.
-/
theorem coe_gsBaseChange_apply (σ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)))
    (x : maxUnramifiedOutside L Ω (placesOver S)) :
    ((gsBaseChange S hL σ x : maxUnramifiedOutside L Ω (placesOver S)) : Ω) =
      ((σ : galUnramifiedOutside F Ω S) ((gsFieldEquiv hL).symm x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_apply _ σ x

/- English proof (translation)
The claim follows from `fieldEquivOfRestrictScalarsEq_apply_apply _ σ x`.
-/
theorem gsFieldEquiv_apply_apply (σ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)))
    (x : maxUnramifiedOutside F Ω S) :
    gsFieldEquiv hL ((σ : galUnramifiedOutside F Ω S) x) = gsBaseChange S hL σ (gsFieldEquiv hL x) :=
  fieldEquivOfRestrictScalarsEq_apply_apply _ σ x

/- English proof (translation)
The claim follows from `coe_fixingMulEquivOfRestrictScalarsEq_symm_apply _ τ x`.
-/
theorem coe_gsBaseChange_symm_apply (τ : galUnramifiedOutside L Ω (placesOver S))
    (x : maxUnramifiedOutside F Ω S) :
    (((((gsBaseChange S hL).symm τ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))) : galUnramifiedOutside F Ω S) x :
        maxUnramifiedOutside F Ω S) : Ω) = (τ (gsFieldEquiv hL x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_symm_apply _ τ x

end Groups

end

end GroundTheory.ProfCoh
