import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.InfinitePlaces
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.IntegerUnits

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

variable (L) in

abbrev SIdelesProduct : Type _ :=
  ((v : InfinitePlace K) → (w : v.placesOver L) → (w.1.Completion)ˣ) ×
    ((v : S) → (w : PlacesOver L v.1) → (w.1.adicCompletion L)ˣ) ×
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)

def integerUnitAt (w : HeightOneSpectrum (𝓞 L)) (x : IdeleGroup L) (hx : ord w x = 0) :
    (w.adicCompletionIntegers L)ˣ where
  val := ⟨(x : 𝔸[L]).2 w, ((ord_eq_zero_iff w x).1 hx).1⟩
  inv := ⟨((x⁻¹ : IdeleGroup L) : 𝔸[L]).2 w, ((ord_eq_zero_iff w x).1 hx).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[L] ↦ y.2 w) x.mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[L] ↦ y.2 w) x.inv_mul)

omit [NumberField K] in
/- English proof (translation)
The claim follows from `hx w.1 fun h ↦ hv (by rwa [mem_placesAbove, (below_eq_iff w.1 v).2 w.2] at h)`.
-/
theorem ord_eq_zero_of_mem_sIdeles_placesAbove {x : IdeleGroup L}
    (hx : x ∈ sIdeles (placesAbove L S)) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (w : PlacesOver L v) : ord w.1 x = 0 :=
  hx w.1 fun h ↦ hv (by rwa [mem_placesAbove, (below_eq_iff w.1 v).2 w.2] at h)

def sIdelesIntegerPart :
    sIdeles (placesAbove L S) →* ((v : ↥Sᶜ) → (w : PlacesOver L v.1) →
      (w.1.adicCompletionIntegers L)ˣ) where
  toFun x v w := integerUnitAt w.1 x (ord_eq_zero_of_mem_sIdeles_placesAbove S x.2 v.2 w)
  map_one' := funext fun _ ↦ funext fun _ ↦ Units.ext (Subtype.ext rfl)
  map_mul' _ _ := funext fun _ ↦ funext fun _ ↦ Units.ext (Subtype.ext rfl)

omit [NumberField K] in
/- English proof (translation)
The claim follows from `funext fun _ ↦ Units.ext rfl`.
-/
theorem integerUnitsAboveIncl_sIdelesIntegerPart (x : sIdeles (placesAbove L S)) (v : ↥Sᶜ) :
    integerUnitsAboveIncl v.1 (sIdelesIntegerPart S x v) = finiteProjAbove v.1 (x : IdeleGroup L) :=
  funext fun _ ↦ Units.ext rfl

def sIdelesToProduct : sIdeles (placesAbove L S) →* SIdelesProduct L S :=
  MonoidHom.prod ((MonoidHom.pi fun v ↦ infiniteProjAbove v).comp (sIdeles _).subtype)
    (MonoidHom.prod ((MonoidHom.pi fun v : S ↦ finiteProjAbove v.1).comp (sIdeles _).subtype)
      (sIdelesIntegerPart S))

omit [NumberField K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sIdelesToProduct_snd_snd (x : sIdeles (placesAbove L S)) (v : ↥Sᶜ) :
    (sIdelesToProduct S x).2.2 v = sIdelesIntegerPart S x v :=
  rfl

/- English proof (translation)
Use `Prod.ext (funext fun v ↦ ?_) (Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_))` and prove the remaining obligations. Conclude with `infiniteProjAbove_smul v σ (x : IdeleGroup L)`. Conclude with `finiteProjAbove_smul v.1 σ (x : IdeleGroup L)`. Apply `integerUnitsAboveIncl_injective v.1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `integerUnitsAboveIncl v.1 (sIdelesIntegerPart S (σ • x) v) = integerUnitsAboveIncl v.1 (σ • sIdelesIntegerPart S x v)`.

Rewrite using `[integerUnitsAboveIncl_smul, integerUnitsAboveIncl_sIdelesIntegerPart, integerUnitsAboveIncl_sIdelesIntegerPart, coe_smul_sIdeles]`. Conclude with `finiteProjAbove_smul v.1 σ (x : IdeleGroup L)`.
-/
theorem sIdelesToProduct_smul (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesToProduct S (σ • x) = σ • sIdelesToProduct S x := by
  refine Prod.ext (funext fun v ↦ ?_) (Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_))
  · exact infiniteProjAbove_smul v σ (x : IdeleGroup L)
  · exact finiteProjAbove_smul v.1 σ (x : IdeleGroup L)
  · apply integerUnitsAboveIncl_injective v.1
    change integerUnitsAboveIncl v.1 (sIdelesIntegerPart S (σ • x) v) =
      integerUnitsAboveIncl v.1 (σ • sIdelesIntegerPart S x v)
    rw [integerUnitsAboveIncl_smul, integerUnitsAboveIncl_sIdelesIntegerPart,
      integerUnitsAboveIncl_sIdelesIntegerPart, coe_smul_sIdeles]
    exact finiteProjAbove_smul v.1 σ (x : IdeleGroup L)

omit [NumberField K] [NumberField L] in
/- English proof (translation)
The claim follows from `(InfinitePlace.liesOver_iff_comap_eq _ u).2 rfl`.
-/
theorem mem_placesOver_comap (u : InfinitePlace L) :
    u ∈ (u.comap (algebraMap K L)).placesOver L :=
  (InfinitePlace.liesOver_iff_comap_eq _ u).2 rfl

omit [NumberField K] in

/- English proof (translation)
Introduce `x y h`. Use `Subtype.ext (Units.ext (adele_ext (funext fun u ↦ ?_) fun u ↦ ?_))` and prove the remaining obligations. Conclude with `congrArg (fun p : SIdelesProduct L S ↦ ((p.1 (u.comap (algebraMap K L)) ⟨u, mem_placesOver_comap u⟩ : (u.Completion)ˣ) : u.Completion)) h`. Distinguish the cases in `hu : below K u ∈ S`. Conclude with `congrArg (fun p : SIdelesProduct L S ↦ ((p.2.1 ⟨below K u, hu⟩ ⟨u, inferInstance⟩ : (u.adicCompletion L)ˣ) : u.adicCompletion L)) h`.

Conclude with `congrArg (fun p : SIdelesProduct L S ↦ (((p.2.2 ⟨below K u, hu⟩ ⟨u, inferInstance⟩ : (u.adicCompletionIntegers L)ˣ) : u.adicCompletionIntegers L) : u.adicCompletion L)) h`.
-/
theorem sIdelesToProduct_injective : Function.Injective (sIdelesToProduct (L := L) S) := by
  intro x y h
  refine Subtype.ext (Units.ext (adele_ext (funext fun u ↦ ?_) fun u ↦ ?_))
  · exact congrArg (fun p : SIdelesProduct L S ↦ ((p.1 (u.comap (algebraMap K L))
      ⟨u, mem_placesOver_comap u⟩ : (u.Completion)ˣ) : u.Completion)) h
  · by_cases hu : below K u ∈ S
    · exact congrArg (fun p : SIdelesProduct L S ↦ ((p.2.1 ⟨below K u, hu⟩
        ⟨u, inferInstance⟩ : (u.adicCompletion L)ˣ) : u.adicCompletion L)) h
    · exact congrArg (fun p : SIdelesProduct L S ↦ (((p.2.2 ⟨below K u, hu⟩
        ⟨u, inferInstance⟩ : (u.adicCompletionIntegers L)ˣ) : u.adicCompletionIntegers L) :
          u.adicCompletion L)) h

variable {S}

def assembleInfinite (p : SIdelesProduct L S) (u : InfinitePlace L) : (u.Completion)ˣ :=
  p.1 (u.comap (algebraMap K L)) ⟨u, mem_placesOver_comap u⟩

open Classical in

def assembleFinite (p : SIdelesProduct L S) (u : HeightOneSpectrum (𝓞 L)) :
    (u.adicCompletion L)ˣ :=
  if h : below K u ∈ S then p.2.1 ⟨below K u, h⟩ ⟨u, inferInstance⟩
  else integerUnitsAboveIncl (below K u) (p.2.2 ⟨below K u, h⟩) ⟨u, inferInstance⟩

omit [NumberField K] in
/- English proof (translation)
Take `⟨u, hu⟩` from `w`. Establish `e : u.comap (algebraMap K L) = v` using `(InfinitePlace.liesOver_iff_comap_eq v u).1 hu`. Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem assembleInfinite_eq (p : SIdelesProduct L S) (v : InfinitePlace K) (w : v.placesOver L) :
    assembleInfinite p w.1 = p.1 v w := by
  obtain ⟨u, hu⟩ := w
  have e : u.comap (algebraMap K L) = v := (InfinitePlace.liesOver_iff_comap_eq v u).1 hu
  subst e
  rfl

omit [NumberField K] in
/- English proof (translation)
Take `⟨u, hu⟩` from `w`. Take `⟨v, hv⟩` from `v`. Establish `e : below K u = v` using `(below_eq_iff u v).2 hu`. Substitute `e` using the available equality. Rewrite using `[assembleFinite, dif_pos hv]`.
-/
theorem assembleFinite_eq_of_mem (p : SIdelesProduct L S) (v : S) (w : PlacesOver L v.1) :
    assembleFinite p w.1 = p.2.1 v w := by
  obtain ⟨u, hu⟩ := w
  obtain ⟨v, hv⟩ := v
  have e : below K u = v := (below_eq_iff u v).2 hu
  subst e
  rw [assembleFinite, dif_pos hv]

omit [NumberField K] in
/- English proof (translation)
Take `⟨u, hu⟩` from `w`. Take `⟨v, hv⟩` from `v`. Establish `e : below K u = v` using `(below_eq_iff u v).2 hu`. Substitute `e` using the available equality. Rewrite using `[assembleFinite, dif_neg hv]`.
-/
theorem assembleFinite_eq_of_not_mem (p : SIdelesProduct L S) (v : ↥Sᶜ) (w : PlacesOver L v.1) :
    assembleFinite p w.1 = integerUnitsAboveIncl v.1 (p.2.2 v) w := by
  obtain ⟨u, hu⟩ := w
  obtain ⟨v, hv⟩ := v
  have e : below K u = v := (below_eq_iff u v).2 hu
  subst e
  rw [assembleFinite, dif_neg hv]

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[assembleFinite_eq_of_not_mem p ⟨below K u, hu⟩ ⟨u, inferInstance⟩]`. Conclude with `(mem_range_integerUnitsAboveIncl_iff (below K u) _).1 ⟨_, rfl⟩ ⟨u, inferInstance⟩`.
-/
theorem assembleFinite_mem (p : SIdelesProduct L S) {u : HeightOneSpectrum (𝓞 L)}
    (hu : u ∉ placesAbove L S) :
    (assembleFinite p u : u.adicCompletion L) ∈ u.adicCompletionIntegers L ∧
      ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val ∈ u.adicCompletionIntegers L := by
  rw [assembleFinite_eq_of_not_mem p ⟨below K u, hu⟩ ⟨u, inferInstance⟩]
  exact (mem_range_integerUnitsAboveIncl_iff (below K u) _).1 ⟨_, rfl⟩ ⟨u, inferInstance⟩

/- English proof (translation)
The claim follows from `Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦ Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).1)`.
-/
theorem assembleFinite_eventually (hS : S.Finite) (p : SIdelesProduct L S) :
    ∀ᶠ u in Filter.cofinite,
      (assembleFinite p u : u.adicCompletion L) ∈ u.adicCompletionIntegers L :=
  Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦
    Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).1)

/- English proof (translation)
The claim follows from `Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦ Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).2)`.
-/
theorem assembleFinite_inv_eventually (hS : S.Finite) (p : SIdelesProduct L S) :
    ∀ᶠ u in Filter.cofinite,
      ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val ∈ u.adicCompletionIntegers L :=
  Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦
    Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).2)

def assemble (hS : S.Finite) (p : SIdelesProduct L S) : IdeleGroup L where
  val := ((fun u ↦ (assembleInfinite p u : u.Completion) : (u : InfinitePlace L) → u.Completion),
    (⟨fun u ↦ (assembleFinite p u : u.adicCompletion L), assembleFinite_eventually hS p⟩ :
      Πʳ u : HeightOneSpectrum (𝓞 L), [u.adicCompletion L, u.adicCompletionIntegers L]))
  inv := ((fun u ↦ ((assembleInfinite p u)⁻¹ : (u.Completion)ˣ).val :
      (u : InfinitePlace L) → u.Completion),
    (⟨fun u ↦ ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val,
        assembleFinite_inv_eventually hS p⟩ :
      Πʳ u : HeightOneSpectrum (𝓞 L), [u.adicCompletion L, u.adicCompletionIntegers L]))
  val_inv := adele_ext (funext fun u ↦ (assembleInfinite p u).mul_inv)
    fun u ↦ (assembleFinite p u).mul_inv
  inv_val := adele_ext (funext fun u ↦ (assembleInfinite p u).inv_mul)
    fun u ↦ (assembleFinite p u).inv_mul

/- English proof (translation)
The claim follows from `fun u hu ↦ (ord_eq_zero_iff u _).2 (assembleFinite_mem p hu)`.
-/
theorem assemble_mem (hS : S.Finite) (p : SIdelesProduct L S) :
    assemble hS p ∈ sIdeles (placesAbove L S) :=
  fun u hu ↦ (ord_eq_zero_iff u _).2 (assembleFinite_mem p hu)

/- English proof (translation)
Use `Prod.ext (funext fun v ↦ funext fun w ↦ ?_) (Prod.ext (funext fun v ↦ funext fun w ↦ ?_) (funext fun v ↦ ?_))` and prove the remaining obligations. Conclude with `Units.ext (congrArg Units.val (assembleInfinite_eq p v w))`. Conclude with `Units.ext (congrArg Units.val (assembleFinite_eq_of_mem p v w))`. Apply `integerUnitsAboveIncl_injective v.1` to reduce the goal to its premises. Rewrite using `[sIdelesToProduct_snd_snd, integerUnitsAboveIncl_sIdelesIntegerPart]`.

Use function extensionality and compare the values at `w`. Conclude with `Units.ext (congrArg Units.val (assembleFinite_eq_of_not_mem p v w))`.
-/
theorem sIdelesToProduct_assemble (hS : S.Finite) (p : SIdelesProduct L S) :
    sIdelesToProduct S ⟨assemble hS p, assemble_mem hS p⟩ = p := by
  refine Prod.ext (funext fun v ↦ funext fun w ↦ ?_)
    (Prod.ext (funext fun v ↦ funext fun w ↦ ?_) (funext fun v ↦ ?_))
  · exact Units.ext (congrArg Units.val (assembleInfinite_eq p v w))
  · exact Units.ext (congrArg Units.val (assembleFinite_eq_of_mem p v w))
  · apply integerUnitsAboveIncl_injective v.1
    rw [sIdelesToProduct_snd_snd, integerUnitsAboveIncl_sIdelesIntegerPart]
    funext w
    exact Units.ext (congrArg Units.val (assembleFinite_eq_of_not_mem p v w))

variable (S)

/- English proof (translation)
The claim follows from `fun p ↦ ⟨⟨assemble hS p, assemble_mem hS p⟩, sIdelesToProduct_assemble hS p⟩`.
-/
theorem sIdelesToProduct_surjective (hS : S.Finite) :
    Function.Surjective (sIdelesToProduct (L := L) S) :=
  fun p ↦ ⟨⟨assemble hS p, assemble_mem hS p⟩, sIdelesToProduct_assemble hS p⟩

def sIdelesEquivProduct (hS : S.Finite) : sIdeles (placesAbove L S) ≃* SIdelesProduct L S :=
  MulEquiv.ofBijective (sIdelesToProduct S)
    ⟨sIdelesToProduct_injective S, sIdelesToProduct_surjective S hS⟩

/- English proof (translation)
The claim follows from `sIdelesToProduct_smul S σ x`.
-/
theorem sIdelesEquivProduct_smul (hS : S.Finite) (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesEquivProduct S hS (σ • x) = σ • sIdelesEquivProduct S hS x :=
  sIdelesToProduct_smul S σ x

end IdeleGroup

end

end GroundTheory.Global
