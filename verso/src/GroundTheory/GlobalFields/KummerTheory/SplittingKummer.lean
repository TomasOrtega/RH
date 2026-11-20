import Mathlib
import GroundTheory.GlobalFields.KummerTheory.Degree
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.GlobalFields.KummerTheory.SplittingInfinite

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct

section Local

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]

omit [NeZero n] [HasEnoughRootsOfUnity K n] [IsScalarTower K F E] in

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [IntermediateField.coe_pow, hy]; rfl)`.
-/
theorem kummerExtension_pow_eq {y : kummerExtension K n Ω Δ} {a : K}
    (hy : (y : Ω) ^ n = algebraMap K Ω a) :
    y ^ n = algebraMap K (kummerExtension K n Ω Δ) a :=
  Subtype.ext (by rw [IntermediateField.coe_pow, hy]; rfl)

/- English proof (translation)
Establish `key : ∀ (y : kummerExtension K n Ω Δ), ∀ a ∈ Δ, (y : Ω) ^ n = algebraMap K Ω (a : K) → ι y ∈ (algebraMap F E).fieldRange`. Introduce `y a ha hy`. Take `⟨x, hx⟩` from `h a ha`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`. Establish `hζ' : IsPrimitiveRoot (algebraMap K E ζ) n` using `hζ.map_of_injective (algebraMap K E).injective`.

Establish `hx0 : algebraMap F E x ≠ 0`. Use `(map_ne_zero _).2 fun hx0 ↦ ?_` and prove the remaining obligations. Rewrite `hx` using `[hx0, zero_pow (NeZero.ne n)]`. Conclude with `a.ne_zero ((algebraMap K F).injective (by rw [← hx, map_zero]))`. Establish `hpow : ι y ^ n = algebraMap F E x ^ n`.

Rewrite using `[← map_pow, kummerExtension_pow_eq hy, ι.commutes, ← map_pow, hx, ← IsScalarTower.algebraMap_apply]`. Establish `hroot : (ι y / algebraMap F E x) ^ n = 1`. Rewrite using `[div_pow, hpow, div_self (pow_ne_zero _ hx0)]`. Take `⟨k, -, hk⟩` from `hζ'.eq_pow_of_pow_eq_one hroot`. Use `⟨algebraMap K F ζ ^ k * x, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0]`. Take `⟨m, hm⟩` from `m`. Proceed by induction on `hm using IntermediateField.adjoin_induction with`. Consider the case `mem α hα`. Take `⟨a, ha, hαa⟩` from `id hα`.

Conclude with `key _ a ha hαa`. Consider the case `algebraMap x`. Use `⟨algebraMap K F x, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `(ι.commutes x).symm`.

Consider the case `add x y hx hy ihx ihy => show ι (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _`. Rewrite using `[map_add]`. Conclude with `add_mem ihx ihy`. Consider the case `inv x hx ih => show ι (⟨x, hx⟩⁻¹) ∈ _`. Rewrite using `[map_inv₀]`.

Conclude with `inv_mem ih`. Consider the case `mul x y hx hy ihx ihy => show ι (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _`. Rewrite using `[map_mul]`. Conclude with `mul_mem ihx ihy`.
-/
theorem algHom_kummerExtension_mem_fieldRange (ι : kummerExtension K n Ω Δ →ₐ[K] E)
    (h : ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K)) (m : kummerExtension K n Ω Δ) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have key : ∀ (y : kummerExtension K n Ω Δ), ∀ a ∈ Δ, (y : Ω) ^ n = algebraMap K Ω (a : K) →
      ι y ∈ (algebraMap F E).fieldRange := by
    intro y a ha hy
    obtain ⟨x, hx⟩ := h a ha
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0 : algebraMap F E x ≠ 0 := by
      refine (map_ne_zero _).2 fun hx0 ↦ ?_
      rw [hx0, zero_pow (NeZero.ne n)] at hx
      exact a.ne_zero ((algebraMap K F).injective (by rw [← hx, map_zero]))
    have hpow : ι y ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, kummerExtension_pow_eq hy, ι.commutes, ← map_pow, hx,
        ← IsScalarTower.algebraMap_apply]
    have hroot : (ι y / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0)]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0]
  obtain ⟨m, hm⟩ := m
  induction hm using IntermediateField.adjoin_induction with
  | mem α hα =>
    obtain ⟨a, ha, hαa⟩ := id hα
    exact key _ a ha hαa
  | algebraMap x =>
    refine ⟨algebraMap K F x, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact (ι.commutes x).symm
  | add x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ih =>
    show ι (⟨x, hx⟩⁻¹) ∈ _
    rw [map_inv₀]
    exact inv_mem ih
  | mul x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
    rw [map_mul]
    exact mul_mem ihx ihy

omit [Algebra K E] [IsScalarTower K F E] in

/- English proof (translation)
Rewrite using `[← Subalgebra.bot_eq_top_iff_finrank_eq_one]`. Use `eq_top_iff.2 fun e he ↦ ?_` and prove the remaining obligations. Use `clear he`. Take `⟨t, rfl⟩` from `hg e`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `tmul c m`. Establish `: c ⊗ₜ[K] m = c • ((1 : F) ⊗ₜ[K] m)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[this, map_smul]`. Conclude with `Subalgebra.smul_mem _ (Algebra.mem_bot.2 (hA m)) c`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.
-/
theorem finrank_eq_one_of_tensor_surjective {A : Type*} [CommRing A] [Algebra K A]
    (g : F ⊗[K] A →ₐ[F] E) (hg : Function.Surjective g)
    (hA : ∀ m : A, g (1 ⊗ₜ m) ∈ (algebraMap F E).fieldRange) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  refine eq_top_iff.2 fun e he ↦ ?_
  clear he
  obtain ⟨t, rfl⟩ := hg e
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c m =>
    have : c ⊗ₜ[K] m = c • ((1 : F) ⊗ₜ[K] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Subalgebra.smul_mem _ (Algebra.mem_bot.2 (hA m)) c
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Set `ι : kummerExtension K n Ω Δ →ₐ[K] E` to `(g.restrictScalars K).comp Algebra.TensorProduct.includeRight`. Prove the components needed by the constructor for the conclusion. Introduce `h1 a ha`. Establish `hsurj : Function.Surjective (algebraMap F E)` using `(Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`.

Establish `hnK : NeZero ((n : ℕ) : K)` using `hζ.neZero'`. Establish `hnΩ : NeZero ((n : ℕ) : Ω)` using `⟨by rw [← map_natCast (algebraMap K Ω)]; exact (map_ne_zero _).2 hnK.out⟩`. Take `⟨α, hα⟩` from `IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) n`. Set `y : kummerExtension K n Ω Δ` to `⟨α, subset_adjoin _ _ ⟨a, ha, hα⟩⟩`. Take `⟨x, hx⟩` from `hsurj (ι y)`.

Use `⟨x, (algebraMap F E).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hx, ← map_pow, kummerExtension_pow_eq (y := y) hα, ι.commutes, ← IsScalarTower.algebraMap_apply]`. Introduce `h`. Conclude with `finrank_eq_one_of_tensor_surjective g hg fun m ↦ algHom_kummerExtension_mem_fieldRange ι h m`.
-/
theorem finrank_eq_one_iff_of_kummerExtension [IsSepClosed Ω]
    (g : F ⊗[K] kummerExtension K n Ω Δ →ₐ[F] E) (hg : Function.Surjective g) :
    finrank F E = 1 ↔ ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  let ι : kummerExtension K n Ω Δ →ₐ[K] E :=
    (g.restrictScalars K).comp Algebra.TensorProduct.includeRight
  constructor
  · intro h1 a ha
    have hsurj : Function.Surjective (algebraMap F E) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hnK : NeZero ((n : ℕ) : K) := hζ.neZero'
    have hnΩ : NeZero ((n : ℕ) : Ω) :=
      ⟨by rw [← map_natCast (algebraMap K Ω)]; exact (map_ne_zero _).2 hnK.out⟩
    obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) n
    let y : kummerExtension K n Ω Δ := ⟨α, subset_adjoin _ _ ⟨a, ha, hα⟩⟩
    obtain ⟨x, hx⟩ := hsurj (ι y)
    refine ⟨x, (algebraMap F E).injective ?_⟩
    rw [map_pow, hx, ← map_pow, kummerExtension_pow_eq (y := y) hα, ι.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro h
    exact finrank_eq_one_of_tensor_surjective g hg fun m ↦
      algHom_kummerExtension_mem_fieldRange ι h m

end Local

section Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

instance numberField_kummerExtension : NumberField (kummerExtension K n Ω Δ) :=
  NumberField.of_module_finite K _

open SemiLocal in

/- English proof (translation)
Establish `key (w : PlacesOver (kummerExtension K n Ω Δ) v)` using `finrank_eq_one_iff_of_kummerExtension ((Pi.evalAlgHom (v.adicCompletion K) _ w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).toAlgHom) ((Function.surjective_eval w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).surjective)`. Rewrite using `[splitsCompletely_iff_forall_finrank]`. Use `⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩` and prove the remaining obligations. Take `⟨w⟩` from `nonempty_placesOver (kummerExtension K n Ω Δ) v`. Conclude with `(key w).1 (h w)`.
-/
theorem splitsCompletely_kummerExtension_iff (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) (a : K) := by
  have key (w : PlacesOver (kummerExtension K n Ω Δ) v) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom (v.adicCompletion K) _ w).comp
        (tensorEquiv (kummerExtension K n Ω Δ) v).toAlgHom)
      ((Function.surjective_eval w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).surjective)
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

open scoped NumberField.LiesOver in

/- English proof (translation)
Establish `key (w : v.placesOver (kummerExtension K n Ω Δ))` using `finrank_eq_one_iff_of_kummerExtension ((Pi.evalAlgHom v.Completion _ w).comp (InfinitePlace.tensorPiHom (L := kummerExtension K n Ω Δ) v)) ((Function.surjective_eval w).comp (InfinitePlace.tensorPiHom_surjective (L := kummerExtension K n Ω Δ) v))`. Rewrite using `[InfinitePlace.splitsCompletely_iff_forall_finrank]`. Use `⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩` and prove the remaining obligations. Take `⟨w⟩` from `InfinitePlace.nonempty_placesOver (kummerExtension K n Ω Δ) v`. Conclude with `(key w).1 (h w)`.
-/
theorem InfinitePlace.splitsCompletely_kummerExtension_iff (v : NumberField.InfinitePlace K) :
    InfinitePlace.SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.Completion, x ^ n = algebraMap K v.Completion (a : K) := by
  have key (w : v.placesOver (kummerExtension K n Ω Δ)) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom v.Completion _ w).comp
        (InfinitePlace.tensorPiHom (L := kummerExtension K n Ω Δ) v))
      ((Function.surjective_eval w).comp
        (InfinitePlace.tensorPiHom_surjective (L := kummerExtension K n Ω Δ) v))
  rw [InfinitePlace.splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := InfinitePlace.nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

end Global

end GroundTheory.Global
