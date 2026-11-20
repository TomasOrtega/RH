import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

/- English proof (translation)
Establish `hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y` using `fun y ↦ by`. Rewrite using `[Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]`. Establish `hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R)`. Rewrite using `[IsSMulRegular.subsingleton_linearMap_iff]`. Introduce and unpack `⟨r, hr, hreg⟩`.

Use `h r ?_ hreg` and prove the remaining obligations. Establish `h1` using `Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)`. Rewrite `h1` using `[hmk, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Rewrite `hns` using `[not_subsingleton_iff_nontrivial]`. Take `⟨f, hf⟩` from `exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)`.

Use `⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]`. Rewrite using `[← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]`.
-/
theorem exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by
  have hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y := fun y ↦ by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    rintro ⟨r, hr, hreg⟩
    refine h r ?_ hreg
    have h1 := Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)
    rwa [hmk, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨f, hf⟩ := exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)
  refine ⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
  · rw [← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/- English proof (translation)
Take `⟨s, hs, hms⟩` from `exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h`. Establish `: Module.Free R M` using `GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM`. Conclude with `(projective_iff_hasProjectiveDimensionLE_zero _).mp (by`. Rewrite using `[← IsProjective.iff_projective]`. Use the proof step `infer_instance)`.
-/
theorem hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  obtain ⟨s, hs, hms⟩ := exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h
  have : Module.Free R M := GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (by
    rw [← IsProjective.iff_projective]; infer_instance)

/- English proof (translation)
Establish `hne : span {x} ≠ ⊤` using `fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))`. Establish `: Nontrivial (R ⧸ span {x})` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `: IsLocalRing (R ⧸ span {x})` using `.of_surjective' _ Ideal.Quotient.mk_surjective`. Proceed by induction on `k generalizing M with`. Consider the case `zero`.

Rewrite `hM`, the goal using `[zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]`. Establish `: Module.Finite (R ⧸ span {x}) (QuotSMulTop x M)` using `Module.Finite.of_restrictScalars_finite R _ _`. Establish `hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M)` using `Module.free_of_flat_of_isLocalRing`. Use `Module.finitePresentation_of_finite R M` as an intermediate fact. Establish `: Module.Free R M` using `(Module.free_quotSMulTop_iff_free R M (IsLocalRing.maximalIdeal_le_jacobson _ hx) hxM).mp hfree`.

Use `infer_instance`. Consider the case `succ k ih`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Set `K` to `LinearMap.ker π`. Establish `hS` using `LinearMap.shortExact_shortComplexKer hπ`.

Establish `hproj : Projective (π.shortComplexKer).X₂`. Rewrite using `[← IsProjective.iff_projective]`. Use `infer_instance`. Establish `hxF : IsSMulRegular (Fin n → R) x`. Introduce `a b h`.

Use function extensionality and compare the values at `i`. Conclude with `hxR (congrFun h i)`. Establish `hxK : IsSMulRegular K x` using `fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))`. Set `f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R)` to `QuotSMulTop.map x K.subtype`. Set `f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M` to `QuotSMulTop.map x π`.

Establish `hex0 : Function.Exact K.subtype π` using `fun y ↦ ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩`. Establish `ex : Function.Exact f₁ f₂` using `QuotSMulTop.map_exact x hex0 hπ`. Establish `surj : Function.Surjective f₂` using `QuotSMulTop.map_surjective x hπ`. Establish `inj : Function.Injective f₁`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `y hy`. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ y`. Rewrite `hy` using `[LinearMap.mem_ker]`. Simplify using `only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hy`. Take `⟨b, -, hb⟩` from `hy`.

Establish `hπb : π b = 0`. Apply `hxM` to reduce the goal to its premises. Use `show x • π b = x • 0`. Rewrite using `[← map_smul, hb, smul_zero]`. Conclude with `y.2`.

Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]`. Conclude with `⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩`. Set `g₁` to `f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))`. Set `g₂` to `f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))`. Set `T` to `ModuleCat.shortComplexOfCompEqZero g₁ g₂ (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)`.

Establish `hT : T.ShortExact` using `ModuleCat.shortComplex_shortExact T ex inj surj`. Establish `hproj2 : Projective T.X₂`. Rewrite using `[← IsProjective.iff_projective]`. Use `infer_instance`. Establish `hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1)` using `(hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM`.

Conclude with `(hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')`.
-/
theorem hasProjectiveDimensionLT_of_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
    have := Module.finitePresentation_of_finite R M
    have : Module.Free R M :=
      (Module.free_quotSMulTop_iff_free R M (IsLocalRing.maximalIdeal_le_jacobson _ hx) hxM).mp hfree
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1) :=
      (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM
    exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')

/- English proof (translation)
Set `lift : R ⧸ span {x} → R` to `Function.surjInv Ideal.Quotient.mk_surjective`. Establish `hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b` using `Function.surjInv_eq Ideal.Quotient.mk_surjective`. Establish `hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs`. Rewrite using `[List.map_map]`. Use `conv_rhs => rw [← List.map_id rs]`.

Conclude with `List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]`. Establish `hloc : IsLocalHom (Ideal.Quotient.mk (span {x}))` using `IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) = maximalIdeal R` using `IsLocalRing.maximalIdeal_comap _`. Establish `hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R`. Introduce `r hr`.

Break down `List.mem_cons.mp hr with rfl | hr` into its components or cases. Conclude with `hx`. Take `⟨b, hb, rfl⟩` from `List.mem_map.mp hr`. Rewrite using `[← hcomap, Ideal.mem_comap, hlift]`. Conclude with `hrs b hb`.

Establish `e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R` using `Submodule.quotEquivOfEq _ _ (by`. Rewrite using `[← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])`. Establish `hreg' : IsWeaklyRegular R (x :: rs.map lift)`. Rewrite using `[isWeaklyRegular_cons_iff]`. Use `⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩` and prove the remaining obligations.

Rewrite using `[← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']`. Conclude with `hreg`. Use `hd _ hmem hreg'` as an intermediate fact. Simplify using `only [List.length_cons, List.length_map] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem length_le_of_isWeaklyRegular_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs]
    exact List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      rw [← hcomap, Ideal.mem_comap, hlift]
      exact hrs b hb
  have e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have hreg' : IsWeaklyRegular R (x :: rs.map lift) := by
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']
    exact hreg
  have := hd _ hmem hreg'
  simp only [List.length_cons, List.length_map] at this
  omega

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `R _ _ _ hd M _ _ _ k hM`. Use `hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM` and prove the remaining obligations. Use `hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')` as an intermediate fact.

Simplify using `at this`. Consider the case `succ d ih`. Introduce `R _ _ _ hd M _ _ _ k hM`. Distinguish the cases in `hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y`. Use `swap`.

Use `push Not at hex`. Use `hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM` as an intermediate fact. Conclude with `hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)`. Take `⟨x, hx, hxR⟩` from `hex`. Establish `hne : span {x} ≠ ⊤` using `fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))`.

Establish `: Nontrivial (R ⧸ span {x})` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `: IsLocalRing (R ⧸ span {x})` using `.of_surjective' _ Ideal.Quotient.mk_surjective`. Establish `hd'` using `length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Set `K` to `LinearMap.ker π`.

Establish `hS` using `LinearMap.shortExact_shortComplexKer hπ`. Establish `hproj : Projective (π.shortComplexKer).X₂`. Rewrite using `[← IsProjective.iff_projective]`. Use `infer_instance`. Establish `hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1)` using `(hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))`.

Establish `hxF : IsSMulRegular (Fin n → R) x`. Introduce `a b h`. Use function extensionality and compare the values at `i`. Conclude with `hxR (congrFun h i)`. Establish `hxK : IsSMulRegular K x` using `fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))`.

Establish `hKx` using `GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK`. Establish `: Module.Finite (R ⧸ span {x}) (QuotSMulTop x K)` using `Module.Finite.of_restrictScalars_finite R _ _`. Establish `hKx'` using `ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx`. Establish `hK2` using `hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'`. Conclude with `(hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2`.
-/
theorem hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _ _ _ k hM
    refine hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM
    have := hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')
    simp at this
  | succ d ih =>
    intro R _ _ _ hd M _ _ _ k hM
    by_cases hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y
    swap
    · push Not at hex
      have := hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM
      exact hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)
    obtain ⟨x, hx, hxR⟩ := hex
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hd' := length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp
        (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hKx := GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hKx' := ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx
    have hK2 := hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'
    exact (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2

end GroundTheory.Heights₂.Heights
