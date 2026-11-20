import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU.SelfDual

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

/- English proof (translation)
Use `Module.IsTorsionFree.trans_faithfulSMul O K V` as an intermediate fact. Establish `: Module.FinitePresentation O L` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective O L` using `Module.Flat.projective_of_finitePresentation`. Establish `: IsLocalizedModule (nonZeroDivisors O) L.subtype` using `{ map_units := fun s => by`. Use `isLocalizedModule_id (nonZeroDivisors O) V K` as an intermediate fact.

Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s`. Use `surj := fun y => by`. Establish `hy : y ∈ Submodule.span K (L : Set V)` using `hL.span_eq_top ▸ Submodule.mem_top`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K _ y hy`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨(⟨_, ht⟩, t), rfl⟩`. Use `exists_of_eq := fun {a b} h => ⟨1, by rw [L.injective_subtype h]⟩ }`. Take `⟨m, π, hπ⟩` from `Module.Finite.exists_fin' O L`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Set `f : Fin m → V →ₗ[K] K` to `fun i => LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K (IsLocalizedModule.lift (nonZeroDivisors O) L.subtype (Algebra.linearMap O K ∘ₗ LinearMap.proj i ∘ₗ s) (IsLocalizedModule.map_units (Algebra.linearMap O K)))`.

Establish `hf : ∀ i (y : L), f i y = algebraMap O K (s y i)` using `fun i y => IsLocalizedModule.lift_apply (nonZeroDivisors O) L.subtype _ (IsLocalizedModule.map_units (Algebra.linearMap O K)) y`. Set `x : Fin m → V` to `fun i => (π (Pi.single i 1) : L)`. Use `⟨m, x, f, fun i => (π (Pi.single i 1)).2, fun y hy i => ⟨_, (hf i ⟨y, hy⟩).symm⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `: (∑ i, (f i).smulRight (x i)) = LinearMap.id`. Apply `LinearMap.ext_on hL.span_eq_top` to reduce the goal to its premises.

Introduce `y hy`. Establish `h1 : π (s ⟨y, hy⟩) = ⟨y, hy⟩` using `LinearMap.congr_fun hs ⟨y, hy⟩`. Establish `h2 : (π (s ⟨y, hy⟩) : V) = y` using `by rw [h1]`. Rewrite `h2` using `[pi_eq_sum_univ' (s ⟨y, hy⟩)]`. Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h2`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2` and prove the remaining obligations. Rewrite using `[hf i ⟨y, hy⟩, algebraMap_smul]`. Simplify using `using LinearMap.congr_fun this y`.
-/
theorem exists_dualFamily_of_isLattice {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (L : Submodule O V) (hL : Submodule.IsLattice K L) :
    ∃ (k : ℕ) (s : Fin k → V) (φ : Fin k → V →ₗ[K] K), (∀ j, s j ∈ L) ∧
      (∀ x ∈ L, ∀ j, φ j x ∈ (algebraMap O K).range) ∧ ∀ x, ∑ j, φ j x • s j = x := by
  have := Module.IsTorsionFree.trans_faithfulSMul O K V
  have : Module.FinitePresentation O L := Module.finitePresentation_of_finite _ _
  have : Module.Projective O L := Module.Flat.projective_of_finitePresentation
  have : IsLocalizedModule (nonZeroDivisors O) L.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (nonZeroDivisors O) V K
        exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
      surj := fun y => by
        have hy : y ∈ Submodule.span K (L : Set V) := hL.span_eq_top ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun {a b} h => ⟨1, by rw [L.injective_subtype h]⟩ }
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' O L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let f : Fin m → V →ₗ[K] K := fun i =>
    LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) L.subtype
        (Algebra.linearMap O K ∘ₗ LinearMap.proj i ∘ₗ s) (IsLocalizedModule.map_units (Algebra.linearMap O K)))
  have hf : ∀ i (y : L), f i y = algebraMap O K (s y i) := fun i y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) L.subtype _ (IsLocalizedModule.map_units (Algebra.linearMap O K)) y
  let x : Fin m → V := fun i => (π (Pi.single i 1) : L)
  refine ⟨m, x, f, fun i => (π (Pi.single i 1)).2, fun y hy i => ⟨_, (hf i ⟨y, hy⟩).symm⟩, fun y => ?_⟩
  have : (∑ i, (f i).smulRight (x i)) = LinearMap.id := by
    apply LinearMap.ext_on hL.span_eq_top
    intro y hy
    have h1 : π (s ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hs ⟨y, hy⟩
    have h2 : (π (s ⟨y, hy⟩) : V) = y := by rw [h1]
    rw [pi_eq_sum_univ' (s ⟨y, hy⟩)] at h2
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
    rw [hf i ⟨y, hy⟩, algebraMap_smul]
  simpa using LinearMap.congr_fun this y

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨N, hN, h⟩` from `exists_integral_multiples ℤ ℚ ({e} : Finset E)`. Use `replace h := h e (Finset.mem_singleton_self e)`. Establish `h0 : ((N : 𝓞 F) : F) ≠ 0` using `by simpa using hN`. Use `⟨N, ⟨N • e, h⟩, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_inv_smul_iff₀ h0]`.

Simplify using `[Algebra.smul_def]`.
-/
theorem exists_den (e : E) : ∃ (N : 𝓞 F) (x : 𝓞 E), (N : F) ≠ 0 ∧ e = (N : F)⁻¹ • (x : E) := by
  obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
  replace h := h e (Finset.mem_singleton_self e)
  have h0 : ((N : 𝓞 F) : F) ≠ 0 := by simpa using hN
  refine ⟨N, ⟨N • e, h⟩, h0, ?_⟩
  rw [eq_inv_smul_iff₀ h0]
  simp [Algebra.smul_def]

/- English proof (translation)
Set `M : Submodule (𝓞 F) E` to `LinearMap.range (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E).toLinearMap`. Establish `hM : Submodule.IsLattice F M`. Use `⟨Submodule.fg_range _, eq_top_iff.2 fun y _ => ?_⟩` and prove the remaining obligations. Take `⟨N, x, -, rfl⟩` from `exists_den (F := F) y`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`.

Take `⟨k, s, φ, hs, hφ, hsum⟩` from `exists_dualFamily_of_isLattice M hM`. Use `choose t ht using hs`. Conclude with `⟨k, t, φ, fun x j => hφ x ⟨x, rfl⟩ j, fun x => (Finset.sum_congr rfl fun j _ => by rw [← ht j]; rfl).trans (hsum x)⟩`.
-/
theorem exists_dualFamily_integers :
    ∃ (k : ℕ) (s : Fin k → 𝓞 E) (φ : Fin k → E →ₗ[F] F),
      (∀ (x : 𝓞 E) j, φ j x ∈ (algebraMap (𝓞 F) F).range) ∧ ∀ x, ∑ j, φ j x • (s j : E) = x := by
  let M : Submodule (𝓞 F) E := LinearMap.range (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E).toLinearMap
  have hM : Submodule.IsLattice F M := by
    refine ⟨Submodule.fg_range _, eq_top_iff.2 fun y _ => ?_⟩
    obtain ⟨N, x, -, rfl⟩ := exists_den (F := F) y
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  obtain ⟨k, s, φ, hs, hφ, hsum⟩ := exists_dualFamily_of_isLattice M hM
  choose t ht using hs
  exact ⟨k, t, φ, fun x j => hφ x ⟨x, rfl⟩ j, fun x =>
    (Finset.sum_congr rfl fun j _ => by rw [← ht j]; rfl).trans (hsum x)⟩

omit [NumberField E] in
/- English proof (translation)
Take `⟨P, hP0⟩ : ∃ P : Fv F v ⊗[F] E →ₗ[F] Fv F v, ∀ a x, P (a ⊗ₜ x) = algebraMap F _ (φ x) * a` from `⟨(TensorProduct.rid F (Fv F v)).toLinearMap ∘ₗ φ.lTensor (Fv F v), fun a x => by simp [Algebra.smul_def]⟩`. Establish `hP : ∀ z ∈ intLoc F E v, P z ∈ v.adicCompletionIntegers F` using `fun z hz => by`. Use `intLoc_induction (p := fun z => P z ∈ v.adicCompletionIntegers F) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hz` and prove the remaining obligations. Take `⟨r, hr⟩` from `hφ x`. Rewrite using `[hP0, ← hr]`.

Conclude with `mul_mem (v.coe_mem_adicCompletionIntegers r) ha`. Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Rewrite using `[map_add]`. Conclude with `add_mem hy hz`.

Rewrite using `[map_neg]`. Conclude with `neg_mem hy`. Establish `h1 : P ((1 : Fv F v) ⊗ₜ e) ∈ v.adicCompletionIntegers F` using `hP _ h`. Rewrite `h1` using `[hP0, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `h1`.
-/
theorem valuation_le_one_of_intLoc {v : HeightOneSpectrum (𝓞 F)} (φ : E →ₗ[F] F)
    (hφ : ∀ x : 𝓞 E, φ x ∈ (algebraMap (𝓞 F) F).range) {e : E} (h : inclR (Fv F v) e ∈ intLoc F E v) :
    v.valuation F (φ e) ≤ 1 := by
  obtain ⟨P, hP0⟩ : ∃ P : Fv F v ⊗[F] E →ₗ[F] Fv F v, ∀ a x, P (a ⊗ₜ x) = algebraMap F _ (φ x) * a :=
    ⟨(TensorProduct.rid F (Fv F v)).toLinearMap ∘ₗ φ.lTensor (Fv F v), fun a x => by simp [Algebra.smul_def]⟩
  have hP : ∀ z ∈ intLoc F E v, P z ∈ v.adicCompletionIntegers F := fun z hz => by
    refine intLoc_induction (p := fun z => P z ∈ v.adicCompletionIntegers F) (fun a ha x => ?_) ?_
        (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · obtain ⟨r, hr⟩ := hφ x
      rw [hP0, ← hr]
      exact mul_mem (v.coe_mem_adicCompletionIntegers r) ha
    · rw [map_zero]; exact zero_mem _
    · rw [map_add]; exact add_mem hy hz
    · rw [map_neg]; exact neg_mem hy
  have h1 : P ((1 : Fv F v) ⊗ₜ e) ∈ v.adicCompletionIntegers F := hP _ h
  rw [hP0, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers] at h1
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h1

/- English proof (translation)
Take `⟨k, s, φ, hφ, hsum⟩` from `exists_dualFamily_integers (F := F) (E := E)`. Rewrite using `[← hsum e]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (φ j e) fun v => valuation_le_one_of_intLoc (φ j) (hφ · j) (h v)`. Conclude with `⟨algebraMap (𝓞 F) (𝓞 E) r * s j, by rw [← hr, Algebra.smul_def, map_mul]; rfl⟩`.
-/
theorem mem_range_of_forall_intLoc {e : E}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), inclR (Fv F v) e ∈ intLoc F E v) : e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := exists_dualFamily_integers (F := F) (E := E)
  rw [← hsum e]
  refine sum_mem fun j _ => ?_
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (φ j e) fun v =>
    valuation_le_one_of_intLoc (φ j) (hφ · j) (h v)
  exact ⟨algebraMap (𝓞 F) (𝓞 E) r * s j, by rw [← hr, Algebra.smul_def, map_mul]; rfl⟩

omit [NumberField E] in
/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Conclude with `tmul_mem_intLoc (one_mem _) r`.
-/
theorem inclR_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) {e : E} (h : e ∈ (algebraMap (𝓞 E) E).range) :
    inclR (Fv F v) e ∈ intLoc F E v := by
  obtain ⟨r, rfl⟩ := h
  exact tmul_mem_intLoc (one_mem _) r

/- English proof (translation)
Take `⟨N, x, -, rfl⟩` from `exists_den (F := F) e`. Use `filter_upwards [(algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹).2] with v hv`. Establish `: inclR (Fv F v) ((N : F)⁻¹ • (x : E)) = algebraMap F (Fv F v) (N : F)⁻¹ ⊗ₜ[F] (x : E)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `tmul_mem_intLoc hv x`.
-/
theorem eventually_mem_intLoc (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, inclR (Fv F v) e ∈ intLoc F E v := by
  obtain ⟨N, x, -, rfl⟩ := exists_den (F := F) e
  filter_upwards [(algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹).2] with v hv
  have : inclR (Fv F v) ((N : F)⁻¹ • (x : E)) = algebraMap F (Fv F v) (N : F)⁻¹ ⊗ₜ[F] (x : E) := by
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]; rfl
  rw [this]
  exact tmul_mem_intLoc hv x

variable {n : ℕ}

/- English proof (translation)
Take `⟨k, s, φ, hs, hφ, hsum⟩` from `exists_dualFamily_of_isLattice L hL`. Use `⟨k, Matrix.of fun i j => s j i, Matrix.of fun j i => φ j (Pi.single i 1), ?_, hs, fun x hx j => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Use `congrFun (hsum (Pi.single b 1)) a` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, mul_comm]`.

Use `hφ x hx j using 1 conv_rhs => rw [pi_eq_sum_univ' x]` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem exists_frame (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    ∃ (k : ℕ) (S : Matrix (Fin n) (Fin k) E) (Φ : Matrix (Fin k) (Fin n) E), S * Φ = 1 ∧ (∀ j, (fun i => S i j) ∈ L) ∧
      ∀ x ∈ L, ∀ j, (Φ *ᵥ x) j ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨k, s, φ, hs, hφ, hsum⟩ := exists_dualFamily_of_isLattice L hL
  refine ⟨k, Matrix.of fun i j => s j i, Matrix.of fun j i => φ j (Pi.single i 1), ?_, hs, fun x hx j => ?_⟩
  · ext a b
    have := congrFun (hsum (Pi.single b 1)) a
    simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, mul_comm] using this
  · convert hφ x hx j using 1
    conv_rhs => rw [pi_eq_sum_univ' x]
    simp [Matrix.mulVec, dotProduct, mul_comm]

section Frame

omit [NumberField E]

variable {L : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} {S : Matrix (Fin n) (Fin k) E} {Φ : Matrix (Fin k) (Fin n) E}

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.one_mulVec y, ← h1, ← Matrix.mulVec_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem eq_sum_col {A : Type} [CommRing A] {S : Matrix (Fin n) (Fin k) A} {Φ : Matrix (Fin k) (Fin n) A}
    (h1 : S * Φ = 1) (y : Fin n → A) : y = ∑ j, (Φ *ᵥ y) j • fun i => S i j := by
  conv_lhs => rw [← Matrix.one_mulVec y, ← h1, ← Matrix.mulVec_mulVec]
  funext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

omit [NumberField F] in
/- English proof (translation)
Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_mul_eq_one (R : Type) [CommRing R] [Algebra F R] (h1 : S * Φ = 1) :
    S.map (inclR (F := F) R) * Φ.map (inclR (F := F) R) = 1 := by
  rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Use `⟨hΦ y, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sum_col h1 y]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `h j`. Rewrite using `[← hr]`.

Conclude with `L.smul_mem r (hS j)`.
-/
theorem mem_iff_of_frame (h1 : S * Φ = 1) (hS : ∀ j, (fun i => S i j) ∈ L)
    (hΦ : ∀ x ∈ L, ∀ j, (Φ *ᵥ x) j ∈ (algebraMap (𝓞 E) E).range) (y : Fin n → E) :
    y ∈ L ↔ ∀ j, (Φ *ᵥ y) j ∈ (algebraMap (𝓞 E) E).range := by
  refine ⟨hΦ y, fun h => ?_⟩
  rw [eq_sum_col h1 y]
  refine sum_mem fun j _ => ?_
  obtain ⟨r, hr⟩ := h j
  rw [← hr]
  exact L.smul_mem r (hS j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `latLoc_induction (p := fun y => ∀ j, (Φ.map (inclR (Fv F v)) *ᵥ y) j ∈ intLoc F E v) (fun a ha x hx j => ?_) (fun j => ?_) (fun y z hy hz j => ?_) (fun y hy j => ?_)` and prove the remaining obligations. Take `⟨r, hr⟩` from `hΦ x hx j`. Establish `: (Φ.map (inclR (Fv F v)) *ᵥ fun i => a ⊗ₜ[F] x i) j = a ⊗ₜ[F] (Φ *ᵥ x) j`. Simplify using `[Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]`.

Rewrite using `[this, ← hr]`. Conclude with `tmul_mem_intLoc ha r`. Rewrite using `[Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Rewrite using `[Matrix.mulVec_add]`.

Conclude with `add_mem (hy j) (hz j)`. Rewrite using `[Matrix.mulVec_neg]`. Conclude with `neg_mem (hy j)`. Introduce `h`. Rewrite using `[eq_sum_col (map_mul_eq_one (F := F) (Fv F v) h1) y]`.

Conclude with `sum_mem fun j _ => (latLoc F L v).smul_mem ⟨_, h j⟩ (tmul_mem_latLoc (one_mem _) (hS j))`.
-/
theorem mem_latLoc_iff_of_frame (h1 : S * Φ = 1) (hS : ∀ j, (fun i => S i j) ∈ L)
    (hΦ : ∀ x ∈ L, ∀ j, (Φ *ᵥ x) j ∈ (algebraMap (𝓞 E) E).range) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ ∀ j, (Φ.map (inclR (Fv F v)) *ᵥ y) j ∈ intLoc F E v := by
  constructor
  · refine latLoc_induction (p := fun y => ∀ j, (Φ.map (inclR (Fv F v)) *ᵥ y) j ∈ intLoc F E v)
      (fun a ha x hx j => ?_) (fun j => ?_) (fun y z hy hz j => ?_) (fun y hy j => ?_)
    · obtain ⟨r, hr⟩ := hΦ x hx j
      have : (Φ.map (inclR (Fv F v)) *ᵥ fun i => a ⊗ₜ[F] x i) j = a ⊗ₜ[F] (Φ *ᵥ x) j := by
        simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]
      rw [this, ← hr]
      exact tmul_mem_intLoc ha r
    · rw [Matrix.mulVec_zero]; exact zero_mem _
    · rw [Matrix.mulVec_add]; exact add_mem (hy j) (hz j)
    · rw [Matrix.mulVec_neg]; exact neg_mem (hy j)
  · intro h
    rw [eq_sum_col (map_mul_eq_one (F := F) (Fv F v) h1) y]
    exact sum_mem fun j _ => (latLoc F L v).smul_mem ⟨_, h j⟩ (tmul_mem_latLoc (one_mem _) (hS j))

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.one_mulVec x, ← h1, ← Matrix.mulVec_mulVec]`. Generalize the expression as in `Φ *ᵥ x = u`. Simplify using `only [hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring`.
-/
theorem hform_eq_sum {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    {S : Matrix (Fin n) (Fin k) A} {Φ : Matrix (Fin k) (Fin n) A} (h1 : S * Φ = 1) (x y : Fin n → A) :
    hform σ J x y = ∑ j, σ ((Φ *ᵥ x) j) * (((S.map σ)ᵀ * J) *ᵥ y) j := by
  conv_lhs => rw [← Matrix.one_mulVec x, ← h1, ← Matrix.mulVec_mulVec]
  generalize Φ *ᵥ x = u
  simp only [hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring

/- English proof (translation)
Simplify using `only [hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem hform_col {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (S : Matrix (Fin n) (Fin k) A) (j : Fin k) (y : Fin n → A) :
    hform σ J (fun i => S i j) y = (((S.map σ)ᵀ * J) *ᵥ y) j := by
  simp only [hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

end Frame

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Conclude with `⟨RingOfIntegers.mapRingHom (σ : E →+* E) r, rfl⟩`.
-/
theorem sig_mem_range {e : E} (h : e ∈ (algebraMap (𝓞 E) E).range) : σ e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingHom (σ : E →+* E) r, rfl⟩

def dualGlob (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range}
  zero_mem' := fun x _ => by simp [hE, hform]
  add_mem' := fun {y y'} hy hy' x hx => by
    have : hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by simp [hE, hform, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem (hy x hx) (hy' x hx)
  smul_mem' := fun c y hy x hx => by
    have : hE σ J x (c • y) = algebraMap (𝓞 E) E c * hE σ J x y := by
      simp only [hE, hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem ⟨c, rfl⟩ (hy x hx)

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dualGlob {L : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ dualGlob σ J L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

section DualFrame

omit [NumberField E]

variable {σ J} {L : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} {S : Matrix (Fin n) (Fin k) E}
  {Φ : Matrix (Fin k) (Fin n) E}

omit [NumberField F] in
/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc _ _ J, ← Matrix.transpose_mul, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ)]`.
-/
theorem dual_mul_eq_one (hJ : J.det ≠ 0) (h1 : S * Φ = 1) :
    (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) * ((S.map (σ : E →+* E))ᵀ * J) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ J, ← Matrix.transpose_mul, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
    Matrix.nonsing_inv_mul _ (Ne.isUnit hJ)]

omit [NumberField F] in
/- English proof (translation)
Introduce `x hx` and use `by have h2 : ∀ a, ∑ b, J a b * (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) b j = σ (Φ j a) := fun a => by rw [← Matrix.mul_apply, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul]; rfl have : hE σ J x (fun i => (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) i j) = σ ((Φ *ᵥ x) j) := …`.
-/
theorem dual_col_mem (hJ : J.det ≠ 0) (hΦ : ∀ x ∈ L, ∀ j, (Φ *ᵥ x) j ∈ (algebraMap (𝓞 E) E).range) (j : Fin k) :
    (fun i => (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) i j) ∈ dualGlob σ J L := fun x hx => by
  have h2 : ∀ a, ∑ b, J a b * (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) b j = σ (Φ j a) := fun a => by
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul]; rfl
  have : hE σ J x (fun i => (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) i j) = σ ((Φ *ᵥ x) j) := by
    simp only [hE, hform, mul_assoc, ← Finset.mul_sum, h2]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [this]
  exact sig_mem_range σ (hΦ x hx j)

omit [NumberField F] in
/- English proof (translation)
Rewrite using `[← hform_col]`. Conclude with `hy _ (hS j)`.
-/
theorem dual_integral (hS : ∀ j, (fun i => S i j) ∈ L) (y : Fin n → E) (hy : y ∈ dualGlob σ J L) (j : Fin k) :
    (((S.map (σ : E →+* E))ᵀ * J) *ᵥ y) j ∈ (algebraMap (𝓞 E) E).range := by
  rw [← hform_col]
  exact hy _ (hS j)

/- English proof (translation)
Establish `e : ((S.map (σ : E →+* E))ᵀ * J).map (inclR (F` using `F) (Fv F v)) = ((((S.map (inclR (F := F) (Fv F v))).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ))ᵀ : Matrix (Fin k) (Fin n) (Fv F v ⊗[F] E)) * (JR (F := F) (Fv F v) J : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin k) (Fin n) (Fv F v ⊗[F …`. Rewrite using `[Matrix.map_mul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Rewrite using `[← hform_col]`. Conclude with `h _ (tmul_mem_latLoc (one_mem _) (hS j))`. Introduce `h x hx`. Express the relevant statement in the definitionally equal form `hform _ _ x y ∈ _`.

Rewrite using `[hform_eq_sum _ _ (map_mul_eq_one (F := F) (Fv F v) h1)]`. Conclude with `sum_mem fun j _ => mul_mem (sigR_mem_intLoc σ ((mem_latLoc_iff_of_frame h1 hS hΦ v x).1 hx j)) (h j)`.
-/
theorem mem_dualLoc_iff_of_frame (h1 : S * Φ = 1) (hS : ∀ j, (fun i => S i j) ∈ L)
    (hΦ : ∀ x ∈ L, ∀ j, (Φ *ᵥ x) j ∈ (algebraMap (𝓞 E) E).range) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ dualLoc σ J L v ↔ ∀ j, (((S.map (σ : E →+* E))ᵀ * J).map (inclR (Fv F v)) *ᵥ y) j ∈ intLoc F E v := by
  have e : ((S.map (σ : E →+* E))ᵀ * J).map (inclR (F := F) (Fv F v)) =
      ((((S.map (inclR (F := F) (Fv F v))).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ))ᵀ :
        Matrix (Fin k) (Fin n) (Fv F v ⊗[F] E)) * (JR (F := F) (Fv F v) J : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin k) (Fin n) (Fv F v ⊗[F] E)) := by
    rw [Matrix.map_mul]; rfl
  rw [e]
  constructor
  · intro h j
    rw [← hform_col]
    exact h _ (tmul_mem_latLoc (one_mem _) (hS j))
  · intro h x hx
    change hform _ _ x y ∈ _
    rw [hform_eq_sum _ _ (map_mul_eq_one (F := F) (Fv F v) h1)]
    exact sum_mem fun j _ => mul_mem (sigR_mem_intLoc σ ((mem_latLoc_iff_of_frame h1 hS hΦ v x).1 hx j)) (h j)

end DualFrame

variable {σ J} {L L' : Submodule (𝓞 E) (Fin n → E)}

omit [NumberField F] in

/- English proof (translation)
Take `⟨k, S, Φ, h1, hS, hΦ⟩` from `exists_frame L hL`. Establish `h2` using `dual_mul_eq_one (σ := σ) hJ h1`. Establish `h3` using `dual_col_mem (σ := σ) hJ hΦ`. Use `⟨⟨Finset.univ.image fun j i => (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) i j, le_antisymm ?_ fun y hy => ?_⟩, eq_top_iff.2 fun y _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `h3 j`. Rewrite using `[eq_sum_col h2 y]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `dual_integral hS y hy j`. Rewrite using `[← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ r (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))`. Rewrite using `[eq_sum_col h2 y]`. Conclude with `sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (h3 j))`.
-/
theorem isLattice_dualGlob (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (dualGlob σ J L) := by
  classical
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  have h2 := dual_mul_eq_one (σ := σ) hJ h1
  have h3 := dual_col_mem (σ := σ) hJ hΦ
  refine ⟨⟨Finset.univ.image fun j i => (J⁻¹ * (Φ.map (σ : E →+* E))ᵀ) i j, le_antisymm ?_ fun y hy => ?_⟩,
    eq_top_iff.2 fun y _ => ?_⟩
  · rw [Submodule.span_le]
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact h3 j
  · rw [eq_sum_col h2 y]
    refine sum_mem fun j _ => ?_
    obtain ⟨r, hr⟩ := dual_integral hS y hy j
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (h3 j))

/- English proof (translation)
Take `⟨k, S, Φ, h1, hS, hΦ⟩` from `exists_frame L hL`. Use extensionality with `y`. Rewrite using `[mem_dualLoc_iff_of_frame h1 hS hΦ, mem_latLoc_iff_of_frame (dual_mul_eq_one hJ h1) (dual_col_mem hJ hΦ) (dual_integral hS)]`.
-/
theorem latLoc_dualGlob (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) (v : HeightOneSpectrum (𝓞 F)) :
    latLoc F (dualGlob σ J L) v = dualLoc σ J L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  ext y
  rw [mem_dualLoc_iff_of_frame h1 hS hΦ,
    mem_latLoc_iff_of_frame (dual_mul_eq_one hJ h1) (dual_col_mem hJ hΦ) (dual_integral hS)]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
The claim follows from `(RingHom.map_mulVec (inclR (F := F) R) Φ y j).symm`.
-/
theorem map_mulVec_inclR (R : Type) [CommRing R] [Algebra F R] {k : ℕ} (Φ : Matrix (Fin k) (Fin n) E) (y : Fin n → E)
    (j : Fin k) : (Φ.map (inclR (F := F) R) *ᵥ fun i => inclR R (y i)) j = inclR R ((Φ *ᵥ y) j) :=
  (RingHom.map_mulVec (inclR (F := F) R) Φ y j).symm

/- English proof (translation)
Use `⟨fun hy v => tmul_mem_latLoc (one_mem _) hy, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, S, Φ, h1, hS, hΦ⟩` from `exists_frame L hL`. Use `(mem_iff_of_frame h1 hS hΦ y).2 fun j => mem_range_of_forall_intLoc (F := F) fun v => ?_` and prove the remaining obligations. Rewrite using `[← map_mulVec_inclR]`. Conclude with `(mem_latLoc_iff_of_frame h1 hS hΦ v _).1 (h v) j`.
-/
theorem mem_iff_forall_latLoc (hL : Submodule.IsLattice E L) (y : Fin n → E) :
    y ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclR (Fv F v) (y i)) ∈ latLoc F L v := by
  refine ⟨fun hy v => tmul_mem_latLoc (one_mem _) hy, fun h => ?_⟩
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  refine (mem_iff_of_frame h1 hS hΦ y).2 fun j => mem_range_of_forall_intLoc (F := F) fun v => ?_
  rw [← map_mulVec_inclR]
  exact (mem_latLoc_iff_of_frame h1 hS hΦ v _).1 (h v) j

/- English proof (translation)
Take `⟨k, S, Φ, h1, hS, hΦ⟩` from `exists_frame L hL`. Use `filter_upwards [Filter.eventually_all.2 fun j => eventually_mem_intLoc (F := F) ((Φ *ᵥ y) j)] with v hv`. Use `(mem_latLoc_iff_of_frame h1 hS hΦ v _).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[map_mulVec_inclR]`. Conclude with `hv j`.
-/
theorem eventually_mem_latLoc (hL : Submodule.IsLattice E L) (y : Fin n → E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (fun i => inclR (Fv F v) (y i)) ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  filter_upwards [Filter.eventually_all.2 fun j => eventually_mem_intLoc (F := F) ((Φ *ᵥ y) j)] with v hv
  refine (mem_latLoc_iff_of_frame h1 hS hΦ v _).2 fun j => ?_
  rw [map_mulVec_inclR]
  exact hv j

/- English proof (translation)
Take `⟨k, S, Φ, h1, hS, hΦ⟩` from `exists_frame L hL`. Use `filter_upwards [Filter.eventually_all.2 fun j => eventually_mem_latLoc (F := F) hL' fun i => S i j] with v hv y hy`. Rewrite using `[eq_sum_col (map_mul_eq_one (F := F) (Fv F v) h1) y]`. Conclude with `sum_mem fun j _ => (latLoc F L' v).smul_mem ⟨_, (mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j⟩ (hv j)`.
-/
theorem eventually_latLoc_le (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, latLoc F L v ≤ latLoc F L' v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  filter_upwards [Filter.eventually_all.2 fun j => eventually_mem_latLoc (F := F) hL' fun i => S i j] with v hv y hy
  rw [eq_sum_col (map_mul_eq_one (F := F) (Fv F v) h1) y]
  exact sum_mem fun j _ => (latLoc F L' v).smul_mem ⟨_, (mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j⟩ (hv j)

/- English proof (translation)
Use `filter_upwards [eventually_latLoc_le (F := F) hL hL', eventually_latLoc_le (F := F) hL' hL] with v h h'`. Conclude with `le_antisymm h h'`.
-/
theorem eventually_latLoc_eq (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, latLoc F L v = latLoc F L' v := by
  filter_upwards [eventually_latLoc_le (F := F) hL hL', eventually_latLoc_le (F := F) hL' hL] with v h h'
  exact le_antisymm h h'

/- English proof (translation)
Use `⟨fun h v => by rw [h], fun h => Submodule.ext fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_iff_forall_latLoc (F := F) hL, mem_iff_forall_latLoc (F := F) hL']`. Simplify using `only [h]`.
-/
theorem eq_iff_forall_latLoc_eq (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') :
    L = L' ↔ ∀ v : HeightOneSpectrum (𝓞 F), latLoc F L v = latLoc F L' v := by
  refine ⟨fun h v => by rw [h], fun h => Submodule.ext fun y => ?_⟩
  rw [mem_iff_forall_latLoc (F := F) hL, mem_iff_forall_latLoc (F := F) hL']
  simp only [h]

/- English proof (translation)
Use `filter_upwards [eventually_latLoc_eq (F := F) hL (isLattice_dualGlob (σ := σ) hJ hL)] with v hv`. Conclude with `hv.trans (latLoc_dualGlob hJ hL v)`.
-/
theorem eventually_isSelfDualAt (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) :
    ∀ᶠ v in Filter.cofinite, IsSelfDualAt σ J L v := by
  filter_upwards [eventually_latLoc_eq (F := F) hL (isLattice_dualGlob (σ := σ) hJ hL)] with v hv
  exact hv.trans (latLoc_dualGlob hJ hL v)

/- English proof (translation)
Simplify using `only [IsSelfDualAt, ← latLoc_dualGlob hJ hL]`. Rewrite using `[← eq_iff_forall_latLoc_eq hL (isLattice_dualGlob hJ hL)]`. Conclude with `Submodule.ext_iff`.
-/
theorem forall_isSelfDualAt_iff (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) :
    (∀ v, IsSelfDualAt σ J L v) ↔ ∀ y : Fin n → E, (y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) := by
  simp only [IsSelfDualAt, ← latLoc_dualGlob hJ hL]
  rw [← eq_iff_forall_latLoc_eq hL (isLattice_dualGlob hJ hL)]
  exact Submodule.ext_iff

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

/- English proof (translation)
Use `⟨frameLat_fg V, ?_⟩` and prove the remaining obligations. Establish `: (frameLat V : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)` using `(V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm`. Rewrite using `[this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem isLattice_frameLat {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) :
    Submodule.IsLattice E (frameLat V) := by
  refine ⟨frameLat_fg V, ?_⟩
  have : (frameLat V : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
    (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
  rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Use `(forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero (isLattice_frameLat V)).2 (fun y => ?_) v` and prove the remaining obligations. Establish `e : ∀ x, hE hc.sig V.gram x y = V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y)` using `fun x => by`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]`. Simplify using `only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Establish `h2 : ∀ z, z ∈ V.L0 ↔ ∀ x ∈ V.L0, V.hT x z ∈ (1 : Submodule (𝓞 E) E)` using `fun z => by conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT V.L0 = V.L0 from V.baseLattice_isUnimodular]`. Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]`. Simplify using `only [e]`. Use `(h2 _).trans ⟨fun h x hx => Submodule.mem_one.1 (h _ hx), fun h x hx => Submodule.mem_one.2 ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `V.frame.equivFun.symm.surjective x`.

Conclude with `h x hx`.
-/
theorem isSelfDualAt_frameLat_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) :
    IsSelfDualAt hc.sig V.gram (frameLat V) v := by
  refine (forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero (isLattice_frameLat V)).2 (fun y => ?_) v
  have e : ∀ x, hE hc.sig V.gram x y = V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) := fun x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
    simp only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ z, z ∈ V.L0 ↔ ∀ x ∈ V.L0, V.hT x z ∈ (1 : Submodule (𝓞 E) E) := fun z => by
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT V.L0 = V.L0 from V.baseLattice_isUnimodular]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  simp only [e]
  refine (h2 _).trans ⟨fun h x hx => Submodule.mem_one.1 (h _ hx), fun h x hx => Submodule.mem_one.2 ?_⟩
  obtain ⟨x, rfl⟩ := V.frame.equivFun.symm.surjective x
  exact h x hx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `isSelfDualAt_frameLat_of_cm D.sp.cm V v`.
-/
theorem isSelfDualAt_frameLat (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsSelfDualAt D.sp.cm.sig V.gram (frameLat V) v := isSelfDualAt_frameLat_of_cm D.sp.cm V v

end Record

end GlobalTheory.AdelicU.SelfDual

end
