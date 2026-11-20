import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TauLat

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.isIntegral_coe`. Introduce `h`.

Conclude with `⟨⟨x, h⟩, rfl⟩`.
-/
theorem mem_one_iff {K : Type} [Field K] (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Rewrite using `[← mem_one_iff, Submodule.mem_one]`. Both sides reduce to the same expression.
-/
theorem mem_range_iff {K : Type} [Field K] (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  rw [← mem_one_iff, Submodule.mem_one]
  rfl

/- English proof (translation)
The claim follows from `map_isIntegral_int f h`.
-/
theorem integral_map {E K : Type} [Field E] [Field K] (f : E →+* K) {x : E} (h : IsIntegral ℤ x) :
    IsIntegral ℤ (f x) := map_isIntegral_int f h

/- English proof (translation)
The claim follows from `M.smul_mem (⟨c, hc⟩ : 𝓞 K) hv`.
-/
theorem smul_mem_of_integral {K : Type} [Field K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) {c : K}
    (hc : IsIntegral ℤ c) {v : Fin n → K} (hv : v ∈ M) : c • v ∈ M :=
  M.smul_mem (⟨c, hc⟩ : 𝓞 K) hv

/- English proof (translation)
Use `isLocalizedModule_id (nonZeroDivisors (𝓞 E)) (Fin n → E) E` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)) s`. Use `surj y := by`. Establish `hy : y ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL.span_eq_top]; trivial`. Take `⟨s, hs⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (L : Set (Fin n → E)) y hy`.

Rewrite `hs` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, hs⟩, s), rfl⟩`. Use `exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩`.
-/
theorem isLocalizedModule_subtype {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype where
  map_units s := by
    have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) (Fin n → E) E
    exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E))
      (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)) s
  surj y := by
    have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (L : Set (Fin n → E)) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨(⟨_, hs⟩, s), rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

/- English proof (translation)
Establish `: Module.FinitePresentation (𝓞 E) L` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) L` using `Module.Flat.projective_of_finitePresentation`. Use `isLocalizedModule_subtype L hL` as an intermediate fact. Take `⟨m, π, hπ⟩` from `Module.Finite.exists_fin' (𝓞 E) L`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`.

Establish `hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x)` using `fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x`. Set `f : Fin m → (Fin n → E) →ₗ[E] E` to `fun i => LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E (IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj i ∘ₗ s) hu)`. Establish `hf : ∀ i (y : L), f i y = algebraMap (𝓞 E) E (s y i)` using `fun i y => IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype _ hu y`. Set `x : Fin m → Fin n → E` to `fun i => (π (Pi.single i 1) : L)`. Establish `hdot : ∀ i y, (fun b => f i (Pi.single b 1)) ⬝ᵥ y = f i y`.

Introduce `i y`. Use `conv_rhs => rw [pi_eq_sum_univ' y]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, dotProduct, mul_comm]`. Establish `key : ∀ y, ∑ i, f i y • x i = y`. Establish `: (∑ i, (f i).smulRight (x i)) = LinearMap.id`.

Apply `LinearMap.ext_on hL.span_eq_top` to reduce the goal to its premises. Introduce `y hy`. Establish `h1 : π (s ⟨y, hy⟩) = ⟨y, hy⟩` using `LinearMap.congr_fun hs ⟨y, hy⟩`. Establish `h2 : (π (s ⟨y, hy⟩) : Fin n → E) = y` using `by rw [h1]`. Rewrite `h2` using `[pi_eq_sum_univ' (s ⟨y, hy⟩)]`.

Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h2`. Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2` and prove the remaining obligations. Rewrite using `[hf i ⟨y, hy⟩, algebraMap_smul]`. Introduce `y`.

Simplify using `using LinearMap.congr_fun this y`. Use `⟨m, x, fun i b => f i (Pi.single b 1), fun i => (π (Pi.single i 1)).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `i y hy`. Rewrite using `[hdot, hf i ⟨y, hy⟩]`. Conclude with `(s ⟨y, hy⟩ i).isIntegral_coe`.

Introduce `a b`. Use `congrFun (key (Pi.single b 1)) a` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at this`. Rewrite using `[← this]`. Simplify using `only [mul_comm]`.
-/
theorem exists_dual_family {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) :
    ∃ (m : ℕ) (x φ : Fin m → Fin n → E), (∀ i, x i ∈ L) ∧ (∀ i, ∀ y ∈ L, IsIntegral ℤ (φ i ⬝ᵥ y)) ∧
      ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0 := by
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  have := isLocalizedModule_subtype L hL
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let f : Fin m → (Fin n → E) →ₗ[E] E := fun i =>
    LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype
        (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj i ∘ₗ s) hu)
  have hf : ∀ i (y : L), f i y = algebraMap (𝓞 E) E (s y i) := fun i y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype _ hu y
  let x : Fin m → Fin n → E := fun i => (π (Pi.single i 1) : L)
  have hdot : ∀ i y, (fun b => f i (Pi.single b 1)) ⬝ᵥ y = f i y := by
    intro i y
    conv_rhs => rw [pi_eq_sum_univ' y]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, mul_comm]
  have key : ∀ y, ∑ i, f i y • x i = y := by
    have : (∑ i, (f i).smulRight (x i)) = LinearMap.id := by
      apply LinearMap.ext_on hL.span_eq_top
      intro y hy
      have h1 : π (s ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hs ⟨y, hy⟩
      have h2 : (π (s ⟨y, hy⟩) : Fin n → E) = y := by rw [h1]
      rw [pi_eq_sum_univ' (s ⟨y, hy⟩)] at h2
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h2
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [hf i ⟨y, hy⟩, algebraMap_smul]
    intro y
    simpa using LinearMap.congr_fun this y
  refine ⟨m, x, fun i b => f i (Pi.single b 1), fun i => (π (Pi.single i 1)).2, ?_, ?_⟩
  · intro i y hy
    rw [hdot, hf i ⟨y, hy⟩]
    exact (s ⟨y, hy⟩ i).isIntegral_coe
  · intro a b
    have := congrFun (key (Pi.single b 1)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at this
    rw [← this]
    simp only [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ a, ∑ i, f (x i a) * v a * f (φ i b) = if a = b then v a else 0`. Introduce `a`.

Establish `h1` using `congrArg f (h a b)`. Rewrite `h1` using `[map_sum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `_ = _ := by rw [h1]; split_ifs <;> simp`. Simplify using `[this]`.
-/
theorem expand_left {E K : Type} [Field E] [Field K] (f : E →+* K) {n m : ℕ} {x φ : Fin m → Fin n → E}
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (v : Fin n → K) :
    v = ∑ i, ((fun a => f (x i a)) ⬝ᵥ v) • fun b => f (φ i b) := by
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ a, ∑ i, f (x i a) * v a * f (φ i b) = if a = b then v a else 0 := by
    intro a
    have h1 := congrArg f (h a b)
    rw [map_sum] at h1
    calc _ = v a * ∑ i, f (x i a * φ i b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
      _ = _ := by rw [h1]; split_ifs <;> simp
  simp [this]

/- English proof (translation)
Apply `expand_left` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [mul_comm (φ _ a), h, eq_comm]`.
-/
theorem expand_right {E K : Type} [Field E] [Field K] (f : E →+* K) {n m : ℕ} {x φ : Fin m → Fin n → E}
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (v : Fin n → K) :
    v = ∑ i, ((fun a => f (φ i a)) ⬝ᵥ v) • fun b => f (x i b) := by
  apply expand_left
  intro a b
  simp only [mul_comm (φ _ a), h, eq_comm]

/- English proof (translation)
Simplify using `[dotProduct]`.
-/
theorem map_dot {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (u v : Fin n → E) :
    f (u ⬝ᵥ v) = (fun a => f (u a)) ⬝ᵥ fun a => f (v a) := by
  simp [dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem map_mulVec {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (fun a => f ((J *ᵥ v) a)) = J.map f *ᵥ fun a => f (v a) := by
  funext a
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Simplify using `[Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq {E : Type} [Field E] {n : ℕ} (c : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform c J x y = (fun a => c (x a)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Introduce `E K _ _ _ _ ι n emb τ L hL`. Take `⟨m, x, φ, hx, hφ, h⟩` from `exists_dual_family L hL`. Establish `hmem : ∀ i, (fun a => emb τ (x i a)) ∈ tauLat emb τ L` using `fun i => Submodule.subset_span ⟨x i, hx i, rfl⟩`. Prove the components needed by the constructor for the conclusion. Use `⟨(Finset.univ.image fun i => fun a => emb τ (x i a)), le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Simplify using `only [Finset.coe_image, Set.mem_image] at hv`. Take `⟨i, -, rfl⟩` from `hv`. Conclude with `hmem i`.

Unfold `tauLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `beta_reduce`. Rewrite using `[SetLike.mem_coe, expand_right (emb τ) h (fun a => emb τ (y a))]`.

Use `Submodule.sum_mem _ fun i _ => smul_mem_of_integral _ ?_ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[← map_dot]`. Conclude with `integral_map _ (hφ i y hy)`. Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Rewrite using `[expand_right (emb τ) h v]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))`.
-/
theorem tauLatLattice : TauLatLattice := by
  classical
  intro E K _ _ _ _ ι n emb τ L hL
  obtain ⟨m, x, φ, hx, hφ, h⟩ := exists_dual_family L hL
  have hmem : ∀ i, (fun a => emb τ (x i a)) ∈ tauLat emb τ L := fun i => Submodule.subset_span ⟨x i, hx i, rfl⟩
  constructor
  · refine ⟨(Finset.univ.image fun i => fun a => emb τ (x i a)), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨i, -, rfl⟩ := hv
      exact hmem i
    · unfold tauLat
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      beta_reduce
      rw [SetLike.mem_coe, expand_right (emb τ) h (fun a => emb τ (y a))]
      refine Submodule.sum_mem _ fun i _ => smul_mem_of_integral _ ?_ (Submodule.subset_span ?_)
      · rw [← map_dot]
        exact integral_map _ (hφ i y hy)
      · simp
  · rw [eq_top_iff]
    intro v _
    rw [expand_right (emb τ) h v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))

/- English proof (translation)
Introduce `E K _ _ _ _ _ ι n emb cE τ hc J L L' hJ hL hL'`. Take `⟨m, x, φ, hx, hφ, h⟩` from `exists_dual_family L hL`. Establish `hstar : ∀ y : Fin n → E, star (fun a => emb τ (y a)) = fun a => emb τ (cE (y a))`. Introduce `y`. Use function extensionality and compare the values at `a`.

Conclude with `hc _`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Establish `hv' : ∀ i, IsIntegral ℤ ((fun a => emb τ (cE (x i a))) ⬝ᵥ (J.map (emb τ) *ᵥ v))`. Introduce `i`.

Rewrite using `[← mem_one_iff, ← hstar]`. Conclude with `hv _ (Submodule.subset_span ⟨x i, hx i, rfl⟩)`. Establish `e1` using `expand_left ((emb τ).comp cE) h (J.map (emb τ) *ᵥ v)`. Establish `e2 : v = (J⁻¹).map (emb τ) *ᵥ (J.map (emb τ) *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ]`.

Simplify using the standard rewrite rules. Rewrite using `[e2, e1, Matrix.mulVec_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Use `smul_mem_of_integral _ (hv' i) ?_` and prove the remaining obligations.

Unfold `tauLat`. Use `Submodule.subset_span ⟨J⁻¹ *ᵥ fun a => cE (φ i a), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hL']`. Introduce `y hy`. Rewrite using `[mem_range_iff, hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, ← map_dot, dotProduct_comm]`.

Conclude with `integral_map _ (hφ i y hy)`. Conclude with `map_mulVec _ _ _`. Unfold `tauLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩ z hz`.

Rewrite using `[mem_one_iff]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨u, hu, rfl⟩` from `hz`. Use `integral_map (emb τ) ((mem_range_iff _).1 ((hL' y).1 hy u hu))` as an intermediate fact.

Rewrite `this` using `[hform_eq, map_dot, map_mulVec]`. Rewrite using `[hstar]`. Conclude with `this`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add u w _ _ hu hw => rw [star_add, add_dotProduct]`.

Conclude with `hu.add hw`. Consider the case `smul c u _ hu`. Rewrite using `[← algebraMap_smul K c u, star_smul, smul_dotProduct, smul_eq_mul]`. Conclude with `(integral_map (starRingEnd K) c.isIntegral_coe).mul hu`.
-/
theorem tauLatDual : TauLatDual := by
  intro E K _ _ _ _ _ ι n emb cE τ hc J L L' hJ hL hL'
  obtain ⟨m, x, φ, hx, hφ, h⟩ := exists_dual_family L hL
  have hstar : ∀ y : Fin n → E, star (fun a => emb τ (y a)) = fun a => emb τ (cE (y a)) := by
    intro y; funext a; exact hc _
  apply le_antisymm
  · intro v hv
    have hv' : ∀ i, IsIntegral ℤ ((fun a => emb τ (cE (x i a))) ⬝ᵥ (J.map (emb τ) *ᵥ v)) := by
      intro i
      rw [← mem_one_iff, ← hstar]
      exact hv _ (Submodule.subset_span ⟨x i, hx i, rfl⟩)
    have e1 := expand_left ((emb τ).comp cE) h (J.map (emb τ) *ᵥ v)
    have e2 : v = (J⁻¹).map (emb τ) *ᵥ (J.map (emb τ) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ]
      simp
    rw [e2, e1, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    refine smul_mem_of_integral _ (hv' i) ?_
    unfold tauLat
    refine Submodule.subset_span ⟨J⁻¹ *ᵥ fun a => cE (φ i a), ?_, ?_⟩
    · rw [SetLike.mem_coe, hL']
      intro y hy
      rw [mem_range_iff, hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, ← map_dot,
        dotProduct_comm]
      exact integral_map _ (hφ i y hy)
    · exact map_mulVec _ _ _
  · unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩ z hz
    rw [mem_one_iff]
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      have := integral_map (emb τ) ((mem_range_iff _).1 ((hL' y).1 hy u hu))
      rw [hform_eq, map_dot, map_mulVec] at this
      rw [hstar]
      exact this
    | zero => simpa using isIntegral_zero
    | add u w _ _ hu hw => rw [star_add, add_dotProduct]; exact hu.add hw
    | smul c u _ hu =>
      rw [← algebraMap_smul K c u, star_smul, smul_dotProduct, smul_eq_mul]
      exact (integral_map (starRingEnd K) c.isIntegral_coe).mul hu

/- English proof (translation)
Introduce `E K _ _ _ _ ι n emb cE τ hc Jg L L' hL hH hL'`. Take `⟨m, x, φ, hx, hφ, h⟩` from `exists_dual_family L hL`. Use `set J : Matrix (Fin n) (Fin n) E := (Jg : Matrix (Fin n) (Fin n) E) with hJdef`. Establish `hJ : IsUnit J.det` using `Matrix.isUnits_det_units Jg`. Establish `hg : ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Jᵀ).map (emb τ)`.

Rewrite using `[map_inv]`. Express the relevant statement in the definitionally equal form `(((embGL emb Jg τ)⁻¹⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = _`. Rewrite using `[inv_inv]`. Both sides reduce to the same expression. Establish `hherm : ∀ a b, cE (J a b) = J b a` using `fun a b => congrFun (congrFun hH b) a`.

Establish `hform' : ∀ u y : Fin n → E, Formalism.UG.hform cE J u y = cE ((Jᵀ *ᵥ fun a => cE (y a)) ⬝ᵥ u)`. Introduce `u y`. Simplify using `only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Matrix.transpose_apply, map_sum, map_mul, hc, hherm, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hJt : IsUnit Jᵀ.det` using `by rwa [Matrix.det_transpose]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[expand_left (emb τ) h v]`. Use `Submodule.sum_mem _ fun i _ => smul_mem_of_integral _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[dotProduct_comm, ← mem_one_iff]`. Conclude with `hv _ (Submodule.subset_span ⟨x i, hx i, rfl⟩)`. Unfold `gLat tauLat`. Use `Submodule.mem_map.2 ⟨_, Submodule.subset_span ⟨fun a => cE ((Jᵀ⁻¹ *ᵥ φ i) a), ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hL']`.

Introduce `y hy`. Rewrite using `[mem_range_iff, hform']`. Simplify using `only [hc]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJt, Matrix.one_mulVec]`. Conclude with `integral_map _ (hφ i y hy)`.

Simplify using `only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, RingHom.comp_apply, hc, hg]`. Rewrite using `[← map_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJt, Matrix.one_mulVec]`. Unfold `gLat`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Unfold `tauLat`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩ z hz`. Rewrite using `[mem_one_iff]`. Simplify using `only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, RingHom.comp_apply, hg]`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨u, hu, rfl⟩` from `hz`. Use `integral_map cE ((mem_range_iff _).1 ((hL' y).1 hy u hu))` as an intermediate fact. Rewrite `this` using `[hform', hc]`. Use `integral_map (emb τ) this` as an intermediate fact.

Rewrite `this` using `[map_dot, map_mulVec]`. Conclude with `this`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add u w _ _ hu hw => rw [dotProduct_add]`. Conclude with `hu.add hw`.

Consider the case `smul c u _ hu`. Rewrite using `[← algebraMap_smul K c u, dotProduct_smul, smul_eq_mul]`. Conclude with `c.isIntegral_coe.mul hu`.
-/
theorem roundLat : RoundLat := by
  intro E K _ _ _ _ ι n emb cE τ hc Jg L L' hL hH hL'
  obtain ⟨m, x, φ, hx, hφ, h⟩ := exists_dual_family L hL
  set J : Matrix (Fin n) (Fin n) E := (Jg : Matrix (Fin n) (Fin n) E) with hJdef
  have hJ : IsUnit J.det := Matrix.isUnits_det_units Jg
  have hg : ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Jᵀ).map (emb τ) := by
    rw [map_inv]
    change (((embGL emb Jg τ)⁻¹⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = _
    rw [inv_inv]
    rfl
  have hherm : ∀ a b, cE (J a b) = J b a := fun a b => congrFun (congrFun hH b) a
  have hform' : ∀ u y : Fin n → E, Formalism.UG.hform cE J u y = cE ((Jᵀ *ᵥ fun a => cE (y a)) ⬝ᵥ u) := by
    intro u y
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Matrix.transpose_apply, map_sum, map_mul, hc, hherm,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hJt : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  apply le_antisymm
  · intro v hv
    rw [expand_left (emb τ) h v]
    refine Submodule.sum_mem _ fun i _ => smul_mem_of_integral _ ?_ ?_
    · rw [dotProduct_comm, ← mem_one_iff]
      exact hv _ (Submodule.subset_span ⟨x i, hx i, rfl⟩)
    · unfold gLat tauLat
      refine Submodule.mem_map.2 ⟨_, Submodule.subset_span ⟨fun a => cE ((Jᵀ⁻¹ *ᵥ φ i) a), ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, hL']
        intro y hy
        rw [mem_range_iff, hform']
        simp only [hc]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJt, Matrix.one_mulVec]
        exact integral_map _ (hφ i y hy)
      · simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, RingHom.comp_apply, hc, hg]
        rw [← map_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJt, Matrix.one_mulVec]
  · unfold gLat
    rw [Submodule.map_le_iff_le_comap]
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩ z hz
    rw [mem_one_iff]
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, RingHom.comp_apply, hg]
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      have := integral_map cE ((mem_range_iff _).1 ((hL' y).1 hy u hu))
      rw [hform', hc] at this
      have := integral_map (emb τ) this
      rw [map_dot, map_mulVec] at this
      exact this
    | zero => simpa using isIntegral_zero
    | add u w _ _ hu hw => rw [dotProduct_add]; exact hu.add hw
    | smul c u _ hu =>
      rw [← algebraMap_smul K c u, dotProduct_smul, smul_eq_mul]
      exact c.isIntegral_coe.mul hu

/- English proof (translation)
Assemble the required witnesses or components as `⟨tauLatLattice, tauLatDual, roundLat⟩`.
-/
theorem tauLat_lattice_dual_round : TauLatLattice ∧ TauLatDual ∧ RoundLat := ⟨tauLatLattice, tauLatDual, roundLat⟩

end GlobalTheory.TauLat
