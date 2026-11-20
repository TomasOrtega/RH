import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsExtra

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

section Family

variable {K K' : Type} [Field K] [Field K']

/- English proof (translation)
Use `letI : Algebra K K' := φ.toAlgebra`. Use `haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation`. Take `⟨m, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' := IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')`.

Establish `hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap` using `IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _`. Set `F : Fin m → K' →ₗ[K] K` to `fun i => hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ g)`. Establish `hF : ∀ i (a : 𝓞 K'), F i (algebraMap (𝓞 K') K' a) = algebraMap (𝓞 K) K (g a i)` using `fun i a => hbc.lift_eq _ a`. Use `⟨m, fun i => f (Pi.single i 1), fun i => (F i).toAddMonoidHom, fun i a x => ?_, fun i a => ⟨_, hF i a⟩, ?_⟩` and prove the remaining obligations. Conclude with `(F i).map_smul a x`.

Introduce `x`. Proceed by induction on `x using hbc.inductionOn with`. Consider the case `zero => simp`. Consider the case `tmul a`. Establish `h1 : a = ∑ i, g a i • f (Pi.single i 1)` using `by conv_lhs => rw [← LinearMap.id_apply (R := 𝓞 K) a, ← hfg, LinearMap.comp_apply, pi_eq_sum_univ' (g a), map_sum]`.

Simplify using `only [map_smul]`. Establish `h2 : ∀ i, (F i).toAddMonoidHom ((IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap a) = algebraMap (𝓞 K) K (g a i)` using `fun i => hF i a`. Simplify using `only [h2]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K') K' a = _`. Use `conv_lhs => rw [h1, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K K']`. Both sides reduce to the same expression. Consider the case `smul s x hx`. Establish `h2 : ∀ i, (F i).toAddMonoidHom (s • x) = s * (F i).toAddMonoidHom x` using `fun i => (F i).map_smul s x`.

Simplify using `only [h2]`. Use `conv_lhs => rw [hx]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`.

Express the relevant statement in the definitionally equal form `φ s * _ = _`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`. Simplify using `only [map_add, mul_add, Finset.sum_add_distrib]`. Rewrite using `[← hx, ← hy]`.
-/
theorem exists_dual_family [NumberField K] [NumberField K'] (φ : K →+* K') :
    ∃ (m : ℕ) (b : Fin m → 𝓞 K') (F : Fin m → K' →+ K), (∀ i a x, F i (φ a * x) = a * F i x) ∧
      (∀ i (a : 𝓞 K'), ∃ r : 𝓞 K, F i (algebraMap (𝓞 K') K' a) = algebraMap (𝓞 K) K r) ∧
      ∀ x, x = ∑ i, algebraMap (𝓞 K') K' (b i) * φ (F i x) := by
  letI : Algebra K K' := φ.toAlgebra
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let F : Fin m → K' →ₗ[K] K := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ g)
  have hF : ∀ i (a : 𝓞 K'), F i (algebraMap (𝓞 K') K' a) = algebraMap (𝓞 K) K (g a i) := fun i a =>
    hbc.lift_eq _ a
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (F i).toAddMonoidHom, fun i a x => ?_, fun i a => ⟨_, hF i a⟩, ?_⟩
  · exact (F i).map_smul a x
  · intro x
    induction x using hbc.inductionOn with
    | zero => simp
    | tmul a =>
      have h1 : a = ∑ i, g a i • f (Pi.single i 1) := by
        conv_lhs => rw [← LinearMap.id_apply (R := 𝓞 K) a, ← hfg, LinearMap.comp_apply, pi_eq_sum_univ' (g a), map_sum]
        simp only [map_smul]
      have h2 : ∀ i, (F i).toAddMonoidHom ((IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap a) =
          algebraMap (𝓞 K) K (g a i) := fun i => hF i a
      simp only [h2]
      change algebraMap (𝓞 K') K' a = _
      conv_lhs => rw [h1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 K) K K']
      rfl
    | smul s x hx =>
      have h2 : ∀ i, (F i).toAddMonoidHom (s • x) = s * (F i).toAddMonoidHom x := fun i => (F i).map_smul s x
      simp only [h2]
      conv_lhs => rw [hx]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      change φ s * _ = _
      ring
    | add x y hx hy =>
      simp only [map_add, mul_add, Finset.sum_add_distrib]
      rw [← hx, ← hy]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Conclude with `(RingHom.map_mulVec φ E x k).symm`.
-/
theorem map_mulVec' (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (x : Fin d → K) :
    (E.map φ) *ᵥ (fun k => φ (x k)) = fun k => φ ((E *ᵥ x) k) := by
  funext k
  exact (RingHom.map_mulVec φ E x k).symm

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨z, rfl⟩` from `hA y`. Rewrite `hy` using `[hM', Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, hN]`. Establish `key : ∀ w ∈ Submodule.span R' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' (N : Set (Fin n → K))), ∃ u, w = C *ᵥ u ∧ ∀ (a : R') i, (fun k => F i (algebraMap R' K' a * u k)) ∈ N`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x, hx, rfl⟩` from `hw`. Use `⟨_, rfl, fun a i => ?_⟩` and prove the remaining obligations.

Take `⟨r, hr⟩` from `hI i a`. Establish `: (fun k => F i (algebraMap R' K' a * φ (x k))) = r • x`. Use function extensionality and compare the values at `k`. Rewrite using `[mul_comm, hF, hr, Pi.smul_apply, Algebra.smul_def, mul_comm]`. Rewrite using `[this]`.

Conclude with `N.smul_mem r hx`. Consider the case `zero => exact ⟨0, by simp, fun a i => by`. Simplify using `only [Pi.zero_apply, mul_zero, map_zero]`. Conclude with `N.zero_mem⟩`. Consider the case `add w w' _ _ h h'`.

Take `⟨u, rfl, hu⟩` from `h`. Take `⟨u', rfl, hu'⟩` from `h'`. Use `⟨u + u', (Matrix.mulVec_add _ _ _).symm, fun a i => ?_⟩` and prove the remaining obligations. Use `N.add_mem (hu a i) (hu' a i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using `[mul_add]`. Consider the case `smul c w _ h`. Take `⟨u, rfl, hu⟩` from `h`. Use `⟨c • u, (Matrix.mulVec_smul _ _ _).symm, fun a i => ?_⟩` and prove the remaining obligations.

Use `hu (a * c) i` as an intermediate fact. Use `this using 3 with k` and compare the differences between its conclusion and the goal. Simplify using `[Algebra.smul_def, mul_assoc]`. Take `⟨u, hu, hu'⟩` from `key _ hy`. Establish `hu2` using `hC hu`.

Establish `hz : z = ∑ i, b i • (fun k => φ (F i (z k)))`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Conclude with `hb (z k)`.

Rewrite using `[hz, Matrix.mulVec_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun k => F i (z k), ?_, rfl⟩)` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hM]`.

Use `hu' 1 i` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[← hu2, map_one, one_mul]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, hF]`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, hM', Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, map_mulVec', hN]`. Conclude with `Submodule.subset_span ⟨_, (hM x).1 hx, rfl⟩`.
-/
theorem comap_baseChange (φ : K →+* K') {R R' : Type} [CommRing R] [CommRing R'] [Algebra R K] [Algebra R' K']
    {m : ℕ} (b : Fin m → R') (F : Fin m → K' →+ K) (hF : ∀ i a x, F i (φ a * x) = a * F i x)
    (hI : ∀ i (a : R'), ∃ r : R, F i (algebraMap R' K' a) = algebraMap R K r)
    (hb : ∀ x, x = ∑ i, algebraMap R' K' (b i) * φ (F i x))
    {n n' d d' : ℕ} (C : Matrix (Fin n') (Fin n) K') (hC : Function.Injective C.mulVec)
    (A : Matrix (Fin d') (Fin d) K') (hA : Function.Surjective A.mulVec)
    (E : Matrix (Fin n) (Fin d) K) (E' : Matrix (Fin n') (Fin d') K') (hE : E' * A = C * E.map φ)
    (N : Submodule R (Fin n → K)) (N' : Submodule R' (Fin n' → K'))
    (hN : N' = Submodule.span R' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' (N : Set (Fin n → K))))
    (M : Submodule R (Fin d → K)) (M' : Submodule R' (Fin d' → K'))
    (hM : ∀ x, x ∈ M ↔ E *ᵥ x ∈ N) (hM' : ∀ x, x ∈ M' ↔ E' *ᵥ x ∈ N') :
    M' = Submodule.span R' ((fun x : Fin d → K => A *ᵥ (fun k => φ (x k))) '' (M : Set (Fin d → K))) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, rfl⟩ := hA y
    rw [hM', Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, hN] at hy
    have key : ∀ w ∈ Submodule.span R' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' (N : Set (Fin n → K))),
        ∃ u, w = C *ᵥ u ∧ ∀ (a : R') i, (fun k => F i (algebraMap R' K' a * u k)) ∈ N := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        refine ⟨_, rfl, fun a i => ?_⟩
        obtain ⟨r, hr⟩ := hI i a
        have : (fun k => F i (algebraMap R' K' a * φ (x k))) = r • x := by
          funext k
          rw [mul_comm, hF, hr, Pi.smul_apply, Algebra.smul_def, mul_comm]
        rw [this]
        exact N.smul_mem r hx
      | zero => exact ⟨0, by simp, fun a i => by
          simp only [Pi.zero_apply, mul_zero, map_zero]; exact N.zero_mem⟩
      | add w w' _ _ h h' =>
        obtain ⟨u, rfl, hu⟩ := h
        obtain ⟨u', rfl, hu'⟩ := h'
        refine ⟨u + u', (Matrix.mulVec_add _ _ _).symm, fun a i => ?_⟩
        have := N.add_mem (hu a i) (hu' a i)
        convert this using 1
        funext k
        simp [mul_add]
      | smul c w _ h =>
        obtain ⟨u, rfl, hu⟩ := h
        refine ⟨c • u, (Matrix.mulVec_smul _ _ _).symm, fun a i => ?_⟩
        have := hu (a * c) i
        convert this using 3 with k
        simp [Algebra.smul_def, mul_assoc]
    obtain ⟨u, hu, hu'⟩ := key _ hy
    have hu2 := hC hu
    have hz : z = ∑ i, b i • (fun k => φ (F i (z k))) := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def]
      exact hb (z k)
    rw [hz, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun k => F i (z k), ?_, rfl⟩)
    rw [SetLike.mem_coe, hM]
    have := hu' 1 i
    convert this using 1
    funext k
    rw [← hu2, map_one, one_mul]
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, hF]
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hM', Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, map_mulVec', hN]
    exact Submodule.subset_span ⟨_, (hM x).1 hx, rfl⟩

/- English proof (translation)
Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 2`. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]`. Rewrite using `[Matrix.mulVec_mulVec, hL, ← Matrix.mulVec_mulVec, map_mulVec']`.
-/
theorem map_baseChange (φ : K →+* K') {R R' : Type} [CommRing R] [CommRing R'] [Algebra R K] [Algebra R' K']
    {n n' d d' : ℕ} (C : Matrix (Fin n') (Fin n) K') (A : Matrix (Fin d') (Fin d) K')
    (L : Matrix (Fin d) (Fin n) K) (L' : Matrix (Fin d') (Fin n') K') (hL : L' * C = A * L.map φ)
    (N : Submodule R (Fin n → K)) :
    (Submodule.span R' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' (N : Set (Fin n → K)))).map
        ((Matrix.mulVecLin L').restrictScalars R') =
      Submodule.span R' ((fun x : Fin d → K => A *ᵥ (fun k => φ (x k))) ''
        (N.map ((Matrix.mulVecLin L).restrictScalars R) : Set (Fin d → K))) := by
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 2
  funext x
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, hL, ← Matrix.mulVec_mulVec, map_mulVec']

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `⟨_, rfl⟩`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[pi_eq_sum_univ' z, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩)` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[Pi.single_apply, apply_ite φ]`.
-/
theorem span_range (φ : K →+* K') {n n' : ℕ} (C : Matrix (Fin n') (Fin n) K') :
    Submodule.span K' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' ((⊤ : Submodule K (Fin n → K)) : Set (Fin n → K))) =
      LinearMap.range C.mulVecLin := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    rw [pi_eq_sum_univ' z, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩)
    simp only [Matrix.mulVecLin_apply]
    congr 1
    funext k
    simp [Pi.single_apply, apply_ite φ]

/- English proof (translation)
Establish `h` using `map_baseChange (R := K) (R' := K') φ C A L L' hL ⊤`. Rewrite `h` using `[span_range, LinearMap.range_eq_top.2 (show Function.Surjective C.mulVecLin from hC), Submodule.map_top, Submodule.map_top]`. Conclude with `h`.
-/
theorem range_baseChange (φ : K →+* K') {n n' d d' : ℕ} (C : Matrix (Fin n') (Fin n) K') (hC : Function.Surjective C.mulVec)
    (A : Matrix (Fin d') (Fin d) K')
    (L : Matrix (Fin d) (Fin n) K) (L' : Matrix (Fin d') (Fin n') K') (hL : L' * C = A * L.map φ) :
    LinearMap.range L'.mulVecLin = Submodule.span K' ((fun x : Fin d → K => A *ᵥ (fun k => φ (x k))) ''
        (LinearMap.range L.mulVecLin : Set (Fin d → K))) := by
  have h := map_baseChange (R := K) (R' := K') φ C A L L' hL ⊤
  rw [span_range, LinearMap.range_eq_top.2 (show Function.Surjective C.mulVecLin from hC), Submodule.map_top,
    Submodule.map_top] at h
  exact h

end Family

section Coord

variable {K K' : Type} [Field K] [Field K'] [StarRing K] [StarRing K']

omit [StarRing K] [StarRing K'] in
/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IsolatedTheoremFive.target`. Consider the case `exact _root_.GlobalTheory.IsolatedTheoremFive.target`. Consider the case `(apply _root_.GlobalTheory.IsolatedTheoremFive.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IsolatedTheoremFive.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IsolatedTheoremFive.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IsolatedTheoremFive.target ..)`.
-/
theorem map_injective (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (hE : Function.Injective E.mulVec) :
    Function.Injective (E.map φ).mulVec := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFive.target
  | exact _root_.GlobalTheory.IsolatedTheoremFive.target
  | (apply _root_.GlobalTheory.IsolatedTheoremFive.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFive.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFive.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFive.target ..)

/- English proof (translation)
Take `⟨hi, hr⟩` from `subspace_image_spec K n W`. Take `⟨hi', hr'⟩` from `subspace_image_spec K' n' W'`. Establish `hrange : LinearMap.range (C * (subE W).map φ).mulVecLin = W'`. Use `range_baseChange φ (1 : Matrix (Fin (subDim W)) (Fin (subDim W)) K') (fun x => ⟨x, Matrix.one_mulVec x⟩) C (subE W) (C * (subE W).map φ) (Matrix.mul_one _)` as an intermediate fact. Rewrite using `[this, hr, hW]`.

Establish `hcol : ∀ j, ∃ y, (subE W') *ᵥ y = (C * (subE W).map φ) *ᵥ (Pi.single j 1)` using `fun j => by`. Establish `: (C * (subE W).map φ) *ᵥ (Pi.single j 1) ∈ LinearMap.range (subE W').mulVecLin`. Rewrite using `[hr', ← hrange]`. Conclude with `⟨_, rfl⟩`. Conclude with `this`.

Use `choose y hy using hcol`. Establish `hA : subE W' * (Matrix.of fun i j => y j i) = C * (subE W).map φ`. Use extensionality with `i j`. Use `congrFun (hy j) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`.

Conclude with `this`. Use `⟨Matrix.of fun i j => y j i, ⟨?_, ?_⟩, hA⟩` and prove the remaining obligations. Introduce `x x' h`. Use `congrArg (subE W').mulVec h` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.

Conclude with `map_injective φ _ hi (hC this)`. Introduce `z`. Establish `: (subE W') *ᵥ z ∈ LinearMap.range (C * (subE W).map φ).mulVecLin`. Rewrite using `[hrange.trans hr'.symm]`. Conclude with `⟨_, rfl⟩`.

Take `⟨x, hx⟩` from `this`. Use `⟨x, hi' ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hA]`. Conclude with `hx`.
-/
theorem subE_baseChange (φ : K →+* K') {n n' : ℕ} (C : Matrix (Fin n') (Fin n) K') (hC : Function.Injective C.mulVec)
    (W : Submodule K (Fin n → K)) (W' : Submodule K' (Fin n' → K'))
    (hW : W' = Submodule.span K' ((fun x : Fin n → K => C *ᵥ (fun k => φ (x k))) '' (W : Set (Fin n → K)))) :
    ∃ A : Matrix (Fin (subDim W')) (Fin (subDim W)) K', Function.Bijective A.mulVec ∧
      subE W' * A = C * (subE W).map φ := by
  obtain ⟨hi, hr⟩ := subspace_image_spec K n W
  obtain ⟨hi', hr'⟩ := subspace_image_spec K' n' W'
  have hrange : LinearMap.range (C * (subE W).map φ).mulVecLin = W' := by
    have := range_baseChange φ (1 : Matrix (Fin (subDim W)) (Fin (subDim W)) K') (fun x => ⟨x, Matrix.one_mulVec x⟩)
      C (subE W) (C * (subE W).map φ) (Matrix.mul_one _)
    rw [this, hr, hW]
  have hcol : ∀ j, ∃ y, (subE W') *ᵥ y = (C * (subE W).map φ) *ᵥ (Pi.single j 1) := fun j => by
    have : (C * (subE W).map φ) *ᵥ (Pi.single j 1) ∈ LinearMap.range (subE W').mulVecLin := by
      rw [hr', ← hrange]; exact ⟨_, rfl⟩
    exact this
  choose y hy using hcol
  have hA : subE W' * (Matrix.of fun i j => y j i) = C * (subE W).map φ := by
    ext i j
    have := congrFun (hy j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  refine ⟨Matrix.of fun i j => y j i, ⟨?_, ?_⟩, hA⟩
  · intro x x' h
    have := congrArg (subE W').mulVec h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
    exact map_injective φ _ hi (hC this)
  · intro z
    have : (subE W') *ᵥ z ∈ LinearMap.range (C * (subE W).map φ).mulVecLin := by
      rw [hrange.trans hr'.symm]; exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := this
    refine ⟨x, hi' ?_⟩
    rw [Matrix.mulVec_mulVec, hA]
    exact hx

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[hφ]`.
-/
theorem map_conjTranspose (φ : K →+* K') (hφ : ∀ x : K, φ (star x) = star (φ x)) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (E.map φ)ᴴ = Eᴴ.map φ := by
  ext i j
  simp [hφ]

omit [StarRing K] [StarRing K'] in
/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv']`. Establish `h1 : (M.map φ).det = φ M.det` using `(φ.map_det M).symm`. Establish `h2 : (M.map φ).adjugate = M.adjugate.map φ` using `(φ.map_adjugate M).symm`. Rewrite using `[h1, h2]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem map_inv' (φ : K →+* K') {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : (M.map φ)⁻¹ = M⁻¹.map φ := by
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv']
  have h1 : (M.map φ).det = φ M.det := (φ.map_det M).symm
  have h2 : (M.map φ).adjugate = M.adjugate.map φ := (φ.map_adjugate M).symm
  rw [h1, h2]
  ext i j
  simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (E.map φ)ᴴ * (Cᴴ * H' * C) * E.map φ := by`. Rewrite using `[hE]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = _ := by rw [hH, map_conjTranspose φ hφ, Matrix.map_mul, Matrix.map_mul]`.
-/
theorem gram_baseChange (φ : K →+* K') (hφ : ∀ x : K, φ (star x) = star (φ x)) {n n' d d' : ℕ}
    (C : Matrix (Fin n') (Fin n) K') (A : Matrix (Fin d') (Fin d) K')
    (H : Matrix (Fin n) (Fin n) K) (H' : Matrix (Fin n') (Fin n') K') (hH : Cᴴ * H' * C = H.map φ)
    (E : Matrix (Fin n) (Fin d) K) (E' : Matrix (Fin n') (Fin d') K') (hE : E' * A = C * E.map φ) :
    Aᴴ * (E'ᴴ * H' * E') * A = (Eᴴ * H * E).map φ := by
  calc Aᴴ * (E'ᴴ * H' * E') * A = (E' * A)ᴴ * H' * (E' * A) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (E.map φ)ᴴ * (Cᴴ * H' * C) * E.map φ := by
        rw [hE]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hH, map_conjTranspose φ hφ, Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Establish `hd : d = d'`. Use `(LinearEquiv.ofBijective A.mulVecLin hA).finrank_eq` as an intermediate fact. Simplify using `using this`. Substitute `hd` using the available equality. Establish `hu : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det A).1 (Matrix.mulVec_injective_iff_isUnit.1 hA.1)`.

Establish `hu' : IsUnit Aᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hu.star`. Establish `h1` using `gram_baseChange φ hφ C A H H' hH E E' hE`. Establish `h2 : (Eᴴ * H).map φ = Aᴴ * (E'ᴴ * H' * C)`. Rewrite using `[Matrix.map_mul, ← map_conjTranspose φ hφ, ← hH]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [← hE]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Unfold `orthPr`. Rewrite using `[Matrix.map_mul, ← map_inv', ← h1, h2, Matrix.mul_inv_rev, Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu']`.
-/
theorem orthPr_baseChange (φ : K →+* K') (hφ : ∀ x : K, φ (star x) = star (φ x)) {n n' d d' : ℕ}
    (C : Matrix (Fin n') (Fin n) K') (A : Matrix (Fin d') (Fin d) K') (hA : Function.Bijective A.mulVec)
    (H : Matrix (Fin n) (Fin n) K) (H' : Matrix (Fin n') (Fin n') K') (hH : Cᴴ * H' * C = H.map φ)
    (E : Matrix (Fin n) (Fin d) K) (E' : Matrix (Fin n') (Fin d') K') (hE : E' * A = C * E.map φ) :
    orthPr H' E' * C = A * (orthPr H E).map φ := by
  have hd : d = d' := by
    have := (LinearEquiv.ofBijective A.mulVecLin hA).finrank_eq
    simpa using this
  subst hd
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 (Matrix.mulVec_injective_iff_isUnit.1 hA.1)
  have hu' : IsUnit Aᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have h1 := gram_baseChange φ hφ C A H H' hH E E' hE
  have h2 : (Eᴴ * H).map φ = Aᴴ * (E'ᴴ * H' * C) := by
    rw [Matrix.map_mul, ← map_conjTranspose φ hφ, ← hH]
    calc (E.map φ)ᴴ * (Cᴴ * H' * C) = (C * E.map φ)ᴴ * H' * C := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hE]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold orthPr
  rw [Matrix.map_mul, ← map_inv', ← h1, h2, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu']

/- English proof (translation)
Unfold `hform`. Rewrite using `[Matrix.toLinearMapₛₗ₂'_apply]`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H *ᵥ y := by
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH, map_mulVec']`. Simplify using `only [dotProduct, map_sum, map_mul, Pi.star_apply, hφ]`.
-/
theorem hform_baseChange (φ : K →+* K') (hφ : ∀ x : K, φ (star x) = star (φ x)) {n n' : ℕ}
    (C : Matrix (Fin n') (Fin n) K')
    (H : Matrix (Fin n) (Fin n) K) (H' : Matrix (Fin n') (Fin n') K') (hH : Cᴴ * H' * C = H.map φ) (x y : Fin n → K) :
    hform H' (C *ᵥ (fun k => φ (x k))) (C *ᵥ (fun k => φ (y k))) = φ (hform H x y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hH, map_mulVec']
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, hφ]

end Coord

section Main

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

/- English proof (translation)
Rewrite using `[CSD.gaMat_eq_lift, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.lift_single]`. Both sides reduce to the same expression.
-/
theorem gaMat_sum_single (S : CSD K) (r : Representation K G S.Forms) {ι : Type} (s : Finset ι) (g : ι → G) (c : ι → K) :
    S.gaMat r (∑ i ∈ s, MonoidAlgebra.single (g i) (c i)) = ∑ i ∈ s, c i • S.actMat r (g i) := by
  rw [CSD.gaMat_eq_lift, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MonoidAlgebra.lift_single]
  rfl

/- English proof (translation)
Simplify using `only [CSD.gaMat_eq_lift, map_sum]`.
-/
theorem gaMat_sum (S : CSD K) (r : Representation K G S.Forms) {ι : Type} (s : Finset ι) (a : ι → MonoidAlgebra K G) :
    S.gaMat r (∑ i ∈ s, a i) = ∑ i ∈ s, S.gaMat r (a i) := by
  simp only [CSD.gaMat_eq_lift, map_sum]

section
variable (φ : K →+* K') (e : G ≃* G') (S : CSD K) (r : Representation K G S.Forms) (S' : CSD K') (r' : Representation K' G' S'.Forms)
  (C : Matrix (Fin S'.dim) (Fin S.dim) K') (hact : ∀ g : G, S'.actMat r' (e g) * C = C * (S.actMat r g).map φ)
include hact

/- English proof (translation)
Establish `: (∑ i ∈ s, c i • S.actMat r (g i)).map φ = ∑ i ∈ s, φ (c i) • (S.actMat r (g i)).map φ`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply]`. Rewrite using `[this, Matrix.sum_mul, Matrix.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hact]`.
-/
theorem sum_baseChange {ι : Type} (s : Finset ι) (g : ι → G) (c : ι → K) :
    (∑ i ∈ s, φ (c i) • S'.actMat r' (e (g i))) * C = C * (∑ i ∈ s, c i • S.actMat r (g i)).map φ := by
  have : (∑ i ∈ s, c i • S.actMat r (g i)).map φ = ∑ i ∈ s, φ (c i) • (S.actMat r (g i)).map φ := by
    ext a b
    simp [Matrix.sum_apply]
  rw [this, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hact]

/- English proof (translation)
Unfold `chiIdem`. Rewrite using `[gaMat_sum_single, gaMat_sum_single, ← sum_baseChange φ e S r S' r' C hact]`. Use `congr 1`. Use `symm`. Use `Fintype.sum_equiv e.toEquiv _ _ fun t => ?_` and prove the remaining obligations.

Simplify using `[Fintype.card_congr e.toEquiv]`.
-/
theorem chiIdem_baseChange (χ : G → K) :
    S'.gaMat r' (chiIdem (fun g => φ (χ (e.symm g)))) * C = C * (S.gaMat r (chiIdem χ)).map φ := by
  unfold chiIdem
  rw [gaMat_sum_single, gaMat_sum_single, ← sum_baseChange φ e S r S' r' C hact]
  congr 1
  symm
  refine Fintype.sum_equiv e.toEquiv _ _ fun t => ?_
  simp [Fintype.card_congr e.toEquiv]

/- English proof (translation)
Unfold `idemOf`. Establish `h : (∑ χ ∈ X, S.gaMat r (chiIdem χ)).map φ = ∑ χ ∈ X, (S.gaMat r (chiIdem χ)).map φ`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply]`. Rewrite using `[gaMat_sum, gaMat_sum, h, Matrix.sum_mul, Matrix.mul_sum]`.

Use `symm`. Use `Finset.sum_bij (fun χ _ => fun g => φ (χ (e.symm g))) (fun χ hχ => (hX _).2 ⟨χ, hχ, rfl⟩) ?_ ?_ ?_` and prove the remaining obligations. Introduce `χ _ χ2 _ h`. Use function extensionality and compare the values at `g`. Use `congrFun h (e g)` as an intermediate fact.

Conclude with `φ.injective (by simpa using this)`. Introduce `χ' h`. Take `⟨χ, hχ, rfl⟩` from `(hX _).1 h`. Conclude with `⟨χ, hχ, rfl⟩`. Introduce `χ _`.

Conclude with `(chiIdem_baseChange φ e S r S' r' C hact χ).symm`.
-/
theorem idemOf_baseChange (X : Finset (G → K)) (X' : Finset (G' → K'))
    (hX : ∀ χ' : G' → K', χ' ∈ X' ↔ ∃ χ ∈ X, χ' = fun g => φ (χ (e.symm g))) :
    S'.gaMat r' (idemOf X') * C = C * (S.gaMat r (idemOf X)).map φ := by
  unfold idemOf
  have h : (∑ χ ∈ X, S.gaMat r (chiIdem χ)).map φ = ∑ χ ∈ X, (S.gaMat r (chiIdem χ)).map φ := by
    ext a b
    simp [Matrix.sum_apply]
  rw [gaMat_sum, gaMat_sum, h, Matrix.sum_mul, Matrix.mul_sum]
  symm
  refine Finset.sum_bij (fun χ _ => fun g => φ (χ (e.symm g))) (fun χ hχ => (hX _).2 ⟨χ, hχ, rfl⟩) ?_ ?_ ?_
  · intro χ _ χ2 _ h
    funext g
    have := congrFun h (e g)
    exact φ.injective (by simpa using this)
  · intro χ' h
    obtain ⟨χ, hχ, rfl⟩ := (hX _).1 h
    exact ⟨χ, hχ, rfl⟩
  · intro χ _
    exact (chiIdem_baseChange φ e S r S' r' C hact χ).symm

/- English proof (translation)
Unfold `lvlIdem`. Rewrite using `[gaMat_sum_single, gaMat_sum_single, ← sum_baseChange φ e S r S' r' C hact]`. Use `congr 1`. Use `symm`. Establish `hc : Nat.card (P.map e.toMonoidHom) = Nat.card P` using `(Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm`.

Use `Fintype.sum_equiv (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv _ _ fun t => ?_` and prove the remaining obligations. Establish `h1 : (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv t = ⟨e t, Subgroup.mem_map_of_mem e.toMonoidHom t.2⟩` using `rfl`. Rewrite using `[h1, hc, map_inv, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hψ]`. Simplify using the standard rewrite rules.
-/
theorem lvlIdem_baseChange (P : Subgroup G) (ψ : P →* Kˣ) (ψ' : P.map e.toMonoidHom →* K'ˣ)
    (hψ : ∀ h : P, ((ψ' ⟨e h, Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ψ h : K)) :
    S'.gaMat r' (lvlIdem (P.map e.toMonoidHom) ψ') * C = C * (S.gaMat r (lvlIdem P ψ)).map φ := by
  classical
  unfold lvlIdem
  rw [gaMat_sum_single, gaMat_sum_single, ← sum_baseChange φ e S r S' r' C hact]
  congr 1
  symm
  have hc : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  refine Fintype.sum_equiv (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv _ _ fun t => ?_
  have h1 : (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv t = ⟨e t, Subgroup.mem_map_of_mem e.toMonoidHom t.2⟩ := rfl
  rw [h1, hc, map_inv, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hψ]
  simp

end

/- English proof (translation)
Introduce `K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s _ h`. Take `⟨⟨C, hC, hH, hact, hnab, hZ⟩, hX, hP, hψ⟩` from `h`. Take `⟨X', P', ψ'⟩` from `ℓ'`. Simplify using `only at hX hP hψ`. Substitute `hP` using the available equality.

Take `⟨m, b, F, hF, hI, hb⟩` from `exists_dual_family φ`. Establish `hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P` using `(Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm`. Establish `hl` using `lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ`. Establish `hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ`. Unfold `goodAt`.

Rewrite using `[(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc, idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]`. Use `set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'`. Take `⟨A0, hA0, hE0⟩` from `subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)`. Take `⟨A1, hA1, hE1⟩` from `subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)`. Express the relevant statement in the definitionally equal form `B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0`.

Express the relevant statement in the definitionally equal form `B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1`. Establish `hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _))` using `comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`. Take `⟨Gm, hGm, hE2⟩` from `subE_baseChange φ A1 hA1.1 _ _ hZ0`. Express the relevant statement in the definitionally equal form `B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2`. Establish `hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ` using `orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1`.

Establish `hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ`. Establish `h1` using `gram_baseChange φ hφ C A1 _ _ hH _ _ hE1`. Express the relevant statement in the definitionally equal form `A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 = ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, h1, hc]`. Generalize the expression as in `(B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]`. Establish `hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ` using `orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2`. Establish `hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ`. Unfold `BlockDat.lPr`.

Rewrite using `[Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1, ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K') ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _))` using `comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`. Use `⟨Gm, hGm, ?_, hform_baseChange φ hφ Gm _ _ (gram_baseChange φ hφ A1 Gm _ _ hHV _ _ hE2)⟩` and prove the remaining obligations. Unfold `BlockDat.Tl matLat`.

Rewrite using `[hN]`. Conclude with `map_baseChange φ A0 Gm _ _ hlPr _`.
-/
theorem defLat_of_blockBC : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ), B.Ok s →
    GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e B B' ℓ ℓ' Z Z' →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x y : Fin (B.dZ ℓ Z) → K, Formalism.DivisionValues.hform (B'.HZ ℓ' Z') (Matrix.mulVec Gm (fun k => φ (x k))) (Matrix.mulVec Gm (fun k => φ (y k))) = φ (Formalism.DivisionValues.hform (B.HZ ℓ Z) x y) := by
  intro K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s _ h
  obtain ⟨⟨C, hC, hH, hact, hnab, hZ⟩, hX, hP, hψ⟩ := h
  obtain ⟨X', P', ψ'⟩ := ℓ'
  dsimp only at hX hP hψ
  subst hP
  obtain ⟨m, b, F, hF, hI, hb⟩ := exists_dual_family φ
  have hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P :=
    (Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hl := lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ
  have hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ := by
    unfold goodAt
    rw [(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc,
      idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]
  set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'
  obtain ⟨A0, hA0, hE0⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)
  obtain ⟨A1, hA1, hE1⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)
  change B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0
  change B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1
  have hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _)) :=
    comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb
      C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨Gm, hGm, hE2⟩ := subE_baseChange φ A1 hA1.1 _ _ hZ0
  change B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2
  have hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ := orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1
  have hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ := by
    have h1 := gram_baseChange φ hφ C A1 _ _ hH _ _ hE1
    change A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 =
      ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ
    rw [Matrix.mul_smul, Matrix.smul_mul, h1, hc]
    generalize (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ := orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2
  have hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ := by
    unfold BlockDat.lPr
    rw [Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1,
      ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K')
      ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _)) :=
    comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb
      C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨Gm, hGm, ?_, hform_baseChange φ hφ Gm _ _ (gram_baseChange φ hφ A1 Gm _ _ hHV _ _ hE2)⟩
  unfold BlockDat.Tl matLat
  rw [hN]
  exact map_baseChange φ A0 Gm _ _ hlPr _

end Main

end GlobalTheory.Mem.R3.DefLatBC

end
