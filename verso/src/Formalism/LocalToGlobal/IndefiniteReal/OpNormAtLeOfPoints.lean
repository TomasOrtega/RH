import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag

open Module NumberField Matrix

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace BlockMetrics

section Forms

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

/- English proof (translation)
Establish `h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]`.
-/
theorem fc_smul (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]

def fcA : V →+ (ι → ℂ) :=
  AddMonoidHom.mk' (Formalism.HermitianLatticesTheory.fcoord b X v) (Formalism.HermitianLatticesTheory.fcoord_add b X v)

/- English proof (translation)
Conclude with `map_sum (fcA b X v) f s`.
-/
theorem fc_sum {α : Type} (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ a ∈ s, f a) = ∑ a ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f a) := by
  exact map_sum (fcA b X v) f s

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_sum_left {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_sum_right {α : Type} (s : Finset α) (c : α → K) (f : α → V) (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (∑ a ∈ s, c a • f a) =
      ∑ a ∈ s, v.embedding (c a) * Formalism.HermitianLatticesTheory.majAt b X v x (f a) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem maj_add_left (x x' y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (x + x') y = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x' y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem maj_add_right (x y y' : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + y') = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x y' := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_smul_left (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  ring

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_smul_right (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Complex.conj_mul' _`.
-/
theorem maj_self (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _

/- English proof (translation)
Rewrite using `[maj_self, Complex.ofReal_re, Real.sqrt_sq]`. Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`. Conclude with `Real.sqrt_nonneg _`.
-/
theorem normAt_eq_sqrt (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [maj_self, Complex.ofReal_re, Real.sqrt_sq]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  exact Real.sqrt_nonneg _

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `[Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`.
-/
theorem normAt_eq_norm (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

/- English proof (translation)
Establish `hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) = ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt]`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]`. Both sides reduce to the same expression.

Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]`.
-/
theorem fcoord_map (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) =
      ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]
    rfl
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]

end Forms

/- English proof (translation)
Break down `Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hr : ComplexEmbedding.IsReal v.embedding`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Establish `hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure` using `v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)`. Rewrite `hx` using `[h]`. Take `⟨r, hr⟩` from `RingHom.mem_fieldRange.1 hx`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hr]`. Simplify using the standard rewrite rules.

Conclude with `(InfinitePlace.isComplex_iff.1 hv) hr`. Introduce `z`. Establish `hz : z ∈ v.embedding.fieldRange.topologicalClosure`. Rewrite using `[h]`. Conclude with `Subfield.mem_top z`.

Establish `hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding)`. Rewrite using `[← RingHom.coe_fieldRange]`. Both sides reduce to the same expression. Rewrite using `[← hc]`. Conclude with `hz`.
-/
theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h
  · exfalso
    have hr : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
        v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)
      rw [h] at hx
      obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.1 hx
      rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
      simp
    exact (InfinitePlace.isComplex_iff.1 hv) hr
  · intro z
    have hz : z ∈ v.embedding.fieldRange.topologicalClosure := by
      rw [h]; exact Subfield.mem_top z
    have hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding) := by
      rw [← RingHom.coe_fieldRange]; rfl
    rw [← hc]; exact hz

/- English proof (translation)
Establish `hemb : DenseRange v.embedding` using `dense_emb v (IsTotallyComplex.isComplex v)`. Establish `h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x`. Establish `hpi : DenseRange (Pi.map fun _ : ι => v.embedding)` using `DenseRange.piMap fun _ => hemb`. Establish `hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) = Set.range (Pi.map fun _ : ι => v.embedding)`. Use extensionality with `u`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨fun i => b.repr x i, rfl⟩`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨b.equivFun.symm c, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `hc` using `congr_fun (b.equivFun.apply_symm_apply c) i`. Rewrite `hc` using `[Basis.equivFun_apply]`. Use `show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)`. Rewrite using `[hc]`.

Rewrite using `[DenseRange, hr]`. Conclude with `hpi`. Establish `h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι)` using `by fun_prop`. Establish `h3 : Function.Surjective fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι)`. Introduce `w`.

Use `⟨(X v).mulVec (WithLp.ofLp w), ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]`. Conclude with `h3.denseRange.comp h1 h2`.
-/
theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have hemb : DenseRange v.embedding := dense_emb v (IsTotallyComplex.isComplex v)
  have h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x := by
    have hpi : DenseRange (Pi.map fun _ : ι => v.embedding) := DenseRange.piMap fun _ => hemb
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (Pi.map fun _ : ι => v.embedding) := by
      ext u; constructor
      · rintro ⟨x, rfl⟩; exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨b.equivFun.symm c, ?_⟩
        funext i
        have hc := congr_fun (b.equivFun.apply_symm_apply c) i
        rw [Basis.equivFun_apply] at hc
        show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)
        rw [hc]
    rw [DenseRange, hr]; exact hpi
  have h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have h3 : Function.Surjective fun u : ι → ℂ =>
      (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    intro w
    refine ⟨(X v).mulVec (WithLp.ofLp w), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
  exact h3.denseRange.comp h1 h2

/- English proof (translation)
Unfold `Formalism.HN.opNormAt`. Use `set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd`. Use `ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_` and prove the remaining obligations. Use `(dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_le (by fun_prop) (by fun_prop)`.

Introduce `f`. Establish `hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) = WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f))`. Rewrite using `[fcoord_map b X v hX φ f]`. Both sides reduce to the same expression. Use `show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖`.

Rewrite using `[hT, ← normAt_eq_norm, ← normAt_eq_norm]`. Conclude with `h f`.
-/
theorem opNormAt_le_of_points {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd
  refine ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_
  refine (dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) =
        WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f)) := by
      rw [fcoord_map b X v hX φ f]; rfl
    show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖
    rw [hT, ← normAt_eq_norm, ← normAt_eq_norm]
    exact h f

/- English proof (translation)
Take `⟨a, ha⟩` from `hσ`. Take `⟨F1, F2, F3, F4⟩` from `hF`. Take `⟨G1, G2, G3, G4⟩` from `hG`. Establish `e1` using `h (x + y)`. Establish `e2` using `h (a • x + y)`.

Simplify using `only [F1, F2, F3, F4, G1, G2, G3, G4] at e1 e2`. Rewrite `e1`, `e2` using `[h x, h y]`. Establish `hne : starRingEnd ℂ (σ a) - σ a ≠ 0`. Introduce `h0`. Apply `ha` to reduce the goal to its premises.

Use `congrArg Complex.im h0` as an intermediate fact. Simplify using `only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : (starRingEnd ℂ (σ a) - σ a) * (F x y - G x y) = 0`. Take the linear combination `e2 - σ a * e1`.

Break down `mul_eq_zero.1 key with h0 | h0` into its components or cases. Conclude with `absurd h0 hne`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem sesq_ext {K V : Type} [Field K] [AddCommGroup V] [Module K V] {F G : V → V → ℂ}
    {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨F1, F2, F3, F4⟩ := hF
  obtain ⟨G1, G2, G3, G4⟩ := hG
  have e1 := h (x + y)
  have e2 := h (a • x + y)
  simp only [F1, F2, F3, F4, G1, G2, G3, G4] at e1 e2
  rw [h x, h y] at e1 e2
  have hne : starRingEnd ℂ (σ a) - σ a ≠ 0 := by
    intro h0
    apply ha
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have key : (starRingEnd ℂ (σ a) - σ a) * (F x y - G x y) = 0 := by
    linear_combination e2 - σ a * e1
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

/- English proof (translation)
Establish `hv` using `IsTotallyComplex.isComplex v`. Rewrite `hv` using `[InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hv` to reduce the goal to its premises.

Use extensionality with `a`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.2 (hcon a)`.
-/
theorem exists_im_ne_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (v : InfinitePlace K) : ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hv := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hv
  by_contra hcon
  push_neg at hcon
  apply hv
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

end BlockMetrics

open BlockMetrics

/- English proof (translation)
Rewrite using `[normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]`.
-/
private theorem normAt_smul_indefinite_real {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (a • x) = ‖v.embedding a‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]

/- English proof (translation)
Rewrite using `[normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]`. Conclude with `norm_add_le _ _`.
-/
private theorem normAt_add_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  rw [normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]
  exact norm_add_le _ _

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)`.
-/
private theorem normAt_finset_sum_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {α : Type} (s : Finset α)
    (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU`. Establish `hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y`. Introduce `g y`. Use `show (ρ g * ρ g⁻¹) y = y`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`.

Both sides reduce to the same expression. Establish `hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V), Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y)`. Introduce `v g x y`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩` and prove the remaining obligations.

Establish `hc` using `fun g => (charFacts K G T τ g).2 v.embedding`. Establish `hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) = v.embedding (charOf τ 1 / (Fintype.card G : K))`. Establish `h1` using `(hc 1).1`. Rewrite `h1` using `[inv_one]`. Simplify using `only [map_div₀, map_natCast]`.

Rewrite using `[starRingEnd_apply, ← h1]`. Simplify using `only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]`. Rewrite using `[maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_` and prove the remaining obligations.

Establish `hg` using `(hc g⁻¹).1`. Rewrite `hg` using `[inv_inv]`. Simplify using `only [Equiv.inv_apply, inv_inv]`. Rewrite using `[hρ, ← hg]`. Establish `hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z`.

Introduce `k z`. Rewrite using `[normAt_eq_sqrt, hU, ← normAt_eq_sqrt]`. Establish `hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1`. Introduce `h`. Rewrite using `[InfinitePlace.norm_embedding_eq]`.

Establish `ht : χ h⁻¹ ∈ NumberField.Units.torsion K` using `χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)`. Conclude with `(NumberField.Units.mem_torsion K).1 ht v`. Use `opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_` and prove the remaining obligations. Rewrite using `[one_mul, LinearMap.comp_apply]`. Simplify using `only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]`.

Rewrite using `[normAt_smul_indefinite_real]`. Use `(mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_` and prove the remaining obligations. Simplify using `only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]`. Rewrite using `[Fintype.card_eq_nat_card, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]`.
-/
theorem metric : Metric := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU
  have hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y := by
    intro g y
    show (ρ g * ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := by
    intro v g x y
    calc Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y
        = Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [hinv]
      _ = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := hU v g x _
  refine ⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩
  · have hc := fun g => (charFacts K G T τ g).2 v.embedding
    have hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) =
        v.embedding (charOf τ 1 / (Fintype.card G : K)) := by
      have h1 := (hc 1).1
      rw [inv_one] at h1
      simp only [map_div₀, map_natCast]
      rw [starRingEnd_apply, ← h1]
    simp only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hg := (hc g⁻¹).1
    rw [inv_inv] at hg
    simp only [Equiv.inv_apply, inv_inv]
    rw [hρ, ← hg]
  · have hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z := by
      intro k z; rw [normAt_eq_sqrt, hU, ← normAt_eq_sqrt]
    have hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
      intro h
      rw [InfinitePlace.norm_embedding_eq]
      have ht : χ h⁻¹ ∈ NumberField.Units.torsion K := χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)
      exact (NumberField.Units.mem_torsion K).1 ht v
    refine opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_
    rw [one_mul, LinearMap.comp_apply]
    simp only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [normAt_smul_indefinite_real]
    refine (mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_
    simp only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
    rw [Fintype.card_eq_nat_card, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hn v g x y`. Use `sesq_ext (F := fun x y => Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g y)) (G := Formalism.HermitianLatticesTheory.majAt b X v) (σ := v.embedding) (exists_im_ne_zero v) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ x y` and prove the remaining obligations. Introduce `x x' y`. Simplify using `only [map_add]`. Conclude with `maj_add_left b X v _ _ _`.

Introduce `x y y'`. Simplify using `only [map_add]`. Conclude with `maj_add_right b X v _ _ _`. Introduce `a x y`. Simplify using `only [map_smul]`.

Conclude with `maj_smul_left b X v _ _ _`. Introduce `a x y`. Simplify using `only [map_smul]`. Conclude with `maj_smul_right b X v _ _ _`. Conclude with `fun x x' y => maj_add_left b X v _ _ _`.

Conclude with `fun x y y' => maj_add_right b X v _ _ _`. Conclude with `fun a x y => maj_smul_left b X v _ _ _`. Conclude with `fun a x y => maj_smul_right b X v _ _ _`. Introduce `z show Formalism.HermitianLatticesTheory.majAt b X v (ρ g z) (ρ g z) = Formalism.HermitianLatticesTheory.majAt b X v z z`. Rewrite using `[maj_self, maj_self, hn]`.
-/
theorem unitOfNorm : UnitOfNorm := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hn v g x y
  refine sesq_ext (F := fun x y => Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g y))
    (G := Formalism.HermitianLatticesTheory.majAt b X v) (σ := v.embedding) (exists_im_ne_zero v)
    ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ x y
  · intro x x' y; simp only [map_add]; exact maj_add_left b X v _ _ _
  · intro x y y'; simp only [map_add]; exact maj_add_right b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_left b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_right b X v _ _ _
  · exact fun x x' y => maj_add_left b X v _ _ _
  · exact fun x y y' => maj_add_right b X v _ _ _
  · exact fun a x y => maj_smul_left b X v _ _ _
  · exact fun a x y => maj_smul_right b X v _ _ _
  · intro z
    show Formalism.HermitianLatticesTheory.majAt b X v (ρ g z) (ρ g z) = Formalism.HermitianLatticesTheory.majAt b X v z z
    rw [maj_self, maj_self, hn]

end Formalism.IndefR.LatticeTransfer
