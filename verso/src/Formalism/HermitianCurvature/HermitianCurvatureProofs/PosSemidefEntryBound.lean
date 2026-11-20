import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.A6x2

/- English proof (translation)
The claim follows from `(inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w).symm`.
-/
lemma normsq_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) :
    ((‖w‖ : ℝ) : ℂ) ^ 2 = inner ℂ w w := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w).symm

/- English proof (translation)
Establish `key : ((∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 : ℝ) : ℂ) = (((Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Establish `h1 : ∀ χ : AddChar G ℂ, ((‖∑ g, χ (-g) • v g‖ : ℂ)) ^ 2 = ∑ g, ∑ h, χ (g - h) * inner ℂ (v g) (v h)`. Introduce `χ`. Rewrite using `[normsq_eq_inner, sum_inner]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, inner_smul_right, AddChar.map_neg_eq_conj, Complex.conj_conj, sub_eq_add_neg, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_comm]`. Establish `h2 : ∀ g : G, ∑ χ : AddChar G ℂ, ∑ h, χ (g - h) * inner ℂ (v g) (v h) = (Fintype.card G : ℂ) * (‖v g‖ : ℂ) ^ 2`. Introduce `g`. Rewrite using `[Finset.sum_comm]`.

Repeatedly rewrite using `[← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]`. Rewrite using `[Finset.sum_eq_single g]`. Rewrite using `[if_pos rfl, normsq_eq_inner]`. Introduce `b _ hb`. Rewrite using `[if_neg (Ne.symm hb), zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ g) h`. Repeatedly rewrite using `[h2]`. Rewrite using `[Finset.mul_sum]`. Conclude with `key` after adjusting the coercions.
-/
lemma sum_addChar_norm_sq (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type)
    [AddCommGroup G] [Fintype G] (v : G → E) :
    ∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 := by
  classical
  have key : ((∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 : ℝ) : ℂ) =
      (((Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have h1 : ∀ χ : AddChar G ℂ, ((‖∑ g, χ (-g) • v g‖ : ℂ)) ^ 2 =
        ∑ g, ∑ h, χ (g - h) * inner ℂ (v g) (v h) := by
      intro χ
      rw [normsq_eq_inner, sum_inner]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [inner_smul_left, inner_smul_right, AddChar.map_neg_eq_conj, Complex.conj_conj,
        sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ g : G, ∑ χ : AddChar G ℂ, ∑ h, χ (g - h) * inner ℂ (v g) (v h) =
        (Fintype.card G : ℂ) * (‖v g‖ : ℂ) ^ 2 := by
      intro g
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
      rw [Finset.sum_eq_single g]
      · rw [if_pos rfl, normsq_eq_inner]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ g) h
    simp_rw [h2]
    rw [Finset.mul_sum]
  exact_mod_cast key

/- English proof (translation)
Introduce `E _ _ G _ _ v`. Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `hN : (Fintype.card G : ℝ) ≠ 0`. Establish `: 0 < Fintype.card G` using `Fintype.card_pos_iff.2 ⟨0⟩`. Check the signs of the components of the expression.

Establish `h1 : ∀ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 = ((Fintype.card G : ℝ)⁻¹) ^ 2 * ‖∑ g, χ (-g) • v g‖ ^ 2`. Introduce `χ`. Rewrite using `[norm_smul, mul_pow, norm_inv, Complex.norm_natCast]`. Repeatedly rewrite using `[h1]`. Rewrite using `[← Finset.mul_sum, sum_addChar_norm_sq]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem parsevalGroup : ParsevalGroup := by
  intro E _ _ G _ _ v
  classical
  rw [finsum_eq_sum_of_fintype]
  have hN : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.2 ⟨0⟩
    positivity
  have h1 : ∀ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 =
      ((Fintype.card G : ℝ)⁻¹) ^ 2 * ‖∑ g, χ (-g) • v g‖ ^ 2 := by
    intro χ
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_addChar_norm_sq]
  field_simp

/- English proof (translation)
Introduce `X F k l hk hl a`. Establish `ht : Tendsto (fun j => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y) atTop (𝓝 (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y))` using `tendsto_finsetSum _ fun x hx => tendsto_finsetSum _ fun y hy => (hl x hx y hy).const_mul _`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `(Complex.continuous_im.tendsto _).comp ht`. Establish `h2 : (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) = fun _ => (0 : ℝ)`.

Use function extensionality and compare the values at `j`. Conclude with `(hk j a).1`. Establish `h3 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) atTop (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).im))` using `h1`. Rewrite `h3` using `[h2]`. Conclude with `(tendsto_nhds_unique h3 tendsto_const_nhds)`.

Establish `h1 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).re) atTop (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).re))` using `(Complex.continuous_re.tendsto _).comp ht`. Conclude with `ge_of_tendsto' h1 fun j => (hk j a).2`.
-/
theorem pSDClosed : PSDClosed := by
  intro X F k l hk hl a
  have ht : Tendsto (fun j => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y) atTop
      (𝓝 (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y)) :=
    tendsto_finsetSum _ fun x hx => tendsto_finsetSum _ fun y hy => (hl x hx y hy).const_mul _
  constructor
  · have h1 := (Complex.continuous_im.tendsto _).comp ht
    have h2 : (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) = fun _ => (0 : ℝ) := by
      funext j; exact (hk j a).1
    have h3 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).im)) := h1
    rw [h2] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  · have h1 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).re) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).re)) :=
      (Complex.continuous_re.tendsto _).comp ht
    exact ge_of_tendsto' h1 fun j => (hk j a).2

/- English proof (translation)
Introduce `I _ θ C hC`. Use `Fintype.ofFinite I` as an intermediate fact. Establish `hb : ∀ j, θ j ∈ Metric.closedBall (0 : I → ℂ) (max C 0)`. Introduce `j`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]`.

Conclude with `fun i => (hC j i).trans (le_max_left _ _)`. Take `⟨l, -, φ, hφ, hl⟩` from `tendsto_subseq_of_bounded Metric.isBounded_closedBall hb`. Conclude with `⟨φ, l, hφ, fun i => (tendsto_pi_nhds.1 hl) i⟩`.
-/
theorem boundedSubseq : BoundedSubseq := by
  intro I _ θ C hC
  have := Fintype.ofFinite I
  have hb : ∀ j, θ j ∈ Metric.closedBall (0 : I → ℂ) (max C 0) := by
    intro j
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    exact fun i => (hC j i).trans (le_max_left _ _)
  obtain ⟨l, -, φ, hφ, hl⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hb
  exact ⟨φ, l, hφ, fun i => (tendsto_pi_nhds.1 hl) i⟩

/- English proof (translation)
Rewrite using `[← Matrix.isPositive_toEuclideanLin_iff, LinearMap.isPositive_iff_complex]`. Introduce `v`. Establish `hv : inner ℂ ((Matrix.of fun x y : F => conj (k x y)).toEuclideanLin v) v = ∑ x ∈ F, ∑ y ∈ F, (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) x * conj ((fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) y) * k x y`. Rewrite using `[← Finset.sum_coe_sort F]`. Repeatedly rewrite using `[← Finset.sum_coe_sort F (fun y => _ * k _ y)]`.

Simplify using `[EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv]`. Take `⟨h1, h2⟩` from `h (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0)`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `using h1.symm`.
-/
lemma posSemidef_of_isPSD {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    (Matrix.of fun x y : F => conj (k x y)).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.isPositive_iff_complex]
  intro v
  have hv : inner ℂ ((Matrix.of fun x y : F => conj (k x y)).toEuclideanLin v) v =
      ∑ x ∈ F, ∑ y ∈ F, (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) x *
        conj ((fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) y) * k x y := by
    rw [← Finset.sum_coe_sort F]
    simp_rw [← Finset.sum_coe_sort F (fun y => _ * k _ y)]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv]
  obtain ⟨h1, h2⟩ := h (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0)
  refine ⟨?_, h2⟩
  apply Complex.ext
  · simp
  · simpa using h1.symm

open scoped MatrixOrder in
/- English proof (translation)
Establish `h0` using `(posSemidef_of_isPSD F k h).nonneg`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h0`. Use `⟨fun j x => B j x, fun x y => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun hB x) y`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h1`.

Establish `h2` using `congrArg conj h1`. Rewrite `h2` using `[Complex.conj_conj, map_sum]`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
lemma exists_factor {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    ∃ S : F → F → ℂ, ∀ x y : F, k x y = ∑ j, S j x * conj (S j y) := by
  classical
  have h0 := (posSemidef_of_isPSD F k h).nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h0
  refine ⟨fun j x => B j x, fun x y => ?_⟩
  have h1 := congrFun (congrFun hB x) y
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at h1
  have h2 := congrArg conj h1
  rw [Complex.conj_conj, map_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/- English proof (translation)
Introduce `X F G Gc h1 h2`. Take `⟨S1, hS1⟩` from `exists_factor F Gc h1`. Take `⟨S2, hS2⟩` from `exists_factor F _ h2`. Set `e : (F ⊕ F) ≃ Fin (Fintype.card (F ⊕ F))` to `Fintype.equivFin _`. Set `u : X → EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F)))` to `fun x => WithLp.toLp 2 (fun i => if hx : x ∈ F then Sum.elim (fun j => S1 j ⟨x, hx⟩) (fun j => S2 j ⟨x, hx⟩) (e.symm i) else 0)`.

Set `d : Fin (Fintype.card (F ⊕ F)) → ℂ` to `fun i => if (e.symm i).isLeft then 1 else 0`. Set `T : EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) →ₗ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F)))` to `{ toFun := fun v => WithLp.toLp 2 (fun i => d i * v i) map_add' := by`. Introduce `v w`. Use extensionality with `i`. Simplify using `[mul_add]`.

Use the proof step `map_smul' := by`. Introduce `c v`. Use extensionality with `i`. Simplify using the standard rewrite rules. Use `ring }`.

Use `⟨_, u, T, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Use `Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Use `show ‖d i * v i‖ ^ 2 ≤ ‖v i‖ ^ 2`.

Distinguish the cases in `hi : (e.symm i).isLeft`. Simplify using `[d, hi]`. Simplify using `[d, hi]`. Introduce `x hx y hy`. Rewrite using `[PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]`.

Establish `h3` using `hS1 ⟨x, hx⟩ ⟨y, hy⟩`. Establish `h4` using `hS2 ⟨x, hx⟩ ⟨y, hy⟩`. Simplify using `only [Finset.univ_eq_attach] at h3 h4`. Simplify using `only [u, hx, hy, dite_true, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, RCLike.inner_apply, Finset.univ_eq_attach]`. Rewrite using `[← h3, ← h4]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x hx y hy`. Rewrite using `[PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]`. Establish `h3` using `hS1 ⟨x, hx⟩ ⟨y, hy⟩`. Simplify using `only [Finset.univ_eq_attach] at h3`.

Simplify using `[u, T, d, hx, hy]`. Conclude with `h3.symm`.
-/
theorem gramRealiseCut : GramRealiseCut := by
  intro X F G Gc h1 h2
  classical
  obtain ⟨S1, hS1⟩ := exists_factor F Gc h1
  obtain ⟨S2, hS2⟩ := exists_factor F _ h2
  let e : (F ⊕ F) ≃ Fin (Fintype.card (F ⊕ F)) := Fintype.equivFin _
  let u : X → EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) := fun x =>
    WithLp.toLp 2 (fun i => if hx : x ∈ F then
      Sum.elim (fun j => S1 j ⟨x, hx⟩) (fun j => S2 j ⟨x, hx⟩) (e.symm i) else 0)
  let d : Fin (Fintype.card (F ⊕ F)) → ℂ := fun i => if (e.symm i).isLeft then 1 else 0
  let T : EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) :=
    { toFun := fun v => WithLp.toLp 2 (fun i => d i * v i)
      map_add' := by
        intro v w; ext i; simp [mul_add]
      map_smul' := by
        intro c v; ext i; simp; ring }
  refine ⟨_, u, T, ?_, ?_, ?_⟩
  · intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    show ‖d i * v i‖ ^ 2 ≤ ‖v i‖ ^ 2
    by_cases hi : (e.symm i).isLeft
    · simp [d, hi]
    · simp [d, hi]
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    have h4 := hS2 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3 h4
    simp only [u, hx, hy, dite_true, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      RCLike.inner_apply, Finset.univ_eq_attach]
    rw [← h3, ← h4]
    ring
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3
    simp [u, T, d, hx, hy]
    exact h3.symm

/- English proof (translation)
Introduce `X F k M h1 h2 x hx y hy`. Take `⟨n, u, T, hT, hG, hGc⟩` from `gramRealiseCut X F M k h1 h2`. Establish `hn : ∀ z ∈ F, ‖u z‖ ^ 2 = (M z z).re`. Introduce `z hz`. Rewrite using `[← hG z hz z hz]`.

Conclude with `(inner_self_eq_norm_sq (𝕜 := ℂ) (u z)).symm`. Rewrite using `[← hGc x hx y hy, ← hn x hx, ← hn y hy, ← mul_pow]`. Establish `h3 : ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖u x‖ * ‖u y‖`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h3 2`.
-/
theorem pSDEntryBound : PSDEntryBound := by
  intro X F k M h1 h2 x hx y hy
  obtain ⟨n, u, T, hT, hG, hGc⟩ := gramRealiseCut X F M k h1 h2
  have hn : ∀ z ∈ F, ‖u z‖ ^ 2 = (M z z).re := by
    intro z hz
    rw [← hG z hz z hz]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u z)).symm
  rw [← hGc x hx y hy, ← hn x hx, ← hn y hy, ← mul_pow]
  have h3 : ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖u x‖ * ‖u y‖ :=
    calc ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖T (u y)‖ * ‖T (u x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u y‖ * ‖u x‖ := mul_le_mul (hT _) (hT _) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u x‖ * ‖u y‖ := mul_comm _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

end Formalism.FourierDecayAlt.P.A6x2

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `A6x2.parsevalGroup`.
-/
theorem parsevalGroup_statement : Formalism.FourierDecayAlt.A6.ParsevalGroup := A6x2.parsevalGroup

/- English proof (translation)
The claim follows from `A6x2.gramRealiseCut`.
-/
theorem gramRealisation : Formalism.FourierDecayAlt.A6.GramRealiseCut := A6x2.gramRealiseCut

/- English proof (translation)
The claim follows from `A6x2.pSDEntryBound`.
-/
theorem posSemidefEntryBound : Formalism.FourierDecayAlt.A6.PSDEntryBound := A6x2.pSDEntryBound

/- English proof (translation)
The claim follows from `A6x2.pSDClosed`.
-/
theorem posSemidefClosed : Formalism.FourierDecayAlt.A6.PSDClosed := A6x2.pSDClosed

/- English proof (translation)
The claim follows from `A6x2.boundedSubseq`.
-/
theorem boundedSubsequence : Formalism.FourierDecayAlt.A6.BoundedSubseq := A6x2.boundedSubseq

end Formalism.FourierDecayAlt.P
