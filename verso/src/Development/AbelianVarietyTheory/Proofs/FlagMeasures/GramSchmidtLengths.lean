import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramFlag

open InnerProductSpace in

/- English proof (translation)
Establish `h` using `gramSchmidt_def'' (𝕜 := ℂ) f a`. Establish `hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a, (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i`. Rewrite using `[sub_eq_iff_eq_add']`. Conclude with `h`. Rewrite using `[hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]`.

Conclude with `Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)`.
-/
theorem sub_gs_mem {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r) :
    f a - gramSchmidt ℂ f a ∈ Submodule.span ℂ (f '' Set.Iio a) := by
  have h := gramSchmidt_def'' (𝕜 := ℂ) f a
  have hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a,
      (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i := by
    rw [sub_eq_iff_eq_add']
    exact h
  rw [hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)

open InnerProductSpace in

/- English proof (translation)
Establish `horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0`. Introduce `v hv`. Rewrite `hv` using `[← span_gramSchmidt_Iio (𝕜 := ℂ) f a]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, hi, rfl⟩` from `hy`. Conclude with `gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))`. Consider the case `zero => exact inner_zero_right _`. Consider the case `add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]`. Consider the case `smul c y _ hy => rw [inner_smul_right, hy, mul_zero]`.

Establish `hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a)` using `Submodule.sub_mem _ (sub_gs_mem f a) hw`. Establish `hpy` using `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)`. Establish `heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w` using `by abel`. Rewrite `hpy` using `[heq]`. Use polynomial arithmetic with `[norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w), mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]`.
-/
theorem norm_gs_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r)
    {w : E} (hw : w ∈ Submodule.span ℂ (f '' Set.Iio a)) : ‖gramSchmidt ℂ f a‖ ≤ ‖f a - w‖ := by
  have horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0 := by
    intro v hv
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) f a] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))
    | zero => exact inner_zero_right _
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  have hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a) :=
    Submodule.sub_mem _ (sub_gs_mem f a) hw
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)
  have heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w := by abel
  rw [heq] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w),
    mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]

open InnerProductSpace in

/- English proof (translation)
Use `choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)`. Use `⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ b, a ≤ b → l a b = 0`. Introduce `b hab`. Assume the negation of the conclusion as `hne`.

Establish `hb` using `(Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))`. Conclude with `absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)`. Establish `hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b`. Introduce `b`. Break down `lt_trichotomy b a with hba | hba | hba` into its components or cases.

Simplify using `[upper, hba, hba.ne]`. Substitute `hba` using the available equality. Simplify using `[upper, hz b le_rfl]`. Simplify using `[upper, not_lt.2 hba.le, hba.ne', hz b hba.le]`. Establish `hsum` using `hlx a`.

Rewrite `hsum` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))]`. Repeatedly rewrite using `[hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsum, sub_sub_cancel]`.
-/
theorem exists_upper {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) :
    ∃ u : UT r → ℂ, ∀ a, ∑ b, upper u b a • f b = gramSchmidt ℂ f a := by
  classical
  choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)
  refine ⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩
  have hz : ∀ b, a ≤ b → l a b = 0 := by
    intro b hab
    by_contra hne
    have hb := (Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    exact absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)
  have hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b := by
    intro b
    rcases lt_trichotomy b a with hba | hba | hba
    · simp [upper, hba, hba.ne]
    · subst hba
      simp [upper, hz b le_rfl]
    · simp [upper, not_lt.2 hba.le, hba.ne', hz b hba.le]
  have hsum := hlx a
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))] at hsum
  simp_rw [hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hsum, sub_sub_cancel]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, eucl]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_norm_sq]`.
-/
theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

/- English proof (translation)
Introduce `k r z x hx`. Establish `hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det`. Take `⟨-, hsq, -⟩` from `Formalism.QuantumDeterminants.hpkFacts k r`. Establish `h` using `congrArg Matrix.det hsq`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`.

Conclude with `isUnit_iff_exists_inv.2 ⟨_, h⟩`. Establish `hxu : IsUnit x.det` using `((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1`. Set `L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1))` to `(WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹`. Establish `hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v)` using `fun v => rfl`. Set `e : Fin r → Fin (2 * r + k + 1) → ℂ` to `fun b => bvec (eI k r b)`.

Set `F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1))` to `fun b => L (e b)`. Establish `hLinj : Function.Injective L`. Introduce `v w hvw`. Rewrite `hvw` using `[hLapp, hLapp]`. Establish `h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w` using `congrArg WithLp.ofLp hvw`.

Establish `h2` using `congrArg (fun t => x *ᵥ t) h1`. Simplify `h2` using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu]`. Establish `heinj : Function.Injective (eI k r)` using `fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')`. Establish `hlie : LinearIndependent ℂ e`. Establish `h0` using `(Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj`.

Use `h0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`. Simplify using `[e, bvec]`. Establish `hli : LinearIndependent ℂ F` using `hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)`. Take `⟨u, hu⟩` from `exists_upper F`.

Establish `hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a`. Introduce `a`. Establish `htl : ∀ v : Fin (2 * r + k + 1) → ℂ, WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v` using `fun v => rfl`. Rewrite using `[← hu a, htl, map_sum]`. Simplify using `only [map_smul]`.

Both sides reduce to the same expression. Establish `hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} => bvec (eI k r b.1)) = e '' Set.Iio a`. Introduce `a`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨b.1, b.2, rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨⟨b, hb⟩, rfl⟩`. Establish `hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖`.

Introduce `a`. Establish `hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a`. Rewrite using `[Formalism.QuantumDeterminants.fvec, dif_pos (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]`. Both sides reduce to the same expression. Establish `hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L`.

Rewrite using `[Submodule.map_span, Set.image_image]`. Unfold `lA`. Rewrite using `[hf, hset a]`. Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Establish `hm` using `sub_gs_mem F a`. Rewrite `hm` using `[hspan]`. Take `⟨y, hy, hyL⟩` from `Submodule.mem_map.1 hm`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[eucl_eq, ← hLapp, map_sub, hyL]`.

Use `show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖`. Rewrite using `[sub_sub_cancel]`. Introduce and unpack `t ⟨y, hy, rfl⟩`. Rewrite using `[eucl_eq, ← hLapp, map_sub]`. Conclude with `norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)`.

Use `⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩` and prove the remaining obligations. Rewrite using `[hlA a]`. Conclude with `norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)`. Rewrite using `[dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']`. Conclude with `InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'`.
-/
theorem gramSchmidt_lengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), ∀ x ∈ GG k r, ∃ u : UT r → ℂ, (∀ a : Fin r, eucl (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = lA k r z x a.castSucc ∧ 0 < lA k r z x a.castSucc) ∧ ∀ a a' : Fin r, a ≠ a' → star (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) ⬝ᵥ (∑ b, upper u b a' • (x⁻¹ *ᵥ bvec (eI k r b))) = 0 := by
  intro k r z x hx
  classical
  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    obtain ⟨-, hsq, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
    have h := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hxu : IsUnit x.det := ((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹
  have hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v) := fun v => rfl
  let e : Fin r → Fin (2 * r + k + 1) → ℂ := fun b => bvec (eI k r b)
  let F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => L (e b)
  have hLinj : Function.Injective L := by
    intro v w hvw
    rw [hLapp, hLapp] at hvw
    have h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w := congrArg WithLp.ofLp hvw
    have h2 := congrArg (fun t => x *ᵥ t) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu] using h2
  have heinj : Function.Injective (eI k r) := fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')
  have hlie : LinearIndependent ℂ e := by
    have h0 := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj
    convert h0 using 1
    funext b
    simp [e, bvec]
  have hli : LinearIndependent ℂ F := hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)
  obtain ⟨u, hu⟩ := exists_upper F
  have hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a := by
    intro a
    have htl : ∀ v : Fin (2 * r + k + 1) → ℂ,
        WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v := fun v => rfl
    rw [← hu a, htl, map_sum]
    simp only [map_smul]
    rfl
  have hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} =>
      bvec (eI k r b.1)) = e '' Set.Iio a := by
    intro a
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖ := by
    intro a
    have hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a := by
      rw [Formalism.QuantumDeterminants.fvec, dif_pos (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]
      rfl
    have hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L := by
      rw [Submodule.map_span, Set.image_image]
    unfold lA
    rw [hf, hset a]
    apply IsLeast.csInf_eq
    constructor
    · have hm := sub_gs_mem F a
      rw [hspan] at hm
      obtain ⟨y, hy, hyL⟩ := Submodule.mem_map.1 hm
      refine ⟨y, hy, ?_⟩
      rw [eucl_eq, ← hLapp, map_sub, hyL]
      show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖
      rw [sub_sub_cancel]
    · rintro t ⟨y, hy, rfl⟩
      rw [eucl_eq, ← hLapp, map_sub]
      exact norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)
  refine ⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩
  · rw [hlA a]
    exact norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)
  · rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']
    exact InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'

end GlobalTheory.Amp.GramFlag
