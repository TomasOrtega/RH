import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll

noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

/- English proof (translation)
Establish `h1` using `Finset.sum_range_succ (fun j => f (a ^ j)) q`. Establish `h2` using `Finset.sum_range_succ' (fun j => f (a ^ j)) q`. Rewrite `h2` using `[h1, h, pow_zero]`. Conclude with `(add_right_cancel h2).symm`.
-/
private theorem sum_pow_fix {α M : Type} [Monoid α] [AddCommGroup M] (a : α) (q : ℕ) (h : a ^ q = 1) (f : α → M) :
    ∑ j ∈ Finset.range q, f (a ^ (j + 1)) = ∑ j ∈ Finset.range q, f (a ^ j) := by
  have h1 := Finset.sum_range_succ (fun j => f (a ^ j)) q
  have h2 := Finset.sum_range_succ' (fun j => f (a ^ j)) q
  rw [h1, h, pow_zero] at h2
  exact (add_right_cancel h2).symm

/- English proof (translation)
Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Rewrite using `[Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]]`. Simplify using `[hq]`.
-/
private theorem sep_sum {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ) (hq : 0 < q)
    {t : ℕ} (x y : Fin t → R) (h : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    {M : Type} [AddCommGroup M] [Module R M] (v : ℕ → M) :
    ∑ i, x i • ∑ j ∈ Finset.range q, (σ ^ j) (y i) • v j = v 0 := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]]
  simp [hq]

/- English proof (translation)
Introduce `k R _ _ _ σ q hG M _ _ _ _ s hs hq`. Take `⟨t, x, y, hxy⟩` from `hG.sep`. Establish `hsj : ∀ (j : ℕ) (r : R) (m : M), (s ^ j) (r • m) = (σ ^ j) r • (s ^ j) m`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro r m`. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `r m`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, AlgEquiv.mul_apply, ih, hs]`.

Establish `hfix : ∀ (n : M), s n = n → ∀ j : ℕ, (s ^ j) n = n`. Introduce `n hn j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hn]`.

Establish `hT : ∀ m : M, (∑ j ∈ Finset.range q, s ^ j) m ∈ LinearMap.eqLocus s LinearMap.id`. Introduce `m`. Rewrite using `[LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.sum_apply, map_sum, ← sum_pow_fix s q hq fun a => a m]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [pow_succ', Module.End.mul_apply]`. Establish `htr : ∀ r : R, ∃ c : k, algebraMap k R c = ∑ j ∈ Finset.range q, (σ ^ j) r`.

Introduce `r`. Use `hG.fix _ ?_` and prove the remaining obligations. Rewrite using `[map_sum, ← sum_pow_fix σ q hG.pow fun a => a r]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]`. Use `choose c hc using htr`.

Set `T : M →ₗ[k] LinearMap.eqLocus s LinearMap.id` to `LinearMap.codRestrict _ _ hT`. Establish `hTv : ∀ m, (T m : M) = ∑ j ∈ Finset.range q, (s ^ j) m` using `fun m => LinearMap.sum_apply _ _ _`. Set `g : M →ₗ[k] R ⊗[k] LinearMap.eqLocus s LinearMap.id` to `∑ i, (TensorProduct.mk k R _ (x i)).comp (T.comp (Algebra.lsmul k k M (y i)))`. Establish `hg : ∀ m, g m = ∑ i, x i ⊗ₜ[k] T (y i • m)` using `fun m => LinearMap.sum_apply _ _ _`. Use `Function.bijective_iff_has_inverse.2 ⟨g, fun z => ?_, fun m => ?_⟩` and prove the remaining obligations.

Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `tmul r n`. Establish `h1 : ∀ i, T (y i • r • (n : M)) = c (y i * r) • n`.

Introduce `i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hTv, Submodule.coe_smul, ← algebraMap_smul R (c _), hc, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hsj, hfix n n.2]`. Establish `h2 : ∑ i, c (y i * r) • x i = r`.

Use `sep_sum σ q hG.pos x y hxy (M := R) fun j => (σ ^ j) r` as an intermediate fact. Simplify using `only [pow_zero, AlgEquiv.one_apply] at this`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hc, smul_eq_mul, mul_comm]`. Simplify using `only [map_mul, smul_eq_mul]`.

Establish `h3 : TensorProduct.lift ((Algebra.lsmul k k M (A` using `R)).toLinearMap.compl₂ (LinearMap.eqLocus s LinearMap.id).subtype) (r ⊗ₜ[k] n) = r • (n : M) := rfl`. Rewrite using `[h3, hg]`. Repeatedly rewrite using `[h1, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, h2]`. Rewrite using `[hg, map_sum]`. Use `sep_sum σ q hG.pos x y hxy fun j => (s ^ j) m` as an intermediate fact.

Simplify using `only [pow_zero, Module.End.one_apply] at this`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x i • (T (y i • m) : M) = _`. Rewrite using `[hTv]`. Simplify using `only [hsj]`.
-/
theorem descent : Descent := by
  intro k R _ _ _ σ q hG M _ _ _ _ s hs hq
  obtain ⟨t, x, y, hxy⟩ := hG.sep
  have hsj : ∀ (j : ℕ) (r : R) (m : M), (s ^ j) (r • m) = (σ ^ j) r • (s ^ j) m := by
    intro j
    induction j with
    | zero => intro r m; simp
    | succ j ih =>
      intro r m
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, AlgEquiv.mul_apply, ih, hs]
  have hfix : ∀ (n : M), s n = n → ∀ j : ℕ, (s ^ j) n = n := by
    intro n hn j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hn]
  have hT : ∀ m : M, (∑ j ∈ Finset.range q, s ^ j) m ∈ LinearMap.eqLocus s LinearMap.id := by
    intro m
    rw [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.sum_apply, map_sum,
      ← sum_pow_fix s q hq fun a => a m]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', Module.End.mul_apply]
  have htr : ∀ r : R, ∃ c : k, algebraMap k R c = ∑ j ∈ Finset.range q, (σ ^ j) r := by
    intro r
    refine hG.fix _ ?_
    rw [map_sum, ← sum_pow_fix σ q hG.pow fun a => a r]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]
  choose c hc using htr
  let T : M →ₗ[k] LinearMap.eqLocus s LinearMap.id := LinearMap.codRestrict _ _ hT
  have hTv : ∀ m, (T m : M) = ∑ j ∈ Finset.range q, (s ^ j) m := fun m => LinearMap.sum_apply _ _ _
  let g : M →ₗ[k] R ⊗[k] LinearMap.eqLocus s LinearMap.id :=
    ∑ i, (TensorProduct.mk k R _ (x i)).comp (T.comp (Algebra.lsmul k k M (y i)))
  have hg : ∀ m, g m = ∑ i, x i ⊗ₜ[k] T (y i • m) := fun m => LinearMap.sum_apply _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨g, fun z => ?_, fun m => ?_⟩
  · induction z with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul r n =>
      have h1 : ∀ i, T (y i • r • (n : M)) = c (y i * r) • n := by
        intro i
        apply Subtype.ext
        rw [hTv, Submodule.coe_smul, ← algebraMap_smul R (c _), hc, Finset.sum_smul, smul_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [hsj, hfix n n.2]
      have h2 : ∑ i, c (y i * r) • x i = r := by
        have := sep_sum σ q hG.pos x y hxy (M := R) fun j => (σ ^ j) r
        simp only [pow_zero, AlgEquiv.one_apply] at this
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
        rw [Algebra.smul_def, hc, smul_eq_mul, mul_comm]
        simp only [map_mul, smul_eq_mul]
      have h3 : TensorProduct.lift ((Algebra.lsmul k k M (A := R)).toLinearMap.compl₂
          (LinearMap.eqLocus s LinearMap.id).subtype) (r ⊗ₜ[k] n) = r • (n : M) := rfl
      rw [h3, hg]
      simp_rw [h1, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, h2]
  · rw [hg, map_sum]
    have := sep_sum σ q hG.pos x y hxy fun j => (s ^ j) m
    simp only [pow_zero, Module.End.one_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    change x i • (T (y i • m) : M) = _
    rw [hTv]
    simp only [hsj]

end UpperTheory.ConvolutionTheory.D
