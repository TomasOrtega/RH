import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceIntegralRestrict

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool} {N : Type*} [AddCommGroup N] [Module ℂ N]

/- English proof (translation)
Rewrite `hw` using `[← ExteriorAlgebra.ιMulti_span_fixedDegree]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Conclude with `involute_ιMulti p v`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `smul a x _ hx => rw [map_smul, hx, smul_comm]`.
-/
theorem involute_exteriorPower {p : ℕ} {w : Fock n} (hw : w ∈ ⋀[ℂ]^p (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute w = ((-1 : ℂ) ^ p) • w := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact involute_ιMulti p v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

/- English proof (translation)
Take `⟨x, rfl⟩` from `hz`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v w`. Simplify using `only [TensorProduct.map_tmul, gradT, Submodule.coe_subtype, AlgHom.toLinearMap_apply, LinearMap.id_apply]`.

Rewrite using `[involute_exteriorPower w.2, TensorProduct.tmul_smul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]`.
-/
theorem gradT_range_ext {V : Submodule ℂ N} {p : ℕ} {z : TensorProduct ℂ N (Fock n)}
    (hz : z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^p (Fin n × Fin n → ℂ)).subtype)) :
    gradT z = ((-1 : ℂ) ^ p) • z := by
  obtain ⟨x, rfl⟩ := hz
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [TensorProduct.map_tmul, gradT, Submodule.coe_subtype, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    rw [involute_exteriorPower w.2, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Rewrite using `[← mul_assoc, gradT_cpT, neg_mul, mul_assoc, gradT_cmT, mul_neg, neg_neg, mul_assoc]`.
-/
theorem gradT_cpcm (i a j b : Fin n) :
    gradT (N := N) * (cpT i a * cmT j b) = cpT i a * cmT j b * gradT := by
  rw [← mul_assoc, gradT_cpT, neg_mul, mul_assoc, gradT_cmT, mul_neg, neg_neg, mul_assoc]

/- English proof (translation)
Unfold `sgE`. Use `split_ifs`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _`. Rewrite using `[mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _`. Simplify using the standard rewrite rules.
-/
theorem gradT_sgE (a b : Fin n) :
    gradT (N := N) * sgE ε cpT cmT a b = sgE ε cpT cmT a b * gradT := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · simp

/- English proof (translation)
Establish `h1` using `LinearMap.congr_fun (eT_gradT E a b) y`. Establish `h2` using `LinearMap.congr_fun (gradT_sgE (ε := ε) (N := N) a b) y`. Simplify using `only [Module.End.mul_apply] at h1 h2`. Simplify using `only [diagE, LinearMap.add_apply, map_add, h1, h2]`.
-/
theorem gradT_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) (y : TensorProduct ℂ N (Fock n)) :
    gradT (diagE ε (eT E) cpT cmT a b y) = diagE ε (eT E) cpT cmT a b (gradT y) := by
  have h1 := LinearMap.congr_fun (eT_gradT E a b) y
  have h2 := LinearMap.congr_fun (gradT_sgE (ε := ε) (N := N) a b) y
  simp only [Module.End.mul_apply] at h1 h2
  simp only [diagE, LinearMap.add_apply, map_add, h1, h2]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, -, rfl⟩` from `hx`. Proceed by induction on `l with`. Consider the case `nil => exact hz`.

Consider the case `cons p l ih`. Simplify using `only [lowWord]`. Rewrite using `[gradT_diagE, ih, map_smul]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]`.

Consider the case `smul a x _ hx => rw [map_smul, hx, smul_comm]`.
-/
theorem gradT_kLowSpan (E : Fin n → Fin n → Module.End ℂ N) {z : TensorProduct ℂ N (Fock n)} {c : ℂ}
    (hz : gradT z = c • z) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) z) : gradT y = c • y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, -, rfl⟩ := hx
    induction l with
    | nil => exact hz
    | cons p l ih =>
      simp only [lowWord]
      rw [gradT_diagE, ih, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end ReciprocityTheory.ChartRestriction.DS.TRGap
