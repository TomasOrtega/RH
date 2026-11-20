import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers

noncomputable section

namespace GlobalTheory.Cyc.Decomp.Coord

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩`.
-/
theorem inC_zero (F : IntermediateField ℚ_[l] (Om l)) : (0 : PadicComplex l) ∈ inC F :=
  ⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `hx`. Take `⟨v, hv, rfl⟩` from `hy`. Conclude with `⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩`.
-/
theorem inC_add {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x + y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `hx`. Take `⟨v, hv, rfl⟩` from `hy`. Conclude with `⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩`.
-/
theorem inC_mul {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x * y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩`.
-/
theorem inC_zC (F : IntermediateField ℚ_[l] (Om l)) (x : ℤ_[l]) : zC x ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h`.
-/
theorem inC_sum {F : IntermediateField ℚ_[l] (Om l)} {ι : Type} (s : Finset ι)
    (g : ι → PadicComplex l) (h : ∀ i ∈ s, g i ∈ inC F) : ∑ i ∈ s, g i ∈ inC F :=
  Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty, kap_zero]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]`.
-/
theorem kap_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {ι : Type}
    (s : Finset ι) (g : ι → OCO LL) (k : Fin f) :
    kap o (∑ i ∈ s, g i) k = ∑ i ∈ s, kap o (g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]`. Rewrite using `[Finset.sum_mul, kap_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, kap_tmul, smul_eq_mul, mul_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem kap_mul_one_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (x : OCO LL) (a : ↥(OL LL)) (k : Fin f) :
    kap o (x * ((1 : OC l) ⊗ₜ[ℤ_[l]] a)) k = ∑ j, kap o x j * zC (o.repr (o j * a) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]
  rw [Finset.sum_mul, kap_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
    kap_tmul, smul_eq_mul, mul_one, mul_one]
  rfl

/- English proof (translation)
Use `⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]`. Simplify using `only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]`. Rewrite using `[add_comm]`. Conclude with `PowerSeries.eq_X_mul_shift_add_const (a j)`.

Introduce `i _ hij`. Simplify using `[letE, Pi.single_eq_of_ne hij.symm]`. Simplify using the standard rewrite rules.
-/
theorem let_split {O : Type} [CommRing O] {n : ℕ} [NeZero n] (a : LetA O n) :
    ∃ a' : LetA O n, a = ∑ i, letE i * algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i))
      + letπ * a' := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]
    rw [add_comm]
    exact PowerSeries.eq_X_mul_shift_add_const (a j)
  · intro i _ hij
    simp [letE, Pi.single_eq_of_ne hij.symm]
  · simp

/- English proof (translation)
Use `haveI := GlobalTheory.TateDecomp.finite_Ks K m`. Establish `hcl : IsClosed (intC (Ks K m))` using `(GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed`. Establish `key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m), ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r`. Introduce `N k`. Proceed by induction on `N with`.

Consider the case `zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩`. Consider the case `succ N ih`. Introduce `a`. Take `⟨a', ha⟩` from `let_split a`. Take `⟨s, hs, r, hr, h⟩` from `ih a'`.

Use `⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩` and prove the remaining obligations. Rewrite using `[kap_mul_one_tmul]`. Conclude with `inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)`. Establish `e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i))) + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a'`. Use `(congrArg φ ha).trans ((φ.map_add _ _).trans ?_)` and prove the remaining obligations.

Use `congrArg₂ (· + ·) ((map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)) ?_` and prove the remaining obligations. Conclude with `(φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))`. Conclude with `(φ.map_mul _ _).trans (congrArg (· * φ a') hπ)`. Rewrite using `[e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]`. Introduce `a k`.

Use `hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)` and prove the remaining obligations. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one hε hc`. Take `⟨s, hs, r, hr, h⟩` from `key N k a`. Establish `hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N`. Rewrite using `[norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_right (by positivity) hr`. Use `⟨s, ⟨hs, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r)` using `by rw [h]; ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Conclude with `hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)`. Rewrite using `[dist_eq_norm, h, add_sub_cancel_left]`. Conclude with `hb.trans_lt hN`.
-/
theorem coord (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n]
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l)
    (hO : ∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a)
    (hπ : φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) (hc : ‖(c : PadicComplex l)‖ < 1)
    (hcF : (c : PadicComplex l) ∈ inC (Ks K m))
    (hE : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) :
    ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  haveI := GlobalTheory.TateDecomp.finite_Ks K m
  have hcl : IsClosed (intC (Ks K m)) := (GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed
  have key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m),
      ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r := by
    intro N k
    induction N with
    | zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha⟩ := let_split a
      obtain ⟨s, hs, r, hr, h⟩ := ih a'
      refine ⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k
        + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩
      · rw [kap_mul_one_tmul]
        exact inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)
      · have e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))
            + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a' := by
          refine (congrArg φ ha).trans ((φ.map_add _ _).trans ?_)
          refine congrArg₂ (· + ·) ((map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)) ?_
          · exact (φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))
          · exact (φ.map_mul _ _).trans (congrArg (· * φ a') hπ)
        rw [e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]
  intro a k
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hc
  obtain ⟨s, hs, r, hr, h⟩ := key N k a
  have hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) hr
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · have e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r) := by rw [h]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)
    rw [norm_neg]
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)
  · rw [dist_eq_norm, h, add_sub_cancel_left]
    exact hb.trans_lt hN

end GlobalTheory.Cyc.Decomp.Coord
