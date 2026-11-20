import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltrationStatement

noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`.
-/
theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [LocAinf.εroot]`. Consider the case `succ m ih`. Rewrite using `[pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]`. Conclude with `ih`.
-/
theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

/- English proof (translation)
Rewrite using `[epsT, ← map_pow, root_pow]`.
-/
theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]`. Conclude with `ih.frob`.
-/
theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

/- English proof (translation)
The claim follows from `IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z`.
-/
theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

/- English proof (translation)
Establish `hl : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `hj : (j.factorial : ℚ_[l]) ≠ 0` using `by exact_mod_cast j.factorial_ne_zero`. Rewrite using `[levSum, mul_add, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) = ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j)`. Use `push_cast`. Rewrite using `[div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (j.factorial : ℚ_[l])⁻¹ = ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, map_mul, map_pow, map_natCast, mul_assoc]`.
-/
theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

/- English proof (translation)
Introduce `l _ P AI TT K s ι T w c m M d hM hw hd`. Take `⟨y₁, h1, h2⟩` from `GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by`. Rewrite using `[(hd j hj).2, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast]⟩)`.

Use `set H : ℕ → Ainf l := fun k => ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH`. Establish `hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1)`. Introduce `k`. Simplify using `only [hH]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) * WittVector.teichmuller l AI.ε ^ m i`.

Simplify using `only [hH]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (m i), pow_mul, epsT_pow]`. Establish `h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i` using `by simp [hH]`. Use `⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩` and prove the remaining obligations.

Establish `ht` using `Finset.sum_range_sub' H s`. Rewrite `ht` using `[Finset.sum_sub_distrib]`. Rewrite using `[map_add, map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]`. Rewrite `h1` using `[← hs]`. Take the linear combination `ht + h1`.

Establish `hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) * ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P ( …`. Use `Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Use `FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)` and prove the remaining obligations. Rewrite using `[← (lifts_iter (hw i hi) k).io_eq]`. Conclude with `io_mem AI _`.

Establish `e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k))`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hH]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[map_mul, (lifts_iter (hw i hi) k).io_eq]`. Establish `e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j = ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * (oB P (P.ζQ s ^ (m i * l ^ k)) * ∑ j ∈ Finset.range …`. Simplify using `only [coeff_eq, map_add, map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `add_mem hk h2` as an intermediate fact. Rewrite using `[map_add, e1, e2]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by
      rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht
    rw [map_add, map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by
      simp only [coeff_eq, map_add, map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add, e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
