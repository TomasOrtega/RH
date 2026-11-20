import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

/- English proof (translation)
Use `show A.bind (fun a => {(a : ℂ)}) = _`. Conclude with `Multiset.bind_singleton A _`.
-/
theorem units_coe_multiset (A : Multiset ℂˣ) :
    (do let a ← A; pure (a : ℂ) : Multiset ℂ) = A.map (fun α : ℂˣ => (α : ℂ)) := by
  show A.bind (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton A _

/- English proof (translation)
Rewrite using `[map_multiset_sum, Multiset.map_map]`. Simplify using `[Function.comp_def, map_pow]`.
-/
theorem powSum_conj (B : Multiset ℂ) (r : ℕ) :
    (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum = starRingEnd ℂ ((B.map fun β => β ^ (r + 1)).sum) := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Function.comp_def, map_pow]

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (by omega : q ≠ 0)`. Rewrite using `[Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natCast_cpow_eq_exp (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) = Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add, Multiset.sum_add]`. Use `set PA := (A.map fun α => α ^ (r + 1)).sum`. Use `set PB := (B.map fun α => α ^ (r + 1)).sum`. Establish `hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB)`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Rewrite using `[← Complex.ofReal_pow, hn, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem four_terms (A B : Multiset ℂ) (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (A.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (A.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) =
    ((‖((A + B).map (· ^ (r + 1))).sum‖ ^ 2 / ((r : ℝ) + 1) : ℝ) : ℂ) *
      Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  rw [powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add, Multiset.sum_add]
  set PA := (A.map fun α => α ^ (r + 1)).sum
  set PB := (B.map fun α => α ^ (r + 1)).sum
  have hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, hn, map_add]
  ring

/- English proof (translation)
Establish `L` using `GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E`. Take `⟨s1, p1⟩` from `L a a σ σ hσ hσ T hT hT x hx`. Take `⟨s2, p2⟩` from `L b b σ' σ' hσ' hσ' T hT' hT' x hx`. Take `⟨s3, p3⟩` from `L a b σ σ' hσ hσ' T hT hT' x hx`. Take `⟨s4, p4⟩` from `L b a σ' σ hσ' hσ T hT' hT x hx`.

Establish `h` using `(((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)`. Use `⟨?g, ?hs, ?hp⟩` and prove the remaining obligations. Use `case hp =>`. Simplify using `only [lfac]`. Rewrite using `[p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]`.

Use `case hs =>`. Use `(congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h` and prove the remaining obligations. Simplify using `only [Pi.add_apply, units_coe_multiset]`. Rewrite using `[four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]`. Both sides reduce to the same expression.
-/
theorem fourProd_eq_exp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a)
    (σ' : CG E b) (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧
      (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  have L := GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E
  obtain ⟨s1, p1⟩ := L a a σ σ hσ hσ T hT hT x hx
  obtain ⟨s2, p2⟩ := L b b σ' σ' hσ' hσ' T hT' hT' x hx
  obtain ⟨s3, p3⟩ := L a b σ σ' hσ hσ' T hT hT' x hx
  obtain ⟨s4, p4⟩ := L b a σ' σ hσ' hσ T hT' hT x hx
  have h := (((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)
  refine ⟨?g, ?hs, ?hp⟩
  case hp =>
    simp only [lfac]
    rw [p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
  case hs =>
    refine (congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h
    simp only [Pi.add_apply, units_coe_multiset]
    rw [four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]
    rfl

end GlobalTheory.RSNonvan
