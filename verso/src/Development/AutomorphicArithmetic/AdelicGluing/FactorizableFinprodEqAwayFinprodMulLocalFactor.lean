import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

/- English proof (translation)
Establish `hA : (Function.mulSupport fun v => if v = q then (1 : ℂ) else a v).Finite`. Use `ha.subset fun v hv => ?_` and prove the remaining obligations. Distinguish the cases in `h : v = q`. Conclude with `absurd (if_pos h) hv`. Introduce `h0`.

Conclude with `hv ((if_neg h).trans h0)`. Establish `hB : (Function.mulSupport fun v => if v = q then a q else (1 : ℂ)).Finite`. Use `(Set.finite_singleton q).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`.

Establish `hq : (∏ᶠ v, if v = q then a q else (1 : ℂ)) = a q`. Rewrite using `[finprod_eq_single _ q fun v hv => if_neg hv]`. Conclude with `if_pos rfl`. Rewrite using `[← hq, ← finprod_mul_distrib hA hB]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `h : v = q`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
private theorem finprod_split_at {α : Type*} (a : α → ℂ) (ha : (Function.mulSupport a).Finite) (q : α)
    [DecidablePred fun v => v = q] :
    (∏ᶠ v, a v) = (∏ᶠ v, if v = q then (1 : ℂ) else a v) * a q := by
  have hA : (Function.mulSupport fun v => if v = q then (1 : ℂ) else a v).Finite := by
    refine ha.subset fun v hv => ?_
    by_cases h : v = q
    · exact absurd (if_pos h) hv
    · intro h0
      exact hv ((if_neg h).trans h0)
  have hB : (Function.mulSupport fun v => if v = q then a q else (1 : ℂ)).Finite := by
    refine (Set.finite_singleton q).subset fun v hv => ?_
    by_contra h
    exact hv (if_neg h)
  have hq : (∏ᶠ v, if v = q then a q else (1 : ℂ)) = a q := by
    rw [finprod_eq_single _ q fun v hv => if_neg hv]
    exact if_pos rfl
  rw [← hq, ← finprod_mul_distrib hA hB]
  refine finprod_congr fun v => ?_
  by_cases h : v = q
  · subst h
    simp
  · simp [h]

/- English proof (translation)
Introduce `K _ _ n f S hf q x`. Establish `hfin : (Function.mulSupport fun v => f v (cf v x)).Finite`. Establish `h` using `Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))`. Use `(h.union S.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[Set.mem_union, not_or]`. Establish `h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion K) n` using `not_not.1 hc.1`. Apply `hv` to reduce the goal to its premises. Simplify using `only [hf v hc.2]`. Conclude with `Set.indicator_of_mem (by exact h1) _`.

Conclude with `@finprod_split_at _ (fun v => f v (cf v x)) hfin q fun _ => Classical.propDecidable _`.
-/
theorem UpperTheory.factorizable_finprod_eq_away_finprod_mul_local_factor :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (f : ∀ v : Pl K, GL (Fin n) (v.adicCompletion K) → ℂ) (S : Finset (Pl K)),
      (∀ v, v ∉ S → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))).indicator 1) →
      ∀ (q : Pl K) (x : AdelicGLn.FiniteAdelicGL K n), (∏ᶠ v, f v (cf v x)) = (∏ᶠ v, (open Classical in if v = q then (1 : ℂ) else f v (cf v x))) * f q (cf q x) := by
  intro K _ _ n f S hf q x
  have hfin : (Function.mulSupport fun v => f v (cf v x)).Finite := by
    have h := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))
    refine (h.union S.finite_toSet).subset fun v hv => ?_
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    have h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion K) n := not_not.1 hc.1
    apply hv
    simp only [hf v hc.2]
    exact Set.indicator_of_mem (by exact h1) _
  exact @finprod_split_at _ (fun v => f v (cf v x)) hfin q fun _ => Classical.propDecidable _
