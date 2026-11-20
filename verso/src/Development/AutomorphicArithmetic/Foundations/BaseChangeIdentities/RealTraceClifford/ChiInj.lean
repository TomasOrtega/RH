import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def chi {n : ℕ} (x : Wt n) : Multiplicative (Wt n) →* ℂ where
  toFun θ := Complex.exp (Complex.I * ∑ a, ((Multiplicative.toAdd θ a : ℝ) : ℂ) * (x a : ℂ))
  map_one' := by simp
  map_mul' s t := by
    simp [← Complex.exp_add, add_mul, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Introduce `x y hxy`. Use function extensionality and compare the values at `a`. Assume the negation of the conclusion as `hne`. Establish `hd' : x a - y a ≠ 0` using `sub_ne_zero.2 hne`. Establish `e` using `congrArg (fun φ : Multiplicative (Wt n) →* ℂ => φ (Multiplicative.ofAdd (Pi.single a (Real.pi / (x a - y a))))) hxy`.

Simplify using `[chi, Pi.single_apply] at e`. Rewrite `e` using `[Complex.exp_eq_exp_iff_exists_int]`. Take `⟨m, hm⟩` from `e`. Establish `hi` using `congrArg Complex.im hm`. Simplify using `at hi`.

Establish `hp : Real.pi / (x a - y a) * (x a - y a) = Real.pi` using `div_mul_cancel₀ _ hd'`. Establish `h2 : Real.pi * 1 = Real.pi * (2 * m)` using `by linear_combination hi - hp`. Establish `h3` using `mul_left_cancel₀ Real.pi_ne_zero h2`. Establish `h4 : (1 : ℤ) = 2 * m` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
private theorem chi_inj {n : ℕ} : Function.Injective (chi (n := n)) := by
  intro x y hxy
  funext a
  by_contra hne
  have hd' : x a - y a ≠ 0 := sub_ne_zero.2 hne
  have e := congrArg (fun φ : Multiplicative (Wt n) →* ℂ =>
    φ (Multiplicative.ofAdd (Pi.single a (Real.pi / (x a - y a))))) hxy
  simp [chi, Pi.single_apply] at e
  rw [Complex.exp_eq_exp_iff_exists_int] at e
  obtain ⟨m, hm⟩ := e
  have hi := congrArg Complex.im hm
  simp at hi
  have hp : Real.pi / (x a - y a) * (x a - y a) = Real.pi := div_mul_cancel₀ _ hd'
  have h2 : Real.pi * 1 = Real.pi * (2 * m) := by linear_combination hi - hp
  have h3 := mul_left_cancel₀ Real.pi_ne_zero h2
  have h4 : (1 : ℤ) = 2 * m := by exact_mod_cast h3
  omega

/- English proof (translation)
Simplify using `[evT, AddMonoidAlgebra.lift_apply, Finsupp.sum, chi]`.
-/
private theorem evT_eq_sum_coeff_chi {n : ℕ} (θ : Wt n) (f : FR n) :
    evT θ f = ∑ x ∈ f.coeff.support, f.coeff x * chi x (Multiplicative.ofAdd θ) := by
  simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum, chi]

/- English proof (translation)
Establish `hli : LinearIndependent ℂ (fun x : Wt n => ((chi x : Multiplicative (Wt n) → ℂ)))` using `(linearIndependent_monoidHom (Multiplicative (Wt n)) ℂ).comp chi chi_inj`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises. Apply `linearIndependent_iff.1 hli` to reduce the goal to its premises. Use extensionality with `θ`. Establish `hθ` using `h (Multiplicative.toAdd θ)`.

Rewrite `hθ` using `[evT_eq_sum_coeff_chi]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Simplify `hθ` using `[Finset.sum_apply]`.
-/
private theorem ev_zero {n : ℕ} (f : FR n) (h : ∀ θ : Wt n, evT θ f = 0) : f = 0 := by
  have hli : LinearIndependent ℂ (fun x : Wt n => ((chi x : Multiplicative (Wt n) → ℂ))) :=
    (linearIndependent_monoidHom (Multiplicative (Wt n)) ℂ).comp chi chi_inj
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.1 hli
  ext θ
  have hθ := h (Multiplicative.toAdd θ)
  rw [evT_eq_sum_coeff_chi] at hθ
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simpa [Finset.sum_apply] using hθ

/- English proof (translation)
Introduce `n f hf`. Apply `ev_zero f` to reduce the goal to its premises. Introduce `θ0`. Set `v : Wt n` to `fun a => ((a : ℕ) : ℝ)`. Choose the witnesses or unpack the hypotheses as in `⟨bad, hbad, hmem⟩ : ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, t ∉ S → Function.Injective fun a => Complex.exp (Complex.I * (((θ0 + t • v) a : ℝ) : ℂ)) ^ 2 := by`.

Use `⟨⋃ p : Fin n × Fin n, ⋃ m : ℤ, {((m : ℝ) * Real.pi - (θ0 p.1 - θ0 p.2)) / (v p.1 - v p.2)}, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Set.countable_iUnion fun p => Set.countable_iUnion fun m => Set.countable_singleton _`. Introduce `t ht a b hab`. Assume the negation of the conclusion as `hne`. Apply `ht` to reduce the goal to its premises.

Simplify using `only at hab`. Rewrite `hab` using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨m, hm⟩` from `hab`. Establish `hi` using `congrArg Complex.im hm`. Simplify using `[Pi.add_apply, Pi.smul_apply] at hi`.

Establish `hv : v a - v b ≠ 0` using `sub_ne_zero.2 (fun e => hne (Fin.ext (by simpa [v] using e)))`. Use `Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨m, Set.mem_singleton_iff.2 ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hv]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hφ : (fun t : ℝ => evT (θ0 + t • v) f) = fun t => ∑ x ∈ f.coeff.support, f.coeff x * Complex.exp (Complex.I * ∑ a, (((θ0 a + t * v a : ℝ)) : ℂ) * (x a : ℂ))`.

Use function extensionality and compare the values at `t`. Simplify using `[evT, AddMonoidAlgebra.lift_apply, Finsupp.sum]`. Establish `hcont : Continuous fun t : ℝ => evT (θ0 + t • v) f`. Rewrite using `[hφ]`. Use `fun_prop`.

Establish `hzero` using `Continuous.ext_on (hbad.dense_compl ℝ) hcont continuous_const (fun t ht => hf (θ0 + t • v) (hmem t ht))`. Simplify using `using congrFun hzero 0`.
-/
theorem UpperTheory.RealTr.evInj :
    ∀ (n : ℕ) (f : FR n), (∀ θ : Wt n, (Function.Injective fun a => Complex.exp (Complex.I * θ a) ^ 2) → evT θ f = 0) → f = 0 := by
  intro n f hf
  apply ev_zero f
  intro θ0
  let v : Wt n := fun a => ((a : ℕ) : ℝ)
  obtain ⟨bad, hbad, hmem⟩ : ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, t ∉ S →
      Function.Injective fun a => Complex.exp (Complex.I * (((θ0 + t • v) a : ℝ) : ℂ)) ^ 2 := by
    refine ⟨⋃ p : Fin n × Fin n, ⋃ m : ℤ,
      {((m : ℝ) * Real.pi - (θ0 p.1 - θ0 p.2)) / (v p.1 - v p.2)}, ?_, ?_⟩
    · exact Set.countable_iUnion fun p => Set.countable_iUnion fun m => Set.countable_singleton _
    · intro t ht a b hab
      by_contra hne
      apply ht
      simp only at hab
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at hab
      obtain ⟨m, hm⟩ := hab
      have hi := congrArg Complex.im hm
      simp [Pi.add_apply, Pi.smul_apply] at hi
      have hv : v a - v b ≠ 0 := sub_ne_zero.2 (fun e => hne (Fin.ext (by simpa [v] using e)))
      refine Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨m, Set.mem_singleton_iff.2 ?_⟩⟩
      rw [eq_div_iff hv]
      linarith
  have hφ : (fun t : ℝ => evT (θ0 + t • v) f) = fun t => ∑ x ∈ f.coeff.support,
      f.coeff x * Complex.exp (Complex.I * ∑ a, (((θ0 a + t * v a : ℝ)) : ℂ) * (x a : ℂ)) := by
    funext t
    simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  have hcont : Continuous fun t : ℝ => evT (θ0 + t • v) f := by
    rw [hφ]
    fun_prop
  have hzero := Continuous.ext_on (hbad.dense_compl ℝ) hcont continuous_const
    (fun t ht => hf (θ0 + t • v) (hmem t ht))
  simpa using congrFun hzero 0
