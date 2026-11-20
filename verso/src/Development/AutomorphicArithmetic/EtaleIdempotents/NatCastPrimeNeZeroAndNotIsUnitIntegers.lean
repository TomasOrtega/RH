import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Establish `h : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l)`. Simplify using `[PadicAlgCl.coe_eq]`. Rewrite using `[h, PadicAlgCl.norm_extends, Padic.norm_p]`.
-/
private theorem norm_l_val {l : ℕ} [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
    simp [PadicAlgCl.coe_eq]
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

/- English proof (translation)
Introduce `l _ K`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hlt : ‖(l : PadicAlgCl l)‖ < 1`. Rewrite using `[norm_l_val]`. Conclude with `inv_lt_one_of_one_lt₀ hl`.

Establish `hval : ∀ x : OK l K, ‖((x : K) : PadicAlgCl l)‖ ≤ 1` using `fun x => x.2`. Establish `hc : (((l : OK l K) : K) : PadicAlgCl l) = (l : PadicAlgCl l)` using `by simp`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h1` using `congrArg (fun x : OK l K => ((x : K) : PadicAlgCl l)) h0`.

Simplify using `only [hc] at h1`. Establish `: (l : PadicAlgCl l) ≠ 0`. Introduce `h`. Rewrite `h` using `[← norm_eq_zero, norm_l_val]`. Establish `: (0:ℝ) < l` using `by linarith`.

Conclude with `(inv_pos.mpr this).ne' h`. Simplify using `at h1`. Conclude with `this (by simpa using h1)`. Introduce and unpack `⟨u, hu⟩`. Establish `hm` using `congrArg (fun x : OK l K => ((x : K) : PadicAlgCl l)) (u.mul_inv)`.

Simplify using `only [hu] at hm`. Establish `h2 : ‖(((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1‖ ≤ 1` using `hval _`. Establish `hm' : (l : PadicAlgCl l) * (((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1 = 1`. Simplify using `using hm`. Establish `h3` using `congrArg norm hm'`.

Rewrite `h3` using `[norm_mul, norm_one]`. Establish `h4 : ‖(l : PadicAlgCl l)‖ * ‖(((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1‖ < 1`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}, (l : OK l K) ≠ 0 ∧ ¬ IsUnit (l : OK l K) := by
  intro l _ K
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlt : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [norm_l_val]; exact inv_lt_one_of_one_lt₀ hl
  have hval : ∀ x : OK l K, ‖((x : K) : PadicAlgCl l)‖ ≤ 1 := fun x => x.2
  have hc : (((l : OK l K) : K) : PadicAlgCl l) = (l : PadicAlgCl l) := by simp
  constructor
  · intro h0
    have h1 := congrArg (fun x : OK l K => ((x : K) : PadicAlgCl l)) h0
    simp only [hc] at h1
    have : (l : PadicAlgCl l) ≠ 0 := by
      intro h
      rw [← norm_eq_zero, norm_l_val] at h
      have : (0:ℝ) < l := by linarith
      exact (inv_pos.mpr this).ne' h
    simp at h1
    exact this (by simpa using h1)
  · rintro ⟨u, hu⟩
    have hm := congrArg (fun x : OK l K => ((x : K) : PadicAlgCl l)) (u.mul_inv)
    simp only [hu] at hm
    have h2 : ‖(((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1‖ ≤ 1 := hval _
    have hm' : (l : PadicAlgCl l) * (((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1 = 1 := by
      simpa using hm
    have h3 := congrArg norm hm'
    rw [norm_mul, norm_one] at h3
    have h4 : ‖(l : PadicAlgCl l)‖ * ‖(((u⁻¹ : (OK l K)ˣ) : OK l K) : K).1‖ < 1 := by
      calc _ ≤ ‖(l : PadicAlgCl l)‖ * 1 := by gcongr
        _ < 1 := by simpa using hlt
    linarith
