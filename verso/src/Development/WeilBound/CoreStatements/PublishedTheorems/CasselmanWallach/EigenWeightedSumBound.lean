import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SumSquaresShift

/- English proof (translation)
Take `⟨-, -, hmem, hadd, -⟩` from `hB3g n ε`. Establish `hg'` using `hmem g hg X hX t`. Establish `h1` using `h _ hg'`. Establish `h0 : HasDerivAt (fun s : ℝ => F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp (s • X))) (D (g * NormedSpace.exp (t • X))) (t - t)`. Rewrite using `[sub_self]`.

Conclude with `h1`. Establish `h4` using `h0.comp_sub_const t t`. Use `h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `hu : t + (u - t) = u` using `by ring`. Use `show F0 (g * NormedSpace.exp (u • X)) = F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp ((u - t) • X))`.

Rewrite using `[mul_assoc, ← hadd X t (u - t), hu]`.
-/
theorem shift {n : ℕ} {ε : Fin n → Bool} (hB3g : UnitaryGroupFacts) (F0 : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (D : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D g) 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D (g * NormedSpace.exp (t • X))) t := by
  obtain ⟨-, -, hmem, hadd, -⟩ := hB3g n ε
  have hg' := hmem g hg X hX t
  have h1 := h _ hg'
  have h0 : HasDerivAt (fun s : ℝ => F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp (s • X)))
      (D (g * NormedSpace.exp (t • X))) (t - t) := by
    rw [sub_self]; exact h1
  have h4 := h0.comp_sub_const t t
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have hu : t + (u - t) = u := by ring
  show F0 (g * NormedSpace.exp (u • X)) = F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp ((u - t) • X))
  rw [mul_assoc, ← hadd X t (u - t), hu]

end SumSquaresShift

open SumSquaresShift in
/- English proof (translation)
Introduce `hB1 hB3g n ε V _ _ E hMod ι b μ hEig κ hκ F hF S a g hg`. Take `⟨hXp, hcas, hnorm⟩` from `hB1 n ε V E hMod`. Establish `hd : ∀ p ∈ nc ε, ∀ (v : V) (t : ℝ), HasDerivAt (fun s : ℝ => F v (g * NormedSpace.exp (s • Xp p.1 p.2))) (F (actM E (Xp p.1 p.2) v) (g * NormedSpace.exp (t • Xp p.1 p.2))) t`. Introduce `p hp v t`. Conclude with `shift hB3g (F v) (Xp p.1 p.2) (hXp p hp) (fun k => F (actM E (Xp p.1 p.2) v) k) (fun k hk => hF _ (hXp p hp) v k hk) g hg t`.

Establish `hexp0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp ((0:ℝ) • X) = g`. Introduce `X`. Simplify using `[NormedSpace.exp_zero]`. Use `⟨fun p => ∑ i ∈ S, a i * (2 * (inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) + ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2)), ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Use `⟨fun t => ∑ i ∈ S, a i * (2 * inner ℝ (F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))) (F (actM E (Xp p.1 p.2) (b i)) (g * NormedSpace.exp (t • Xp p.1 p.2)))), ?_, ?_⟩` and prove the remaining obligations. Introduce `t beta_reduce`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `i _`. Conclude with `((hd p hp (b i) t).norm_sq).const_mul (a i)`.

Use `beta_reduce`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `i _`. Establish `h1` using `hd p hp (b i) 0`. Establish `h2` using `hd p hp (actM E (Xp p.1 p.2) (b i)) 0`.

Establish `h3` using `((HasDerivAt.inner ℝ h1 h2).const_mul 2).const_mul (a i)`. Rewrite `h3` using `[hexp0]`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[real_inner_self_eq_norm_sq]`. Simplify using `only`.

Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hN : ∑ p ∈ nc ε, ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2 = ∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2` using `hnorm ((LinearMap.proj g).comp F) (b i)`. Establish `hs : ∑ p ∈ nc ε, F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g = ((κ - μ i : ℝ) : ℂ) * F (b i) g`. Establish `h0` using `congrArg (fun v => F v g) (hcas κ hκ (b i))`.

Simplify using `only [map_sum, Finset.sum_apply] at h0`. Rewrite using `[h0, (hEig.eig i : casimirK ε E (b i) = _)]`. Simplify using `only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hI : ∑ p ∈ nc ε, inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) = (κ - μ i) * ‖F (b i) g‖ ^ 2`. Rewrite using `[← inner_sum, hs, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hI, hN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem second_derivatives_of_growth : B1 → UnitaryGroupFacts → SumSquaresSecondDerivative := by
  intro hB1 hB3g n ε V _ _ E hMod ι b μ hEig κ hκ F hF S a g hg
  obtain ⟨hXp, hcas, hnorm⟩ := hB1 n ε V E hMod
  have hd : ∀ p ∈ nc ε, ∀ (v : V) (t : ℝ),
      HasDerivAt (fun s : ℝ => F v (g * NormedSpace.exp (s • Xp p.1 p.2)))
        (F (actM E (Xp p.1 p.2) v) (g * NormedSpace.exp (t • Xp p.1 p.2))) t := by
    intro p hp v t
    exact shift hB3g (F v) (Xp p.1 p.2) (hXp p hp) (fun k => F (actM E (Xp p.1 p.2) v) k)
      (fun k hk => hF _ (hXp p hp) v k hk) g hg t
  have hexp0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp ((0:ℝ) • X) = g := by
    intro X
    simp [NormedSpace.exp_zero]
  refine ⟨fun p => ∑ i ∈ S, a i * (2 * (inner ℝ (F (b i) g)
      (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) + ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2)), ?_, ?_⟩
  · intro p hp
    refine ⟨fun t => ∑ i ∈ S, a i * (2 * inner ℝ (F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2)))
      (F (actM E (Xp p.1 p.2) (b i)) (g * NormedSpace.exp (t • Xp p.1 p.2)))), ?_, ?_⟩
    · intro t
      beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      exact ((hd p hp (b i) t).norm_sq).const_mul (a i)
    · beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      have h1 := hd p hp (b i) 0
      have h2 := hd p hp (actM E (Xp p.1 p.2) (b i)) 0
      have h3 := ((HasDerivAt.inner ℝ h1 h2).const_mul 2).const_mul (a i)
      rw [hexp0] at h3
      refine h3.congr_deriv ?_
      rw [real_inner_self_eq_norm_sq]
  · dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hN : ∑ p ∈ nc ε, ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2
        = ∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2 :=
      hnorm ((LinearMap.proj g).comp F) (b i)
    have hs : ∑ p ∈ nc ε, F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g
        = ((κ - μ i : ℝ) : ℂ) * F (b i) g := by
      have h0 := congrArg (fun v => F v g) (hcas κ hκ (b i))
      simp only [map_sum, Finset.sum_apply] at h0
      rw [h0, (hEig.eig i : casimirK ε E (b i) = _)]
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hI : ∑ p ∈ nc ε, inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g)
        = (κ - μ i) * ‖F (b i) g‖ ^ 2 := by
      rw [← inner_sum, hs, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hI, hN]
    ring

end PositivityTheory.CW

end
