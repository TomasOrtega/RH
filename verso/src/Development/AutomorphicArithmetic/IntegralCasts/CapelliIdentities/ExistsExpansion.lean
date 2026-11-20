import Mathlib

/- English proof (translation)
Establish `h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j`. Simplify using `only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]`. Rewrite using `[h1, hy]`. Take the linear combination `a * hc`.
-/
private lemma UpperTheory.Reformulated.B.Qn12.step {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (p e x a : R) (j : ι) (hy : y j = x - a) (hc : p = e + ∑ i, c i * y i) :
    p * x = e * a + ∑ i, (c i * a + if i = j then p else 0) * y i := by
  have h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]
  rw [h1, hy]
  linear_combination a * hc

/- English proof (translation)
Simplify using `only [add_mul, Finset.sum_add_distrib]`. Take the linear combination `hc + hd`.
-/
private lemma UpperTheory.Reformulated.B.Qn12.step_add {R ι : Type*} [CommRing R] [Fintype ι]
    (y c d : ι → R) (p r e f : R) (hc : p = e + ∑ i, c i * y i) (hd : r = f + ∑ i, d i * y i) :
    p + r = (e + f) + ∑ i, (c i + d i) * y i := by
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hc + hd

/- English proof (translation)
Introduce `n q p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, by simp⟩`. Consider the case `add p r hp hr`. Take `⟨c, hc⟩` from `hp`.

Take `⟨d, hd⟩` from `hr`. Use `⟨fun i => c i + d i, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add]`. Conclude with `UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd`. Consider the case `mul_X p j hp`.

Take `⟨c, hc⟩` from `hp`. Use `⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.eval_X, map_mul]`. Conclude with `UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc`.
-/
theorem UpperTheory.Reformulated.B.Qn12.exists_expansion :
    ∀ {n : ℕ} (q : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ),
    ∃ (c : Fin n → MvPolynomial (Fin n) ℂ),
      p =
        (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) ((MvPolynomial.eval q : MvPolynomial (Fin n) ℂ → ℂ) p) +
          ∑ i : Fin n, c i * (MvPolynomial.X i - (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) (q i)) := by
  intro n q p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p r hp hr =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hr
    refine ⟨fun i => c i + d i, ?_⟩
    rw [map_add, map_add]
    exact UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd
  | mul_X p j hp =>
    obtain ⟨c, hc⟩ := hp
    refine ⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul]
    exact UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc
