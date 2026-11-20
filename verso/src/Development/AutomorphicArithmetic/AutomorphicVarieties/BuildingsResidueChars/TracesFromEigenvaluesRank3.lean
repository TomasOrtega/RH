import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Introduce `q e hq D`. Establish `hqR : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hqC : (q : ℂ) ≠ 0` using `by exact_mod_cast hqR.ne'`. Use `⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩` and prove the remaining obligations. Introduce `σ`.

Take `⟨u, hu⟩` from `D.conj σ`. Use `⟨u, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `s`. Use `(norm_multiset_sum_le _).trans ?_` and prove the remaining obligations. Establish `h` using `Multiset.sum_le_card_nsmul (((D.β s).map fun b => ((q : ℂ) * b)⁻¹).map fun x => ‖x‖) (1 : ℝ) (by`. Introduce `x hx`.

Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hx`. Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hy`. Establish `hp` using `D.pure s b hb`. Establish `he : (((1 - ((3 : ℕ) : ℤ) : ℤ) : ℝ) / 2) = -1` using `by push_cast; norm_num`. Rewrite `hp` using `[he, Real.rpow_neg_one]`.

Rewrite using `[norm_inv, norm_mul, hp, Complex.norm_natCast, mul_inv_cancel₀ hqR.ne', inv_one])`. Rewrite `h` using `[Multiset.card_map, Multiset.card_map, D.card]`. Simplify using `using h`. Introduce `s`. Rewrite using `[← Multiset.sum_map_mul_left]`.

Use `(integralClosure ℤ ℂ).multiset_sum_mem ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hx`. Establish `h` using `D.intInv ((e : ℤ) - 1) (by`. Introduce `i`.

Apply the tactic sequence `fin_cases i <;> simp <;> omega) s b hb`. Establish `he : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹`. Rewrite using `[zpow_sub_one₀ hqC, zpow_natCast, mul_inv, mul_assoc]`. Rewrite using `[mem_integralClosure_iff, he]`. Conclude with `h`.
-/
theorem UpperTheory.traces_from_eigenvalues_rank3 :
    ∀ (q e : ℕ), 1 ≤ q → ∀ D : EigData 3 q ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - ((3 : ℕ) : ℤ)), ∃ (T : TrData q e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum := by
  intro q e hq D
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
  refine ⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  · intro s
    refine (norm_multiset_sum_le _).trans ?_
    have h := Multiset.sum_le_card_nsmul (((D.β s).map fun b => ((q : ℂ) * b)⁻¹).map fun x => ‖x‖) (1 : ℝ) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hy
      have hp := D.pure s b hb
      have he : (((1 - ((3 : ℕ) : ℤ) : ℤ) : ℝ) / 2) = -1 := by push_cast; norm_num
      rw [he, Real.rpow_neg_one] at hp
      rw [norm_inv, norm_mul, hp, Complex.norm_natCast, mul_inv_cancel₀ hqR.ne', inv_one])
    rw [Multiset.card_map, Multiset.card_map, D.card] at h
    simpa using h
  · intro s
    rw [← Multiset.sum_map_mul_left]
    refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    have h := D.intInv ((e : ℤ) - 1) (by
      intro i
      fin_cases i <;> simp <;> omega) s b hb
    have he : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹ := by
      rw [zpow_sub_one₀ hqC, zpow_natCast, mul_inv, mul_assoc]
    rw [mem_integralClosure_iff, he]
    exact h
