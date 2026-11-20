import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Introduce `p h e D`. Use `⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩` and prove the remaining obligations. Introduce `σ`. Take `⟨u, hu⟩` from `D.conj σ`. Use `⟨u, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[hu, map_add, map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]`. Use `congr 2`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, map_pow, map_inv₀]`. Introduce `s`.

Take `⟨x, y, hxy⟩` from `Multiset.card_eq_two.1 (D.card s)`. Establish `hx : ‖x‖ = 1` using `by simpa using D.pure s x (by rw [hxy]; simp)`. Establish `hy : ‖y‖ = 1` using `by simpa using D.pure s y (by rw [hxy]; simp)`. Establish `e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h`. Rewrite using `[hxy]`.

Simplify using the standard rewrite rules. Establish `h1 : ‖x⁻¹ ^ h‖ = 1` using `by simp [hx]`. Establish `h2 : ‖y⁻¹ ^ h‖ = 1` using `by simp [hy]`. Rewrite using `[e1]`. Establish `h3` using `norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)`.

Establish `h4` using `norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)`. Rewrite `h3` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `s`. Take `⟨x, y, hxy⟩` from `Multiset.card_eq_two.1 (D.card s)`.

Establish `hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ)`. Introduce `i`. Use `fin_cases i`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish `hx` using `D.intInv e hm s x (by rw [hxy]; simp)`. Establish `hy` using `D.intInv e hm s y (by rw [hxy]; simp)`. Rewrite `hx`, `hy` using `[zpow_natCast]`. Establish `e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h`. Rewrite using `[hxy]`.

Simplify using the standard rewrite rules. Establish `e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) = ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h)` using `by push_cast; ring`. Rewrite using `[e1, e2]`. Use `IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))` and prove the remaining obligations. Conclude with `(isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))` after adjusting the coercions.
-/
theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add, map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
