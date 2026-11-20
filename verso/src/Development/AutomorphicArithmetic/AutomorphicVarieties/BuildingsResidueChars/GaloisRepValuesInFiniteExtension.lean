import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

/- English proof (translation)
Introduce `F Ω C _ _ _ _ M hM χ hχ`. Establish `hpos : 0 < M` using `by omega`. Establish `hR : {ζ : Ω | ζ ^ M = 1}.Finite`. Use `(Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_` and prove the remaining obligations. Introduce `ζ hζ`.

Simplify `hζ` using `[Polynomial.mem_nthRoots hpos]`. Use `haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype`. Set `π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1})` to `fun s ζ => ⟨s ζ, by show (s ζ) ^ M = 1`. Rewrite using `[← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩`. Establish `hfac : ∀ s t, π s = π t → χ s = χ t`.

Introduce `s t hst`. Establish `h1 : χ (t⁻¹ * s) = 1`. Use `hχ _ (fun ζ hζ => ?_)` and prove the remaining obligations. Establish `h` using `congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst`. Simplify using `only [π] at h`.

Rewrite using `[AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1.symm`. Use `(Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`.

Conclude with `⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩`.
-/
theorem UpperTheory.galois_rep_values_in_finite_extension :
    UpperTheory.V.Af.Wd.FinVal := by
  intro F Ω C _ _ _ _ M hM χ hχ
  classical
  have hpos : 0 < M := by omega
  have hR : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hpos] using hζ
  haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype
  let π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1}) := fun s ζ =>
    ⟨s ζ, by
      show (s ζ) ^ M = 1
      rw [← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩
  have hfac : ∀ s t, π s = π t → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      refine hχ _ (fun ζ hζ => ?_)
      have h := congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst
      simp only [π] at h
      rw [AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  refine (Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩
