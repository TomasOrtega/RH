import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `A M _ _ _ _ _ t S B ht hS`. Use `haveI : Module.Finite A (S.map B.mkQ) := Module.Finite.iff_fg.mpr (hS.map _)`. Take `⟨n, ι, _, p, hp, e, ⟨φ⟩⟩` from `Module.equiv_free_prod_directSum A (S.map B.mkQ)`. Set `ψ : (Fin n →₀ A) →ₗ[A] S.map B.mkQ` to `φ.symm.toLinearMap ∘ₗ LinearMap.inl A _ _`. Establish `hlift : ∀ j : Fin n, ∃ m ∈ S, B.mkQ m = (ψ (Finsupp.single j 1) : M ⧸ B)` using `fun j => Submodule.mem_map.mp (ψ (Finsupp.single j 1)).2`.

Use `choose κ hκS hκ using hlift`. Establish `hψinj : Function.Injective ψ` using `φ.symm.injective.comp LinearMap.inl_injective`. Establish `hli : LinearIndependent A (fun j => (ψ (Finsupp.single j 1) : M ⧸ B))`. Establish `h1` using `(Finsupp.basisSingleOne (R := A) (ι := Fin n)).linearIndependent`. Establish `h2` using `h1.map' ψ (LinearMap.ker_eq_bot.mpr hψinj)`.

Establish `h3` using `h2.map' (S.map B.mkQ).subtype (Submodule.ker_subtype _)`. Simplify `h3` using `[Function.comp_def]`. Use `⟨n, κ, hκS, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Establish `h0 : ∑ j, c j • (ψ (Finsupp.single j 1) : M ⧸ B) = 0`.

Repeatedly rewrite using `[← hκ, ← map_smul, ← map_sum]`. Conclude with `(Submodule.Quotient.mk_eq_zero B).mpr hc`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp hli c h0 j`. Introduce `z hz`.

Set `w : S.map B.mkQ` to `⟨B.mkQ z, Submodule.mem_map_of_mem hz⟩`. Set `K` to `∑ i, e i`. Establish `hd : t ^ K • (φ w).2 = 0`. Use `DFinsupp.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[DirectSum.smul_apply, DirectSum.zero_apply]`.

Take `⟨x, hx⟩` from `Submodule.Quotient.mk_surjective _ ((φ w).2 i)`. Rewrite using `[← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`. Take `⟨u, hu⟩` from `((IsDiscreteValuationRing.associated_of_irreducible A (hp i) ht).pow_pow (n := e i)).dvd.trans (pow_dvd_pow t (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))`. Conclude with `⟨u * x, by rw [hu, smul_eq_mul, smul_eq_mul]; ring⟩`. Establish `hφ : t ^ K • w = ψ (t ^ K • (φ w).1)`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_smul]`. Use `show t ^ K • φ w = φ (φ.symm (t ^ K • (φ w).1, 0))`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `ext1`.

Both sides reduce to the same expression. Conclude with `hd`. Use `⟨K, fun j => t ^ K * (φ w).1 j, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, map_sum]`. Repeatedly rewrite using `[map_smul, hκ]`.

Establish `hz' : B.mkQ z = (w : M ⧸ B)` using `rfl`. Rewrite using `[hz', sub_eq_zero, ← Submodule.coe_smul, hφ]`. Use `conv_lhs => rw [← Finsupp.univ_sum_single (t ^ K • (φ w).1)]`. Rewrite using `[map_sum, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.smul_apply, smul_eq_mul, ← Finsupp.smul_single_one, map_smul, Submodule.coe_smul]`.
-/
theorem UpperTheory.V.Pa.Det.maxIndep :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] (t : A) (S B : Submodule A M), Irreducible t → S.FG → ∃ (g : ℕ) (κ : Fin g → M), (∀ j, κ j ∈ S) ∧ (∀ c : Fin g → A, ∑ j, c j • κ j ∈ B → c = 0) ∧ ∀ z ∈ S, ∃ (s : ℕ) (c : Fin g → A), t ^ s • z - ∑ j, c j • κ j ∈ B := by
  intro A M _ _ _ _ _ t S B ht hS
  haveI : Module.Finite A (S.map B.mkQ) := Module.Finite.iff_fg.mpr (hS.map _)
  obtain ⟨n, ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_free_prod_directSum A (S.map B.mkQ)
  let ψ : (Fin n →₀ A) →ₗ[A] S.map B.mkQ := φ.symm.toLinearMap ∘ₗ LinearMap.inl A _ _
  have hlift : ∀ j : Fin n, ∃ m ∈ S, B.mkQ m = (ψ (Finsupp.single j 1) : M ⧸ B) :=
    fun j => Submodule.mem_map.mp (ψ (Finsupp.single j 1)).2
  choose κ hκS hκ using hlift
  have hψinj : Function.Injective ψ := φ.symm.injective.comp LinearMap.inl_injective
  have hli : LinearIndependent A (fun j => (ψ (Finsupp.single j 1) : M ⧸ B)) := by
    have h1 := (Finsupp.basisSingleOne (R := A) (ι := Fin n)).linearIndependent
    have h2 := h1.map' ψ (LinearMap.ker_eq_bot.mpr hψinj)
    have h3 := h2.map' (S.map B.mkQ).subtype (Submodule.ker_subtype _)
    simpa [Function.comp_def] using h3
  refine ⟨n, κ, hκS, ?_, ?_⟩
  · intro c hc
    have h0 : ∑ j, c j • (ψ (Finsupp.single j 1) : M ⧸ B) = 0 := by
      simp_rw [← hκ, ← map_smul, ← map_sum]
      exact (Submodule.Quotient.mk_eq_zero B).mpr hc
    funext j
    exact Fintype.linearIndependent_iff.mp hli c h0 j
  · intro z hz
    let w : S.map B.mkQ := ⟨B.mkQ z, Submodule.mem_map_of_mem hz⟩
    let K := ∑ i, e i
    have hd : t ^ K • (φ w).2 = 0 := by
      refine DFinsupp.ext fun i => ?_
      rw [DirectSum.smul_apply, DirectSum.zero_apply]
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((φ w).2 i)
      rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
      obtain ⟨u, hu⟩ := ((IsDiscreteValuationRing.associated_of_irreducible A (hp i) ht).pow_pow (n := e i)).dvd.trans
        (pow_dvd_pow t (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
      exact ⟨u * x, by rw [hu, smul_eq_mul, smul_eq_mul]; ring⟩
    have hφ : t ^ K • w = ψ (t ^ K • (φ w).1) := by
      apply φ.injective
      rw [map_smul]
      show t ^ K • φ w = φ (φ.symm (t ^ K • (φ w).1, 0))
      rw [LinearEquiv.apply_symm_apply]
      ext1
      · rfl
      · exact hd
    refine ⟨K, fun j => t ^ K * (φ w).1 j, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, map_sum]
    simp_rw [map_smul, hκ]
    have hz' : B.mkQ z = (w : M ⧸ B) := rfl
    rw [hz', sub_eq_zero, ← Submodule.coe_smul, hφ]
    conv_lhs => rw [← Finsupp.univ_sum_single (t ^ K • (φ w).1)]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, ← Finsupp.smul_single_one, map_smul, Submodule.coe_smul]
