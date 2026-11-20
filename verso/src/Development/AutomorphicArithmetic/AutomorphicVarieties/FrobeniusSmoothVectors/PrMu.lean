import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker`. Establish `hwd : ∀ y y' : K, u y = u y' → q y = q y'`. Introduce `y y' h`. Establish `h0 : u (y - y') = 0` using `by rw [map_sub, h, sub_self]`. Establish `h1` using `hker _ h0`.

Rewrite `h1` using `[Submodule.coe_sub, map_sub, sub_eq_zero]`. Conclude with `h1`. Establish `hmem : ∀ y : K, q y ∈ maximalIdeal C''`. Introduce `y`. Rewrite using `[← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]`.

Conclude with `hKm y.2`. Distinguish the cases in `hu : ∀ y, u y = 0`. Use `⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩ show (0 : C'') = q y` and prove the remaining obligations. Conclude with `(hker y (hu y)).symm`. Use `push_neg at hu`.

Take `⟨y0, hy0⟩` from `hu`. Establish `hsurj : Function.Surjective u`. Introduce `c`. Take `⟨o, ho⟩` from `IsLocalRing.residue_surjective (c * (u y0)⁻¹)`. Use `⟨o • y0, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, Algebra.smul_def]`. Use `show residue O o * u y0 = c`. Rewrite using `[ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]`. Set `s` to `Function.surjInv hsurj`. Establish `hs : ∀ c, u (s c) = c` using `Function.surjInv_eq hsurj`.

Set `μ : ResidueField O →+ C''` to `{ toFun := fun c => q (s c) map_zero' := by show q (s 0 : C') = 0`. Rewrite using `[hwd (s 0) 0 (by rw [hs, map_zero])]`. Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `c d`.

Use `show q (s (c + d) : C') = q (s c : C') + q (s d : C')`. Rewrite using `[hwd (s (c + d)) (s c + s d) (by rw [hs, map_add, hs, hs]), Submodule.coe_add, map_add] }`. Establish `hμ : ∀ c, μ c = q (s c)` using `fun c => rfl`. Use `⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c`.

Take `⟨b, rfl⟩` from `hq a`. Take `⟨o, ho⟩` from `IsCO.res_surj (O := O) b`. Establish `hby : b * (s c : C') = o • (s c : C')`. Establish `hz : (b - algebraMap O C' o) * (s c : C') = 0`. Establish `hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K` using `Ideal.mul_mem_mul ho (s c).2`.

Rewrite `hin` using `[hmK]`. Simplify using `using hin`. Rewrite using `[Algebra.smul_def]`. Take the linear combination `hz`. Establish `hres : res O C' b = algebraMap O (ResidueField O) o`.

Rewrite using `[← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]`. Conclude with `ho`. Establish `hw` using `hwd (s (res O C'' (q b) * c)) (o • s c) (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])`. Rewrite using `[hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]`. Introduce `c`.

Rewrite using `[hμ]`. Conclude with `hmem _`. Introduce `y`. Rewrite using `[hμ]`. Conclude with `hwd _ _ (hs _)`.

Introduce `c`. Conclude with `⟨s c, rfl⟩`.
-/
theorem UpperTheory.V.Fr.pr_mu :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (K : Ideal C') (q : C' →ₐ[O] C'') (u : K →ₗ[O] ResidueField O), maximalIdeal C' * K = ⊥ → K ≤ maximalIdeal C' → Function.Surjective q → (∀ y : K, u y = 0 → q y = 0) → ∃ μ : ResidueField O →+ C'', IsSq O μ ∧ (∀ y : K, μ (u y) = q y) ∧ ∀ c, ∃ y : K, μ c = q y := by
  intro O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker
  classical
  have hwd : ∀ y y' : K, u y = u y' → q y = q y' := by
    intro y y' h
    have h0 : u (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker _ h0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    exact h1
  have hmem : ∀ y : K, q y ∈ maximalIdeal C'' := by
    intro y
    rw [← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]
    exact hKm y.2
  by_cases hu : ∀ y, u y = 0
  · refine ⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩
    show (0 : C'') = q y
    exact (hker y (hu y)).symm
  · push_neg at hu
    obtain ⟨y0, hy0⟩ := hu
    have hsurj : Function.Surjective u := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (c * (u y0)⁻¹)
      refine ⟨o • y0, ?_⟩
      rw [map_smul, Algebra.smul_def]
      show residue O o * u y0 = c
      rw [ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    let s := Function.surjInv hsurj
    have hs : ∀ c, u (s c) = c := Function.surjInv_eq hsurj
    let μ : ResidueField O →+ C'' :=
      { toFun := fun c => q (s c)
        map_zero' := by
          show q (s 0 : C') = 0
          rw [hwd (s 0) 0 (by rw [hs, map_zero])]
          simp
        map_add' := by
          intro c d
          show q (s (c + d) : C') = q (s c : C') + q (s d : C')
          rw [hwd (s (c + d)) (s c + s d) (by rw [hs, map_add, hs, hs]), Submodule.coe_add, map_add] }
    have hμ : ∀ c, μ c = q (s c) := fun c => rfl
    refine ⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro a c
      obtain ⟨b, rfl⟩ := hq a
      obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
      have hby : b * (s c : C') = o • (s c : C') := by
        have hz : (b - algebraMap O C' o) * (s c : C') = 0 := by
          have hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K :=
            Ideal.mul_mem_mul ho (s c).2
          rw [hmK] at hin
          simpa using hin
        rw [Algebra.smul_def]
        linear_combination hz
      have hres : res O C' b = algebraMap O (ResidueField O) o := by
        rw [← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]
        exact ho
      have hw := hwd (s (res O C'' (q b) * c)) (o • s c)
        (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])
      rw [hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]
    · intro c
      rw [hμ]
      exact hmem _
    · intro y
      rw [hμ]
      exact hwd _ _ (hs _)
    · intro c
      exact ⟨s c, rfl⟩
