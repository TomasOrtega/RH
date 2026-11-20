import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)`. Use `⟨k + 1, fun x hxI hxm => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ maximalIdeal R ^ (k + 1) • (⊤ : Submodule R R) ⊓ (I : Submodule R R)`. Use `⟨?_, hxI⟩` and prove the remaining obligations. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`.

Conclude with `hxm`. Rewrite `hx` using `[hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one]`. Establish `hle : maximalIdeal R • (maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R)) ≤ maximalIdeal R • (I : Submodule R R)` using `Submodule.smul_mono le_rfl inf_le_right`. Establish `hx'` using `hle hx`. Rewrite `hx'` using `[Ideal.smul_eq_mul, h]`.

Conclude with `(Submodule.mem_bot R).1 hx'`.
-/
private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ maximalIdeal R ^ (k + 1) • (⊤ : Submodule R R) ⊓ (I : Submodule R R) := by
    refine ⟨?_, hxI⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hxm
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hle : maximalIdeal R • (maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R))
      ≤ maximalIdeal R • (I : Submodule R R) :=
    Submodule.smul_mono le_rfl inf_le_right
  have hx' := hle hx
  rw [Ideal.smul_eq_mul, h] at hx'
  exact (Submodule.mem_bot R).1 hx'

/- English proof (translation)
Introduce `O _ _ C' _ _ _ C _ _ _ p hp hker Γ _ x hx`. Establish `hmem : ∀ z : C', p z ∈ maximalIdeal C ↔ z ∈ maximalIdeal C'`. Introduce `z`. Rewrite using `[← res_eq_zero_iff O C, ← res_eq_zero_iff O C', res_map]`. Establish `hmap : Ideal.map p (maximalIdeal C') = maximalIdeal C`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `z hz`. Conclude with `(hmem z).2 hz`. Introduce `c hc`.

Take `⟨z, rfl⟩` from `hp c`. Conclude with `Ideal.mem_map_of_mem p ((hmem z).1 hc)`. Establish `hpow : ∀ n : ℕ, ∀ c ∈ maximalIdeal C ^ n, ∃ z ∈ maximalIdeal C' ^ n, p z = c`. Introduce `n c hc`. Rewrite `hc` using `[← hmap, ← Ideal.map_pow]`.

Conclude with `(Ideal.mem_map_iff_of_surjective p hp).1 hc`. Use `haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O`. Take `⟨N₀, hN₀⟩` from `inf_pow_bot C' (RingHom.ker p) hker`. Establish `hq : Function.Surjective (fun z : C' => Ideal.Quotient.mk (maximalIdeal C ^ N₀) (p z))` using `Ideal.Quotient.mk_surjective.comp hp`. Set `σ` to `Function.surjInv hq`.

Establish `hσ : ∀ c : C, c - p (σ (Ideal.Quotient.mk _ c)) ∈ maximalIdeal C ^ N₀`. Introduce `c`. Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises. Conclude with `(Function.surjInv_eq hq (Ideal.Quotient.mk _ c)).symm`. Establish `hw : ∀ c : C, ∃ w ∈ maximalIdeal C' ^ N₀, p w = c - p (σ (Ideal.Quotient.mk _ c))` using `fun c => hpow N₀ _ (hσ c)`.

Use `choose w hwm hwp using hw`. Set `s : C → C'` to `fun c => σ (Ideal.Quotient.mk (maximalIdeal C ^ N₀) c) + w c`. Establish `hs : ∀ c, p (s c) = c`. Introduce `c`. Simplify using `only [s, map_add, hwp]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsd : ∀ n ≥ N₀, ∀ c₁ c₂ : C, c₁ - c₂ ∈ maximalIdeal C ^ n → s c₁ - s c₂ ∈ maximalIdeal C' ^ n`. Introduce `n hn c₁ c₂ h`. Establish `hcl : Ideal.Quotient.mk (maximalIdeal C ^ N₀) c₁ = Ideal.Quotient.mk _ c₂` using `Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hn h)`. Take `⟨z, hz, hpz⟩` from `hpow n _ h`.

Establish `hdiff : s c₁ - s c₂ = w c₁ - w c₂`. Simplify using `only [s, hcl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz0 : (s c₁ - s c₂) - z = 0`. Apply `hN₀` to reduce the goal to its premises.

Rewrite using `[RingHom.mem_ker]`. Simplify using `[map_sub, hs, hpz]`. Rewrite using `[hdiff]`. Conclude with `sub_mem (sub_mem (hwm c₁) (hwm c₂)) (Ideal.pow_le_pow_right hn hz)`. Rewrite using `[sub_eq_zero.1 hz0]`.

Conclude with `hz`. Use `⟨fun g => s (x g), ?_, fun g => hs (x g)⟩` and prove the remaining obligations. Introduce `n`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g`.

Establish `hxl` using `(IsLocallyConstant.iff_eventually_eq _).1 (hx (max n N₀)) g`. Use `filter_upwards [hxl] with g' hg'`. Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Conclude with `Ideal.pow_le_pow_right (le_max_left n N₀) (hsd _ (le_max_right _ _) _ _ (Ideal.Quotient.eq.1 hg'))`.
-/
theorem UpperTheory.V.Fr.pr_sec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → ∀ (Γ : Type) [TopologicalSpace Γ] (x : Γ → C), AdicCont (maximalIdeal C) x → ∃ y : Γ → C', AdicCont (maximalIdeal C') y ∧ ∀ g, p (y g) = x g := by
  intro O _ _ C' _ _ _ C _ _ _ p hp hker Γ _ x hx
  have hmem : ∀ z : C', p z ∈ maximalIdeal C ↔ z ∈ maximalIdeal C' := by
    intro z
    rw [← res_eq_zero_iff O C, ← res_eq_zero_iff O C', res_map]
  have hmap : Ideal.map p (maximalIdeal C') = maximalIdeal C := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmem z).2 hz
    · intro c hc
      obtain ⟨z, rfl⟩ := hp c
      exact Ideal.mem_map_of_mem p ((hmem z).1 hc)
  have hpow : ∀ n : ℕ, ∀ c ∈ maximalIdeal C ^ n, ∃ z ∈ maximalIdeal C' ^ n, p z = c := by
    intro n c hc
    rw [← hmap, ← Ideal.map_pow] at hc
    exact (Ideal.mem_map_iff_of_surjective p hp).1 hc
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  obtain ⟨N₀, hN₀⟩ := inf_pow_bot C' (RingHom.ker p) hker
  have hq : Function.Surjective (fun z : C' => Ideal.Quotient.mk (maximalIdeal C ^ N₀) (p z)) :=
    Ideal.Quotient.mk_surjective.comp hp
  let σ := Function.surjInv hq
  have hσ : ∀ c : C, c - p (σ (Ideal.Quotient.mk _ c)) ∈ maximalIdeal C ^ N₀ := by
    intro c
    apply Ideal.Quotient.eq.1
    exact (Function.surjInv_eq hq (Ideal.Quotient.mk _ c)).symm
  have hw : ∀ c : C, ∃ w ∈ maximalIdeal C' ^ N₀, p w = c - p (σ (Ideal.Quotient.mk _ c)) :=
    fun c => hpow N₀ _ (hσ c)
  choose w hwm hwp using hw
  let s : C → C' := fun c => σ (Ideal.Quotient.mk (maximalIdeal C ^ N₀) c) + w c
  have hs : ∀ c, p (s c) = c := by
    intro c
    simp only [s, map_add, hwp]
    ring
  have hsd : ∀ n ≥ N₀, ∀ c₁ c₂ : C, c₁ - c₂ ∈ maximalIdeal C ^ n →
      s c₁ - s c₂ ∈ maximalIdeal C' ^ n := by
    intro n hn c₁ c₂ h
    have hcl : Ideal.Quotient.mk (maximalIdeal C ^ N₀) c₁ = Ideal.Quotient.mk _ c₂ :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hn h)
    obtain ⟨z, hz, hpz⟩ := hpow n _ h
    have hdiff : s c₁ - s c₂ = w c₁ - w c₂ := by
      simp only [s, hcl]
      ring
    have hz0 : (s c₁ - s c₂) - z = 0 := by
      apply hN₀
      · rw [RingHom.mem_ker]
        simp [map_sub, hs, hpz]
      · rw [hdiff]
        exact sub_mem (sub_mem (hwm c₁) (hwm c₂)) (Ideal.pow_le_pow_right hn hz)
    rw [sub_eq_zero.1 hz0]
    exact hz
  refine ⟨fun g => s (x g), ?_, fun g => hs (x g)⟩
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hxl := (IsLocallyConstant.iff_eventually_eq _).1 (hx (max n N₀)) g
  filter_upwards [hxl] with g' hg'
  apply Ideal.Quotient.eq.2
  exact Ideal.pow_le_pow_right (le_max_left n N₀)
    (hsd _ (le_max_right _ _) _ _ (Ideal.Quotient.eq.1 hg'))
