import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)`. Use `⟨k + 1, fun x hxI hxm => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ (I : Submodule R R))` using `⟨by simpa [smul_eq_mul] using hxm, hxI⟩`. Rewrite `hx` using `[hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one]`. Establish `hmem : x ∈ maximalIdeal R • (I : Submodule R R)` using `Submodule.smul_mono le_rfl inf_le_right hx`.

Rewrite `hmem` using `[smul_eq_mul, h]`. Simplify using `using hmem`.
-/
private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ (I : Submodule R R)) :=
    ⟨by simpa [smul_eq_mul] using hxm, hxI⟩
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hmem : x ∈ maximalIdeal R • (I : Submodule R R) := Submodule.smul_mono le_rfl inf_le_right hx
  rw [smul_eq_mul, h] at hmem
  simpa using hmem

/- English proof (translation)
Introduce `Λ _ _ _ _ A R _ _ _ _ _ _ p hp hK`. Use `haveI : IsNoetherianRing A := IsCO.toIsNoetherian Λ`. Take `⟨N0, hN0⟩` from `inf_pow_bot A (RingHom.ker p) hK`. Establish `hm : ∀ a : A, a ∈ maximalIdeal A ↔ p a ∈ maximalIdeal R`. Introduce `a`.

Rewrite using `[← res_eq_zero_iff Λ A, ← res_eq_zero_iff Λ R, res_map]`. Establish `hmap1 : Ideal.map p (maximalIdeal A) = maximalIdeal R`. Use extensionality with `r`. Rewrite using `[Ideal.mem_map_iff_of_surjective p hp]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `(hm a).mp ha`. Introduce `hr`. Take `⟨a, rfl⟩` from `hp r`. Conclude with `⟨a, (hm a).mpr hr, rfl⟩`.

Establish `hmap : ∀ n, ∀ r ∈ maximalIdeal R ^ n, ∃ z ∈ maximalIdeal A ^ n, p z = r`. Introduce `n r hr`. Rewrite `hr` using `[← hmap1, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective p hp]`. Conclude with `hr`. Use `choose ρ hρ using fun c : R ⧸ maximalIdeal R ^ N0 => Ideal.Quotient.mk_surjective c`.

Use `choose l hl using fun c : R ⧸ maximalIdeal R ^ N0 => hp (ρ c)`. Establish `hu : ∀ r : R, ∃ z ∈ maximalIdeal A ^ N0, p z = r - ρ (Ideal.Quotient.mk _ r)`. Introduce `r`. Apply `hmap` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq, hρ]`.

Use `choose u hu1 hu2 using hu`. Set `σ : R → A` to `fun r => l (Ideal.Quotient.mk _ r) + u r`. Establish `hpσ : ∀ r, p (σ r) = r`. Introduce `r`. Simplify using `only [σ, map_add, hl, hu2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hL : ∀ M, N0 ≤ M → ∀ r r' : R, r - r' ∈ maximalIdeal R ^ M → σ r - σ r' ∈ maximalIdeal A ^ M`. Introduce `M hM r r' h`. Establish `hq : (Ideal.Quotient.mk (maximalIdeal R ^ N0) r) = Ideal.Quotient.mk _ r'` using `Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hM h)`. Take `⟨z, hz, hpz⟩` from `hmap M _ h`.

Establish `hzero : z - (u r - u r') = 0`. Apply `hN0` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker]`. Simplify using `only [map_sub]`. Rewrite using `[hpz, hu2, hu2, hq]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_mem (Ideal.pow_le_pow_right hM hz) (sub_mem (hu1 r) (hu1 r'))`. Establish `hz' : u r - u r' = z` using `(sub_eq_zero.mp hzero).symm`. Simplify using `only [σ]`. Rewrite using `[hq, add_sub_add_left_eq_sub, hz']`.

Conclude with `hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `S _ x hx`. Use `⟨fun s => σ (x s), ?_, fun s => hpσ _⟩` and prove the remaining obligations. Introduce `n`.

Establish `hc` using `hx (max n N0)`. Rewrite `hc`, the goal using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Use `filter_upwards [hc s] with s' hs'`. Establish `h1` using `Ideal.Quotient.eq.mp hs'`.

Establish `h2` using `hL (max n N0) (le_max_right _ _) _ _ h1`. Conclude with `Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right (le_max_left _ _) h2)`. Introduce `S _ y hy h0`. Establish `hc` using `hy N0`. Rewrite `hc`, the goal using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `s`. Use `filter_upwards [hc s] with s' hs'`. Establish `h1` using `Ideal.Quotient.eq.mp hs'`. Establish `h2 : y s' - y s = 0`. Apply `hN0 _ _ h1` to reduce the goal to its premises.

Rewrite using `[RingHom.mem_ker, map_sub, h0, h0, sub_zero]`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem UpperTheory.V.Ws.X1.contLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → (∀ (S : Type) [TopologicalSpace S] (x : S → R), AdicCont (maximalIdeal R) x → ∃ y : S → A, AdicCont (maximalIdeal A) y ∧ ∀ s, p (y s) = x s) ∧ ∀ (S : Type) [TopologicalSpace S] (y : S → A), AdicCont (maximalIdeal A) y → (∀ s, p (y s) = 0) → IsLocallyConstant y := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p hp hK
  haveI : IsNoetherianRing A := IsCO.toIsNoetherian Λ
  obtain ⟨N0, hN0⟩ := inf_pow_bot A (RingHom.ker p) hK
  have hm : ∀ a : A, a ∈ maximalIdeal A ↔ p a ∈ maximalIdeal R := by
    intro a
    rw [← res_eq_zero_iff Λ A, ← res_eq_zero_iff Λ R, res_map]
  have hmap1 : Ideal.map p (maximalIdeal A) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hm a).mp ha
    · intro hr
      obtain ⟨a, rfl⟩ := hp r
      exact ⟨a, (hm a).mpr hr, rfl⟩
  have hmap : ∀ n, ∀ r ∈ maximalIdeal R ^ n, ∃ z ∈ maximalIdeal A ^ n, p z = r := by
    intro n r hr
    rw [← hmap1, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective p hp] at hr
    exact hr
  choose ρ hρ using fun c : R ⧸ maximalIdeal R ^ N0 => Ideal.Quotient.mk_surjective c
  choose l hl using fun c : R ⧸ maximalIdeal R ^ N0 => hp (ρ c)
  have hu : ∀ r : R, ∃ z ∈ maximalIdeal A ^ N0, p z = r - ρ (Ideal.Quotient.mk _ r) := by
    intro r
    apply hmap
    rw [← Ideal.Quotient.eq, hρ]
  choose u hu1 hu2 using hu
  let σ : R → A := fun r => l (Ideal.Quotient.mk _ r) + u r
  have hpσ : ∀ r, p (σ r) = r := by
    intro r
    simp only [σ, map_add, hl, hu2]
    ring
  have hL : ∀ M, N0 ≤ M → ∀ r r' : R, r - r' ∈ maximalIdeal R ^ M → σ r - σ r' ∈ maximalIdeal A ^ M := by
    intro M hM r r' h
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N0) r) = Ideal.Quotient.mk _ r' :=
      Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hM h)
    obtain ⟨z, hz, hpz⟩ := hmap M _ h
    have hzero : z - (u r - u r') = 0 := by
      apply hN0
      · rw [RingHom.mem_ker]
        simp only [map_sub]
        rw [hpz, hu2, hu2, hq]
        ring
      · exact sub_mem (Ideal.pow_le_pow_right hM hz) (sub_mem (hu1 r) (hu1 r'))
    have hz' : u r - u r' = z := (sub_eq_zero.mp hzero).symm
    simp only [σ]
    rw [hq, add_sub_add_left_eq_sub, hz']
    exact hz
  refine ⟨?_, ?_⟩
  · intro S _ x hx
    refine ⟨fun s => σ (x s), ?_, fun s => hpσ _⟩
    intro n
    have hc := hx (max n N0)
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 := hL (max n N0) (le_max_right _ _) _ _ h1
    exact Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right (le_max_left _ _) h2)
  · intro S _ y hy h0
    have hc := hy N0
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 : y s' - y s = 0 := by
      apply hN0 _ _ h1
      rw [RingHom.mem_ker, map_sub, h0, h0, sub_zero]
    exact sub_eq_zero.mp h2
