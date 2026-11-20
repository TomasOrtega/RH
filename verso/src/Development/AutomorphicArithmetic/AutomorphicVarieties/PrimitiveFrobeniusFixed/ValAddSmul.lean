import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Rewrite using `[ZMod.val_add, ← add_smul]`. Use `conv_rhs => rw [← Nat.mod_add_div' (a.val + b.val) M]`. Rewrite using `[add_smul, mul_smul, hx, smul_zero, add_zero]`.
-/
private theorem val_add_smul {W : Type} [AddCommGroup W] {M : ℕ} [NeZero M] (x : W) (hx : M • x = 0) (a b : ZMod M) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← add_smul]
  conv_rhs => rw [← Nat.mod_add_div' (a.val + b.val) M]
  rw [add_smul, mul_smul, hx, smul_zero, add_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `IsLocallyConstant.const (0 : W)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`.

Conclude with `(h a).add ih`.
-/
private theorem lc_sum {X ι W : Type} [TopologicalSpace X] [AddCommGroup W] (s : Finset ι) (f : ι → X → W)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const (0 : W)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

/- English proof (translation)
Introduce `Ω _ _ _ O W _ _ _ M F n _ _ hFn β hβ σ hσ w hw κ hκ hlc hunr`. Establish `hF0 : F ≠ 0` using `NeZero.ne F`. Take `⟨hN, -, -, -, hlift, -, -, -, -, hmul⟩` from `galBasic Ω F hF0`. Establish `pb` using `(placeBasic Ω).2.2.2.2.2.2.2.2.2`. Establish `hcm : ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, g⁻¹ * u * g ∈ fixMu ℚ Ω F`.

Introduce `g u hu`. Use `hN.conj_mem u hu g⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hfix : ∀ k ∈ fixMu ℚ Ω F, ∀ x : W, M • x = 0 → (β k : O) • x = x`. Introduce `k hk x hx`.

Take `⟨c, hc⟩` from `hβ k hk`. Establish `e : (β k : O) = 1 + c * M`. Rewrite using `[mul_comm, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero, add_zero]`.

Establish `hx : ∀ g : G ℚ Ω, M • ((β g : O) • w) = 0`. Introduce `g`. Rewrite using `[smul_comm, hw, smul_zero]`. Establish `h1 : κ 1 = 0`. Use `hκ 1 (one_mem _) 1 (one_mem _)` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Take the linear combination `-this`. Establish `hinv : ∀ k ∈ fixMu ℚ Ω F, κ k⁻¹ + κ k = 0`. Introduce `k hk`. Rewrite using `[← hκ _ (inv_mem hk) _ hk, inv_mul_cancel, h1]`.

Establish `hconj : ∀ k ∈ fixMu ℚ Ω F, ∀ y ∈ fixMu ℚ Ω F, κ (k⁻¹ * y * k) = κ y`. Introduce `k hk y hy`. Rewrite using `[hκ _ (mul_mem (inv_mem hk) hy) _ hk, hκ _ (inv_mem hk) _ hy]`. Take the linear combination `hinv k hk`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu v hv`. Simplify using `only [nu]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Establish `e : (σ t)⁻¹ * (u * v) * σ t = ((σ t)⁻¹ * u * σ t) * ((σ t)⁻¹ * v * σ t)` using `by group`.

Rewrite using `[e, hκ _ (hcm _ u hu) _ (hcm _ v hv)]`. Conclude with `val_add_smul _ (hx (σ t)) _ _`. Simplify using `only [nu]`. Apply `lc_sum` to reduce the goal to its premises. Introduce `t`.

Set `c : fixMu ℚ Ω F → fixMu ℚ Ω F` to `fun u => ⟨(σ t)⁻¹ * u * σ t, hcm _ u u.2⟩`. Establish `hc : Continuous c` using `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`. Conclude with `(hlc.comp_continuous hc).comp (fun k : ZMod M => k.val • ((β (σ t) : O) • w))`. Introduce `g u hu`. Take `⟨b, hb⟩` from `hlift g`.

Simplify using `only [nu]`. Rewrite using `[Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft b) (fun t => (κ ((σ t)⁻¹ * (g * u * g⁻¹) * σ t)).val • (β (σ t) : O) • w)]`. Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Use `show (κ ((σ (b * s))⁻¹ * (g * u * g⁻¹) * σ (b * s))).val • (β (σ (b * s)) : O) • w = _`. Establish `hk0 : (g * σ s)⁻¹ * σ (b * s) ∈ fixMu ℚ Ω F` using `(hmul (b * s) (b * s) (g * σ s) (σ (b * s)) (hmul b s g (σ s) hb (hσ s)).1 (hσ (b * s))).2.2.mp rfl`.

Take `⟨k, hk, hτ⟩ : ∃ k ∈ fixMu ℚ Ω F, σ (b * s) = g * σ s * k` from `⟨_, hk0, by group⟩`. Rewrite using `[hτ]`. Establish `e : (g * σ s * k)⁻¹ * (g * u * g⁻¹) * (g * σ s * k) = k⁻¹ * ((σ s)⁻¹ * u * σ s) * k` using `by group`. Rewrite using `[e, hconj k hk _ (hcm _ u hu), map_mul, map_mul, Units.val_mul, Units.val_mul, mul_smul, mul_smul, hfix k hk w hw]`. Conclude with `smul_comm _ _ _`.

Introduce `u hu`. Simplify using `only [nu]`. Rewrite using `[Finset.smul_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `t _`.

Rewrite using `[smul_comm, hx (σ t), smul_zero]`. Introduce `A hA g hg`. Simplify using `only [nu]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `t _`.

Establish `hA' : ¬ Over ((σ t)⁻¹ • A) n`. Introduce `h'`. Apply `hA` to reduce the goal to its premises. Use `((pb A (σ t)⁻¹).2.2.2.1 (n : Ω)).1` as an intermediate fact. Rewrite `this` using `[map_natCast]`.

Conclude with `this h'`. Establish `hmem : (σ t)⁻¹ * g * σ t ∈ Ine (F` using `ℚ) ((σ t)⁻¹ • A) := by`. Rewrite using `[(pb A (σ t)⁻¹).2.1]`. Establish `e : (σ t)⁻¹⁻¹ * ((σ t)⁻¹ * g * σ t) * (σ t)⁻¹ = g` using `by group`. Rewrite using `[e]`.

Conclude with `hg`. Rewrite using `[hunr _ hA' _ hmem, ZMod.val_zero, zero_smul]`.
-/
theorem UpperTheory.V.ML.nuIs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ) [NeZero M] [NeZero F], F ∣ n → ∀ (β : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, (M : O) ∣ (β g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ w : W, M • w = 0 → ∀ κ : G ℚ Ω → ZMod M, (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) → IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) →
    (∀ A : ValuationSubring Ω, ¬ Over A n → ∀ g ∈ Ine (F := ℚ) A, κ g = 0) → IsNu M F n β (nu β σ w κ) := by
  intro Ω _ _ _ O W _ _ _ M F n _ _ hFn β hβ σ hσ w hw κ hκ hlc hunr
  have hF0 : F ≠ 0 := NeZero.ne F
  obtain ⟨hN, -, -, -, hlift, -, -, -, -, hmul⟩ := galBasic Ω F hF0
  have pb := (placeBasic Ω).2.2.2.2.2.2.2.2.2
  have hcm : ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, g⁻¹ * u * g ∈ fixMu ℚ Ω F := by
    intro g u hu
    have := hN.conj_mem u hu g⁻¹
    rwa [inv_inv] at this
  have hfix : ∀ k ∈ fixMu ℚ Ω F, ∀ x : W, M • x = 0 → (β k : O) • x = x := by
    intro k hk x hx
    obtain ⟨c, hc⟩ := hβ k hk
    have e : (β k : O) = 1 + c * M := by
      rw [mul_comm, ← hc]
      ring
    rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero, add_zero]
  have hx : ∀ g : G ℚ Ω, M • ((β g : O) • w) = 0 := by
    intro g
    rw [smul_comm, hw, smul_zero]
  have h1 : κ 1 = 0 := by
    have := hκ 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hinv : ∀ k ∈ fixMu ℚ Ω F, κ k⁻¹ + κ k = 0 := by
    intro k hk
    rw [← hκ _ (inv_mem hk) _ hk, inv_mul_cancel, h1]
  have hconj : ∀ k ∈ fixMu ℚ Ω F, ∀ y ∈ fixMu ℚ Ω F, κ (k⁻¹ * y * k) = κ y := by
    intro k hk y hy
    rw [hκ _ (mul_mem (inv_mem hk) hy) _ hk, hκ _ (inv_mem hk) _ hy]
    linear_combination hinv k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    simp only [nu]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e : (σ t)⁻¹ * (u * v) * σ t = ((σ t)⁻¹ * u * σ t) * ((σ t)⁻¹ * v * σ t) := by group
    rw [e, hκ _ (hcm _ u hu) _ (hcm _ v hv)]
    exact val_add_smul _ (hx (σ t)) _ _
  · simp only [nu]
    apply lc_sum
    intro t
    let c : fixMu ℚ Ω F → fixMu ℚ Ω F := fun u => ⟨(σ t)⁻¹ * u * σ t, hcm _ u u.2⟩
    have hc : Continuous c :=
      Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
    exact (hlc.comp_continuous hc).comp (fun k : ZMod M => k.val • ((β (σ t) : O) • w))
  · intro g u hu
    obtain ⟨b, hb⟩ := hlift g
    simp only [nu]
    rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft b)
      (fun t => (κ ((σ t)⁻¹ * (g * u * g⁻¹) * σ t)).val • (β (σ t) : O) • w)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    show (κ ((σ (b * s))⁻¹ * (g * u * g⁻¹) * σ (b * s))).val • (β (σ (b * s)) : O) • w = _
    have hk0 : (g * σ s)⁻¹ * σ (b * s) ∈ fixMu ℚ Ω F :=
      (hmul (b * s) (b * s) (g * σ s) (σ (b * s)) (hmul b s g (σ s) hb (hσ s)).1 (hσ (b * s))).2.2.mp rfl
    obtain ⟨k, hk, hτ⟩ : ∃ k ∈ fixMu ℚ Ω F, σ (b * s) = g * σ s * k := ⟨_, hk0, by group⟩
    rw [hτ]
    have e : (g * σ s * k)⁻¹ * (g * u * g⁻¹) * (g * σ s * k) = k⁻¹ * ((σ s)⁻¹ * u * σ s) * k := by group
    rw [e, hconj k hk _ (hcm _ u hu), map_mul, map_mul, Units.val_mul, Units.val_mul, mul_smul, mul_smul,
      hfix k hk w hw]
    exact smul_comm _ _ _
  · intro u hu
    simp only [nu]
    rw [Finset.smul_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [smul_comm, hx (σ t), smul_zero]
  · intro A hA g hg
    simp only [nu]
    apply Finset.sum_eq_zero
    intro t _
    have hA' : ¬ Over ((σ t)⁻¹ • A) n := by
      intro h'
      apply hA
      have := ((pb A (σ t)⁻¹).2.2.2.1 (n : Ω)).1
      rw [map_natCast] at this
      exact this h'
    have hmem : (σ t)⁻¹ * g * σ t ∈ Ine (F := ℚ) ((σ t)⁻¹ • A) := by
      rw [(pb A (σ t)⁻¹).2.1]
      have e : (σ t)⁻¹⁻¹ * ((σ t)⁻¹ * g * σ t) * (σ t)⁻¹ = g := by group
      rw [e]
      exact hg
    rw [hunr _ hA' _ hmem, ZMod.val_zero, zero_smul]
