import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩`. Conclude with `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) x hx`.
-/
private theorem cyc_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ)
    (g : G ℚ Ω) (x : Ω) (hx : x ^ l ^ m = 1) :
    g x = x ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) x hx

/- English proof (translation)
Establish `h : PadicInt.toZModPow m (z - ((PadicInt.toZModPow m z).val : ℤ_[l])) = 0`. Simplify using the standard rewrite rules. Establish `hk : z - ((PadicInt.toZModPow m z).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p` using `l) m) := h`. Rewrite `hk` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Conclude with `hk`.
-/
private theorem dvd_sub_val (l : ℕ) [Fact l.Prime] (m : ℕ) (z : ℤ_[l]) :
    (l : ℤ_[l]) ^ m ∣ z - ((PadicInt.toZModPow m z).val : ℤ_[l]) := by
  have h : PadicInt.toZModPow m (z - ((PadicInt.toZModPow m z).val : ℤ_[l])) = 0 := by
    simp
  have hk : z - ((PadicInt.toZModPow m z).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  exact hk

/- English proof (translation)
Introduce `Ω _ _ _ l _ O W _ _ _ _ m F r hF hlF hr ρ hρ γ f hadd hconj htor hfixρ g u hu`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hmem : ∀ w : G ℚ Ω, w ∈ fixMu ℚ Ω F ↔ ∀ x : Ω, x ^ F = 1 → w x = x` using `fun w => Iff.rfl`. Establish `hr0 : (r : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr hr`. Establish `hρ0 : ρ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hρ` using `[zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Conclude with `hr0 hρ.symm`. Establish `hroot : ∀ σ : G ℚ Ω, (σ ρ / ρ) ^ (l ^ m) = 1`. Introduce `σ`.

Rewrite using `[div_pow, ← map_pow, hρ, map_natCast, div_self hr0]`. Establish `hfix : ∀ x : Ω, x ^ (l ^ m) = 1 → u x = x`. Introduce `x hx`. Take `⟨c, hc⟩` from `hlF`. Conclude with `(hmem u).mp hu x (by rw [hc, pow_mul, hx, one_pow])`.

Take `⟨ζ, hζdef⟩ : ∃ ζ, ζ = u ρ / ρ` from `⟨_, rfl⟩`. Establish `hζ : ζ ^ (l ^ m) = 1` using `hζdef ▸ hroot u`. Establish `huρ : u ρ = ζ * ρ` using `by rw [hζdef, div_mul_cancel₀ _ hρ0]`. Establish `hpow : ∀ n : ℕ, (u ^ n) ρ = ζ ^ n * ρ`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfix ζ hζ, huρ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨k, hkdef⟩ : ∃ k, k = (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val` from `⟨_, rfl⟩`. Establish `hgζ : g ζ = ζ ^ k` using `by rw [hkdef]; exact cyc_pow l m g ζ hζ`. Establish `hg : ∀ x : Ω, g (g⁻¹ x) = x`. Introduce `x`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.

Establish `hconjρ : (g * u * g⁻¹) ρ = ζ ^ k * ρ`. Take `⟨ξ, hξdef⟩ : ∃ ξ, ξ = g⁻¹ ρ / ρ` from `⟨_, rfl⟩`. Establish `hξ : g⁻¹ ρ = ξ * ρ` using `by rw [hξdef, div_mul_cancel₀ _ hρ0]`. Establish `hξ1 : ξ ^ (l ^ m) = 1` using `hξdef ▸ hroot g⁻¹`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hξ, map_mul, hfix ξ hξ1, huρ, show ξ * (ζ * ρ) = ζ * (ξ * ρ) by ring, map_mul, ← hξ, hg, hgζ]`.

Establish `hgu : g * u * g⁻¹ ∈ fixMu ℚ Ω F`. Rewrite using `[hmem]`. Introduce `x hx`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, (hmem u).mp hu (g⁻¹ x) (by rw [← map_pow, hx, map_one]), hg]`. Establish `hukm : u ^ k ∈ fixMu ℚ Ω F` using `Subgroup.pow_mem _ hu k`.

Take `⟨v, hvdef⟩ : ∃ v, v = (u ^ k)⁻¹ * (g * u * g⁻¹)` from `⟨_, rfl⟩`. Establish `hv : v ∈ fixMu ℚ Ω F` using `hvdef ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hukm) hgu`. Establish `hvρ : v ρ = ρ`. Rewrite using `[hvdef, AlgEquiv.mul_apply, hconjρ, ← hpow k, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Establish `hsplit : g * u * g⁻¹ = u ^ k * v` using `by rw [hvdef, mul_inv_cancel_left]`.

Establish `hf1 : f 1 = 0`. Establish `h1` using `hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)`. Rewrite `h1` using `[mul_one]`. Simplify using `using h1`. Establish `hfpow : ∀ n : ℕ, f (u ^ n) = n • f u`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, hf1, zero_smul]`. Consider the case `succ n ih => rw [pow_succ, hadd _ (Subgroup.pow_mem _ hu n) _ hu, ih, succ_nsmul]`. Establish `hγ : (γ g : O) • f u = k • f u`.

Rewrite using `[← hconj g u hu, hsplit, hadd _ hukm _ hv, hfixρ v hv hvρ, add_zero, hfpow]`. Establish `hχ : (chiO ℚ Ω l O g : O) • f u = k • f u`. Take `⟨t, ht⟩` from `dvd_sub_val l m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])`. Rewrite `ht` using `[← hkdef]`. Establish `hz : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = (k : ℤ_[l]) + (l : ℤ_[l]) ^ m * t` using `sub_eq_iff_eq_add'.mp ht`.

Establish `hc : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])` using `rfl`. Establish `hlm : ((l : O) ^ m) • f u = 0`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul O (l ^ m) (f u), htor u hu]`. Rewrite using `[hc, hz, map_add, map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_comm, mul_smul, hlm, smul_zero, add_zero, Nat.cast_smul_eq_nsmul O k (f u)]`. Rewrite using `[sub_smul, hγ, hχ, sub_self]`.
-/
theorem UpperTheory.V.ML.radEqv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O W : Type) [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup W] [Module O W] (m F r : ℕ), F ≠ 0 → l ^ m ∣ F → r ≠ 0 → ∀ ρ : Ω, ρ ^ (l ^ m) = (r : Ω) →
    ∀ (γ : G ℚ Ω →* Oˣ) (f : G ℚ Ω → W), (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, f (u * v) = f u + f v) → (∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, f (g * u * g⁻¹) = (γ g : O) • f u) →
    (∀ u ∈ fixMu ℚ Ω F, (l ^ m) • f u = 0) → (∀ u ∈ fixMu ℚ Ω F, u ρ = ρ → f u = 0) → ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, ((γ g : O) - (chiO ℚ Ω l O g : O)) • f u = 0 := by
  intro Ω _ _ _ l _ O W _ _ _ _ m F r hF hlF hr ρ hρ γ f hadd hconj htor hfixρ g u hu
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hmem : ∀ w : G ℚ Ω, w ∈ fixMu ℚ Ω F ↔ ∀ x : Ω, x ^ F = 1 → w x = x := fun w => Iff.rfl
  have hr0 : (r : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hρ
    exact hr0 hρ.symm
  have hroot : ∀ σ : G ℚ Ω, (σ ρ / ρ) ^ (l ^ m) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hfix : ∀ x : Ω, x ^ (l ^ m) = 1 → u x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := hlF
    exact (hmem u).mp hu x (by rw [hc, pow_mul, hx, one_pow])
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = u ρ / ρ := ⟨_, rfl⟩
  have hζ : ζ ^ (l ^ m) = 1 := hζdef ▸ hroot u
  have huρ : u ρ = ζ * ρ := by rw [hζdef, div_mul_cancel₀ _ hρ0]
  have hpow : ∀ n : ℕ, (u ^ n) ρ = ζ ^ n * ρ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfix ζ hζ, huρ, pow_succ]
      ring
  obtain ⟨k, hkdef⟩ : ∃ k, k = (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val := ⟨_, rfl⟩
  have hgζ : g ζ = ζ ^ k := by rw [hkdef]; exact cyc_pow l m g ζ hζ
  have hg : ∀ x : Ω, g (g⁻¹ x) = x := by
    intro x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hconjρ : (g * u * g⁻¹) ρ = ζ ^ k * ρ := by
    obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = g⁻¹ ρ / ρ := ⟨_, rfl⟩
    have hξ : g⁻¹ ρ = ξ * ρ := by rw [hξdef, div_mul_cancel₀ _ hρ0]
    have hξ1 : ξ ^ (l ^ m) = 1 := hξdef ▸ hroot g⁻¹
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hξ, map_mul, hfix ξ hξ1, huρ,
      show ξ * (ζ * ρ) = ζ * (ξ * ρ) by ring, map_mul, ← hξ, hg, hgζ]
  have hgu : g * u * g⁻¹ ∈ fixMu ℚ Ω F := by
    rw [hmem]
    intro x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, (hmem u).mp hu (g⁻¹ x) (by rw [← map_pow, hx, map_one]), hg]
  have hukm : u ^ k ∈ fixMu ℚ Ω F := Subgroup.pow_mem _ hu k
  obtain ⟨v, hvdef⟩ : ∃ v, v = (u ^ k)⁻¹ * (g * u * g⁻¹) := ⟨_, rfl⟩
  have hv : v ∈ fixMu ℚ Ω F := hvdef ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hukm) hgu
  have hvρ : v ρ = ρ := by
    rw [hvdef, AlgEquiv.mul_apply, hconjρ, ← hpow k, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hsplit : g * u * g⁻¹ = u ^ k * v := by rw [hvdef, mul_inv_cancel_left]
  have hf1 : f 1 = 0 := by
    have h1 := hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h1
    simpa using h1
  have hfpow : ∀ n : ℕ, f (u ^ n) = n • f u := by
    intro n
    induction n with
    | zero => rw [pow_zero, hf1, zero_smul]
    | succ n ih => rw [pow_succ, hadd _ (Subgroup.pow_mem _ hu n) _ hu, ih, succ_nsmul]
  have hγ : (γ g : O) • f u = k • f u := by
    rw [← hconj g u hu, hsplit, hadd _ hukm _ hv, hfixρ v hv hvρ, add_zero, hfpow]
  have hχ : (chiO ℚ Ω l O g : O) • f u = k • f u := by
    obtain ⟨t, ht⟩ := dvd_sub_val l m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])
    rw [← hkdef] at ht
    have hz : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = (k : ℤ_[l]) + (l : ℤ_[l]) ^ m * t := sub_eq_iff_eq_add'.mp ht
    have hc : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    have hlm : ((l : O) ^ m) • f u = 0 := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul O (l ^ m) (f u), htor u hu]
    rw [hc, hz, map_add, map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_comm, mul_smul, hlm,
      smul_zero, add_zero, Nat.cast_smul_eq_nsmul O k (f u)]
  rw [sub_smul, hγ, hχ, sub_self]
