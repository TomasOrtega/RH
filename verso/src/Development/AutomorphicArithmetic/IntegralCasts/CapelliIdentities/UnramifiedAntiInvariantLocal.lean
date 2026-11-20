import Mathlib

open NumberField

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hr hU ξ hξ hσ v`. Establish `hne : σ ξ ≠ ξ`. Introduce `h`. Rewrite `h` using `[hσ]`. Conclude with `hξ (by linear_combination (-1 / 2 : E) * h)`.

Establish `hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y`. Introduce `y hy`. Use `Subalgebra.isSimpleOrder_of_finrank hr` as an intermediate fact. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h` into its components or cases. Establish `: y ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `hy`.

Rewrite `this` using `[h]`. Conclude with `Algebra.mem_bot.mp this`. Establish `: ξ ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `by rw [h]; trivial`. Conclude with `absurd this hne`. Establish `hinv : ∀ y : E, σ (σ y) = y`.

Introduce `y`. Use `Subalgebra.isSimpleOrder_of_finrank hr` as an intermediate fact. Break down `eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h` into its components or cases. Establish `: ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)` using `by show σ (σ ξ) = ξ`. Rewrite using `[hσ, map_neg, hσ, neg_neg]`.

Rewrite `this` using `[h]`. Take `⟨c, hc⟩` from `Algebra.mem_bot.mp this`. Conclude with `absurd (by rw [← hc, AlgHom.commutes]) hne`. Establish `: y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)` using `by rw [h]; trivial`. Conclude with `this`.

Set `τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E` to `RingOfIntegers.mapAlgHom σ`. Establish `hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x` using `fun _ => rfl`. Use `v.isMaximal` as an intermediate fact. Take `⟨w, hw, hwv⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hx : ∃ x : 𝓞 E, x - τ x ∉ w`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `heq : AlgHom.id (𝓞 F) (𝓞 E) = τ` using `Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top) (fun x => Ideal.Quotient.eq.mpr (hcon x))`. Establish `hall : ∀ x : 𝓞 E, σ x = x` using `fun x => by rw [← hτ, ← heq]; rfl`. Take `⟨p, q, -, hpq⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) ξ`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hpq, map_div₀]`. Conclude with `congrArg₂ (· / ·) (hall p) (hall q)`. Take `⟨x, hx⟩` from `hx`. Use `set a : 𝓞 E := x - τ x with ha`.

Establish `hσa : σ (a : E) = -(a : E)`. Establish `: (a : E) = x - σ x` using `by rw [← hτ]; rfl`. Rewrite using `[this, map_sub, hinv, neg_sub]`. Take `⟨c, hc⟩` from `hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])`. Establish `hci : IsIntegral ℤ c`.

Rewrite using `[← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hc]`. Conclude with `a.isIntegral_coe.mul a.isIntegral_coe`. Use `⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩` and prove the remaining obligations. Introduce `hn`. Establish `h1` using `(Ideal.mem_of_liesOver w v.asIdeal _).mp hn`.

Establish `h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hc`. Rewrite `h1` using `[h2]`. Conclude with `hx ((hw.isPrime.mem_or_mem h1).elim id id)`.
-/
theorem UpperTheory.unramified_anti_invariant_local :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      Module.finrank F E = 2 →
      Algebra.Unramified (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) →
      ∀ (ξ : E), ξ ≠ 0 → σ ξ = -ξ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∃ (a b : NumberField.RingOfIntegers E) (n : NumberField.RingOfIntegers F),
          n ∉ v.asIdeal ∧ σ (a : E) = -(a : E) ∧ (a : E) * (b : E) = algebraMap F E (n : F) := by
  intro F E _ _ _ _ _ σ hr hU ξ hξ hσ v
  have hne : σ ξ ≠ ξ := by
    intro h
    rw [hσ] at h
    exact hξ (by linear_combination (-1 / 2 : E) * h)
  have hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y := by
    intro y hy
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := hy
      rw [h] at this
      exact Algebra.mem_bot.mp this
    · have : ξ ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      exact absurd this hne
  have hinv : ∀ y : E, σ (σ y) = y := by
    intro y
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h
    · have : ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by
        show σ (σ ξ) = ξ
        rw [hσ, map_neg, hσ, neg_neg]
      rw [h] at this
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp this
      exact absurd (by rw [← hc, AlgHom.commutes]) hne
    · have : y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by rw [h]; trivial
      exact this
  let τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom σ
  have hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x := fun _ => rfl
  have := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hx : ∃ x : 𝓞 E, x - τ x ∉ w := by
    by_contra hcon
    push Not at hcon
    have heq : AlgHom.id (𝓞 F) (𝓞 E) = τ :=
      Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top)
        (fun x => Ideal.Quotient.eq.mpr (hcon x))
    have hall : ∀ x : 𝓞 E, σ x = x := fun x => by rw [← hτ, ← heq]; rfl
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
    apply hne
    rw [← hpq, map_div₀]
    exact congrArg₂ (· / ·) (hall p) (hall q)
  obtain ⟨x, hx⟩ := hx
  set a : 𝓞 E := x - τ x with ha
  have hσa : σ (a : E) = -(a : E) := by
    have : (a : E) = x - σ x := by rw [← hτ]; rfl
    rw [this, map_sub, hinv, neg_sub]
  obtain ⟨c, hc⟩ := hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])
  have hci : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hc]
    exact a.isIntegral_coe.mul a.isIntegral_coe
  refine ⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩
  intro hn
  have h1 := (Ideal.mem_of_liesOver w v.asIdeal _).mp hn
  have h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a := by
    apply RingOfIntegers.ext
    exact hc
  rw [h2] at h1
  exact hx ((hw.isPrime.mem_or_mem h1).elim id id)
