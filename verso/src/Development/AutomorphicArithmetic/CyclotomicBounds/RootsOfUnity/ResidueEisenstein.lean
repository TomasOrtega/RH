import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.TorsionReduceInjective

open NumberField IsDedekindDomain

namespace UpperTheory.Mu

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

/- English proof (translation)
Establish `hv' : v.asIdeal ≠ ⊤` using `v.isPrime.ne_top`. Establish `hpos` using `Units.torsionOrder_pos L`. Establish `hn : ((Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal`. Introduce `hn`. Establish `hcop : Nat.Coprime (Units.torsionOrder L) p`.

Rewrite using `[Nat.coprime_comm, hp.coprime_iff_not_dvd]`. Introduce `hd`. Use `Nat.le_of_dvd hpos hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hcop`.

Establish `h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((Units.torsionOrder L : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((p : ℕ) : 𝓞 L)`. Use `congrArg (Int.cast : ℤ → 𝓞 L) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this.symm`. Apply `hv'` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, h1]`. Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hn) (v.asIdeal.mul_mem_left _ hv)`. Establish `hN : Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal`. Establish `hd : Ideal.absNorm v.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 L)`. Establish `h1` using `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)`.

Rewrite `h1` using `[Ideal.absNorm_span_singleton, show ((p : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (p : ℤ) by simp, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast]`. Then use the resulting hypothesis. Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hp).1 hd`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hv' (Ideal.absNorm_eq_one_iff.1 (by simpa using hk))`.

Rewrite using `[hk]`. Conclude with `lt_of_lt_of_le hw (Nat.le_self_pow hk0 p)`. Take `⟨θ, hθ, hθε⟩` from `tame_ext L v hn hN (ε.comp (Units.torsion L).subtype)`. Use `⟨θ, hθ, fun ζ hζ => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hζm⟩` from `hζ`.

Establish `hmem : ζ ∈ Units.torsion L`. Rewrite using `[Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using `using hζm`. Conclude with `hθε ⟨ζ, hmem⟩`.
-/
theorem tame_ext_prime {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    (ε : (𝓞 L)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) = ε ζ := by
  have hv' : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hpos := Units.torsionOrder_pos L
  have hn : ((Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal := by
    intro hn
    have hcop : Nat.Coprime (Units.torsionOrder L) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd hpos hd
      omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((Units.torsionOrder L : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((p : ℕ) : 𝓞 L) := by
      have := congrArg (Int.cast : ℤ → 𝓞 L) hab
      push_cast at this
      exact this.symm
    apply hv'
    rw [Ideal.eq_top_iff_one, h1]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hn) (v.asIdeal.mul_mem_left _ hv)
  have hN : Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal := by
    have hd : Ideal.absNorm v.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 L) := by
      have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)
      rwa [Ideal.absNorm_span_singleton, show ((p : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (p : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hv' (Ideal.absNorm_eq_one_iff.1 (by simpa using hk))
    rw [hk]
    exact lt_of_lt_of_le hw (Nat.le_self_pow hk0 p)
  obtain ⟨θ, hθ, hθε⟩ := tame_ext L v hn hN (ε.comp (Units.torsion L).subtype)
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  obtain ⟨m, hm, hζm⟩ := hζ
  have hmem : ζ ∈ Units.torsion L := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨m, hm, ?_⟩
    apply Units.ext
    apply RingOfIntegers.ext
    simpa using hζm
  exact hθε ⟨ζ, hmem⟩

/- English proof (translation)
Set `f : I → (𝓞 L)ˣ →* ℂˣ` to `fun i => (zpowGroupHom (e i)).comp (Units.map ((φ i).toMonoidHom.comp (algebraMap (𝓞 L) L).toMonoidHom))`. Take `⟨θ, hθ, hθε⟩` from `tame_ext_prime v hp hw hv (∏ i, f i)⁻¹`. Use `⟨θ, hθ, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `hf : (((∏ i, f i ζ : ℂˣ)) : ℂ) = ∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i`. Rewrite using `[Units.coe_prod]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[f, Units.val_zpow_eq_zpow_val]`. Rewrite using `[hθε ζ hζ, MonoidHom.inv_apply, MonoidHom.finset_prod_apply, ← hf]`. Conclude with `Units.mul_inv _`.
-/
theorem tame_par {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      (∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i) * ((θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
  classical
  let f : I → (𝓞 L)ˣ →* ℂˣ := fun i =>
    (zpowGroupHom (e i)).comp (Units.map ((φ i).toMonoidHom.comp (algebraMap (𝓞 L) L).toMonoidHom))
  obtain ⟨θ, hθ, hθε⟩ := tame_ext_prime v hp hw hv (∏ i, f i)⁻¹
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  have hf : (((∏ i, f i ζ : ℂˣ)) : ℂ) = ∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [f, Units.val_zpow_eq_zpow_val]
  rw [hθε ζ hζ, MonoidHom.inv_apply, MonoidHom.finset_prod_apply, ← hf]
  exact Units.mul_inv _

/- English proof (translation)
Take `⟨m, hm, hzm⟩` from `hz`. Establish `hint : IsIntegral ℤ z`. Use `IsIntegral.of_pow hm ?_` and prove the remaining obligations. Rewrite using `[hzm]`. Conclude with `isIntegral_one`.

Set `y : 𝓞 L` to `⟨z, hint⟩`. Establish `hy : y ^ m = 1`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hzm`.

Conclude with `⟨(IsUnit.of_pow_eq_one hy hm.ne').unit, rfl⟩`.
-/
theorem exists_unit_of_root {z : L} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∃ ζ : (𝓞 L)ˣ, ((ζ : 𝓞 L) : L) = z := by
  obtain ⟨m, hm, hzm⟩ := hz
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow hm ?_
    rw [hzm]
    exact isIntegral_one
  let y : 𝓞 L := ⟨z, hint⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    push_cast
    exact hzm
  exact ⟨(IsUnit.of_pow_eq_one hy hm.ne').unit, rfl⟩

end UpperTheory.Mu
