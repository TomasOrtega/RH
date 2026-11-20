import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperTheory.V.Af.Rs in
/- English proof (translation)
Introduce and unpack `⟨n, a, ha⟩ ⟨m, b, hb⟩ h`. Simplify using `only at h`. Establish `h0` using `congrFun h 0`. Establish `h1` using `congrFun h 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h0 h1`.

Establish `ga : (a 0).gcd (a 1) = 1` using `Int.isCoprime_iff_gcd_eq_one.mp ha`. Establish `gb : (b 0).gcd (b 1) = 1` using `Int.isCoprime_iff_gcd_eq_one.mp hb`. Establish `hk : (((n + 1 : ℕ) : ℤ) * a 0).gcd (((n + 1 : ℕ) : ℤ) * a 1) = (((m + 1 : ℕ) : ℤ) * b 0).gcd (((m + 1 : ℕ) : ℤ) * b 1)`. Rewrite using `[h0, h1]`. Rewrite `hk` using `[Int.gcd_mul_left, Int.gcd_mul_left, ga, gb]`.

Simplify using `only [Int.natAbs_natCast, mul_one] at hk`. Establish `hnm : n = m` using `by omega`. Substitute `hnm` using the available equality. Establish `hpos : ((n + 1 : ℕ) : ℤ) ≠ 0` using `by positivity`. Establish `e0 : a 0 = b 0` using `mul_left_cancel₀ hpos h0`.

Establish `e1 : a 1 = b 1` using `mul_left_cancel₀ hpos h1`. Establish `hab : a = b`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `e0`.

Conclude with `e1`. Substitute `hab` using the available equality. Both sides reduce to the same expression.
-/
private lemma gcdSum_inj :
    Function.Injective (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
  simp only at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have ga : (a 0).gcd (a 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp ha
  have gb : (b 0).gcd (b 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb
  have hk : (((n + 1 : ℕ) : ℤ) * a 0).gcd (((n + 1 : ℕ) : ℤ) * a 1)
      = (((m + 1 : ℕ) : ℤ) * b 0).gcd (((m + 1 : ℕ) : ℤ) * b 1) := by
    rw [h0, h1]
  rw [Int.gcd_mul_left, Int.gcd_mul_left, ga, gb] at hk
  simp only [Int.natAbs_natCast, mul_one] at hk
  have hnm : n = m := by omega
  subst hnm
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have e0 : a 0 = b 0 := mul_left_cancel₀ hpos h0
  have e1 : a 1 = b 1 := mul_left_cancel₀ hpos h1
  have hab : a = b := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
  subst hab
  rfl

open UpperTheory.V.Af.Rs in
/- English proof (translation)
Use `set g := (v 0).gcd (v 1) with hg`. Establish `hpos : 0 < g`. Break down `Nat.eq_zero_or_pos g with h0 | h` into its components or cases. It suffices to derive a contradiction. Take `⟨a0, a1⟩` from `Int.gcd_eq_zero_iff.mp h0`.

Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `a0`. Conclude with `a1`.

Conclude with `h`. Establish `hc : IsCoprime ((fun i => v i / (g : ℤ)) 0) ((fun i => v i / (g : ℤ)) 1)` using `Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)`. Use `⟨(g - 1, ⟨fun i => v i / (g : ℤ), hc⟩), ?_⟩` and prove the remaining obligations. Establish `hg1 : g - 1 + 1 = g` using `Nat.sub_add_cancel hpos`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, hg1]`. Use `fin_cases i`. Conclude with `Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))`. Conclude with `Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))`.
-/
private lemma gcdSum_surj (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    v ∈ Set.range (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  set g := (v 0).gcd (v 1) with hg
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h
    · exfalso
      obtain ⟨a0, a1⟩ := Int.gcd_eq_zero_iff.mp h0
      apply hv
      funext i
      fin_cases i
      · exact a0
      · exact a1
    · exact h
  have hc : IsCoprime ((fun i => v i / (g : ℤ)) 0) ((fun i => v i / (g : ℤ)) 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
  refine ⟨(g - 1, ⟨fun i => v i / (g : ℤ), hc⟩), ?_⟩
  have hg1 : g - 1 + 1 = g := Nat.sub_add_cancel hpos
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, hg1]
  fin_cases i
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))

/- English proof (translation)
Introduce `u c hu hc hu0 hc0 hmul`. Establish `hsupp : Function.support u ⊆ Set.range (fun p : ℕ × UpperTheory.V.Af.Rs.Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1)`. Introduce `v hv`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hv hu0`. Conclude with `gcdSum_surj v hv0`. Rewrite using `[← gcdSum_inj.tsum_eq hsupp]`. Establish `hterm : ∀ p : ℕ × UpperTheory.V.Af.Rs.Cop, u ((((p.1 + 1 : ℕ) : ℤ)) • p.2.1) = c (p.1 + 1) * u p.2.1` using `fun p => hmul (p.1 + 1) p.2`. Establish `hprod : Summable fun p : ℕ × UpperTheory.V.Af.Rs.Cop => c (p.1 + 1) * u p.2.1`.

Use `hu.comp_injective gcdSum_inj` as an intermediate fact. Use `this.congr fun p => ?_` and prove the remaining obligations. Conclude with `hterm p`. Simplify using `only [hterm]`. Rewrite using `[hc.tsum_eq_zero_add, hc0, zero_add]`.

Conclude with `((hc.comp_injective (add_left_injective 1)).tsum_mul_tsum (hu.comp_injective Subtype.val_injective) hprod).symm`.
-/
theorem UpperTheory.V.Af.Rs.gcdSum :
    UpperTheory.V.Af.Rs.GcdSum := by
  intro u c hu hc hu0 hc0 hmul
  have hsupp : Function.support u ⊆
      Set.range (fun p : ℕ × UpperTheory.V.Af.Rs.Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv hu0
    exact gcdSum_surj v hv0
  rw [← gcdSum_inj.tsum_eq hsupp]
  have hterm : ∀ p : ℕ × UpperTheory.V.Af.Rs.Cop,
      u ((((p.1 + 1 : ℕ) : ℤ)) • p.2.1) = c (p.1 + 1) * u p.2.1 := fun p => hmul (p.1 + 1) p.2
  have hprod : Summable fun p : ℕ × UpperTheory.V.Af.Rs.Cop => c (p.1 + 1) * u p.2.1 := by
    have := hu.comp_injective gcdSum_inj
    refine this.congr fun p => ?_
    exact hterm p
  simp only [hterm]
  rw [hc.tsum_eq_zero_add, hc0, zero_add]
  exact ((hc.comp_injective (add_left_injective 1)).tsum_mul_tsum
    (hu.comp_injective Subtype.val_injective) hprod).symm
