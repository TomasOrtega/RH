import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

noncomputable section

namespace Formalism.MainNotions.Gaps.LevGap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped Pointwise

/- English proof (translation)
Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 h`. Distinguish the cases in `hN : N = 0`. Substitute `hN` using the available equality. Simplify using `only [Int.cast_zero, mul_zero] at hz`. Establish `: a = 0` using `by exact_mod_cast hz.symm`.

Simplify using `[this]`. Establish `hNE : (N : E) ≠ 0` using `by exact_mod_cast hN`. Establish `hzE' : (z : E) * (N : E) = (a : E)`. Use `congrArg (fun t : 𝓞 E => (t : E)) hz` as an intermediate fact. Simplify using `using this`.

Establish `hzE : (z : E) = algebraMap ℚ E ((a : ℚ) / N)`. Rewrite using `[map_div₀, eq_div_iff (by simpa using hNE)]`. Simplify using `using hzE'`. Establish `hint : IsIntegral ℤ ((a : ℚ) / N)`. Establish `: IsIntegral ℤ (z : E)` using `RingOfIntegers.isIntegral_coe z`.

Rewrite `this` using `[hzE]`. Conclude with `(isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 this`. Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hNQ : (N : ℚ) ≠ 0` using `by exact_mod_cast hN`.

Establish `: (a : ℚ) = N * m`. Establish `h2 : (m : ℚ) = (a : ℚ) / N` using `by simpa using hm`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem int_dvd_of_mem_span {E : Type*} [Field E] [NumberField E] (N a : ℤ)
    (h : (a : 𝓞 E) ∈ Ideal.span {(N : 𝓞 E)}) : N ∣ a := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  by_cases hN : N = 0
  · subst hN
    simp only [Int.cast_zero, mul_zero] at hz
    have : a = 0 := by exact_mod_cast hz.symm
    simp [this]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hzE' : (z : E) * (N : E) = (a : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) hz
    simpa using this
  have hzE : (z : E) = algebraMap ℚ E ((a : ℚ) / N) := by
    rw [map_div₀, eq_div_iff (by simpa using hNE)]
    simpa using hzE'
  have hint : IsIntegral ℤ ((a : ℚ) / N) := by
    have : IsIntegral ℤ (z : E) := RingOfIntegers.isIntegral_coe z
    rw [hzE] at this
    exact (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨m, ?_⟩
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have : (a : ℚ) = N * m := by
    have h2 : (m : ℚ) = (a : ℚ) / N := by simpa using hm
    rw [h2]; field_simp
  exact_mod_cast this

/- English proof (translation)
Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hcong`. Use `set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'`. Establish `hT : (T : 𝓞 E) = pz * c' pz`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: ((c' pz : 𝓞 E) : E) = c (pz : E)` using `rfl`.

Use `show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)`. Rewrite using `[this, hpz]`. Simplify using the standard rewrite rules. Establish `hp : pz = 1 + y * M` using `by rw [hy]; ring`. Establish `hcp : c' pz = 1 + c' y * M` using `by rw [hp]; simp`.

Apply `int_dvd_of_mem_span (E := E)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨y + c' y + y * c' y * M, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hT, hcp]`.

Take the linear combination `(-(1 + c' y * M)) * hp`.
-/
theorem norm_congr_one {E : Type*} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (T M : ℕ) (pz : 𝓞 E)
    (hpz : (pz : E) * c (pz : E) = (T : E)) (hcong : (pz - 1) ∈ Ideal.span {(M : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hcong
  set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'
  have hT : (T : 𝓞 E) = pz * c' pz := by
    apply RingOfIntegers.ext
    have : ((c' pz : 𝓞 E) : E) = c (pz : E) := rfl
    show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)
    rw [this, hpz]; simp
  have hp : pz = 1 + y * M := by rw [hy]; ring
  have hcp : c' pz = 1 + c' y * M := by rw [hp]; simp
  apply int_dvd_of_mem_span (E := E)
  rw [Ideal.mem_span_singleton']
  refine ⟨y + c' y + y * c' y * M, ?_⟩
  push_cast
  rw [hT, hcp]
  linear_combination (-(1 + c' y * M)) * hp

/- English proof (translation)
Take `⟨m, hm⟩` from `hT`. Establish `h4' : (T : ℤ) = 1 + 4 * (q * m)` using `by linarith`. Establish `h4 : T % 4 = 1`. Generalize the expression as in `(q : ℤ) * m = k at h4'`. Use linear arithmetic over natural numbers and integers.

Establish `hTq : (T : ℤ) % q = 1 % q`. Establish `: (T : ℤ) = 1 + q * (4 * m)` using `by linarith`. Rewrite using `[this, Int.add_mul_emod_self_left]`. Establish `hodd : Odd T` using `Nat.odd_iff.2 (by omega)`. Rewrite using `[show (-(q : ℤ)) = (-1) * q by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hq h4, jacobiSym.mod_left, hTq, ← jacobiSym.mod_left, jacobiSym.one_left]`.
-/
theorem jacobi_neg_eq_one (q T : ℕ) (hq : Odd q) (hT : (4 * q : ℤ) ∣ (T : ℤ) - 1) :
    jacobiSym (-(q : ℤ)) T = 1 := by
  obtain ⟨m, hm⟩ := hT
  have h4' : (T : ℤ) = 1 + 4 * (q * m) := by linarith
  have h4 : T % 4 = 1 := by
    generalize (q : ℤ) * m = k at h4'
    omega
  have hTq : (T : ℤ) % q = 1 % q := by
    have : (T : ℤ) = 1 + q * (4 * m) := by linarith
    rw [this, Int.add_mul_emod_self_left]
  have hodd : Odd T := Nat.odd_iff.2 (by omega)
  rw [show (-(q : ℤ)) = (-1) * q by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
    ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hq h4,
    jacobiSym.mod_left, hTq, ← jacobiSym.mod_left, jacobiSym.one_left]

section Gen

variable {E : Type} [Field E] [NumberField E]

def pullPl (σ : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := σ⁻¹ • w.asIdeal
  isPrime := (Ideal.IsPrime.smul_iff _).2 w.isPrime
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 E) => σ • I) h
    simpa using this

/- English proof (translation)
The claim follows from `Ideal.mem_inv_pointwise_smul_iff`.
-/
theorem mem_pullPl (σ : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ∈ (pullPl σ w).asIdeal ↔ σ • x ∈ w.asIdeal :=
  Ideal.mem_inv_pointwise_smul_iff

/- English proof (translation)
Rewrite using `[mem_pullPl]`. Establish `: σ • (p : 𝓞 E) = (p : 𝓞 E)` using `map_natCast (MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) (𝓞 E) σ) p`. Rewrite using `[this]`.
-/
theorem natCast_mem_pullPl (σ : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) :
    (p : 𝓞 E) ∈ (pullPl σ w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  rw [mem_pullPl]
  have : σ • (p : 𝓞 E) = (p : 𝓞 E) := map_natCast (MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) (𝓞 E) σ) p
  rw [this]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[mem_pullPl, mem_pullPl, mem_pullPl, mul_smul]`.
-/
theorem pullPl_mul (σ τ : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) :
    pullPl (σ * τ) w = pullPl τ (pullPl σ w) := by
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_pullPl, mem_pullPl, mem_pullPl, mul_smul]

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hpI : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ`. Establish `hpM : (Ideal.span {(p : ℤ)}).IsMaximal` using `hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 K) p ∈ v.asIdeal`. Simplify using `using hv`. Use `v.isPrime` as an intermediate fact. Conclude with `hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle`.
-/
theorem liesOver_of_natCast_mem {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  refine ⟨?_⟩
  have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) p ∈ v.asIdeal
    simpa using hv
  have := v.isPrime
  exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle

/- English proof (translation)
Establish `: IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ E`. Establish `h1` using `liesOver_of_natCast_mem p hp w hw`. Establish `h2` using `liesOver_of_natCast_mem p hp w' hw'`. Use `w.isPrime` as an intermediate fact. Use `w'.isPrime` as an intermediate fact.

Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) w.asIdeal w'.asIdeal Gal(E/ℚ)`. Use `⟨σ⁻¹, HeightOneSpectrum.ext ?_⟩` and prove the remaining obligations. Use `show (σ⁻¹)⁻¹ • w.asIdeal = w'.asIdeal`. Rewrite using `[inv_inv, hσ]`.
-/
theorem exists_pullPl_eq [IsGalois ℚ E] (p : ℕ) (hp : p.Prime) (w w' : HeightOneSpectrum (𝓞 E))
    (hw : (p : 𝓞 E) ∈ w.asIdeal) (hw' : (p : 𝓞 E) ∈ w'.asIdeal) :
    ∃ σ : E ≃ₐ[ℚ] E, pullPl σ w = w' := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have h1 := liesOver_of_natCast_mem p hp w hw
  have h2 := liesOver_of_natCast_mem p hp w' hw'
  have := w.isPrime
  have := w'.isPrime
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) w.asIdeal w'.asIdeal
    Gal(E/ℚ)
  refine ⟨σ⁻¹, HeightOneSpectrum.ext ?_⟩
  show (σ⁻¹)⁻¹ • w.asIdeal = w'.asIdeal
  rw [inv_inv, hσ]

/- English proof (translation)
Set `f : (E ≃ₐ[ℚ] E) → {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}` to `fun σ => ⟨pullPl σ w, (natCast_mem_pullPl σ w p).2 hw⟩`. Establish `hsurj : Function.Surjective f`. Introduce and unpack `⟨w', hw'⟩`. Take `⟨σ, hσ⟩` from `exists_pullPl_eq p hp w w' hw hw'`. Conclude with `⟨σ, Subtype.ext hσ⟩`.

Establish `hcard : Nat.card (E ≃ₐ[ℚ] E) ≤ Nat.card {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}`. Rewrite using `[Nat.card_coe_set_eq, hs, IsGalois.card_aut_eq_finrank]`. Establish `hb` using `hsurj.bijective_of_nat_card_le hcard`. Introduce `σ τ h`. Conclude with `hb.1 (Subtype.ext h)`.
-/
theorem pullPl_injective [IsGalois ℚ E] (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) :
    Function.Injective (fun σ : E ≃ₐ[ℚ] E => pullPl σ w) := by
  let f : (E ≃ₐ[ℚ] E) → {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal} :=
    fun σ => ⟨pullPl σ w, (natCast_mem_pullPl σ w p).2 hw⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨w', hw'⟩
    obtain ⟨σ, hσ⟩ := exists_pullPl_eq p hp w w' hw hw'
    exact ⟨σ, Subtype.ext hσ⟩
  have hcard : Nat.card (E ≃ₐ[ℚ] E) ≤
      Nat.card {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal} := by
    rw [Nat.card_coe_set_eq, hs, IsGalois.card_aut_eq_finrank]
  have hb := hsurj.bijective_of_nat_card_le hcard
  intro σ τ h
  exact hb.1 (Subtype.ext h)

end Gen

section Fix

variable {E : Type} [Field E] [NumberField E] (F : Subfield E) [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap_int (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (x : F) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_smul_int (σ : E ≃ₐ[ℚ] E) (x : 𝓞 E) : ((σ • x : 𝓞 E) : E) = σ (x : E) := rfl

/- English proof (translation)
Establish `hint : IsIntegral ℤ (⟨(y : E), hy⟩ : F)`. Establish `h : IsIntegral ℤ (y : E)` using `RingOfIntegers.isIntegral_coe y`. Conclude with `(isIntegral_algebraMap_iff (algebraMap F E).injective).1 h`. Conclude with `⟨⟨⟨(y : E), hy⟩, hint⟩, RingOfIntegers.ext rfl⟩`.
-/
theorem exists_int_of_mem (y : 𝓞 E) (hy : (y : E) ∈ F) : ∃ y' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) y' = y := by
  have hint : IsIntegral ℤ (⟨(y : E), hy⟩ : F) := by
    have h : IsIntegral ℤ (y : E) := RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h
  exact ⟨⟨⟨(y : E), hy⟩, hint⟩, RingOfIntegers.ext rfl⟩

def underPl (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨p, hp, hpw⟩ := PlacesToy.exists_prime_mem w
    intro h
    have h1 : (p : 𝓞 F) ∈ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact hpw
    rw [h, Ideal.mem_bot] at h1
    exact hp.ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_underPl (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 F) :
    x ∈ (underPl F w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_underPl, map_natCast]`.
-/
theorem natCast_mem_underPl (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) :
    (p : 𝓞 F) ∈ (underPl F w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  rw [mem_underPl, map_natCast]

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Take `⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E))` from `inferInstance`. Establish `hP0 : P ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hPl.over]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))`. Conclude with `⟨⟨P, hPp, hP0⟩, HeightOneSpectrum.ext hPl.over.symm⟩`.
-/
theorem exists_underPl_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), underPl F w = v := by
  have := v.isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hPl.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  exact ⟨⟨P, hPp, hP0⟩, HeightOneSpectrum.ext hPl.over.symm⟩

variable {F} (c : E ≃ₐ[ℚ] E) (hF : ∀ x : E, x ∈ F ↔ c x = x) (hc : ∀ x : E, c (c x) = x)

include hF in
/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[mem_underPl, mem_underPl, mem_pullPl]`. Establish `: c • algebraMap (𝓞 F) (𝓞 E) x = algebraMap (𝓞 F) (𝓞 E) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[coe_smul_int, coe_algebraMap_int]`. Conclude with `(hF _).1 (x : F).2`. Rewrite using `[this]`.
-/
theorem underPl_pullPl_conj (w : HeightOneSpectrum (𝓞 E)) : underPl F (pullPl c w) = underPl F w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_underPl, mem_underPl, mem_pullPl]
  have : c • algebraMap (𝓞 F) (𝓞 E) x = algebraMap (𝓞 F) (𝓞 E) x := by
    apply RingOfIntegers.ext
    rw [coe_smul_int, coe_algebraMap_int]
    exact (hF _).1 (x : F).2
  rw [this]

include hF hc in

/- English proof (translation)
Establish `hsub : (w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ ((pullPl c w).asIdeal : Set (𝓞 E))`. Introduce `x hx`. Establish `hy : ((x * c • x : 𝓞 E) : E) ∈ F`. Rewrite using `[hF]`. Use `show c ((x : E) * c (x : E)) = (x : E) * c (x : E)`.

Rewrite using `[map_mul, hc, mul_comm]`. Take `⟨y', hy'⟩` from `exists_int_of_mem F _ hy`. Establish `h1 : y' ∈ (underPl F w').asIdeal`. Rewrite using `[mem_underPl, hy']`. Conclude with `w'.asIdeal.mul_mem_right _ hx`.

Rewrite `h1` using `[← h, mem_underPl, hy']`. Break down `w.isPrime.mem_or_mem h1 with h2 | h2` into its components or cases. Conclude with `Or.inl h2`. Conclude with `Or.inr ((mem_pullPl c w x).2 h2)`. Establish `hmax : w'.asIdeal.IsMaximal` using `w'.isMaximal`.

Break down `Ideal.subset_union.1 hsub with h1 | h1` into its components or cases. Conclude with `Or.inl (HeightOneSpectrum.ext (hmax.eq_of_le w.isPrime.ne_top h1))`. Conclude with `Or.inr (HeightOneSpectrum.ext (hmax.eq_of_le (pullPl c w).isPrime.ne_top h1))`.
-/
theorem eq_or_eq_conj_of_underPl_eq (w w' : HeightOneSpectrum (𝓞 E)) (h : underPl F w = underPl F w') :
    w' = w ∨ w' = pullPl c w := by
  have hsub : (w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ ((pullPl c w).asIdeal : Set (𝓞 E)) := by
    intro x hx
    have hy : ((x * c • x : 𝓞 E) : E) ∈ F := by
      rw [hF]
      show c ((x : E) * c (x : E)) = (x : E) * c (x : E)
      rw [map_mul, hc, mul_comm]
    obtain ⟨y', hy'⟩ := exists_int_of_mem F _ hy
    have h1 : y' ∈ (underPl F w').asIdeal := by
      rw [mem_underPl, hy']; exact w'.asIdeal.mul_mem_right _ hx
    rw [← h, mem_underPl, hy'] at h1
    rcases w.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ((mem_pullPl c w x).2 h2)
  have hmax : w'.asIdeal.IsMaximal := w'.isMaximal
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (hmax.eq_of_le w.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (hmax.eq_of_le (pullPl c w).isPrime.ne_top h1))

include hF hc in

/- English proof (translation)
Establish `hfree` using `pullPl_injective p hp hs w hw`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Establish `hij' : underPl F (pullPl (s i) w) = underPl F (pullPl (s j) w)` using `congrArg Subtype.val hij`. Break down `eq_or_eq_conj_of_underPl_eq c hF hc _ _ hij' with h | h` into its components or cases.

Conclude with `(hinj (hfree h)).symm`. Rewrite `h` using `[← pullPl_mul]`. Conclude with `absurd (hfree h) (h1 i j)`. Introduce and unpack `⟨v, hv⟩`. Take `⟨w', rfl⟩` from `exists_underPl_eq F v`.

Establish `hw' : (p : 𝓞 E) ∈ w'.asIdeal` using `(natCast_mem_underPl F w' p).1 hv`. Take `⟨ρ, rfl⟩` from `exists_pullPl_eq p hp w w' hw hw'`. Break down `h2 ρ with ⟨i, hi⟩ | ⟨i, hi⟩` into its components or cases. Conclude with `⟨i, Subtype.ext (by show underPl F (pullPl (s i) w) = _; rw [hi])⟩`. Use `⟨i, Subtype.ext ?_⟩ show underPl F (pullPl (s i) w) = _` and prove the remaining obligations.

Rewrite using `[hi, pullPl_mul, underPl_pullPl_conj c hF]`.
-/
theorem bijective_underPl_pullPl [IsGalois ℚ E] (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {ι : Type} (s : ι → (E ≃ₐ[ℚ] E)) (hinj : Function.Injective s) (h1 : ∀ i j, s j ≠ s i * c)
    (h2 : ∀ ρ, (∃ i, s i = ρ) ∨ ∃ i, s i = ρ * c)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) :
    Function.Bijective (fun i : ι => (⟨underPl F (pullPl (s i) w),
      (natCast_mem_underPl F _ p).2 ((natCast_mem_pullPl _ w p).2 hw)⟩ :
        {v : HeightOneSpectrum (𝓞 F) // (p : 𝓞 F) ∈ v.asIdeal})) := by
  have hfree := pullPl_injective p hp hs w hw
  constructor
  · intro i j hij
    have hij' : underPl F (pullPl (s i) w) = underPl F (pullPl (s j) w) := congrArg Subtype.val hij
    rcases eq_or_eq_conj_of_underPl_eq c hF hc _ _ hij' with h | h
    · exact (hinj (hfree h)).symm
    · rw [← pullPl_mul] at h
      exact absurd (hfree h) (h1 i j)
  · rintro ⟨v, hv⟩
    obtain ⟨w', rfl⟩ := exists_underPl_eq F v
    have hw' : (p : 𝓞 E) ∈ w'.asIdeal := (natCast_mem_underPl F w' p).1 hv
    obtain ⟨ρ, rfl⟩ := exists_pullPl_eq p hp w w' hw hw'
    rcases h2 ρ with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, Subtype.ext (by show underPl F (pullPl (s i) w) = _; rw [hi])⟩
    · refine ⟨i, Subtype.ext ?_⟩
      show underPl F (pullPl (s i) w) = _
      rw [hi, pullPl_mul, underPl_pullPl_conj c hF]

/- English proof (translation)
Rewrite using `[mem_underPl, mem_pullPl, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]`. Both sides reduce to the same expression.
-/
theorem mem_underPl_pullPl_iff (σ : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 F) :
    x ∈ (underPl F (pullPl σ w)).asIdeal ↔ w.valuation E (σ (algebraMap F E (x : F))) < 1 := by
  rw [mem_underPl, mem_pullPl, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  rfl

end Fix

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h1 : (T : ℤ) ∣ (T : ℤ) - 1` using `(Int.natCast_dvd_natCast.2 hm).trans h`. Establish `h2 : (T : ℤ) ∣ 1`. Use `dvd_sub (dvd_refl (T : ℤ)) h1` as an intermediate fact. Simplify using `using this`.

Conclude with `hm1 (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)`.
-/
theorem ne_of_dvd_of_congr {M T m : ℕ} (h : (M : ℤ) ∣ (T : ℤ) - 1) (hm : m ∣ M) (hm1 : m ≠ 1) : T ≠ m := by
  rintro rfl
  have h1 : (T : ℤ) ∣ (T : ℤ) - 1 := (Int.natCast_dvd_natCast.2 hm).trans h
  have h2 : (T : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (T : ℤ)) h1
    simpa using this
  exact hm1 (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)

section HostInst

variable {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E)
  (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})

include hpz hcong

/- English proof (translation)
The claim follows from `norm_congr_one H.conj T _ pz hpz hcong`.
-/
theorem T_congr : ((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ) ∣ (T : ℤ) - 1 :=
  norm_congr_one H.conj T _ pz hpz hcong

/- English proof (translation)
Use `ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ?_ (H.g_prime i).one_lt.ne'` and prove the remaining obligations. Use `fin_cases i`. Conclude with `⟨H.QS * H.q * H.d * (H.g 0 * H.g 1 ^ 2), by simp only [Fin.zero_eta]; ring⟩`. Conclude with `⟨H.QS * H.q * H.d * (H.g 0 ^ 2 * H.g 1), by simp only [Fin.mk_one]; ring⟩`.
-/
theorem T_ne_g (i : Fin 2) : T ≠ H.g i := by
  refine ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ?_ (H.g_prime i).one_lt.ne'
  fin_cases i
  · exact ⟨H.QS * H.q * H.d * (H.g 0 * H.g 1 ^ 2), by simp only [Fin.zero_eta]; ring⟩
  · exact ⟨H.QS * H.q * H.d * (H.g 0 ^ 2 * H.g 1), by simp only [Fin.mk_one]; ring⟩

/- English proof (translation)
The claim follows from `ne_of_dvd_of_congr (T_congr H T pz hpz hcong) (((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans H.tower_dvd).mul_right _).mul_right _).mul_right _) (by norm_num)`.
-/
theorem T_ne_two : T ≠ 2 :=
  ne_of_dvd_of_congr (T_congr H T pz hpz hcong)
    (((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans H.tower_dvd).mul_right _).mul_right _).mul_right _) (by norm_num)

/- English proof (translation)
The claim follows from `ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ⟨H.QS * H.d * (H.g 0 * H.g 1) ^ 2, by ring⟩ H.hypOdd.1.one_lt.ne'`.
-/
theorem T_ne_q : T ≠ H.q :=
  ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ⟨H.QS * H.d * (H.g 0 * H.g 1) ^ 2, by ring⟩
    H.hypOdd.1.one_lt.ne'

/- English proof (translation)
The claim follows from `ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ⟨H.QS * H.q * (H.g 0 * H.g 1) ^ 2, by ring⟩ H.hypOdd.2.1.one_lt.ne'`.
-/
theorem T_ne_d : T ≠ H.d :=
  ne_of_dvd_of_congr (T_congr H T pz hpz hcong) ⟨H.QS * H.q * (H.g 0 * H.g 1) ^ 2, by ring⟩
    H.hypOdd.2.1.one_lt.ne'

/- English proof (translation)
Use `jacobi_neg_eq_one H.q T (H.hypOdd.1.odd_of_ne_two H.hypOdd.2.2.2.1) (Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong))` and prove the remaining obligations. Take `⟨c, hc⟩` from `H.tower_dvd`. Conclude with `⟨((2 ^ R.e * c * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩`.
-/
theorem T_jacobi_q : jacobiSym (-(H.q : ℤ)) T = 1 := by
  refine jacobi_neg_eq_one H.q T (H.hypOdd.1.odd_of_ne_two H.hypOdd.2.2.2.1) (Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong))
  obtain ⟨c, hc⟩ := H.tower_dvd
  exact ⟨((2 ^ R.e * c * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩

/- English proof (translation)
Use `jacobi_neg_eq_one H.d T (H.hypOdd.2.1.odd_of_ne_two H.hypOdd.2.2.2.2) (Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong))` and prove the remaining obligations. Take `⟨c, hc⟩` from `H.tower_dvd`. Conclude with `⟨((2 ^ R.e * c * H.q * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩`.
-/
theorem T_jacobi_d : jacobiSym (-(H.d : ℤ)) T = 1 := by
  refine jacobi_neg_eq_one H.d T (H.hypOdd.2.1.odd_of_ne_two H.hypOdd.2.2.2.2) (Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong))
  obtain ⟨c, hc⟩ := H.tower_dvd
  exact ⟨((2 ^ R.e * c * H.q * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩

/- English proof (translation)
Establish `h : ((2 ^ (R.e + 2) : ℕ) : ℤ) ∣ (T : ℤ) - 1`. Use `Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong)` and prove the remaining obligations. Take `⟨c, hc⟩` from `H.tower_dvd`. Conclude with `⟨((c * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩`. Use `(ZMod.intCast_eq_intCast_iff_dvd_sub 1 (T : ℤ) (2 ^ (R.e + 2))).2 h` as an intermediate fact.

Simplify using `using this.symm`.
-/
theorem T_mod_pow : (T : ZMod (2 ^ (R.e + 2))) = 1 := by
  have h : ((2 ^ (R.e + 2) : ℕ) : ℤ) ∣ (T : ℤ) - 1 := by
    refine Dvd.dvd.trans ?_ (T_congr H T pz hpz hcong)
    obtain ⟨c, hc⟩ := H.tower_dvd
    exact ⟨((c * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ), by rw [hc]; push_cast; ring⟩
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (T : ℤ) (2 ^ (R.e + 2))).2 h
  simpa using this.symm

/- English proof (translation)
Establish `: Fact T.Prime` using `⟨hT⟩`. Establish `hm : T ≡ 1 [MOD H.condN]`. Use `Nat.ModEq.symm (Nat.modEq_iff_dvd.2 ?_)` and prove the remaining obligations. Conclude with `(Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans (T_congr H T pz hpz hcong)`. Establish `h1 : H.condN ≠ 1`.

Introduce `h`. Establish `hq : H.q ∣ H.condN` using `⟨H.QS * H.d, by show H.QS * H.q * H.d = _; ring⟩`. Rewrite `hq` using `[h]`. Conclude with `H.hypOdd.1.one_lt.ne' (Nat.dvd_one.1 hq)`. Use `placesOver_ncard_of_split H T ?_` and prove the remaining obligations.

Rewrite using `[hm, Nat.one_mod_eq_one.2 h1]`.
-/
theorem T_split_E (hT : T.Prime) :
    {v : HeightOneSpectrum (𝓞 H.E) | (T : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E := by
  have : Fact T.Prime := ⟨hT⟩
  have hm : T ≡ 1 [MOD H.condN] := by
    refine Nat.ModEq.symm (Nat.modEq_iff_dvd.2 ?_)
    exact (Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans (T_congr H T pz hpz hcong)
  have h1 : H.condN ≠ 1 := by
    intro h
    have hq : H.q ∣ H.condN := ⟨H.QS * H.d, by show H.QS * H.q * H.d = _; ring⟩
    rw [h] at hq
    exact H.hypOdd.1.one_lt.ne' (Nat.dvd_one.1 hq)
  refine placesOver_ncard_of_split H T ?_
  rw [hm, Nat.one_mod_eq_one.2 h1]

end HostInst

section HostGal

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_eq_sigmaOf : H.conj = H.sigmaOf (R.cc) := rfl

/- English proof (translation)
The claim follows from `map_mul (H.gal).symm g h`.
-/
theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h :=
  map_mul (H.gal).symm g h

/- English proof (translation)
The claim follows from `(H.gal).symm.injective`.
-/
theorem sigmaOf_injective : Function.Injective H.sigmaOf := (H.gal).symm.injective

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[H.conjE_apply, H.conjE_apply]`. Simplify using the standard rewrite rules.
-/
theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [H.conjE_apply, H.conjE_apply]
  simp

/- English proof (translation)
The claim follows from `H.conjE_mem_hostF_iff x`.
-/
theorem mem_F_iff (x : H.E) : x ∈ H.F ↔ H.conj x = x := H.conjE_mem_hostF_iff x

/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Use `bijective_underPl_pullPl H.conj (mem_F_iff H) (conj_conj H) p hp hs (fun τ : ↥(R.Psi) => H.sigmaOf (τ : R.GG)) ((sigmaOf_injective H).comp Subtype.val_injective) ?_ ?_ w hw` and prove the remaining obligations. Introduce `i j h`. Rewrite `h` using `[conj_eq_sigmaOf, ← sigmaOf_mul]`. Establish `h1` using `sigmaOf_injective H h`.

Establish `hi : (i : R.GG).1.2 = 1` using `(Formalism.HC.Frame.mem_Psi_iff _).1 i.2`. Establish `hj : (j : R.GG).1.2 = 1` using `(Formalism.HC.Frame.mem_Psi_iff _).1 j.2`. Establish `h2 : (j : R.GG).1.2 = (i : R.GG).1.2 * (-1)` using `by rw [h1]; rfl`. Rewrite `h2` using `[hi, hj]`. Conclude with `absurd h2 (by decide)`.

Introduce `ρ`. Take `⟨g, rfl⟩` from `(H.gal).symm.surjective ρ`. Break down `Int.units_eq_one_or g.1.2 with hg | hg` into its components or cases. Conclude with `Or.inl ⟨⟨g, (Formalism.HC.Frame.mem_Psi_iff _).2 hg⟩, rfl⟩`. Use `Or.inr ⟨⟨g * R.cc, (Formalism.HC.Frame.mem_Psi_iff _).2 ?_⟩, sigmaOf_mul H g (R.cc)⟩ show g.1.2 * (-1) = 1` and prove the remaining obligations.

Rewrite using `[hg]`. Evaluate the decidable proposition.
-/
theorem bijective_Psi (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 H.E) | (p : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E)
    (w : HeightOneSpectrum (𝓞 H.E)) (hw : (p : 𝓞 H.E) ∈ w.asIdeal) :
    Function.Bijective (fun τ : ↥(R.Psi) => (⟨underPl H.F (pullPl (H.sigmaOf (τ : R.GG)) w),
      (natCast_mem_underPl H.F _ p).2 ((natCast_mem_pullPl _ w p).2 hw)⟩ : PlT H p)) := by
  have := H.hostE_isGalois
  refine bijective_underPl_pullPl H.conj (mem_F_iff H) (conj_conj H) p hp hs
    (fun τ : ↥(R.Psi) => H.sigmaOf (τ : R.GG)) ((sigmaOf_injective H).comp Subtype.val_injective) ?_ ?_ w hw
  · intro i j h
    rw [conj_eq_sigmaOf, ← sigmaOf_mul] at h
    have h1 := sigmaOf_injective H h
    have hi : (i : R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 i.2
    have hj : (j : R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 j.2
    have h2 : (j : R.GG).1.2 = (i : R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [hi, hj] at h2
    exact absurd h2 (by decide)
  · intro ρ
    obtain ⟨g, rfl⟩ := (H.gal).symm.surjective ρ
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · exact Or.inl ⟨⟨g, (Formalism.HC.Frame.mem_Psi_iff _).2 hg⟩, rfl⟩
    · refine Or.inr ⟨⟨g * R.cc, (Formalism.HC.Frame.mem_Psi_iff _).2 ?_⟩, sigmaOf_mul H g (R.cc)⟩
      show g.1.2 * (-1) = 1
      rw [hg]; decide

/- English proof (translation)
Establish `hne : Ideal.span {(p : 𝓞 H.E)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Establish `h1 : (1 : 𝓞 H.E) ∈ Ideal.span {(p : 𝓞 H.E)}`. Rewrite using `[Ideal.span_singleton_eq_top.2 hu]`.

Discharge the goal by the elementary cases of `trivial`. Establish `h2 : ((p : ℕ) : ℤ) ∣ 1` using `int_dvd_of_mem_span (E := H.E) p 1 (by simpa using h1)`. Conclude with `hp.one_lt.ne' (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hpP : (p : 𝓞 H.E) ∈ P` using `hle (Ideal.mem_span_singleton_self _)`.

Use `⟨⟨P, hP.isPrime, ?_⟩, hpP⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpP))`.
-/
theorem exists_place_E (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal := by
  have hne : Ideal.span {(p : 𝓞 H.E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : (1 : 𝓞 H.E) ∈ Ideal.span {(p : 𝓞 H.E)} := by
      rw [Ideal.span_singleton_eq_top.2 hu]; trivial
    have h2 : ((p : ℕ) : ℤ) ∣ 1 := int_dvd_of_mem_span (E := H.E) p 1 (by simpa using h1)
    exact hp.one_lt.ne' (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hpP : (p : 𝓞 H.E) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨P, hP.isPrime, ?_⟩, hpP⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpP))

end HostGal

/- English proof (translation)
The claim follows from `T_split_E H T pz h.pz_norm h.pz_cong h.T_prime`.
-/
theorem T_split_of_levHyp {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E)
    (h : LevHyp H T pz piG) :
    {w : HeightOneSpectrum (𝓞 H.E) | ((T : ℕ) : 𝓞 H.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ H.E :=
  T_split_E H T pz h.pz_norm h.pz_cong h.T_prime

/- English proof (translation)
Introduce `H T pz _ h i` and use `T_ne_g H T pz h.pz_norm h.pz_cong i`.
-/
theorem factTNeG : FactTNeG := fun H T pz _ h i => T_ne_g H T pz h.pz_norm h.pz_cong i

/- English proof (translation)
Introduce `R H T pz piG h w hw`. Establish `hb` using `bijective_Psi H T h.T_prime (T_split_E H T pz h.pz_norm h.pz_cong h.T_prime) w hw`. Use `⟨(Equiv.ofBijective _ hb).symm, fun v x => ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_underPl_pullPl_iff]`. Establish `hv` using `(Equiv.ofBijective _ hb).apply_symm_apply v`.

Use `conv_lhs => rw [← hv]`. Both sides reduce to the same expression.
-/
theorem factTau : FactTau := by
  intro R H T pz piG h w hw
  have hb := bijective_Psi H T h.T_prime (T_split_E H T pz h.pz_norm h.pz_cong h.T_prime) w hw
  refine ⟨(Equiv.ofBijective _ hb).symm, fun v x => ?_⟩
  rw [← mem_underPl_pullPl_iff]
  have hv := (Equiv.ofBijective _ hb).apply_symm_apply v
  conv_lhs => rw [← hv]
  rfl

/- English proof (translation)
Introduce `R H T pz piG h`. Take `⟨w, hw⟩` from `exists_place_E H T h.T_prime`. Establish `hb` using `bijective_Psi H T h.T_prime (T_split_E H T pz h.pz_norm h.pz_cong h.T_prime) w hw`. Conclude with `⟨((Fintype.equivFinOfCardEq (card_realPlaces_eq_degree R)).symm).trans (Equiv.ofBijective _ hb)⟩`.
-/
theorem factPlacesT : FactPlacesT := by
  intro R H T pz piG h
  obtain ⟨w, hw⟩ := exists_place_E H T h.T_prime
  have hb := bijective_Psi H T h.T_prime (T_split_E H T pz h.pz_norm h.pz_cong h.T_prime) w hw
  exact ⟨((Fintype.equivFinOfCardEq (card_realPlaces_eq_degree R)).symm).trans (Equiv.ofBijective _ hb)⟩

section Deg

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Use extensionality with `I`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v.isPrime, liesOver_of_natCast_mem p hp v hv⟩`.

Introduce and unpack `⟨hI, hIl⟩`. Establish `hI0 : I ≠ ⊥`. Introduce and unpack `rfl`. Establish `h0 : Ideal.span {(p : ℤ)} = ⊥`. Rewrite using `[hIl.over]`.

Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))`. Conclude with `hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)`. Use `⟨⟨I, hI, hI0⟩, ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((p : ℕ) : 𝓞 K) ∈ I`. Establish `: (p : ℤ) ∈ I.under ℤ` using `by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _`.

Simplify using `using this`.
-/
theorem image_places_eq_primesOver (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | (p : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  ext I
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_of_natCast_mem p hp v hv⟩
  · rintro ⟨hI, hIl⟩
    have hI0 : I ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hIl.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    refine ⟨⟨I, hI, hI0⟩, ?_, rfl⟩
    change ((p : ℕ) : 𝓞 K) ∈ I
    have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
    simpa using this

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hpI : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ`. Establish `hpM : (Ideal.span {(p : ℤ)}).IsMaximal` using `hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)`. Rewrite `hsum` using `[RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h), image_places_eq_primesOver p hp, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]`.

Establish `hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ`. Introduce and unpack `⟨q, hq, hql⟩`. Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos q ℤ) (Ideal.inertiaDeg_pos q ℤ)`. Establish `hall` using `(Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm ⟨v.asIdeal, v.isPrime, liesOver_of_natCast_mem p hp v hv⟩ (Finset.mem_univ _)`. Conclude with `⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩`.
-/
theorem ram_inertia_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _
    (fun v w h => HeightOneSpectrum.ext h), image_places_eq_primesOver p hp,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones] at hsum
  have hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hql⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q ℤ) (Ideal.inertiaDeg_pos q ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm
    ⟨v.asIdeal, v.isPrime, liesOver_of_natCast_mem p hp v hv⟩ (Finset.mem_univ _)
  exact ⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Use `liesOver_of_natCast_mem p hp v hv` as an intermediate fact. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hpI : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ`. Establish `hpM : (Ideal.span {(p : ℤ)}).IsMaximal` using `hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)`.

Establish `h1 : Ideal.absNorm v.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)` using `Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp`. Rewrite `h1` using `[Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal, (ram_inertia_of_split p hp hs v hv).2, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `h1`.
-/
theorem card_quot_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := liesOver_of_natCast_mem p hp v hv
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have h1 : Ideal.absNorm v.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  rw [Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal,
    (ram_inertia_of_split p hp hs v hv).2, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  exact h1

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Establish `hr : ((p : ℕ) : 𝓞 K) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Simplify using the standard rewrite rules.

Establish `hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥`. Rewrite using `[hmap, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hr`. Use `liesOver_of_natCast_mem p hp v hv` as an intermediate fact. Establish `he` using `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal hne`.

Rewrite `he` using `[hmap, (ram_inertia_of_split p hp hs v hv).1]`. Rewrite using `[v.intValuation_eq_exp_neg_multiplicity hr, ← he]`. Both sides reduce to the same expression.
-/
theorem intValuation_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation (p : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  have := v.isPrime
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have := liesOver_of_natCast_mem p hp v hv
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    v.asIdeal hne
  rw [hmap, (ram_inertia_of_split p hp hs v hv).1] at he
  rw [v.intValuation_eq_exp_neg_multiplicity hr, ← he]
  rfl

/- English proof (translation)
Introduce `h`. Establish `h1` using `(v.intValuation_le_pow_iff_mem (p : 𝓞 K) 2).2 h`. Rewrite `h1` using `[intValuation_of_split p hp hs v hv, WithZero.exp_le_exp]`. Evaluate the numerical expressions using `at h1`.
-/
theorem natCast_notMem_sq_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) : (p : 𝓞 K) ∉ v.asIdeal ^ 2 := by
  intro h
  have h1 := (v.intValuation_le_pow_iff_mem (p : 𝓞 K) 2).2 h
  rw [intValuation_of_split p hp hs v hv, WithZero.exp_le_exp] at h1
  norm_num at h1

end Deg

section Two

variable {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F]
  (c : E ≃ₐ[ℚ] E) (hF : ∀ x : E, x ∈ F ↔ c x = x) (hc : ∀ x : E, c (c x) = x)

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[mem_pullPl, one_smul]`.
-/
theorem pullPl_one (w : HeightOneSpectrum (𝓞 E)) : pullPl 1 w = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_pullPl, one_smul]

/- English proof (translation)
Introduce `h`. Apply `hσ` to reduce the goal to its premises. Apply `pullPl_injective p hp hs w hw` to reduce the goal to its premises. Use `show pullPl σ w = pullPl 1 w`. Rewrite using `[h, pullPl_one]`.
-/
theorem pullPl_ne_self [IsGalois ℚ E] (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) (σ : E ≃ₐ[ℚ] E) (hσ : σ ≠ 1) :
    pullPl σ w ≠ w := by
  intro h
  apply hσ
  apply pullPl_injective p hp hs w hw
  show pullPl σ w = pullPl 1 w
  rw [h, pullPl_one]

/- English proof (translation)
Establish `hT : (p : 𝓞 E) = pz * c • pz`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show ((p : 𝓞 E) : E) = (pz : E) * c (pz : E)`. Rewrite using `[hpz]`. Simplify using the standard rewrite rules.

Rewrite using `[mem_pullPl]`. Distinguish the cases in `h1 : pz ∈ w.asIdeal`. Use `Or.inl ⟨h1, fun h2 => hw2 ?_⟩` and prove the remaining obligations. Rewrite using `[hT, sq]`. Conclude with `Ideal.mul_mem_mul h1 h2`.

Use `Or.inr ⟨h1, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[hT]`. Conclude with `(w.isPrime.mem_or_mem hw).resolve_left h1`.
-/
theorem mem_xor_of_norm (p : ℕ) (pz : 𝓞 E) (hpz : (pz : E) * c (pz : E) = (p : E))
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) (hw2 : (p : 𝓞 E) ∉ w.asIdeal ^ 2) :
    (pz ∈ w.asIdeal ∧ pz ∉ (pullPl c w).asIdeal) ∨ (pz ∉ w.asIdeal ∧ pz ∈ (pullPl c w).asIdeal) := by
  have hT : (p : 𝓞 E) = pz * c • pz := by
    apply RingOfIntegers.ext
    show ((p : 𝓞 E) : E) = (pz : E) * c (pz : E)
    rw [hpz]; simp
  rw [mem_pullPl]
  by_cases h1 : pz ∈ w.asIdeal
  · refine Or.inl ⟨h1, fun h2 => hw2 ?_⟩
    rw [hT, sq]
    exact Ideal.mul_mem_mul h1 h2
  · refine Or.inr ⟨h1, ?_⟩
    rw [hT] at hw
    exact (w.isPrime.mem_or_mem hw).resolve_left h1

include hF hc in

/- English proof (translation)
Take `⟨w0, rfl⟩` from `exists_underPl_eq F v`. Establish `hw0 : (p : 𝓞 E) ∈ w0.asIdeal` using `(natCast_mem_underPl F w0 p).1 hv`. Establish `key : ∀ w : HeightOneSpectrum (𝓞 E), underPl F w = underPl F w0 → pz ∈ w.asIdeal → ∀ w' : HeightOneSpectrum (𝓞 E), underPl F w' = underPl F w0 ∧ pz ∈ w'.asIdeal → w' = w`. Introduce and unpack `w hw hpw w' ⟨hw', hpw'⟩`. Establish `hwp : (p : 𝓞 E) ∈ w.asIdeal`.

Rewrite using `[← natCast_mem_underPl F w p, hw]`. Conclude with `hv`. Break down `eq_or_eq_conj_of_underPl_eq c hF hc w w' (hw.trans hw'.symm) with h | h` into its components or cases. Conclude with `h`. Break down `mem_xor_of_norm c p pz hpz w hwp (natCast_notMem_sq_of_split p hp hs w hwp) with h1 | h1` into its components or cases.

Conclude with `absurd (h ▸ hpw') h1.2`. Conclude with `absurd hpw h1.1`. Break down `mem_xor_of_norm c p pz hpz w0 hw0 (natCast_notMem_sq_of_split p hp hs w0 hw0) with h1 | h1` into its components or cases. Conclude with `⟨w0, ⟨rfl, h1.1⟩, key w0 rfl h1.1⟩`. Conclude with `⟨pullPl c w0, ⟨underPl_pullPl_conj c hF w0, h1.2⟩, key _ (underPl_pullPl_conj c hF w0) h1.2⟩`.
-/
theorem existsUnique_place_over (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (pz : 𝓞 E) (hpz : (pz : E) * c (pz : E) = (p : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    ∃! w : HeightOneSpectrum (𝓞 E), underPl F w = v ∧ pz ∈ w.asIdeal := by
  obtain ⟨w0, rfl⟩ := exists_underPl_eq F v
  have hw0 : (p : 𝓞 E) ∈ w0.asIdeal := (natCast_mem_underPl F w0 p).1 hv
  have key : ∀ w : HeightOneSpectrum (𝓞 E), underPl F w = underPl F w0 → pz ∈ w.asIdeal →
      ∀ w' : HeightOneSpectrum (𝓞 E), underPl F w' = underPl F w0 ∧ pz ∈ w'.asIdeal → w' = w := by
    rintro w hw hpw w' ⟨hw', hpw'⟩
    have hwp : (p : 𝓞 E) ∈ w.asIdeal := by
      rw [← natCast_mem_underPl F w p, hw]; exact hv
    rcases eq_or_eq_conj_of_underPl_eq c hF hc w w' (hw.trans hw'.symm) with h | h
    · exact h
    · rcases mem_xor_of_norm c p pz hpz w hwp (natCast_notMem_sq_of_split p hp hs w hwp) with h1 | h1
      · exact absurd (h ▸ hpw') h1.2
      · exact absurd hpw h1.1
  rcases mem_xor_of_norm c p pz hpz w0 hw0 (natCast_notMem_sq_of_split p hp hs w0 hw0) with h1 | h1
  · exact ⟨w0, ⟨rfl, h1.1⟩, key w0 rfl h1.1⟩
  · exact ⟨pullPl c w0, ⟨underPl_pullPl_conj c hF w0, h1.2⟩, key _ (underPl_pullPl_conj c hF w0) h1.2⟩

end Two

section HostDeg

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Rewrite using `[H.finrank_hostF]`. Both sides reduce to the same expression.
-/
theorem finrank_F : Module.finrank ℚ H.F = R.f := by
  rw [H.finrank_hostF]; rfl

/- English proof (translation)
Introduce `h`. Establish `h1 : H.galE H.conj = R.cc` using `H.galE_conjE`. Rewrite `h1` using `[h, H.galE_one]`. Establish `h2 : (1 : ℤˣ) = -1` using `congrArg (fun g : R.GG => g.1.2) h1`. Conclude with `absurd h2 (by decide)`.
-/
theorem conj_ne_one : H.conj ≠ 1 := by
  intro h
  have h1 : H.galE H.conj = R.cc := H.galE_conjE
  rw [h, H.galE_one] at h1
  have h2 : (1 : ℤˣ) = -1 := congrArg (fun g : R.GG => g.1.2) h1
  exact absurd h2 (by decide)

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_place_E H p hp`. Establish `hb` using `bijective_Psi H p hp hs w hw`. Establish `h1 : Nat.card (PlT H p) = Nat.card ↥(R.Psi)` using `(Nat.card_congr (Equiv.ofBijective _ hb)).symm`. Establish `h2` using `card_realPlaces_eq_degree R`. Rewrite `h2` using `[← Nat.card_eq_fintype_card]`.

Rewrite using `[← Nat.card_coe_set_eq, finrank_F, ← h2, ← h1]`. Both sides reduce to the same expression.
-/
theorem split_F (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 H.E) | (p : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E) :
    {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.F := by
  obtain ⟨w, hw⟩ := exists_place_E H p hp
  have hb := bijective_Psi H p hp hs w hw
  have h1 : Nat.card (PlT H p) = Nat.card ↥(R.Psi) := (Nat.card_congr (Equiv.ofBijective _ hb)).symm
  have h2 := card_realPlaces_eq_degree R
  rw [← Nat.card_eq_fintype_card] at h2
  rw [← Nat.card_coe_set_eq, finrank_F, ← h2, ← h1]
  rfl

/- English proof (translation)
The claim follows from `card_quot_of_split p hp (split_F H p hp hs) v hv`.
-/
theorem card_quot_F (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 H.E) | (p : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    Nat.card (𝓞 H.F ⧸ v.asIdeal) = p :=
  card_quot_of_split p hp (split_F H p hp hs) v hv

/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Conclude with `pullPl_ne_self p hp hs w hw H.conj (conj_ne_one H)`.
-/
theorem conj_place_ne (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 H.E) | (p : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E)
    (w : HeightOneSpectrum (𝓞 H.E)) (hw : (p : 𝓞 H.E) ∈ w.asIdeal) : pullPl H.conj w ≠ w := by
  have := H.hostE_isGalois
  exact pullPl_ne_self p hp hs w hw H.conj (conj_ne_one H)

/- English proof (translation)
The claim follows from `existsUnique_place_over H.conj (mem_F_iff H) (conj_conj H) p hp hs pz hpz v hv`.
-/
theorem existsUnique_place_over_host (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 H.E) | (p : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E)
    (pz : 𝓞 H.E) (hpz : (pz : H.E) * H.conj (pz : H.E) = (p : H.E))
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ∃! w : HeightOneSpectrum (𝓞 H.E), underPl H.F w = v ∧ pz ∈ w.asIdeal :=
  existsUnique_place_over H.conj (mem_F_iff H) (conj_conj H) p hp hs pz hpz v hv

end HostDeg

end Formalism.MainNotions.Gaps.LevGap

end
