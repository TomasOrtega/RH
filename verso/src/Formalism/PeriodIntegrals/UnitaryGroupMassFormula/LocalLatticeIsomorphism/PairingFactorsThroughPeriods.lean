import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.EquivariantPartsOfFiniteType

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/- English proof (translation)
Establish `e : z * cj ((s : E) * y) = algebraMap K E (s : K) * (z * cj y)`. Rewrite using `[map_mul cj, map_natCast cj, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Algebra.smul_def, map_smul, smul_eq_mul]`.
-/
theorem trace_mul_natCast (cj : E ≃ₐ[ℚ] E) (s : ℕ) (z y : E) :
    Algebra.trace K E (z * cj ((s : E) * y)) = (s : K) * Algebra.trace K E (z * cj y) := by
  have e : z * cj ((s : E) * y) = algebraMap K E (s : K) * (z * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `h1 : (1 : E) ∈ I` using `(hI 1).2 fun z hz => by`. Rewrite using `[hne z hz, zero_mul, map_zero]`. Conclude with `zero_mem _`.

Conclude with `one_ne_zero (hne 1 h1)`.
-/
theorem exists_ne_zero_mem (cj : E ≃ₐ[ℚ] E) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hI : PI.KerIso.SelfDualI K cj I) : ∃ y0 ∈ I, y0 ≠ 0 := by
  by_contra hne
  push Not at hne
  have h1 : (1 : E) ∈ I := (hI 1).2 fun z hz => by
    rw [hne z hz, zero_mul, map_zero]; exact zero_mem _
  exact one_ne_zero (hne 1 h1)

/- English proof (translation)
Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (L := E) {e / y0}`. Establish `hi : IsIntegral ℤ ((y : E) * (e / y0))`. Use `hint (e / y0) (Finset.mem_singleton_self _)` as an intermediate fact. Simplify `this` using `[zsmul_eq_mul]`. Establish `hN : IsIntegral ℤ ((y.natAbs : E) * (e / y0))`.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `: (y.natAbs : E) = (y : E)` using `by rw [← Int.cast_natCast, ← h]`. Rewrite using `[this]`. Conclude with `hi`. Establish `: (y.natAbs : E) = -(y : E)`.

Establish `h' : (y.natAbs : ℤ) = -y` using `by omega`. Rewrite using `[← Int.cast_natCast, h', Int.cast_neg]`. Rewrite using `[this, neg_mul]`. Conclude with `hi.neg`. Use `⟨y.natAbs, Int.natAbs_ne_zero.mpr hy, ?_⟩` and prove the remaining obligations.

Establish `key : (y.natAbs : E) * e = ((⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) : E) * y0` using `by show (y.natAbs : E) * e = (y.natAbs : E) * (e / y0) * y0`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `(I : Submodule (𝓞 E) E).smul_mem (⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) hy0`.
-/
theorem exists_natCast_mul_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {y0 : E}
    (hy0 : y0 ∈ I) (hne : y0 ≠ 0) (e : E) : ∃ N : ℕ, N ≠ 0 ∧ (N : E) * e ∈ I := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e / y0}
  have hi : IsIntegral ℤ ((y : E) * (e / y0)) := by
    have := hint (e / y0) (Finset.mem_singleton_self _)
    simpa [zsmul_eq_mul] using this
  have hN : IsIntegral ℤ ((y.natAbs : E) * (e / y0)) := by
    rcases Int.natAbs_eq y with h | h
    · have : (y.natAbs : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]; exact hi
    · have : (y.natAbs : E) = -(y : E) := by
        have h' : (y.natAbs : ℤ) = -y := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hi.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy, ?_⟩
  have key : (y.natAbs : E) * e = ((⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) : E) * y0 := by
    show (y.natAbs : E) * e = (y.natAbs : E) * (e / y0) * y0
    field_simp
  rw [key]
  exact (I : Submodule (𝓞 E) E).smul_mem (⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) hy0

/- English proof (translation)
Use `(I : Submodule (𝓞 E) E).smul_mem (q : 𝓞 E) hz` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, map_natCast]`. Then use the resulting hypothesis.
-/
theorem natCast_mul_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (q : ℕ) {z : E}
    (hz : z ∈ I) : (q : E) * z ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (q : 𝓞 E) hz
  rwa [Algebra.smul_def, map_natCast] at this

variable (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {n : Type} [Fintype n]
  (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
  (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))

include hc in
/- English proof (translation)
Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsv⟩ w ⟨t, ht, htw⟩`. Use `⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩` and prove the remaining obligations. Establish `e1 : hf (conjK cj hc.2.1) v w = ∑ a, Algebra.trace K E (g₀.symm v a * cj (g₀.symm w a))`.

Rewrite using `[← hf_isom cj hc.2.1 g₀ hg]`. Simplify using the standard rewrite rules. Rewrite using `[e1, Finset.mul_sum]`. Use `Subring.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← trace_natCast_mul]`.

Conclude with `(hI _).1 (htw a) _ (hsv a)`. Introduce `hv set x := g₀.symm v with hx`. Establish `claim1 : ∀ a, ∀ z ∈ I, Rp K p (Algebra.trace K E (z * cj (x a)))`. Introduce `a z hz`. Establish `hw : g₀ (Pi.single a z) ∈ Lset I p g₀` using `⟨1, Nat.coprime_one_left p, fun b => by`.

Rewrite using `[Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `using hz`. Rewrite using `[Pi.single_eq_of_ne hb]`.

Conclude with `FractionalIdeal.mem_coe.mp (I : Submodule (𝓞 E) E).zero_mem⟩`. Establish `h2` using `Rp_map (conjK cj hc.2.1) (hv _ hw)`. Rewrite `h2` using `[← hf_symm _ (conjK_invol cj hc)]`. Establish `e2 : hf (conjK cj hc.2.1) (g₀ (Pi.single a z)) v = Algebra.trace K E (z * cj (x a))`. Establish `: v = g₀ x` using `by simp [hx]`.

Rewrite using `[this, hf_isom cj hc.2.1 g₀ hg, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`. Rewrite `h2` using `[e2]`. Then use the resulting hypothesis. Take `⟨T, hT⟩` from `(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars (R := ℤ)`. Establish `hTI : ∀ z ∈ T, z ∈ I` using `fun z hz => by`. Establish `: z ∈ ((I : Submodule (𝓞 E) E).restrictScalars ℤ)` using `hT ▸ Submodule.subset_span hz`.

Conclude with `this`. Establish `claim2 : ∀ a, ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z ∈ I, (s : K) * Algebra.trace K E (z * cj (x a)) ∈ (algebraMap (𝓞 K) K).range`. Introduce `a`. Take `⟨s, hs, hsT⟩` from `Rp_finset (p := p) T (fun z => Algebra.trace K E (z * cj (x a))) fun z hz => claim1 a z (hTI z hz)`. Use `⟨s, hs, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hz' : z ∈ Submodule.span ℤ (T : Set E)`. Rewrite using `[hT]`. Conclude with `hz`. Use `clear hz`. Proceed by induction on `hz' using Submodule.span_induction with`.

Consider the case `mem z hz => exact hsT z hz`. Consider the case `zero => simp`. Consider the case `add z z' _ _ h h'`. Rewrite using `[add_mul, map_add, mul_add]`. Conclude with `Subring.add_mem _ h h'`.

Consider the case `smul k z _ h`. Establish `e : (s : K) * Algebra.trace K E ((k • z) * cj (x a)) = k • ((s : K) * Algebra.trace K E (z * cj (x a)))`. Rewrite using `[smul_mul_assoc, map_zsmul, mul_smul_comm]`. Rewrite using `[e]`. Conclude with `Subring.zsmul_mem _ h k`.

Use `choose s hs hsI using claim2`. Use `⟨∏ a, s a, Nat.Coprime.prod_left fun a _ => hs a, fun a => (hI _).2 fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[trace_mul_natCast]`. Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem s (Finset.mem_univ a)`. Rewrite using `[hq, Nat.cast_mul, mul_comm (s a : K), mul_assoc]`.

Conclude with `Subring.mul_mem _ (natCast_mem _ q) (hsI a z hz)`.
-/
theorem lset_unimod (hI : PI.KerIso.SelfDualI K cj I) (hg : PI.KerIso.IsIsom cj g₀) :
    Unimod K (conjK cj hc.2.1) p (Lset I p g₀) := by
  intro v
  constructor
  · rintro ⟨s, hs, hsv⟩ w ⟨t, ht, htw⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e1 : hf (conjK cj hc.2.1) v w =
        ∑ a, Algebra.trace K E (g₀.symm v a * cj (g₀.symm w a)) := by
      rw [← hf_isom cj hc.2.1 g₀ hg]; simp
    rw [e1, Finset.mul_sum]
    refine Subring.sum_mem _ fun a _ => ?_
    rw [← trace_natCast_mul]
    exact (hI _).1 (htw a) _ (hsv a)
  · intro hv
    set x := g₀.symm v with hx

    have claim1 : ∀ a, ∀ z ∈ I, Rp K p (Algebra.trace K E (z * cj (x a))) := by
      intro a z hz
      classical
      have hw : g₀ (Pi.single a z) ∈ Lset I p g₀ := ⟨1, Nat.coprime_one_left p, fun b => by
        rw [Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]
        by_cases hb : b = a
        · subst hb; simpa using hz
        · rw [Pi.single_eq_of_ne hb]; exact FractionalIdeal.mem_coe.mp (I : Submodule (𝓞 E) E).zero_mem⟩
      have h2 := Rp_map (conjK cj hc.2.1) (hv _ hw)
      rw [← hf_symm _ (conjK_invol cj hc)] at h2
      have e2 : hf (conjK cj hc.2.1) (g₀ (Pi.single a z)) v =
          Algebra.trace K E (z * cj (x a)) := by
        have : v = g₀ x := by simp [hx]
        rw [this, hf_isom cj hc.2.1 g₀ hg, Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ a) h
      rwa [e2] at h2

    obtain ⟨T, hT⟩ := (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars (R := ℤ)
    have hTI : ∀ z ∈ T, z ∈ I := fun z hz => by
      have : z ∈ ((I : Submodule (𝓞 E) E).restrictScalars ℤ) := hT ▸ Submodule.subset_span hz
      exact this
    have claim2 : ∀ a, ∃ s : ℕ, Nat.Coprime s p ∧
        ∀ z ∈ I, (s : K) * Algebra.trace K E (z * cj (x a)) ∈ (algebraMap (𝓞 K) K).range := by
      intro a
      obtain ⟨s, hs, hsT⟩ := Rp_finset (p := p) T (fun z => Algebra.trace K E (z * cj (x a)))
        fun z hz => claim1 a z (hTI z hz)
      refine ⟨s, hs, fun z hz => ?_⟩
      have hz' : z ∈ Submodule.span ℤ (T : Set E) := by
        rw [hT]; exact hz
      clear hz
      induction hz' using Submodule.span_induction with
      | mem z hz => exact hsT z hz
      | zero => simp
      | add z z' _ _ h h' =>
        rw [add_mul, map_add, mul_add]; exact Subring.add_mem _ h h'
      | smul k z _ h =>
        have e : (s : K) * Algebra.trace K E ((k • z) * cj (x a)) =
            k • ((s : K) * Algebra.trace K E (z * cj (x a))) := by
          rw [smul_mul_assoc, map_zsmul, mul_smul_comm]
        rw [e]; exact Subring.zsmul_mem _ h k
    choose s hs hsI using claim2
    refine ⟨∏ a, s a, Nat.Coprime.prod_left fun a _ => hs a, fun a => (hI _).2 fun z hz => ?_⟩
    rw [trace_mul_natCast]
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ a)
    rw [hq, Nat.cast_mul, mul_comm (s a : K), mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ q) (hsI a z hz)

include hc in
/- English proof (translation)
Introduce `v`. Take `⟨y0, hy0, hne⟩` from `exists_ne_zero_mem cj I hI`. Use `choose N hN hNI using fun a => exists_natCast_mul_mem I hy0 hne (g₀.symm v a)`. Use `⟨∏ a, N a, Finset.prod_ne_zero_iff.mpr fun a _ => hN a, 1, Nat.coprime_one_left p, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, one_mul, map_smul, Pi.smul_apply, Algebra.smul_def, map_natCast]`.

Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem N (Finset.mem_univ a)`. Rewrite using `[hq, Nat.cast_mul, mul_comm (N a : E), mul_assoc]`. Conclude with `natCast_mul_mem I q (hNI a)`.
-/
theorem lset_spans (hI : PI.KerIso.SelfDualI K cj I) : Spans K (Lset I p g₀) := by
  intro v
  obtain ⟨y0, hy0, hne⟩ := exists_ne_zero_mem cj I hI
  choose N hN hNI using fun a => exists_natCast_mul_mem I hy0 hne (g₀.symm v a)
  refine ⟨∏ a, N a, Finset.prod_ne_zero_iff.mpr fun a _ => hN a, 1, Nat.coprime_one_left p,
    fun a => ?_⟩
  rw [Nat.cast_one, one_mul, map_smul, Pi.smul_apply, Algebra.smul_def, map_natCast]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hq, Nat.cast_mul, mul_comm (N a : E), mul_assoc]
  exact natCast_mul_mem I q (hNI a)

end PI.KLW
