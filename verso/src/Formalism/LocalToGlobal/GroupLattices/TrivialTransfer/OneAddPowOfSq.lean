import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureUpperUni
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowOfMulSelfEqZero
import Lemmata.GeneralBFactLeftTail.Imports

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions

namespace Formalism.L2.G.Triv

section Helpers

/- English proof (translation)
Use `conj_pow (a := a⁻¹) (b := b) (i := n)` as an intermediate fact. Simplify using `using this`.
-/
theorem conj_pow' {G : Type} [Group G] (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  have := conj_pow (a := a⁻¹) (b := b) (i := n)
  simpa using this

/- English proof (translation)
Introduce `x y hxy`. Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `congrArg (fun z : GL n B => (z : Matrix n n B)) hxy`. Conclude with `Matrix.map_injective hφ h`.
-/
theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (n := n) φ) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : GL n B => (z : Matrix n n B)) hxy
  exact Matrix.map_injective hφ h

end Helpers

section Ring

variable {R : Type} [CommRing R] {k : ℕ}

/- English proof (translation)
Set `π` to `Ideal.Quotient.mk I`. Set `φ` to `π.mapMatrix (m := Fin k)`. Set `N : Matrix (Fin k) (Fin k) (R ⧸ I)` to `φ (A - 1)`. Establish `hN0 : ∀ i j : Fin k, j ≤ i → N i j = 0` using `fun i j h => Ideal.Quotient.eq_zero_iff_mem.2 (hA i j h)`. Establish `hpow : ∀ m : ℕ, ∀ i j : Fin k, (j : ℕ) < i + m → (N ^ m) i j = 0`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j h`. Rewrite using `[pow_zero, Matrix.one_apply, if_neg]`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `i j h`. Rewrite using `[pow_succ, Matrix.mul_apply]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : (l : ℕ) < i + m`. Rewrite using `[ih i l hl, zero_mul]`. Rewrite using `[hN0 l j (by rw [Fin.le_def]; omega), mul_zero]`.

Establish `hAm : φ A = N + 1` using `by simp [N]`. Establish `hg0 : ((g : ℕ) : R ⧸ I) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hgI` as an intermediate fact. Simplify using `using this`. Establish `key : (φ A) ^ (g ^ s) = 1`.

Rewrite using `[hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `m hm hm0`. Rewrite `hm` using `[Finset.mem_range]`. Distinguish the cases in `hmm : m = g ^ s`.

Establish `: N ^ m = 0`. Use extensionality with `a b`. Conclude with `hpow m a b (by have := b.2; omega)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `hd : g ∣ (g ^ s).choose m` using `hg.dvd_choose_pow hm0 hmm`. Take `⟨c, hc⟩` from `hd`. Establish `: (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`. Rewrite using `[hc, Nat.cast_mul]`. Establish `: ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`.

Use extensionality with `a b`. Simplify using `[Matrix.natCast_apply, hg0]`. Rewrite using `[this, zero_mul]`. Rewrite using `[this, mul_zero]`. Introduce `h`.

Simplify using `at h`. Establish `: φ (A ^ (g ^ s) - 1) = 0` using `by rw [map_sub, map_pow, key, map_one, sub_self]`. Establish `h2` using `congrFun (congrFun this i) j`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2`.
-/
theorem unip_pow (I : Ideal R) (g : ℕ) (hg : g.Prime) (hgI : (g : R) ∈ I) (A : Matrix (Fin k) (Fin k) R)
    (hA : ∀ i j, j ≤ i → (A - 1) i j ∈ I) (s : ℕ) (hs : k ≤ g ^ s) (i j : Fin k) : (A ^ (g ^ s) - 1) i j ∈ I := by
  let π := Ideal.Quotient.mk I
  let φ := π.mapMatrix (m := Fin k)
  let N : Matrix (Fin k) (Fin k) (R ⧸ I) := φ (A - 1)
  have hN0 : ∀ i j : Fin k, j ≤ i → N i j = 0 := fun i j h =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hA i j h)
  have hpow : ∀ m : ℕ, ∀ i j : Fin k, (j : ℕ) < i + m → (N ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j h
      rw [pow_zero, Matrix.one_apply, if_neg]
      rintro rfl
      omega
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + m
      · rw [ih i l hl, zero_mul]
      · rw [hN0 l j (by rw [Fin.le_def]; omega), mul_zero]
  have hAm : φ A = N + 1 := by simp [N]
  have hg0 : ((g : ℕ) : R ⧸ I) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hgI
    simpa using this
  have key : (φ A) ^ (g ^ s) = 1 := by
    rw [hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      rw [Finset.mem_range] at hm
      by_cases hmm : m = g ^ s
      · have : N ^ m = 0 := by
          ext a b
          exact hpow m a b (by have := b.2; omega)
        rw [this]; simp
      · have hd : g ∣ (g ^ s).choose m := hg.dvd_choose_pow hm0 hmm
        obtain ⟨c, hc⟩ := hd
        have : (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
          rw [hc, Nat.cast_mul]
          have : ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
            ext a b
            simp [Matrix.natCast_apply, hg0]
          rw [this, zero_mul]
        rw [this, mul_zero]
    · intro h; simp at h
  have : φ (A ^ (g ^ s) - 1) = 0 := by rw [map_sub, map_pow, key, map_one, sub_self]
  have h2 := congrFun (congrFun this i) j
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero .. | (apply GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (intros; apply GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (apply @ …`.
-/
theorem one_add_pow_of_sq {S : Type} [Ring S] (X : S) (h : X * X = 0) (N : ℕ) : (1 + X) ^ N = 1 + (N : S) * X := by
  first | exact GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero .. | (apply GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (intros; apply GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (apply @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (intros; apply @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> assumption) | (apply @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero <;> first | assumption | infer_instance) | exact @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero S ‹_› X h N | exact @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero S ‹_› X h | exact @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero S ‹_› X | exact @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero S ‹_› | exact @GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero S

/- English proof (translation)
Take `⟨c, hc⟩` from `hN.exists_left_inv`. Establish `step : ∀ m : ℕ, ∀ i j, (B - 1) i j ∈ I ^ (m + 1)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using hB`.

Consider the case `succ m ih`. Set `φ` to `(Ideal.Quotient.mk (I ^ (m + 1 + 1))).mapMatrix (m := Fin k)`. Establish `hXX : φ (B - 1) * φ (B - 1) = 0`. Rewrite using `[← map_mul]`. Use extensionality with `a b`.

Use `show Ideal.Quotient.mk _ (((B - 1) * (B - 1)) a b) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Matrix.mul_apply]`. Use `Ideal.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Establish `h1 : (B - 1) a l * (B - 1) l b ∈ I ^ (m + 1) * I ^ (m + 1)` using `Ideal.mul_mem_mul (ih a l) (ih l b)`. Rewrite `h1` using `[← pow_add]`.

Conclude with `Ideal.pow_le_pow_right (by omega) h1`. Establish `h2 : (1 + φ (B - 1)) ^ N = 1`. Establish `: 1 + φ (B - 1) = φ B` using `by rw [map_sub, map_one]; abel`. Rewrite using `[this, ← map_pow, hBN, map_one]`. Rewrite `h2` using `[one_add_pow_of_sq _ hXX]`.

Establish `h3 : ((N : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I ^ (m + 1 + 1))) * φ (B - 1) = 0`. Simplify using `using h2`. Introduce `i j`. Establish `e : ((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j) = 0`. Establish `h4` using `congrFun (congrFun h3 i) j`.

Rewrite `h4` using `[← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]`. Conclude with `h4`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, map_one, one_mul]`.

Use `_ = Ideal.Quotient.mk (I ^ (m + 1 + 1)) c * (((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j)) := by`. Rewrite using `[map_mul, map_natCast, mul_assoc]`. Use `_ = 0 := by rw [e, mul_zero]`. Establish `hz : B - 1 = 0`. Use extensionality with `i j`.

Establish `: (B - 1) i j ∈ (⨅ m : ℕ, I ^ m)`. Rewrite using `[Ideal.mem_iInf]`. Introduce `m`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ m) (step m i j)`. Rewrite `this` using `[hinf]`.

Simplify using `using this`. Conclude with `sub_eq_zero.1 hz`.
-/
theorem cong_coprime (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (B : Matrix (Fin k) (Fin k) R)
    (hB : ∀ i j, (B - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R)) (hBN : B ^ N = 1) : B = 1 := by
  obtain ⟨c, hc⟩ := hN.exists_left_inv
  have step : ∀ m : ℕ, ∀ i j, (B - 1) i j ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hB
    | succ m ih =>
      let φ := (Ideal.Quotient.mk (I ^ (m + 1 + 1))).mapMatrix (m := Fin k)
      have hXX : φ (B - 1) * φ (B - 1) = 0 := by
        rw [← map_mul]
        ext a b
        show Ideal.Quotient.mk _ (((B - 1) * (B - 1)) a b) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Matrix.mul_apply]
        refine Ideal.sum_mem _ fun l _ => ?_
        have h1 : (B - 1) a l * (B - 1) l b ∈ I ^ (m + 1) * I ^ (m + 1) := Ideal.mul_mem_mul (ih a l) (ih l b)
        rw [← pow_add] at h1
        exact Ideal.pow_le_pow_right (by omega) h1
      have h2 : (1 + φ (B - 1)) ^ N = 1 := by
        have : 1 + φ (B - 1) = φ B := by rw [map_sub, map_one]; abel
        rw [this, ← map_pow, hBN, map_one]
      rw [one_add_pow_of_sq _ hXX] at h2
      have h3 : ((N : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I ^ (m + 1 + 1))) * φ (B - 1) = 0 := by
        simpa using h2
      intro i j
      have e : ((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j) = 0 := by
        have h4 := congrFun (congrFun h3 i) j
        rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul] at h4
        exact h4
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      calc Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j)
          = Ideal.Quotient.mk (I ^ (m + 1 + 1)) (c * (N : R)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j) := by
            rw [hc, map_one, one_mul]
        _ = Ideal.Quotient.mk (I ^ (m + 1 + 1)) c *
            (((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j)) := by
            rw [map_mul, map_natCast, mul_assoc]
        _ = 0 := by rw [e, mul_zero]
  have hz : B - 1 = 0 := by
    ext i j
    have : (B - 1) i j ∈ (⨅ m : ℕ, I ^ m) := by
      rw [Ideal.mem_iInf]
      intro m
      exact Ideal.pow_le_pow_right (Nat.le_succ m) (step m i j)
    rw [hinf] at this
    simpa using this
  exact sub_eq_zero.1 hz

/- English proof (translation)
Take `⟨s, hs⟩ : ∃ s, k ≤ g ^ s` from `⟨k, (Nat.lt_pow_self hg.one_lt).le⟩`. Establish `h1 : A ^ (g ^ s) = 1` using `cong_coprime I hinf _ (unip_pow I g hg hgI A hA s hs) N hN (by rw [← pow_mul, mul_comm, pow_mul, hAN, one_pow])`. Establish `h2` using `pow_gcd_eq_one.2 ⟨hAN, h1⟩`. Rewrite `h2` using `[Nat.Coprime.pow_right s hc, pow_one]`. Then use the resulting hypothesis.
-/
theorem unip_coprime (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (g : ℕ) (hg : g.Prime) (hgI : (g : R) ∈ I)
    (A : Matrix (Fin k) (Fin k) R) (hA : ∀ i j, j ≤ i → (A - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R))
    (hc : Nat.Coprime N g) (hAN : A ^ N = 1) : A = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, k ≤ g ^ s := ⟨k, (Nat.lt_pow_self hg.one_lt).le⟩
  have h1 : A ^ (g ^ s) = 1 :=
    cong_coprime I hinf _ (unip_pow I g hg hgI A hA s hs) N hN (by rw [← pow_mul, mul_comm, pow_mul, hAN, one_pow])
  have h2 := pow_gcd_eq_one.2 ⟨hAN, h1⟩
  rwa [Nat.Coprime.pow_right s hc, pow_one] at h2

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qe27.closure_upperUni .. | (apply UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe27.closure_upperUni …`.
-/
theorem closure_upperUni (A : Type) [CommRing A] (x : GL (Fin k) A) (hx : x ∈ Subgroup.closure (upperUni k A)) :
    x ∈ upperUni k A := by
  first | exact UpperTheory.Reformulated.B.Qe27.closure_upperUni .. | (apply UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe27.closure_upperUni <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe27.closure_upperUni k A ‹_› x hx | exact @UpperTheory.Reformulated.B.Qe27.closure_upperUni k A ‹_› x | exact @UpperTheory.Reformulated.B.Qe27.closure_upperUni k A ‹_› | exact @UpperTheory.Reformulated.B.Qe27.closure_upperUni k A | exact @UpperTheory.Reformulated.B.Qe27.closure_upperUni k

end Ring

section Place

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `h1 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) = 1`. Rewrite using `[← map_mul]`.

Use `congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hu` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at this`. Establish `e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) = (g : v.adicCompletion F)` using `by simp`. Rewrite `this` using `[e]`. Rewrite using `[this, map_one]`.

Establish `h2 : Valued.v ((g : v.adicCompletion F)) < 1`. Establish `e : (g : v.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : v.adicCompletion F)`. Rewrite using `[map_natCast]`. Conclude with `(map_natCast (algebraMap F (v.adicCompletion F)) g).symm`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]`.

Conclude with `hg`. Establish `h3 : Valued.v (u : v.adicCompletion F) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2`. Establish `h4 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2`. Rewrite `h4` using `[h1]`. Conclude with `lt_irrefl _ h4`.
-/
theorem natCast_mem_max (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hu
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    have e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) = (g : v.adicCompletion F) := by simp
    rw [e] at this
    rw [this, map_one]
  have h2 : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have e : (g : v.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : v.adicCompletion F) := by
      rw [map_natCast]
      exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hg
  have h3 : Valued.v (u : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2
  have h4 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2
  rw [h1] at h4
  exact lt_irrefl _ h4

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hδ`. Establish `hinj : Function.Injective (bc (n` using `Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) := bc_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Establish `haN : a ^ N = 1` using `hinj (by rw [map_pow, hN, map_one])`. Establish `hu` using `closure_upperUni _ _ (Subgroup.mem_comap.1 ha)`. Establish `hgm` using `natCast_mem_max v g hgv`.

Establish `hNu : IsUnit (N : v.adicCompletionIntegers F)`. Assume the negation of the conclusion as `h`. Establish `hm : (N : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)` using `(IsLocalRing.mem_maximalIdeal _).2 h`. Establish `h1 : ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Establish `hb` using `Nat.gcd_eq_gcd_ab N g`.

Establish `: ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) = (N : v.adicCompletionIntegers F) * ((Nat.gcdA N g : ℤ) : v.adicCompletionIntegers F) + (g : v.adicCompletionIntegers F) * ((Nat.gcdB N g : ℤ) : v.adicCompletionIntegers F)`. Use `congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hb` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hgm)`. Rewrite `h1` using `[hc, Nat.cast_one]`. Conclude with `(Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1`. Establish `hA : ∀ i j : Fin k, j ≤ i → ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) - 1) i j ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Introduce `i j hij`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub]`. Break down `hij.lt_or_eq with h | h` into its components or cases. Use `(hu i j).1 h` as an intermediate fact. Establish `h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i j) = 0` using `this`. Rewrite using `[h', Matrix.one_apply_ne h.ne', map_zero, sub_zero]`.

Substitute `h` using the available equality. Use `(hu j j).2` as an intermediate fact. Establish `h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) j j) = 1` using `this`. Rewrite using `[h', Matrix.one_apply_eq, map_one, sub_self]`. Establish `h1 : (a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) = 1` using `unip_coprime _ (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) g hg hgm _ hA N hNu hc (by rw [← Units.val_pow_eq_pow_val, haN, Units.val_one])`.

Establish `: a = 1` using `Units.ext h1`. Rewrite using `[this, map_one]`.
-/
theorem iwU_coprime (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal)
    (δ : GL (Fin k) (v.adicCompletion F)) (hδ : δ ∈ iwU F k v) (N : ℕ) (hc : Nat.Coprime N g) (hN : δ ^ N = 1) : δ = 1 := by
  obtain ⟨a, ha, rfl⟩ := hδ
  have hinj : Function.Injective (bc (n := Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have haN : a ^ N = 1 := hinj (by rw [map_pow, hN, map_one])
  have hu := closure_upperUni _ _ (Subgroup.mem_comap.1 ha)
  have hgm := natCast_mem_max v g hgv
  have hNu : IsUnit (N : v.adicCompletionIntegers F) := by
    by_contra h
    have hm : (N : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    have h1 : ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      have hb := Nat.gcd_eq_gcd_ab N g
      have : ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) =
          (N : v.adicCompletionIntegers F) * ((Nat.gcdA N g : ℤ) : v.adicCompletionIntegers F) +
          (g : v.adicCompletionIntegers F) * ((Nat.gcdB N g : ℤ) : v.adicCompletionIntegers F) := by
        have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hb
        push_cast at this
        exact this
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hgm)
    rw [hc, Nat.cast_one] at h1
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hA : ∀ i j : Fin k, j ≤ i → ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) - 1) i j ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro i j hij
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub]
    rcases hij.lt_or_eq with h | h
    · have := (hu i j).1 h
      have h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i j) = 0 := this
      rw [h', Matrix.one_apply_ne h.ne', map_zero, sub_zero]
    · subst h
      have := (hu j j).2
      have h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) j j) = 1 := this
      rw [h', Matrix.one_apply_eq, map_one, sub_self]
  have h1 : (a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) = 1 :=
    unip_coprime _ (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) g hg hgm _ hA N hNu hc
      (by rw [← Units.val_pow_eq_pow_val, haN, Units.val_one])
  have : a = 1 := Units.ext h1
  rw [this, map_one]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_left_tail.goal1 .. | (apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_ta …`.
-/
theorem exists_place (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  first | exact Bl.general_b_fact_left_tail.goal1 .. | (apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_tail.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_tail.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› g hg | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› g | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› | exact @Bl.general_b_fact_left_tail.goal1 F

end Place

end Formalism.L2.G.Triv

end
