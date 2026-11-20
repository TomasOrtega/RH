import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3.EtaMu

private def Fx {Ω : Type} [Field Ω] (s : Ω →+* Ω) (a : ℤ) : Prop := ∀ δ : Ω, δ ^ 2 = (a : Ω) → s δ = δ

section
variable {Ω : Type} [Field Ω] {s : Ω →+* Ω}

/- English proof (translation)
Introduce `δ hδ`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp (hδ.trans hx.symm) with h | h` into its components or cases. Rewrite using `[h, hs]`. Rewrite using `[h, map_neg, hs]`.
-/
private theorem fx_of {a : ℤ} {x : Ω} (hx : x ^ 2 = (a : Ω)) (hs : s x = x) : Fx s a := by
  intro δ hδ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hδ.trans hx.symm) with h | h
  · rw [h, hs]
  · rw [h, map_neg, hs]

/- English proof (translation)
Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq (a : Ω) two_pos`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq (b : Ω) two_pos`. Use `fx_of (x := x * y) (by rw [mul_pow, hx, hy, Int.cast_mul]) ?_` and prove the remaining obligations. Rewrite using `[map_mul, ha x hx, hb y hy]`.
-/
private theorem fx_mul [IsAlgClosed Ω] {a b : ℤ} (ha : Fx s a) (hb : Fx s b) : Fx s (a * b) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a : Ω) two_pos
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (b : Ω) two_pos
  refine fx_of (x := x * y) (by rw [mul_pow, hx, hy, Int.cast_mul]) ?_
  rw [map_mul, ha x hx, hb y hy]

/- English proof (translation)
The claim follows from `fx_of (x := 1) (by simp) (map_one s)`.
-/
private theorem fx_one : Fx s 1 := fx_of (x := 1) (by simp) (map_one s)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `fx_one`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Conclude with `fx_mul ih ha`.
-/
private theorem fx_pow [IsAlgClosed Ω] {a : ℤ} (ha : Fx s a) (k : ℕ) : Fx s (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact fx_one
  | succ k ih =>
    rw [pow_succ]
    exact fx_mul ih ha

/- English proof (translation)
The claim follows from `fx_of (x := 2) (by norm_num) (map_ofNat s 2)`.
-/
private theorem fx_four : Fx s 4 := fx_of (x := 2) (by norm_num) (map_ofNat s 2)

variable {M : ℕ}

/- English proof (translation)
Take `⟨k, rfl⟩` from `hn`. Conclude with `h ζ (by rw [pow_mul, hζ, one_pow])`.
-/
private theorem fix_dvd (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) {n : ℕ} (hn : n ∣ M) {ζ : Ω} (hζ : ζ ^ n = 1) :
    s ζ = ζ := by
  obtain ⟨k, rfl⟩ := hn
  exact h ζ (by rw [pow_mul, hζ, one_pow])

/- English proof (translation)
Introduce `δ hδ`. Use `fix_dvd h h4 ?_` and prove the remaining obligations. Establish `: δ ^ 4 = (δ ^ 2) ^ 2` using `by ring`. Rewrite using `[this, hδ]`. Evaluate the numerical expressions.
-/
private theorem fx_neg_one (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h4 : 4 ∣ M) : Fx s (-1) := by
  intro δ hδ
  refine fix_dvd h h4 ?_
  have : δ ^ 4 = (δ ^ 2) ^ 2 := by ring
  rw [this, hδ]
  norm_num

/- English proof (translation)
Take `⟨i, hi⟩` from `IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by norm_num : 0 < 2)`. Take `⟨η, hη⟩` from `IsAlgClosed.exists_pow_nat_eq i (by norm_num : 0 < 2)`. Establish `hη8 : η ^ 8 = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h14 : η ^ 14 = -i`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsη : s η = η` using `fix_dvd h h8 hη8`. Use `fx_of (x := η + η ^ 7) ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, map_pow, hsη]`.
-/
private theorem fx_two [IsAlgClosed Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h8 : 8 ∣ M) : Fx s 2 := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by norm_num : 0 < 2)
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq i (by norm_num : 0 < 2)
  have hη8 : η ^ 8 = 1 := by
    calc η ^ 8 = ((η ^ 2) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hη, hi]; norm_num
  have h14 : η ^ 14 = -i := by
    calc η ^ 14 = ((η ^ 2) ^ 2) ^ 3 * η ^ 2 := by ring
      _ = -i := by rw [hη, hi]; ring
  have hsη : s η = η := fix_dvd h h8 hη8
  refine fx_of (x := η + η ^ 7) ?_ ?_
  · calc (η + η ^ 7) ^ 2 = η ^ 2 + 2 * η ^ 8 + η ^ 14 := by ring
      _ = ((2 : ℤ) : Ω) := by rw [hη, hη8, h14]; push_cast; ring
  · rw [map_add, map_pow, hsη]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn2 hnM`. Distinguish the cases in `h1 : n = 1`. Substitute `h1` using the available equality.

Conclude with `⟨1, rfl, rfl, fx_one⟩`. Use `set p := n.minFac with hp_def`. Establish `hp : p.Prime` using `Nat.minFac_prime h1`. Take `⟨k, hk⟩` from `Nat.minFac_dvd n`. Rewrite `hk` using `[← hp_def]`.

Establish `hp2 : p ≠ 2`. Introduce `h2`. Rewrite `hk` using `[h2]`. Use linear arithmetic over natural numbers and integers. Establish `hkpos : 0 < k`.

Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. Rewrite `hk` using `[h0, mul_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hkn : k < n`.

Rewrite using `[hk]`. Use `hp.two_le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hodd : Odd (p * k)`. Rewrite using `[← hk]`.

Conclude with `Nat.odd_iff.mpr hn2`. Establish `hk2 : k % 2 = 1` using `Nat.odd_iff.mp (Nat.odd_mul.mp hodd).2`. Take `⟨a', ha'4, ha'abs, ha'⟩` from `ih k hkn hk2 ((Dvd.intro_left p hk.symm).trans hnM)`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω p`. Take `⟨⟨x, hx⟩, hall⟩` from `CF.gauss Ω p ζ hp2 hζ`. Establish `hpM : p ∣ M` using `(Dvd.intro k hk.symm).trans hnM`. Establish `hsz : s ζ = ζ ^ 1`. Rewrite using `[pow_one]`.

Conclude with `fix_dvd h hpM hζ.pow_eq_one`. Establish `hsx : s x = x`. Use `(hall x hx).2 s 1 hsz` as an intermediate fact. Simplify `this` using `[legendreSym.at_one]`. Establish `hps : (CF.pStar p).natAbs = p`.

Simplify using `[CF.pStar, Int.natAbs_mul, Int.natAbs_pow]`. Establish `hp4 : CF.pStar p % 4 = 1`. Take `⟨a, ha⟩` from `hp.odd_of_ne_two hp2`. Use `clear_value p`. Break down `Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩` into its components or cases.

Establish `e : p / 2 = 2 * c` using `by omega`. Establish `hpz : (p : ℤ) = 4 * c + 1` using `by omega`. Rewrite using `[CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]`. Use linear arithmetic over natural numbers and integers. Establish `e : p / 2 = 2 * c + 1` using `by omega`.

Establish `hpz : (p : ℤ) = 4 * c + 3` using `by omega`. Rewrite using `[CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]`. Use linear arithmetic over natural numbers and integers. Use `⟨CF.pStar p * a', ?_, ?_, fx_mul (fx_of hx hsx) ha'⟩` and prove the remaining obligations. Rewrite using `[Int.mul_emod, hp4, ha'4]`.

Both sides reduce to the same expression. Rewrite using `[Int.natAbs_mul, hps, ha'abs, hk]`.
-/
private theorem fx_odd [IsAlgClosed Ω] [CharZero Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (n : ℕ) :
    n % 2 = 1 → n ∣ M → ∃ a : ℤ, a % 4 = 1 ∧ a.natAbs = n ∧ Fx s a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 hnM
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, fx_one⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk
          omega
        · exact h0
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hodd : Odd (p * k) := by
        rw [← hk]
        exact Nat.odd_iff.mpr hn2
      have hk2 : k % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hodd).2
      obtain ⟨a', ha'4, ha'abs, ha'⟩ := ih k hkn hk2 ((Dvd.intro_left p hk.symm).trans hnM)
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hpM : p ∣ M := (Dvd.intro k hk.symm).trans hnM
      have hsz : s ζ = ζ ^ 1 := by
        rw [pow_one]
        exact fix_dvd h hpM hζ.pow_eq_one
      have hsx : s x = x := by
        have := (hall x hx).2 s 1 hsz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * a', ?_, ?_, fx_mul (fx_of hx hsx) ha'⟩
      · rw [Int.mul_emod, hp4, ha'4]
        rfl
      · rw [Int.natAbs_mul, hps, ha'abs, hk]

/- English proof (translation)
Establish `hM0 : d.natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr hd0`. Take `⟨j, u, hu, hdu⟩` from `Nat.exists_eq_two_pow_mul_odd hM0`. Take `⟨a, ha4, haabs, ha⟩` from `fx_odd h u (Nat.odd_iff.mp hu) (Dvd.intro_left _ hdu.symm)`. Establish `hsign : d = 2 ^ j * a ∨ d = -1 * (2 ^ j * a)`. Establish `e : d.natAbs = (2 ^ j * a).natAbs`.

Rewrite using `[Int.natAbs_mul, Int.natAbs_pow, haabs, hdu]`. Both sides reduce to the same expression. Break down `Int.natAbs_eq_natAbs_iff.mp e with h' | h'` into its components or cases. Conclude with `Or.inl h'`. Conclude with `Or.inr (by rw [h']; ring)`.

Break down `Nat.lt_or_ge j 2 with hj | hj` into its components or cases. Use `interval_cases j`. Break down `hsign with h' | h'` into its components or cases. Rewrite using `[h']`. Simplify using `using ha`.

It suffices to derive a contradiction. Evaluate the numerical expressions using `at h'`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply the tactic sequence `rcases hsign with h' | h' <;> norm_num at h' <;> omega`.

Establish `h4 : 4 ∣ d.natAbs`. Rewrite using `[hdu, show (4 : ℕ) = 2 ^ 2 by norm_num]`. Conclude with `(pow_dvd_pow 2 hj).mul_right u`. Establish `hneg : Fx s (-1)` using `fx_neg_one h h4`. Establish `hpow : Fx s (2 ^ j)`.

Break down `Nat.lt_or_ge j 3 with hj3 | hj3` into its components or cases. Establish `hj2 : j = 2` using `by omega`. Rewrite using `[hj2, show (2 : ℤ) ^ 2 = 4 by norm_num]`. Conclude with `fx_four`. Establish `h8 : 8 ∣ d.natAbs`.

Rewrite using `[hdu, show (8 : ℕ) = 2 ^ 3 by norm_num]`. Conclude with `(pow_dvd_pow 2 hj3).mul_right u`. Conclude with `fx_pow (fx_two h h8) j`. Break down `hsign with h' | h'` into its components or cases. Rewrite using `[h']`.

Conclude with `fx_mul hpow ha`. Rewrite using `[h']`. Conclude with `fx_mul hneg (fx_mul hpow ha)`.
-/
private theorem fx_disc [IsAlgClosed Ω] [CharZero Ω] {d : ℤ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (h : ∀ ζ : Ω, ζ ^ d.natAbs = 1 → s ζ = ζ) : Fx s d := by
  have hM0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  obtain ⟨j, u, hu, hdu⟩ := Nat.exists_eq_two_pow_mul_odd hM0
  obtain ⟨a, ha4, haabs, ha⟩ := fx_odd h u (Nat.odd_iff.mp hu) (Dvd.intro_left _ hdu.symm)
  have hsign : d = 2 ^ j * a ∨ d = -1 * (2 ^ j * a) := by
    have e : d.natAbs = (2 ^ j * a).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow, haabs, hdu]
      rfl
    rcases Int.natAbs_eq_natAbs_iff.mp e with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [h']; ring)
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rcases hsign with h' | h'
      · rw [h']
        simpa using ha
      · exfalso
        norm_num at h'
        omega
    · exfalso
      rcases hsign with h' | h' <;> norm_num at h' <;> omega
  · have h4 : 4 ∣ d.natAbs := by
      rw [hdu, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (pow_dvd_pow 2 hj).mul_right u
    have hneg : Fx s (-1) := fx_neg_one h h4
    have hpow : Fx s (2 ^ j) := by
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · have hj2 : j = 2 := by omega
        rw [hj2, show (2 : ℤ) ^ 2 = 4 by norm_num]
        exact fx_four
      · have h8 : 8 ∣ d.natAbs := by
          rw [hdu, show (8 : ℕ) = 2 ^ 3 by norm_num]
          exact (pow_dvd_pow 2 hj3).mul_right u
        exact fx_pow (fx_two h h8) j
    rcases hsign with h' | h'
    · rw [h']
      exact fx_mul hpow ha
    · rw [h']
      exact fx_mul hneg (fx_mul hpow ha)

end

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }`. Use `haveI : IsGalois ℚ K := inferInstance`. Establish `hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `(IsGalois.card_aut_eq_finrank ℚ K).trans hK`.

Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ1⟩ : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h1 : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1` using `Fintype.card_le_one_iff.mpr (fun a b => by rw [hcon a, hcon b])`. Use linear arithmetic over natural numbers and integers.

Establish `hall : ∀ τ : K ≃ₐ[ℚ] K, τ = 1 ∨ τ = σ`. Introduce `τ`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h3 : ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K)).card = 3` using `Finset.card_eq_three.mpr ⟨1, σ, τ, hσ1.symm, hcon.1.symm, hcon.2.symm, rfl⟩`.

Establish `h4` using `Finset.card_le_univ ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K))`. Use linear arithmetic over natural numbers and integers. Establish `hσσ : ∀ x : K, σ (σ x) = x`. Establish `hsq : σ * σ = 1`. Break down `hall (σ * σ) with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Conclude with `hσ1 (mul_left_cancel (h.trans (mul_one σ).symm))`. Introduce `x`. Rewrite using `[← AlgEquiv.mul_apply, hsq, AlgEquiv.one_apply]`.

Establish `hother : ∀ τ : K ≃ₐ[ℚ] K, ¬ (τ ≠ 1 ∧ τ ≠ σ)`. Introduce `τ hτ`. Break down `hall τ with h | h` into its components or cases. Conclude with `hτ.1 h`. Conclude with `hτ.2 h`.

Establish `htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x`. Introduce `x`. Rewrite using `[trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 σ (Ne.symm hσ1)]`. Rewrite using `[AlgEquiv.one_apply]`. Introduce `τ hτ`.

Conclude with `absurd hτ (hother τ)`. Establish `hnm : ∀ x : K, algebraMap ℚ K (Algebra.norm ℚ x) = x * σ x`. Introduce `x`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, Fintype.prod_eq_mul 1 σ (Ne.symm hσ1)]`. Rewrite using `[AlgEquiv.one_apply]`.

Introduce `τ hτ`. Conclude with `absurd hτ (hother τ)`. Establish `hcardι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2`. Rewrite using `[← Module.finrank_eq_card_basis (integralBasis K), hK]`. Set `e` to `Fintype.equivFinOfCardEq hcardι`.

Take `⟨u, hu_def⟩ : ∃ u, u = integralBasis K (e.symm 0)` from `⟨_, rfl⟩`. Take `⟨v, hv_def⟩ : ∃ v, v = integralBasis K (e.symm 1)` from `⟨_, rfl⟩`. Establish `hD : ((discr K : ℤ) : ℚ) = Algebra.trace ℚ K (u * u) * Algebra.trace ℚ K (v * v) - Algebra.trace ℚ K (u * v) * Algebra.trace ℚ K (v * u)`. Rewrite using `[coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, Algebra.discr_def, Matrix.det_fin_two]`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply, hu_def, hv_def]`.

Establish `hu : IsIntegral ℤ u`. Rewrite using `[hu_def, integralBasis_apply]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Establish `hv : IsIntegral ℤ v`. Rewrite using `[hv_def, integralBasis_apply]`.

Conclude with `RingOfIntegers.isIntegral_coe _`. Establish `hintZ : ∀ q : ℚ, IsIntegral ℤ q → ∃ r : ℤ, (r : ℚ) = q`. Introduce `q hq`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hq`. Conclude with `⟨r, by simpa using hr⟩`.

Establish `hP : IsIntegral ℤ (u * σ v)` using `hu.mul (map_isIntegral_int σ hv)`. Take `⟨α, hα⟩` from `hintZ _ (Algebra.isIntegral_trace (L := ℚ) hP)`. Take `⟨β, hβ⟩` from `hintZ _ (Algebra.isIntegral_norm ℚ hP)`. Establish `hDK : ((discr K : ℤ) : K) = (u * u + σ (u * u)) * (v * v + σ (v * v)) - (u * v + σ (u * v)) * (v * u + σ (v * u))`. Establish `h` using `congrArg (algebraMap ℚ K) hD`.

Simplify using `only [map_sub, map_mul, htr, map_intCast] at h`. Rewrite using `[h]`. Simplify using `only [map_mul]`. Take `⟨δ, hδ_def⟩ : ∃ δ : K, δ = u * σ v - σ u * v` from `⟨_, rfl⟩`. Establish `hδ2 : δ ^ 2 = ((discr K : ℤ) : K)`.

Rewrite using `[hDK, hδ_def]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hα' : (α : K) = u * σ v + σ u * v`. Establish `h` using `htr (u * σ v)`.

Rewrite `h` using `[← hα, map_intCast, map_mul, hσσ]`. Conclude with `h`. Establish `hβ' : (β : K) = u * σ v * (σ u * v)`. Establish `h` using `hnm (u * σ v)`. Rewrite `h` using `[← hβ, map_intCast, map_mul, hσσ]`.

Conclude with `h`. Establish `hDK2 : ((discr K : ℤ) : K) = (α : K) ^ 2 - 4 * (β : K)`. Rewrite using `[← hδ2, hα', hβ', hδ_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hDZ : discr K = α ^ 2 - 4 * β` using `by exact_mod_cast hDK2`.

Establish `hmod : discr K % 4 = 0 ∨ discr K % 4 = 1`. Rewrite using `[hDZ]`. Break down `Int.even_or_odd α with ⟨k, hk⟩ | ⟨k, hk⟩` into its components or cases. Use `left`. Establish `h' : α ^ 2 - 4 * β = 4 * (k * k - β)` using `by rw [hk]; ring`.

Rewrite using `[h']`. Conclude with `Int.mul_emod_right 4 _`. Use `right`. Establish `h' : α ^ 2 - 4 * β = 4 * (k * k + k - β) + 1` using `by rw [hk]; ring`. Rewrite using `[h']`.

Generalize the expression as in `k * k + k - β = X`. Use linear arithmetic over natural numbers and integers. Establish `hσδ : σ δ = -δ`. Rewrite using `[hδ_def, map_sub, map_mul, map_mul, hσσ, hσσ]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨hmod, δ, hδ2, fun x => ⟨Algebra.trace ℚ K x, Algebra.trace ℚ K (x * δ), ?_⟩⟩` and prove the remaining obligations. Establish `h1 : ((Algebra.trace ℚ K x : ℚ) : K) = x + σ x` using `(eq_ratCast (algebraMap ℚ K) _).symm.trans (htr x)`. Establish `h2 : ((Algebra.trace ℚ K (x * δ) : ℚ) : K) = x * δ + σ x * -δ`. Rewrite using `[← eq_ratCast (algebraMap ℚ K), htr, map_mul, hσδ]`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    (discr K % 4 = 0 ∨ discr K % 4 = 1) ∧ ∃ δ : K, δ ^ 2 = (discr K : K) ∧
      ∀ x : K, ∃ a b : ℚ, 2 * x * δ = (a : K) * δ + (b : K) := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank ℚ K).trans hK
  obtain ⟨σ, hσ1⟩ : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hcon a, hcon b])
    omega
  have hall : ∀ τ : K ≃ₐ[ℚ] K, τ = 1 ∨ τ = σ := by
    intro τ
    by_contra hcon
    push_neg at hcon
    have h3 : ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K)).card = 3 :=
      Finset.card_eq_three.mpr ⟨1, σ, τ, hσ1.symm, hcon.1.symm, hcon.2.symm, rfl⟩
    have h4 := Finset.card_le_univ ({1, σ, τ} : Finset (K ≃ₐ[ℚ] K))
    omega
  have hσσ : ∀ x : K, σ (σ x) = x := by
    have hsq : σ * σ = 1 := by
      rcases hall (σ * σ) with h | h
      · exact h
      · exfalso
        exact hσ1 (mul_left_cancel (h.trans (mul_one σ).symm))
    intro x
    rw [← AlgEquiv.mul_apply, hsq, AlgEquiv.one_apply]
  have hother : ∀ τ : K ≃ₐ[ℚ] K, ¬ (τ ≠ 1 ∧ τ ≠ σ) := by
    intro τ hτ
    rcases hall τ with h | h
    · exact hτ.1 h
    · exact hτ.2 h
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 σ (Ne.symm hσ1)]
    · rw [AlgEquiv.one_apply]
    · intro τ hτ
      exact absurd hτ (hother τ)
  have hnm : ∀ x : K, algebraMap ℚ K (Algebra.norm ℚ x) = x * σ x := by
    intro x
    rw [Algebra.norm_eq_prod_automorphisms, Fintype.prod_eq_mul 1 σ (Ne.symm hσ1)]
    · rw [AlgEquiv.one_apply]
    · intro τ hτ
      exact absurd hτ (hother τ)
  have hcardι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis (integralBasis K), hK]
  let e := Fintype.equivFinOfCardEq hcardι
  obtain ⟨u, hu_def⟩ : ∃ u, u = integralBasis K (e.symm 0) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = integralBasis K (e.symm 1) := ⟨_, rfl⟩
  have hD : ((discr K : ℤ) : ℚ) = Algebra.trace ℚ K (u * u) * Algebra.trace ℚ K (v * v) -
      Algebra.trace ℚ K (u * v) * Algebra.trace ℚ K (v * u) := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply, hu_def, hv_def]
  have hu : IsIntegral ℤ u := by
    rw [hu_def, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hv : IsIntegral ℤ v := by
    rw [hv_def, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hintZ : ∀ q : ℚ, IsIntegral ℤ q → ∃ r : ℤ, (r : ℚ) = q := by
    intro q hq
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
    exact ⟨r, by simpa using hr⟩
  have hP : IsIntegral ℤ (u * σ v) := hu.mul (map_isIntegral_int σ hv)
  obtain ⟨α, hα⟩ := hintZ _ (Algebra.isIntegral_trace (L := ℚ) hP)
  obtain ⟨β, hβ⟩ := hintZ _ (Algebra.isIntegral_norm ℚ hP)
  have hDK : ((discr K : ℤ) : K) = (u * u + σ (u * u)) * (v * v + σ (v * v)) -
      (u * v + σ (u * v)) * (v * u + σ (v * u)) := by
    have h := congrArg (algebraMap ℚ K) hD
    simp only [map_sub, map_mul, htr, map_intCast] at h
    rw [h]
    simp only [map_mul]
  obtain ⟨δ, hδ_def⟩ : ∃ δ : K, δ = u * σ v - σ u * v := ⟨_, rfl⟩
  have hδ2 : δ ^ 2 = ((discr K : ℤ) : K) := by
    rw [hDK, hδ_def]
    simp only [map_mul]
    ring
  have hα' : (α : K) = u * σ v + σ u * v := by
    have h := htr (u * σ v)
    rw [← hα, map_intCast, map_mul, hσσ] at h
    exact h
  have hβ' : (β : K) = u * σ v * (σ u * v) := by
    have h := hnm (u * σ v)
    rw [← hβ, map_intCast, map_mul, hσσ] at h
    exact h
  have hDK2 : ((discr K : ℤ) : K) = (α : K) ^ 2 - 4 * (β : K) := by
    rw [← hδ2, hα', hβ', hδ_def]
    ring
  have hDZ : discr K = α ^ 2 - 4 * β := by exact_mod_cast hDK2
  have hmod : discr K % 4 = 0 ∨ discr K % 4 = 1 := by
    rw [hDZ]
    rcases Int.even_or_odd α with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      have h' : α ^ 2 - 4 * β = 4 * (k * k - β) := by rw [hk]; ring
      rw [h']
      exact Int.mul_emod_right 4 _
    · right
      have h' : α ^ 2 - 4 * β = 4 * (k * k + k - β) + 1 := by rw [hk]; ring
      rw [h']
      generalize k * k + k - β = X
      omega
  have hσδ : σ δ = -δ := by
    rw [hδ_def, map_sub, map_mul, map_mul, hσσ, hσσ]
    ring
  refine ⟨hmod, δ, hδ2, fun x => ⟨Algebra.trace ℚ K x, Algebra.trace ℚ K (x * δ), ?_⟩⟩
  have h1 : ((Algebra.trace ℚ K x : ℚ) : K) = x + σ x :=
    (eq_ratCast (algebraMap ℚ K) _).symm.trans (htr x)
  have h2 : ((Algebra.trace ℚ K (x * δ) : ℚ) : K) = x * δ + σ x * -δ := by
    rw [← eq_ratCast (algebraMap ℚ K), htr, map_mul, hσδ]
  rw [h1, h2]
  ring

/- English proof (translation)
Establish `key : ∀ t ∈ rootsOfUnity N Ω, (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (t : Ω) = (t : Ω) ^ (1 : ZMod N).val`. Introduce `t ht`. Establish `htN : (t : Ω) ^ N = 1`. Rewrite `ht` using `[mem_rootsOfUnity]`. Rewrite using `[← Units.val_pow_eq_pow_val, ht, Units.val_one]`.

Express the relevant statement in the definitionally equal form `s (t : Ω) = _`. Rewrite using `[h _ htN, ZMod.val_one_eq_one_mod]`. Break down `Nat.lt_or_ge 1 N with hN | hN` into its components or cases. Rewrite using `[Nat.mod_eq_of_lt hN, pow_one]`. Establish `hN1 : N = 1`.

Use `NeZero.ne N` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `htN`, the goal using `[hN1]`. Rewrite using `[Nat.mod_self, pow_zero]`. Simplify using `using htN`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`. Conclude with `(modularCyclotomicCharacter.unique Ω (Chr.card_roots ℚ Ω N) _ key).symm`.
-/
private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {N : ℕ} [NeZero N] (s : G ℚ Ω)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  have key : ∀ t ∈ rootsOfUnity N Ω,
      (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (t : Ω) = (t : Ω) ^ (1 : ZMod N).val := by
    intro t ht
    have htN : (t : Ω) ^ N = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    change s (t : Ω) = _
    rw [h _ htN, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 N with hN | hN
    · rw [Nat.mod_eq_of_lt hN, pow_one]
    · have hN1 : N = 1 := by
        have := NeZero.ne N
        omega
      rw [hN1] at htN ⊢
      rw [Nat.mod_self, pow_zero]
      simpa using htN
  apply Units.ext
  rw [Units.val_one]
  exact (modularCyclotomicCharacter.unique Ω (Chr.card_roots ℚ Ω N) _ key).symm

end UpperTheory.V.U3.EtaMu

open UpperTheory.V.U3.EtaMu in
/- English proof (translation)
Introduce `Ω _ _ _ K _ _ _ l _ c N _ e ψ D`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hK` using `D.gd.quad`. Take `⟨hd4, δ, hδ, hspan⟩` from `sub_smul_mul_sub_smul_eq_zero_of_quadratic hK`. Establish `hd0 : discr K ≠ 0` using `discr_ne_zero K`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `hmem : s ∈ galOf ℚ K Ω`. Rewrite using `[mem_galOf]`. Establish `hfx : Fx (s : Ω →+* Ω) (discr K)` using `fx_disc hd0 hd4 (fun ζ hζ => by simpa using hs ζ hζ)`.

Establish `hδΩ : (algebraMap K Ω δ) ^ 2 = ((discr K : ℤ) : Ω)`. Rewrite using `[← map_pow, hδ, map_intCast]`. Establish `hsδ : s (algebraMap K Ω δ) = algebraMap K Ω δ` using `by simpa using hfx _ hδΩ`. Establish `hδne : algebraMap K Ω δ ≠ 0`. Introduce `h0`.

Rewrite `hδΩ` using `[h0]`. Establish `h00 : ((discr K : ℤ) : Ω) = 0` using `by rw [← hδΩ]; ring`. Conclude with `hd0 (by exact_mod_cast h00)`. Introduce `x`. Take `⟨a, b, hab⟩` from `hspan x`.

Establish `e1` using `congrArg (algebraMap K Ω) hab`. Simplify using `only [map_mul, map_add, map_ratCast, map_ofNat] at e1`. Establish `e2` using `congrArg s e1`. Simplify using `only [map_mul, map_add, map_ratCast, map_ofNat, hsδ] at e2`. Establish `hz : (s (algebraMap K Ω x) - algebraMap K Ω x) * (2 * algebraMap K Ω δ) = 0`.

Take the linear combination `e2 - e1`. Break down `mul_eq_zero.mp hz with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. It suffices to derive a contradiction. Conclude with `hδne (by linear_combination (1 / 2 : Ω) * h)`.

Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`. Conclude with `hmem`. Conclude with `Int.natAbs_pos.mpr hd0`. Introduce `s hs`. Simplify using `only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]`.

Introduce `s hs`. Simplify using `only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]`.
-/
theorem UpperTheory.V.U3.eta_killsMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Af.KillsMu (discr K).natAbs D.η ∧ 1 ≤ (discr K).natAbs ∧ Af.KillsMu N (Chr.dirG ℚ Ω ψ) ∧ Af.KillsMu N (Chr.dirG ℚ Ω (comp l ψ)) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hK := D.gd.quad
  obtain ⟨hd4, δ, hδ, hspan⟩ := sub_smul_mul_sub_smul_eq_zero_of_quadratic hK
  have hd0 : discr K ≠ 0 := discr_ne_zero K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    have hmem : s ∈ galOf ℚ K Ω := by
      rw [mem_galOf]
      have hfx : Fx (s : Ω →+* Ω) (discr K) := fx_disc hd0 hd4 (fun ζ hζ => by simpa using hs ζ hζ)
      have hδΩ : (algebraMap K Ω δ) ^ 2 = ((discr K : ℤ) : Ω) := by
        rw [← map_pow, hδ, map_intCast]
      have hsδ : s (algebraMap K Ω δ) = algebraMap K Ω δ := by simpa using hfx _ hδΩ
      have hδne : algebraMap K Ω δ ≠ 0 := by
        intro h0
        rw [h0] at hδΩ
        have h00 : ((discr K : ℤ) : Ω) = 0 := by rw [← hδΩ]; ring
        exact hd0 (by exact_mod_cast h00)
      intro x
      obtain ⟨a, b, hab⟩ := hspan x
      have e1 := congrArg (algebraMap K Ω) hab
      simp only [map_mul, map_add, map_ratCast, map_ofNat] at e1
      have e2 := congrArg s e1
      simp only [map_mul, map_add, map_ratCast, map_ofNat, hsδ] at e2
      have hz : (s (algebraMap K Ω x) - algebraMap K Ω x) * (2 * algebraMap K Ω δ) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exfalso
        exact hδne (by linear_combination (1 / 2 : Ω) * h)
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact hmem
  · exact Int.natAbs_pos.mpr hd0
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
