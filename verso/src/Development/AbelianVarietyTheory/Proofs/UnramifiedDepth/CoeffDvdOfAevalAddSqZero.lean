import Mathlib
import ReciprocityTheory.DualLattices.FormalChartAtZero
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C r => simp`. Consider the case `add f h hf hh => simp only [map_add, hf, hh]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f j hf`.

Simplify using `only [map_mul, hf, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add, MvPolynomial.pderiv_X, Pi.add_apply]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `only [Pi.single_eq_same, map_one]`. Take the linear combination `(MvPolynomial.aeval a (MvPolynomial.pderiv j f)) * hε`.

Simplify using `only [Pi.single_eq_of_ne hij, map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma polCoef_taylor {R₀ A : Type} [CommRing R₀] [CommRing A] [Algebra R₀ A] {g : ℕ}
    (a : Fin g → A) (i : Fin g) (ε : A) (hε : ε * ε = 0) (G : MvPolynomial (Fin g) R₀) :
    MvPolynomial.aeval (a + Pi.single i ε) G
      = MvPolynomial.aeval a G + MvPolynomial.aeval a (MvPolynomial.pderiv i G) * ε := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add f h hf hh => simp only [map_add, hf, hh]; ring
  | mul_X f j hf =>
    simp only [map_mul, hf, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add,
      MvPolynomial.pderiv_X, Pi.add_apply]
    by_cases hij : j = i
    · subst hij
      simp only [Pi.single_eq_same, map_one]
      linear_combination (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) * hε
    · simp only [Pi.single_eq_of_ne hij, map_zero]
      ring

/- English proof (translation)
Establish `hpS : (p : DualNumber A) = 0`. Rewrite using `[← map_natCast (algebraMap A (DualNumber A)), hpA, map_zero]`. Set `φ : A →ₐ[R₀] DualNumber A` to `IsScalarTower.toAlgHom R₀ A (DualNumber A)`. Set `a : Fin g → DualNumber A` to `fun j => φ (x j)`. Establish `h1` using `H (DualNumber A) hpS a (Pi.single i DualNumber.eps) (fun j => by simp only [a]; rw [← map_pow, hx, map_zero]) (fun j k => by`.

Distinguish the cases in `hj : j = i`. Distinguish the cases in `hk : k = i`. Substitute `hj` using the available equality. Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same, DualNumber.eps_mul_eps]`.

Rewrite using `[Pi.single_eq_of_ne hk, mul_zero]`. Rewrite using `[Pi.single_eq_of_ne hj, zero_mul])`. Rewrite `h1` using `[polCoef_taylor a i _ DualNumber.eps_mul_eps]`. Establish `h2 : MvPolynomial.aeval a (MvPolynomial.pderiv i G) * DualNumber.eps = 0` using `add_eq_left.mp h1`. Establish `h3 : MvPolynomial.aeval a (MvPolynomial.pderiv i G) = φ (MvPolynomial.aeval x (MvPolynomial.pderiv i G))`.

Rewrite using `[MvPolynomial.comp_aeval_apply]`. Rewrite `h2` using `[h3]`. Generalize the expression as in `MvPolynomial.aeval x (MvPolynomial.pderiv i G) = y at h2 ⊢`. Use `congrArg TrivSqZeroExt.snd h2` as an intermediate fact. Simplify `this` using `[φ, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
private lemma polCoef_pderiv {R₀ : Type} [CommRing R₀] (p : ℕ) {g N : ℕ}
    (G : MvPolynomial (Fin g) R₀)
    (H : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S,
      (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G)
    {A : Type} [CommRing A] [Algebra R₀ A] (hpA : (p : A) = 0) (x : Fin g → A)
    (hx : ∀ j, x j ^ N = 0) (i : Fin g) :
    MvPolynomial.aeval x (MvPolynomial.pderiv i G) = 0 := by
  have hpS : (p : DualNumber A) = 0 := by
    rw [← map_natCast (algebraMap A (DualNumber A)), hpA, map_zero]
  let φ : A →ₐ[R₀] DualNumber A := IsScalarTower.toAlgHom R₀ A (DualNumber A)
  let a : Fin g → DualNumber A := fun j => φ (x j)
  have h1 := H (DualNumber A) hpS a (Pi.single i DualNumber.eps)
    (fun j => by simp only [a]; rw [← map_pow, hx, map_zero])
    (fun j k => by
      by_cases hj : j = i
      · by_cases hk : k = i
        · subst hj; subst hk
          rw [Pi.single_eq_same, DualNumber.eps_mul_eps]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
      · rw [Pi.single_eq_of_ne hj, zero_mul])
  rw [polCoef_taylor a i _ DualNumber.eps_mul_eps] at h1
  have h2 : MvPolynomial.aeval a (MvPolynomial.pderiv i G) * DualNumber.eps = 0 :=
    add_eq_left.mp h1
  have h3 : MvPolynomial.aeval a (MvPolynomial.pderiv i G)
      = φ (MvPolynomial.aeval x (MvPolynomial.pderiv i G)) := by
    rw [MvPolynomial.comp_aeval_apply]
  rw [h3] at h2
  generalize MvPolynomial.aeval x (MvPolynomial.pderiv i G) = y at h2 ⊢
  have := congrArg TrivSqZeroExt.snd h2
  simpa [φ, TrivSqZeroExt.algebraMap_eq_inl] using this

/- English proof (translation)
Rewrite `hf` using `[Ideal.mem_span_range_iff_exists_fun]`. Take `⟨c, rfl⟩` from `hf`. Introduce `m hm`. Rewrite using `[MvPolynomial.coeff_sum]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]`. Introduce `h`. Use `h j` as an intermediate fact. Simplify using `only [Finsupp.single_eq_same] at this`. Conclude with `absurd (hm j) (not_lt.mpr this)`.
-/
private lemma polCoef_span {R : Type} [CommRing R] {g N : ℕ} (f : MvPolynomial (Fin g) R)
    (hf : f ∈ Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)) :
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → MvPolynomial.coeff m f = 0 := by
  rw [Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  intro m hm
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h j
  simp only [Finsupp.single_eq_same] at this
  exact absurd (hm j) (not_lt.mpr this)

/- English proof (translation)
Introduce `R₀ _ p hp g N G H m hm ⟨i, hi⟩`. Set `I : Ideal R₀` to `Ideal.span {(p : R₀)}`. Set `R` to `R₀ ⧸ I`. Set `J : Ideal (MvPolynomial (Fin g) R)` to `Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)`. Set `A` to `MvPolynomial (Fin g) R ⧸ J`.

Establish `hpR : (p : R) = 0`. Establish `: (Ideal.Quotient.mk I) (p : R₀) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)`. Simplify using `using this`. Establish `hpA : (p : A) = 0`. Rewrite using `[← map_natCast (algebraMap R A), hpR, map_zero]`.

Set `x : Fin g → A` to `fun j => Ideal.Quotient.mk J (MvPolynomial.X j)`. Establish `hx : ∀ j, x j ^ N = 0` using `fun j => by`. Simplify using `only [x]`. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.

Establish `h4` using `polCoef_pderiv p G H hpA x hx i`. Establish `h5 : ∀ f : MvPolynomial (Fin g) R₀, MvPolynomial.aeval x f = Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R₀ R) f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C]`.

Both sides reduce to the same expression. Consider the case `add f h hf hh => simp only [map_add, hf, hh]`. Consider the case `mul_X f j hf => simp only [map_mul, hf, MvPolynomial.aeval_X, MvPolynomial.map_X, x]`. Rewrite `h4` using `[h5, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hpos : 1 ≤ m i`.

Break down `Nat.eq_zero_or_pos (m i) with h | h` into its components or cases. Conclude with `absurd (h ▸ dvd_zero p) hi`. Conclude with `h`. Establish `h6` using `polCoef_span _ h4 (m - Finsupp.single i 1) (fun j => lt_of_le_of_lt (by simp) (hm j))`. Establish `hle : Finsupp.single i 1 ≤ m` using `Finsupp.single_le_iff.mpr hpos`.

Rewrite `h6` using `[MvPolynomial.coeff_map, MvPolynomial.coeff_pderiv, tsub_add_cancel_of_le hle]`. Establish `h7 : MvPolynomial.coeff m G * (m i : R₀) ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `e : (((m - Finsupp.single i 1 : Fin g →₀ ℕ) i : ℕ) : R₀) + 1 = (m i : R₀)`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub hpos]`.

Simplify using the standard rewrite rules. Rewrite `h6` using `[e]`. Conclude with `h6`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.mp h7`. Establish `hc : IsCoprime (p : R₀) (m i : R₀)` using `Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hi)`.

Take `⟨u, v, huv⟩` from `hc`. Conclude with `⟨u * MvPolynomial.coeff m G + v * s, by`. Take the linear combination `(-MvPolynomial.coeff m G) * huv - v * hs⟩`.
-/
theorem coeff_dvd_of_aeval_add_sq_zero :
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, MvPolynomial.coeff m G = p * r) := by
  intro R₀ _ p hp g N G H m hm ⟨i, hi⟩
  let I : Ideal R₀ := Ideal.span {(p : R₀)}
  let R := R₀ ⧸ I
  let J : Ideal (MvPolynomial (Fin g) R) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)
  let A := MvPolynomial (Fin g) R ⧸ J
  have hpR : (p : R) = 0 := by
    have : (Ideal.Quotient.mk I) (p : R₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simpa using this
  have hpA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap R A), hpR, map_zero]
  let x : Fin g → A := fun j => Ideal.Quotient.mk J (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    simp only [x]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h4 := polCoef_pderiv p G H hpA x hx i
  have h5 : ∀ f : MvPolynomial (Fin g) R₀, MvPolynomial.aeval x f
      = Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R₀ R) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C]; rfl
    | add f h hf hh => simp only [map_add, hf, hh]
    | mul_X f j hf => simp only [map_mul, hf, MvPolynomial.aeval_X, MvPolynomial.map_X, x]
  rw [h5, Ideal.Quotient.eq_zero_iff_mem] at h4
  have hpos : 1 ≤ m i := by
    rcases Nat.eq_zero_or_pos (m i) with h | h
    · exact absurd (h ▸ dvd_zero p) hi
    · exact h
  have h6 := polCoef_span _ h4 (m - Finsupp.single i 1)
    (fun j => lt_of_le_of_lt (by simp) (hm j))
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hpos
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_pderiv, tsub_add_cancel_of_le hle] at h6
  have h7 : MvPolynomial.coeff m G * (m i : R₀) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (((m - Finsupp.single i 1 : Fin g →₀ ℕ) i : ℕ) : R₀) + 1 = (m i : R₀) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub hpos]; simp
    rw [e] at h6
    exact h6
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h7
  have hc : IsCoprime (p : R₀) (m i : R₀) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hi)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨u * MvPolynomial.coeff m G + v * s, by
    linear_combination (-MvPolynomial.coeff m G) * huv - v * hs⟩

end GlobalTheory
