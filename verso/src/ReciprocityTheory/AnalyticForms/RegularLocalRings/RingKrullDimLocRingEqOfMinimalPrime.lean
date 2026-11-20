import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {n : ℕ}

/- English proof (translation)
The claim follows from `RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)`.
-/
theorem ptIdeal_isMaximal (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)

/- English proof (translation)
Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot => simp at hb`. Consider the case `coe y`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => rw [← h] at hb`.

Simplify using `at hb`. Consider the case `coe x`. Rewrite `h` using `[← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj]`. Rewrite `hb` using `[← WithBot.coe_add]`. Establish `hc : c ≠ ⊤`.

Introduce and unpack `rfl`. Rewrite `hb` using `[add_top]`. Rewrite `hb` using `[← WithBot.coe_natCast, WithBot.coe_inj]`. Conclude with `ENat.top_ne_natCast N hb`. Conclude with `congrArg _ (WithTop.add_right_cancel hc h)`.
-/
private theorem withBot_add_right_cancel {a b : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h : a + (c : WithBot ℕ∞) = b + c) (hb : b + (c : WithBot ℕ∞) = N) : a = b := by
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe y =>
    induction a using WithBot.recBotCoe with
    | bot => rw [← h] at hb; simp at hb
    | coe x =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      rw [← WithBot.coe_add] at hb
      have hc : c ≠ ⊤ := by
        rintro rfl
        rw [add_top] at hb
        rw [← WithBot.coe_natCast, WithBot.coe_inj] at hb
        exact ENat.top_ne_natCast N hb
      exact congrArg _ (WithTop.add_right_cancel hc h)

/- English proof (translation)
Use `set A := MvPolynomial (Fin n) ℂ`. Use `set P := ptIdeal p`. Use `set S := locPt p`. Use `set I : Ideal S := Ideal.map (algebraMap A S) K with hI`. Establish `: IsDomain (S ⧸ I)` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _`.

Establish `hIp : I.IsPrime` using `(Ideal.Quotient.isDomain_iff_prime I).mp inferInstance`. Use `set 𝔮 : Ideal A := I.under A with h𝔮`. Establish `h𝔮p : 𝔮.IsPrime` using `Ideal.IsPrime.under A I`. Establish `hdisj : Disjoint (P.primeCompl : Set A) 𝔮` using `((IsLocalization.isPrime_iff_isPrime_disjoint P.primeCompl S I).mp hIp).2`. Establish `h𝔮P : 𝔮 ≤ P`.

Introduce `x hx`. Assume the negation of the conclusion as `hxP`. Conclude with `Set.disjoint_left.mp hdisj (show x ∈ (P.primeCompl : Set A) from hxP) hx`. Establish `hK𝔮 : K ≤ 𝔮` using `fun x hx => Ideal.mem_map_of_mem _ hx`. Establish `key : ∀ Q : Ideal A, Q.IsPrime → K ≤ Q → Q ≤ P → 𝔮 ≤ Q`.

Introduce `Q hQ hKQ hQP`. Establish `hd : Disjoint (P.primeCompl : Set A) Q`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxQ`. Conclude with `hx (hQP hxQ)`.

Establish `hmap : I ≤ Ideal.map (algebraMap A S) Q` using `Ideal.map_mono hKQ`. Combine the equalities or inequalities in the displayed calculation. Establish `hmin : 𝔮 ∈ K.minimalPrimes` using `⟨⟨h𝔮p, hK𝔮⟩, fun Q ⟨hQ, hKQ⟩ hQ𝔮 => key Q hQ hKQ (hQ𝔮.trans h𝔮P)⟩`. Use `⟨𝔮, hmin, h𝔮P, ?_, ?_⟩` and prove the remaining obligations. Introduce `𝔮' h' h'P`.

Conclude with `le_antisymm (h'.2 ⟨h𝔮p, hK𝔮⟩ (key 𝔮' h'.1.1 h'.1.2 h'P)) (key 𝔮' h'.1.1 h'.1.2 h'P)`. Use `set 𝔪 : Ideal (A ⧸ 𝔮) := P.map (Ideal.Quotient.mk 𝔮) with h𝔪`. Establish `hmem : ∀ a : A, Ideal.Quotient.mk 𝔮 a ∈ 𝔪 ↔ a ∈ P` using `fun a => Ideal.mem_quotient_iff_mem h𝔮P`. Establish `hPmax : P.IsMaximal` using `ptIdeal_isMaximal p`. Establish `h𝔪max : 𝔪.IsMaximal`.

Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective hPmax with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : Ideal.Quotient.mk 𝔮 1 ∈ 𝔪` using `by rw [h𝔪, h]; exact Submodule.mem_top`. Conclude with `hPmax.ne_top ((Ideal.eq_top_iff_one (I := P)).mpr ((hmem 1).mp h1))`. Conclude with `h`.

Set `f : A ⧸ 𝔮 →+* S ⧸ I` to `Ideal.quotientMap I (algebraMap A S) le_rfl`. Use `letI : Algebra (A ⧸ 𝔮) (S ⧸ I) := f.toAlgebra`. Establish `hf : ∀ a : A, algebraMap (A ⧸ 𝔮) (S ⧸ I) (Ideal.Quotient.mk 𝔮 a) = Ideal.Quotient.mk I (algebraMap A S a)` using `fun a => Ideal.quotientMap_mk`. Establish `hloc : IsLocalization.AtPrime (S ⧸ I) 𝔪` using `by show IsLocalization 𝔪.primeCompl (S ⧸ I)`. Rewrite using `[isLocalization_iff]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `ha : a ∈ P.primeCompl` using `fun h => hy ((hmem a).mpr h)`. Rewrite using `[hf]`.

Conclude with `(IsLocalization.map_units S (⟨a, ha⟩ : P.primeCompl)).map _`. Introduce `z`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl s`. Establish `ht : Ideal.Quotient.mk 𝔮 (t : A) ∈ 𝔪.primeCompl` using `fun h => t.2 ((hmem _).mp h)`.

Use `⟨⟨Ideal.Quotient.mk 𝔮 a, ⟨_, ht⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hf, ← map_mul]`. Rewrite using `[IsLocalization.mk'_spec]`. Introduce `x y hxy`. Conclude with `⟨1, by rw [Ideal.quotientMap_injective hxy]⟩`.

Establish `hdim : ringKrullDim (S ⧸ I) = 𝔪.height` using `IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (S ⧸ I)`. Establish `hsum` using `ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 𝔪`. Use `show ringKrullDim (S ⧸ I) + _ = _`. Rewrite using `[hdim, ← WithBot.coe_add, add_comm, hsum]`. Both sides reduce to the same expression.
-/
theorem regular_point_unique_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsRegularLocalRing (locRing K p)] :
    ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧
      (∀ 𝔮' ∈ K.minimalPrimes, 𝔮' ≤ ptIdeal p → 𝔮' = 𝔮) ∧
      ringKrullDim (locRing K p) + (𝔮.height : WithBot ℕ∞) = n := by
  set A := MvPolynomial (Fin n) ℂ
  set P := ptIdeal p
  set S := locPt p
  set I : Ideal S := Ideal.map (algebraMap A S) K with hI
  have : IsDomain (S ⧸ I) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  have hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  set 𝔮 : Ideal A := I.under A with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under A I
  have hdisj : Disjoint (P.primeCompl : Set A) 𝔮 :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint P.primeCompl S I).mp hIp).2
  have h𝔮P : 𝔮 ≤ P := by
    intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hdisj (show x ∈ (P.primeCompl : Set A) from hxP) hx
  have hK𝔮 : K ≤ 𝔮 := fun x hx => Ideal.mem_map_of_mem _ hx

  have key : ∀ Q : Ideal A, Q.IsPrime → K ≤ Q → Q ≤ P → 𝔮 ≤ Q := by
    intro Q hQ hKQ hQP
    have hd : Disjoint (P.primeCompl : Set A) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQP hxQ)
    have hmap : I ≤ Ideal.map (algebraMap A S) Q := Ideal.map_mono hKQ
    calc 𝔮 ≤ (Ideal.map (algebraMap A S) Q).under A := Ideal.comap_mono hmap
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl S hQ hd
  have hmin : 𝔮 ∈ K.minimalPrimes :=
    ⟨⟨h𝔮p, hK𝔮⟩, fun Q ⟨hQ, hKQ⟩ hQ𝔮 => key Q hQ hKQ (hQ𝔮.trans h𝔮P)⟩
  refine ⟨𝔮, hmin, h𝔮P, ?_, ?_⟩
  · intro 𝔮' h' h'P
    exact le_antisymm (h'.2 ⟨h𝔮p, hK𝔮⟩ (key 𝔮' h'.1.1 h'.1.2 h'P)) (key 𝔮' h'.1.1 h'.1.2 h'P)
  ·
    set 𝔪 : Ideal (A ⧸ 𝔮) := P.map (Ideal.Quotient.mk 𝔮) with h𝔪
    have hmem : ∀ a : A, Ideal.Quotient.mk 𝔮 a ∈ 𝔪 ↔ a ∈ P := fun a =>
      Ideal.mem_quotient_iff_mem h𝔮P
    have hPmax : P.IsMaximal := ptIdeal_isMaximal p
    have h𝔪max : 𝔪.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective hPmax with h | h
      · exfalso
        have h1 : Ideal.Quotient.mk 𝔮 1 ∈ 𝔪 := by rw [h𝔪, h]; exact Submodule.mem_top
        exact hPmax.ne_top ((Ideal.eq_top_iff_one (I := P)).mpr ((hmem 1).mp h1))
      · exact h
    let f : A ⧸ 𝔮 →+* S ⧸ I := Ideal.quotientMap I (algebraMap A S) le_rfl
    letI : Algebra (A ⧸ 𝔮) (S ⧸ I) := f.toAlgebra
    have hf : ∀ a : A, algebraMap (A ⧸ 𝔮) (S ⧸ I) (Ideal.Quotient.mk 𝔮 a) =
        Ideal.Quotient.mk I (algebraMap A S a) := fun a => Ideal.quotientMap_mk
    have hloc : IsLocalization.AtPrime (S ⧸ I) 𝔪 := by
      show IsLocalization 𝔪.primeCompl (S ⧸ I)
      rw [isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        have ha : a ∈ P.primeCompl := fun h => hy ((hmem a).mpr h)
        rw [hf]
        exact (IsLocalization.map_units S (⟨a, ha⟩ : P.primeCompl)).map _
      · intro z
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
        have ht : Ideal.Quotient.mk 𝔮 (t : A) ∈ 𝔪.primeCompl := fun h => t.2 ((hmem _).mp h)
        refine ⟨⟨Ideal.Quotient.mk 𝔮 a, ⟨_, ht⟩⟩, ?_⟩
        simp only [hf, ← map_mul]
        rw [IsLocalization.mk'_spec]
      · intro x y hxy
        exact ⟨1, by rw [Ideal.quotientMap_injective hxy]⟩
    have hdim : ringKrullDim (S ⧸ I) = 𝔪.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (S ⧸ I)
    have hsum := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 𝔪
    show ringKrullDim (S ⧸ I) + _ = _
    rw [hdim, ← WithBot.coe_add, add_comm, hsum]
    rfl

/- English proof (translation)
Take `⟨q1, -, -, hu1, hd1⟩` from `regular_point_unique_minimalPrime K p`. Take `⟨q2, -, -, hu2, hd2⟩` from `regular_point_unique_minimalPrime K p'`. Take `rfl` from `hu1 𝔮 h𝔮 hp`. Take `rfl` from `hu2 𝔮 h𝔮 hp'`. Rewrite `hd1` using `[← hd2]`.

Conclude with `withBot_add_right_cancel hd1 hd2`.
-/
theorem ringKrullDim_locRing_eq_of_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p p' : Fin n → ℂ) [IsRegularLocalRing (locRing K p)] [IsRegularLocalRing (locRing K p')]
    (𝔮 : Ideal (MvPolynomial (Fin n) ℂ)) (h𝔮 : 𝔮 ∈ K.minimalPrimes)
    (hp : 𝔮 ≤ ptIdeal p) (hp' : 𝔮 ≤ ptIdeal p') :
    ringKrullDim (locRing K p) = ringKrullDim (locRing K p') := by
  obtain ⟨q1, -, -, hu1, hd1⟩ := regular_point_unique_minimalPrime K p
  obtain ⟨q2, -, -, hu2, hd2⟩ := regular_point_unique_minimalPrime K p'
  obtain rfl := hu1 𝔮 h𝔮 hp
  obtain rfl := hu2 𝔮 h𝔮 hp'
  rw [← hd2] at hd1
  exact withBot_add_right_cancel hd1 hd2

end ReciprocityTheory.AnForm.R
