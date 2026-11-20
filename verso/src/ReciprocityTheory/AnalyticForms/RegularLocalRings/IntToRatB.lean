import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def eQ (x : PrimeSpectrum (MvPolynomial σ ℤ)) (h : ChZero x.asIdeal) :
    PrimeSpectrum (MvPolynomial σ ℚ) :=
  ⟨Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal, map_isPrime x.asIdeal h⟩

/- English proof (translation)
Establish `hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal` using `by show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal`. Conclude with `Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)`. Use `show (eQ x hx).asIdeal < (eQ y hy).asIdeal`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `heq`.

Establish `h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap (MvPolynomial.map (Int.castRingHom ℚ)) = (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap (MvPolynomial.map (Int.castRingHom ℚ))` using `congrArg (Ideal.comap _) heq`. Rewrite `h2` using `[comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy]`. Conclude with `(show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2`.
-/
lemma eQ_lt {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by
  have hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal := by
    show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal
    exact Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)
  show (eQ x hx).asIdeal < (eQ y hy).asIdeal
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) =
      (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) := congrArg (Ideal.comap _) heq
  rw [comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy] at h2
  exact (show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2

/- English proof (translation)
Proceed by induction on `s using RelSeries.inductionOn with`. Consider the case `singleton x => intros`. Simplify using the standard rewrite rules. Consider the case `cons t x hx ih`. Introduce `z hz h0`.

Rewrite `hz` using `[RelSeries.head_cons]`. Substitute `hz` using the available equality. Simplify using `only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]`. Distinguish the cases in `h1 : ChZero t.head.asIdeal`. Establish `h2` using `ih t.head rfl h1`.

Establish `h3` using `Order.coheight_add_one_le (eQ_lt h0 h1 hx)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (t.length : ℕ∞) ≤ Order.coheight t.head` using `Order.length_le_coheight_head`. Establish `h3` using `dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1`. Rewrite `h3` using `[ringKrullDim_quotient_eq_coheight, ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)]`.

Establish `h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0)` using `WithBot.coe_le_coe.mp h3`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma length_le_coheight_eQ (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by
  induction s using RelSeries.inductionOn with
  | singleton x => intros; simp
  | cons t x hx ih =>
    intro z hz h0
    rw [RelSeries.head_cons] at hz
    subst hz
    simp only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
    by_cases h1 : ChZero t.head.asIdeal
    · have h2 := ih t.head rfl h1
      have h3 := Order.coheight_add_one_le (eQ_lt h0 h1 hx)
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight (eQ t.head h1) + 1 + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h3 1
    · have h2 : (t.length : ℕ∞) ≤ Order.coheight t.head := Order.length_le_coheight_head
      have h3 := dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1
      rw [ringKrullDim_quotient_eq_coheight,
        ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)] at h3
      have h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0) := WithBot.coe_le_coe.mp h3
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight t.head + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h4 1

/- English proof (translation)
Rewrite using `[isJacobsonRing_iff_prime_eq]`. Introduce `P hP`. Use `le_antisymm ?_ Ideal.le_jacobson` and prove the remaining obligations. Distinguish the cases in `hb : P = ⊥`. Substitute `hb` using the available equality.

Introduce `m hm`. Rewrite `hm` using `[Ideal.mem_jacobson_bot]`. Rewrite using `[Ideal.mem_bot]`. Establish `h1` using `Int.isUnit_iff.mp (hm 1)`. Establish `h2` using `Int.isUnit_iff.mp (hm 2)`.

Use linear arithmetic over natural numbers and integers. Establish `hmax : P.IsMaximal` using `by first`. Consider the case `exact Ideal.IsPrime.isMaximal hP hb`. Consider the case `exact hP.isMaximal hb`. Consider the case `exact Ideal.IsPrime.to_maximal_ideal hb`.

Consider the case `exact Ring.DimensionLEOne.maximalOfPrime hb hP`. Conclude with `sInf_le ⟨le_rfl, hmax⟩`.
-/
private lemma isJacobsonRing_int_regular_local_rings : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases hb : P = ⊥
  · subst hb
    intro m hm
    rw [Ideal.mem_jacobson_bot] at hm
    rw [Ideal.mem_bot]
    have h1 := Int.isUnit_iff.mp (hm 1)
    have h2 := Int.isUnit_iff.mp (hm 2)
    omega
  · have hmax : P.IsMaximal := by
      first
        | exact Ideal.IsPrime.isMaximal hP hb
        | exact hP.isMaximal hb
        | exact Ideal.IsPrime.to_maximal_ideal hb
        | exact Ring.DimensionLEOne.maximalOfPrime hb hP
    exact sInf_le ⟨le_rfl, hmax⟩

/- English proof (translation)
Introduce `hmax`. Use `haveI := hmax`. Use `haveI := isJacobsonRing_int_regular_local_rings`. Use `letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q`. Establish `hint` using `MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective`.

Establish `hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) = algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)` using `RingHom.ext_int _ _`. Use `haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Establish `hx` using `hint x`.

Rewrite `hx` using `[hfe]`. Conclude with `hx`. Establish `hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`.

Rewrite `hm` using `[← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hQ m hm`. Establish `hF : IsField ℤ` using `isField_of_isIntegral_of_isField hinj ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)`. Take `⟨b, hb⟩` from `hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)`. Use linear arithmetic over natural numbers and integers.
-/
private lemma not_isMaximal_of_chZero (Q : Ideal (MvPolynomial σ ℤ)) (hQ : ChZero Q) :
    ¬ Q.IsMaximal := by
  intro hmax
  haveI := hmax
  haveI := isJacobsonRing_int_regular_local_rings
  letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) =
      algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q) := RingHom.ext_int _ _
  haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by
    constructor
    intro x
    have hx := hint x
    rw [hfe] at hx
    exact hx
  have hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hm
    exact hQ m hm
  have hF : IsField ℤ := isField_of_isIntegral_of_isField hinj
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega

/- English proof (translation)
Set `φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ` to `MvPolynomial.map (Int.castRingHom ℚ)`. Set `g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ)` to `fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩`. Establish `hg : StrictMono g`. Introduce `a b hab`. Use `show a.asIdeal.comap φ < b.asIdeal.comap φ`.

Conclude with `comap_strictMono (show a.asIdeal < b.asIdeal from hab)`. Establish `hg0 : g (eQ P hP) = P` using `PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)`. Establish `hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M`. Introduce `L`. Establish `hQ : ChZero (g L).asIdeal` using `chZero_comap L.asIdeal`.

Establish `hnm` using `not_isMaximal_of_chZero (g L).asIdeal hQ`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top`. Use `⟨⟨M, hM.isPrime⟩, ?_⟩` and prove the remaining obligations. Use `show (g L).asIdeal < M`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations.

Introduce `heq`. Apply `hnm` to reduce the goal to its premises. Rewrite using `[heq]`. Conclude with `hM`. Establish `key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) → ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P`.

Introduce `n hn`. Take `⟨p, hph, hpl⟩` from `Order.exists_series_of_le_coheight (eQ P hP) hn`. Take `⟨M, hM⟩` from `hup p.last`. Establish `hlast : (p.map g hg).last < M` using `hM`. Set `q` to `(p.map g hg).snoc M hlast`.

Establish `hqh : q.head = P`. Rewrite using `[RelSeries.head_snoc]`. Use `show g p.head = P`. Rewrite using `[hph]`. Conclude with `hg0`.

Establish `hql : q.length = n + 1`. Rewrite using `[← hpl]`. Both sides reduce to the same expression. Rewrite using `[← hql, ← hqh]`. Conclude with `Order.length_le_coheight_head`.

Break down `eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h` into its components or cases. Establish `htop : Order.coheight P = ⊤`. Assume the negation of the conclusion as `hne`. Establish `h1` using `key (Order.coheight P).toNat (by rw [h]; exact le_top)`. Establish `h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞)`.

Rewrite using `[ENat.coe_toNat hne]`. Conclude with `h1`. Establish `h3` using `(Nat.cast_le (α := ℕ∞)).mp h2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[htop]`.

Conclude with `le_top`. Establish `h1` using `key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])`. Rewrite using `[← ENat.coe_toNat h]`. Conclude with `h1` after adjusting the coercions.
-/
lemma coheight_eQ_add_one_le (P : PrimeSpectrum (MvPolynomial σ ℤ)) (hP : ChZero P.asIdeal) :
    Order.coheight (eQ P hP) + 1 ≤ Order.coheight P := by
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ) :=
    fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩
  have hg : StrictMono g := by
    intro a b hab
    show a.asIdeal.comap φ < b.asIdeal.comap φ
    exact comap_strictMono (show a.asIdeal < b.asIdeal from hab)
  have hg0 : g (eQ P hP) = P := PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)
  have hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M := by
    intro L
    have hQ : ChZero (g L).asIdeal := chZero_comap L.asIdeal
    have hnm := not_isMaximal_of_chZero (g L).asIdeal hQ
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top
    refine ⟨⟨M, hM.isPrime⟩, ?_⟩
    show (g L).asIdeal < M
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnm
    rw [heq]
    exact hM
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P := by
    intro n hn
    obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight (eQ P hP) hn
    obtain ⟨M, hM⟩ := hup p.last
    have hlast : (p.map g hg).last < M := hM
    let q := (p.map g hg).snoc M hlast
    have hqh : q.head = P := by
      rw [RelSeries.head_snoc]
      show g p.head = P
      rw [hph]
      exact hg0
    have hql : q.length = n + 1 := by
      rw [← hpl]
      rfl
    rw [← hql, ← hqh]
    exact Order.length_le_coheight_head
  rcases eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h
  · have htop : Order.coheight P = ⊤ := by
      by_contra hne
      have h1 := key (Order.coheight P).toNat (by rw [h]; exact le_top)
      have h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hne]
        exact h1
      have h3 := (Nat.cast_le (α := ℕ∞)).mp h2
      omega
    rw [htop]
    exact le_top
  · have h1 := key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])
    rw [← ENat.coe_toNat h]
    exact_mod_cast h1

end ReciprocityTheory.AnForm.R.IntegerToRational
