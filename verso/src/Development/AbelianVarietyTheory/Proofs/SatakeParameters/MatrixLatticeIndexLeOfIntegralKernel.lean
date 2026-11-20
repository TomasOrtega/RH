import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Conclude with `⟨0, by simp [hz]⟩`. Establish `hv : Valued.v z ≠ 0` using `(Valuation.ne_zero_iff _).2 hz`. Take `⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m` from `⟨_, (WithZero.exp_log hv).symm⟩`. Use `⟨m.toNat, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hϖ, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]`. Use `Int.self_le_toNat m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_pow_mul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (z : L) :
    ∃ n : ℕ, Valued.v (ϖ ^ n * z) ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hv).symm⟩
  refine ⟨m.toNat, ?_⟩
  rw [map_mul, map_pow, hϖ, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]
  have := Int.self_le_toNat m
  omega

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Rewrite using `[pow_add, mul_comm (ϖ ^ n), mul_assoc, map_mul, map_pow]`. Conclude with `mul_le_one' (pow_le_one' hϖ k) h`.
-/
theorem pow_mul_int_mono {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) {z : L} {n m : ℕ} (hnm : n ≤ m)
    (h : Valued.v (ϖ ^ n * z) ≤ 1) : Valued.v (ϖ ^ m * z) ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm (ϖ ^ n), mul_assoc, map_mul, map_pow]
  exact mul_le_one' (pow_le_one' hϖ k) h

/- English proof (translation)
Use `choose n hn using fun p : Fin a × Fin b => exists_pow_mul_int hϖ (x p.1 p.2)`. Establish `hϖ1 : Valued.v ϖ ≤ 1` using `by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega`. Use `⟨∑ p, n p, fun i j => pow_mul_int_mono hϖ1 ?_ (hn (i, j))⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))`.
-/
theorem exists_pow_smul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) : ∃ K : ℕ, ∀ i j, Valued.v (ϖ ^ K * x i j) ≤ 1 := by
  choose n hn using fun p : Fin a × Fin b => exists_pow_mul_int hϖ (x p.1 p.2)
  have hϖ1 : Valued.v ϖ ≤ 1 := by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  refine ⟨∑ p, n p, fun i j => pow_mul_int_mono hϖ1 ?_ (hn (i, j))⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))

/- English proof (translation)
Take `⟨-, -, -, hϖ, -, h2q, hc⟩` from `hU`. Use `set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV`. Establish `hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`. Establish `hϖ1 : V ϖ ≤ 1` using `by rw [hV, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega`. Establish `hc' : Nat.card (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) = q ^ 2` using `hc`.

Use `haveI : Finite (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) := Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ (by omega))`. Set `ϖO : V.valuationSubring` to `⟨ϖ, hϖ1⟩`. Establish `hmax : IsLocalRing.maximalIdeal V.valuationSubring ≤ Ideal.span {ϖO}`. Introduce `z hz`. Rewrite `hz` using `[Valuation.mem_maximalIdeal_iff]`.

Rewrite using `[Ideal.mem_span_singleton']`. Distinguish the cases in `hz0 : (z : L) = 0`. Conclude with `⟨0, by ext; simp [hz0]⟩`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `e`.

Rewrite `hϖ'` using `[e, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ'`. Establish `hz' : Valued.v (z : L) < 1` using `hz`. Establish `hle : Valued.v (z : L) ≤ Valued.v ϖ`. Establish `hv : Valued.v (z : L) ≠ 0` using `(Valuation.ne_zero_iff _).2 hz0`.

Rewrite using `[hϖ', ← WithZero.exp_log hv, WithZero.exp_le_exp]`. Rewrite `hz'` using `[← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hq1 : Valued.v ((z : L) / ϖ) ≤ 1`. Rewrite using `[map_div₀, div_le_one₀ (by rw [hϖ']; exact WithZero.exp_pos)]`.

Conclude with `hle`. Use `⟨⟨(z : L) / ϖ, hq1⟩, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[ϖO, div_mul_cancel₀ _ hϖ0]`. Use `haveI : Finite (V.valuationSubring ⧸ Ideal.span {ϖO}) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hmax)`.

Take `⟨K, hK⟩` from `exists_pow_smul_int hϖ' x`. Use `haveI hfinK : Finite (V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) := Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) K`. Set `g : (Fin b → V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) → (Fin a → L) ⧸ intVec L a` to `fun c => QuotientAddGroup.mk (Matrix.mulVec x fun j => (((c j).out : V.valuationSubring) : L))`. Use `(Set.finite_range g).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`.

Establish `hu : ∀ j, Valued.v ((u : Fin b → L) j) ≤ 1` using `(mem_intVec _).1 u.2`. Use `⟨fun j => Ideal.Quotient.mk _ ⟨(u : Fin b → L) j, hu j⟩, ?_⟩` and prove the remaining obligations. Establish `hd : ∀ j, ∃ t : V.valuationSubring, (((Ideal.Quotient.mk (Ideal.span {ϖO} ^ K) ⟨(u : Fin b → L) j, hu j⟩).out : V.valuationSubring) : L) = (u : Fin b → L) j + ϖ ^ K * t`. Introduce `j`. Establish `hm` using `Ideal.Quotient.mk_out (I := Ideal.span {ϖO} ^ K) (⟨(u : Fin b → L) j, hu j⟩ : V.valuationSubring)`.

Establish `hm'` using `Ideal.Quotient.eq.1 hm`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 ((Ideal.span_singleton_pow ϖO K).le hm')`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `congrArg (fun w : V.valuationSubring => (w : L)) ht` as an intermediate fact. Move the coercions through the operations in `at this`.

Simplify using `only [ϖO] at this`. Take the linear combination `-this`. Use `choose t ht using hd`. Use `(QuotientAddGroup.eq.2 ?_).symm` and prove the remaining obligations. Introduce `i`.

Simplify using `only [Pi.add_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, ht, mul_add, Finset.sum_add_distrib, neg_add_cancel_left]`. Use `Subring.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show x i j * (ϖ ^ K * (t j : L)) = (ϖ ^ K * x i j) * (t j : L) by ring]`. Conclude with `Subring.mul_mem _ (hK i j) (t j).2`.
-/
theorem finite_range_latIdx {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) :
    (Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a)).Finite := by
  obtain ⟨-, -, -, hϖ, -, h2q, hc⟩ := hU
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : V ϖ ≤ 1 := by rw [hV, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hc' : Nat.card (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) = q ^ 2 := hc
  haveI : Finite (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ (by omega))
  let ϖO : V.valuationSubring := ⟨ϖ, hϖ1⟩
  have hmax : IsLocalRing.maximalIdeal V.valuationSubring ≤ Ideal.span {ϖO} := by
    intro z hz
    rw [Valuation.mem_maximalIdeal_iff] at hz
    rw [Ideal.mem_span_singleton']
    by_cases hz0 : (z : L) = 0
    · exact ⟨0, by ext; simp [hz0]⟩
    have hϖ0 : ϖ ≠ 0 := by
      intro e; rw [e, map_zero] at hϖ'; exact WithZero.zero_ne_coe hϖ'
    have hz' : Valued.v (z : L) < 1 := hz
    have hle : Valued.v (z : L) ≤ Valued.v ϖ := by
      have hv : Valued.v (z : L) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
      rw [hϖ', ← WithZero.exp_log hv, WithZero.exp_le_exp]
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz'
      omega
    have hq1 : Valued.v ((z : L) / ϖ) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (by rw [hϖ']; exact WithZero.exp_pos)]
      exact hle
    refine ⟨⟨(z : L) / ϖ, hq1⟩, ?_⟩
    ext
    simp [ϖO, div_mul_cancel₀ _ hϖ0]
  haveI : Finite (V.valuationSubring ⧸ Ideal.span {ϖO}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hmax)
  obtain ⟨K, hK⟩ := exists_pow_smul_int hϖ' x
  haveI hfinK : Finite (V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) :=
    Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) K
  let g : (Fin b → V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) → (Fin a → L) ⧸ intVec L a :=
    fun c => QuotientAddGroup.mk (Matrix.mulVec x fun j => (((c j).out : V.valuationSubring) : L))
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨u, rfl⟩
  have hu : ∀ j, Valued.v ((u : Fin b → L) j) ≤ 1 := (mem_intVec _).1 u.2
  refine ⟨fun j => Ideal.Quotient.mk _ ⟨(u : Fin b → L) j, hu j⟩, ?_⟩
  have hd : ∀ j, ∃ t : V.valuationSubring,
      (((Ideal.Quotient.mk (Ideal.span {ϖO} ^ K) ⟨(u : Fin b → L) j, hu j⟩).out : V.valuationSubring) : L) =
        (u : Fin b → L) j + ϖ ^ K * t := by
    intro j
    have hm := Ideal.Quotient.mk_out (I := Ideal.span {ϖO} ^ K)
      (⟨(u : Fin b → L) j, hu j⟩ : V.valuationSubring)
    have hm' := Ideal.Quotient.eq.1 hm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((Ideal.span_singleton_pow ϖO K).le hm')
    refine ⟨t, ?_⟩
    have := congrArg (fun w : V.valuationSubring => (w : L)) ht
    push_cast at this
    simp only [ϖO] at this
    linear_combination -this
  choose t ht using hd
  refine (QuotientAddGroup.eq.2 ?_).symm
  intro i
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, ht, mul_add, Finset.sum_add_distrib,
    neg_add_cancel_left]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [show x i j * (ϖ ^ K * (t j : L)) = (ϖ ^ K * x i j) * (t j : L) by ring]
  exact Subring.mul_mem _ (hK i j) (t j).2

/- English proof (translation)
Introduce `L _ _ ϖ σ q a b x y hU hN`. Establish `hfin` using `finite_range_latIdx hU x`. Use `set Sx := Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSx`. Use `set Sy := Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec y (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSy`. Set `h : (Fin a → L) ⧸ intVec L a → (Fin a → L) ⧸ intVec L a` to `fun c => if hc : ∃ u : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = c then QuotientAddGroup.mk (Matrix.mulVec y (hc.choose : Fin b → L)) else 0`.

Establish `hsub : Sy ⊆ h '' Sx`. Introduce and unpack `_ ⟨u, rfl⟩`. Use `⟨_, ⟨u, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hc : ∃ u' : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u' : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L))` using `⟨u, rfl⟩`. Simplify using `only [h, dif_pos hc]`.

Establish `he` using `hc.choose_spec`. Use `set u' := hc.choose`. Rewrite `he`, the goal using `[QuotientAddGroup.eq]`. Establish `hd` using `hN ((u : Fin b → L) - (u' : Fin b → L)) (fun i => Subring.sub_mem _ (u.2 i) (u'.2 i)) (fun i => by`. Use `he i` as an intermediate fact.

Rewrite using `[Matrix.mulVec_sub]`. Simplify `this)` using `[neg_add_eq_sub]`. Introduce `i`. Use `hd i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_sub]`.

Simplify `this` using `[neg_add_eq_sub]`. Unfold `latIdx`. Rewrite using `[← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]`. Conclude with `(Set.ncard_le_ncard hsub (hfin.image h)).trans (Set.ncard_image_le hfin)`.
-/
theorem latIdx_le_of_ker : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) →
      ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  intro L _ _ ϖ σ q a b x y hU hN
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSx
  set Sy := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec y (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSy
  let h : (Fin a → L) ⧸ intVec L a → (Fin a → L) ⧸ intVec L a := fun c =>
    if hc : ∃ u : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = c
    then QuotientAddGroup.mk (Matrix.mulVec y (hc.choose : Fin b → L)) else 0
  have hsub : Sy ⊆ h '' Sx := by
    rintro _ ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    have hc : ∃ u' : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u' : Fin b → L)) : (Fin a → L) ⧸ intVec L a) =
        QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) := ⟨u, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he ⊢
    have hd := hN ((u : Fin b → L) - (u' : Fin b → L)) (fun i => Subring.sub_mem _ (u.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  unfold latIdx
  rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (hfin.image h)).trans (Set.ncard_image_le hfin)

end GlobalTheory.Hk3.HoweDuality

end
