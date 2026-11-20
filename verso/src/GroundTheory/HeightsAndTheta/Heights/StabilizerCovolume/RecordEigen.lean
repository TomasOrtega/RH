import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

structure SmallBlockLattices (L : Type) [Field L] [NumberField L] (Ψ : Type) where

  eig : Ψ → FractionalIdeal (𝓞 L)⁰ L

  record : Ψ → FractionalIdeal (𝓞 L)⁰ L

  ht : Ψ → FractionalIdeal (𝓞 L)⁰ L
  eig_ne : ∀ τ, eig τ ≠ 0
  record_ne : ∀ τ, record τ ≠ 0
  ht_ne : ∀ τ, ht τ ≠ 0

  arch : Ψ → (L →+* ℂ) → ℝ
  arch_pos : ∀ τ σ, 0 < arch τ σ

def lineDeg {L : Type} [Field L] [NumberField L] (𝔞 : FractionalIdeal (𝓞 L)⁰ L) (nrm : (L →+* ℂ) → ℝ) : ℝ :=
  (-Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) - ∑ σ : L →+* ℂ, Real.log (nrm σ)) / Module.finrank ℚ L

def SmallBlockLattices.degree {L : Type} [Field L] [NumberField L] {Ψ : Type} [Fintype Ψ]
    (P : SmallBlockLattices L Ψ) (lat : Ψ → FractionalIdeal (𝓞 L)⁰ L) : ℝ :=
  ∑ τ, lineDeg (lat τ) (P.arch τ)

def primesB (B : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Nat.Prime ∪ bad

def OrderBoundAtPrime {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] {Ψ : Type}
    (ι : Ψ → E →+* L) (j' : ℕ) (S : Finset ℕ) (P : SmallBlockLattices L Ψ) : Prop :=
  ∀ τ, LocalCountBound (P.ht τ * (P.record τ)⁻¹) (extDifferent (ι τ)) S j' j'

def EigenRecordAt {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] {Ψ : Type}
    (ι : Ψ → E →+* L) (j' : ℕ) (P : SmallBlockLattices L Ψ) : Prop :=
  ∀ τ, ∀ 𝔓 : HeightOneSpectrum (𝓞 L),
    |(FractionalIdeal.count L 𝔓 (P.record τ * (P.eig τ)⁻¹) : ℝ)| ≤
      j' * (FractionalIdeal.count L 𝔓 (extDifferent (ι τ) : FractionalIdeal (𝓞 L)⁰ L) : ℝ)

def RecordEigen.Statement : Prop :=
  ∃ C : ℝ, ∀ (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] (Ψ : Type) [Fintype Ψ]
    (ι : Ψ → E →+* L) (j' B : ℕ) (bad : Finset ℕ) (P : SmallBlockLattices L Ψ),
    2 ≤ B → (∀ p ∈ bad, p.Prime) → bad.card ≤ B → EigenRecordAt ι j' P → OrderBoundAtPrime ι j' (primesB B bad) P →
      |P.degree P.record - P.degree P.eig| ≤ Fintype.card Ψ * j' * logRd E ∧
        |P.degree P.ht - P.degree P.record| ≤ C * (Fintype.card Ψ * j') * (Real.log B + logRd E)

/- English proof (translation)
Apply `div_nonneg _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h` using `Int.one_le_abs (NumberField.discr_ne_zero E)`. Conclude with `h` after adjusting the coercions.
-/
theorem logRd_nonneg (E : Type) [Field E] [NumberField E] : 0 ≤ logRd E := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h

/- English proof (translation)
Establish `ha' : (FractionalIdeal.absNorm a : ℝ) ≠ 0`. Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.mpr ha)` after adjusting the coercions. Establish `hb' : (FractionalIdeal.absNorm b : ℝ) ≠ 0`. Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.mpr hb)` after adjusting the coercions. Rewrite using `[map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, Real.log_mul ha' (inv_ne_zero hb'), Real.log_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_absNorm_mul_inv {L : Type} [Field L] [NumberField L] {a b : FractionalIdeal (𝓞 L)⁰ L}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (FractionalIdeal.absNorm (a * b⁻¹) : ℝ) =
      Real.log (FractionalIdeal.absNorm a : ℝ) - Real.log (FractionalIdeal.absNorm b : ℝ) := by
  have ha' : (FractionalIdeal.absNorm a : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr ha)
  have hb' : (FractionalIdeal.absNorm b : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hb)
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, Real.log_mul ha' (inv_ne_zero hb'), Real.log_inv]
  ring

/- English proof (translation)
The claim follows from `|P.degree lat₁ - P.degree lat₂| ≤ Fintype.card Ψ * K := by have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos set x := fun τ => Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ) with hxdef have hτ : ∀ τ, lineDeg (lat₁ τ) (P.arch τ) - lineDeg …`.
-/
theorem abs_degree_sub_le {L : Type} [Field L] [NumberField L] {Ψ : Type} [Fintype Ψ]
    (P : SmallBlockLattices L Ψ) (lat₁ lat₂ : Ψ → FractionalIdeal (𝓞 L)⁰ L) (h₁ : ∀ τ, lat₁ τ ≠ 0)
    (h₂ : ∀ τ, lat₂ τ ≠ 0) (K : ℝ)
    (hx : ∀ τ, |Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ)| ≤ Module.finrank ℚ L * K) :
    |P.degree lat₁ - P.degree lat₂| ≤ Fintype.card Ψ * K := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set x := fun τ => Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ) with hxdef
  have hτ : ∀ τ, lineDeg (lat₁ τ) (P.arch τ) - lineDeg (lat₂ τ) (P.arch τ) = -x τ / Module.finrank ℚ L := by
    intro τ
    rw [lineDeg, lineDeg, hxdef]
    simp only
    rw [log_absNorm_mul_inv (h₁ τ) (h₂ τ)]
    ring
  rw [SmallBlockLattices.degree, SmallBlockLattices.degree, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun τ _ => hτ τ), ← Finset.sum_div, Finset.sum_neg_distrib, abs_div, abs_neg,
    abs_of_pos hd, div_le_iff₀ hd]
  calc |∑ τ, x τ| ≤ ∑ τ, |x τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _τ : Ψ, Module.finrank ℚ L * K := Finset.sum_le_sum fun τ _ => hx τ
    _ = Fintype.card Ψ * K * Module.finrank ℚ L := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/- English proof (translation)
Establish `hnn : ∀ p ∈ (Finset.Icc 1 B).filter Nat.Prime ∩ bad, 0 ≤ Real.log p / ((p : ℝ) - 1)`. Introduce `p hp`. Establish `hp'` using `hbad p (Finset.mem_inter.mp hp).2`. Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp'.two_le`. Conclude with `div_nonneg (Real.log_nonneg (by linarith)) (by linarith)`.

Establish `hA : ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B`. Apply `h5 B hB` to reduce the goal to its premises. Introduce `p hp`. Conclude with `(Finset.mem_filter.mp hp).2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hU` using `Finset.sum_union_inter (s₁ := (Finset.Icc 1 B).filter Nat.Prime) (s₂ := bad) (f := fun p : ℕ => Real.log p / ((p : ℝ) - 1))`. Establish `hI` using `Finset.sum_nonneg hnn`. Establish `hb` using `h5 B hB bad hbad hcard`. Rewrite using `[primesB]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_primesB_le {C : ℝ} (h5 : ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
      ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B)
    {B : ℕ} (hB : 2 ≤ B) {bad : Finset ℕ} (hbad : ∀ p ∈ bad, p.Prime) (hcard : bad.card ≤ B) :
    ∑ p ∈ primesB B bad, Real.log p / ((p : ℝ) - 1) ≤ 2 * C * Real.log B := by
  have hnn : ∀ p ∈ (Finset.Icc 1 B).filter Nat.Prime ∩ bad, 0 ≤ Real.log p / ((p : ℝ) - 1) := by
    intro p hp
    have hp' := hbad p (Finset.mem_inter.mp hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hA : ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B := by
    apply h5 B hB
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · calc ((Finset.Icc 1 B).filter Nat.Prime).card ≤ (Finset.Icc 1 B).card := Finset.card_filter_le _ _
        _ = B := by simp
  have hU := Finset.sum_union_inter (s₁ := (Finset.Icc 1 B).filter Nat.Prime) (s₂ := bad)
    (f := fun p : ℕ => Real.log p / ((p : ℝ) - 1))
  have hI := Finset.sum_nonneg hnn
  have hb := h5 B hB bad hbad hcard
  rw [primesB]
  linarith

/- English proof (translation)
Rewrite using `[extDifferent, Ne, Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`. Introduce `x y h`. Establish `h'` using `congrArg (fun z : 𝓞 L => (z : L)) h`. Simplify using `only [RingOfIntegers.mapRingHom_apply] at h'`.

Conclude with `RingOfIntegers.ext (ι.injective h')`.
-/
theorem extDifferent_ne_bot {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    extDifferent ι ≠ ⊥ := by
  rw [extDifferent, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · intro x y h
    have h' := congrArg (fun z : 𝓞 L => (z : L)) h
    simp only [RingOfIntegers.mapRingHom_apply] at h'
    exact RingOfIntegers.ext (ι.injective h')

def smallBlockTwo {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    SmallBlockLattices L Unit where
  eig _ := ((extDifferent ι : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)
  record _ := 1
  ht _ := (primeFrac L 2)⁻¹
  eig_ne _ := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact extDifferent_ne_bot ι
  record_ne _ := one_ne_zero
  ht_ne _ := inv_ne_zero (primeFrac_ne_zero L Nat.prime_two)
  arch _ _ := 2
  arch_pos _ _ := two_pos

/- English proof (translation)
Introduce `τ 𝔓`. Establish `h0` using `FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)`. Simplify using `only [smallBlockTwo, one_mul]`. Rewrite using `[FractionalIdeal.count_inv, Int.cast_neg, abs_neg, abs_of_nonneg (by exact_mod_cast h0)]`. Conclude with `le_mul_of_one_le_left (by exact_mod_cast h0) (by exact_mod_cast hj)`.
-/
theorem smallBlockTwo_eigenRecord {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') : EigenRecordAt (fun _ => ι) j' (smallBlockTwo ι) := by
  intro τ 𝔓
  have h0 := FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)
  simp only [smallBlockTwo, one_mul]
  rw [FractionalIdeal.count_inv, Int.cast_neg, abs_neg, abs_of_nonneg (by exact_mod_cast h0)]
  exact le_mul_of_one_le_left (by exact_mod_cast h0) (by exact_mod_cast hj)

/- English proof (translation)
Introduce `τ p hp 𝔓 h`. Establish `hD0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (extDifferent ι : FractionalIdeal (𝓞 L)⁰ L)`. Conclude with `FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)` after adjusting the coercions. Establish `hj' : (1 : ℝ) ≤ j'` using `by exact_mod_cast hj`. Simplify using `only [smallBlockTwo, inv_one, mul_one]`.

Rewrite using `[FractionalIdeal.count_inv, Int.cast_neg, abs_neg]`. Distinguish the cases in `hp2 : p = 2`. Substitute `hp2` using the available equality. Rewrite using `[if_pos h2]`. Establish `h0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L 2)`.

Conclude with `FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {((2 : ℕ) : 𝓞 L)})` after adjusting the coercions. Rewrite using `[abs_of_nonneg h0]`. Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[count_primeFrac_of_ne hp Nat.prime_two hp2 𝔓 h]`.

Establish `hpc : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L p)`. Conclude with `FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {(p : 𝓞 L)})` after adjusting the coercions. Establish `hp1 : (0 : ℝ) ≤ (p : ℝ) - 1`. Use `hp.one_lt` as an intermediate fact. Establish `: (1 : ℝ) < p` using `by exact_mod_cast this`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Int.cast_zero, abs_zero]`. Apply `add_nonneg _ (mul_nonneg (by positivity) hD0)` to reduce the goal to its premises. Use `split_ifs`. Conclude with `div_nonneg (mul_nonneg (by positivity) hpc) hp1`.

Conclude with `le_rfl`.
-/
theorem smallBlockTwo_m1Prime {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') {S : Finset ℕ} (h2 : 2 ∈ S) :
    OrderBoundAtPrime (fun _ => ι) j' S (smallBlockTwo ι) := by
  intro τ p hp 𝔓 h
  have hD0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (extDifferent ι : FractionalIdeal (𝓞 L)⁰ L) := by
    exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  simp only [smallBlockTwo, inv_one, mul_one]
  rw [FractionalIdeal.count_inv, Int.cast_neg, abs_neg]
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_pos h2]
    have h0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L 2) := by
      exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {((2 : ℕ) : 𝓞 L)})
    rw [abs_of_nonneg h0]
    norm_num
    nlinarith
  · rw [count_primeFrac_of_ne hp Nat.prime_two hp2 𝔓 h]
    have hpc : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L p) := by
      exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {(p : 𝓞 L)})
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have := hp.one_lt
      have : (1 : ℝ) < p := by exact_mod_cast this
      linarith
    rw [Int.cast_zero, abs_zero]
    apply add_nonneg _ (mul_nonneg (by positivity) hD0)
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) hpc) hp1
    · exact le_rfl

/- English proof (translation)
Rewrite using `[primesB]`. Conclude with `Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hB⟩, Nat.prime_two⟩)`.
-/
theorem two_mem_primesB {B : ℕ} (hB : 2 ≤ B) (bad : Finset ℕ) : 2 ∈ primesB B bad := by
  rw [primesB]
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hB⟩, Nat.prime_two⟩)

/- English proof (translation)
Assemble the required witnesses or components as `⟨le_rfl, by simp, by simp, smallBlockTwo_eigenRecord ι le_rfl, smallBlockTwo_m1Prime ι le_rfl (two_mem_primesB le_rfl ∅)⟩`.
-/
theorem recordEigen_bundle_two {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    2 ≤ 2 ∧ (∀ p ∈ (∅ : Finset ℕ), p.Prime) ∧ (∅ : Finset ℕ).card ≤ 2 ∧
      EigenRecordAt (fun _ => ι) 1 (smallBlockTwo ι) ∧ OrderBoundAtPrime (fun _ => ι) 1 (primesB 2 ∅) (smallBlockTwo ι) :=
  ⟨le_rfl, by simp, by simp, smallBlockTwo_eigenRecord ι le_rfl,
    smallBlockTwo_m1Prime ι le_rfl (two_mem_primesB le_rfl ∅)⟩

/- English proof (translation)
Take `⟨C₅, h5⟩` from `h₁`. Use `⟨max (2 * C₅) 1, ?_⟩` and prove the remaining obligations. Introduce `E L _ _ _ _ Ψ _ ι j' B bad P hB hbad hcard hER hM`. Establish `hd : (0 : ℝ) ≤ Module.finrank ℚ L` using `Nat.cast_nonneg _`. Establish `hj : (0 : ℝ) ≤ j'` using `Nat.cast_nonneg _`.

Establish `hD : ∀ τ, extDifferent (ι τ) ≠ ⊥ ∧ Real.log (Ideal.absNorm (extDifferent (ι τ)) : ℝ) = Module.finrank ℚ L * logRd E` using `fun τ => h₃ E L (ι τ)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Apply `abs_degree_sub_le P P.record P.eig P.record_ne P.eig_ne (j' * logRd E)` to reduce the goal to its premises. Introduce `τ`.

Establish `hloc : LocalCountBound (P.record τ * (P.eig τ)⁻¹) (extDifferent (ι τ)) ∅ 0 j'`. Introduce `p _ 𝔓 _`. Rewrite using `[if_neg (Finset.notMem_empty p), zero_add]`. Conclude with `hER τ 𝔓`. Establish `h` using `h₂ L _ _ ∅ 0 j' (mul_ne_zero (P.record_ne τ) (inv_ne_zero (P.eig_ne τ))) (hD τ).1 le_rfl hj hloc`.

Rewrite `h` using `[(hD τ).2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hS` using `sum_primesB_le h5 hB hbad hcard`. Establish `hlogB : 0 ≤ Real.log B` using `Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))`. Establish `hR` using `logRd_nonneg E`.

Establish `key : |P.degree P.ht - P.degree P.record| ≤ Fintype.card Ψ * (j' * (2 * C₅ * Real.log B + logRd E))`. Apply `abs_degree_sub_le P P.ht P.record P.ht_ne P.record_ne` to reduce the goal to its premises. Introduce `τ`. Establish `h` using `h₂ L _ _ (primesB B bad) j' j' (mul_ne_zero (P.ht_ne τ) (inv_ne_zero (P.record_ne τ))) (hD τ).1 hj hj (hM τ)`. Rewrite `h` using `[(hD τ).2]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM1 : 2 * C₅ * Real.log B ≤ max (2 * C₅) 1 * Real.log B` using `mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB`. Establish `hM2 : logRd E ≤ max (2 * C₅) 1 * logRd E` using `le_mul_of_one_le_left hR (le_max_right _ _)`. Establish `hf : (0 : ℝ) ≤ Fintype.card Ψ * j'` using `mul_nonneg (Nat.cast_nonneg _) hj`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem RecordEigen.proof (h₁ : PrimeLogSum.Statement) (h₂ : NormCountBound.Statement)
    (h₃ : DifferentExtNorm.Statement) : RecordEigen.Statement := by
  obtain ⟨C₅, h5⟩ := h₁
  refine ⟨max (2 * C₅) 1, ?_⟩
  intro E L _ _ _ _ Ψ _ ι j' B bad P hB hbad hcard hER hM
  have hd : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
  have hD : ∀ τ, extDifferent (ι τ) ≠ ⊥ ∧
      Real.log (Ideal.absNorm (extDifferent (ι τ)) : ℝ) = Module.finrank ℚ L * logRd E :=
    fun τ => h₃ E L (ι τ)
  refine ⟨?_, ?_⟩
  · rw [mul_assoc]
    apply abs_degree_sub_le P P.record P.eig P.record_ne P.eig_ne (j' * logRd E)
    intro τ
    have hloc : LocalCountBound (P.record τ * (P.eig τ)⁻¹) (extDifferent (ι τ)) ∅ 0 j' := by
      intro p _ 𝔓 _
      rw [if_neg (Finset.notMem_empty p), zero_add]
      exact hER τ 𝔓
    have h := h₂ L _ _ ∅ 0 j' (mul_ne_zero (P.record_ne τ) (inv_ne_zero (P.eig_ne τ))) (hD τ).1 le_rfl hj hloc
    rw [(hD τ).2] at h
    calc _ ≤ _ := h
      _ = Module.finrank ℚ L * (j' * logRd E) := by ring
  · have hS := sum_primesB_le h5 hB hbad hcard
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
    have hR := logRd_nonneg E
    have key : |P.degree P.ht - P.degree P.record| ≤ Fintype.card Ψ * (j' * (2 * C₅ * Real.log B + logRd E)) := by
      apply abs_degree_sub_le P P.ht P.record P.ht_ne P.record_ne
      intro τ
      have h := h₂ L _ _ (primesB B bad) j' j' (mul_ne_zero (P.ht_ne τ) (inv_ne_zero (P.record_ne τ))) (hD τ).1 hj hj
        (hM τ)
      rw [(hD τ).2] at h
      calc _ ≤ _ := h
        _ ≤ Module.finrank ℚ L * (j' * (2 * C₅ * Real.log B)) + j' * (Module.finrank ℚ L * logRd E) := by
          gcongr
        _ = Module.finrank ℚ L * (j' * (2 * C₅ * Real.log B + logRd E)) := by ring
    have hM1 : 2 * C₅ * Real.log B ≤ max (2 * C₅) 1 * Real.log B :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB
    have hM2 : logRd E ≤ max (2 * C₅) 1 * logRd E :=
      le_mul_of_one_le_left hR (le_max_right _ _)
    have hf : (0 : ℝ) ≤ Fintype.card Ψ * j' := mul_nonneg (Nat.cast_nonneg _) hj
    calc _ ≤ _ := key
      _ = (Fintype.card Ψ * j') * (2 * C₅ * Real.log B + logRd E) := by ring
      _ ≤ (Fintype.card Ψ * j') * (max (2 * C₅) 1 * Real.log B + max (2 * C₅) 1 * logRd E) := by
        gcongr
      _ = max (2 * C₅) 1 * (Fintype.card Ψ * j') * (Real.log B + logRd E) := by ring

end GroundTheory.Heights₂.Heights.NineStatements
