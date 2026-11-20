import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

noncomputable section

namespace GlobalTheory.UnramReps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Proceed by induction on `y using WithZero.recZeroCoe with`. Consider the case `zero => exact zero_le'`. Consider the case `coe a`. Rewrite `h` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Rewrite using `[WithZero.coe_le_coe]`.

Establish `h' : Multiplicative.toAdd a < 0` using `h`. Use `show Multiplicative.toAdd a ≤ -1`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_ofAdd_neg_one_of_lt_one' {y : WithZero (Multiplicative ℤ)} (h : y < 1) :
    y ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

/- English proof (translation)
Use `set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))`. Establish `hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring)` using `Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Use `haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin`. Use `haveI := Fintype.ofFinite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring)`. Set `f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → L` to `fun c => ((Ideal.Quotient.mk_surjective c).choose : L)`.

Use `⟨Finset.univ.image f, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hr`. Use `show _ ∈ v.integer`. Rewrite using `[Valuation.mem_integer_iff]`.

Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2`. Introduce `x hx`. Establish `hx' : x ∈ v.valuationSubring` using `(Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)`. Set `xs : v.valuationSubring` to `⟨x, hx'⟩`. Set `c` to `Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs`.

Use `⟨f c, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hspec` using `(Ideal.Quotient.mk_surjective c).choose_spec`. Establish `hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈ IsLocalRing.maximalIdeal v.valuationSubring` using `Ideal.Quotient.eq.1 (hspec.symm)`. Rewrite `hmem` using `[Valuation.mem_maximalIdeal_iff]`. Simplify `hmem` using `[xs, f]`.
-/
theorem exists_residue_reps' {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2) :
    ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ x ∈ Formalism.UG.intL L, ∃ r ∈ R,
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (x - r) < 1 := by
  classical
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin
  haveI := Fintype.ofFinite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring)
  let f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → L :=
    fun c => ((Ideal.Quotient.mk_surjective c).choose : L)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    show _ ∈ v.integer
    rw [Valuation.mem_integer_iff]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2
  · intro x hx
    have hx' : x ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)
    let xs : v.valuationSubring := ⟨x, hx'⟩
    let c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs
    refine ⟨f c, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    have hspec := (Ideal.Quotient.mk_surjective c).choose_spec
    have hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈
        IsLocalRing.maximalIdeal v.valuationSubring :=
      Ideal.Quotient.eq.1 (hspec.symm)
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    simpa [xs, f] using hmem

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU`. Take `⟨-, -, -, hϖ, -, hq, hcard⟩` from `hU`. Take `⟨R, hRO, hR⟩` from `exists_residue_reps' (L := L) hq hcard`. Use `set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))`. Establish `h0 : v ϖ ≠ 0` using `by rw [hϖ]; exact WithZero.coe_ne_zero`.

Establish `hϖ1 : v ϖ ≤ 1`. Rewrite using `[hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]`. Use `show (-1 : ℤ) ≤ 0`. Evaluate the numerical expressions. Establish `hϖO : ϖ ∈ Formalism.UG.intL L` using `(Valuation.mem_integer_iff _ _).2 hϖ1`.

Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Use `⟨{0}, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`.

Rewrite using `[Finset.mem_singleton.1 hr]`. Conclude with `(Formalism.UG.intL L).zero_mem`. Introduce `x hx`. Use `⟨0, Finset.mem_singleton_self 0, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero, pow_zero]`.

Conclude with `(Valuation.mem_integer_iff _ _).1 hx`. Consider the case `succ N ih`. Take `⟨T, hTO, hT⟩` from `ih`. Use `⟨Finset.image₂ (fun r t => r + ϖ * t) R T, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Take `⟨r, hr, t, ht, rfl⟩` from `Finset.mem_image₂.1 hz`. Conclude with `(Formalism.UG.intL L).add_mem (hRO r hr) ((Formalism.UG.intL L).mul_mem hϖO (hTO t ht))`. Introduce `x hx`. Take `⟨r, hr, hxr⟩` from `hR x hx`. Establish `hle : v (x - r) ≤ v ϖ` using `hϖ ▸ le_ofAdd_neg_one_of_lt_one' hxr`.

Use `set y := (x - r) * ϖ⁻¹ with hy`. Establish `hϖ0 : ϖ ≠ 0` using `fun h => h0 (by rw [h, map_zero])`. Establish `hyO : y ∈ Formalism.UG.intL L`. Apply `(Valuation.mem_integer_iff _ _).2` to reduce the goal to its premises. Rewrite using `[hy, map_mul, map_inv₀]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨t, ht, hyt⟩` from `hT y hyO`. Use `⟨r + ϖ * t, Finset.mem_image₂.2 ⟨r, hr, t, ht, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `he : x - (r + ϖ * t) = ϖ * (y - t)`. Rewrite using `[hy]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show v (x - (r + ϖ * t)) ≤ v ϖ ^ (N + 1)`. Rewrite using `[he, map_mul, pow_succ']`. Conclude with `mul_le_mul' le_rfl hyt`.
-/
theorem exists_reps_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
      ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  intro L _ _ ϖ σ q hU
  classical
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := hU
  obtain ⟨R, hRO, hR⟩ := exists_residue_reps' (L := L) hq hcard
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  have hϖ1 : v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    norm_num
  have hϖO : ϖ ∈ Formalism.UG.intL L := (Valuation.mem_integer_iff _ _).2 hϖ1
  intro K
  induction K with
  | zero =>
    refine ⟨{0}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton.1 hr]; exact (Formalism.UG.intL L).zero_mem
    · intro x hx
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      rw [sub_zero, pow_zero]
      exact (Valuation.mem_integer_iff _ _).1 hx
  | succ N ih =>
    obtain ⟨T, hTO, hT⟩ := ih
    refine ⟨Finset.image₂ (fun r t => r + ϖ * t) R T, ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_image₂.1 hz
      exact (Formalism.UG.intL L).add_mem (hRO r hr) ((Formalism.UG.intL L).mul_mem hϖO (hTO t ht))
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := hR x hx
      have hle : v (x - r) ≤ v ϖ := hϖ ▸ le_ofAdd_neg_one_of_lt_one' hxr
      set y := (x - r) * ϖ⁻¹ with hy
      have hϖ0 : ϖ ≠ 0 := fun h => h0 (by rw [h, map_zero])
      have hyO : y ∈ Formalism.UG.intL L := by
        apply (Valuation.mem_integer_iff _ _).2
        rw [hy, map_mul, map_inv₀]
        calc v (x - r) * (v ϖ)⁻¹ ≤ v ϖ * (v ϖ)⁻¹ := mul_le_mul' hle le_rfl
          _ = 1 := mul_inv_cancel₀ h0
      obtain ⟨t, ht, hyt⟩ := hT y hyO
      refine ⟨r + ϖ * t, Finset.mem_image₂.2 ⟨r, hr, t, ht, rfl⟩, ?_⟩
      have he : x - (r + ϖ * t) = ϖ * (y - t) := by
        rw [hy]; field_simp; ring
      show v (x - (r + ϖ * t)) ≤ v ϖ ^ (N + 1)
      rw [he, map_mul, pow_succ']
      exact mul_le_mul' le_rfl hyt

end GlobalTheory.UnramReps
