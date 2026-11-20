import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Det

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Establish `e : ∀ i k, LinearMap.toMatrix' γ.1.toLinearMap k i = γ.1 (Pi.single i 1) k`. Introduce `i k`. Rewrite using `[LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression. Establish `h : (LinearMap.toMatrix' γ.1.toLinearMap).conjTranspose * LinearMap.toMatrix' γ.1.toLinearMap = 1`.

Use extensionality with `i j`. Establish `h1 : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (Pi.single j 1)) = hStd E n (Pi.single i 1) (Pi.single j 1)` using `γ.2 _ _`. Establish `h2 : ∀ x y : Sp E n, hStd E n x y = ∑ k, star (x k) * y k` using `fun _ _ => rfl`. Rewrite `h1` using `[h2, h2]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.conjTranspose_apply, e]`. Rewrite using `[h1, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Pi.single_apply]`.

Simplify using `[Pi.single_apply, hij, Ne.symm hij]`. Establish `hd` using `congrArg Matrix.det h`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, LinearMap.det_toMatrix']`. Rewrite using `[LinearEquiv.coe_det, mul_comm]`. Conclude with `hd`.
-/
theorem mh_det_norm (γ : UF E n) : ((LinearEquiv.det γ.1 : Eˣ) : E) * star ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  have e : ∀ i k, LinearMap.toMatrix' γ.1.toLinearMap k i = γ.1 (Pi.single i 1) k := by
    intro i k
    rw [LinearMap.toMatrix'_apply]
    rfl
  have h : (LinearMap.toMatrix' γ.1.toLinearMap).conjTranspose * LinearMap.toMatrix' γ.1.toLinearMap = 1 := by
    ext i j
    have h1 : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (Pi.single j 1)) = hStd E n (Pi.single i 1) (Pi.single j 1) := γ.2 _ _
    have h2 : ∀ x y : Sp E n, hStd E n x y = ∑ k, star (x k) * y k := fun _ _ => rfl
    rw [h2, h2] at h1
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, e]
    rw [h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, LinearMap.det_toMatrix'] at hd
  rw [LinearEquiv.coe_det, mul_comm]
  exact hd

end Det

section H90

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hX.cplxE` as an intermediate fact. Set `w : InfinitePlace X.E` to `Classical.arbitrary _`. Establish `hw : w.IsComplex` using `IsTotallyComplex.isComplex w`.

Rewrite `hw` using `[InfinitePlace.isComplex_iff]`. Apply `hw` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hc]`.
-/
theorem mh_exists_ne (X : Fields) (hX : X.Ok) : ∃ a : X.E, star a ≠ a := by
  by_contra hc
  push Not at hc
  have := hX.cplxE
  let w : InfinitePlace X.E := Classical.arbitrary _
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  rw [InfinitePlace.isComplex_iff] at hw
  apply hw
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hc]

/- English proof (translation)
Distinguish the cases in `h : z = -1`. Take `⟨a, ha⟩` from `mh_exists_ne X hX`. Establish `h0 : a - star a ≠ 0` using `fun h0 => ha (sub_eq_zero.1 h0).symm`. Use `⟨Units.mk0 (a - star a) h0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, star_sub, star_star, h, ← neg_sub a (star a), div_neg, div_self h0]`.

Establish `h0 : 1 + z ≠ 0` using `fun h0 => h (by linear_combination h0)`. Establish `h1 : star (1 + z) ≠ 0` using `fun h1 => h0 (star_eq_zero.1 h1)`. Use `⟨Units.mk0 (1 + z) h0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, eq_div_iff h1, star_add, star_one, mul_add, mul_one, hz, add_comm]`.
-/
theorem hilbert_ninety_norm_one (X : Fields) (hX : X.Ok) (z : X.E) (hz : z * star z = 1) : ∃ x : X.Eˣ, z = (x : X.E) / star (x : X.E) := by
  by_cases h : z = -1
  · obtain ⟨a, ha⟩ := mh_exists_ne X hX
    have h0 : a - star a ≠ 0 := fun h0 => ha (sub_eq_zero.1 h0).symm
    refine ⟨Units.mk0 (a - star a) h0, ?_⟩
    rw [Units.val_mk0, star_sub, star_star, h, ← neg_sub a (star a), div_neg, div_self h0]
  · have h0 : 1 + z ≠ 0 := fun h0 => h (by linear_combination h0)
    have h1 : star (1 + z) ≠ 0 := fun h1 => h0 (star_eq_zero.1 h1)
    refine ⟨Units.mk0 (1 + z) h0, ?_⟩
    rw [Units.val_mk0, eq_div_iff h1, star_add, star_one, mul_add, mul_one, hz, add_comm]

end H90

section Bridge

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Unfold `redP at h`. Use `split_ifs at h with hex`. Take `⟨r', s', hs', hrs', hmk⟩` from `hex.choose_spec`.

Establish `hc0 : hex.choose ≠ 0` using `h.ne_zero`. Establish `hr' : r' ∉ P.asIdeal`. Introduce `hr`. Apply `hc0` to reduce the goal to its premises. Establish `h6 : Ideal.Quotient.mk P.asIdeal s' * hex.choose = 0`.

Rewrite using `[hmk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hr`. Break down `mul_eq_zero.mp h6 with h' | h'` into its components or cases. Conclude with `absurd (Ideal.Quotient.eq_zero_iff_mem.mp h') hs'`. Conclude with `h'`.

Establish `hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1` using `(le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))`. Establish `hr1 : P.valuation E (algebraMap (𝓞 E) E r') = 1` using `(le_antisymm (P.valuation_le_one r') (not_lt.mp (fun h => hr' ((P.valuation_lt_one_iff_mem r').mp h))))`. Establish `h5` using `congrArg (P.valuation E) hrs'`. Rewrite `h5` using `[map_mul, hs1, one_mul, hr1]`. Conclude with `h5`.

Conclude with `absurd h not_isUnit_zero`.
-/
theorem mh_val_unit {u : E} (h : IsUnit (redP P u)) : P.valuation E u = 1 := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  unfold redP at h
  split_ifs at h with hex
  · obtain ⟨r', s', hs', hrs', hmk⟩ := hex.choose_spec
    have hc0 : hex.choose ≠ 0 := h.ne_zero
    have hr' : r' ∉ P.asIdeal := by
      intro hr
      apply hc0
      have h6 : Ideal.Quotient.mk P.asIdeal s' * hex.choose = 0 := by
        rw [hmk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rcases mul_eq_zero.mp h6 with h' | h'
      · exact absurd (Ideal.Quotient.eq_zero_iff_mem.mp h') hs'
      · exact h'
    have hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1 := (le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))
    have hr1 : P.valuation E (algebraMap (𝓞 E) E r') = 1 := (le_antisymm (P.valuation_le_one r') (not_lt.mp (fun h => hr' ((P.valuation_lt_one_iff_mem r').mp h))))
    have h5 := congrArg (P.valuation E) hrs'
    rw [map_mul, hs1, one_mul, hr1] at h5
    exact h5
  · exact absurd h not_isUnit_zero

/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Establish `hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * w = algebraMap (𝓞 E) E r ∧ Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r`. Take `⟨r, s, hs, hrs⟩` from `hI`. Establish `hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)`.

Use `⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hrs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]`. Unfold `redP at h0`. Rewrite `h0` using `[dif_pos hex]`. Take `⟨r', s', hs', hrs', hmk⟩` from `hex.choose_spec`.

Rewrite `hmk` using `[h0, mul_zero]`. Establish `hr' : r' ∈ P.asIdeal` using `Ideal.Quotient.eq_zero_iff_mem.mp hmk.symm`. Establish `hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1` using `(le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))`. Establish `h5` using `congrArg (P.valuation E) hrs'`. Rewrite `h5` using `[map_mul, hs1, one_mul]`.

Rewrite using `[h5]`. Conclude with `(P.valuation_lt_one_iff_mem r').mpr hr'`.
-/
theorem mh_val_lt {w : E} (hI : IntAt P w) (h0 : redP P w = 0) : P.valuation E w < 1 := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * w = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r := by
    obtain ⟨r, s, hs, hrs⟩ := hI
    have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    refine ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hrs, ?_⟩
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  unfold redP at h0
  rw [dif_pos hex] at h0
  obtain ⟨r', s', hs', hrs', hmk⟩ := hex.choose_spec
  rw [h0, mul_zero] at hmk
  have hr' : r' ∈ P.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk.symm
  have hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1 := (le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))
  have h5 := congrArg (P.valuation E) hrs'
  rw [map_mul, hs1, one_mul] at h5
  rw [h5]
  exact (P.valuation_lt_one_iff_mem r').mpr hr'

/- English proof (translation)
The claim follows from `P.valuation_lt_one_iff_mem b`.
-/
theorem mh_val_mem {b : 𝓞 E} : P.valuation E (b : E) < 1 ↔ b ∈ P.asIdeal := P.valuation_lt_one_iff_mem b

/- English proof (translation)
Rewrite using `[show (b : E) = algebraMap (𝓞 E) E b from rfl, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]`.
-/
theorem mh_val_pow {b : 𝓞 E} (k : ℕ) : P.valuation E (b : E) ≤ WithZero.exp (-(k : ℤ)) ↔ b ∈ P.asIdeal ^ k := by
  rw [show (b : E) = algebraMap (𝓞 E) E b from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_mem]

/- English proof (translation)
Establish `h2` using `(mh_val_pow (P := P) 2).mpr h`. Simplify using `using h2`.
-/
theorem mh_val_sq {b : 𝓞 E} (h : b ∈ P.asIdeal ^ 2) : P.valuation E (b : E) ≤ WithZero.exp (-2 : ℤ) := by
  have h2 := (mh_val_pow (P := P) 2).mpr h
  simpa using h2

/- English proof (translation)
Establish `hb0 : (b : E) ≠ 0`. Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[NumberField.RingOfIntegers.coe_eq_zero_iff.mp h0]`. Conclude with `Submodule.zero_mem _`.

Establish `hv0 : P.valuation E (b : E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hb0`. Establish `hle1 : P.valuation E (b : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ))` using `(mh_val_pow 1).mpr (by simpa using h1)`. Establish `hnle2 : ¬ P.valuation E (b : E) ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => h2 ((mh_val_pow 2).mp h)`. Take `⟨m, hm⟩ : ∃ m : ℤ, P.valuation E (b : E) = WithZero.exp m` from `⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩`. Rewrite `hle1`, `hnle2`, the goal using `[hm]`.

Rewrite `hle1`, `hnle2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Move the coercions through the operations in `at hle1 hnle2`. Use linear arithmetic over natural numbers and integers.
-/
theorem mh_val_unif {b : 𝓞 E} (h1 : b ∈ P.asIdeal) (h2 : b ∉ P.asIdeal ^ 2) : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
  have hb0 : (b : E) ≠ 0 := by
    intro h0
    apply h2
    rw [NumberField.RingOfIntegers.coe_eq_zero_iff.mp h0]
    exact Submodule.zero_mem _
  have hv0 : P.valuation E (b : E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hle1 : P.valuation E (b : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := (mh_val_pow 1).mpr (by simpa using h1)
  have hnle2 : ¬ P.valuation E (b : E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h => h2 ((mh_val_pow 2).mp h)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, P.valuation E (b : E) = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩
  rw [hm] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  push_cast at hle1 hnle2
  omega

/- English proof (translation)
Unfold `ordE`. Rewrite using `[h, WithZero.log_exp, neg_neg]`.
-/
theorem mh_ordE_unif {a : E} {n : ℤ} (h : P.valuation E a = WithZero.exp (-n)) : ordE P a = n := by
  unfold ordE
  rw [h, WithZero.log_exp, neg_neg]

end Bridge

end Formalism.L2.Ker
