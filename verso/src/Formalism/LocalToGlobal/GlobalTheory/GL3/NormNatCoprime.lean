import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

variable {D : D7}

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨P, hPm, hPy⟩` from `hy`. Rewrite `hPy` using `[hPm.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hPy`.

Establish `h1` using `eq_neg_of_add_eq_zero_left hPy`. Establish `hn0 : P.natDegree ≠ 0`. Introduce `h0`. Rewrite `hPy` using `[h0]`. Simplify using `at hPy`.

Establish `hc : ∀ z : ℤ, ‖(Int.castRingHom k) z‖ ≤ 1`. Introduce `z`. Rewrite using `[eq_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one k z`. Establish `hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom k) (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (P.natDegree - 1)`.

Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ P.natDegree - 1`. Rewrite `hi` using `[Finset.mem_range]`.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (hc _) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one` to reduce the goal to its premises. Use `_ = ‖y‖ ^ (P.natDegree - 1) := one_mul _`. Establish `h2 : ‖y‖ ^ P.natDegree ≤ ‖y‖ ^ (P.natDegree - 1)`.

Rewrite using `[← norm_pow, h1, norm_neg]`. Conclude with `hbound`. Establish `h3 : ‖y‖ ^ (P.natDegree - 1) < ‖y‖ ^ P.natDegree` using `pow_lt_pow_right₀ hlt (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_int {k : Type} [NormedField k] [IsUltrametricDist k] {y : k}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hPm, hPy⟩ := hy
  rw [hPm.as_sum] at hPy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C] at hPy
  have h1 := eq_neg_of_add_eq_zero_left hPy
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hPy
    simp at hPy
  have hc : ∀ z : ℤ, ‖(Int.castRingHom k) z‖ ≤ 1 := by
    intro z
    rw [eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one k z
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom k) (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ P.natDegree - 1 := by
      rw [Finset.mem_range] at hi
      omega
    calc ‖(Int.castRingHom k) (P.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (P.natDegree - 1) := by
          apply mul_le_mul (hc _) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = ‖y‖ ^ (P.natDegree - 1) := one_mul _
  have h2 : ‖y‖ ^ P.natDegree ≤ ‖y‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, h1, norm_neg]
    exact hbound
  have h3 : ‖y‖ ^ (P.natDegree - 1) < ‖y‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

/- English proof (translation)
Establish `hs : ¬ p ∣ s` using `(Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp h.symm`. Establish `hQ : ‖(s : ℚ_[p])‖ = 1`. Establish `h1 : ‖((s : ℤ) : ℚ_[p])‖ ≤ 1` using `by first`. Consider the case `exact Padic.norm_int_le_one _`. Consider the case `exact padicNormE.norm_int_le_one _`.

Establish `h2 : ¬ ‖((s : ℤ) : ℚ_[p])‖ < 1` using `by first`. Consider the case `rw [Padic.norm_int_lt_one_iff_dvd]`. Conclude with `hs` after adjusting the coercions. Consider the case `rw [Padic.norm_intCast_lt_one_iff_dvd]`. Conclude with `hs` after adjusting the coercions.

Consider the case `rw [Padic.norm_intCast_lt_one_iff]`. Conclude with `hs` after adjusting the coercions. Consider the case `rw [padicNormE.norm_intCast_lt_one_iff_dvd]`. Conclude with `hs` after adjusting the coercions. Consider the case `(intro hlt; apply hs; exact_mod_cast (Padic.norm_int_lt_one_iff_dvd (s : ℤ)).mp hlt)`.

Consider the case `(intro hlt; apply hs; exact_mod_cast (Padic.norm_intCast_lt_one_iff_dvd (s : ℤ)).mp hlt)`. Establish `e : ((s : ℤ) : ℚ_[p]) = (s : ℚ_[p])` using `by simp`. Rewrite using `[← e]`. Conclude with `le_antisymm h1 (not_lt.mp h2)`. Establish `e : (s : ℂ_[p]) = (((s : ℚ_[p]) : PadicAlgCl p) : ℂ_[p])` using `by simp`.

Rewrite using `[e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, hQ]`.
-/
theorem norm_nat_coprime (p : ℕ) [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have hs : ¬ p ∣ s := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp h.symm
  have hQ : ‖(s : ℚ_[p])‖ = 1 := by
    have h1 : ‖((s : ℤ) : ℚ_[p])‖ ≤ 1 := by
      first
        | exact Padic.norm_int_le_one _
        | exact padicNormE.norm_int_le_one _
    have h2 : ¬ ‖((s : ℤ) : ℚ_[p])‖ < 1 := by
      first
        | rw [Padic.norm_int_lt_one_iff_dvd]; exact_mod_cast hs
        | rw [Padic.norm_intCast_lt_one_iff_dvd]; exact_mod_cast hs
        | rw [Padic.norm_intCast_lt_one_iff]; exact_mod_cast hs
        | rw [padicNormE.norm_intCast_lt_one_iff_dvd]; exact_mod_cast hs
        | (intro hlt; apply hs; exact_mod_cast (Padic.norm_int_lt_one_iff_dvd (s : ℤ)).mp hlt)
        | (intro hlt; apply hs; exact_mod_cast (Padic.norm_intCast_lt_one_iff_dvd (s : ℤ)).mp hlt)
    have e : ((s : ℤ) : ℚ_[p]) = (s : ℚ_[p]) := by simp
    rw [← e]
    exact le_antisymm h1 (not_lt.mp h2)
  have e : (s : ℂ_[p]) = (((s : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by simp
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, hQ]

/- English proof (translation)
Unfold `Qbar embT`. Establish `hx : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Establish `hy : IsAlgebraic ℚ ((D.host.emb ↑(D.eTau τ)) x)` using `(hx.map (D.host.emb ↑(D.eTau τ)).toRatAlgHom).isAlgebraic`. Use `first`. Consider the case `exact mem_algebraicClosure_iff.mpr hy`.

Consider the case `exact IntermediateField.mem_algebraicClosure_iff.mpr hy`. Consider the case `exact (mem_algebraicClosure_iff' ).mpr hy.isIntegral`.
-/
theorem emb_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  unfold Qbar embT
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hy : IsAlgebraic ℚ ((D.host.emb ↑(D.eTau τ)) x) :=
    (hx.map (D.host.emb ↑(D.eTau τ)).toRatAlgHom).isAlgebraic
  first
    | exact mem_algebraicClosure_iff.mpr hy
    | exact IntermediateField.mem_algebraicClosure_iff.mpr hy
    | exact (mem_algebraicClosure_iff' ).mpr hy.isIntegral

def embQ (τ : D.what₂.Tau) : D.host.E →+* Qbar := (embT D τ).codRestrict Qbar (emb_mem τ)

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.mem_one.mp hx`. Apply `norm_le_one_of_int` to reduce the goal to its premises. Establish `ha : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E a)` using `by first`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe a`. Consider the case `exact a.2`.

Consider the case `exact isIntegral_algebraMap.tower_top`. Take `⟨P, hm, hP⟩` from `ha`. Use `⟨P, hm, ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg (lam.comp (embQ τ)) hP`. Rewrite `e1` using `[Polynomial.hom_eval₂, map_zero]`.

Use `e1 using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `exact RingHom.ext_int _ _`. Consider the case `rfl`.
-/
theorem norm_lam_int {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {x : D.host.E}
    (hx : x ∈ (1 : IdE D)) : ‖lam (embQ τ x)‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
  apply norm_le_one_of_int
  have ha : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E a) := by
    first
      | exact NumberField.RingOfIntegers.isIntegral_coe a
      | exact a.2
      | exact isIntegral_algebraMap.tower_top
  obtain ⟨P, hm, hP⟩ := ha
  refine ⟨P, hm, ?_⟩
  have e1 := congrArg (lam.comp (embQ τ)) hP
  rw [Polynomial.hom_eval₂, map_zero] at e1
  convert e1 using 2
  all_goals first
    | exact RingHom.ext_int _ _
    | rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx`. Simplify using `using hx`. Consider the case `succ k ih`.

Introduce `x hx`. Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Establish `e : (s : D.host.E) ^ (k + 1) * (a * b) = ((s : D.host.E) ^ k * a) * ((s : D.host.E) * b)` using `by ring`. Rewrite using `[e]`.

Establish `hm` using `Submodule.mul_mem_mul (ih a ha) (h1 b hb)`. Rewrite `hm` using `[one_mul]`. Then use the resulting hypothesis. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem oneAt_pow_mem {𝔞 : IdE D} {s : ℕ} (h1 : ∀ x ∈ 𝔞, (s : D.host.E) * x ∈ (1 : IdE D)) (k : ℕ) :
    ∀ x ∈ 𝔞 ^ k, (s : D.host.E) ^ k * x ∈ (1 : IdE D) := by
  induction k with
  | zero =>
    intro x hx
    simpa using hx
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · have e : (s : D.host.E) ^ (k + 1) * (a * b) = ((s : D.host.E) ^ k * a) * ((s : D.host.E) * b) := by ring
      rw [e]
      have hm := Submodule.mul_mem_mul (ih a ha) (h1 b hb)
      rwa [one_mul] at hm
    · rw [mul_add]
      exact Submodule.add_mem _ hy hz

/- English proof (translation)
Introduce `χ hχ p _ lam 𝔞 ha hone`. Set `_` to `D.host.cmStar`. Take `⟨s, hs, h1, h2⟩` from `hone`. Take `⟨k, hk, z, hz, hspan⟩` from `CU.pow_unitary D ha`. Establish `hz0 : z ≠ 0` using `by rintro rfl; simp at hz`.

Establish `hzu : z ∈ unitary D.host.E`. Rewrite using `[Unitary.mem_iff, CU.star_conj]`. Conclude with `⟨by rw [mul_comm]; exact hz, hz⟩`. Establish `hpow : χ 𝔞 ^ k = ∏ τ : D.what₂.Tau, (embT D τ z)⁻¹`. Establish `h` using `hχ.2 ⟨z, hzu⟩`.

Simplify using `only at h`. Rewrite `h` using `[← hspan, CU.chi_pow D χ hχ ha k hk]`. Conclude with `h`. Establish `hz𝔞 : z ∈ 𝔞 ^ k` using `by rw [hspan]; exact Submodule.mem_span_singleton_self z`. Establish `hA : (s : D.host.E) ^ k * z ∈ (1 : IdE D)` using `oneAt_pow_mem h1 k z hz𝔞`.

Establish `hsk : (s : D.host.E) ^ k ∈ 𝔞 ^ k` using `Submodule.pow_mem_pow 𝔞 h2 k`. Rewrite `hsk` using `[hspan]`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp hsk`. Establish `hB : (s : D.host.E) ^ k * z⁻¹ ∈ (1 : IdE D)`. Rewrite using `[← hr, Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hz0, mul_one]`.

Conclude with `Submodule.mem_one.mpr ⟨r, rfl⟩`. Establish `hn : ‖(s : ℂ_[p])‖ = 1` using `norm_nat_coprime p hs`. Establish `hτ : ∀ τ, ‖lam (embQ τ z)‖ = 1`. Introduce `τ`. Establish `a1` using `norm_lam_int lam τ hA`.

Establish `b1` using `norm_lam_int lam τ hB`. Establish `hprod : lam (embQ τ ((s : D.host.E) ^ k * z)) * lam (embQ τ ((s : D.host.E) ^ k * z⁻¹)) = (s : ℂ_[p]) ^ (2 * k)`. Rewrite using `[← map_mul, ← map_mul]`. Establish `e : (s : D.host.E) ^ k * z * ((s : D.host.E) ^ k * z⁻¹) = (s : D.host.E) ^ (2 * k)` using `by field_simp; ring`. Rewrite using `[e, map_pow, map_pow, map_natCast, map_natCast]`.

Establish `hnorm : ‖lam (embQ τ ((s : D.host.E) ^ k * z))‖ * ‖lam (embQ τ ((s : D.host.E) ^ k * z⁻¹))‖ = 1`. Rewrite using `[← norm_mul, hprod, norm_pow, hn, one_pow]`. Establish `hA1 : ‖lam (embQ τ ((s : D.host.E) ^ k * z))‖ = 1`. Establish `n0` using `norm_nonneg (lam (embQ τ ((s : D.host.E) ^ k * z)))`. Establish `n1` using `norm_nonneg (lam (embQ τ ((s : D.host.E) ^ k * z⁻¹)))`.

Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, hn, one_pow, one_mul] at hA1`. Conclude with `hA1`. Establish `hmem : χ 𝔞 ∈ Qbar`. Rewrite using `[mem_algebraicClosure_iff']`.

Use `IsIntegral.of_pow (by omega : 0 < k) ?_` and prove the remaining obligations. Rewrite using `[hpow]`. Use `IsIntegral.prod _ fun τ _ => ?_` and prove the remaining obligations. Use `mem_algebraicClosure_iff'.mp (emb_mem τ z⁻¹)` as an intermediate fact. Rewrite `this` using `[map_inv₀]`. Then use the resulting hypothesis.

Use `⟨hmem, ?_⟩` and prove the remaining obligations. Use `set c : Qbar := ⟨χ 𝔞, hmem⟩ with hc`. Establish `hcpow : c ^ k = ∏ τ : D.what₂.Tau, (embQ τ z)⁻¹`. Apply `Subtype.val_injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Qbar.val (c ^ k) = Qbar.val (∏ τ : D.what₂.Tau, (embQ τ z)⁻¹)`.

Rewrite using `[map_pow, map_prod]`. Simplify using `only [map_inv₀]`. Conclude with `hpow`. Apply the tactic sequence `have hl : lamC lam (χ 𝔞) = lam c := by simp only [lamC, dif_pos hmem]; try rfl`. Rewrite using `[hl]`.

Establish `hk1 : ‖lam c‖ ^ k = 1`. Rewrite using `[← norm_pow, ← map_pow, hcpow, map_prod, norm_prod]`. Conclude with `Finset.prod_eq_one fun τ _ => by rw [map_inv₀, norm_inv, hτ τ, inv_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp hk1`.
-/
theorem lemmaU : LemmaU D := by
  intro χ hχ p _ lam 𝔞 ha hone
  let _ := D.host.cmStar
  obtain ⟨s, hs, h1, h2⟩ := hone
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have hpow : χ 𝔞 ^ k = ∏ τ : D.what₂.Tau, (embT D τ z)⁻¹ := by
    have h := hχ.2 ⟨z, hzu⟩
    simp only at h
    rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
    exact h
  have hz𝔞 : z ∈ 𝔞 ^ k := by rw [hspan]; exact Submodule.mem_span_singleton_self z
  have hA : (s : D.host.E) ^ k * z ∈ (1 : IdE D) := oneAt_pow_mem h1 k z hz𝔞
  have hsk : (s : D.host.E) ^ k ∈ 𝔞 ^ k := Submodule.pow_mem_pow 𝔞 h2 k
  rw [hspan] at hsk
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsk
  have hB : (s : D.host.E) ^ k * z⁻¹ ∈ (1 : IdE D) := by
    rw [← hr, Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  have hn : ‖(s : ℂ_[p])‖ = 1 := norm_nat_coprime p hs
  have hτ : ∀ τ, ‖lam (embQ τ z)‖ = 1 := by
    intro τ
    have a1 := norm_lam_int lam τ hA
    have b1 := norm_lam_int lam τ hB
    have hprod : lam (embQ τ ((s : D.host.E) ^ k * z)) * lam (embQ τ ((s : D.host.E) ^ k * z⁻¹)) =
        (s : ℂ_[p]) ^ (2 * k) := by
      rw [← map_mul, ← map_mul]
      have e : (s : D.host.E) ^ k * z * ((s : D.host.E) ^ k * z⁻¹) = (s : D.host.E) ^ (2 * k) := by
        field_simp; ring
      rw [e, map_pow, map_pow, map_natCast, map_natCast]
    have hnorm : ‖lam (embQ τ ((s : D.host.E) ^ k * z))‖ * ‖lam (embQ τ ((s : D.host.E) ^ k * z⁻¹))‖ = 1 := by
      rw [← norm_mul, hprod, norm_pow, hn, one_pow]
    have hA1 : ‖lam (embQ τ ((s : D.host.E) ^ k * z))‖ = 1 := by
      have n0 := norm_nonneg (lam (embQ τ ((s : D.host.E) ^ k * z)))
      have n1 := norm_nonneg (lam (embQ τ ((s : D.host.E) ^ k * z⁻¹)))
      nlinarith
    simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, hn, one_pow, one_mul] at hA1
    exact hA1
  have hmem : χ 𝔞 ∈ Qbar := by
    rw [mem_algebraicClosure_iff']
    refine IsIntegral.of_pow (by omega : 0 < k) ?_
    rw [hpow]
    refine IsIntegral.prod _ fun τ _ => ?_
    have := mem_algebraicClosure_iff'.mp (emb_mem τ z⁻¹)
    rwa [map_inv₀] at this
  refine ⟨hmem, ?_⟩
  set c : Qbar := ⟨χ 𝔞, hmem⟩ with hc
  have hcpow : c ^ k = ∏ τ : D.what₂.Tau, (embQ τ z)⁻¹ := by
    apply Subtype.val_injective
    change Qbar.val (c ^ k) = Qbar.val (∏ τ : D.what₂.Tau, (embQ τ z)⁻¹)
    rw [map_pow, map_prod]
    simp only [map_inv₀]
    exact hpow
  have hl : lamC lam (χ 𝔞) = lam c := by simp only [lamC, dif_pos hmem]; try rfl
  rw [hl]
  have hk1 : ‖lam c‖ ^ k = 1 := by
    rw [← norm_pow, ← map_pow, hcpow, map_prod, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [map_inv₀, norm_inv, hτ τ, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp hk1

/- English proof (translation)
Use `first`. Consider the case `exact Matrix.smul_mulVec_assoc c A v`. Consider the case `(ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])`.
-/
theorem smul_mulVec' {N : ℕ} (c : D.host.E) (A : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    (c • A).mulVec v = c • A.mulVec v := by
  first
    | exact Matrix.smul_mulVec_assoc c A v
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

/- English proof (translation)
Establish `hv : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`. Unfold `Formalism.MainNotions.StandardLatticesGL3.stdL`. Rewrite using `[Submodule.mem_pi]`. Introduce `k _`. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.one_le.mp le_rfl`. Rewrite using `[Pi.single_eq_of_ne hk]`. Conclude with `Submodule.zero_mem _`.

Establish `hw` using `hM _ hv`. Unfold `Formalism.MainNotions.StandardLatticesGL3.stdL at hw`. Rewrite `hw` using `[Submodule.mem_pi]`. Simplify `hw i trivial` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem entry_mem_of_std {N : ℕ} {M : Matrix (Fin N) (Fin N) D.host.E}
    (hM : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, M.mulVec v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) (i j : Fin N) :
    M i j ∈ (1 : IdE D) := by
  have hv : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    unfold Formalism.MainNotions.StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    intro k _
    by_cases hk : k = j
    · subst hk
      rw [Pi.single_eq_same]
      exact Submodule.one_le.mp le_rfl
    · rw [Pi.single_eq_of_ne hk]
      exact Submodule.zero_mem _
  have hw := hM _ hv
  unfold Formalism.MainNotions.StandardLatticesGL3.stdL at hw
  rw [Submodule.mem_pi] at hw
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hw i trivial

/- English proof (translation)
Establish `h` using `fun i j => Submodule.mem_one.mp (entry_mem_of_std hM i j)`. Use `choose A hA using h`. Establish `hMA : M = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix A`. Use extensionality with `i j`. Conclude with `(hA i j).symm`.

Rewrite using `[hMA]`. Conclude with `Submodule.mem_one.mpr ⟨Matrix.det (A : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), RingHom.map_det _ (A : Matrix (Fin N) (Fin N) (𝓞 D.host.E))⟩`.
-/
theorem det_int_of_std {N : ℕ} {M : Matrix (Fin N) (Fin N) D.host.E}
    (hM : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, M.mulVec v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) : M.det ∈ (1 : IdE D) := by
  have h := fun i j => Submodule.mem_one.mp (entry_mem_of_std hM i j)
  choose A hA using h
  have hMA : M = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix A := by
    ext i j
    exact (hA i j).symm
  rw [hMA]
  exact Submodule.mem_one.mpr ⟨Matrix.det (A : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), RingHom.map_det _ (A : Matrix (Fin N) (Fin N) (𝓞 D.host.E))⟩

/- English proof (translation)
Introduce `p N L hL`. Take `⟨s, hs, h1, h2⟩` from `hL`. Use `⟨s ^ N, Nat.Coprime.pow_left N hs, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Unfold `detId at hx`.

Use `Submodule.span_induction (p := fun x _ => ((s ^ N : ℕ) : D.host.E) * x ∈ (1 : IdE D)) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `x ⟨A, hA, rfl⟩`. Establish `hsA : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, ((s : D.host.E) • A).mulVec v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`. Introduce `v hv`. Rewrite using `[smul_mulVec']`.

Conclude with `h2 _ (hA v hv)`. Establish `hd` using `det_int_of_std hsA`. Rewrite `hd` using `[Matrix.det_smul, Fintype.card_fin, ← Nat.cast_pow]`. Then use the resulting hypothesis. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `r x _ hx`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r hx`.

Unfold `detId`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨(s : D.host.E) • (1 : Matrix (Fin N) (Fin N) D.host.E), ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Rewrite using `[smul_mulVec', Matrix.one_mulVec]`.

Conclude with `h1 v hv`. Rewrite using `[Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Nat.cast_pow]`.
-/
theorem detOneAt : DetOneAt D := by
  intro p N L hL
  obtain ⟨s, hs, h1, h2⟩ := hL
  refine ⟨s ^ N, Nat.Coprime.pow_left N hs, ?_, ?_⟩
  · intro x hx
    unfold detId at hx
    refine Submodule.span_induction (p := fun x _ => ((s ^ N : ℕ) : D.host.E) * x ∈ (1 : IdE D)) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨A, hA, rfl⟩
      have hsA : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N,
          ((s : D.host.E) • A).mulVec v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
        intro v hv
        rw [smul_mulVec']
        exact h2 _ (hA v hv)
      have hd := det_int_of_std hsA
      rwa [Matrix.det_smul, Fintype.card_fin, ← Nat.cast_pow] at hd
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
    · intro r x _ hx
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hx
  · unfold detId
    apply Submodule.subset_span
    refine ⟨(s : D.host.E) • (1 : Matrix (Fin N) (Fin N) D.host.E), ?_, ?_⟩
    · intro v hv
      rw [smul_mulVec', Matrix.one_mulVec]
      exact h1 v hv
    · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Nat.cast_pow]

/- English proof (translation)
Introduce `χ hχ p _ lam N N' L L' hAdm hL hL'`. Set `_` to `D.host.cmStar`. Take `⟨hN, hN', hsdL, hsdL'⟩` from `hAdm`. Establish `n1 : N1 D (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)` using `relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsdL`. Establish `n1' : N1 D (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L')` using `relative_determinant_norm_one D N' _ _ hN' (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hsdL'`.

Take `⟨m1, u1⟩` from `lemmaU χ hχ p lam _ n1 (detOneAt p N L hL)`. Take `⟨m2, u2⟩` from `lemmaU χ hχ p lam _ n1' (detOneAt p N' L' hL')`. Use `set a : Qbar := ⟨_, m1⟩ with ha`. Use `set b : Qbar := ⟨_, m2⟩ with hb`. Establish `hcf : Base.chiFac χ N N' L L' = ((a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ)) : Qbar) : ℂ)`.

Express the relevant statement in the definitionally equal form `_ = Qbar.val (a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ)))`. Rewrite using `[map_mul, map_zpow₀, map_zpow₀]`. Apply the tactic sequence `try rfl`. Establish `hmem : Base.chiFac χ N N' L L' ∈ Qbar` using `by rw [hcf]; exact Subtype.property _`. Use `⟨hmem, ?_⟩` and prove the remaining obligations.

Establish `hl : lamC lam (Base.chiFac χ N N' L L') = lam (a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ)))`. Simplify using `only [lamC, dif_pos hmem]`. Use `congr 1`. Apply the tactic sequence `try exact Subtype.ext hcf`. Apply the tactic sequence `have hla : lam a = lamC lam (χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)) := by simp only [lamC, dif_pos m1]; try rfl`.

Apply the tactic sequence `have hlb : lam b = lamC lam (χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L')) := by simp only [lamC, dif_pos m2]; try rfl`. Rewrite using `[hl, map_mul, map_zpow₀, map_zpow₀, norm_mul, norm_zpow, norm_zpow, hla, hlb, u1, u2, one_zpow, one_zpow, one_mul]`.
-/
theorem chiFacUnit : ChiFacUnit D := by
  intro χ hχ p _ lam N N' L L' hAdm hL hL'
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hsdL, hsdL'⟩ := hAdm
  have n1 : N1 D (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L) :=
    relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsdL
  have n1' : N1 D (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L') :=
    relative_determinant_norm_one D N' _ _ hN' (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hsdL'
  obtain ⟨m1, u1⟩ := lemmaU χ hχ p lam _ n1 (detOneAt p N L hL)
  obtain ⟨m2, u2⟩ := lemmaU χ hχ p lam _ n1' (detOneAt p N' L' hL')
  set a : Qbar := ⟨_, m1⟩ with ha
  set b : Qbar := ⟨_, m2⟩ with hb
  have hcf : Base.chiFac χ N N' L L' =
      ((a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ)) : Qbar) : ℂ) := by
    change _ = Qbar.val (a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ)))
    rw [map_mul, map_zpow₀, map_zpow₀]
    try rfl
  have hmem : Base.chiFac χ N N' L L' ∈ Qbar := by rw [hcf]; exact Subtype.property _
  refine ⟨hmem, ?_⟩
  have hl : lamC lam (Base.chiFac χ N N' L L') = lam (a ^ (((N' / 2 : ℕ) : ℤ)) * b ^ (-((N / 2 : ℕ) : ℤ))) := by
    simp only [lamC, dif_pos hmem]
    congr 1
    try exact Subtype.ext hcf
  have hla : lam a = lamC lam (χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)) := by simp only [lamC, dif_pos m1]; try rfl
  have hlb : lam b = lamC lam (χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L')) := by simp only [lamC, dif_pos m2]; try rfl
  rw [hl, map_mul, map_zpow₀, map_zpow₀, norm_mul, norm_zpow, norm_zpow, hla, hlb, u1, u2, one_zpow, one_zpow,
    one_mul]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
