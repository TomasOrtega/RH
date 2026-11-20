import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.DirichletDensity.HostDensityArith

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33.HK

open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Conclude with `Prod.ext (Int.units_mul_self _) (Int.units_mul_self _)`.
-/
theorem conjugation_mul_self : c0 * c0 = 1 := by
  exact Prod.ext (Int.units_mul_self _) (Int.units_mul_self _)

/- English proof (translation)
Conclude with `Prod.ext Formalism.MainNotions.UnusedSlot33.HK.conjugation_mul_self (mul_one _)`.
-/
theorem cc_mul_cc (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  exact Prod.ext Formalism.MainNotions.UnusedSlot33.HK.conjugation_mul_self (mul_one _)

/- English proof (translation)
Conclude with `H.gal.apply_symm_apply g`.
-/
theorem galE_sigmaOf (g : R.GG) :
    H.galE (H.sigmaOf g) = g := by
  exact H.gal.apply_symm_apply g

/- English proof (translation)
Conclude with `H.gal.symm_apply_apply σ`.
-/
theorem sigmaOf_galE (σ : H.E ≃ₐ[ℚ] H.E) :
    H.sigmaOf (H.galE σ) = σ := by
  exact H.gal.symm_apply_apply σ

/- English proof (translation)
Establish `hρ : τ⁻¹ * σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd`. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Establish `hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd)` using `by show IntermediateField.adjoin ℚ {H.sqd} ≤ _`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hf`.

Establish `h1` using `(IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ hρ`. Rewrite `h1` using `[AlgEquiv.mul_apply, AlgEquiv.aut_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem algEquiv_eqOn_K_of_eq_sqd (H : Host R) (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqd = τ H.sqd)
    (x : H.E) (hx : x ∈ H.K) : σ x = τ x := by
  have hρ : τ⁻¹ * σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd := by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.mul_apply, h,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    show IntermediateField.adjoin ℚ {H.sqd} ≤ _
    rw [IntermediateField.adjoin_simple_le_iff]
    exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hf
  have h1 := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ hρ
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h1
  calc σ x = τ (τ.symm (σ x)) := (τ.apply_symm_apply _).symm
    _ = τ x := by rw [h1]

/- English proof (translation)
Establish `h1` using `algEquiv_eqOn_K_of_eq_sqd H σ 1 (by rw [H.gal_sqd, h, AlgEquiv.one_apply]; simp) x hx`. Rewrite `h1` using `[AlgEquiv.one_apply]`. Then use the resulting hypothesis.
-/
private theorem algEquiv_fix_K_of_gal_eq_one (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E) (h : (H.gal σ).1.2 = 1)
    (x : H.E) (hx : x ∈ H.K) : σ x = x := by
  have h1 := algEquiv_eqOn_K_of_eq_sqd H σ 1 (by rw [H.gal_sqd, h, AlgEquiv.one_apply]; simp) x hx
  rwa [AlgEquiv.one_apply] at h1

/- English proof (translation)
Establish `hk : R.toFrame.chD g = 1` using `MonoidHom.mem_ker.1 (show g ∈ R.toFrame.chD.ker from hg)`. Establish `hg' : g.1.2 = 1` using `by simpa [Formalism.HC.Frame.chD] using hk`. Use `algEquiv_fix_K_of_gal_eq_one H (H.sigmaOf g) ?_ x hx` and prove the remaining obligations. Rewrite using `[show H.gal (H.sigmaOf g) = g from H.gal.apply_symm_apply g]`. Conclude with `hg'`.
-/
theorem sigmaOf_fix_K (g : R.GG) (hg : g ∈ R.Psi) (x : H.E) (hx : x ∈ H.K) :
    H.sigmaOf g x = x := by
  have hk : R.toFrame.chD g = 1 := MonoidHom.mem_ker.1 (show g ∈ R.toFrame.chD.ker from hg)
  have hg' : g.1.2 = 1 := by simpa [Formalism.HC.Frame.chD] using hk
  refine algEquiv_fix_K_of_gal_eq_one H (H.sigmaOf g) ?_ x hx
  rw [show H.gal (H.sigmaOf g) = g from H.gal.apply_symm_apply g]
  exact hg'

/- English proof (translation)
Use `show H.conj H.sqd = - H.sqd`. Rewrite using `[H.gal_sqd, show H.gal H.conj = R.cc from H.gal.apply_symm_apply _]`. Simplify using `[Formalism.HC.Frame.cc, c0]`.
-/
theorem conj_b : H.conj H.sqrtMinusD = - H.sqrtMinusD := by
  show H.conj H.sqd = - H.sqd
  rw [H.gal_sqd, show H.gal H.conj = R.cc from H.gal.apply_symm_apply _]
  simp [Formalism.HC.Frame.cc, c0]

/- English proof (translation)
Take `⟨-, hd, -⟩` from `H.hyp`. Conclude with `Real.sqrt_pos.2 (by exact_mod_cast hd.pos)`.
-/
theorem sqrt_d_pos : 0 < Real.sqrt H.d := by
  obtain ⟨-, hd, -⟩ := H.hyp
  exact Real.sqrt_pos.2 (by exact_mod_cast hd.pos)

/- English proof (translation)
Take `⟨-, hd, -⟩` from `H.hyp`. Introduce `h`. Establish `h2` using `H.sqd_sq`. Express the relevant statement in the definitionally equal form `H.sqd = 0 at h`. Rewrite `h2` using `[h]`.

Establish `h3 : H.d = 0` using `by simpa using h2`. Conclude with `hd.ne_zero h3`.
-/
theorem b_ne_zero : H.sqrtMinusD ≠ 0 := by
  obtain ⟨-, hd, -⟩ := H.hyp
  intro h
  have h2 := H.sqd_sq
  change H.sqd = 0 at h
  rw [h] at h2
  have h3 : H.d = 0 := by simpa using h2
  exact hd.ne_zero h3

/- English proof (translation)
Establish `h : H.conj * H.conj = 1`. Apply `H.gal.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, show H.gal H.conj = R.cc from H.gal.apply_symm_apply _]`. Conclude with `Formalism.MainNotions.UnusedSlot33.HK.cc_mul_cc R.toFrame`. Rewrite using `[← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]`.
-/
theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  have h : H.conj * H.conj = 1 := by
    apply H.gal.injective
    rw [map_mul, map_one, show H.gal H.conj = R.cc from H.gal.apply_symm_apply _]
    exact Formalism.MainNotions.UnusedSlot33.HK.cc_mul_cc R.toFrame
  rw [← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]

def DiffKH (H : Host R) : Prop :=
  ∃ β : 𝓞 H.E, (β : H.E) = H.sqrtMinusD ∧
    (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = Ideal.span {β}

def NormKH (H : Host R) : Prop :=
  ∀ cc : Ideal (𝓞 H.K), cc ≠ ⊥ →
    Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
      (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)}

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `h1 : Ideal.absNorm M = 1`. Establish `h2` using `congrArg Ideal.absNorm hM`. Rewrite `h2` using `[map_mul, ← h]`. Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (h2.symm.trans (mul_one _).symm)`.

Rewrite `h1` using `[Ideal.absNorm_eq_one_iff]`. Rewrite using `[hM, h1, Ideal.mul_top]`.
-/
theorem eq_of_le_of_absNorm_eq {K : Type*} [Field K] [NumberField K] {I J : Ideal (𝓞 K)}
    (hle : I ≤ J) (hI : Ideal.absNorm I ≠ 0) (h : Ideal.absNorm I = Ideal.absNorm J) : I = J := by
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have h1 : Ideal.absNorm M = 1 := by
    have h2 := congrArg Ideal.absNorm hM
    rw [map_mul, ← h] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (h2.symm.trans (mul_one _).symm)
  rw [Ideal.absNorm_eq_one_iff] at h1
  rw [hM, h1, Ideal.mul_top]

/- English proof (translation)
Establish `hdisc : discr K = a` using `Formalism.HF.quadDiscr K a x hx hadj hsf h4`. Establish `ha0 : a ≠ 0` using `hsf.ne_zero`. Establish `hirr : Irreducible (X ^ 2 - C (a : ℚ))` using `X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)`. Establish `hmon : (X ^ 2 - C (a : ℚ)).Monic` using `monic_X_pow_sub_C _ two_ne_zero`. Establish `hev : aeval x (X ^ 2 - C (a : ℚ)) = 0` using `by simp [hx]`.

Establish `hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ)` using `(minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm`. Establish `hrank : Module.finrank ℚ K = 2`. Use `IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)` as an intermediate fact. Rewrite `this` using `[hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top']`. Conclude with `this`.

Take `⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1` from `⟨a / 4, by omega⟩`. Establish `hcK : (a : K) = 4 * c + 1` using `by rw [hc]; push_cast; ring`. Take `⟨ω, hω⟩ : ∃ ω : K, ω = (1 + x) / 2` from `⟨_, rfl⟩`. Establish `hrelK : ω ^ 2 - ω - (c : K) = 0`. Rewrite using `[hω]`.

Take the linear combination `(1 / 4 : K) * hx + (1 / 4 : K) * hcK`. Establish `hωint : IsIntegral ℤ ω`. Use `⟨X ^ 2 - X - C c, by monicity!, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast]`. Conclude with `hrelK`.

Take `⟨ω', hω'⟩ : ∃ ω' : 𝓞 K, algebraMap (𝓞 K) K ω' = ω` from `⟨⟨ω, hωint⟩, rfl⟩`. Establish `hxω : x = 2 * ω - 1` using `by rw [hω]; ring`. Establish `hadjω : IntermediateField.adjoin ℚ {ω} = ⊤`. Rewrite using `[eq_top_iff, ← hadj, IntermediateField.adjoin_simple_le_iff, hxω]`. Establish `hm` using `IntermediateField.mem_adjoin_simple_self ℚ ω`.

Conclude with `sub_mem (mul_mem (ofNat_mem _ 2) hm) (one_mem _)`. Establish `hdeg : (minpoly ℚ ω).natDegree = 2`. Use `IntermediateField.adjoin.finrank (K := ℚ) (x := ω) (.of_finite ℚ ω)` as an intermediate fact. Rewrite `this` using `[hadjω, IntermediateField.finrank_top', hrank]`. Conclude with `this.symm`.

Establish `hint' : IsIntegral ℤ ω'` using `RingOfIntegers.isIntegral ω'`. Establish `hdegZ : (minpoly ℤ ω').natDegree = 2`. Establish `hmap` using `minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint'`. Rewrite `hmap` using `[hω']`. Rewrite using `[← (minpoly.monic hint').natDegree_map (algebraMap ℤ ℚ), ← hmap]`.

Conclude with `hdeg`. Establish `hPmon : (X ^ 2 - X - C c : ℤ[X]).Monic` using `by monicity!`. Establish `hPdeg : (X ^ 2 - X - C c : ℤ[X]).natDegree = 2` using `by compute_degree!`. Establish `hrel : ω' ^ 2 - ω' - (c : 𝓞 K) = 0`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Simplify using `only [map_sub, map_pow, map_intCast, map_zero, hω']`. Conclude with `hrelK`. Establish `hP : (X ^ 2 - X - C c : ℤ[X]) = minpoly ℤ ω'`. Use `minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly hPmon ?_ ?_` and prove the remaining obligations. Simplify using `using hrel`.

Rewrite using `[degree_eq_natDegree hPmon.ne_zero, degree_eq_natDegree (minpoly.ne_zero hint'), hPdeg, hdegZ]`. Establish `hAdj : Algebra.adjoin ℚ {algebraMap (𝓞 K) K ω'} = ⊤`. Use `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (α := ω) (Algebra.IsAlgebraic.isAlgebraic ω)` as an intermediate fact. Rewrite `this` using `[hadjω, IntermediateField.top_toSubalgebra]`. Rewrite using `[hω']`.

Conclude with `this.symm`. Establish `hmem` using `aeval_derivative_mem_differentIdeal ℤ ℚ K ω' hAdj`. Rewrite `hmem` using `[← hP]`. Establish `hder : derivative (X ^ 2 - X - C c : ℤ[X]) = C 2 * X - 1`. Rewrite using `[derivative_sub, derivative_sub, derivative_X_pow, derivative_X, derivative_C, sub_zero]`.

Evaluate the numerical expressions. Establish `hx'' : x' = 2 * ω' - 1`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show algebraMap (𝓞 K) K x' = algebraMap (𝓞 K) K (2 * ω' - 1)`. Rewrite using `[map_sub, map_mul, map_one, hω', map_ofNat]`.

Conclude with `hx'.trans hxω`. Establish `hval : aeval ω' (derivative (X ^ 2 - X - C c : ℤ[X])) = x'`. Rewrite using `[hder, hx'', map_sub, map_mul, aeval_C, aeval_X, map_one]`. Simplify using the standard rewrite rules. Rewrite `hmem` using `[hval]`.

Establish `hle : Ideal.span {x'} ≤ differentIdeal ℤ (𝓞 K)` using `(Ideal.span_singleton_le_iff_mem _).2 hmem`. Establish `hn : (Algebra.norm ℤ x') ^ 2 = a ^ 2`. Establish `: ((Algebra.norm ℤ x' : ℤ) : ℚ) ^ 2 = (a : ℚ) ^ 2`. Rewrite using `[Algebra.coe_norm_int, hx', ← map_pow, hx, show ((a : ℤ) : K) = algebraMap ℚ K a by simp, Algebra.norm_algebraMap, hrank]`. Conclude with `this` after adjusting the coercions.

Establish `hN1 : Ideal.absNorm (Ideal.span {x'}) = a.natAbs`. Rewrite using `[Ideal.absNorm_span_singleton]`. Conclude with `Int.natAbs_eq_iff_sq_eq.2 hn`. Establish `hN2 : Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = a.natAbs`. Rewrite using `[NumberField.absNorm_differentIdeal K (𝓞 K), hdisc]`.

Conclude with `(eq_of_le_of_absNorm_eq hle (by rw [hN1]; exact Int.natAbs_ne_zero.2 ha0) (hN1.trans hN2.symm)).symm`.
-/
theorem different_quad (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) (x' : 𝓞 K) (hx' : (x' : K) = x) :
    differentIdeal ℤ (𝓞 K) = Ideal.span {x'} := by
  have hdisc : discr K = a := Formalism.HF.quadDiscr K a x hx hadj hsf h4
  have ha0 : a ≠ 0 := hsf.ne_zero
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = (1 + x) / 2 := ⟨_, rfl⟩
  have hrelK : ω ^ 2 - ω - (c : K) = 0 := by
    rw [hω]
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, by monicity!, ?_⟩
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast]
    exact hrelK
  obtain ⟨ω', hω'⟩ : ∃ ω' : 𝓞 K, algebraMap (𝓞 K) K ω' = ω := ⟨⟨ω, hωint⟩, rfl⟩
  have hxω : x = 2 * ω - 1 := by rw [hω]; ring
  have hadjω : IntermediateField.adjoin ℚ {ω} = ⊤ := by
    rw [eq_top_iff, ← hadj, IntermediateField.adjoin_simple_le_iff, hxω]
    have hm := IntermediateField.mem_adjoin_simple_self ℚ ω
    exact sub_mem (mul_mem (ofNat_mem _ 2) hm) (one_mem _)
  have hdeg : (minpoly ℚ ω).natDegree = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := ω) (.of_finite ℚ ω)
    rw [hadjω, IntermediateField.finrank_top', hrank] at this
    exact this.symm
  have hint' : IsIntegral ℤ ω' := RingOfIntegers.isIntegral ω'
  have hdegZ : (minpoly ℤ ω').natDegree = 2 := by
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint'
    rw [hω'] at hmap
    rw [← (minpoly.monic hint').natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact hdeg
  have hPmon : (X ^ 2 - X - C c : ℤ[X]).Monic := by monicity!
  have hPdeg : (X ^ 2 - X - C c : ℤ[X]).natDegree = 2 := by compute_degree!
  have hrel : ω' ^ 2 - ω' - (c : 𝓞 K) = 0 := by
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, map_intCast, map_zero, hω']
    exact hrelK
  have hP : (X ^ 2 - X - C c : ℤ[X]) = minpoly ℤ ω' := by
    refine minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly hPmon ?_ ?_
    · simpa using hrel
    · rw [degree_eq_natDegree hPmon.ne_zero, degree_eq_natDegree (minpoly.ne_zero hint'), hPdeg,
        hdegZ]
  have hAdj : Algebra.adjoin ℚ {algebraMap (𝓞 K) K ω'} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (α := ω)
      (Algebra.IsAlgebraic.isAlgebraic ω)
    rw [hadjω, IntermediateField.top_toSubalgebra] at this
    rw [hω']
    exact this.symm
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K ω' hAdj
  rw [← hP] at hmem
  have hder : derivative (X ^ 2 - X - C c : ℤ[X]) = C 2 * X - 1 := by
    rw [derivative_sub, derivative_sub, derivative_X_pow, derivative_X, derivative_C, sub_zero]
    norm_num
  have hx'' : x' = 2 * ω' - 1 := by
    apply RingOfIntegers.coe_injective
    show algebraMap (𝓞 K) K x' = algebraMap (𝓞 K) K (2 * ω' - 1)
    rw [map_sub, map_mul, map_one, hω', map_ofNat]
    exact hx'.trans hxω
  have hval : aeval ω' (derivative (X ^ 2 - X - C c : ℤ[X])) = x' := by
    rw [hder, hx'', map_sub, map_mul, aeval_C, aeval_X, map_one]
    simp
  rw [hval] at hmem
  have hle : Ideal.span {x'} ≤ differentIdeal ℤ (𝓞 K) :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  have hn : (Algebra.norm ℤ x') ^ 2 = a ^ 2 := by
    have : ((Algebra.norm ℤ x' : ℤ) : ℚ) ^ 2 = (a : ℚ) ^ 2 := by
      rw [Algebra.coe_norm_int, hx', ← map_pow, hx, show ((a : ℤ) : K) = algebraMap ℚ K a by simp,
        Algebra.norm_algebraMap, hrank]
    exact_mod_cast this
  have hN1 : Ideal.absNorm (Ideal.span {x'}) = a.natAbs := by
    rw [Ideal.absNorm_span_singleton]
    exact Int.natAbs_eq_iff_sq_eq.2 hn
  have hN2 : Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = a.natAbs := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), hdisc]
  exact (eq_of_le_of_absNorm_eq hle (by rw [hN1]; exact Int.natAbs_ne_zero.2 ha0)
    (hN1.trans hN2.symm)).symm

/- English proof (translation)
Apply `IntermediateField.map_injective (IsScalarTower.toAlgHom ℚ H.K H.E)` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_map, Set.image_singleton]`. Use `first`. Consider the case `rw [IntermediateField.map_top]`. Consider the case `rw [← AlgHom.fieldRange_eq_map]`.

Use extensionality with `z`. Rewrite using `[AlgHom.mem_fieldRange]`. Establish `h1 : IsScalarTower.toAlgHom ℚ H.K H.E x = H.sqd` using `hx`. Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Conclude with `⟨⟨z, hz⟩, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.
-/
theorem gen_top (H : Host R) (x : H.K) (hx : (x : H.E) = H.sqd) :
    IntermediateField.adjoin ℚ {x} = ⊤ := by
  apply IntermediateField.map_injective (IsScalarTower.toAlgHom ℚ H.K H.E)
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  first
  | rw [IntermediateField.map_top]
  | rw [← AlgHom.fieldRange_eq_map]
  ext z
  rw [AlgHom.mem_fieldRange]
  have h1 : IsScalarTower.toAlgHom ℚ H.K H.E x = H.sqd := hx
  rw [h1]
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/- English proof (translation)
Take `⟨-, hd, -, hd16, -⟩` from `H.hyp`. Establish `hmem : H.sqd ∈ H.K` using `IntermediateField.mem_adjoin_simple_self ℚ H.sqd`. Establish `hx2 : (⟨H.sqd, hmem⟩ : H.K) ^ 2 = -(H.d : H.K)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[H.sqd_sq]`.

Establish `hint : IsIntegral ℤ (⟨H.sqd, hmem⟩ : H.K)`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hx2]`. Simplify using the standard rewrite rules. Establish `hint' : (⟨H.sqd, hmem⟩ : H.K) ∈ integralClosure ℤ H.K` using `(mem_integralClosure_iff ℤ _).2 hint`.

Establish `hdiff` using `Formalism.MainNotions.UnusedSlot33.HK.different_quad H.K (-(H.d : ℤ)) ⟨H.sqd, hmem⟩ (by rw [hx2]; simp) (Formalism.MainNotions.UnusedSlot33.HK.gen_top H _ rfl) (Int.squarefree_natAbs.1 (by simpa using Irreducible.squarefree hd)) (by omega) (by omega) ⟨⟨H.sqd, hmem⟩, hint'⟩ rfl`. Use `⟨algebraMap (𝓞 H.K) (𝓞 H.E) ⟨⟨H.sqd, hmem⟩, hint'⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hdiff, Ideal.map_span]`. Conclude with `congrArg Ideal.span Set.image_singleton`.
-/
theorem diffK_holds (H : Host R) : DiffKH H := by
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hmem : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx2 : (⟨H.sqd, hmem⟩ : H.K) ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simp [H.sqd_sq]
  have hint : IsIntegral ℤ (⟨H.sqd, hmem⟩ : H.K) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hx2]
    simp
  have hint' : (⟨H.sqd, hmem⟩ : H.K) ∈ integralClosure ℤ H.K := (mem_integralClosure_iff ℤ _).2 hint
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad H.K (-(H.d : ℤ)) ⟨H.sqd, hmem⟩ (by rw [hx2]; simp)
    (Formalism.MainNotions.UnusedSlot33.HK.gen_top H _ rfl)
    (Int.squarefree_natAbs.1 (by simpa using Irreducible.squarefree hd)) (by omega) (by omega)
    ⟨⟨H.sqd, hmem⟩, hint'⟩ rfl
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) ⟨⟨H.sqd, hmem⟩, hint'⟩, rfl, ?_⟩
  rw [hdiff, Ideal.map_span]
  exact congrArg Ideal.span Set.image_singleton

/- English proof (translation)
Break down `Int.units_eq_one_or (H.gal σ).1.2 with h | h` into its components or cases. Conclude with `Or.inl (fun x hx => algEquiv_fix_K_of_gal_eq_one H σ h x hx)`. Use `Or.inr (fun x hx => algEquiv_eqOn_K_of_eq_sqd H σ H.conj ?_ x hx)` and prove the remaining obligations. Establish `hc` using `Formalism.MainNotions.UnusedSlot33.HK.conj_b H`. Express the relevant statement in the definitionally equal form `H.conj H.sqd = - H.sqd at hc`.

Rewrite using `[H.gal_sqd, h, hc]`. Simplify using the standard rewrite rules.
-/
theorem cases_K (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x ∈ H.K, σ x = x) ∨ (∀ x ∈ H.K, σ x = H.conj x) := by
  rcases Int.units_eq_one_or (H.gal σ).1.2 with h | h
  · exact Or.inl (fun x hx => algEquiv_fix_K_of_gal_eq_one H σ h x hx)
  · refine Or.inr (fun x hx => algEquiv_eqOn_K_of_eq_sqd H σ H.conj ?_ x hx)
    have hc := Formalism.MainNotions.UnusedSlot33.HK.conj_b H
    change H.conj H.sqd = - H.sqd at hc
    rw [H.gal_sqd, h, hc]
    simp

/- English proof (translation)
The claim follows from `IntermediateField.mem_adjoin_simple_self ℚ H.sqd`.
-/
theorem bE_mem : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd

/- English proof (translation)
Use `haveI : IsGalois ℚ H.E := H.galois`. Use `haveI hn : (IntermediateField.fixingSubgroup H.K).Normal := by`. Prove the components needed by the constructor for the conclusion. Introduce `n hn g`. Establish `hc : g * n * g⁻¹ = n` using `H.gal.injective (by`.

Rewrite using `[map_mul, map_mul, map_inv, mul_comm (H.gal g) (H.gal n), mul_inv_cancel_right])`. Rewrite using `[hc]`. Conclude with `hn`. Establish `h1` using `IsGalois.of_fixedField_normal_subgroup (IntermediateField.fixingSubgroup H.K)`. Rewrite `h1` using `[IsGalois.fixedField_fixingSubgroup]`.

Conclude with `h1`.
-/
theorem isGalK : IsGalois ℚ H.K := by
  haveI : IsGalois ℚ H.E := H.galois
  haveI hn : (IntermediateField.fixingSubgroup H.K).Normal := by
    constructor
    intro n hn g
    have hc : g * n * g⁻¹ = n := H.gal.injective (by
      rw [map_mul, map_mul, map_inv, mul_comm (H.gal g) (H.gal n), mul_inv_cancel_right])
    rw [hc]
    exact hn
  have h1 := IsGalois.of_fixedField_normal_subgroup (IntermediateField.fixingSubgroup H.K)
  rw [IsGalois.fixedField_fixingSubgroup] at h1
  exact h1

/- English proof (translation)
Establish `hG` using `isGalK H`. Establish `hE` using `H.hostE_isGalois`. Take `⟨cK, hcK⟩ : ∃ cK : Gal(H.K/ℚ), cK = H.conj.restrictNormal H.K` from `⟨_, rfl⟩`. Establish `hcK' : ∀ y : H.K, ((cK y : H.K) : H.E) = H.conj (y : H.E)`. Introduce `y`.

Rewrite using `[hcK]`. Conclude with `AlgEquiv.restrictNormal_commutes H.conj H.K y`. Establish `hne : (1 : Gal(H.K/ℚ)) ≠ cK`. Introduce `h1`. Establish `h2` using `hcK' ⟨_, bE_mem H⟩`.

Rewrite `h2` using `[← h1]`. Express the relevant statement in the definitionally equal form `H.sqd = _ at h2`. Rewrite `h2` using `[show H.conj (H.sqd) = - H.sqd from conj_b H]`. Establish `h3 : (2 : H.E) * H.sqd = 0` using `by linear_combination h2`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases.

Conclude with `two_ne_zero h4`. Conclude with `b_ne_zero H h4`. Establish `huniv : (Finset.univ : Finset Gal(H.K/ℚ)) = {1, cK}`. Use `symm`. Rewrite using `[Finset.eq_univ_iff_forall]`.

Introduce `τ`. Take `⟨σ, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective H.E τ`. Rewrite using `[Finset.mem_insert, Finset.mem_singleton]`. Break down `cases_K H σ with h | h` into its components or cases. Use `left`.

Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `y`. Apply `Subtype.ext` to reduce the goal to its premises. Use `AlgEquiv.restrictNormal_commutes σ H.K y` as an intermediate fact. Conclude with `this.trans (h _ y.2)`.

Use `right`. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `y`. Apply `Subtype.ext` to reduce the goal to its premises. Use `AlgEquiv.restrictNormal_commutes σ H.K y` as an intermediate fact.

Conclude with `(this.trans (h _ y.2)).trans (hcK' y).symm`. Establish `h` using `Algebra.norm_eq_prod_automorphisms ℚ x`. Rewrite `h` using `[huniv, Finset.prod_pair hne]`. Establish `h2` using `congrArg (fun z : H.K => (z : H.E)) h`. Rewrite using `[← hcK' x]`.

Conclude with `h2`.
-/
theorem norm_K (x : H.K) :
    algebraMap ℚ H.E (Algebra.norm ℚ x) = (x : H.E) * H.conj (x : H.E) := by
  classical
  have hG := isGalK H
  have hE := H.hostE_isGalois
  obtain ⟨cK, hcK⟩ : ∃ cK : Gal(H.K/ℚ), cK = H.conj.restrictNormal H.K := ⟨_, rfl⟩
  have hcK' : ∀ y : H.K, ((cK y : H.K) : H.E) = H.conj (y : H.E) := by
    intro y
    rw [hcK]
    exact AlgEquiv.restrictNormal_commutes H.conj H.K y
  have hne : (1 : Gal(H.K/ℚ)) ≠ cK := by
    intro h1
    have h2 := hcK' ⟨_, bE_mem H⟩
    rw [← h1] at h2
    change H.sqd = _ at h2
    rw [show H.conj (H.sqd) = - H.sqd from conj_b H] at h2
    have h3 : (2 : H.E) * H.sqd = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact b_ne_zero H h4
  have huniv : (Finset.univ : Finset Gal(H.K/ℚ)) = {1, cK} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective H.E τ
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases cases_K H σ with h | h
    · left
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext
      have := AlgEquiv.restrictNormal_commutes σ H.K y
      exact this.trans (h _ y.2)
    · right
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext
      have := AlgEquiv.restrictNormal_commutes σ H.K y
      exact (this.trans (h _ y.2)).trans (hcK' y).symm
  have h := Algebra.norm_eq_prod_automorphisms ℚ x
  rw [huniv, Finset.prod_pair hne] at h
  have h2 := congrArg (fun z : H.K => (z : H.E)) h
  rw [← hcK' x]
  exact h2

/- English proof (translation)
Rewrite using `[← norm_K H (x : H.K), ← Algebra.coe_norm_int, Algebra.intNorm_eq_norm, map_intCast]`.
-/
theorem norm_int (x : 𝓞 H.K) :
    ((Algebra.intNorm ℤ (𝓞 H.K) x : ℤ) : H.E) =
      ((x : H.K) : H.E) * H.conj ((x : H.K) : H.E) := by
  rw [← norm_K H (x : H.K), ← Algebra.coe_norm_int, Algebra.intNorm_eq_norm, map_intCast]

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `h1 : Ideal.relNorm ℤ cc ≤ Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc * (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc))`. Rewrite using `[Ideal.relNorm_apply, Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Ideal.mem_comap.2 ?_` and prove the remaining obligations.

Establish `h2 : algebraMap ℤ (𝓞 H.E) (Algebra.intNorm ℤ (𝓞 H.K) x) = algebraMap (𝓞 H.K) (𝓞 H.E) x * (H.conj • algebraMap (𝓞 H.K) (𝓞 H.E) x)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h3` using `norm_int H x`. Rewrite using `[eq_intCast]`. Use `push_cast`.

Conclude with `h3`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hx) (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hx))`. Establish `h3 : ((Ideal.absNorm cc : ℕ) : ℤ) ∈ Ideal.relNorm ℤ cc`. Rewrite using `[Ideal.relNorm_int]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `h4` using `h1 h3`. Rewrite `h4` using `[Ideal.mem_comap]`. Simplify using `using h4`.
-/
theorem span_le (cc : Ideal (𝓞 H.K)) :
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} ≤
      Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
        (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc) := by
  rw [Ideal.span_singleton_le_iff_mem]
  have h1 : Ideal.relNorm ℤ cc ≤ Ideal.comap (algebraMap ℤ (𝓞 H.E))
      (Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
        (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc)) := by
    rw [Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Ideal.mem_comap.2 ?_
    have h2 : algebraMap ℤ (𝓞 H.E) (Algebra.intNorm ℤ (𝓞 H.K) x) =
        algebraMap (𝓞 H.K) (𝓞 H.E) x *
          (H.conj • algebraMap (𝓞 H.K) (𝓞 H.E) x) := by
      apply RingOfIntegers.coe_injective
      have h3 := norm_int H x
      rw [eq_intCast]
      push_cast
      exact h3
    rw [h2]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hx)
      (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hx))
  have h3 : ((Ideal.absNorm cc : ℕ) : ℤ) ∈ Ideal.relNorm ℤ cc := by
    rw [Ideal.relNorm_int]
    exact Ideal.mem_span_singleton_self _
  have h4 := h1 h3
  rw [Ideal.mem_comap] at h4
  simpa using h4

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv I (H.conj • I) (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj) rfl).toEquiv.symm`.
-/
theorem absNorm_smul (I : Ideal (𝓞 H.E)) :
    Ideal.absNorm (H.conj • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (H.conj • I)
    (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj) rfl).toEquiv.symm

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `h : (Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) = (N : ℤ) ^ 2`. Establish `h1` using `norm_int H (N : 𝓞 H.K)`. Rewrite `h1` using `[Algebra.intNorm_eq_norm]`. Simplify using `only [map_natCast] at h1`.

Establish `h2 : ((Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) : H.E) = (((N : ℤ) ^ 2 : ℤ) : H.E)`. Rewrite using `[h1]`. Use `push_cast`. Rewrite using `[map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h2` after adjusting the coercions. Rewrite using `[h, Int.natAbs_pow, Int.natAbs_natCast]`.
-/
theorem absNorm_natK (N : ℕ) : Ideal.absNorm (Ideal.span {(N : 𝓞 H.K)}) = N ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) = (N : ℤ) ^ 2 := by
    have h1 := norm_int H (N : 𝓞 H.K)
    rw [Algebra.intNorm_eq_norm] at h1
    simp only [map_natCast] at h1
    have h2 : ((Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) : H.E) = (((N : ℤ) ^ 2 : ℤ) : H.E) := by
      rw [h1]
      push_cast
      rw [map_natCast]
      ring
    exact_mod_cast h2
  rw [h, Int.natAbs_pow, Int.natAbs_natCast]

/- English proof (translation)
Introduce `cc hcc`. Establish `hN : Ideal.absNorm cc ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hcc`. Establish `e1 : Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} = Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.K)})`.

Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `e2 : Ideal.absNorm (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)}) = (Ideal.absNorm cc ^ 2) ^ Module.finrank (𝓞 H.K) (𝓞 H.E)`. Rewrite using `[e1, Ideal.absNorm_algebraMap, absNorm_natK]`. Use `symm`. Apply `eq_of_le_of_absNorm_eq (span_le H cc)` to reduce the goal to its premises.

Rewrite using `[e2]`. Conclude with `pow_ne_zero _ (pow_ne_zero _ hN)`. Rewrite using `[e2, map_mul, absNorm_smul, Ideal.absNorm_algebraMap]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normK_holds (H : Host R) : NormKH H := by
  intro cc hcc
  have hN : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcc
  have e1 : Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} =
      Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E))
        (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.K)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have e2 : Ideal.absNorm (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)}) =
      (Ideal.absNorm cc ^ 2) ^ Module.finrank (𝓞 H.K) (𝓞 H.E) := by
    rw [e1, Ideal.absNorm_algebraMap, absNorm_natK]
  symm
  apply eq_of_le_of_absNorm_eq (span_le H cc)
  · rw [e2]
    exact pow_ne_zero _ (pow_ne_zero _ hN)
  · rw [e2, map_mul, absNorm_smul, Ideal.absNorm_algebraMap]
    ring

end Formalism.MainNotions.UnusedSlot33.HK

end
