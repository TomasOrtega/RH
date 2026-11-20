import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.DefectSumCompare

/- English proof (translation)
Establish `hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E))` using `mem_nonZeroDivisors_of_ne_zero hI`. Use `set h := Fintype.card (ClassGroup (𝓞 E)) with hh`. Establish `hpos : h ≠ 0` using `Fintype.card_ne_zero`. Establish `hprin : (I ^ h).IsPrincipal`. Establish `h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1` using `by rw [map_pow, pow_card_eq_one]`.

Conclude with `(ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1`. Take `⟨x, hx⟩` from `hprin`. Establish `hx' : I ^ h = Ideal.span {x}` using `hx`. Establish `hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h`. Introduce `σ`.

Establish `: σ • (I ^ h) = I ^ h` using `by rw [smul_pow', hfix]`. Rewrite using `[← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Establish `h1` using `Algebra.norm_eq_prod_automorphisms ℚ (x : E)`. Rewrite `h1` using `[← Algebra.coe_norm_int]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _`. Rewrite using `[map_prod, map_intCast]`. Rewrite `h1` using `[map_intCast]`.

Conclude with `h1`. Establish `h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h`. Rewrite using `[Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]`. Establish `h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} = Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)}`. Break down `Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4` into its components or cases.

Use `conv_rhs => rw [h4]`. Rewrite using `[Int.cast_natCast]`. Use `conv_rhs => rw [h4]`. Rewrite using `[Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]`. Rewrite using `[h3, hnorm, ← Ideal.prod_span_singleton]`.

Simplify using `only [hσ]`. Rewrite using `[Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, ← pow_mul, ← pow_mul, mul_comm]`. Conclude with `(pow_left_injective hpos h2).symm`.
-/
theorem pow_finrank_eq_span_absNorm {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by
  classical
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h := by
    intro σ
    have : σ • (I ^ h) = I ^ h := by rw [smul_pow', hfix]
    rw [← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
    apply RingOfIntegers.ext
    have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : E)
    rw [← Algebra.coe_norm_int] at h1
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_prod, map_intCast]
    rw [map_intCast] at h1
    exact h1
  have h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h := by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    have h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} =
        Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)} := by
      rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
      · conv_rhs => rw [h4]
        rw [Int.cast_natCast]
      · conv_rhs => rw [h4]
        rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
    rw [h3, hnorm, ← Ideal.prod_span_singleton]
    simp only [hσ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_left_injective hpos h2).symm

/- English proof (translation)
Unfold `ord_vw vla`. Rewrite using `[Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]`.
-/
theorem ord_vw_eq_vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ord_vw la I = vla la I := by
  classical
  unfold ord_vw vla
  rw [Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]

/- English proof (translation)
Unfold `lrd lrdOf`. Rewrite using `[rootDiscr_def, one_div, Int.cast_abs]`.
-/
theorem lrd_eq_lrdOf (E : Type) [Field E] [NumberField E] : lrd E = lrdOf E := by
  unfold lrd lrdOf
  rw [rootDiscr_def, one_div, Int.cast_abs]

/- English proof (translation)
Establish `hd : (0 : ℝ) < |((discr E : ℤ) : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))`. Establish `hn : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Rewrite using `[lrd_eq_lrdOf]`. Unfold `lrdOf`. Rewrite using `[Real.log_rpow hd]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem log_discr_eq (E : Type) [Field E] [NumberField E] :
    Real.log |((discr E : ℤ) : ℝ)| = (Module.finrank ℚ E : ℝ) * lrd E := by
  have hd : (0 : ℝ) < |((discr E : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [lrd_eq_lrdOf]
  unfold lrdOf
  rw [Real.log_rpow hd]
  field_simp

/- English proof (translation)
Unfold `conjDifferent discAt`. Rewrite using `[← Ideal.map_pow, pow_finrank_eq_span_absNorm _ differentIdeal_ne_bot ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal, absNorm_differentIdeal E, Ideal.map_span, Set.image_singleton, map_natCast]`.
-/
theorem conjDifferent_pow {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ^ Module.finrank ℚ E = discAt E K := by
  unfold conjDifferent discAt
  rw [← Ideal.map_pow, pow_finrank_eq_span_absNorm _ differentIdeal_ne_bot
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal, absNorm_differentIdeal E, Ideal.map_span,
    Set.image_singleton, map_natCast]

/- English proof (translation)
Unfold `vla`. Rewrite using `[Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]`.
-/
theorem vla_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (k : ℕ) : vla la (I ^ k) = k * vla la I := by
  unfold vla
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]

section Galois

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]`.
-/
theorem vla_discAt (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by
  rw [← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]

/- English proof (translation)
Establish `h : mOf E ((n' : ℕ) ^ Module.finrank ℚ E) la = Module.finrank ℚ E * max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}))`. Unfold `mOf`. Rewrite using `[vla_discAt σ, Nat.cast_pow, ← Ideal.span_singleton_pow, vla_pow la (span_natCast_ne_bot n'), ord_vw_eq_vla la (span_natCast_ne_bot n'), Nat.mul_max_mul_left]`. Unfold `beOf defectAt_vw`. Rewrite using `[h]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_mul_defectAt (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defectAt_vw σ n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  have h : mOf E ((n' : ℕ) ^ Module.finrank ℚ E) la = Module.finrank ℚ E *
      max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)})) := by
    unfold mOf
    rw [vla_discAt σ, Nat.cast_pow, ← Ideal.span_singleton_pow, vla_pow la (span_natCast_ne_bot n'),
      ord_vw_eq_vla la (span_natCast_ne_bot n'), Nat.mul_max_mul_left]
  unfold beOf defectAt_vw
  rw [h]
  push_cast
  ring

/- English proof (translation)
Use `le_antisymm (Finset.sup_le fun τ _ => le_of_eq ?_) (defectAt_vw_le σ n' a la)` and prove the remaining obligations. Establish `hn : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Use `(finrank_mul_defectAt τ n' a la).trans (finrank_mul_defectAt σ n' a la).symm` as an intermediate fact. Conclude with `mul_left_cancel₀ hn this` after adjusting the coercions.
-/
theorem defect_vw_eq_defectAt (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defect_vw E n' a la = defectAt_vw σ n' a la := by
  refine le_antisymm (Finset.sup_le fun τ _ => le_of_eq ?_) (defectAt_vw_le σ n' a la)
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have := (finrank_mul_defectAt τ n' a la).trans (finrank_mul_defectAt σ n' a la).symm
  exact_mod_cast mul_left_cancel₀ hn this

/- English proof (translation)
Take `⟨σ⟩` from `hσ`. Rewrite using `[defect_vw_eq_defectAt σ, finrank_mul_defectAt]`.
-/
theorem finrank_mul_defect (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defect_vw E n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  obtain ⟨σ⟩ := hσ
  rw [defect_vw_eq_defectAt σ, finrank_mul_defectAt]

/- English proof (translation)
Use extensionality with `la`. Establish `hn : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Simplify using `only [Function.mem_support, ← finrank_mul_defect hσ, ne_eq, mul_eq_zero, hn, false_or, Nat.cast_eq_zero]`.
-/
theorem support_eq (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ) :
    Function.support (defect_vw E (K := K) n' a) =
      Function.support (beOf E (K := K) ((n' : ℕ) ^ Module.finrank ℚ E) a) := by
  ext la
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [Function.mem_support, ← finrank_mul_defect hσ, ne_eq, mul_eq_zero, hn, false_or,
    Nat.cast_eq_zero]

end Galois

end GlobalTheory.DefectSumCompare
