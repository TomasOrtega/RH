import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Imports

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Rewrite `hx` using `[Valuation.mem_integer_iff]`. Establish `h1 : A.ιF x ≤ᵥ A.ιF 1`. Rewrite using `[map_one, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A.Fp), map_one]`. Conclude with `hx`. Establish `hv : p.valuation F x ≤ 1`.

Use `(A.val x 1).mp h1` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p x hv`. Use `⟨d, d.2, n, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `hnd`.
-/
theorem int_of_val (A : LocAt F E sig p) (x : F) (hx : A.ιF x ∈ 𝒪[A.Fp]) :
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * x = n := by
  rw [Valuation.mem_integer_iff] at hx
  have h1 : A.ιF x ≤ᵥ A.ιF 1 := by
    rw [map_one, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A.Fp), map_one]
    exact hx
  have hv : p.valuation F x ≤ 1 := by
    have := (A.val x 1).mp h1
    rwa [map_one] at this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p x hv
  refine ⟨d, d.2, n, ?_⟩
  rw [mul_comm]
  exact hnd

/- English proof (translation)
Use `A.free` as an intermediate fact. Conclude with `Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)`.
-/
theorem ep_nontrivial (A : LocAt F E sig p) : Nontrivial A.Ep := by
  have := A.free
  exact Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

/- English proof (translation)
Use `haveI := ep_nontrivial A`. Use `haveI := A.free`. Establish `hli : LinearIndependent F ![(1 : E), a]`. Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `c hc`.

Apply `hnot` to reduce the goal to its premises. Conclude with `⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩`. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Establish `hB : ⇑B = ![(1 : E), a]` using `coe_basisOfLinearIndependentOfCardEqFinrank hli _`. Establish `hspanP : ⊤ ≤ Submodule.span A.Fp (Set.range ![(1 : A.Ep), A.ιE a])`.

Rewrite using `[← A.span]`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx` using `B.sum_repr x`. Rewrite `hx` using `[hB, Fin.sum_univ_two]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx`. Establish `: A.ιE x = A.ιF (B.repr x 0) • (1 : A.Ep) + A.ιF (B.repr x 1) • A.ιE a` using `by conv_lhs => rw [← hx]`. Simplify using `only [map_add, map_mul, map_one, Algebra.smul_def, A.compat, mul_one]`. Rewrite using `[SetLike.mem_coe, this]`. Apply `Submodule.add_mem` to reduce the goal to its premises.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)`. Establish `hliP : LinearIndependent A.Fp ![(1 : A.Ep), A.ιE a]` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspanP (by simp [A.rank])`. Establish `hnotP : A.ιE a ∉ (algebraMap A.Fp A.Ep).range`. Introduce and unpack `⟨c, hc⟩`.

Rewrite `hliP` using `[LinearIndependent.pair_iff' one_ne_zero]`. Apply `hliP c` to reduce the goal to its premises. Rewrite using `[← hc, Algebra.algebraMap_eq_smul_one]`. Use `haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)`. Establish `hintP : IsIntegral A.Fp (A.ιE a)` using `Algebra.IsIntegral.isIntegral _`.

Establish `hdegP : 2 ≤ (minpoly A.Fp (A.ιE a)).natDegree`. Establish `h0` using `minpoly.natDegree_pos hintP`. Establish `h1 : (minpoly A.Fp (A.ιE a)).natDegree ≠ 1` using `fun h => hnotP (minpoly.natDegree_eq_one_iff.mp h)`. Use linear arithmetic over natural numbers and integers. Establish `hintF : IsIntegral F a` using `Algebra.IsIntegral.isIntegral _`.

Establish `hdegF : (minpoly F a).natDegree ≤ 2` using `h2 ▸ minpoly.natDegree_le a`. Use `set g : A.Fp[X] := (minpoly F a).map A.ιF with hg`. Establish `hgmon : g.Monic` using `(minpoly.monic hintF).map _`. Establish `hgdeg : g.natDegree ≤ 2`. Rewrite using `[hg, natDegree_map]`.

Conclude with `hdegF`. Establish `hgα : aeval (A.ιE a) g = 0`. Rewrite using `[hg, aeval_def, eval₂_map]`. Establish `hcomp : (algebraMap A.Fp A.Ep).comp A.ιF = A.ιE.comp (algebraMap F E)`. Use extensionality with `y`.

Simplify using `[A.compat]`. Rewrite using `[hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]`. Establish `hdvd : minpoly A.Fp (A.ιE a) ∣ g` using `minpoly.dvd A.Fp _ hgα`. Establish `hgeq : g = minpoly A.Fp (A.ιE a)` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintP) hgmon hdvd (by omega)`. Establish `hdvd2 : minpoly A.Fp (A.ιE a) ∣ (minpoly 𝒪[A.Fp] (A.ιE a)).map (algebraMap 𝒪[A.Fp] A.Fp)`.

Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_map_algebraMap, minpoly.aeval]`. Take `⟨g', hg'⟩` from `IsIntegrallyClosed.eq_map_mul_C_of_dvd A.Fp (minpoly.monic ha) hdvd2`. Rewrite `hg'` using `[(minpoly.monic hintP).leadingCoeff, C_1, mul_one]`. Establish `hc` using `congrArg (fun q => q.coeff i) (hg'.trans hgeq.symm)`.

Simplify using `only [coeff_map, hg] at hc`. Rewrite using `[← hc]`. Conclude with `(g'.coeff i).2`.
-/
theorem coeff_mem (h2 : Module.finrank F E = 2) (A : LocAt F E sig p) (a : E)
    (ha : IsIntegral 𝒪[A.Fp] (A.ιE a)) (hnot : a ∉ (algebraMap F E).range) (i : ℕ) :
    A.ιF ((minpoly F a).coeff i) ∈ 𝒪[A.Fp] := by
  classical
  haveI := ep_nontrivial A
  haveI := A.free
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    apply hnot
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hspanP : ⊤ ≤ Submodule.span A.Fp (Set.range ![(1 : A.Ep), A.ιE a]) := by
    rw [← A.span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx := B.sum_repr x
    rw [hB, Fin.sum_univ_two] at hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
    have : A.ιE x = A.ιF (B.repr x 0) • (1 : A.Ep) + A.ιF (B.repr x 1) • A.ιE a := by
      conv_lhs => rw [← hx]
      simp only [map_add, map_mul, map_one, Algebra.smul_def, A.compat, mul_one]
    rw [SetLike.mem_coe, this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hliP : LinearIndependent A.Fp ![(1 : A.Ep), A.ιE a] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanP (by simp [A.rank])
  have hnotP : A.ιE a ∉ (algebraMap A.Fp A.Ep).range := by
    rintro ⟨c, hc⟩
    rw [LinearIndependent.pair_iff' one_ne_zero] at hliP
    apply hliP c
    rw [← hc, Algebra.algebraMap_eq_smul_one]
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  have hintP : IsIntegral A.Fp (A.ιE a) := Algebra.IsIntegral.isIntegral _
  have hdegP : 2 ≤ (minpoly A.Fp (A.ιE a)).natDegree := by
    have h0 := minpoly.natDegree_pos hintP
    have h1 : (minpoly A.Fp (A.ιE a)).natDegree ≠ 1 := fun h => hnotP (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
  have hdegF : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  set g : A.Fp[X] := (minpoly F a).map A.ιF with hg
  have hgmon : g.Monic := (minpoly.monic hintF).map _
  have hgdeg : g.natDegree ≤ 2 := by
    rw [hg, natDegree_map]
    exact hdegF
  have hgα : aeval (A.ιE a) g = 0 := by
    rw [hg, aeval_def, eval₂_map]
    have hcomp : (algebraMap A.Fp A.Ep).comp A.ιF = A.ιE.comp (algebraMap F E) := by
      ext y
      simp [A.compat]
    rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hdvd : minpoly A.Fp (A.ιE a) ∣ g := minpoly.dvd A.Fp _ hgα
  have hgeq : g = minpoly A.Fp (A.ιE a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintP) hgmon hdvd (by omega)
  have hdvd2 : minpoly A.Fp (A.ιE a) ∣ (minpoly 𝒪[A.Fp] (A.ιE a)).map (algebraMap 𝒪[A.Fp] A.Fp) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, minpoly.aeval]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd A.Fp (minpoly.monic ha) hdvd2
  rw [(minpoly.monic hintP).leadingCoeff, C_1, mul_one] at hg'
  have hc := congrArg (fun q => q.coeff i) (hg'.trans hgeq.symm)
  simp only [coeff_map, hg] at hc
  rw [← hc]
  exact (g'.coeff i).2

/- English proof (translation)
Introduce `F E _ _ _ _ _ h2 sig p A a ha`. Rewrite `ha` using `[A.O_def]`. Use `ep_nontrivial A` as an intermediate fact. Distinguish the cases in `hr : a ∈ (algebraMap F E).range`. Take `⟨f, rfl⟩` from `hr`.

Establish `hf : A.ιF f ∈ 𝒪[A.Fp]`. Rewrite `ha` using `[A.compat]`. Establish `hi : IsIntegral 𝒪[A.Fp] (A.ιF f)` using `(isIntegral_algebraMap_iff (algebraMap A.Fp A.Ep).injective).mp ha`. Conclude with `(Valuation.integer.integers _).mem_of_integral hi`. Take `⟨d, hd, n, hn⟩` from `int_of_val A f hf`.

Use `⟨d, hd, algebraMap (𝓞 F) (𝓞 E) n, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F E (d : F) * algebraMap F E f = algebraMap F E (n : F)`. Rewrite using `[← map_mul, hn]`. Establish `hc : ∀ i, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * (minpoly F a).coeff i = n` using `fun i => int_of_val A _ (coeff_mem h2 A a ha hr i)`. Take `⟨d0, hd0, n0, hn0⟩` from `hc 0`.

Take `⟨d1, hd1, n1, hn1⟩` from `hc 1`. Establish `hintF : IsIntegral F a` using `Algebra.IsIntegral.isIntegral _`. Establish `hdeg : (minpoly F a).natDegree = 2`. Establish `h1 : (minpoly F a).natDegree ≠ 1` using `fun h => hr (minpoly.natDegree_eq_one_iff.mp h)`. Establish `h0` using `minpoly.natDegree_pos hintF`.

Use `minpoly.natDegree_le (A := F) a` as an intermediate fact. Rewrite `this` using `[h2]`. Use linear arithmetic over natural numbers and integers. Establish `hlead : (minpoly F a).coeff 2 = 1`. Use `(minpoly.monic hintF).leadingCoeff` as an intermediate fact.

Rewrite `this` using `[leadingCoeff, hdeg]`. Then use the resulting hypothesis. Establish `hrel : algebraMap F E ((minpoly F a).coeff 0) + algebraMap F E ((minpoly F a).coeff 1) * a + a ^ 2 = 0`. Use `minpoly.aeval F a` as an intermediate fact. Rewrite `this` using `[aeval_eq_sum_range' (n := 3) (by omega)]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, Algebra.smul_def, map_one, pow_zero, pow_one, one_mul, mul_one, zero_add] at this`.

Take the linear combination `this`. Establish `hd : d0 * d1 ∉ p.asIdeal` using `fun h => (p.isPrime.mem_or_mem h).elim hd0 hd1`. Establish `hint : IsIntegral (𝓞 F) (algebraMap F E ((d0 * d1 : 𝓞 F) : F) * a)`. Use `⟨X ^ 2 + C (d0 * n1) * X + C (d0 * d1 * d1 * n0), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]`.

Establish `e0` using `congrArg (algebraMap F E) hn0`. Establish `e1` using `congrArg (algebraMap F E) hn1`. Simplify using `only [map_mul] at e0 e1`. Simplify using `only [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_mul] at *`. Express the relevant statement in the definitionally equal form `_ = algebraMap F E (n0 : F) at e0`.

Take the linear combination `(algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) ^ 2 * hrel - (algebraMap F E (d0 : F) * (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) * a) * e1 - (algebraMap F E (d0 : F) * algebraMap F E (d1 : F) ^ 2) * e0`. Take `⟨b, hb⟩` from `IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := 𝓞 F) (B := E) |>.mp hint`. Use `⟨d0 * d1, hd, b, ?_⟩` and prove the remaining obligations. Rewrite using `[show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, hb]`. Both sides reduce to the same expression.
-/
theorem intP : IntP := by
  intro F E _ _ _ _ _ h2 sig p A a ha
  rw [A.O_def] at ha
  have := ep_nontrivial A
  by_cases hr : a ∈ (algebraMap F E).range
  · obtain ⟨f, rfl⟩ := hr
    have hf : A.ιF f ∈ 𝒪[A.Fp] := by
      rw [A.compat] at ha
      have hi : IsIntegral 𝒪[A.Fp] (A.ιF f) :=
        (isIntegral_algebraMap_iff (algebraMap A.Fp A.Ep).injective).mp ha
      exact (Valuation.integer.integers _).mem_of_integral hi
    obtain ⟨d, hd, n, hn⟩ := int_of_val A f hf
    refine ⟨d, hd, algebraMap (𝓞 F) (𝓞 E) n, ?_⟩
    change algebraMap F E (d : F) * algebraMap F E f = algebraMap F E (n : F)
    rw [← map_mul, hn]
  · have hc : ∀ i, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * (minpoly F a).coeff i = n :=
      fun i => int_of_val A _ (coeff_mem h2 A a ha hr i)
    obtain ⟨d0, hd0, n0, hn0⟩ := hc 0
    obtain ⟨d1, hd1, n1, hn1⟩ := hc 1
    have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
    have hdeg : (minpoly F a).natDegree = 2 := by
      have h1 : (minpoly F a).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.mp h)
      have h0 := minpoly.natDegree_pos hintF
      have := minpoly.natDegree_le (A := F) a
      rw [h2] at this
      omega
    have hlead : (minpoly F a).coeff 2 = 1 := by
      have := (minpoly.monic hintF).leadingCoeff
      rwa [leadingCoeff, hdeg] at this
    have hrel : algebraMap F E ((minpoly F a).coeff 0) + algebraMap F E ((minpoly F a).coeff 1) * a
        + a ^ 2 = 0 := by
      have := minpoly.aeval F a
      rw [aeval_eq_sum_range' (n := 3) (by omega)] at this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, Algebra.smul_def,
        map_one, pow_zero, pow_one, one_mul, mul_one, zero_add] at this
      linear_combination this
    have hd : d0 * d1 ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd0 hd1
    have hint : IsIntegral (𝓞 F) (algebraMap F E ((d0 * d1 : 𝓞 F) : F) * a) := by
      refine ⟨X ^ 2 + C (d0 * n1) * X + C (d0 * d1 * d1 * n0), by monicity!, ?_⟩
      simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
      have e0 := congrArg (algebraMap F E) hn0
      have e1 := congrArg (algebraMap F E) hn1
      simp only [map_mul] at e0 e1
      simp only [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_mul] at *
      change _ = algebraMap F E (n0 : F) at e0
      linear_combination (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) ^ 2 * hrel
        - (algebraMap F E (d0 : F) * (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) * a) * e1
        - (algebraMap F E (d0 : F) * algebraMap F E (d1 : F) ^ 2) * e0
    obtain ⟨b, hb⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := 𝓞 F) (B := E) |>.mp hint
    refine ⟨d0 * d1, hd, b, ?_⟩
    rw [show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, hb]
    rfl

end PI.LocLatEq.W
