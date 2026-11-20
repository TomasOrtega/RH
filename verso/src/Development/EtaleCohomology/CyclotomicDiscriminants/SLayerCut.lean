import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg

noncomputable section

open NumberField NumberField.InfinitePlace Polynomial UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Tower

namespace LateralTheory.Q.SLayerCut

/- English proof (translation)
Establish `: NeZero N` using `⟨hN⟩`. Establish `hz` using `IsCyclotomicExtension.zeta_spec N L L'`. Use `set z := IsCyclotomicExtension.zeta N L L' with hzd`. Set `x : 𝓞 L'` to `hz.toInteger`. Establish `hx : x ^ N = 1` using `hz.toInteger_isPrimitiveRoot.pow_eq_one`.

Establish `hadj : Algebra.adjoin L {algebraMap (𝓞 L') L' x} = ⊤` using `IsCyclotomicExtension.adjoin_primitive_root_eq_top hz`. Establish `hmem` using `aeval_derivative_mem_differentIdeal (𝓞 L) L L' x hadj`. Establish `hint : IsIntegral (𝓞 L) x` using `Algebra.IsIntegral.isIntegral x`. Establish `hdvd : minpoly (𝓞 L) x ∣ (X ^ N - 1 : (𝓞 L)[X])` using `minpoly.isIntegrallyClosed_dvd hint (by simp [hx])`. Take `⟨g, hg⟩` from `hdvd`.

Establish `h1` using `congrArg (fun p => aeval x (derivative p) * x) hg`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero, map_pow, aeval_X, map_natCast] at h1`. Establish `h2 : (N : 𝓞 L') ∈ differentIdeal (𝓞 L) (𝓞 L')`. Establish `h3 : (N : 𝓞 L') = aeval x (derivative (minpoly (𝓞 L) x)) * (aeval x g * x)`. Rewrite using `[← mul_assoc, ← h1, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hx, mul_one]`.

Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Establish `h4 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 L')) ∣ N ^ Module.finrank ℚ L'`. Establish `h5` using `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h2)`. Rewrite `h5` using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Then use the resulting hypothesis.

Rewrite using `[NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) L' (𝓞 L'), mul_comm]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hN) _) h4)`.
-/
theorem disc_cyc (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (N : ℕ)
    (hN : N ≠ 0) [hc : IsCyclotomicExtension {N} L L'] :
    (discr L').natAbs ≤ (discr L).natAbs ^ Module.finrank L L' * N ^ Module.finrank ℚ L' := by
  have : NeZero N := ⟨hN⟩
  have hz := IsCyclotomicExtension.zeta_spec N L L'
  set z := IsCyclotomicExtension.zeta N L L' with hzd
  let x : 𝓞 L' := hz.toInteger
  have hx : x ^ N = 1 := hz.toInteger_isPrimitiveRoot.pow_eq_one
  have hadj : Algebra.adjoin L {algebraMap (𝓞 L') L' x} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hz
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 L) L L' x hadj
  have hint : IsIntegral (𝓞 L) x := Algebra.IsIntegral.isIntegral x
  have hdvd : minpoly (𝓞 L) x ∣ (X ^ N - 1 : (𝓞 L)[X]) :=
    minpoly.isIntegrallyClosed_dvd hint (by simp [hx])
  obtain ⟨g, hg⟩ := hdvd
  have h1 := congrArg (fun p => aeval x (derivative p) * x) hg
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul, map_add, map_mul,
    minpoly.aeval, zero_mul, add_zero, map_pow, aeval_X, map_natCast] at h1
  have h2 : (N : 𝓞 L') ∈ differentIdeal (𝓞 L) (𝓞 L') := by
    have h3 : (N : 𝓞 L') = aeval x (derivative (minpoly (𝓞 L) x)) * (aeval x g * x) := by
      rw [← mul_assoc, ← h1, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hx, mul_one]
    rw [h3]
    exact Ideal.mul_mem_right _ _ hmem
  have h4 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 L')) ∣ N ^ Module.finrank ℚ L' := by
    have h5 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h2)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h5
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) L' (𝓞 L'), mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hN) _) h4)

/- English proof (translation)
Take `⟨γ, -, -, -, hd⟩` from `exists_descends l L (AlgebraicClosure L) hμ`. Establish `h0 : IsLayer l 0 L L`. Use `⟨⟨0, ?_⟩, by simp⟩` and prove the remaining obligations. Establish `: NeZero (l ^ 0)` using `⟨by simp⟩`. Rewrite using `[IsCyclotomicExtension.iff_singleton]`.

Conclude with `⟨⟨1, by simp⟩, fun x => Subalgebra.algebraMap_mem _ x⟩`. Rewrite using `[hd E hE 0 L h0, hd E hE m L' h, pow_zero, pow_one]`. Generalize the expression as in `xTw l l (⊤ : Subgroup (Formalism.ConjugateSelfDual.G L (AlgebraicClosure L))) (E : ℤ) γ = g`. Establish `hr : LinearMap.range (g ^ l ^ m - 1) ≤ LinearMap.range (g - 1)`. Rewrite using `[← mul_geom_sum g (l ^ m), Module.End.mul_eq_comp]`.

Conclude with `LinearMap.range_comp_le_range _ _`. Conclude with `Module.length_le_of_surjective (Submodule.factor hr) (Submodule.factor_surjective hr)`.
-/
theorem sha_le (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (l E m : ℕ)
    [Fact l.Prime] (hμ : HasMuQ l L) (hE : 1 ≤ E) (h : IsLayer l m L L') : shaInv L l E ≤ shaInv L' l E := by
  obtain ⟨γ, -, -, -, hd⟩ := exists_descends l L (AlgebraicClosure L) hμ
  have h0 : IsLayer l 0 L L := by
    refine ⟨⟨0, ?_⟩, by simp⟩
    have : NeZero (l ^ 0) := ⟨by simp⟩
    rw [IsCyclotomicExtension.iff_singleton]
    exact ⟨⟨1, by simp⟩, fun x => Subalgebra.algebraMap_mem _ x⟩
  rw [hd E hE 0 L h0, hd E hE m L' h, pow_zero, pow_one]
  generalize xTw l l (⊤ : Subgroup (Formalism.ConjugateSelfDual.G L (AlgebraicClosure L))) (E : ℤ) γ = g
  have hr : LinearMap.range (g ^ l ^ m - 1) ≤ LinearMap.range (g - 1) := by
    rw [← mul_geom_sum g (l ^ m), Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  exact Module.length_le_of_surjective (Submodule.factor hr) (Submodule.factor_surjective hr)

/- English proof (translation)
Introduce `L _ _ l E hl hμ hE`. Establish `hp : l.Prime` using `hl.out`. Set `Ω` to `AlgebraicClosure L`. Set `m` to `Nat.clog l (4 * E + 4)`. Establish `hm1 : 4 * E + 4 ≤ l ^ m` using `Nat.le_pow_clog hp.one_lt _`.

Establish `hm2 : l ^ m ≤ l * (4 * E + 4)`. Establish `h1` using `Nat.pow_pred_clog_lt_self hp.one_lt (x := 4 * E + 4) (by omega)`. Establish `h2 : 0 < m` using `Nat.clog_pos hp.one_lt (by omega)`. Combine the equalities or inequalities in the displayed calculation. Establish `hLay` using `(layerUniq L Ω l hμ).1 m`.

Establish `hcyc` using `(Kum.fnCyc L Ω l (cZero l L + m)).1`. Set `L' : Type` to `layF l L Ω m`. Establish `hμ' : HasMuQ l L'`. Take `⟨ζ, hζ⟩` from `hμ`. Conclude with `⟨_, hζ.map_of_injective (algebraMap L L').injective⟩`.

Take `⟨q1, -, q3, q4, -⟩` from `muQ L' (AlgebraicClosure L') l`. Establish `htc : IsTotallyComplex L'` using `(q4 hμ').1`. Establish `hq` using `q3.1 hμ'`. Establish `hle : cZero l L + m ≤ cZero l L'` using `(q1 _).1 (hcyc.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hp.ne_zero))`. Establish `hdeg : Module.finrank L L' = l ^ m` using `hLay.2`.

Establish `hfin : Module.finrank ℚ L' = l ^ m * Module.finrank ℚ L`. Rewrite using `[← Module.finrank_mul_finrank ℚ L L', hdeg, mul_comm]`. Establish `hpos : 0 < Module.finrank ℚ L` using `Module.finrank_pos`. Establish `hln : l ≤ Module.finrank ℚ L + 1`. Distinguish the cases in `h2 : l = 2`.

Use linear arithmetic over natural numbers and integers. Take `⟨z, hz⟩` from `hμ`. Rewrite `hz` using `[if_neg h2]`. Establish `h1` using `IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat (by rw [Nat.lcm_self]; exact hp.pos))`. Rewrite `h1` using `[Nat.lcm_self, Nat.totient_prime hp]`.

Use linear arithmetic over natural numbers and integers. Establish `hpw : l ^ (cZero l L + m) ≤ l ^ cZero l L'` using `Nat.pow_le_pow_right hp.pos hle`. Establish `hpm : l ^ m ≤ l ^ (cZero l L + m)` using `Nat.pow_le_pow_right hp.pos (by omega)`. Use `⟨L', inferInstance, inferInstance, cZero l L', l ^ m, htc, ⟨?_, fun h2 => ?_, (q1 _).2 le_rfl, fun h => ?_⟩, by omega, ?_, hfin, hm2.trans (Nat.mul_le_mul_right _ hln), Win.rootdeg L' l _ hp ((q1 _).2 le_rfl), ?_, sha_le L L' l E m hμ hE hLay⟩` and prove the remaining obligations. Apply the tactic sequence `unfold Base.qExp at hq split_ifs at hq <;> omega`.

Unfold `Base.qExp at hq`. Rewrite `hq` using `[if_pos h2]`. Then use the resulting hypothesis. Use `(q1 _).1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `IsTotallyComplex.finrank L'`.

Establish `h2 : l ^ m ≤ l ^ m * Module.finrank ℚ L` using `Nat.le_mul_of_pos_right _ hpos`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `disc_cyc L L' (l ^ (cZero l L + m)) (pow_ne_zero _ hp.ne_zero) (hc := hcyc)`. Rewrite `h1` using `[hdeg]`. Conclude with `h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpw _))`.
-/
theorem goal_of : UpperTheory.V.ZK.SLayer := by
  intro L _ _ l E hl hμ hE
  have hp : l.Prime := hl.out
  let Ω := AlgebraicClosure L
  let m := Nat.clog l (4 * E + 4)
  have hm1 : 4 * E + 4 ≤ l ^ m := Nat.le_pow_clog hp.one_lt _
  have hm2 : l ^ m ≤ l * (4 * E + 4) := by
    have h1 := Nat.pow_pred_clog_lt_self hp.one_lt (x := 4 * E + 4) (by omega)
    have h2 : 0 < m := Nat.clog_pos hp.one_lt (by omega)
    calc l ^ m = l * l ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel h2]
      _ ≤ _ := Nat.mul_le_mul_left _ h1.le
  have hLay := (layerUniq L Ω l hμ).1 m
  have hcyc := (Kum.fnCyc L Ω l (cZero l L + m)).1
  let L' : Type := layF l L Ω m
  have hμ' : HasMuQ l L' := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L L').injective⟩
  obtain ⟨q1, -, q3, q4, -⟩ := muQ L' (AlgebraicClosure L') l
  have htc : IsTotallyComplex L' := (q4 hμ').1
  have hq := q3.1 hμ'
  have hle : cZero l L + m ≤ cZero l L' :=
    (q1 _).1 (hcyc.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hp.ne_zero))
  have hdeg : Module.finrank L L' = l ^ m := hLay.2
  have hfin : Module.finrank ℚ L' = l ^ m * Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ L L', hdeg, mul_comm]
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hln : l ≤ Module.finrank ℚ L + 1 := by
    by_cases h2 : l = 2
    · omega
    · obtain ⟨z, hz⟩ := hμ
      rw [if_neg h2] at hz
      have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz
        (Polynomial.cyclotomic.irreducible_rat (by rw [Nat.lcm_self]; exact hp.pos))
      rw [Nat.lcm_self, Nat.totient_prime hp] at h1
      omega
  have hpw : l ^ (cZero l L + m) ≤ l ^ cZero l L' := Nat.pow_le_pow_right hp.pos hle
  have hpm : l ^ m ≤ l ^ (cZero l L + m) := Nat.pow_le_pow_right hp.pos (by omega)
  refine ⟨L', inferInstance, inferInstance, cZero l L', l ^ m, htc, ⟨?_, fun h2 => ?_, (q1 _).2 le_rfl, fun h => ?_⟩,
    by omega, ?_, hfin, hm2.trans (Nat.mul_le_mul_right _ hln), Win.rootdeg L' l _ hp ((q1 _).2 le_rfl), ?_,
    sha_le L L' l E m hμ hE hLay⟩
  · unfold Base.qExp at hq
    split_ifs at hq <;> omega
  · unfold Base.qExp at hq
    rwa [if_pos h2] at hq
  · have := (q1 _).1 h
    omega
  · have h1 := IsTotallyComplex.finrank L'
    have h2 : l ^ m ≤ l ^ m * Module.finrank ℚ L := Nat.le_mul_of_pos_right _ hpos
    omega
  · have h1 := disc_cyc L L' (l ^ (cZero l L + m)) (pow_ne_zero _ hp.ne_zero) (hc := hcyc)
    rw [hdeg] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpw _))

end LateralTheory.Q.SLayerCut

end
