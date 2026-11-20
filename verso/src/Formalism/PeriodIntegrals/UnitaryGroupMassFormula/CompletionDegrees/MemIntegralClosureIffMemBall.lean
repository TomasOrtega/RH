import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥K.1]`. Conclude with `(algebraMap ℚ_[l] ↥K.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])`.
-/
theorem algebraMap_padicInt_injective (K : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥K.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥K.1]
  exact (algebraMap ℚ_[l] ↥K.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

instance isTorsionFree_finExt (K : FinExt l) : Module.IsTorsionFree ℤ_[l] ↥K.1 where
  isSMulRegular r hr := fun x y h => by
    have hr0 : algebraMap ℤ_[l] ↥K.1 r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((map_eq_zero_iff _ (algebraMap_padicInt_injective K)).1 h0)
    change r • x = r • y at h
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ hr0 h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n`. Distinguish the cases in `hn : n < P.natDegree`. Establish `ht : spectralValueTerms P n ≤ 1` using `(le_ciSup (spectralValueTerms_bddAbove P) n).trans h`. Rewrite `ht` using `[spectralValueTerms, if_pos hn]`.

Establish `hexp : (0 : ℝ) < 1 / ((P.natDegree : ℝ) - n)`. Establish `: (n : ℝ) < P.natDegree` using `by exact_mod_cast hn`. Apply `div_pos one_pos` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `absurd ht (not_le.mpr (Real.one_lt_rpow hc hexp))`. Break down `eq_or_lt_of_le (not_lt.mp hn) with h' | h'` into its components or cases. Rewrite using `[← h', hP.coeff_natDegree, norm_one]`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt h', norm_zero]`.

Conclude with `zero_le_one`. Introduce `h`. Unfold `spectralValue`. Apply `ciSup_le` to reduce the goal to its premises. Introduce `n`.

Simplify using `only [spectralValueTerms]`. Use `split_ifs with hn`. Establish `: (n : ℝ) < P.natDegree` using `by exact_mod_cast hn`. Conclude with `Real.rpow_le_one (norm_nonneg _) (h n) (div_nonneg zero_le_one (by linarith))`. Conclude with `zero_le_one`.
-/
private theorem spectralValue_le_one_iff_norm_coeff_le_one (P : ℚ_[l][X]) (hP : P.Monic) :
    spectralValue P ≤ 1 ↔ ∀ n, ‖P.coeff n‖ ≤ 1 := by
  constructor
  · intro h n
    by_cases hn : n < P.natDegree
    · have ht : spectralValueTerms P n ≤ 1 :=
        (le_ciSup (spectralValueTerms_bddAbove P) n).trans h
      rw [spectralValueTerms, if_pos hn] at ht
      have hexp : (0 : ℝ) < 1 / ((P.natDegree : ℝ) - n) := by
        have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
        apply div_pos one_pos; linarith
      by_contra hc
      push_neg at hc
      exact absurd ht (not_le.mpr (Real.one_lt_rpow hc hexp))
    · rcases eq_or_lt_of_le (not_lt.mp hn) with h' | h'
      · rw [← h', hP.coeff_natDegree, norm_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h', norm_zero]; exact zero_le_one
  · intro h
    unfold spectralValue
    apply ciSup_le
    intro n
    simp only [spectralValueTerms]
    split_ifs with hn
    · have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
      exact Real.rpow_le_one (norm_nonneg _) (h n) (div_nonneg zero_le_one (by linarith))
    · exact zero_le_one

/- English proof (translation)
Establish `hzQ : IsIntegral ℚ_[l] z` using `by first`. Consider the case `exact Algebra.IsIntegral.isIntegral z`. Consider the case `exact (Algebra.IsAlgebraic.isAlgebraic z).isIntegral`. Establish `hnorm : ‖z‖ = spectralValue (minpoly ℚ_[l] z)` using `rfl`. Rewrite using `[hnorm, spectralValue_le_one_iff_norm_coeff_le_one _ (minpoly.monic hzQ)]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hlift : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Conclude with `⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hqmap, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hzQ)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hqmap, minpoly.aeval]`. Introduce `hz n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]`. Conclude with `PadicInt.norm_le_one _`.
-/
theorem norm_le_one_iff_isIntegral (z : Om l) : ‖z‖ ≤ 1 ↔ IsIntegral ℤ_[l] z := by
  have hzQ : IsIntegral ℚ_[l] z := by
    first
      | exact Algebra.IsIntegral.isIntegral z
      | exact (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hnorm : ‖z‖ = spectralValue (minpoly ℚ_[l] z) := rfl
  rw [hnorm, spectralValue_le_one_iff_norm_coeff_le_one _ (minpoly.monic hzQ)]
  constructor
  · intro h
    have hlift : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hqmap, -, hqm⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hzQ)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hqmap, minpoly.aeval]
  · intro hz n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

/- English proof (translation)
Rewrite using `[mem_integralClosure_iff]`. Use `show IsIntegral ℤ_[l] x ↔ ‖((x : ↥K.1) : Om l)‖ ≤ 1`. Rewrite using `[norm_le_one_iff_isIntegral]`. Use `first`. Consider the case `exact (isIntegral_algebraMap_iff (A := ↥K.1) (B := Om l) (algebraMap (↥K.1) (Om l)).injective).symm`.

Consider the case `exact (isIntegral_algHom_iff ((K.1.val).restrictScalars ℤ_[l]) K.1.val.injective).symm`.
-/
theorem mem_integralClosure_iff_mem_ball (K : FinExt l) (x : ↥K.1) :
    x ∈ integralClosure ℤ_[l] ↥K.1 ↔ x ∈ ball K := by
  rw [mem_integralClosure_iff]
  show IsIntegral ℤ_[l] x ↔ ‖((x : ↥K.1) : Om l)‖ ≤ 1
  rw [norm_le_one_iff_isIntegral]
  first
    | exact (isIntegral_algebraMap_iff (A := ↥K.1) (B := Om l) (algebraMap (↥K.1) (Om l)).injective).symm
    | exact (isIntegral_algHom_iff ((K.1.val).restrictScalars ℤ_[l]) K.1.val.injective).symm

/- English proof (translation)
Set `f : C →+ (Fin n → ZMod l)` to `AddMonoidHom.pi fun i => (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toAddMonoidHom.comp (b.coord i).toAddMonoidHom`. Establish `hf : ∀ x i, f x i = PadicInt.toZMod (b.repr x i)` using `fun x i => rfl`. Establish `hsurj : Function.Surjective f`. Introduce `w`. Use `⟨b.equivFun.symm (fun i => ((w i).val : ℤ_[l])), funext fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hf]`. Establish `h1 : b.repr (b.equivFun.symm (fun i => ((w i).val : ℤ_[l]))) i = ((w i).val : ℤ_[l])`. Rewrite using `[← b.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[h1, map_natCast, ZMod.natCast_zmod_val]`. Establish `hlC : ((l : ℕ) : C) = algebraMap ℤ_[l] C (l : ℤ_[l])` using `(map_natCast _ _).symm`.

Establish `hk : (Ideal.span {((l : ℕ) : C)}).toAddSubgroup = f.ker`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]`. Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩`. Use function extensionality and compare the values at `i`. Use `show f (y * ((l : ℕ) : C)) i = 0`. Rewrite using `[hf, hlC, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul]`. Introduce `hx`.

Establish `hdiv : ∀ i, ∃ d : ℤ_[l], b.repr x i = (l : ℤ_[l]) * d` using `fun i => by`. Establish `h0 : PadicInt.toZMod (b.repr x i) = 0` using `congrFun hx i`. Establish `hm : b.repr x i ∈ Ideal.span {((l : ℕ) : ℤ_[l])}`. Rewrite using `[← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]`. Conclude with `RingHom.mem_ker.mpr h0`.

Conclude with `(Ideal.mem_span_singleton'.mp hm).imp fun d hd => by rw [← hd, mul_comm]`. Use `choose d hd using hdiv`. Use `⟨∑ i, d i • b i, ?_⟩` and prove the remaining obligations. Rewrite using `[hlC, mul_comm, ← Algebra.smul_def, Finset.smul_sum]`. Use `conv_rhs => rw [← b.sum_repr x]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hd, smul_smul]`. Establish `hcard : Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = Nat.card (C ⧸ f.ker)`. Rewrite using `[← hk]`. Both sides reduce to the same expression.

Rewrite using `[hcard, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]`. Rewrite using `[Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
theorem card_quot_l {C : Type} [CommRing C] [Algebra ℤ_[l] C] {n : ℕ} (b : Basis (Fin n) ℤ_[l] C) :
    Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = l ^ n := by
  let f : C →+ (Fin n → ZMod l) :=
    AddMonoidHom.pi fun i =>
      (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  have hf : ∀ x i, f x i = PadicInt.toZMod (b.repr x i) := fun x i => rfl
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨b.equivFun.symm (fun i => ((w i).val : ℤ_[l])), funext fun i => ?_⟩
    rw [hf]
    have h1 : b.repr (b.equivFun.symm (fun i => ((w i).val : ℤ_[l]))) i = ((w i).val : ℤ_[l]) := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [h1, map_natCast, ZMod.natCast_zmod_val]
  have hlC : ((l : ℕ) : C) = algebraMap ℤ_[l] C (l : ℤ_[l]) := (map_natCast _ _).symm
  have hk : (Ideal.span {((l : ℕ) : C)}).toAddSubgroup = f.ker := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      funext i
      show f (y * ((l : ℕ) : C)) i = 0
      rw [hf, hlC, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        map_natCast, ZMod.natCast_self, zero_mul]
    · intro hx
      have hdiv : ∀ i, ∃ d : ℤ_[l], b.repr x i = (l : ℤ_[l]) * d := fun i => by
        have h0 : PadicInt.toZMod (b.repr x i) = 0 := congrFun hx i
        have hm : b.repr x i ∈ Ideal.span {((l : ℕ) : ℤ_[l])} := by
          rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
          exact RingHom.mem_ker.mpr h0
        exact (Ideal.mem_span_singleton'.mp hm).imp fun d hd => by rw [← hd, mul_comm]
      choose d hd using hdiv
      refine ⟨∑ i, d i • b i, ?_⟩
      rw [hlC, mul_comm, ← Algebra.smul_def, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd, smul_smul]
  have hcard : Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = Nat.card (C ⧸ f.ker) := by
    rw [← hk]; rfl
  rw [hcard, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/- English proof (translation)
Introduce `l _ K`. Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2`. Set `S` to `integralClosure ℤ_[l] ↥K.1`. Set `e : ↥(ball K) ≃+* ↥S` to `{ toFun := fun x => ⟨x.1, (mem_integralClosure_iff_mem_ball K x.1).mpr x.2⟩ invFun := fun y => ⟨y.1, (mem_integralClosure_iff_mem_ball K y.1).mp y.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => Subtype.ext rfl map_add' := fun _ _ => Subtype.ext rfl }`. Establish `hIJ : Ideal.span {((l : ℕ) : ↥S)} = (Ideal.span {((l : ℕ) : ↥(ball K))}).map e`.

Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Rewrite using `[Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv]`. Use `haveI : Module.Free ℤ_[l] S := IsIntegralClosure.module_free (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)`. Use `haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)`. Rewrite using `[card_quot_l (Module.finBasis ℤ_[l] S), IsIntegralClosure.rank (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)]`.
-/
theorem ballCard : BallCard := by
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let S := integralClosure ℤ_[l] ↥K.1
  let e : ↥(ball K) ≃+* ↥S :=
    { toFun := fun x => ⟨x.1, (mem_integralClosure_iff_mem_ball K x.1).mpr x.2⟩
      invFun := fun y => ⟨y.1, (mem_integralClosure_iff_mem_ball K y.1).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hIJ : Ideal.span {((l : ℕ) : ↥S)} = (Ideal.span {((l : ℕ) : ↥(ball K))}).map e := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv]
  haveI : Module.Free ℤ_[l] S :=
    IsIntegralClosure.module_free (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  haveI : Module.Finite ℤ_[l] S :=
    IsIntegralClosure.finite (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  rw [card_quot_l (Module.finBasis ℤ_[l] S),
    IsIntegralClosure.rank (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)]

end PI.CompDegEF
