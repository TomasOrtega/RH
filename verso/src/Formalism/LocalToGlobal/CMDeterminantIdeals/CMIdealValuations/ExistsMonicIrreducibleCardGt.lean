import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG

noncomputable section

namespace Formalism.L2.LamCM

open Polynomial IsLocalRing

/- English proof (translation)
Establish `hcard : ∀ f : k[X], f.Monic → Nat.card (AdjoinRoot f) = Nat.card k ^ f.natDegree`. Introduce `f hf`. Rewrite using `[Nat.card_congr (AdjoinRoot.powerBasis hf.ne_zero).basis.equivFun.toEquiv, Nat.card_fun]`. Simplify using `[AdjoinRoot.powerBasis_dim]`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hq : 2 ≤ Nat.card k` using `Finite.one_lt_card`. Establish `hdeg : ∀ α : AlgebraicClosure k, (minpoly k α).natDegree ≤ N`. Introduce `α`. Establish `hint : IsIntegral k α` using `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral`.

Establish `h1` using `hcon _ (minpoly.monic hint) (minpoly.irreducible hint)`. Rewrite `h1` using `[hcard _ (minpoly.monic hint)]`. Establish `h2 : (minpoly k α).natDegree < 2 ^ (minpoly k α).natDegree` using `Nat.lt_two_pow_self`. Establish `h3 : 2 ^ (minpoly k α).natDegree ≤ Nat.card k ^ (minpoly k α).natDegree` using `Nat.pow_le_pow_left hq _`. Use linear arithmetic over natural numbers and integers.

Establish `hsub : (Set.univ : Set (AlgebraicClosure k)) ⊆ ⋃ c : Fin (N + 1) → k, (∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).rootSet (AlgebraicClosure k)`. Introduce `α _`. Establish `hint : IsIntegral k α` using `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral`. Use `Set.mem_iUnion.2 ⟨fun i => (minpoly k α).coeff i, ?_⟩` and prove the remaining obligations. Establish `hp : (∑ i : Fin (N + 1), Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ (i : ℕ)) = minpoly k α`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ i)]`. Use `conv_rhs => rw [Polynomial.as_sum_range' (minpoly k α) (N + 1) (by have := hdeg α; omega)]`. Simplify using `only [Polynomial.C_mul_X_pow_eq_monomial]`. Rewrite using `[hp, Polynomial.mem_rootSet]`. Conclude with `⟨minpoly.ne_zero hint, minpoly.aeval k α⟩`.

Establish `hfin : (Set.univ : Set (AlgebraicClosure k)).Finite` using `Set.Finite.subset (Set.finite_iUnion fun c => Polynomial.rootSet_finite _ _) hsub`. Establish `: Finite (AlgebraicClosure k)` using `Set.finite_univ_iff.1 hfin`. Conclude with `not_finite (AlgebraicClosure k)`.
-/
theorem exists_monic_irreducible_card_gt (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ N < Nat.card (AdjoinRoot f) := by
  classical

  have hcard : ∀ f : k[X], f.Monic → Nat.card (AdjoinRoot f) = Nat.card k ^ f.natDegree := by
    intro f hf
    rw [Nat.card_congr (AdjoinRoot.powerBasis hf.ne_zero).basis.equivFun.toEquiv, Nat.card_fun]
    simp [AdjoinRoot.powerBasis_dim]
  by_contra hcon
  push_neg at hcon
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card

  have hdeg : ∀ α : AlgebraicClosure k, (minpoly k α).natDegree ≤ N := by
    intro α
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    have h1 := hcon _ (minpoly.monic hint) (minpoly.irreducible hint)
    rw [hcard _ (minpoly.monic hint)] at h1
    have h2 : (minpoly k α).natDegree < 2 ^ (minpoly k α).natDegree := Nat.lt_two_pow_self
    have h3 : 2 ^ (minpoly k α).natDegree ≤ Nat.card k ^ (minpoly k α).natDegree := Nat.pow_le_pow_left hq _
    omega
  have hsub : (Set.univ : Set (AlgebraicClosure k)) ⊆ ⋃ c : Fin (N + 1) → k,
      (∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).rootSet (AlgebraicClosure k) := by
    intro α _
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    refine Set.mem_iUnion.2 ⟨fun i => (minpoly k α).coeff i, ?_⟩
    have hp : (∑ i : Fin (N + 1), Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ (i : ℕ)) = minpoly k α := by
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ i)]
      conv_rhs => rw [Polynomial.as_sum_range' (minpoly k α) (N + 1) (by have := hdeg α; omega)]
      simp only [Polynomial.C_mul_X_pow_eq_monomial]
    rw [hp, Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval k α⟩
  have hfin : (Set.univ : Set (AlgebraicClosure k)).Finite :=
    Set.Finite.subset (Set.finite_iUnion fun c => Polynomial.rootSet_finite _ _) hsub
  have : Finite (AlgebraicClosure k) := Set.finite_univ_iff.1 hfin
  exact not_finite (AlgebraicClosure k)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Use `Submodule.smul_induction_on (p := fun x => b.repr x i ∈ J) hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `J.mul_mem_right _ hr`.

Simplify using `only [map_add, Finsupp.add_apply]`. Conclude with `J.add_mem hx hy`. Introduce `h`. Rewrite using `[← b.sum_repr x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top`.
-/
theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ J • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun x => b.repr x i ∈ J) hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · simp only [map_add, Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`.
-/
theorem mem_smul_top_self_iff {R : Type} [CommRing R] (J : Ideal R) (y : R) :
    y ∈ J • (⊤ : Submodule R R) ↔ y ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Establish `key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔ ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)]`. Introduce `n x y`. Rewrite using `[SModEq.sub_mem, mem_smul_top_iff_repr b]`. Simplify using `only [map_sub, Finsupp.sub_apply, SModEq.sub_mem, mem_smul_top_self_iff]`. Use `haveI := h`.

Establish `hH : IsHausdorff I M`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ i, b.repr x i = 0` using `fun i => IsHausdorff.haus' (I := I) (b.repr x i) fun n => by simpa using (key n x 0).1 (hx n) i`. Conclude with `b.repr.injective (Finsupp.ext fun i => by simpa using h0 i)`. Establish `hP : IsPrecomplete I M`.

Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]` using `fun i => IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) fun hmn => (key _ _ _).1 (hf hmn) i`. Use `choose L hL using hc`. Use `⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩` and prove the remaining obligations. Establish `hr : b.repr (b.equivFun.symm L) i = L i`.

Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[hr]`. Conclude with `hL i n`. Conclude with `{ toIsHausdorff := hH, toIsPrecomplete := hP }`.
-/
theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (I : Ideal R) (b : Module.Basis ι R M) (h : IsAdicComplete I R) : IsAdicComplete I M := by

  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    simp only [map_sub, Finsupp.sub_apply, SModEq.sub_mem, mem_smul_top_self_iff]
  haveI := h
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    have h0 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := I) (b.repr x i) fun n => by simpa using (key n x 0).1 (hx n) i
    exact b.repr.injective (Finsupp.ext fun i => by simpa using h0 i)
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
      IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have hr : b.repr (b.equivFun.symm L) i = L i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hr]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

def quotResidueEquiv {V : Type} [CommRing V] [IsLocalRing V] (g : V[X]) :
    AdjoinRoot g ⧸ Ideal.map (algebraMap V (AdjoinRoot g)) (maximalIdeal V) ≃+*
      AdjoinRoot (g.map (residue V)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal V) g

/- English proof (translation)
Introduce `V _ _ _ hV _ N`. Take `⟨gb, hgbm, hgbi, hN⟩` from `exists_monic_irreducible_card_gt (ResidueField V) N`. Take `⟨g, hgmap, hgdeg, hg⟩` from `lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 (map_surjective (residue V) residue_surjective gb)) hgbm`. Substitute `hgmap` using the available equality. Use `set W := AdjoinRoot g`.

Establish `hirr : Irreducible g` using `Monic.irreducible_of_irreducible_map (residue V) g hg hgbi`. Establish `hdom : IsDomain W` using `AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr)`. Set `pb` to `AdjoinRoot.powerBasis' hg`. Establish `: Module.Finite V W` using `pb.finite`. Establish `: Algebra.IsIntegral V W` using `Algebra.IsIntegral.of_finite V W`.

Establish `: IsNoetherianRing W` using `IsNoetherianRing.of_finite V W`. Use `set M0 : Ideal W := Ideal.map (algebraMap V W) (maximalIdeal V) with hM0def`. Establish `: Fact (Irreducible (g.map (residue V)))` using `⟨hgbi⟩`. Establish `hM0 : M0.IsMaximal` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).2 (MulEquiv.isField (Field.toIsField (AdjoinRoot (g.map (residue V)))) (quotResidueEquiv g).toMulEquiv)`. Establish `hloc : IsLocalRing W` using `IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM => by`.

Establish `hc : (M.comap (algebraMap V W)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Establish `h1` using `eq_maximalIdeal hc`. Establish `hle : M0 ≤ M`. Rewrite using `[hM0def, ← h1]`. Conclude with `Ideal.map_comap_le`.

Conclude with `(hM0.eq_of_le hM.ne_top hle).symm⟩`. Establish `hmax : maximalIdeal W = M0` using `(eq_maximalIdeal hM0).symm`. Establish `hdeg : g.degree ≠ 0`. Introduce `h`. Establish `h0 : g.natDegree = 0` using `by rw [natDegree_eq_zero_iff_degree_le_zero, h]`.

Use `hgbi.natDegree_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hinj : Function.Injective (algebraMap V W)`. Rewrite using `[AdjoinRoot.algebraMap_eq]`. Conclude with `AdjoinRoot.of.injective_of_degree_ne_zero hdeg`.

Take `⟨⟨ϖ, hϖ⟩⟩` from `IsPrincipalIdealRing.principal (maximalIdeal V)`. Establish `hprin : (maximalIdeal W).IsPrincipal`. Use `⟨⟨algebraMap V W ϖ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hmax, hM0def, hϖ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]`. Establish `hnf : ¬ IsField W`.

Introduce `hf`. Establish `h1 : maximalIdeal W = ⊥` using `(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf`. Rewrite `h1` using `[hmax, hM0def, Ideal.map_eq_bot_iff_of_injective hinj]`. Conclude with `IsDiscreteValuationRing.not_a_field V h1`. Establish `hdvr : IsDiscreteValuationRing W` using `((IsDiscreteValuationRing.TFAE W hnf).out 0 4).2 hprin`.

Establish `ecard : Nat.card (ResidueField W) = Nat.card (AdjoinRoot (g.map (residue V)))` using `Nat.card_congr ((Ideal.quotEquivOfEq hmax).trans (quotResidueEquiv g)).toEquiv`. Use `⟨W, inferInstance, hdom, hdvr, inferInstance, ?_, ?_, ?_, hinj, ?_⟩` and prove the remaining obligations. Rewrite using `[hmax, hM0def, IsAdicComplete.map_algebraMap_iff]`. Conclude with `isAdicComplete_of_basis _ pb.basis hV`. Conclude with `Nat.finite_of_card_ne_zero (by omega)`.

Use linear arithmetic over natural numbers and integers. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `h1 : a ∈ maximalIdeal V` using `(mem_maximalIdeal a).2 hna`. Establish `h2 : algebraMap V W a ∈ maximalIdeal W`.

Rewrite using `[hmax]`. Conclude with `Ideal.mem_map_of_mem _ h1`. Conclude with `(mem_maximalIdeal _).1 h2 ha`.
-/
theorem largeResidueExtension : BigResExt := by
  intro V _ _ _ hV _ N
  obtain ⟨gb, hgbm, hgbi, hN⟩ := exists_monic_irreducible_card_gt (ResidueField V) N
  obtain ⟨g, hgmap, hgdeg, hg⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).2 (map_surjective (residue V) residue_surjective gb)) hgbm
  subst hgmap
  set W := AdjoinRoot g
  have hirr : Irreducible g := Monic.irreducible_of_irreducible_map (residue V) g hg hgbi
  have hdom : IsDomain W := AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr)
  let pb := AdjoinRoot.powerBasis' hg
  have : Module.Finite V W := pb.finite
  have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  set M0 : Ideal W := Ideal.map (algebraMap V W) (maximalIdeal V) with hM0def
  have : Fact (Irreducible (g.map (residue V))) := ⟨hgbi⟩
  have hM0 : M0.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).2
    (MulEquiv.isField (Field.toIsField (AdjoinRoot (g.map (residue V)))) (quotResidueEquiv g).toMulEquiv)
  have hloc : IsLocalRing W := IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM => by
    have hc : (M.comap (algebraMap V W)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h1 := eq_maximalIdeal hc
    have hle : M0 ≤ M := by
      rw [hM0def, ← h1]
      exact Ideal.map_comap_le
    exact (hM0.eq_of_le hM.ne_top hle).symm⟩
  have hmax : maximalIdeal W = M0 := (eq_maximalIdeal hM0).symm
  have hdeg : g.degree ≠ 0 := by
    intro h
    have h0 : g.natDegree = 0 := by rw [natDegree_eq_zero_iff_degree_le_zero, h]
    have := hgbi.natDegree_pos
    omega
  have hinj : Function.Injective (algebraMap V W) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  obtain ⟨⟨ϖ, hϖ⟩⟩ := IsPrincipalIdealRing.principal (maximalIdeal V)
  have hprin : (maximalIdeal W).IsPrincipal := by
    refine ⟨⟨algebraMap V W ϖ, ?_⟩⟩
    rw [hmax, hM0def, hϖ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField W := by
    intro hf
    have h1 : maximalIdeal W = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hf
    rw [hmax, hM0def, Ideal.map_eq_bot_iff_of_injective hinj] at h1
    exact IsDiscreteValuationRing.not_a_field V h1
  have hdvr : IsDiscreteValuationRing W := ((IsDiscreteValuationRing.TFAE W hnf).out 0 4).2 hprin
  have ecard : Nat.card (ResidueField W) = Nat.card (AdjoinRoot (g.map (residue V))) :=
    Nat.card_congr ((Ideal.quotEquivOfEq hmax).trans (quotResidueEquiv g)).toEquiv
  refine ⟨W, inferInstance, hdom, hdvr, inferInstance, ?_, ?_, ?_, hinj, ?_⟩
  · rw [hmax, hM0def, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis _ pb.basis hV
  · exact Nat.finite_of_card_ne_zero (by omega)
  · omega
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal V := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap V W a ∈ maximalIdeal W := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha

end Formalism.L2.LamCM
