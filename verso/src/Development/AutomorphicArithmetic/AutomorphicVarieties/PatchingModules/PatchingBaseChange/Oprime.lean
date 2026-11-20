import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on (p := fun y : Fin r → R => ∀ i, y i ∈ J) hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Simplify using `using J.mul_mem_right (y i) ha`. Simplify using `using J.add_mem (ha i) (hb i)`.

Introduce `hx`. Rewrite using `[← Finset.univ_sum_single x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hs : (Pi.single i (x i) : Fin r → R) = x i • (Pi.single i 1 : Fin r → R)`. Use extensionality with `j`.

Break down `eq_or_ne j i with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[hs]`. Conclude with `Submodule.smul_mem_smul (hx i) trivial`.
-/
private theorem op_mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y : Fin r → R => ∀ i, y i ∈ J) hx
      (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · simpa using J.mul_mem_right (y i) ha
    · simpa using J.add_mem (ha i) (hb i)
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hs : (Pi.single i (x i) : Fin r → R) = x i • (Pi.single i 1 : Fin r → R) := by
      ext j
      rcases eq_or_ne j i with rfl | h
      · simp
      · simp [h]
    rw [hs]
    exact Submodule.smul_mem_smul (hx i) trivial

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]`. Introduce `i`. Use `IsPrecomplete.prec' (I := I) (fun n => f n i) (fun {m n} hmn => ?_)` and prove the remaining obligations. Establish `h` using `hf hmn`.

Rewrite `h` using `[SModEq.sub_mem, op_mem_smul_top_pi]`. Rewrite using `[SModEq.sub_mem]`. Simplify `h i` using `[smul_eq_mul, Ideal.mul_top]`. Use `choose L hL using hc`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem, op_mem_smul_top_pi]`. Introduce `i`. Establish `h` using `hL i n`. Rewrite `h` using `[SModEq.sub_mem]`. Simplify `h` using `[smul_eq_mul, Ideal.mul_top]`.
-/
private theorem op_isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (I := I) (fun n => f n i) (fun {m n} hmn => ?_)
    have h := hf hmn
    rw [SModEq.sub_mem, op_mem_smul_top_pi] at h
    rw [SModEq.sub_mem]
    simpa [smul_eq_mul, Ideal.mul_top] using h i
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, op_mem_smul_top_pi]
  intro i
  have h := hL i n
  rw [SModEq.sub_mem] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

/- English proof (translation)
Take `⟨r, φ, hφ⟩` from `Module.Finite.exists_fin' R M`. Use `haveI := op_isPrecomplete_pi I r`. Establish `hmap : ∀ n, (I ^ n • ⊤ : Submodule R M) = (I ^ n • ⊤ : Submodule R (Fin r → R)).map φ`. Introduce `n`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]`.

Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ n, ∃ d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)), φ d = f (n + 1) - f n`. Introduce `n`. Establish `h` using `hf (Nat.le_succ n)`. Rewrite `h` using `[SModEq.sub_mem, hmap]`.

Take `⟨d, hd, he⟩` from `h`. Conclude with `⟨-d, Submodule.neg_mem _ hd, by rw [map_neg, he, neg_sub]⟩`. Use `choose d hdm hde using hd`. Take `⟨x0, hx0⟩` from `hφ (f 0)`. Set `F : ℕ → Fin r → R` to `fun n => x0 + ∑ k ∈ Finset.range n, d k`.

Establish `hF : ∀ n, φ (F n) = f n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [F, hx0]`. Consider the case `succ n ih`.

Simplify using `only [F, Finset.sum_range_succ, ← add_assoc, map_add] at ih ⊢`. Rewrite using `[ih, hde]`. Normalize the expressions using the abelian group laws. Establish `hFc : ∀ {m n}, m ≤ n → F m ≡ F n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))]`. Introduce `m n hmn`.

Rewrite using `[SModEq.sub_mem]`. Establish `he : F m - F n = -∑ k ∈ Finset.Ico m n, d k`. Simplify using `only [F]`. Rewrite using `[← Finset.sum_range_add_sum_Ico _ hmn]`. Normalize the expressions using the abelian group laws.

Rewrite using `[he]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1) (hdm k)`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' F hFc`. Use `⟨φ L, fun n => ?_⟩` and prove the remaining obligations.

Establish `h` using `hL n`. Rewrite `h`, the goal using `[SModEq.sub_mem]`. Rewrite using `[hmap, ← hF n, ← map_sub]`. Conclude with `Submodule.mem_map_of_mem h`.
-/
private theorem op_isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, φ, hφ⟩ := Module.Finite.exists_fin' R M
  haveI := op_isPrecomplete_pi I r
  have hmap : ∀ n, (I ^ n • ⊤ : Submodule R M) = (I ^ n • ⊤ : Submodule R (Fin r → R)).map φ := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)), φ d = f (n + 1) - f n := by
    intro n
    have h := hf (Nat.le_succ n)
    rw [SModEq.sub_mem, hmap] at h
    obtain ⟨d, hd, he⟩ := h
    exact ⟨-d, Submodule.neg_mem _ hd, by rw [map_neg, he, neg_sub]⟩
  choose d hdm hde using hd
  obtain ⟨x0, hx0⟩ := hφ (f 0)
  let F : ℕ → Fin r → R := fun n => x0 + ∑ k ∈ Finset.range n, d k
  have hF : ∀ n, φ (F n) = f n := by
    intro n
    induction n with
    | zero => simp [F, hx0]
    | succ n ih =>
      simp only [F, Finset.sum_range_succ, ← add_assoc, map_add] at ih ⊢
      rw [ih, hde]
      abel
  have hFc : ∀ {m n}, m ≤ n → F m ≡ F n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have he : F m - F n = -∑ k ∈ Finset.Ico m n, d k := by
      simp only [F]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [he]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1) (hdm k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' F hFc
  refine ⟨φ L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem] at h ⊢
  rw [hmap, ← hF n, ← map_sub]
  exact Submodule.mem_map_of_mem h

/- English proof (translation)
Establish `hne : RingHom.ker (algebraMap O K) ≠ ⊥`. Introduce `h`. Establish `hinj : Function.Injective (algebraMap O K)` using `(RingHom.injective_iff_ker_eq_bot _).mpr h`. Use `haveI : Finite O := Finite.of_injective _ hinj`. Conclude with `IsDiscreteValuationRing.not_a_field' (IsLocalRing.isField_iff_maximalIdeal_eq.mp (Finite.isField_of_domain O))`.

Establish `hmax : (RingHom.ker (algebraMap O K)).IsMaximal` using `Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hne`. Establish `hker : RingHom.ker (algebraMap O K) = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hmax`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`. Establish `hxm : x ∈ maximalIdeal O` using `hnu`.

Rewrite `hxm` using `[← hker, RingHom.mem_ker]`. Rewrite `hx` using `[hxm]`. Conclude with `not_isUnit_zero hx`.
-/
private theorem op_localHom (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Finite K] [Algebra O K] : IsLocalHom (algebraMap O K) := by
  have hne : RingHom.ker (algebraMap O K) ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (algebraMap O K) := (RingHom.injective_iff_ker_eq_bot _).mpr h
    haveI : Finite O := Finite.of_injective _ hinj
    exact IsDiscreteValuationRing.not_a_field' (IsLocalRing.isField_iff_maximalIdeal_eq.mp
      (Finite.isField_of_domain O))
  have hmax : (RingHom.ker (algebraMap O K)).IsMaximal :=
    Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hne
  have hker : RingHom.ker (algebraMap O K) = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  refine ⟨fun x hx => ?_⟩
  by_contra hnu
  have hxm : x ∈ maximalIdeal O := hnu
  rw [← hker, RingHom.mem_ker] at hxm
  rw [hxm] at hx
  exact not_isUnit_zero hx

open Polynomial in
/- English proof (translation)
Introduce `l _ O _ _ _ _ K _ _ _`. Use `haveI := op_localHom O K`. Use `letI : Algebra (ResidueField O) K := (IsLocalRing.ResidueField.lift (algebraMap O K)).toAlgebra`. Use `haveI : Finite (ResidueField O) := IsCoef.finite (l := l)`. Use `haveI : Fintype K := Fintype.ofFinite K`.

Use `haveI : Fintype (ResidueField O) := Fintype.ofFinite _`. Take `⟨α, hα⟩` from `Field.exists_primitive_element (ResidueField O) K`. Establish `hαi : IsIntegral (ResidueField O) α` using `.of_finite _ α`. Establish `hgi : Irreducible (minpoly (ResidueField O) α)` using `minpoly.irreducible hαi`. Establish `hgm : (minpoly (ResidueField O) α).Monic` using `minpoly.monic hαi`.

Take `⟨P, hPmap, -, hPmon⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic (f := IsLocalRing.residue O) (p := minpoly (ResidueField O) α) (by`. Rewrite using `[Polynomial.lifts_iff_set_range, (Polynomial.map_surjective _ IsLocalRing.residue_surjective).range_eq]`. Use the proof step `trivial) hgm`. Use `haveI : Module.Finite O (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPmon).finite`. Use `haveI : Module.Free O (AdjoinRoot P) := Module.Free.of_basis (AdjoinRoot.powerBasis' hPmon).basis`.

Use `set M : Ideal (AdjoinRoot P) := (maximalIdeal O).map (algebraMap O (AdjoinRoot P)) with hM`. Set `e0 : AdjoinRoot (P.map (IsLocalRing.residue O)) ≃+* AdjoinRoot (minpoly (ResidueField O) α)` to `by`. Rewrite using `[hPmap]`. Set `e1 : AdjoinRoot P ⧸ M ≃+* AdjoinRoot (minpoly (ResidueField O) α)` to `(AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal O) P).trans e0`. Set `eK : AdjoinRoot P ⧸ M ≃+* K` to `e1.trans ((IntermediateField.adjoinRootEquivAdjoin _ hαi).toRingEquiv.trans ((IntermediateField.equivOfEq hα).toRingEquiv.trans IntermediateField.topEquiv.toRingEquiv))`.

Establish `hMmax : M.IsMaximal` using `Ideal.Quotient.maximal_of_isField M (MulEquiv.isField (Field.toIsField K) eK.toMulEquiv)`. Use `haveI hloc : IsLocalRing (AdjoinRoot P) := by`. Use `IsLocalRing.of_unique_max_ideal ⟨M, hMmax, fun Q hQ => ?_⟩` and prove the remaining obligations. Establish `hc : (Q.comap (algebraMap O (AdjoinRoot P))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q`. Establish `hle : M ≤ Q` using `Ideal.map_le_iff_le_comap.mpr (IsLocalRing.eq_maximalIdeal hc).symm.le`.

Conclude with `(hMmax.eq_of_le hQ.ne_top hle).symm`. Establish `hMeq : M = maximalIdeal (AdjoinRoot P)` using `IsLocalRing.eq_maximalIdeal hMmax`. Use `haveI : IsNoetherianRing (AdjoinRoot P) := isNoetherian_of_tower O inferInstance`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Use `set π : AdjoinRoot P := algebraMap O (AdjoinRoot P) ϖ with hπ`.

Establish `hMspan : M = Ideal.span {π}`. Rewrite using `[hM, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Establish `hinj : Function.Injective (algebraMap O (AdjoinRoot P))` using `FaithfulSMul.algebraMap_injective O (AdjoinRoot P)`. Establish `hπn : ∀ n : ℕ, π ^ n ≠ 0`. Introduce `n h`.

Rewrite `h` using `[hπ, ← map_pow]`. Conclude with `pow_ne_zero n hϖ.ne_zero (hinj (h.trans (map_zero _).symm))`. Establish `hKrull : ⨅ i : ℕ, M ^ i = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing M hMmax.ne_top`. Establish `hfac : ∀ x : AdjoinRoot P, x ≠ 0 → ∃ n : ℕ, ∃ u : AdjoinRoot P, IsUnit u ∧ x = π ^ n * u`. Introduce `x hx`.

Establish `hex : ∃ i : ℕ, x ∉ M ^ i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hx` to reduce the goal to its premises. Establish `hmem : x ∈ ⨅ i : ℕ, M ^ i` using `Submodule.mem_iInf _ |>.mpr h`.

Rewrite `hmem` using `[hKrull]`. Conclude with `hmem`. Take `⟨i, hi, hmin⟩ : ∃ i, x ∉ M ^ i ∧ ∀ j < i, x ∈ M ^ j` from `⟨Nat.find hex, Nat.find_spec hex, fun j hj => by simpa using Nat.find_min hex hj⟩`. Establish `hi0 : i ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hi (by simp)`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Establish `hxj` using `hmin j (by omega)`. Rewrite `hxj` using `[hMspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨u, hu⟩` from `hxj`.

Use `⟨j, u, ?_, by rw [← hu, mul_comm]⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu'`. Establish `hum : u ∈ maximalIdeal (AdjoinRoot P)` using `(IsLocalRing.mem_maximalIdeal _).mpr hu'`. Rewrite `hum` using `[← hMeq, hMspan, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hum`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hMspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Conclude with `⟨c, by rw [← hu, ← hc]; ring⟩`. Use `haveI : NoZeroDivisors (AdjoinRoot P) := ⟨fun {x y} hxy => by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Take `⟨a, u, hu, rfl⟩` from `hfac x h.1`. Take `⟨b, v, hv, rfl⟩` from `hfac y h.2`. Establish `h0 : π ^ (a + b) * (u * v) = 0` using `by rw [← hxy]; ring`. Conclude with `hπn (a + b) ((hu.mul hv).mul_left_eq_zero.mp h0)⟩`.

Use `haveI : IsDomain (AdjoinRoot P) := NoZeroDivisors.to_isDomain _`. Establish `hnf : ¬ IsField (AdjoinRoot P)`. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← hMeq, hMspan, Ideal.span_singleton_eq_bot]`. Simplify using `using hπn 1`. Establish `hprin : (maximalIdeal (AdjoinRoot P)).IsPrincipal` using `⟨⟨π, by rw [← hMeq, hMspan]⟩⟩`.

Use `haveI : IsDiscreteValuationRing (AdjoinRoot P) := ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 0 4).mpr hprin`. Establish `hsub : ∀ n : ℕ, ((maximalIdeal O ^ n • ⊤ : Submodule O (AdjoinRoot P)) : Set (AdjoinRoot P)) = ((maximalIdeal (AdjoinRoot P) ^ n • ⊤ : Submodule (AdjoinRoot P) (AdjoinRoot P)) : Set (AdjoinRoot P))`. Introduce `n`. Rewrite using `[Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top, ← hMeq, hM, Ideal.map_pow]`. Both sides reduce to the same expression.

Use `haveI : IsPrecomplete (maximalIdeal O) O := (IsCoef.complete (l := l) (O := O)).toIsPrecomplete`. Establish `hpre : IsPrecomplete (maximalIdeal O) (AdjoinRoot P)` using `op_isPrecomplete_finite (maximalIdeal O)`. Establish `hcomp : IsAdicComplete (maximalIdeal (AdjoinRoot P)) (AdjoinRoot P)`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`.

Establish `hmem : x ∈ ⨅ i : ℕ, M ^ i` using `(Submodule.mem_iInf _).mpr fun n => by`. Establish `h` using `hx n`. Rewrite `h` using `[SModEq.sub_mem, sub_zero]`. Rewrite using `[hMeq]`. Simplify `h` using `[smul_eq_mul, Ideal.mul_top]`.

Rewrite `hmem` using `[hKrull]`. Conclude with `hmem`. Introduce `f hf`. Take `⟨L, hL⟩` from `hpre.prec' f (fun {m n} hmn => by`. Establish `h` using `hf hmn`.

Rewrite `h`, the goal using `[SModEq.sub_mem]`. Rewrite using `[← SetLike.mem_coe, hsub]`. Conclude with `h)`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h` using `hL n`.

Rewrite `h`, the goal using `[SModEq.sub_mem]`. Rewrite using `[← SetLike.mem_coe, ← hsub]`. Conclude with `h`. Establish `hlh : IsLocalHom (algebraMap O (AdjoinRoot P))` using `⟨fun x hx => by`. Assume the negation of the conclusion as `hnu`.

Establish `hxm : x ∈ maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr hnu`. Establish `hm : algebraMap O (AdjoinRoot P) x ∈ maximalIdeal (AdjoinRoot P)`. Rewrite using `[← hMeq]`. Conclude with `Ideal.mem_map_of_mem _ hxm`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hm hx⟩`.

Set `eR : ResidueField (AdjoinRoot P) ≃+* K` to `(Ideal.quotEquivOfEq hMeq.symm).trans eK`. Use `haveI hfin : Finite (ResidueField (AdjoinRoot P)) := Finite.of_equiv K eR.symm.toEquiv`. Use `haveI : CharP (ResidueField O) l := IsCoef.char`. Establish `hchar : CharP (ResidueField (AdjoinRoot P)) l` using `charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap O (AdjoinRoot P))).injective l`. Use `⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, AdjoinRoot.root P, P, ⟨hcomp, hfin, hchar⟩, inferInstance, inferInstance, hlh, Nat.card_congr eR.toEquiv, AdjoinRoot.adjoinRoot_eq_top, hPmon, by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], ?_⟩` and prove the remaining obligations.

Introduce `K' _ _ _ hK'`. Use `haveI := op_localHom O K'`. Use `haveI : Fintype K' := Fintype.ofFinite K'`. Establish `hφ : algebraMap O K' = (IsLocalRing.ResidueField.lift (algebraMap O K')).comp (IsLocalRing.residue O)` using `(IsLocalRing.ResidueField.lift_comp_residue _).symm`. Rewrite using `[hφ, ← Polynomial.map_map, hPmap]`.

Establish `hcard : Fintype.card K' = Fintype.card K`. Rewrite using `[← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK']`. Establish `hdvd : minpoly (ResidueField O) α ∣ (X ^ Fintype.card K - X : (ResidueField O)[X])` using `minpoly.dvd _ _ (by simp [FiniteField.pow_card])`. Establish `hsplit : (X ^ Fintype.card K' - X : K'[X]).Splits`. Rewrite using `[Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K' Fintype.one_lt_card]`.

Establish `hne : (X ^ Fintype.card K' - X : K'[X]) ≠ 0`. Introduce `h`. Use `FiniteField.X_pow_card_sub_X_natDegree_eq K' (Fintype.one_lt_card (α := K'))` as an intermediate fact. Rewrite `this` using `[h, Polynomial.natDegree_zero]`. Conclude with `Fintype.card_ne_zero this.symm`.

Use `hsplit.of_dvd hne ?_` and prove the remaining obligations. Rewrite using `[hcard]`. Simplify using `using Polynomial.map_dvd (IsLocalRing.ResidueField.lift (algebraMap O K')) hdvd`.
-/
theorem UpperTheory.V.Pa.BC.oprime :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] (K : Type) [Field K] [Finite K] [Algebra O K], ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (α : O') (P : Polynomial O), IsCoef l O' ∧ Module.Finite O O' ∧ Module.Free O O' ∧ IsLocalHom (algebraMap O O') ∧ Nat.card (ResidueField O') = Nat.card K ∧ Algebra.adjoin O {α} = ⊤ ∧ P.Monic ∧ Polynomial.aeval α P = 0 ∧ ∀ (K' : Type) [Field K'] [Finite K'] [Algebra O K'], Nat.card K' = Nat.card K → (P.map (algebraMap O K')).Splits := by
  intro l _ O _ _ _ _ K _ _ _
  classical
  haveI := op_localHom O K
  letI : Algebra (ResidueField O) K := (IsLocalRing.ResidueField.lift (algebraMap O K)).toAlgebra
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField O) K
  have hαi : IsIntegral (ResidueField O) α := .of_finite _ α
  have hgi : Irreducible (minpoly (ResidueField O) α) := minpoly.irreducible hαi
  have hgm : (minpoly (ResidueField O) α).Monic := minpoly.monic hαi
  obtain ⟨P, hPmap, -, hPmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := IsLocalRing.residue O) (p := minpoly (ResidueField O) α)
    (by
      rw [Polynomial.lifts_iff_set_range,
        (Polynomial.map_surjective _ IsLocalRing.residue_surjective).range_eq]
      trivial) hgm
  haveI : Module.Finite O (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPmon).finite
  haveI : Module.Free O (AdjoinRoot P) := Module.Free.of_basis (AdjoinRoot.powerBasis' hPmon).basis
  set M : Ideal (AdjoinRoot P) := (maximalIdeal O).map (algebraMap O (AdjoinRoot P)) with hM
  let e0 : AdjoinRoot (P.map (IsLocalRing.residue O)) ≃+* AdjoinRoot (minpoly (ResidueField O) α) := by
    rw [hPmap]
  let e1 : AdjoinRoot P ⧸ M ≃+* AdjoinRoot (minpoly (ResidueField O) α) :=
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal O) P).trans e0
  let eK : AdjoinRoot P ⧸ M ≃+* K :=
    e1.trans ((IntermediateField.adjoinRootEquivAdjoin _ hαi).toRingEquiv.trans
      ((IntermediateField.equivOfEq hα).toRingEquiv.trans IntermediateField.topEquiv.toRingEquiv))
  have hMmax : M.IsMaximal :=
    Ideal.Quotient.maximal_of_isField M (MulEquiv.isField (Field.toIsField K) eK.toMulEquiv)
  haveI hloc : IsLocalRing (AdjoinRoot P) := by
    refine IsLocalRing.of_unique_max_ideal ⟨M, hMmax, fun Q hQ => ?_⟩
    have hc : (Q.comap (algebraMap O (AdjoinRoot P))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    have hle : M ≤ Q := Ideal.map_le_iff_le_comap.mpr (IsLocalRing.eq_maximalIdeal hc).symm.le
    exact (hMmax.eq_of_le hQ.ne_top hle).symm
  have hMeq : M = maximalIdeal (AdjoinRoot P) := IsLocalRing.eq_maximalIdeal hMmax
  haveI : IsNoetherianRing (AdjoinRoot P) := isNoetherian_of_tower O inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π : AdjoinRoot P := algebraMap O (AdjoinRoot P) ϖ with hπ
  have hMspan : M = Ideal.span {π} := by
    rw [hM, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap O (AdjoinRoot P)) :=
    FaithfulSMul.algebraMap_injective O (AdjoinRoot P)
  have hπn : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n h
    rw [hπ, ← map_pow] at h
    exact pow_ne_zero n hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hKrull : ⨅ i : ℕ, M ^ i = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing M hMmax.ne_top
  have hfac : ∀ x : AdjoinRoot P, x ≠ 0 → ∃ n : ℕ, ∃ u : AdjoinRoot P, IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ i : ℕ, x ∉ M ^ i := by
      by_contra h
      push_neg at h
      apply hx
      have hmem : x ∈ ⨅ i : ℕ, M ^ i := Submodule.mem_iInf _ |>.mpr h
      rw [hKrull] at hmem
      exact hmem
    obtain ⟨i, hi, hmin⟩ : ∃ i, x ∉ M ^ i ∧ ∀ j < i, x ∈ M ^ j :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by simpa using Nat.find_min hex hj⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hi (by simp)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hxj := hmin j (by omega)
    rw [hMspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hxj
    obtain ⟨u, hu⟩ := hxj
    refine ⟨j, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal (AdjoinRoot P) := (IsLocalRing.mem_maximalIdeal _).mpr hu'
    rw [← hMeq, hMspan, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, hc⟩ := hum
    apply hi
    rw [hMspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← hu, ← hc]; ring⟩
  haveI : NoZeroDivisors (AdjoinRoot P) := ⟨fun {x y} hxy => by
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv, rfl⟩ := hfac y h.2
    have h0 : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact hπn (a + b) ((hu.mul hv).mul_left_eq_zero.mp h0)⟩
  haveI : IsDomain (AdjoinRoot P) := NoZeroDivisors.to_isDomain _
  have hnf : ¬ IsField (AdjoinRoot P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hMeq, hMspan, Ideal.span_singleton_eq_bot]
    simpa using hπn 1
  have hprin : (maximalIdeal (AdjoinRoot P)).IsPrincipal := ⟨⟨π, by rw [← hMeq, hMspan]⟩⟩
  haveI : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 0 4).mpr hprin
  have hsub : ∀ n : ℕ, ((maximalIdeal O ^ n • ⊤ : Submodule O (AdjoinRoot P)) : Set (AdjoinRoot P))
      = ((maximalIdeal (AdjoinRoot P) ^ n • ⊤ : Submodule (AdjoinRoot P) (AdjoinRoot P)) : Set (AdjoinRoot P)) := by
    intro n
    rw [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top, ← hMeq, hM, Ideal.map_pow]
    rfl
  haveI : IsPrecomplete (maximalIdeal O) O := (IsCoef.complete (l := l) (O := O)).toIsPrecomplete
  have hpre : IsPrecomplete (maximalIdeal O) (AdjoinRoot P) := op_isPrecomplete_finite (maximalIdeal O)
  have hcomp : IsAdicComplete (maximalIdeal (AdjoinRoot P)) (AdjoinRoot P) := by
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      have hmem : x ∈ ⨅ i : ℕ, M ^ i := (Submodule.mem_iInf _).mpr fun n => by
        have h := hx n
        rw [SModEq.sub_mem, sub_zero] at h
        rw [hMeq]
        simpa [smul_eq_mul, Ideal.mul_top] using h
      rw [hKrull] at hmem
      exact hmem
    · intro f hf
      obtain ⟨L, hL⟩ := hpre.prec' f (fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem] at h ⊢
        rw [← SetLike.mem_coe, hsub]
        exact h)
      refine ⟨L, fun n => ?_⟩
      have h := hL n
      rw [SModEq.sub_mem] at h ⊢
      rw [← SetLike.mem_coe, ← hsub]
      exact h
  have hlh : IsLocalHom (algebraMap O (AdjoinRoot P)) := ⟨fun x hx => by
    by_contra hnu
    have hxm : x ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm : algebraMap O (AdjoinRoot P) x ∈ maximalIdeal (AdjoinRoot P) := by
      rw [← hMeq]
      exact Ideal.mem_map_of_mem _ hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hx⟩
  let eR : ResidueField (AdjoinRoot P) ≃+* K := (Ideal.quotEquivOfEq hMeq.symm).trans eK
  haveI hfin : Finite (ResidueField (AdjoinRoot P)) := Finite.of_equiv K eR.symm.toEquiv
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hchar : CharP (ResidueField (AdjoinRoot P)) l :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap O (AdjoinRoot P))).injective l
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, AdjoinRoot.root P, P,
    ⟨hcomp, hfin, hchar⟩, inferInstance, inferInstance, hlh, Nat.card_congr eR.toEquiv,
    AdjoinRoot.adjoinRoot_eq_top, hPmon, by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], ?_⟩
  intro K' _ _ _ hK'
  haveI := op_localHom O K'
  haveI : Fintype K' := Fintype.ofFinite K'
  have hφ : algebraMap O K' = (IsLocalRing.ResidueField.lift (algebraMap O K')).comp (IsLocalRing.residue O) :=
    (IsLocalRing.ResidueField.lift_comp_residue _).symm
  rw [hφ, ← Polynomial.map_map, hPmap]
  have hcard : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK']
  have hdvd : minpoly (ResidueField O) α ∣ (X ^ Fintype.card K - X : (ResidueField O)[X]) :=
    minpoly.dvd _ _ (by simp [FiniteField.pow_card])
  have hsplit : (X ^ Fintype.card K' - X : K'[X]).Splits := by
    rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def,
      Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K' Fintype.one_lt_card]
  have hne : (X ^ Fintype.card K' - X : K'[X]) ≠ 0 := by
    intro h
    have := FiniteField.X_pow_card_sub_X_natDegree_eq K' (Fintype.one_lt_card (α := K'))
    rw [h, Polynomial.natDegree_zero] at this
    exact Fintype.card_ne_zero this.symm
  refine hsplit.of_dvd hne ?_
  rw [hcard]
  simpa using Polynomial.map_dvd (IsLocalRing.ResidueField.lift (algebraMap O K')) hdvd
