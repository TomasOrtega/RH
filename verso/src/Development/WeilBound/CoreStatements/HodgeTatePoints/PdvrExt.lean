import Mathlib

namespace PositivityTheory.HtPt.Pdvr

open Polynomial IsLocalRing

/- English proof (translation)
Take `⟨P, hP, hdeg, hPm⟩` from `lifts_and_degree_eq_and_monic ((mem_lifts q).mpr (map_surjective (residue V) residue_surjective q)) hm`. Establish `hPi : Irreducible P` using `Monic.irreducible_of_irreducible_map (residue V) P hPm (hP ▸ hq)`. Establish `: IsDomain (AdjoinRoot P)` using `AdjoinRoot.isDomain_of_prime hPi.prime`. Establish `hinj : Function.Injective (AdjoinRoot.of P)` using `AdjoinRoot.of.injective_of_degree_ne_zero (hdeg ▸ (degree_pos_of_irreducible hq).ne')`. Establish `: Module.Finite V (AdjoinRoot P)` using `hPm.finite_adjoinRoot`.

Establish `hmax : (Ideal.map (AdjoinRoot.of P) (maximalIdeal V)).IsMaximal`. Apply `Ideal.Quotient.maximal_of_isField` to reduce the goal to its premises. Establish `: Fact (Irreducible (P.map (residue V)))` using `⟨hP ▸ hq⟩`. Establish `h1 : IsField (AdjoinRoot (P.map (residue V)))` using `Field.toIsField _`. Conclude with `MulEquiv.isField h1 (AdjoinRoot.quotEquivQuotMap P (maximalIdeal V)).toRingEquiv.toMulEquiv`.

Establish `huniq : ∀ M : Ideal (AdjoinRoot P), M.IsMaximal → M = Ideal.map (AdjoinRoot.of P) (maximalIdeal V)`. Introduce `M hM`. Establish `h1 : (M.comap (algebraMap V (AdjoinRoot P))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Establish `h2` using `eq_maximalIdeal h1`. Use `(hmax.eq_of_le hM.ne_top ?_).symm` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap, ← h2]`. Conclude with `le_rfl`. Establish `: IsLocalRing (AdjoinRoot P)` using `.of_unique_max_ideal ⟨_, hmax, huniq⟩`. Establish `hme : maximalIdeal (AdjoinRoot P) = Ideal.map (AdjoinRoot.of P) (maximalIdeal V)` using `huniq _ inferInstance`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`.

Establish `hme' : maximalIdeal (AdjoinRoot P) = Ideal.span {AdjoinRoot.of P π}`. Rewrite using `[hme, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Establish `hnf : ¬ IsField (AdjoinRoot P)`. Rewrite using `[isField_iff_maximalIdeal_eq, hme', Ideal.span_singleton_eq_bot]`. Conclude with `fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))`.

Establish `: IsNoetherianRing (AdjoinRoot P)` using `IsNoetherianRing.of_finite V _`. Establish `hdvr : IsDiscreteValuationRing (AdjoinRoot P)` using `((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 0 4).mpr (show (maximalIdeal (AdjoinRoot P)).IsPrincipal from ⟨_, hme'⟩)`. Establish `hloc : IsLocalHom (AdjoinRoot.of P)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Establish `: AdjoinRoot.of P a ∈ maximalIdeal (AdjoinRoot P)` using `hme ▸ Ideal.mem_map_of_mem _ h`. Conclude with `this ha`. Use `⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, AdjoinRoot.of P, hloc, hinj, residue _ (AdjoinRoot.root P), ?_⟩` and prove the remaining obligations. Rewrite using `[← hP, Polynomial.map_map, ResidueField.map_comp_residue, IsRoot.def, eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]`.
-/
theorem exists_root (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (q : (ResidueField V)[X]) (hm : q.Monic) (hq : Irreducible q) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      ∃ a, (q.map (ResidueField.map f)).IsRoot a := by
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts q).mpr (map_surjective (residue V) residue_surjective q)) hm
  have hPi : Irreducible P :=
    Monic.irreducible_of_irreducible_map (residue V) P hPm (hP ▸ hq)
  have : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hPi.prime
  have hinj : Function.Injective (AdjoinRoot.of P) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (hdeg ▸ (degree_pos_of_irreducible hq).ne')
  have : Module.Finite V (AdjoinRoot P) := hPm.finite_adjoinRoot
  have hmax : (Ideal.map (AdjoinRoot.of P) (maximalIdeal V)).IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have : Fact (Irreducible (P.map (residue V))) := ⟨hP ▸ hq⟩
    have h1 : IsField (AdjoinRoot (P.map (residue V))) := Field.toIsField _
    exact MulEquiv.isField h1
      (AdjoinRoot.quotEquivQuotMap P (maximalIdeal V)).toRingEquiv.toMulEquiv
  have huniq : ∀ M : Ideal (AdjoinRoot P), M.IsMaximal →
      M = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) := by
    intro M hM
    have h1 : (M.comap (algebraMap V (AdjoinRoot P))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h2 := eq_maximalIdeal h1
    refine (hmax.eq_of_le hM.ne_top ?_).symm
    rw [Ideal.map_le_iff_le_comap, ← h2]
    exact le_rfl
  have : IsLocalRing (AdjoinRoot P) := .of_unique_max_ideal ⟨_, hmax, huniq⟩
  have hme : maximalIdeal (AdjoinRoot P) = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) :=
    huniq _ inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hme' : maximalIdeal (AdjoinRoot P) = Ideal.span {AdjoinRoot.of P π} := by
    rw [hme, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot P) := by
    rw [isField_iff_maximalIdeal_eq, hme', Ideal.span_singleton_eq_bot]
    exact fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have : IsNoetherianRing (AdjoinRoot P) := IsNoetherianRing.of_finite V _
  have hdvr : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 0 4).mpr
      (show (maximalIdeal (AdjoinRoot P)).IsPrincipal from ⟨_, hme'⟩)
  have hloc : IsLocalHom (AdjoinRoot.of P) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have : AdjoinRoot.of P a ∈ maximalIdeal (AdjoinRoot P) :=
      hme ▸ Ideal.mem_map_of_mem _ h
    exact this ha
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, AdjoinRoot.of P, hloc, hinj,
    residue _ (AdjoinRoot.root P), ?_⟩
  rw [← hP, Polynomial.map_map, ResidueField.map_comp_residue, IsRoot.def, eval_map,
    ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ _ q hq`. Conclude with `⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, inferInstance, Function.injective_id, (Splits.of_natDegree_eq_zero hq).map _⟩`. Consider the case `succ n ih`.

Introduce `V _ _ _ q hq`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hq`. Establish `hnu : ¬ IsUnit q` using `not_isUnit_of_natDegree_pos q (by omega)`.

Take `⟨g, hgm, hgi, hgd⟩` from `exists_monic_irreducible_factor q hnu`. Take `⟨R, _, _, _, f, _, hf, a, ha⟩` from `exists_root V g hgm hgi`. Establish `hr : (q.map (ResidueField.map f)).IsRoot a` using `ha.dvd (Polynomial.map_dvd _ hgd)`. Take `⟨q', hq'⟩` from `dvd_iff_isRoot.mpr hr`. Establish `hq1 : q.map (ResidueField.map f) ≠ 0` using `Polynomial.map_ne_zero hq0`.

Establish `hd : q'.natDegree = n`. Establish `h1` using `congrArg natDegree hq'`. Establish `h2 : q' ≠ 0`. Introduce and unpack `rfl`. Conclude with `hq1 (by rw [hq', mul_zero])`.

Rewrite `h1` using `[natDegree_map, natDegree_mul (X_sub_C_ne_zero a) h2, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Take `⟨S, _, _, _, f', _, hf', hs⟩` from `ih R q' hd`. Use `⟨S, inferInstance, inferInstance, inferInstance, f'.comp f, inferInstance, hf'.comp hf, ?_⟩` and prove the remaining obligations. Rewrite using `[ResidueField.map_comp, ← Polynomial.map_map, hq', Polynomial.map_mul]`.

Conclude with `((Splits.X_sub_C a).map _).mul hs`.
-/
theorem exists_splits (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (q : (ResidueField V)[X]), q.natDegree = n →
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      (q.map (ResidueField.map f)).Splits := by
  induction n with
  | zero =>
    intro V _ _ _ q hq
    exact ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, inferInstance,
      Function.injective_id, (Splits.of_natDegree_eq_zero hq).map _⟩
  | succ n ih =>
    intro V _ _ _ q hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
    have hnu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
    obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor q hnu
    obtain ⟨R, _, _, _, f, _, hf, a, ha⟩ := exists_root V g hgm hgi
    have hr : (q.map (ResidueField.map f)).IsRoot a := ha.dvd (Polynomial.map_dvd _ hgd)
    obtain ⟨q', hq'⟩ := dvd_iff_isRoot.mpr hr
    have hq1 : q.map (ResidueField.map f) ≠ 0 := Polynomial.map_ne_zero hq0
    have hd : q'.natDegree = n := by
      have h1 := congrArg natDegree hq'
      have h2 : q' ≠ 0 := by
        rintro rfl
        exact hq1 (by rw [hq', mul_zero])
      rw [natDegree_map, natDegree_mul (X_sub_C_ne_zero a) h2, natDegree_X_sub_C] at h1
      omega
    obtain ⟨S, _, _, _, f', _, hf', hs⟩ := ih R q' hd
    refine ⟨S, inferInstance, inferInstance, inferInstance, f'.comp f, inferInstance,
      hf'.comp hf, ?_⟩
    rw [ResidueField.map_comp, ← Polynomial.map_map, hq', Polynomial.map_mul]
    exact ((Splits.X_sub_C a).map _).mul hs

/- English proof (translation)
Set `R` to `AdicCompletion (maximalIdeal V) V`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Set `ϖ : R` to `algebraMap V R π`. Establish `hme : maximalIdeal R = Ideal.span {ϖ}`. Use `AdicCompletion.maximalIdeal_eq_map.trans ?_` and prove the remaining obligations.

Use `(congrArg (Ideal.map (algebraMap V R)) hπ.maximalIdeal_eq).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Establish `hreg : ∀ r : V, r ≠ 0 → ∀ x : R, algebraMap V R r * x = 0 → x = 0`. Introduce `r hr x hx`. Establish `h1 : IsSMulRegular R r` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)`.

Apply `h1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `r • x = r • (0 : R)`. Rewrite using `[smul_zero, Algebra.smul_def, hx]`. Establish `hfac : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), ϖ ^ n * u = x`. Introduce `x hx`.

Establish `hex : ∃ n : ℕ, ¬ ϖ ^ n ∣ x`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hx` to reduce the goal to its premises. Use `IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_` and prove the remaining obligations.

Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, hme, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h n`. Establish `h0 : Nat.find hex ≠ 0`. Introduce `h`. Use `Nat.find_spec hex` as an intermediate fact.

Rewrite `this` using `[h, pow_zero]`. Conclude with `this (one_dvd _)`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero h0`. Establish `h1 : ϖ ^ n ∣ x` using `not_not.mp (Nat.find_min hex (by omega))`. Take `⟨y, rfl⟩` from `h1`.

Establish `hy : IsUnit y`. Assume the negation of the conclusion as `h`. Establish `h2 : y ∈ maximalIdeal R` using `h`. Rewrite `h2` using `[hme, Ideal.mem_span_singleton]`. Establish `h3` using `Nat.find_spec hex`.

Rewrite `h3` using `[hn, pow_succ]`. Conclude with `h3 (mul_dvd_mul_left _ h2)`. Conclude with `⟨n, hy.unit, rfl⟩`. Establish `: NoZeroDivisors R` using `⟨fun {a b} hab => by`. Distinguish the cases in `ha : a = 0`.

Conclude with `Or.inl ha`. Use `right`. Take `⟨n, u, rfl⟩` from `hfac a ha`. Establish `h1 : algebraMap V R (π ^ n) * (u * b) = 0`. Rewrite using `[map_pow, ← mul_assoc]`.

Conclude with `hab`. Establish `h2` using `hreg _ (pow_ne_zero n hπ.ne_zero) _ h1`. Conclude with `(Units.mul_right_eq_zero u).mp h2⟩`. Establish `: IsDomain R` using `NoZeroDivisors.to_isDomain R`. Establish `hinj : Function.Injective (algebraMap V R)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h`. Conclude with `one_ne_zero (hreg a h 1 (by rw [ha, zero_mul]))`. Establish `hϖ0 : ϖ ≠ 0` using `fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))`.

Establish `hϖ : Irreducible ϖ`. Use `Prime.irreducible ((Ideal.span_singleton_prime hϖ0).mp ?_)` and prove the remaining obligations. Rewrite using `[← hme]`. Use `infer_instance`. Establish `hdvr : IsDiscreteValuationRing R` using `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hϖ, fun {x} hx => hfac x hx⟩`.

Conclude with `⟨R, inferInstance, inferInstance, hdvr, algebraMap V R, inferInstance, (inferInstance : IsAdicComplete (maximalIdeal R) R), hinj⟩`.
-/
theorem exists_complete (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), IsAdicComplete (maximalIdeal R) R ∧
      Function.Injective f := by
  classical
  let R := AdicCompletion (maximalIdeal V) V
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ : R := algebraMap V R π
  have hme : maximalIdeal R = Ideal.span {ϖ} := by
    refine AdicCompletion.maximalIdeal_eq_map.trans ?_
    refine (congrArg (Ideal.map (algebraMap V R)) hπ.maximalIdeal_eq).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hreg : ∀ r : V, r ≠ 0 → ∀ x : R, algebraMap V R r * x = 0 → x = 0 := by
    intro r hr x hx
    have h1 : IsSMulRegular R r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    apply h1
    change r • x = r • (0 : R)
    rw [smul_zero, Algebra.smul_def, hx]
  have hfac : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), ϖ ^ n * u = x := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ ϖ ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hme, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact h n
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero] at this
      exact this (one_dvd _)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h1 : ϖ ^ n ∣ x := not_not.mp (Nat.find_min hex (by omega))
    obtain ⟨y, rfl⟩ := h1
    have hy : IsUnit y := by
      by_contra h
      have h2 : y ∈ maximalIdeal R := h
      rw [hme, Ideal.mem_span_singleton] at h2
      have h3 := Nat.find_spec hex
      rw [hn, pow_succ] at h3
      exact h3 (mul_dvd_mul_left _ h2)
    exact ⟨n, hy.unit, rfl⟩
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨n, u, rfl⟩ := hfac a ha
      have h1 : algebraMap V R (π ^ n) * (u * b) = 0 := by
        rw [map_pow, ← mul_assoc]
        exact hab
      have h2 := hreg _ (pow_ne_zero n hπ.ne_zero) _ h1
      exact (Units.mul_right_eq_zero u).mp h2⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hinj : Function.Injective (algebraMap V R) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    exact one_ne_zero (hreg a h 1 (by rw [ha, zero_mul]))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hϖ : Irreducible ϖ := by
    refine Prime.irreducible ((Ideal.span_singleton_prime hϖ0).mp ?_)
    rw [← hme]
    infer_instance
  have hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖ, hϖ, fun {x} hx => hfac x hx⟩
  exact ⟨R, inferInstance, inferInstance, hdvr, algebraMap V R, inferInstance,
    (inferInstance : IsAdicComplete (maximalIdeal R) R), hinj⟩

/- English proof (translation)
Introduce `V _ _ _ l _ _ _`. Set `b` to `Module.finBasis (ResidueField V) l`. Set `q : (ResidueField V)[X]` to `∏ i, minpoly (ResidueField V) (b i)`. Establish `hint : ∀ x : l, IsIntegral (ResidueField V) x` using `fun x => Algebra.IsIntegral.isIntegral x`. Establish `hq0 : q ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero (hint _)`.

Take `⟨S, _, _, _, f, _, hf, hs⟩` from `exists_splits _ V q rfl`. Take `⟨R, _, _, _, g, _, hR, hg⟩` from `exists_complete S`. Establish `hs' : (q.map (ResidueField.map (g.comp f))).Splits`. Rewrite using `[ResidueField.map_comp, ← Polynomial.map_map]`. Conclude with `hs.map _`.

Set `: Algebra (ResidueField V) (ResidueField R)` to `(ResidueField.map (g.comp f)).toAlgebra`. Establish `htop : IntermediateField.adjoin (ResidueField V) (Set.range b) = ⊤`. Rewrite using `[IntermediateField.adjoin_eq_top_iff, eq_top_iff]`. Introduce `x _`. Establish `: x ∈ Submodule.span (ResidueField V) (Set.range b)`.

Rewrite using `[b.span_eq]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `Algebra.span_le_adjoin _ _ this`. Choose the witnesses or unpack the hypotheses as in `⟨s⟩ : Nonempty (l →ₐ[ResidueField V] ResidueField R) := by`. Use `IntermediateField.nonempty_algHom_of_adjoin_splits ?_ htop` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨hint _, ?_⟩` and prove the remaining obligations. Conclude with `hs'.of_dvd (Polynomial.map_ne_zero hq0) (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))`. Conclude with `⟨R, inferInstance, inferInstance, inferInstance, g.comp f, inferInstance, s.toRingHom, hR, hg.comp hf, s.comp_algebraMap⟩`.
-/
theorem dvr_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type)
    [Field l] [Algebra (IsLocalRing.ResidueField V) l]
    [FiniteDimensional (IsLocalRing.ResidueField V) l],
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧
        s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  intro V _ _ _ l _ _ _
  let b := Module.finBasis (ResidueField V) l
  let q : (ResidueField V)[X] := ∏ i, minpoly (ResidueField V) (b i)
  have hint : ∀ x : l, IsIntegral (ResidueField V) x := fun x => Algebra.IsIntegral.isIntegral x
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero (hint _)
  obtain ⟨S, _, _, _, f, _, hf, hs⟩ := exists_splits _ V q rfl
  obtain ⟨R, _, _, _, g, _, hR, hg⟩ := exists_complete S
  have hs' : (q.map (ResidueField.map (g.comp f))).Splits := by
    rw [ResidueField.map_comp, ← Polynomial.map_map]
    exact hs.map _
  let : Algebra (ResidueField V) (ResidueField R) := (ResidueField.map (g.comp f)).toAlgebra
  have htop : IntermediateField.adjoin (ResidueField V) (Set.range b) = ⊤ := by
    rw [IntermediateField.adjoin_eq_top_iff, eq_top_iff]
    intro x _
    have : x ∈ Submodule.span (ResidueField V) (Set.range b) := by
      rw [b.span_eq]
      trivial
    exact Algebra.span_le_adjoin _ _ this
  obtain ⟨s⟩ : Nonempty (l →ₐ[ResidueField V] ResidueField R) := by
    refine IntermediateField.nonempty_algHom_of_adjoin_splits ?_ htop
    rintro _ ⟨i, rfl⟩
    refine ⟨hint _, ?_⟩
    exact hs'.of_dvd (Polynomial.map_ne_zero hq0)
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  exact ⟨R, inferInstance, inferInstance, inferInstance, g.comp f, inferInstance, s.toRingHom,
    hR, hg.comp hf, s.comp_algebraMap⟩

end PositivityTheory.HtPt.Pdvr
