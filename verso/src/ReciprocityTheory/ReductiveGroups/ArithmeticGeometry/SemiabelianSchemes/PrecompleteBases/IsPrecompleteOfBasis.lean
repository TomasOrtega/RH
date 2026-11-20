import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option autoImplicit false

open IsLocalRing Polynomial

namespace ReciprocityTheory.ChartRestriction.G.Semi

namespace Nb

section Coord
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
lemma coord_mem_of_mem (b : Module.Basis ι R M) (J : Ideal R) {x : M}
    (hx : x ∈ (J • ⊤ : Submodule R M)) (i : ι) : b.repr x i ∈ J := by
  have key : (J • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) J := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  simpa using key hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma mem_of_coord_mem (b : Module.Basis ι R M) (J : Ideal R) {x : M}
    (h : ∀ i, b.repr x i ∈ J) : x ∈ (J • ⊤ : Submodule R M) := by
  rw [← b.sum_repr x]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma isPrecomplete_of_basis (I : Ideal R) [IsPrecomplete I R] (b : Module.Basis ι R M) :
    IsPrecomplete I M := by
  have hI : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) ?_
    intro m n hmn
    have h0 := coord_mem_of_mem b (I ^ m) (SModEq.sub_mem.mp (hf hmn)) i
    rw [SModEq.sub_mem, hI]
    simpa using h0
  choose L hL using key
  refine ⟨∑ i, L i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem]
  apply mem_of_coord_mem b
  intro i
  have h1 := hL i n
  rw [SModEq.sub_mem, hI] at h1
  have hs : b.repr (f n - ∑ j, L j • b j) i = b.repr (f n) i - L i := by
    rw [map_sub, Finsupp.sub_apply, map_sum, Finsupp.finset_sum_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj, Ne.symm hj]
    · simp
  rw [hs]
  exact h1

end Coord

section Step
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
lemma exists_monic_lift (g : (ResidueField V)[X]) (hg : g.Monic) :
    ∃ f : V[X], f.map (residue V) = g ∧ f.natDegree = g.natDegree ∧ f.Monic := by
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue V) residue_surjective g
  exact lifts_and_natDegree_eq_and_monic ((mem_lifts g).2 ⟨q, hq⟩) hg

variable (f : V[X]) (hf : f.Monic) (hg : Irreducible (f.map (residue V)))
include hf hg

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma irr : Irreducible f := by
  exact Polynomial.Monic.irreducible_of_irreducible_map (residue V) f hf hg

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma isDomain : IsDomain (AdjoinRoot f) := by
  exact AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irr f hf hg))

omit hg in
/- English proof (translation)
A detailed English derivation is pending.
-/
lemma finite : Module.Finite V (AdjoinRoot f) := by
  exact (AdjoinRoot.powerBasis' hf).finite

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma natDeg_pos : 0 < f.natDegree := by
  rw [← hf.natDegree_map (residue V)]
  exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hg)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma inj : Function.Injective (algebraMap V (AdjoinRoot f)) := by
  rw [AdjoinRoot.algebraMap_eq]
  refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
  rw [degree_eq_natDegree hf.ne_zero]
  exact_mod_cast (natDeg_pos f hf hg).ne'

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma quot_isField : IsField (AdjoinRoot f ⧸ (maximalIdeal V).map (AdjoinRoot.of f)) := by
  haveI : Fact (Irreducible (f.map (residue V))) := ⟨hg⟩
  have e := (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv
  first
  | exact MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V)))) e.toMulEquiv
  | exact MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V)))) e.symm.toMulEquiv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma J_max : ((maximalIdeal V).map (algebraMap V (AdjoinRoot f))).IsMaximal := by
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _ (quot_isField f hf hg)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma isLocal : IsLocalRing (AdjoinRoot f) := by
  haveI := finite f hf
  refine IsLocalRing.of_unique_max_ideal ⟨_, J_max f hf hg, fun P hP => ?_⟩
  haveI := hP
  have hc : P.comap (algebraMap V (AdjoinRoot f)) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
  have hle : (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) ≤ P := by
    rw [← hc]
    exact Ideal.map_comap_le
  exact ((J_max f hf hg).eq_of_le hP.ne_top hle).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma maxEq [IsLocalRing (AdjoinRoot f)] :
    maximalIdeal (AdjoinRoot f) = (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) := by
  exact (IsLocalRing.eq_maximalIdeal (J_max f hf hg)).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma locHom [IsLocalRing (AdjoinRoot f)] : IsLocalHom (algebraMap V (AdjoinRoot f)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr h)
  have h2 : algebraMap V (AdjoinRoot f) a ∈ maximalIdeal (AdjoinRoot f) := by
    rw [maxEq f hf hg]
    exact Ideal.mem_map_of_mem _ hm
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h2) ha

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
lemma dvr [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)] :
    IsDiscreteValuationRing (AdjoinRoot f) := by
  haveI := finite f hf
  haveI : IsNoetherianRing (AdjoinRoot f) := isNoetherian_of_tower V inferInstance
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmV : maximalIdeal V = Ideal.span {w} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer w).mp hw
  have hmA : maximalIdeal (AdjoinRoot f) = Ideal.span {algebraMap V (AdjoinRoot f) w} := by
    rw [maxEq f hf hg, hmV, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap V (AdjoinRoot f) w ≠ 0 := by
    rw [← map_zero (algebraMap V (AdjoinRoot f))]
    exact fun h => hw.ne_zero (inj f hf hg h)
  have hnf : ¬IsField (AdjoinRoot f) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : (maximalIdeal (AdjoinRoot f)).IsPrincipal := ⟨⟨_, hmA⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 0 4).mpr hpr

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma complete [IsLocalRing (AdjoinRoot f)] [IsAdicComplete (maximalIdeal V) V] :
    IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
  let b := (AdjoinRoot.powerBasis' hf).basis
  have key : ∀ (n : ℕ) (x : AdjoinRoot f),
      x ∈ (maximalIdeal (AdjoinRoot f) ^ n • ⊤ : Submodule (AdjoinRoot f) (AdjoinRoot f)) ↔
        x ∈ ((maximalIdeal V) ^ n • ⊤ : Submodule V (AdjoinRoot f)) := by
    intro n x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, maxEq f hf hg, ← Ideal.map_pow, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem]
  have hP : IsPrecomplete (maximalIdeal V) (AdjoinRoot f) := isPrecomplete_of_basis _ b
  have hH : IsHausdorff (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
    refine ⟨fun x hx => ?_⟩
    have h1 : ∀ n, x ∈ ((maximalIdeal V) ^ n • ⊤ : Submodule V (AdjoinRoot f)) := fun n =>
      (key n x).mp (by simpa using SModEq.sub_mem.mp (hx n))
    have h2 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := maximalIdeal V) (b.repr x i) fun n => by
        rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
        exact coord_mem_of_mem b _ (h1 n) i
    rw [← b.sum_repr x]
    simp [h2]
  have hC : IsPrecomplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
    refine ⟨fun g hg' => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' g fun {a c} hac => by
      rw [SModEq.sub_mem, ← key]
      exact SModEq.sub_mem.mp (hg' hac)
    exact ⟨L, fun n => by
      rw [SModEq.sub_mem, key]
      exact SModEq.sub_mem.mp (hL n)⟩
  exact IsAdicComplete.mk

noncomputable def resEquiv [IsLocalRing (AdjoinRoot f)] :
    ResidueField (AdjoinRoot f) ≃+* AdjoinRoot (f.map (residue V)) :=
  (Ideal.quotEquivOfEq (maxEq f hf hg)).trans
    (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
lemma resEquiv_comp [IsLocalRing (AdjoinRoot f)] :
    have := locHom f hf hg
    (resEquiv f hf hg).toRingHom.comp (ResidueField.map (algebraMap V (AdjoinRoot f))) =
      AdjoinRoot.of (f.map (residue V)) := by
  intro hl
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := residue_surjective x
  refine (AdjoinRoot.quotEquivQuotMap_apply_mk f (C y) (maximalIdeal V)).trans ?_
  rw [Polynomial.map_C]
  rfl

end Step
section Main

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Extract witnesses or component facts from the available result. Equip the data with the indicated structure.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem nbMain (n : ℕ) : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [IsAdicComplete (maximalIdeal V') V']
    (k'' : Type) [Field k''] [Algebra (ResidueField V') k'']
    [FiniteDimensional (ResidueField V') k''], Module.finrank (ResidueField V') k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V' V''),
      Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧
      ∃ (_ : IsLocalHom (algebraMap V' V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V') k'') =
          ResidueField.map (algebraMap V' V'') := by
  refine Nat.strong_induction_on n fun n ih => ?_
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · let e0 : ResidueField V' ≃+* k'' := RingEquiv.ofBijective (algebraMap (ResidueField V') k'')
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', fun x y h => h, ⟨fun x hx => hx⟩, e0.symm, ?_⟩
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := residue_surjective x
    rw [RingHom.comp_apply, ResidueField.map_residue]
    exact e0.symm_apply_apply (residue V' y)
  · obtain ⟨a, ha⟩ : ∃ a : k'', a ∉ (algebraMap (ResidueField V') k'').range := by
      by_contra h
      push_neg at h
      exact hs fun x => RingHom.mem_range.mp (h x)
    have hint : IsIntegral (ResidueField V') a := Algebra.IsIntegral.isIntegral a
    obtain ⟨f, hfg, -, hf⟩ := exists_monic_lift (minpoly (ResidueField V') a) (minpoly.monic hint)
    have hg : Irreducible (f.map (residue V')) := by
      rw [hfg]
      exact minpoly.irreducible hint
    haveI := isLocal f hf hg
    haveI := isDomain f hf hg
    haveI := locHom f hf hg
    haveI := dvr f hf hg
    haveI := complete f hf hg
    haveI := finite f hf
    have hroot : (f.map (residue V')).eval₂ (algebraMap (ResidueField V') k'') a = 0 := by
      rw [hfg, ← aeval_def]
      exact minpoly.aeval _ a
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' := RingHom.toAlgebra
      ((AdjoinRoot.lift (f := f.map (residue V')) (algebraMap (ResidueField V') k'') a hroot).comp
        (resEquiv f hf hg).toRingHom)
    have htow_eq : algebraMap (ResidueField V') k'' =
        (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
          (algebraMap (ResidueField V') (ResidueField (AdjoinRoot f))) := by
      refine RingHom.ext fun x => ?_
      have hc : (resEquiv f hf hg) (ResidueField.map (algebraMap V' (AdjoinRoot f)) x) =
          AdjoinRoot.of (f.map (residue V')) x := RingHom.congr_fun (resEquiv_comp f hf hg) x
      change _ = AdjoinRoot.lift (f := f.map (residue V')) (algebraMap (ResidueField V') k'') a hroot
        ((resEquiv f hf hg) (ResidueField.map (algebraMap V' (AdjoinRoot f)) x))
      rw [hc, AdjoinRoot.lift_of]
    haveI : IsScalarTower (ResidueField V') (ResidueField (AdjoinRoot f)) k'' :=
      IsScalarTower.of_algebraMap_eq' htow_eq
    haveI : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') (ResidueField (AdjoinRoot f)) k''
    have hdim : 2 ≤ Module.finrank (ResidueField V') (ResidueField (AdjoinRoot f)) := by
      let E : ResidueField (AdjoinRoot f) ≃ₐ[ResidueField V'] AdjoinRoot (f.map (residue V')) :=
        AlgEquiv.ofRingEquiv (f := resEquiv f hf hg) fun x => RingHom.congr_fun (resEquiv_comp f hf hg) x
      rw [E.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hg.ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hfg]
      have h1 : (minpoly (ResidueField V') a).natDegree ≠ 1 := fun h =>
        ha (minpoly.natDegree_eq_one_iff.mp h)
      have h2 := minpoly.natDegree_pos hint
      omega
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      have h1 := Module.finrank_mul_finrank (ResidueField V') (ResidueField (AdjoinRoot f)) k''
      have h2 : 0 < Module.finrank (ResidueField (AdjoinRoot f)) k'' := Module.finrank_pos
      rw [hn] at h1
      nlinarith
    obtain ⟨V2, i1, i2, i3, i4, i5, hfin, hinj, hloc, e, he⟩ := ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V2 :=
      ((algebraMap (AdjoinRoot f) V2).comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    haveI : IsScalarTower V' (AdjoinRoot f) V2 := IsScalarTower.of_algebraMap_eq' rfl
    haveI hl2 : IsLocalHom (algebraMap V' V2) := by
      show IsLocalHom ((algebraMap (AdjoinRoot f) V2).comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V2, i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V2,
      hinj.comp (inj f hf hg), hl2, e, ?_⟩
    rw [htow_eq, ← RingHom.comp_assoc, he]
    first
    | exact (ResidueField.map_comp (algebraMap V' (AdjoinRoot f)) (algebraMap (AdjoinRoot f) V2)).symm
    | exact (ResidueField.map_comp (algebraMap (AdjoinRoot f) V2) (algebraMap V' (AdjoinRoot f))).symm

end Main

end Nb

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem nb : NbSt := by
  unfold NbSt
  intro V' _ _ _ _ k'' _ _ _
  exact Nb.nbMain _ V' k'' rfl

end ReciprocityTheory.ChartRestriction.G.Semi
