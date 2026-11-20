import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.FiniteExtension

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

abbrev ramificationIndex : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).ramificationIdx 𝒪[K]

abbrev residueDegree : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg 𝒪[K]

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

instance t2Space : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

variable [FiniteDimensional K L]

/- English proof (translation)
Set `` to `normedField K`. Use `normedField_completeSpace K` as an intermediate fact. Set `b` to `Module.finBasis K L`. Set `e` to `b.equivFun.toContinuousLinearEquiv`. Establish `hc : IsCompact (e '' {x : L | valuation L x ≤ 1})` using `(IsNonarchimedeanLocalField.isCompact_closedBall L 1).image e.continuous`.

Take `⟨r, hr⟩` from `(Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded`. Take `⟨a, ha⟩` from `NormedField.exists_lt_norm K (max r 1)`. Establish `ha0 : 0 < ‖a‖` using `lt_of_lt_of_le zero_lt_one (le_max_right r 1) |>.trans ha`. Use `⟨a, norm_pos_iff.1 ha0, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖e x‖ ≤ r` using `by simpa using hr ⟨x, hx, rfl⟩`.

Establish `h2 : ‖b.repr x i‖ ≤ r` using `(norm_le_pi_norm (e x) i).trans h1`. Establish `h3 : ‖b.repr x i / a‖ ≤ ‖(1 : K)‖`. Rewrite using `[norm_div, norm_one, div_le_one ha0]`. Conclude with `h2.trans ((le_max_left r 1).trans ha.le)`. Use `(normedField_norm_le_norm_iff K _ _).1 h3` as an intermediate fact.

Rewrite `this` using `[(valuation K).vle_iff_le, map_one]`. Then use the resulting hypothesis.
-/
theorem exists_basis_coord_bound : ∃ a : K, a ≠ 0 ∧ ∀ x : L, valuation L x ≤ 1 →
    ∀ i, valuation K ((Module.finBasis K L).repr x i / a) ≤ 1 := by
  let := normedField K
  have := normedField_completeSpace K
  let b := Module.finBasis K L
  let e := b.equivFun.toContinuousLinearEquiv
  have hc : IsCompact (e '' {x : L | valuation L x ≤ 1}) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall L 1).image e.continuous
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm K (max r 1)
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le zero_lt_one (le_max_right r 1) |>.trans ha
  refine ⟨a, norm_pos_iff.1 ha0, fun x hx i => ?_⟩
  have h1 : ‖e x‖ ≤ r := by simpa using hr ⟨x, hx, rfl⟩
  have h2 : ‖b.repr x i‖ ≤ r := (norm_le_pi_norm (e x) i).trans h1
  have h3 : ‖b.repr x i / a‖ ≤ ‖(1 : K)‖ := by
    rw [norm_div, norm_one, div_le_one ha0]
    exact h2.trans ((le_max_left r 1).trans ha.le)
  have := (normedField_norm_le_norm_iff K _ _).1 h3
  rwa [(valuation K).vle_iff_le, map_one] at this

/- English proof (translation)
Take `⟨a, ha, hb⟩` from `exists_basis_coord_bound K L`. Set `b` to `Module.finBasis K L`. Set `N : Submodule 𝒪[K] L` to `Submodule.span 𝒪[K] (Set.range fun i => a • b i)`. Establish `hN : N.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `: IsNoetherian 𝒪[K] N` using `isNoetherian_of_fg_of_noetherian N hN`.

Establish `hmem : ∀ x : 𝒪[L], (x : L) ∈ N`. Introduce `x`. Establish `hx : valuation L (x : L) ≤ 1` using `x.2`. Rewrite using `[← b.sum_repr (x : L)]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `hc` using `hb x hx i`. Establish `: b.repr x i • b i = (⟨b.repr x i / a, hc⟩ : 𝒪[K]) • (a • b i)`. Rewrite using `[← algebraMap_smul K (⟨_, hc⟩ : 𝒪[K]) (a • b i), smul_smul]`. Use `congr 1`. Conclude with `(div_mul_cancel₀ _ ha).symm`.

Rewrite using `[this]`. Conclude with `N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `f : 𝒪[L] →ₗ[𝒪[K]] N` to `LinearMap.codRestrict N ((IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap) fun x => hmem x`. Use `Module.Finite.of_injective f fun x y h => ?_` and prove the remaining obligations. Establish `h'` using `congrArg Subtype.val h`.

Conclude with `Subtype.ext h'`.
-/
theorem finite_integer : Module.Finite 𝒪[K] 𝒪[L] := by
  obtain ⟨a, ha, hb⟩ := exists_basis_coord_bound K L
  let b := Module.finBasis K L
  let N : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range fun i => a • b i)
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have : IsNoetherian 𝒪[K] N := isNoetherian_of_fg_of_noetherian N hN
  have hmem : ∀ x : 𝒪[L], (x : L) ∈ N := by
    intro x
    have hx : valuation L (x : L) ≤ 1 := x.2
    rw [← b.sum_repr (x : L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc := hb x hx i
    have : b.repr x i • b i = (⟨b.repr x i / a, hc⟩ : 𝒪[K]) • (a • b i) := by
      rw [← algebraMap_smul K (⟨_, hc⟩ : 𝒪[K]) (a • b i), smul_smul]
      congr 1
      exact (div_mul_cancel₀ _ ha).symm
    rw [this]
    exact N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : 𝒪[L] →ₗ[𝒪[K]] N :=
    LinearMap.codRestrict N ((IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap) fun x => hmem x
  refine Module.Finite.of_injective f fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

instance : Module.Finite 𝒪[K] 𝒪[L] := finite_integer K L

/- English proof (translation)
The claim follows from `Module.free_of_finite_type_torsion_free'`.
-/
theorem free_integer : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'

instance : Module.Free 𝒪[K] 𝒪[L] := free_integer K L

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in

/- English proof (translation)
The claim follows from `(IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L).symm`.
-/
theorem finrank_integer : Module.finrank 𝒪[K] 𝒪[L] = Module.finrank K L :=
  (IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h2 : IsIntegral 𝒪[L] x` using `hx.tower_top`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Conclude with `y.2`.

Introduce `hx`. Establish `: IsIntegral 𝒪[K] (⟨x, hx⟩ : 𝒪[L])` using `Algebra.IsIntegral.isIntegral _`. Conclude with `this.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L)`.
-/
theorem isIntegral_iff (x : L) : IsIntegral 𝒪[K] x ↔ valuation L x ≤ 1 := by
  constructor
  · intro hx
    have h2 : IsIntegral 𝒪[L] x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact y.2
  · intro hx
    have : IsIntegral 𝒪[K] (⟨x, hx⟩ : 𝒪[L]) := Algebra.IsIntegral.isIntegral _
    exact this.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L)

instance isIntegralClosure : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isDiscreteValuationRing : IsDiscreteValuationRing 𝒪[L] := inferInstance

/- English proof (translation)
Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hl⟩`. Establish `: P.IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal P (IsLocalRing.maximalIdeal 𝒪[K])`. Conclude with `IsLocalRing.eq_maximalIdeal this`.

Introduce and unpack `rfl`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem primesOver_eq : (IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L] =
    {IsLocalRing.maximalIdeal 𝒪[L]} := by
  ext P
  constructor
  · rintro ⟨hP, hl⟩
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (IsLocalRing.maximalIdeal 𝒪[K])
    exact IsLocalRing.eq_maximalIdeal this
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

instance uniquePrimesOver : Unique ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) where
  default := ⟨IsLocalRing.maximalIdeal 𝒪[L], inferInstance, inferInstance⟩
  uniq P := Subtype.ext (Set.mem_singleton_iff.1 ((Set.ext_iff.1 (primesOver_eq K L) P.1).1 P.2))

/- English proof (translation)
Set `: Fintype ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L])` to `Fintype.ofFinite _`. Use `Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[L]` as an intermediate fact. Rewrite `this` using `[Fintype.sum_unique, finrank_integer]`. Conclude with `this`.
-/
theorem ramificationIndex_mul_residueDegree :
    ramificationIndex K L * residueDegree K L = Module.finrank K L := by
  let : Fintype ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) := Fintype.ofFinite _
  have := Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[L]
  rw [Fintype.sum_unique, finrank_integer] at this
  exact this

/- English proof (translation)
The claim follows from `IsDiscreteValuationRing.not_a_field _`.
-/
theorem maximalIdeal_ne_bot : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field _

/- English proof (translation)
Establish `hne : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot (maximalIdeal_ne_bot K)`. Take `⟨n, hn⟩` from `exists_maximalIdeal_pow_eq_of_principal 𝒪[L] (IsPrincipalIdealRing.principal _) _ hne`. Establish `hL : IsLocalRing.maximalIdeal 𝒪[L] ≠ ⊥` using `IsDiscreteValuationRing.not_a_field _`. Establish `h : (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx' (IsLocalRing.maximalIdeal 𝒪[L]) = n` using `Ideal.ramificationIdx'_spec hn.le (by`. Rewrite using `[hn]`.

Conclude with `not_le_of_gt (Ideal.pow_succ_lt_pow hL n))`. Rewrite using `[ramificationIndex, ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot K), h, hn]`.
-/
theorem map_maximalIdeal :
    (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) =
      IsLocalRing.maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
  have hne : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (maximalIdeal_ne_bot K)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ hne
  have hL : IsLocalRing.maximalIdeal 𝒪[L] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have h : (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx' (IsLocalRing.maximalIdeal 𝒪[L]) = n :=
    Ideal.ramificationIdx'_spec hn.le (by
      rw [hn]
      exact not_le_of_gt (Ideal.pow_succ_lt_pow hL n))
  rw [ramificationIndex, ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot K), h,
    hn]

/- English proof (translation)
The claim follows from `Ideal.ramificationIdx_pos _ _`.
-/
theorem ramificationIndex_pos : 0 < ramificationIndex K L := Ideal.ramificationIdx_pos _ _

/- English proof (translation)
The claim follows from `Ideal.inertiaDeg_pos _ _`.
-/
theorem residueDegree_pos : 0 < residueDegree K L := Ideal.inertiaDeg_pos _ _

/- English proof (translation)
The claim follows from `Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L])`.
-/
theorem residueDegree_eq_finrank : residueDegree K L = Module.finrank 𝓀[K] 𝓀[L] :=
  Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L])

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Field M] [ValuativeRel M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply K L M, IsScalarTower.algebraMap_apply K L M, ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]`.
-/
theorem valuativeExtension_trans [ValuativeExtension K L] [ValuativeExtension L M] :
    ValuativeExtension K M where
  vle_iff_vle a b := by
    rw [IsScalarTower.algebraMap_apply K L M, IsScalarTower.algebraMap_apply K L M,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]

variable [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]

instance isScalarTower_integer : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
  IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K L M (x : K))

/- English proof (translation)
The claim follows from `Ideal.inertiaDeg_tower _ _`.
-/
theorem residueDegree_tower :
    residueDegree K M = residueDegree K L * residueDegree L M :=
  Ideal.inertiaDeg_tower _ _

/- English proof (translation)
The claim follows from `Ideal.ramificationIdx_tower _ _`.
-/
theorem ramificationIndex_tower [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [FiniteDimensional L M] :
    ramificationIndex K M = ramificationIndex K L * ramificationIndex L M :=
  Ideal.ramificationIdx_tower _ _

end Tower

end GroundTheory.LocalField
