import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBase

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.LatIndexDet

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ`. Establish `h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation ϖ = WithZero.exp (-1 : ℤ)` using `(IsDiscreteValuationRing.maximalIdeal O).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq`. Establish `h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1`. Use `le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).intValuation_le_one _) (not_lt.1 fun h => ?_)` and prove the remaining obligations.

Use `((IsDiscreteValuationRing.maximalIdeal O).intValuation_lt_one_iff_mem _).1 h` as an intermediate fact. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this u.isUnit`. Rewrite using `[IsDiscreteValuationRing.addVal_def' u hϖ n]`. Simplify using `only [val, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2, one_mul, ← WithZero.exp_nsmul, WithZero.log_exp, ENat.toNat_coe]`. Simplify using the standard rewrite rules.
-/
theorem val_algebraMap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] {d : O} (hd : d ≠ 0) :
    val O (algebraMap O E d) = ((IsDiscreteValuationRing.addVal O d).toNat : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    (IsDiscreteValuationRing.maximalIdeal O).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 := by
    refine le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).intValuation_le_one _) (not_lt.1 fun h => ?_)
    have := ((IsDiscreteValuationRing.maximalIdeal O).intValuation_lt_one_iff_mem _).1 h
    exact (IsLocalRing.mem_maximalIdeal _).1 this u.isUnit
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  simp only [val, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2,
    one_mul, ← WithZero.exp_nsmul, WithZero.log_exp, ENat.toNat_coe]
  simp

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

variable (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

include E in

/- English proof (translation)
Use `Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `Or.inr (Subtype.ext ?_)` and prove the remaining obligations. Establish `h' : r • (x : V) = 0` using `congrArg Subtype.val h`.

Rewrite `h'` using `[← algebraMap_smul E r (x : V)]`. Establish `hr' : algebraMap O E r ≠ 0` using `fun h0 => hr (IsFractionRing.injective O E (by rw [h0, map_zero]))`. Conclude with `(smul_eq_zero.1 h').resolve_left hr'`.
-/
theorem isTorsionFree_lat (N : Submodule O V) : Module.IsTorsionFree O N := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr (Subtype.ext ?_)
    have h' : r • (x : V) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul E r (x : V)] at h'
    have hr' : algebraMap O E r ≠ 0 := fun h0 => hr (IsFractionRing.injective O E (by rw [h0, map_zero]))
    exact (smul_eq_zero.1 h').resolve_left hr'

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O N`. Set `bV : Module.Free.ChooseBasisIndex O N → V` to `fun i => (b i : V)`. Establish `hliO : LinearIndependent O bV` using `b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)`. Establish `hli : LinearIndependent E bV` using `(LinearIndependent.iff_fractionRing O E).1 hliO`. Establish `hNle : (N : Set V) ⊆ Submodule.span E (Set.range bV)`.

Introduce `x hx`. Establish `hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • bV i`. Establish `h0` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`. Rewrite `h0` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h0`.

Conclude with `h0.symm`. Rewrite using `[hx'']`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul E]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hsp : ⊤ ≤ Submodule.span E (Set.range bV)`. Rewrite using `[← hspan]`. Conclude with `Submodule.span_le.2 hNle`. Set `BE` to `Module.Basis.mk hli hsp`. Set `T'` to `(T.restrictScalars O).restrict hT`.

Establish `hmat : LinearMap.toMatrix BE BE T = (LinearMap.toMatrix b b T').map (algebraMap O E)`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]`. Establish `h1 : T (BE j) = ∑ k, algebraMap O E (b.repr (T' (b j)) k) • BE k`. Establish `h2 : T' (b j) = ∑ k, b.repr (T' (b j)) k • b k` using `(b.sum_repr _).symm`.

Establish `h3` using `congrArg Subtype.val h2`. Simplify using `only [Module.Basis.mk_apply, BE, bV]`. Rewrite using `[show T (b j : V) = ((T' (b j) : N) : V) from rfl]`. Use `conv_lhs => rw [h3]`. Rewrite using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul, algebraMap_smul]`. Rewrite using `[h1, BE.repr_sum_self]`. Rewrite using `[← LinearMap.det_toMatrix BE, hmat, ← LinearMap.det_toMatrix b T', RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem algebraMap_det_restrict (N : Submodule O V) [Module.Free O N] [Module.Finite O N]
    (hspan : Submodule.span E (N : Set V) = ⊤) (T : V →ₗ[E] V) (hT : ∀ x ∈ N, T x ∈ N) :
    algebraMap O E (LinearMap.det ((T.restrictScalars O).restrict hT)) = LinearMap.det T := by
  classical
  let b := Module.Free.chooseBasis O N
  let bV : Module.Free.ChooseBasisIndex O N → V := fun i => (b i : V)
  have hliO : LinearIndependent O bV :=
    b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hli : LinearIndependent E bV := (LinearIndependent.iff_fractionRing O E).1 hliO
  have hNle : (N : Set V) ⊆ Submodule.span E (Set.range bV) := by
    intro x hx
    have hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • bV i := by
      have h0 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    rw [hx'']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul E]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span E (Set.range bV) := by
    rw [← hspan]; exact Submodule.span_le.2 hNle
  let BE := Module.Basis.mk hli hsp
  let T' := (T.restrictScalars O).restrict hT
  have hmat : LinearMap.toMatrix BE BE T = (LinearMap.toMatrix b b T').map (algebraMap O E) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : T (BE j) = ∑ k, algebraMap O E (b.repr (T' (b j)) k) • BE k := by
      have h2 : T' (b j) = ∑ k, b.repr (T' (b j)) k • b k := (b.sum_repr _).symm
      have h3 := congrArg Subtype.val h2
      simp only [Module.Basis.mk_apply, BE, bV]
      rw [show T (b j : V) = ((T' (b j) : N) : V) from rfl]
      conv_lhs => rw [h3]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, algebraMap_smul]
    rw [h1, BE.repr_sum_self]
  rw [← LinearMap.det_toMatrix BE, hmat, ← LinearMap.det_toMatrix b T', RingHom.map_det]
  rfl

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

/- English proof (translation)
Introduce `O _ _ _ _ E _ _ _ V _ _ _ _ _ N hfg hspan T hdet hT`. Use `haveI := isTorsionFree_lat O E N`. Use `haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Free O N := Module.free_of_finite_type_torsion_free'`. Set `T' : N →ₗ[O] N` to `(T.restrictScalars O).restrict hT`.

Establish `hdetT : algebraMap O E (LinearMap.det T') = LinearMap.det T` using `algebraMap_det_restrict O E N hspan T hT`. Establish `hdet' : LinearMap.det T' ≠ 0` using `fun h => hdet (by rw [← hdetT, h, map_zero])`. Establish `hrange : (N.map (T.restrictScalars O)).comap N.subtype = LinearMap.range T'`. Use extensionality with `⟨x, hx⟩`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `⟨⟨y, hy⟩, Subtype.ext hyx⟩`. Introduce and unpack `⟨⟨y, hy⟩, hyx⟩`. Conclude with `⟨y, hy, congrArg Subtype.val hyx⟩`.

Rewrite using `[hrange, GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det T' hdet', ← hdetT, val_algebraMap O E hdet']`. Use `push_cast`. Rewrite using `[zpow_natCast]`.
-/
theorem card_quot_eq_pow_val : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (V : Type) [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [FiniteDimensional E V] (N : Submodule O V), N.FG → Submodule.span E (N : Set V) = ⊤ → ∀ T : V →ₗ[E] V, LinearMap.det T ≠ 0 → (∀ x ∈ N, T x ∈ N) → (Nat.card (↥N ⧸ (N.map (T.restrictScalars O)).comap N.subtype) : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (LinearMap.det T) := by
  intro O _ _ _ _ E _ _ _ V _ _ _ _ _ N hfg hspan T hdet hT
  haveI := isTorsionFree_lat O E N
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O N := Module.free_of_finite_type_torsion_free'
  let T' : N →ₗ[O] N := (T.restrictScalars O).restrict hT
  have hdetT : algebraMap O E (LinearMap.det T') = LinearMap.det T := algebraMap_det_restrict O E N hspan T hT
  have hdet' : LinearMap.det T' ≠ 0 := fun h => hdet (by rw [← hdetT, h, map_zero])
  have hrange : (N.map (T.restrictScalars O)).comap N.subtype = LinearMap.range T' := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨⟨y, hy⟩, hyx⟩
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  rw [hrange, GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det T' hdet', ← hdetT, val_algebraMap O E hdet']
  push_cast
  rw [zpow_natCast]

end GlobalTheory.LatIndexDet
