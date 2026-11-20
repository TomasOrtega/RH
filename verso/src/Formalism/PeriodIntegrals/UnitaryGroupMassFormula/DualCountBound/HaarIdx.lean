import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.IsOpenLocO

noncomputable section

open scoped Classical
open ValuativeRel MeasureTheory

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

/- English proof (translation)
Distinguish the cases in `h0 : H.relIndex K = 0`. Simplify using `[h0]`. Establish `hfin : Finite (K ⧸ H.addSubgroupOf K)` using `Nat.finite_of_card_ne_zero h0`. Use `letI := Fintype.ofFinite (K ⧸ H.addSubgroupOf K)`. Set `f : (K ⧸ H.addSubgroupOf K) → G` to `fun c => ((Quotient.out c : K) : G)`.

Set `A : (K ⧸ H.addSubgroupOf K) → Set G` to `fun c => (fun x => -f c + x) ⁻¹' (H : Set G)`. Establish `hmeas : ∀ c, MeasurableSet (A c)` using `fun c => measurable_const_add (-f c) hH`. Establish `hμ : ∀ c, μ (A c) = μ (H : Set G)` using `fun c => measure_preimage_add μ (-f c) _`. Establish `hdisj : Pairwise (Function.onFun Disjoint A)`. Introduce `c c' hcc'`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hx hx'`. Apply `hcc'` to reduce the goal to its premises. Establish `hx1 : -f c + x ∈ H` using `hx`. Establish `hx2 : -f c' + x ∈ H` using `hx'`.

Establish `h1 : -f c + f c' ∈ H`. Use `H.add_mem hx1 (H.neg_mem hx2)` as an intermediate fact. Simplify `this` using `[neg_add_rev, add_assoc]`. Rewrite using `[← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify `h1` using `[f]`.

Establish `hsub : (⋃ c, A c) ⊆ (K : Set G)`. Use `Set.iUnion_subset fun c x hx => ?_` and prove the remaining obligations. Establish `hx1 : -f c + x ∈ H` using `hx`. Establish `: f c + (-f c + x) ∈ K` using `K.add_mem (Quotient.out c).2 (hHK hx1)`. Simplify using `using this`.

Establish `hcard : H.relIndex K = Fintype.card (K ⧸ H.addSubgroupOf K)`. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcard]`. Simplify using `[hμ, Finset.sum_const, Finset.card_univ, mul_comm]`.

Use `_ = μ (⋃ c, A c) := by rw [measure_iUnion hdisj hmeas, tsum_fintype]`. Use `_ ≤ μ (K : Set G) := measure_mono hsub`.
-/
theorem measure_mul_relIndex_le {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {H K : AddSubgroup G} (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) :
    μ (H : Set G) * (H.relIndex K : ENNReal) ≤ μ (K : Set G) := by
  by_cases h0 : H.relIndex K = 0
  · simp [h0]
  have hfin : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero h0
  letI := Fintype.ofFinite (K ⧸ H.addSubgroupOf K)
  let f : (K ⧸ H.addSubgroupOf K) → G := fun c => ((Quotient.out c : K) : G)
  let A : (K ⧸ H.addSubgroupOf K) → Set G := fun c => (fun x => -f c + x) ⁻¹' (H : Set G)
  have hmeas : ∀ c, MeasurableSet (A c) := fun c => measurable_const_add (-f c) hH
  have hμ : ∀ c, μ (A c) = μ (H : Set G) := fun c => measure_preimage_add μ (-f c) _
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro c c' hcc'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hcc'
    have hx1 : -f c + x ∈ H := hx
    have hx2 : -f c' + x ∈ H := hx'
    have h1 : -f c + f c' ∈ H := by
      have := H.add_mem hx1 (H.neg_mem hx2)
      simpa [neg_add_rev, add_assoc] using this
    rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [f] using h1
  have hsub : (⋃ c, A c) ⊆ (K : Set G) := by
    refine Set.iUnion_subset fun c x hx => ?_
    have hx1 : -f c + x ∈ H := hx
    have : f c + (-f c + x) ∈ K := K.add_mem (Quotient.out c).2 (hHK hx1)
    simpa using this
  have hcard : H.relIndex K = Fintype.card (K ⧸ H.addSubgroupOf K) := by
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  calc μ (H : Set G) * (H.relIndex K : ENNReal)
      = ∑ c, μ (A c) := by
        rw [hcard]; simp [hμ, Finset.sum_const, Finset.card_univ, mul_comm]
    _ = μ (⋃ c, A c) := by rw [measure_iUnion hdisj hmeas, tsum_fintype]
    _ ≤ μ (K : Set G) := measure_mono hsub

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Unfold `Model.R`. Rewrite using `[h]`.
-/
theorem R_eq_O_of_none {M : Model F E} (h : M.split = none) : M.R = M.L.O := by
  unfold Model.R
  rw [h]

/- English proof (translation)
Unfold `Model.R`. Rewrite using `[h]`. Rewrite using `[Subring.mem_comap, Subring.mem_map]`. Use `⟨(g.q * a, g.q * b), ?_, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * a) = Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * b)`.

Rewrite using `[Ideal.Quotient.eq]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨a - b, by ring⟩`. Use `show ((((g.q * a : 𝒪[F]) : F)), ((g.q * b : 𝒪[F]) : F)) = g.e y`. Rewrite using `[hy]`. Simplify using the standard rewrite rules.
-/
theorem memR_of_split {M : Model F E} {g : SplitG M.L} (h : M.split = some g) (y : E) (a b : 𝒪[F])
    (hy : g.e y = ((g.q : F) * a, (g.q : F) * b)) : y ∈ M.R := by
  unfold Model.R
  rw [h]
  rw [Subring.mem_comap, Subring.mem_map]
  refine ⟨(g.q * a, g.q * b), ?_, ?_⟩
  · show Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * a) = Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * b)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨a - b, by ring⟩
  · show ((((g.q * a : 𝒪[F]) : F)), ((g.q * b : 𝒪[F]) : F)) = g.e y
    rw [hy]
    simp

/- English proof (translation)
Unfold `Model.R at hx`. Rewrite `hx` using `[h]`. Rewrite `hx` using `[Subring.mem_comap, Subring.mem_map]`. Take `⟨⟨a, b⟩, -, hxe⟩` from `hx`. Rewrite using `[M.L.O_def]`.

Use `⟨(Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b), (Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b), ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C]`. Apply `g.e.injective` to reduce the goal to its premises. Establish `hxe' : g.e x = ((a : F), (b : F))` using `hxe.symm`. Establish `e1 : g.e (x - algebraMap F E (algebraMap 𝒪[F] F a)) = (0, (b : F) - a)`.

Rewrite using `[map_sub, AlgEquiv.commutes, hxe']`. Conclude with `Prod.ext (sub_self _) rfl`. Establish `e2 : g.e (x - algebraMap F E (algebraMap 𝒪[F] F b)) = ((a : F) - b, 0)`. Rewrite using `[map_sub, AlgEquiv.commutes, hxe']`. Conclude with `Prod.ext rfl (sub_self _)`.

Rewrite using `[map_zero, map_mul, IsScalarTower.algebraMap_apply 𝒪[F] F E, IsScalarTower.algebraMap_apply 𝒪[F] F E, e1, e2]`. Conclude with `Prod.ext (zero_mul _) (mul_zero _)`.
-/
theorem memO_of_memR_split {M : Model F E} {g : SplitG M.L} (h : M.split = some g) {x : E}
    (hx : x ∈ M.R) : x ∈ M.L.O := by
  unfold Model.R at hx
  rw [h] at hx
  rw [Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨⟨a, b⟩, -, hxe⟩ := hx
  rw [M.L.O_def]
  refine ⟨(Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b),
    (Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b), ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_C]
  apply g.e.injective
  have hxe' : g.e x = ((a : F), (b : F)) := hxe.symm
  have e1 : g.e (x - algebraMap F E (algebraMap 𝒪[F] F a)) = (0, (b : F) - a) := by
    rw [map_sub, AlgEquiv.commutes, hxe']
    exact Prod.ext (sub_self _) rfl
  have e2 : g.e (x - algebraMap F E (algebraMap 𝒪[F] F b)) = ((a : F) - b, 0) := by
    rw [map_sub, AlgEquiv.commutes, hxe']
    exact Prod.ext rfl (sub_self _)
  rw [map_zero, map_mul, IsScalarTower.algebraMap_apply 𝒪[F] F E, IsScalarTower.algebraMap_apply 𝒪[F] F E, e1, e2]
  exact Prod.ext (zero_mul _) (mul_zero _)

/- English proof (translation)
Establish `hint` using `(M.L.O_def x).mp hx`. Establish `hfst` using `hint.map (((AlgHom.fst F F F).comp (g.e : E →ₐ[F] F × F)).restrictScalars 𝒪[F])`. Establish `hsnd` using `hint.map (((AlgHom.snd F F F).comp (g.e : E →ₐ[F] F × F)).restrictScalars 𝒪[F])`. Establish `hI` using `Valuation.integer.integers (ValuativeRel.valuation F)`. Prove the components needed by the constructor for the conclusion.

Establish `h1` using `hI.mem_of_integral hfst first`. Consider the case `exact h1`. Consider the case `simpa using h1`. Consider the case `(obtain ⟨y, hy⟩ := h1; rw [← hy]; exact y.2)`. Establish `h1` using `hI.mem_of_integral hsnd first`.

Consider the case `exact h1`. Consider the case `simpa using h1`. Consider the case `(obtain ⟨y, hy⟩ := h1; rw [← hy]; exact y.2)`.
-/
theorem coords_mem_of_memO {M : Model F E} (g : SplitG M.L) {x : E} (hx : x ∈ M.L.O) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] := by
  have hint := (M.L.O_def x).mp hx
  have hfst := hint.map (((AlgHom.fst F F F).comp (g.e : E →ₐ[F] F × F)).restrictScalars 𝒪[F])
  have hsnd := hint.map (((AlgHom.snd F F F).comp (g.e : E →ₐ[F] F × F)).restrictScalars 𝒪[F])
  have hI := Valuation.integer.integers (ValuativeRel.valuation F)
  constructor
  · have h1 := hI.mem_of_integral hfst
    first
      | exact h1
      | simpa using h1
      | (obtain ⟨y, hy⟩ := h1; rw [← hy]; exact y.2)
  · have h1 := hI.mem_of_integral hsnd
    first
      | exact h1
      | simpa using h1
      | (obtain ⟨y, hy⟩ := h1; rw [← hy]; exact y.2)

/- English proof (translation)
Take `⟨h1, h2⟩` from `coords_mem_of_memO g hx`. Apply `memR_of_split h _ ⟨(g.e x).1, h1⟩ ⟨(g.e x).2, h2⟩` to reduce the goal to its premises. Rewrite using `[map_mul, AlgEquiv.commutes]`. Use `ext`. Use `show (algebraMap F (F × F) (g.q : F) * g.e x).1 = (g.q : F) * (g.e x).1`.

Rewrite using `[Prod.fst_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Use `show (algebraMap F (F × F) (g.q : F) * g.e x).2 = (g.q : F) * (g.e x).2`. Rewrite using `[Prod.snd_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`.
-/
theorem qmul_memR {M : Model F E} {g : SplitG M.L} (h : M.split = some g) {x : E} (hx : x ∈ M.L.O) :
    algebraMap F E (g.q : F) * x ∈ M.R := by
  obtain ⟨h1, h2⟩ := coords_mem_of_memO g hx
  apply memR_of_split h _ ⟨(g.e x).1, h1⟩ ⟨(g.e x).2, h2⟩
  rw [map_mul, AlgEquiv.commutes]
  ext
  · show (algebraMap F (F × F) (g.q : F) * g.e x).1 = (g.q : F) * (g.e x).1
    rw [Prod.fst_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · show (algebraMap F (F × F) (g.q : F) * g.e x).2 = (g.q : F) * (g.e x).2
    rw [Prod.snd_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/- English proof (translation)
Use `haveI := M.L.top`. Use `haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E`. Establish `hq0 : (g.q : F) ≠ 0` using `fun h0 => g.q_irr.ne_zero (Subtype.ext h0)`. Establish `hce : Continuous (g.e : E → F × F)` using `IsModuleTopology.continuous_of_linearMap g.e.toLinearEquiv.toLinearMap`. Establish `ho : IsOpen ((𝒪[F] : Subring F) : Set F)` using `Valuation.isOpen_integer`.

Set `U : Set E` to `{x | (g.q : F)⁻¹ * (g.e x).1 ∈ 𝒪[F] ∧ (g.q : F)⁻¹ * (g.e x).2 ∈ 𝒪[F]}`. Establish `hUo : IsOpen U` using `(ho.preimage (continuous_const.mul (continuous_fst.comp hce))).inter (ho.preimage (continuous_const.mul (continuous_snd.comp hce)))`. Establish `hU0 : (0 : E) ∈ U` using `by simp [U]`. Establish `hUR : U ⊆ (M.R : Set E)`. Introduce and unpack `x ⟨h1, h2⟩`.

Use `memR_of_split h x ⟨_, h1⟩ ⟨_, h2⟩ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [mul_inv_cancel_left₀ hq0]`. Conclude with `AddSubgroup.isOpen_of_mem_nhds M.R.toAddSubgroup (Filter.mem_of_superset (hUo.mem_nhds hU0) hUR)`.
-/
theorem isOpen_R_split [IsNonarchimedeanLocalField F] {M : Model F E} {g : SplitG M.L}
    (h : M.split = some g) : IsOpen (M.R : Set E) := by
  haveI := M.L.top
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hce : Continuous (g.e : E → F × F) :=
    IsModuleTopology.continuous_of_linearMap g.e.toLinearEquiv.toLinearMap
  have ho : IsOpen ((𝒪[F] : Subring F) : Set F) := Valuation.isOpen_integer
  let U : Set E := {x | (g.q : F)⁻¹ * (g.e x).1 ∈ 𝒪[F] ∧ (g.q : F)⁻¹ * (g.e x).2 ∈ 𝒪[F]}
  have hUo : IsOpen U :=
    (ho.preimage (continuous_const.mul (continuous_fst.comp hce))).inter
      (ho.preimage (continuous_const.mul (continuous_snd.comp hce)))
  have hU0 : (0 : E) ∈ U := by simp [U]
  have hUR : U ⊆ (M.R : Set E) := by
    rintro x ⟨h1, h2⟩
    refine memR_of_split h x ⟨_, h1⟩ ⟨_, h2⟩ ?_
    ext <;> simp [mul_inv_cancel_left₀ hq0]
  exact AddSubgroup.isOpen_of_mem_nhds M.R.toAddSubgroup
    (Filter.mem_of_superset (hUo.mem_nhds hU0) hUR)

end Split

def LocOOpen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), IsOpen (L.O : Set E)

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK δ hδ`. Use `hOK.loc` as an intermediate fact. Use `hOK.borel` as an intermediate fact. Use `hOK.haar.haar` as an intermediate fact. Use `haveI := M.L.top`.

Use `haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E`. Use `set n := Nat.card (M.L.O ⧸ Ideal.span {toO M δ}) with hn`. Establish `hδF : (δ : F) ≠ 0` using `fun h0 => hδ (Subtype.ext h0)`. Use `set d : E := algebraMap F E (δ : F) with hd`. Use `set d' : E := algebraMap F E (δ : F)⁻¹ with hd'`.

Establish `hdd' : d * d' = 1` using `by rw [hd, hd', ← map_mul, mul_inv_cancel₀ hδF, map_one]`. Establish `hd'd : d' * d = 1` using `by rw [mul_comm, hdd']`. Establish `hdR : d ∈ M.R` using `lattice_membership_ring F E M hOK δ`. Establish `hdO : d ∈ M.L.O` using `(toO M δ).2`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Distinguish the cases in `hu : IsUnit δ`. Establish `hI : Ideal.span {toO M δ} = ⊤` using `Ideal.span_singleton_eq_top.2 (hu.map (toO M))`. Establish `h1 : n = 1`.

Rewrite using `[hn, hI]`. Conclude with `Nat.card_eq_one_iff_unique.2 ⟨Submodule.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩`. Rewrite using `[h1, Nat.cast_one, mul_one]`. Conclude with `lattice_index_modulus_le F E M hOK d hdR`. Set `Oa : AddSubgroup E` to `M.L.O.toAddSubgroup`.

Set `Ra : AddSubgroup E` to `M.R.toAddSubgroup`. Set `ψ : E →+ E` to `AddMonoidHom.mulLeft d`. Establish `hψ : Function.Injective ψ` using `fun x y hxy => by`. Establish `: d' * (d * x) = d' * (d * y)` using `congrArg (d' * ·) hxy`. Rewrite `this` using `[← mul_assoc, ← mul_assoc, hd'd, one_mul, one_mul]`. Then use the resulting hypothesis.

Establish `hRO : Ra ≤ Oa`. Introduce `x hx`. Consider the cases of `h : M.split with`. Consider the case `none`. Establish `hx' : x ∈ M.R` using `hx`.

Rewrite `hx'` using `[R_eq_O_of_none h]`. Conclude with `hx'`. Consider the case `some g => exact memO_of_memR_split h hx`. Establish `hRR : Ra.map ψ ≤ Ra`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `M.R.mul_mem hdR hy`. Establish `hOO : Oa.map ψ ≤ Oa`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `M.L.O.mul_mem hdO hy`. Establish `hRmO : Ra.map ψ ≤ Oa.map ψ` using `AddSubgroup.map_mono hRO`.

Establish `e1` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hRmO hOO`. Establish `e2` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hRR hRO`. Establish `e3` using `AddSubgroup.relIndex_map_map_of_injective Ra Oa hψ`. Set `ι : M.L.O →+ E` to `M.L.O.subtype.toAddMonoidHom`. Establish `hIeq : (Ideal.span {toO M δ}).toAddSubgroup = (Oa.map ψ).comap ι`.

Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap, AddSubgroup.mem_map]`. Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a, a.2, by simp [ψ, ι, d, mul_comm]⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ, ι, d, mul_comm] using hyx)⟩`. Establish `htop : (⊤ : AddSubgroup M.L.O).map ι = Oa`. Use extensionality with `x`.

Simplify using `[ι, Oa]`. Establish `hn' : n = (Oa.map ψ).relIndex Oa`. Establish `: n = ((Ideal.span {toO M δ}).toAddSubgroup).index` using `rfl`. Rewrite using `[this, hIeq, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, htop]`. Establish `ha : Ra.relIndex Oa ≠ 0`.

Consider the cases of `h : M.split with`. Consider the case `none`. Establish `: Ra = Oa`. Use extensionality with `x`. Use `show x ∈ M.R ↔ x ∈ M.L.O`.

Rewrite using `[R_eq_O_of_none h]`. Rewrite using `[this, AddSubgroup.relIndex_self]`. Conclude with `one_ne_zero`. Consider the case `some g`. Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer g.q).1 g.q_irr`.

Establish `hmem : δ ∈ IsLocalRing.maximalIdeal 𝒪[F]` using `(IsLocalRing.mem_maximalIdeal δ).2 (mem_nonunits_iff.2 hu)`. Rewrite `hmem` using `[hmax, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hmem`. Establish `hle : Oa.map ψ ≤ Ra`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Establish `: ψ y = algebraMap F E (g.q : F) * (algebraMap F E (c : F) * y)`. Simplify using `only [ψ, AddMonoidHom.coe_mulLeft, d, ← hc, MulMemClass.coe_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `qmul_memR h (M.L.O.mul_mem (toO M c).2 hy)`.

Establish `hdvd` using `AddSubgroup.relIndex_dvd_of_le_left Oa hle`. Rewrite `hdvd` using `[← hn']`. Introduce `h0`. Rewrite `hdvd` using `[h0, zero_dvd_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hm : (Ra.map ψ).relIndex Ra = n`. Establish `hpos' : 0 < Ra.relIndex Oa` using `Nat.pos_of_ne_zero ha`. Rewrite `e1` using `[e3]`. Rewrite using `[hn']`. Establish `: Ra.relIndex Oa * (Oa.map ψ).relIndex Oa = Ra.relIndex Oa * (Ra.map ψ).relIndex Ra`.

Rewrite using `[e1, ← e2, mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_left hpos' this).symm`. Establish `hset : ((Ra.map ψ : AddSubgroup E) : Set E) = (fun y => d' * y) ⁻¹' (M.R : Set E)`. Use extensionality with `x`. Simplify using `only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `: d' * ψ y = y` using `by simp [ψ, ← mul_assoc, hd'd]`. Rewrite using `[this]`. Conclude with `hy`.

Introduce `hx`. Conclude with `⟨d' * x, hx, by simp [ψ, ← mul_assoc, hdd']⟩`. Establish `hRopen : IsOpen (M.R : Set E)`. Consider the cases of `h : M.split with`. Consider the case `none => rw [R_eq_O_of_none h]`.

Conclude with `hO F E M.L`. Consider the case `some g => exact isOpen_R_split h`. Establish `hcont : Continuous (fun y : E => d' * y)`. Establish `: (fun y : E => d' * y) = fun y => ((δ : F)⁻¹) • y`. Use function extensionality and compare the values at `y`.

Rewrite using `[Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `continuous_const_smul _`. Establish `hmeasS : MeasurableSet ((Ra.map ψ : AddSubgroup E) : Set E)`. Rewrite using `[hset]`.

Conclude with `(hRopen.preimage hcont).measurableSet`. Establish `key` using `measure_mul_relIndex_le M.mu hRR hmeasS`. Rewrite `key` using `[hm]`. Establish `hvol : M.mu (Ra : Set E) = 1` using `hOK.haar.volR`. Rewrite `key` using `[hvol]`.

Establish `himg : (fun y => d * y) '' (M.R : Set E) = ((Ra.map ψ : AddSubgroup E) : Set E)`. Simplify using `[ψ, Ra]`. Unfold `Model.modK`. Rewrite using `[himg]`. Use `ENNReal.toReal_mono ENNReal.one_ne_top key` as an intermediate fact.

Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one]`. Then use the resulting hypothesis.
-/
theorem haarIdx_of_open (hO : LocOOpen) : HaarIdx := by
  intro F _ _ _ E _ _ _ _ M hOK δ hδ
  have := hOK.loc
  have := hOK.borel
  have := hOK.haar.haar
  haveI := M.L.top
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  set n := Nat.card (M.L.O ⧸ Ideal.span {toO M δ}) with hn
  have hδF : (δ : F) ≠ 0 := fun h0 => hδ (Subtype.ext h0)
  set d : E := algebraMap F E (δ : F) with hd
  set d' : E := algebraMap F E (δ : F)⁻¹ with hd'
  have hdd' : d * d' = 1 := by rw [hd, hd', ← map_mul, mul_inv_cancel₀ hδF, map_one]
  have hd'd : d' * d = 1 := by rw [mul_comm, hdd']
  have hdR : d ∈ M.R := lattice_membership_ring F E M hOK δ
  have hdO : d ∈ M.L.O := (toO M δ).2
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]; simp
  by_cases hu : IsUnit δ
  · have hI : Ideal.span {toO M δ} = ⊤ := Ideal.span_singleton_eq_top.2 (hu.map (toO M))
    have h1 : n = 1 := by
      rw [hn, hI]
      exact Nat.card_eq_one_iff_unique.2 ⟨Submodule.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩
    rw [h1, Nat.cast_one, mul_one]
    exact lattice_index_modulus_le F E M hOK d hdR
  let Oa : AddSubgroup E := M.L.O.toAddSubgroup
  let Ra : AddSubgroup E := M.R.toAddSubgroup
  let ψ : E →+ E := AddMonoidHom.mulLeft d
  have hψ : Function.Injective ψ := fun x y hxy => by
    have : d' * (d * x) = d' * (d * y) := congrArg (d' * ·) hxy
    rwa [← mul_assoc, ← mul_assoc, hd'd, one_mul, one_mul] at this
  have hRO : Ra ≤ Oa := by
    intro x hx
    cases h : M.split with
    | none =>
      have hx' : x ∈ M.R := hx
      rw [R_eq_O_of_none h] at hx'
      exact hx'
    | some g => exact memO_of_memR_split h hx
  have hRR : Ra.map ψ ≤ Ra := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.R.mul_mem hdR hy
  have hOO : Oa.map ψ ≤ Oa := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.L.O.mul_mem hdO hy
  have hRmO : Ra.map ψ ≤ Oa.map ψ := AddSubgroup.map_mono hRO
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ hRmO hOO
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ hRR hRO
  have e3 := AddSubgroup.relIndex_map_map_of_injective Ra Oa hψ
  let ι : M.L.O →+ E := M.L.O.subtype.toAddMonoidHom
  have hIeq : (Ideal.span {toO M δ}).toAddSubgroup = (Oa.map ψ).comap ι := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap, AddSubgroup.mem_map]
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [ψ, ι, d, mul_comm]⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ, ι, d, mul_comm] using hyx)⟩
  have htop : (⊤ : AddSubgroup M.L.O).map ι = Oa := by
    ext x
    simp [ι, Oa]
  have hn' : n = (Oa.map ψ).relIndex Oa := by
    have : n = ((Ideal.span {toO M δ}).toAddSubgroup).index := rfl
    rw [this, hIeq, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, htop]
  have ha : Ra.relIndex Oa ≠ 0 := by
    cases h : M.split with
    | none =>
      have : Ra = Oa := by
        ext x
        show x ∈ M.R ↔ x ∈ M.L.O
        rw [R_eq_O_of_none h]
      rw [this, AddSubgroup.relIndex_self]
      exact one_ne_zero
    | some g =>
      have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer g.q).1 g.q_irr
      have hmem : δ ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
        (IsLocalRing.mem_maximalIdeal δ).2 (mem_nonunits_iff.2 hu)
      rw [hmax, Ideal.mem_span_singleton'] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hle : Oa.map ψ ≤ Ra := by
        rintro _ ⟨y, hy, rfl⟩
        have : ψ y = algebraMap F E (g.q : F) * (algebraMap F E (c : F) * y) := by
          simp only [ψ, AddMonoidHom.coe_mulLeft, d, ← hc, MulMemClass.coe_mul, map_mul]
          ring
        rw [this]
        exact qmul_memR h (M.L.O.mul_mem (toO M c).2 hy)
      have hdvd := AddSubgroup.relIndex_dvd_of_le_left Oa hle
      rw [← hn'] at hdvd
      intro h0
      rw [h0, zero_dvd_iff] at hdvd
      omega
  have hm : (Ra.map ψ).relIndex Ra = n := by
    have hpos' : 0 < Ra.relIndex Oa := Nat.pos_of_ne_zero ha
    rw [e3] at e1
    rw [hn']
    have : Ra.relIndex Oa * (Oa.map ψ).relIndex Oa = Ra.relIndex Oa * (Ra.map ψ).relIndex Ra := by
      rw [e1, ← e2, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hpos' this).symm
  have hset : ((Ra.map ψ : AddSubgroup E) : Set E) = (fun y => d' * y) ⁻¹' (M.R : Set E) := by
    ext x
    simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : d' * ψ y = y := by simp [ψ, ← mul_assoc, hd'd]
      rw [this]; exact hy
    · intro hx
      exact ⟨d' * x, hx, by simp [ψ, ← mul_assoc, hdd']⟩
  have hRopen : IsOpen (M.R : Set E) := by
    cases h : M.split with
    | none => rw [R_eq_O_of_none h]; exact hO F E M.L
    | some g => exact isOpen_R_split h
  have hcont : Continuous (fun y : E => d' * y) := by
    have : (fun y : E => d' * y) = fun y => ((δ : F)⁻¹) • y := by
      funext y; rw [Algebra.smul_def]
    rw [this]
    exact continuous_const_smul _
  have hmeasS : MeasurableSet ((Ra.map ψ : AddSubgroup E) : Set E) := by
    rw [hset]; exact (hRopen.preimage hcont).measurableSet
  have key := measure_mul_relIndex_le M.mu hRR hmeasS
  rw [hm] at key
  have hvol : M.mu (Ra : Set E) = 1 := hOK.haar.volR
  rw [hvol] at key
  have himg : (fun y => d * y) '' (M.R : Set E) = ((Ra.map ψ : AddSubgroup E) : Set E) := by
    simp [ψ, Ra]
  unfold Model.modK
  rw [himg]
  have := ENNReal.toReal_mono ENNReal.one_ne_top key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ L` and use `isOpen_locO L`.
-/
theorem local_orbit_isOpen : LocOOpen := fun _ _ _ _ _ _ _ _ _ L => isOpen_locO L

/- English proof (translation)
The claim follows from `haarIdx_of_open local_orbit_isOpen`.
-/
theorem haar_measure_index_formula : HaarIdx := haarIdx_of_open local_orbit_isOpen

end PI.NGStepBBW
