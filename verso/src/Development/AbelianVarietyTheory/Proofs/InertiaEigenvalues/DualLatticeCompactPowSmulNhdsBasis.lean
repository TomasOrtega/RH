import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualTop

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Take `⟨d, hd⟩` from `h (k + 1)`. Establish `hk : ϖ ^ k ≠ 0` using `pow_ne_zero _ hϖ.ne_zero`. Establish `hu : (u : O) = ϖ * d`.

Apply `mul_right_cancel₀ hk` to reduce the goal to its premises. Rewrite using `[hd]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro d hu.symm) u.isUnit)`.
-/
theorem eq_zero_of_forall_pow_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ c : O} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  obtain ⟨d, hd⟩ := h (k + 1)
  have hk : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hu : (u : O) = ϖ * d := by
    apply mul_right_cancel₀ hk
    rw [hd]; ring
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro d hu.symm) u.isUnit)

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

/- English proof (translation)
The claim follows from `(IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT (FractionRing O)).map_smul (D.bT.flip y) k x`.
-/
theorem bT_smul_left (k : FractionRing O) (x : VT) (y : VT') :
    D.bT (k • x) y = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT
    (FractionRing O)).map_smul (D.bT.flip y) k x

/- English proof (translation)
The claim follows from `(IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT' (FractionRing O)).map_smul (D.bT x) k y`.
-/
theorem bT_smul_right (k : FractionRing O) (x : VT) (y : VT') :
    D.bT x (k • y) = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT'
    (FractionRing O)).map_smul (D.bT x) k y

/- English proof (translation)
The claim follows from `(hP 0).unique h (fun x => by simp)`.
-/
theorem eq_zero_of_bT (hP : PerfectRight D.bT) {y : VT'} (h : ∀ x, D.bT x y = 0) : y = 0 :=
  (hP 0).unique h (fun x => by simp)

/- English proof (translation)
Set `ψ` to `(D.bT.flip y).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)`. Establish `hs : Submodule.span (FractionRing O) (D.T : Set VT) ≤ LinearMap.ker ψ` using `Submodule.span_le.2 fun z hz => LinearMap.mem_ker.2 (h z hz)`. Establish `hx : x ∈ Submodule.span (FractionRing O) (D.T : Set VT)` using `hL.2 ▸ Submodule.mem_top`. Conclude with `LinearMap.mem_ker.1 (hs hx)`.
-/
theorem dualLatticePairing_eq_zero_of_mem_lattice (hL : IsLatticeIn D.T) {y : VT'} (h : ∀ x ∈ D.T, D.bT x y = 0) (x : VT) :
    D.bT x y = 0 := by
  let ψ := (D.bT.flip y).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
  have hs : Submodule.span (FractionRing O) (D.T : Set VT) ≤ LinearMap.ker ψ :=
    Submodule.span_le.2 fun z hz => LinearMap.mem_ker.2 (h z hz)
  have hx : x ∈ Submodule.span (FractionRing O) (D.T : Set VT) := hL.2 ▸ Submodule.mem_top
  exact LinearMap.mem_ker.1 (hs hx)

/- English proof (translation)
The claim follows from `D.contbT.comp (continuous_const.prodMk continuous_id)`.
-/
theorem cont_bT (x : VT) : Continuous fun y : VT' => D.bT x y :=
  D.contbT.comp (continuous_const.prodMk continuous_id)

/- English proof (translation)
Establish `: ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) = Set.range (algebraMap O (FractionRing O))`. Use extensionality with `t`. Simplify using `[Submodule.mem_one]`. Rewrite using `[this]`. Conclude with `hemb.isOpen_range`.
-/
theorem isOpen_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsOpen ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
  have : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext t; simp [Submodule.mem_one]
  rw [this]; exact hemb.isOpen_range

/- English proof (translation)
The claim follows from `AddSubgroup.isClosed_of_isOpen (1 : Submodule O (FractionRing O)).toAddSubgroup (isOpen_one hemb)`.
-/
theorem isClosed_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) :=
  AddSubgroup.isClosed_of_isOpen (1 : Submodule O (FractionRing O)).toAddSubgroup (isOpen_one hemb)

/- English proof (translation)
Establish `: (D.T' : Set VT') = ⋂ x ∈ D.T, (fun y => D.bT x y) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))`. Use extensionality with `y`. Conclude with `⟨fun h => Set.mem_iInter₂.2 fun x hx => h x hx, fun h x hx => Set.mem_iInter₂.1 h x hx⟩`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun x _ => (isClosed_one hemb).preimage (cont_bT D x)`.
-/
theorem isClosed_dualLattice_of_pairing (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed (D.T' : Set VT') := by
  have : (D.T' : Set VT') = ⋂ x ∈ D.T,
      (fun y => D.bT x y) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext y
    exact ⟨fun h => Set.mem_iInter₂.2 fun x hx => h x hx, fun h x hx => Set.mem_iInter₂.1 h x hx⟩
  rw [this]
  exact isClosed_biInter fun x _ => (isClosed_one hemb).preimage (cont_bT D x)

end Lat

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

/- English proof (translation)
Take `⟨s, hs⟩` from `hL.1`. Establish `hsK : Submodule.span (FractionRing O) (s : Set VT) = ⊤`. Rewrite using `[eq_top_iff, ← hL.2]`. Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[← hs]`.

Conclude with `Submodule.span_subset_span O (FractionRing O) (s : Set VT) hx`. Take `⟨b, hbs, hbspan, hbli⟩` from `exists_linearIndependent (FractionRing O) (s : Set VT)`. Use `haveI : Fintype b := (s.finite_toSet.subset hbs).fintype`. Take `⟨e, he⟩ : ∃ e : Module.Basis b (FractionRing O) VT, ∀ i, e i = (i : VT)` from `⟨Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hsK])), fun i => Module.Basis.mk_apply _ _ i⟩`. Establish `hbT : ∀ i : b, (i : VT) ∈ D.T` using `fun i => hs ▸ Submodule.subset_span (hbs i.2)`.

Use `choose f hf using fun i : b => (hP (e.coord i)).exists`. Set `Φ : (b → O) → VT'` to `fun c => ∑ i, c i • f i`. Establish `hΦ : Continuous Φ` using `continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const`. Establish `hsub : (D.T' : Set VT') ⊆ Set.range Φ`. Introduce `y hy`.

Establish `hy' : ∀ i : b, D.bT (i : VT) y ∈ (1 : Submodule O (FractionRing O))` using `fun i => hy _ (hbT i)`. Use `choose c hc using fun i => Submodule.mem_one.1 (hy' i)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `symm`. Rewrite using `[← sub_eq_zero]`.

Apply `eq_zero_of_bT D hP` to reduce the goal to its premises. Introduce `x`. Establish `hx : D.bT x y = ∑ i, e.coord i x * algebraMap O (FractionRing O) (c i)` using `by conv_lhs => rw [← e.sum_repr x]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[bT_smul_left, he, ← hc i, Module.Basis.coord_apply]`. Rewrite using `[map_sub, map_sum, hx, sub_eq_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hf, Algebra.smul_def, mul_comm]`. Conclude with `(isCompact_range hΦ).of_isClosed_subset (isClosed_dualLattice_of_pairing D hemb) hsub`.
-/
theorem isCompact_dualLattice_of_pairing [CompactSpace O] (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) : IsCompact (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hL.1
  have hsK : Submodule.span (FractionRing O) (s : Set VT) = ⊤ := by
    rw [eq_top_iff, ← hL.2]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [← hs] at hx
    exact Submodule.span_subset_span O (FractionRing O) (s : Set VT) hx
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (FractionRing O) (s : Set VT)
  haveI : Fintype b := (s.finite_toSet.subset hbs).fintype
  obtain ⟨e, he⟩ : ∃ e : Module.Basis b (FractionRing O) VT, ∀ i, e i = (i : VT) :=
    ⟨Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hsK])),
      fun i => Module.Basis.mk_apply _ _ i⟩
  have hbT : ∀ i : b, (i : VT) ∈ D.T := fun i => hs ▸ Submodule.subset_span (hbs i.2)
  choose f hf using fun i : b => (hP (e.coord i)).exists
  let Φ : (b → O) → VT' := fun c => ∑ i, c i • f i
  have hΦ : Continuous Φ := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hsub : (D.T' : Set VT') ⊆ Set.range Φ := by
    intro y hy
    have hy' : ∀ i : b, D.bT (i : VT) y ∈ (1 : Submodule O (FractionRing O)) := fun i => hy _ (hbT i)
    choose c hc using fun i => Submodule.mem_one.1 (hy' i)
    refine ⟨c, ?_⟩
    symm
    rw [← sub_eq_zero]
    apply eq_zero_of_bT D hP
    intro x
    have hx : D.bT x y = ∑ i, e.coord i x * algebraMap O (FractionRing O) (c i) := by
      conv_lhs => rw [← e.sum_repr x]
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bT_smul_left, he, ← hc i, Module.Basis.coord_apply]
    rw [map_sub, map_sum, hx, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf, Algebra.smul_def, mul_comm]
  exact (isCompact_range hΦ).of_isClosed_subset (isClosed_dualLattice_of_pairing D hemb) hsub

end Lat2

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

/- English proof (translation)
Take `⟨s, hs⟩` from `hL.1`. Use `set a : FractionRing O := algebraMap O (FractionRing O) ϖ ^ n with ha`. Establish `ha0 : a ≠ 0` using `pow_ne_zero _ (fun h => hϖ.ne_zero (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero])))`. Set `W : Set ↥D.T'` to `⋂ x ∈ s, (fun z : ↥D.T' => D.bT (a⁻¹ • x) (z : VT')) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))`. Establish `hW : IsOpen W` using `isOpen_biInter_finset fun x _ => (isOpen_one hemb).preimage ((cont_bT D _).comp continuous_subtype_val)`.

Establish `h0 : (0 : ↥D.T') ∈ W` using `Set.mem_iInter₂.2 fun x _ => by`. Simplify using `only [Set.mem_preimage, ZeroMemClass.coe_zero, map_zero, SetLike.mem_coe]`. Conclude with `Submodule.zero_mem _`. Establish `hWsub : W ⊆ ((powSub (M` using `↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by`. Introduce `z hz`.

Establish `hz'` using `Set.mem_iInter₂.1 hz`. Establish `hyT : a⁻¹ • (z : VT') ∈ D.T'`. Introduce `x hx`. Establish `hle : Submodule.span O (s : Set VT) ≤ (1 : Submodule O (FractionRing O)).comap (D.bT.flip (a⁻¹ • (z : VT')))`. Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations.

Use `hz' x hx` as an intermediate fact. Simplify using `only [Set.mem_preimage, SetLike.mem_coe] at this`. Use `show D.bT x (a⁻¹ • (z : VT')) ∈ (1 : Submodule O (FractionRing O))`. Rewrite using `[bT_smul_right, ← bT_smul_left]` and apply the resulting hypothesis. Rewrite `hle` using `[hs]`.

Conclude with `hle hx`. Use `mem_powSub.2 ⟨⟨a⁻¹ • (z : VT'), hyT⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ϖ ^ n • a⁻¹ • (z : VT') = z`. Rewrite using `[← algebraMap_smul (FractionRing O) (ϖ ^ n), smul_smul, map_pow, ← ha, mul_inv_cancel₀ ha0, one_smul]`. Conclude with `AddSubgroup.isOpen_of_mem_nhds (powSub (M := ↥D.T') ϖ n).toAddSubgroup (Filter.mem_of_superset (hW.mem_nhds h0) hWsub)`.
-/
theorem isOpen_powSub (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
  obtain ⟨s, hs⟩ := hL.1
  set a : FractionRing O := algebraMap O (FractionRing O) ϖ ^ n with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (fun h => hϖ.ne_zero
    (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero])))
  let W : Set ↥D.T' := ⋂ x ∈ s, (fun z : ↥D.T' => D.bT (a⁻¹ • x) (z : VT')) ⁻¹'
    ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))
  have hW : IsOpen W := isOpen_biInter_finset fun x _ =>
    (isOpen_one hemb).preimage ((cont_bT D _).comp continuous_subtype_val)
  have h0 : (0 : ↥D.T') ∈ W := Set.mem_iInter₂.2 fun x _ => by
    simp only [Set.mem_preimage, ZeroMemClass.coe_zero, map_zero, SetLike.mem_coe]
    exact Submodule.zero_mem _
  have hWsub : W ⊆ ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
    intro z hz
    have hz' := Set.mem_iInter₂.1 hz
    have hyT : a⁻¹ • (z : VT') ∈ D.T' := by
      intro x hx
      have hle : Submodule.span O (s : Set VT) ≤
          (1 : Submodule O (FractionRing O)).comap (D.bT.flip (a⁻¹ • (z : VT'))) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have := hz' x hx
        simp only [Set.mem_preimage, SetLike.mem_coe] at this
        show D.bT x (a⁻¹ • (z : VT')) ∈ (1 : Submodule O (FractionRing O))
        rwa [bT_smul_right, ← bT_smul_left]
      rw [hs] at hle
      exact hle hx
    refine mem_powSub.2 ⟨⟨a⁻¹ • (z : VT'), hyT⟩, Subtype.ext ?_⟩
    show ϖ ^ n • a⁻¹ • (z : VT') = z
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n), smul_smul, map_pow, ← ha, mul_inv_cancel₀ ha0,
      one_smul]
  exact AddSubgroup.isOpen_of_mem_nhds (powSub (M := ↥D.T') ϖ n).toAddSubgroup
    (Filter.mem_of_superset (hW.mem_nhds h0) hWsub)

/- English proof (translation)
Use `Subtype.ext (eq_zero_of_bT D hP (dualLatticePairing_eq_zero_of_mem_lattice D hL (fun x hx => ?_)))` and prove the remaining obligations. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (z.2 x hx)`. Establish `hdvd : ∀ n : ℕ, ϖ ^ n ∣ c`. Introduce `n`. Take `⟨w, hw⟩` from `mem_powSub.1 (hz n)`.

Take `⟨d, hd⟩` from `Submodule.mem_one.1 (w.2 x hx)`. Use `⟨d, IsFractionRing.injective O (FractionRing O) ?_⟩` and prove the remaining obligations. Rewrite using `[hc, ← hw, map_mul, hd]`. Use `show D.bT x (ϖ ^ n • (w : VT')) = _`. Rewrite using `[map_smul, Algebra.smul_def]`.

Rewrite using `[← hc, eq_zero_of_forall_pow_dvd hϖ hdvd, map_zero]`.
-/
theorem eq_zero_of_mem_powSub (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) {ϖ : O}
    (hϖ : Irreducible ϖ) {z : ↥D.T'} (hz : ∀ n, z ∈ powSub (M := ↥D.T') ϖ n) : z = 0 := by
  refine Subtype.ext (eq_zero_of_bT D hP (dualLatticePairing_eq_zero_of_mem_lattice D hL (fun x hx => ?_)))
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (z.2 x hx)
  have hdvd : ∀ n : ℕ, ϖ ^ n ∣ c := by
    intro n
    obtain ⟨w, hw⟩ := mem_powSub.1 (hz n)
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (w.2 x hx)
    refine ⟨d, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [hc, ← hw, map_mul, hd]
    show D.bT x (ϖ ^ n • (w : VT')) = _
    rw [map_smul, Algebra.smul_def]
  rw [← hc, eq_zero_of_forall_pow_dvd hϖ hdvd, map_zero]

end Lat3

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

/- English proof (translation)
Introduce `O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D hO hemb hL hP hT2 ϖ hϖ`. Establish `hK : IsCompact (D.T' : Set VT')` using `isCompact_dualLattice_of_pairing D hemb hL hP`. Use `haveI : CompactSpace ↥D.T' := isCompact_iff_compactSpace.1 hK`. Establish `hopen` using `isOpen_powSub D hemb hL hϖ`. Use `⟨inferInstance, hopen, fun U hU => ?_⟩` and prove the remaining obligations.

Take `⟨V, hVU, hV, h0V⟩` from `mem_nhds_iff.1 hU`. Take `⟨n, hn⟩` from `hV.isClosed_compl.isCompact.elim_directed_family_closed (fun n : ℕ => ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) (fun n => AddSubgroup.isClosed_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n)) (by`. Rewrite using `[← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]`. Introduce `z hz hz'`. Establish `: z = 0` using `eq_zero_of_mem_powSub D hL hP hϖ fun n => Set.mem_iInter.1 hz' n`.

Conclude with `hz (this ▸ h0V))`. Use the proof step `(fun a b => ⟨max a b, fun x hx => powSub_anti ϖ (le_max_left a b) hx, fun x hx => powSub_anti ϖ (le_max_right a b) hx⟩)`. Use `⟨n, fun z hz => hVU ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hn) hc hz`.
-/
theorem dualLat_compact_powSub_nhds : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D hO hemb hL hP hT2 ϖ hϖ
  have hK : IsCompact (D.T' : Set VT') := isCompact_dualLattice_of_pairing D hemb hL hP
  haveI : CompactSpace ↥D.T' := isCompact_iff_compactSpace.1 hK
  have hopen := isOpen_powSub D hemb hL hϖ
  refine ⟨inferInstance, hopen, fun U hU => ?_⟩
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.1 hU
  obtain ⟨n, hn⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed
    (fun n : ℕ => ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T'))
    (fun n => AddSubgroup.isClosed_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro z hz hz'
      have : z = 0 := eq_zero_of_mem_powSub D hL hP hϖ fun n => Set.mem_iInter.1 hz' n
      exact hz (this ▸ h0V))
    (fun a b => ⟨max a b, fun x hx => powSub_anti ϖ (le_max_left a b) hx,
      fun x hx => powSub_anti ϖ (le_max_right a b) hx⟩)
  refine ⟨n, fun z hz => hVU ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hn) hc hz

end GlobalTheory.LocDualTop
