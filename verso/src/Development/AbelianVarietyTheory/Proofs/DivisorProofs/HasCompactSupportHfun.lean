import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentTrace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.HeckeTraceIndep

variable {G : Type} [Group G]

def conjInter (K' : Subgroup G) (s : Finset G) : Subgroup G where
  carrier := {u | u ∈ K' ∧ ∀ g ∈ s, g⁻¹ * u * g ∈ K'}
  one_mem' := ⟨K'.one_mem, fun g _ => by simp [K'.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K'.mul_mem ha hb, fun g hg => ?_⟩
    convert K'.mul_mem (ha' g hg) (hb' g hg) using 1
    group
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K'.inv_mem ha, fun g hg => ?_⟩
    convert K'.inv_mem (ha' g hg) using 1
    group

/- English proof (translation)
Establish `: (conjInter K' s : Set G) = (K' : Set G) ∩ ⋂ g ∈ s, (fun u => g⁻¹ * u * g) ⁻¹' (K' : Set G)`. Use extensionality with `u`. Simplify using `[conjInter]`. Rewrite using `[this]`. Conclude with `hK'.inter (isOpen_biInter_finset fun g _ => hK'.preimage (by fun_prop))`.
-/
theorem isOpen_conjInter [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (s : Finset G) : IsOpen (conjInter K' s : Set G) := by
  have : (conjInter K' s : Set G) = (K' : Set G) ∩ ⋂ g ∈ s, (fun u => g⁻¹ * u * g) ⁻¹' (K' : Set G) := by
    ext u
    simp [conjInter]
  rw [this]
  exact hK'.inter (isOpen_biInter_finset fun g _ => hK'.preimage (by fun_prop))

/- English proof (translation)
Use `(show ∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v from hv) h` as an intermediate fact. Simplify using `using this`.
-/
theorem fixed_apply {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {H : Subgroup G}
    {v : V} (hv : v ∈ fixed ρ H) (h : H) : ρ h v = v := by
  have := (show ∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v from hv) h
  simpa using this

def hfun (K' U : Subgroup G) [Fintype (K' ⧸ U.subgroupOf K')] (s : Finset G) (a : G → ℂ) (y : G) : ℂ :=
  ∑ q : K' ⧸ U.subgroupOf K', ∑ g ∈ s,
    a g * if (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk y then 1 else 0

variable (K' U : Subgroup G) [Fintype (K' ⧸ U.subgroupOf K')] (s : Finset G) (a : G → ℂ)

/- English proof (translation)
Establish `: (QuotientGroup.mk (y * k) : G ⧸ K') = QuotientGroup.mk y` using `QuotientGroup.eq.2 (by simp [mul_assoc, K'.inv_mem hk])`. Simplify using `only [hfun, this]`.
-/
theorem hfun_mul_right {k : G} (hk : k ∈ K') (y : G) : hfun K' U s a (y * k) = hfun K' U s a y := by
  have : (QuotientGroup.mk (y * k) : G ⧸ K') = QuotientGroup.mk y :=
    QuotientGroup.eq.2 (by simp [mul_assoc, K'.inv_mem hk])
  simp only [hfun, this]

/- English proof (translation)
Unfold `hfun`. Set `kk : K'` to `⟨k, hk⟩`. Use `(Fintype.sum_equiv (MulAction.toPerm kk) _ _ fun q => ?_).symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : U.subgroupOf K', ((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') = kk * q.out * u := by`.

Establish `: (MulAction.toPerm kk q : K' ⧸ U.subgroupOf K') = QuotientGroup.mk (kk * q.out)`. Rewrite using `[MulAction.toPerm_apply]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `QuotientGroup.mk_out_eq_mul _ _`. Establish `hug : g⁻¹ * ((u : K') : G) * g ∈ K'` using `hU _ (Subgroup.mem_subgroupOf.1 u.2) g hg`. Establish `hiff : (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk y ↔ (QuotientGroup.mk ((((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk (k * y)`. Rewrite using `[hu, QuotientGroup.eq, QuotientGroup.eq]`. Simplify using `only [Subgroup.coe_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `K'.mul_mem (K'.inv_mem hug) h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [kk]`. Use `group`.

Introduce `h`. Use `K'.mul_mem hug h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [kk]`. Use `group`. Simplify using `only [hiff]`.
-/
theorem hfun_mul_left (hU : ∀ u ∈ U, ∀ g ∈ s, g⁻¹ * u * g ∈ K') {k : G} (hk : k ∈ K') (y : G) :
    hfun K' U s a (k * y) = hfun K' U s a y := by
  unfold hfun
  let kk : K' := ⟨k, hk⟩
  refine (Fintype.sum_equiv (MulAction.toPerm kk) _ _ fun q => ?_).symm
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨u, hu⟩ : ∃ u : U.subgroupOf K', ((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') = kk * q.out * u := by
    have : (MulAction.toPerm kk q : K' ⧸ U.subgroupOf K') = QuotientGroup.mk (kk * q.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    exact QuotientGroup.mk_out_eq_mul _ _
  have hug : g⁻¹ * ((u : K') : G) * g ∈ K' := hU _ (Subgroup.mem_subgroupOf.1 u.2) g hg
  have hiff : (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk y ↔
      (QuotientGroup.mk ((((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') : G) * g) : G ⧸ K') =
        QuotientGroup.mk (k * y) := by
    rw [hu, QuotientGroup.eq, QuotientGroup.eq]
    simp only [Subgroup.coe_mul]
    constructor
    · intro h
      convert K'.mul_mem (K'.inv_mem hug) h using 1
      simp only [kk]
      group
    · intro h
      convert K'.mul_mem hug h using 1
      simp only [kk]
      group
  simp only [hiff]

/- English proof (translation)
Unfold `hfun`. Use `Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun g hg => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hy q g hg (QuotientGroup.eq.1 h)), mul_zero]`.
-/
theorem hfun_eq_zero (y : G) (hy : ∀ q : K' ⧸ U.subgroupOf K', ∀ g ∈ s, (((q.out : K') : G) * g)⁻¹ * y ∉ K') :
    hfun K' U s a y = 0 := by
  unfold hfun
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun g hg => ?_
  rw [if_neg (fun h => hy q g hg (QuotientGroup.eq.1 h)), mul_zero]

/- English proof (translation)
Use `haveI : Finite (K' ⧸ U.subgroupOf K') := inferInstance`. Use `HasCompactSupport.intro' (K := ⋃ q : K' ⧸ U.subgroupOf K', ⋃ g ∈ s, (Homeomorph.mulLeft (((q.out : K') : G) * g)⁻¹) ⁻¹' (K' : Set G)) ?_ ?_ ?_` and prove the remaining obligations. Conclude with `isCompact_iUnion fun q => s.isCompact_biUnion fun g _ => (Homeomorph.isCompact_preimage _).2 hK'c`. Conclude with `isClosed_iUnion_of_finite fun q => isClosed_biUnion_finset fun g _ => (Subgroup.isClosed_of_isOpen _ hK'o).preimage (Homeomorph.continuous _)`. Introduce `y hy`.

Use `hfun_eq_zero K' U s a y fun q g hg hmem => hy ?_` and prove the remaining obligations. Conclude with `Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨g, hg, hmem⟩⟩`.
-/
theorem hasCompactSupport_hfun [TopologicalSpace G] [IsTopologicalGroup G] (hK'c : IsCompact (K' : Set G))
    (hK'o : IsOpen (K' : Set G)) : HasCompactSupport (hfun K' U s a) := by
  haveI : Finite (K' ⧸ U.subgroupOf K') := inferInstance
  refine HasCompactSupport.intro' (K := ⋃ q : K' ⧸ U.subgroupOf K', ⋃ g ∈ s,
    (Homeomorph.mulLeft (((q.out : K') : G) * g)⁻¹) ⁻¹' (K' : Set G)) ?_ ?_ ?_
  · exact isCompact_iUnion fun q => s.isCompact_biUnion fun g _ => (Homeomorph.isCompact_preimage _).2 hK'c
  · exact isClosed_iUnion_of_finite fun q => isClosed_biUnion_finset fun g _ =>
      (Subgroup.isClosed_of_isOpen _ hK'o).preimage (Homeomorph.continuous _)
  · intro y hy
    refine hfun_eq_zero K' U s a y fun q g hg hmem => hy ?_
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨g, hg, hmem⟩⟩

/- English proof (translation)
Use `set T : Finset (G ⧸ K') := Finset.univ.biUnion fun q : K' ⧸ U.subgroupOf K' => s.image fun g => (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') with hT`. Establish `hmemT : ∀ (q : K' ⧸ U.subgroupOf K'), ∀ g ∈ s, (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') ∈ T` using `fun q g hg => Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, Finset.mem_image.2 ⟨g, hg, rfl⟩⟩`. Establish `hsupp : (Function.support fun Q : G ⧸ K' => hfun K' U s a Q.out • (ρ Q.out ∘ₗ LinearMap.id)) ⊆ T`. Introduce `Q hQ`. Assume the negation of the conclusion as `hQT`.

Apply `hQ` to reduce the goal to its premises. Establish `: hfun K' U s a Q.out = 0`. Use `hfun_eq_zero K' U s a _ fun q g hg hmem => hQT ?_` and prove the remaining obligations. Establish `: (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = Q`. Rewrite using `[← QuotientGroup.out_eq' Q]`.

Conclude with `QuotientGroup.eq.2 hmem`. Rewrite using `[← this]`. Conclude with `hmemT q g hg`. Simplify using `[this]`. Establish `hout : ∀ z : G, ρ ((QuotientGroup.mk z : G ⧸ K').out) v = ρ z v`.

Introduce `z`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul K' z`. Rewrite using `[hh, map_mul, Module.End.mul_apply, fixed_apply hv h]`. Unfold `levOp`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, LinearMap.smul_apply, LinearMap.sum_apply]`.

Use `congr 1`. Simplify using `only [hfun, Finset.sum_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, QuotientGroup.out_eq']`. Rewrite using `[Finset.sum_comm (s := T)]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := T)]`.

Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.sum_apply, Finset.sum_ite_eq, if_pos (hmemT q g hg), LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, hout]`.
-/
theorem levOp_hfun {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (v : V) (hv : v ∈ fixed ρ K') :
    levOp ρ K K' (hfun K' U s a) LinearMap.id v =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q : K' ⧸ U.subgroupOf K', ∑ g ∈ s, a g • ρ (((q.out : K') : G) * g) v := by
  set T : Finset (G ⧸ K') := Finset.univ.biUnion fun q : K' ⧸ U.subgroupOf K' =>
    s.image fun g => (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') with hT
  have hmemT : ∀ (q : K' ⧸ U.subgroupOf K'), ∀ g ∈ s, (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') ∈ T :=
    fun q g hg => Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have hsupp : (Function.support fun Q : G ⧸ K' => hfun K' U s a Q.out • (ρ Q.out ∘ₗ LinearMap.id)) ⊆ T := by
    intro Q hQ
    by_contra hQT
    apply hQ
    have : hfun K' U s a Q.out = 0 := by
      refine hfun_eq_zero K' U s a _ fun q g hg hmem => hQT ?_
      have : (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = Q := by
        rw [← QuotientGroup.out_eq' Q]
        exact QuotientGroup.eq.2 hmem
      rw [← this]
      exact hmemT q g hg
    simp [this]
  have hout : ∀ z : G, ρ ((QuotientGroup.mk z : G ⧸ K').out) v = ρ z v := by
    intro z
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' z
    rw [hh, map_mul, Module.End.mul_apply, fixed_apply hv h]
  unfold levOp
  rw [finsum_eq_sum_of_support_subset _ hsupp, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  simp only [hfun, Finset.sum_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, mul_ite,
    mul_one, mul_zero, ite_smul, zero_smul, QuotientGroup.out_eq']
  rw [Finset.sum_comm (s := T)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm (s := T)]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [← LinearMap.sum_apply, Finset.sum_ite_eq, if_pos (hmemT q g hg), LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.id_apply, hout]

end GlobalTheory.HeckeTraceIndep

namespace GlobalTheory.HeckeTraceIndep

/- English proof (translation)
Introduce `G _ _ _ K hKo hKc K' hL ι _ σ hfix hne c hc i₀`. Take `⟨hK'o, hK'K, -⟩` from `hL`. Establish `hK'c : IsCompact (K' : Set G)` using `hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hK'o) hK'K`. Use `haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).ρ.asModule := fun i => (Representation.irreducible_iff_isSimpleModule_asModule _).mp (σ i).irred`. Establish `hzero : ∀ i j, i ≠ j → ∀ f : (σ i).ρ.asModule →ₗ[MonoidAlgebra ℂ G] (σ j).ρ.asModule, f = 0`.

Introduce `i j hij f`. Use `haveI := (σ i).irred`. Use `haveI := (σ j).irred`. Use `haveI : IsEmpty ((σ i).ρ.Equiv (σ j).ρ) := ⟨fun e => hij (hne i j ⟨e⟩)⟩`. Use `haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i).ρ (σ j).ρ).toEquiv.symm.subsingleton`.

Conclude with `Subsingleton.elim _ _`. Use `haveI : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ K') := fun i => (hfix i).1`. Set `b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (fixed (σ i).ρ K'))) ℂ (fixed (σ i).ρ K')` to `fun i => Module.finBasis ℂ _`. Take `⟨x, hx⟩` from `GlobalTheory.SimpleCharIndep.exists_smul_eq_ite (R := MonoidAlgebra ℂ G) (fun i => (σ i).ρ.asModule) hzero i₀ (fun i => Finset.univ.image fun k => (((b i k : fixed (σ i).ρ K') : (σ i).V) : (σ i).ρ.asModule))`. Use `set s : Finset G := x.coeff.support`.

Use `set U : Subgroup G := conjInter K' s`. Establish `hUo : IsOpen (U : Set G)` using `isOpen_conjInter K' hK'o s`. Use `haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c`. Use `haveI : Finite (K' ⧸ U.subgroupOf K') := Subgroup.quotient_finite_of_isOpen _ (by`. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `hUo.preimage continuous_subtype_val)`. Use `letI : Fintype (K' ⧸ U.subgroupOf K') := Fintype.ofFinite _`. Establish `hU : ∀ u ∈ U, ∀ g ∈ s, g⁻¹ * u * g ∈ K'` using `fun u hu => hu.2`. Use `set f : G → ℂ := hfun K' U s (fun g => x.coeff g) with hf`. Establish `hHecke : IsHecke K' f` using `⟨hasCompactSupport_hfun K' U s _ hK'c hK'o, fun k hk y => ⟨hfun_mul_left K' U s _ hU hk y, hfun_mul_right K' U s _ hk y⟩⟩`.

Use `set r : ℂ := ((K'.relIndex K : ℕ) : ℂ) with hr_def`. Use `set N : ℕ := Fintype.card (K' ⧸ U.subgroupOf K') with hN_def`. Establish `hact : ∀ i (v : (σ i).V), v ∈ fixed (σ i).ρ K' → levOp (σ i).ρ K K' f LinearMap.id v = r⁻¹ • ∑ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) ((σ i).ρ.asAlgebraHom x v)`. Introduce `i v hv`. Rewrite using `[hf, levOp_hfun K' U s _ (σ i).ρ K v hv]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `[map_mul, Module.End.mul_apply]`.

Establish `hbasis : ∀ i k, levOp (σ i).ρ K K' f LinearMap.id (b i k : (σ i).V) = (if i = i₀ then r⁻¹ * N else 0) • (b i k : (σ i).V)`. Introduce `i k`. Establish `hxk` using `hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))`. Rewrite using `[hact i _ (b i k).2]`. Distinguish the cases in `hi : i = i₀`.

Establish `e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = b i k`. Conclude with `hxk.trans (if_pos hi)`. Rewrite using `[if_pos hi, e]`. Establish `h2 : ∀ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) (b i k : (σ i).V) = b i k` using `fun q => fixed_apply (b i k).2 q.out`. Simplify using `only [h2, Finset.sum_const, Finset.card_univ]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Establish `e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = 0` using `hxk.trans (if_neg hi)`. Rewrite using `[if_neg hi, e]`. Simplify using the standard rewrite rules. Establish `hfixedEq : ∀ i, ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v = (if i = i₀ then r⁻¹ * N else 0) • v`.

Introduce `i v hv`. Use `LinearMap.congr_fun ((b i).ext (f₁ := (levOp (σ i).ρ K K' f LinearMap.id).comp (fixed (σ i).ρ K').subtype) (f₂ := (if i = i₀ then r⁻¹ * N else 0) • (fixed (σ i).ρ K').subtype) (fun k => by` as an intermediate fact. Rewrite using `[LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply]`. Conclude with `hbasis i k)) ⟨v, hv⟩`. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply]`.

Conclude with `this`. Establish `htr : ∀ i, twTr (σ i).ρ K K' f LinearMap.id = (if i = i₀ then r⁻¹ * N else 0) * Module.finrank ℂ (fixed (σ i).ρ K')`. Introduce `i`. Establish `hmem : ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v ∈ fixed (σ i).ρ K'` using `fun v hv => by`. Rewrite using `[hfixedEq i v hv]`.

Conclude with `Submodule.smul_mem _ _ hv`. Unfold `twTr`. Rewrite using `[dif_pos hmem]`. Establish `: (levOp (σ i).ρ K K' f LinearMap.id).restrict hmem = (if i = i₀ then r⁻¹ * N else 0) • LinearMap.id`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.coe_restrict_apply, hfixedEq i v v.2, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]`. Rewrite using `[this, map_smul, LinearMap.trace_id, smul_eq_mul]`. Establish `hsum` using `hc f hHecke`. Simplify using `only [htr] at hsum`. Rewrite `hsum` using `[Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp), if_pos rfl]`.

Establish `hr : r ≠ 0` using `by haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (by`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hK'o.preimage continuous_subtype_val)`. Rewrite using `[hr_def, Nat.cast_ne_zero]`. Conclude with `Subgroup.index_ne_zero_of_finite`.

Establish `hN : (N : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hd : (Module.finrank ℂ (fixed (σ i₀).ρ K') : ℂ) ≠ 0` using `by haveI : Nontrivial (fixed (σ i₀).ρ K') := Submodule.nontrivial_iff_ne_bot.2 (hfix i₀).2`. Conclude with `Module.finrank_pos.ne'` after adjusting the coercions. Conclude with `(mul_eq_zero.1 hsum).resolve_right (mul_ne_zero (mul_ne_zero (inv_ne_zero hr) hN) hd)`.
-/
theorem twTr_linearIndependent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ K' : Subgroup G, IsLevel (MonoidHom.id G) K K' → ∀ (ι : Type) [Fintype ι] (σ : ι → SmIrr G), (∀ i, FiniteDimensional ℂ (fixed (σ i).ρ K') ∧ fixed (σ i).ρ K' ≠ ⊥) → (∀ i j, Nonempty ((σ i).ρ.Equiv (σ j).ρ) → i = j) → ∀ c : ι → ℂ, (∀ f, IsHecke K' f → ∑ i, c i * twTr (σ i).ρ K K' f LinearMap.id = 0) → ∀ i, c i = 0 := by
  intro G _ _ _ K hKo hKc K' hL ι _ σ hfix hne c hc i₀
  obtain ⟨hK'o, hK'K, -⟩ := hL
  have hK'c : IsCompact (K' : Set G) := hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hK'o) hK'K
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).ρ.asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (σ i).irred
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).ρ.asModule →ₗ[MonoidAlgebra ℂ G] (σ j).ρ.asModule, f = 0 := by
    intro i j hij f
    haveI := (σ i).irred
    haveI := (σ j).irred
    haveI : IsEmpty ((σ i).ρ.Equiv (σ j).ρ) := ⟨fun e => hij (hne i j ⟨e⟩)⟩
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i).ρ (σ j).ρ).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  haveI : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ K') := fun i => (hfix i).1
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (fixed (σ i).ρ K'))) ℂ (fixed (σ i).ρ K') :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := GlobalTheory.SimpleCharIndep.exists_smul_eq_ite (R := MonoidAlgebra ℂ G)
    (fun i => (σ i).ρ.asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : fixed (σ i).ρ K') : (σ i).V) : (σ i).ρ.asModule))
  set s : Finset G := x.coeff.support
  set U : Subgroup G := conjInter K' s
  have hUo : IsOpen (U : Set G) := isOpen_conjInter K' hK'o s
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  haveI : Finite (K' ⧸ U.subgroupOf K') := Subgroup.quotient_finite_of_isOpen _ (by
    rw [Subgroup.coe_subgroupOf]; exact hUo.preimage continuous_subtype_val)
  letI : Fintype (K' ⧸ U.subgroupOf K') := Fintype.ofFinite _
  have hU : ∀ u ∈ U, ∀ g ∈ s, g⁻¹ * u * g ∈ K' := fun u hu => hu.2
  set f : G → ℂ := hfun K' U s (fun g => x.coeff g) with hf
  have hHecke : IsHecke K' f := ⟨hasCompactSupport_hfun K' U s _ hK'c hK'o,
    fun k hk y => ⟨hfun_mul_left K' U s _ hU hk y, hfun_mul_right K' U s _ hk y⟩⟩
  set r : ℂ := ((K'.relIndex K : ℕ) : ℂ) with hr_def
  set N : ℕ := Fintype.card (K' ⧸ U.subgroupOf K') with hN_def
  have hact : ∀ i (v : (σ i).V), v ∈ fixed (σ i).ρ K' → levOp (σ i).ρ K K' f LinearMap.id v =
      r⁻¹ • ∑ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) ((σ i).ρ.asAlgebraHom x v) := by
    intro i v hv
    rw [hf, levOp_hfun K' U s _ (σ i).ρ K v hv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [map_mul, Module.End.mul_apply]
  have hbasis : ∀ i k, levOp (σ i).ρ K K' f LinearMap.id (b i k : (σ i).V) =
      (if i = i₀ then r⁻¹ * N else 0) • (b i k : (σ i).V) := by
    intro i k
    have hxk := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [hact i _ (b i k).2]
    by_cases hi : i = i₀
    · have e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = b i k := by
        exact hxk.trans (if_pos hi)
      rw [if_pos hi, e]
      have h2 : ∀ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) (b i k : (σ i).V) = b i k :=
        fun q => fixed_apply (b i k).2 q.out
      simp only [h2, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    · have e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = 0 := hxk.trans (if_neg hi)
      rw [if_neg hi, e]
      simp
  have hfixedEq : ∀ i, ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v =
      (if i = i₀ then r⁻¹ * N else 0) • v := by
    intro i v hv
    have := LinearMap.congr_fun ((b i).ext (f₁ := (levOp (σ i).ρ K K' f LinearMap.id).comp (fixed (σ i).ρ K').subtype)
      (f₂ := (if i = i₀ then r⁻¹ * N else 0) • (fixed (σ i).ρ K').subtype) (fun k => by
        rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply]
        exact hbasis i k)) ⟨v, hv⟩
    rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply] at this
    exact this
  have htr : ∀ i, twTr (σ i).ρ K K' f LinearMap.id =
      (if i = i₀ then r⁻¹ * N else 0) * Module.finrank ℂ (fixed (σ i).ρ K') := by
    intro i
    have hmem : ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v ∈ fixed (σ i).ρ K' :=
      fun v hv => by
        rw [hfixedEq i v hv]
        exact Submodule.smul_mem _ _ hv
    unfold twTr
    rw [dif_pos hmem]
    have : (levOp (σ i).ρ K K' f LinearMap.id).restrict hmem =
        (if i = i₀ then r⁻¹ * N else 0) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [LinearMap.coe_restrict_apply, hfixedEq i v v.2, LinearMap.smul_apply, LinearMap.id_apply,
        Submodule.coe_smul]
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hsum := hc f hHecke
  simp only [htr] at hsum
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp), if_pos rfl] at hsum
  have hr : r ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val)
    rw [hr_def, Nat.cast_ne_zero]
    exact Subgroup.index_ne_zero_of_finite
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (Module.finrank ℂ (fixed (σ i₀).ρ K') : ℂ) ≠ 0 := by
    haveI : Nontrivial (fixed (σ i₀).ρ K') := Submodule.nontrivial_iff_ne_bot.2 (hfix i₀).2
    exact_mod_cast Module.finrank_pos.ne'
  exact (mul_eq_zero.1 hsum).resolve_right (mul_ne_zero (mul_ne_zero (inv_ne_zero hr) hN) hd)

end GlobalTheory.HeckeTraceIndep
