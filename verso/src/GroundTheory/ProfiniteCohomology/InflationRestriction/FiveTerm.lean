import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.Transgression
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

section Restriction

noncomputable def cohomologyResInv : cohomology A 1 →ₗ[k] cohomologyConjInvariants A N 1 :=
  (cohomologyRes A N 1).hom.codRestrict _ (cohomologyRes_mem_cohomologyConjInvariants A N)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cohomologyResInv_apply (h : cohomology A 1) :
    (cohomologyResInv A N h : cohomology (Rep.res N.subtype A) 1) = (cohomologyRes A N 1).hom h :=
  rfl

/- English proof (translation)
Simplify using `only [cocycleOneApply, cocyclesMapAlong, iCycles_cyclesMap_apply]`. Both sides reduce to the same expression.
-/
theorem cocycleOneApply_cocyclesMapAlong (y : cocycles A 1) (n : N) :
    cocycleOneApply A N ((cocyclesMapAlong N.subtype (continuous_subgroup_subtype N) (𝟙 _) 1).hom y)
      n = cocycleOneApplyG A y n := by
  simp only [cocycleOneApply, cocyclesMapAlong, iCycles_cyclesMap_apply]
  rfl

/- English proof (translation)
Rewrite using `[cohomologyRes, cohomologyMapAlong]`. Use `erw [homologyMap_homologyπ_apply]`. Both sides reduce to the same expression.
-/
theorem cohomologyRes_π (y : cocycles A 1) :
    (cohomologyRes A N 1).hom ((cohomologyπ A 1).hom y) = (cohomologyπ _ 1).hom
      ((cocyclesMapAlong N.subtype (continuous_subgroup_subtype N) (𝟙 _) 1).hom y) := by
  rw [cohomologyRes, cohomologyMapAlong]
  erw [homologyMap_homologyπ_apply]
  rfl

/- English proof (translation)
The claim follows from `cocycle_one_apply_one A (iCycles_d_apply _ 1 2 y) mul_right g n := by rw [cocycleOneApply_cocyclesMapAlong, cocycleOneApplyG_mul] conj h n := by rw [cocycleOneApply_cocyclesMapAlong, cocycleOneApply_cocyclesMapAlong] have e : h * (GroundTheory.GroupCoh.conjHom N h n : G) = n * h …`.
-/
theorem isTgLift_cocycleOneApplyG (y : cocycles A 1) :
    IsTgLift A N (cocycleOneApply A N ((cocyclesMapAlong N.subtype (continuous_subgroup_subtype N)
      (𝟙 _) 1).hom y)) (cocycleOneApplyG A y) where
  map_one := cocycle_one_apply_one A (iCycles_d_apply _ 1 2 y)
  mul_right g n := by
    rw [cocycleOneApply_cocyclesMapAlong, cocycleOneApplyG_mul]
  conj h n := by
    rw [cocycleOneApply_cocyclesMapAlong, cocycleOneApply_cocyclesMapAlong]
    have e : h * (GroundTheory.GroupCoh.conjHom N h n : G) = n * h := by
      simp only [GroundTheory.GroupCoh.coe_conjHom_apply]; group
    have h1 := cocycleOneApplyG_mul A y h (GroundTheory.GroupCoh.conjHom N h n)
    rw [e, cocycleOneApplyG_mul A y n h] at h1
    rw [show A.ρ h (cocycleOneApplyG A y (GroundTheory.GroupCoh.conjHom N h n)) =
      cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y h) - cocycleOneApplyG A y h by
        rw [h1]; abel]
    abel

/- English proof (translation)
The claim follows from `(((cochainsComplex A).iCycles 1).hom y).2.comp_continuous (continuous_pi fun _ => continuous_id)`.
-/
theorem isLocallyConstant_cocycleOneApplyG (y : cocycles A 1) :
    IsLocallyConstant (cocycleOneApplyG A y) :=
  (((cochainsComplex A).iCycles 1).hom y).2.comp_continuous (continuous_pi fun _ => continuous_id)

/- English proof (translation)
Take `⟨y, rfl⟩` from `homologyπ_surjective (cochainsComplex A) 1 h`. Use `⟨_, _, isTgLift_cocycleOneApplyG A N y, isLocallyConstant_cocycleOneApplyG A y, (cohomologyRes_π A N y).symm, ?_⟩` and prove the remaining obligations. Establish `h0 : cocycleOf 2 (tgCochain (isCocycleOne_cocycleOneApply A N _) (isTgLift_cocycleOneApplyG A N y) (isLocallyConstant_cocycleOneApplyG A y)) (tgCochain_d _ _ _) = 0`. Rewrite using `[cocycleOf_eq_iff, map_zero]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(0 : A) = A.ρ _ (cocycleOneApplyG A y _) - cocycleOneApplyG A y _ + cocycleOneApplyG A y _`. Rewrite using `[cocycleOneApplyG_mul]`. Normalize the expressions using the abelian group laws.

Simplify using `only [tgClass, h0, map_zero]`.
-/
theorem isTransgression_cohomologyRes (h : cohomology A 1) :
    IsTransgression A N ((cohomologyRes A N 1).hom h) 0 := by
  obtain ⟨y, rfl⟩ := homologyπ_surjective (cochainsComplex A) 1 h
  refine ⟨_, _, isTgLift_cocycleOneApplyG A N y, isLocallyConstant_cocycleOneApplyG A y,
    (cohomologyRes_π A N y).symm, ?_⟩
  have h0 : cocycleOf 2 (tgCochain (isCocycleOne_cocycleOneApply A N _)
      (isTgLift_cocycleOneApplyG A N y) (isLocallyConstant_cocycleOneApplyG A y))
      (tgCochain_d _ _ _) = 0 := by
    rw [cocycleOf_eq_iff, map_zero]
    apply Subtype.ext
    funext c
    apply Subtype.ext
    change (0 : A) = A.ρ _ (cocycleOneApplyG A y _) - cocycleOneApplyG A y _ +
      cocycleOneApplyG A y _
    rw [cocycleOneApplyG_mul]
    abel
  simp only [tgClass, h0, map_zero]

end Restriction

section Inflation

variable {A N}

/- English proof (translation)
Simplify using `only [tgClass]`. Rewrite using `[cohomologyInfl, cohomologyMapAlong]`. Use `erw [homologyMap_homologyπ_apply]`. Use `(homologyπ_succ_eq_zero_iff _ 1 _).2 ⟨liftCochain A hyc, ?_⟩` and prove the remaining obligations. Rewrite using `[iCycles_cyclesMap_apply, iCycles_cocycleOf]`.

Conclude with `(cochainsMapAlong_tgCochain _ hy hyc).symm`.
-/
theorem cohomologyInfl_tgClass (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y) :
    (cohomologyInfl A N 2).hom (tgClass z hy hyc) = 0 := by
  simp only [tgClass]
  rw [cohomologyInfl, cohomologyMapAlong]
  erw [homologyMap_homologyπ_apply]
  refine (homologyπ_succ_eq_zero_iff _ 1 _).2 ⟨liftCochain A hyc, ?_⟩
  rw [iCycles_cyclesMap_apply, iCycles_cocycleOf]
  exact (cochainsMapAlong_tgCochain _ hy hyc).symm

end Inflation

section Exactness

variable [CompactSpace G] [TotallyDisconnectedSpace G] (hN : IsClosed (N : Set G))

include hN in

/- English proof (translation)
Take `⟨z, y, hy, hyc, -, ht⟩` from `isTransgression_transgression A N hN h`. Rewrite using `[← ht]`. Conclude with `cohomologyInfl_tgClass z hy hyc`.
-/
theorem cohomologyInfl_transgression (h : cohomologyConjInvariants A N 1) :
    (cohomologyInfl A N 2).hom (transgression A N hN h) = 0 := by
  obtain ⟨z, y, hy, hyc, -, ht⟩ := isTransgression_transgression A N hN h
  rw [← ht]
  exact cohomologyInfl_tgClass z hy hyc

/- English proof (translation)
The claim follows from `(transgression_eq_iff A N hN _ 0).2 (isTransgression_cohomologyRes A N h)`.
-/
theorem transgression_cohomologyResInv (h : cohomology A 1) :
    transgression A N hN (cohomologyResInv A N h) = 0 :=
  (transgression_eq_iff A N hN _ 0).2 (isTransgression_cohomologyRes A N h)

/- English proof (translation)
Take `⟨z, y, hy, hyc, hz, ht⟩` from `(transgression_eq_iff A N hN h 0).1 hh`. Establish `hxc` using `isCocycleOne_cocycleOneApply A N z`. Take `⟨W, hW⟩` from `(homologyπ_succ_eq_zero_iff _ 1 _).1 ht`. Rewrite `hW` using `[iCycles_cocycleOf]`. Set `Wf : G → A` to `fun g => ((W.1 fun _ => (g : G ⧸ N)) : A)`.

Establish `hWf : ∀ g h : G, A.ρ g (Wf h) - Wf (g * h) + Wf g = tgDiff A y g h`. Introduce `g h`. Establish `e` using `congrArg (fun v : locallyConstantCochains (A.quotientToInvariants N) 2 => ((v.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)) hW`. Establish `hd` using `congrArg Subtype.val (cochainsComplex_d_one_apply (A.quotientToInvariants N) W ![(g : G ⧸ N), (h : G ⧸ N)])`. Rewrite using `[← hy.tgDiff_out hxc g h]`.

Conclude with `hd.symm.trans e`. Establish `hW1 : Wf 1 = 0`. Use `hWf 1 1` as an intermediate fact. Simplify using `only [one_mul, map_one, Module.End.one_apply, tgDiff, hy.map_one, sub_self, add_zero] at this`. Simplify using `using this`.

Set `y' : G → A` to `fun g => y g - Wf g`. Establish `hWc : IsLocallyConstant Wf` using `(W.2.comp_continuous (continuous_pi fun _ => QuotientGroup.continuous_mk)).comp Subtype.val`. Establish `hy'c : IsLocallyConstant y'` using `hyc.sub hWc`. Establish `hcoc : ∀ g h : G, tgDiff A y' g h = 0`. Introduce `g h`.

Use `hWf g h` as an intermediate fact. Simplify using `only [tgDiff, y', map_sub] at this ⊢`. Rewrite using `[← sub_eq_zero.mpr this.symm]`. Normalize the expressions using the abelian group laws. Establish `hd' : ((cochainsComplex A).d 1 (1 + 1)).hom (liftCochain A hy'c) = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Conclude with `(cochainsComplex_d_liftCochain A hy'c g).trans (hcoc (g 0) (g 1))`. Use `⟨(cohomologyπ A 1).hom (cocycleOf 1 (liftCochain A hy'c) hd'), Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_cohomologyResInv_apply, cohomologyRes_π, ← hz]`.

Use `congr 1`. Apply `iCycles_injective` to reduce the goal to its premises. Rewrite using `[iCycles_cyclesMap_apply, iCycles_cocycleOf]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Express the relevant statement in the definitionally equal form `y' (g 0 : G) = (((cochainsComplex (Rep.res N.subtype A)).iCycles 1).hom z).1 g`. Rewrite using `[fin_one_eq_const g]`. Express the relevant statement in the definitionally equal form `y (g 0 : G) - Wf (g 0 : G) = cocycleOneApply A N z (g 0)`. Establish `hm : ((g 0 : G) : G ⧸ N) = ((1 : G) : G ⧸ N)`. Rewrite using `[QuotientGroup.mk_one]`.

Conclude with `(QuotientGroup.eq_one_iff _).2 (g 0).2`. Establish `hWn : Wf (g 0 : G) = Wf 1`. Express the relevant statement in the definitionally equal form `((W.1 fun _ => ((g 0 : G) : G ⧸ N)) : A) = ((W.1 fun _ => ((1 : G) : G ⧸ N)) : A)`. Rewrite using `[hm]`. Rewrite using `[hWn, hW1, sub_zero, show ((g 0 : N) : G) = 1 * (g 0 : G) from (one_mul _).symm, hy.mul_right, hy.map_one, zero_add, map_one, Module.End.one_apply]`.
-/
theorem exists_cohomologyResInv_eq (h : cohomologyConjInvariants A N 1)
    (hh : transgression A N hN h = 0) : ∃ g, cohomologyResInv A N g = h := by
  obtain ⟨z, y, hy, hyc, hz, ht⟩ := (transgression_eq_iff A N hN h 0).1 hh
  have hxc := isCocycleOne_cocycleOneApply A N z
  obtain ⟨W, hW⟩ := (homologyπ_succ_eq_zero_iff _ 1 _).1 ht
  rw [iCycles_cocycleOf] at hW
  let Wf : G → A := fun g => ((W.1 fun _ => (g : G ⧸ N)) : A)
  have hWf : ∀ g h : G, A.ρ g (Wf h) - Wf (g * h) + Wf g = tgDiff A y g h := by
    intro g h
    have e := congrArg (fun v : locallyConstantCochains (A.quotientToInvariants N) 2 =>
      ((v.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)) hW
    have hd := congrArg Subtype.val
      (cochainsComplex_d_one_apply (A.quotientToInvariants N) W ![(g : G ⧸ N), (h : G ⧸ N)])
    rw [← hy.tgDiff_out hxc g h]
    exact hd.symm.trans e
  have hW1 : Wf 1 = 0 := by
    have := hWf 1 1
    simp only [one_mul, map_one, Module.End.one_apply, tgDiff, hy.map_one, sub_self,
      add_zero] at this
    simpa using this
  let y' : G → A := fun g => y g - Wf g
  have hWc : IsLocallyConstant Wf :=
    (W.2.comp_continuous (continuous_pi fun _ => QuotientGroup.continuous_mk)).comp Subtype.val
  have hy'c : IsLocallyConstant y' := hyc.sub hWc
  have hcoc : ∀ g h : G, tgDiff A y' g h = 0 := by
    intro g h
    have := hWf g h
    simp only [tgDiff, y', map_sub] at this ⊢
    rw [← sub_eq_zero.mpr this.symm]
    abel
  have hd' : ((cochainsComplex A).d 1 (1 + 1)).hom (liftCochain A hy'c) = 0 := by
    apply Subtype.ext
    funext g
    exact (cochainsComplex_d_liftCochain A hy'c g).trans (hcoc (g 0) (g 1))
  refine ⟨(cohomologyπ A 1).hom (cocycleOf 1 (liftCochain A hy'c) hd'), Subtype.ext ?_⟩
  rw [coe_cohomologyResInv_apply, cohomologyRes_π, ← hz]
  congr 1
  apply iCycles_injective
  rw [iCycles_cyclesMap_apply, iCycles_cocycleOf]
  apply Subtype.ext
  funext g
  change y' (g 0 : G) = (((cochainsComplex (Rep.res N.subtype A)).iCycles 1).hom z).1 g
  rw [fin_one_eq_const g]
  change y (g 0 : G) - Wf (g 0 : G) = cocycleOneApply A N z (g 0)
  have hm : ((g 0 : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).2 (g 0).2
  have hWn : Wf (g 0 : G) = Wf 1 := by
    change ((W.1 fun _ => ((g 0 : G) : G ⧸ N)) : A) = ((W.1 fun _ => ((1 : G) : G ⧸ N)) : A)
    rw [hm]
  rw [hWn, hW1, sub_zero, show ((g 0 : N) : G) = 1 * (g 0 : G) from (one_mul _).symm,
    hy.mul_right, hy.map_one, zero_add, map_one, Module.End.one_apply]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem comp_vecCons_mk (g h : G) :
    (⇑(QuotientGroup.mk' N) ∘ ![g, h]) = ![(g : G ⧸ N), (h : G ⧸ N)] := by
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Take `⟨ζ, rfl⟩` from `homologyπ_surjective (cochainsComplex (A.quotientToInvariants N)) 2 t`. Rewrite `ht` using `[cohomologyInfl, cohomologyMapAlong]`. Use `erw [homologyMap_homologyπ_apply] at ht`. Take `⟨y₀, hy₀⟩` from `(homologyπ_succ_eq_zero_iff _ 1 _).1 ht`. Rewrite `hy₀` using `[iCycles_cyclesMap_apply]`.

Use `set Zf : locallyConstantCochains (A.quotientToInvariants N) 2 := ((cochainsComplex (A.quotientToInvariants N)).iCycles 2).hom ζ with hZf`. Set `ZA : G → G → A` to `fun g h => ((Zf.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)`. Set `Y₀ : G → A` to `fun g => y₀.1 fun _ => g`. Establish `hY₀ : ∀ g h, tgDiff A Y₀ g h = ZA g h`. Introduce `g h`.

Establish `e` using `congrArg (fun v : locallyConstantCochains A 2 => v.1 ![g, h]) hy₀`. Establish `hd` using `cochainsComplex_d_one_apply A y₀ ![g, h]`. Use `hd.symm.trans (e.trans ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((Zf.1 (⇑(QuotientGroup.mk' N) ∘ ![g, h])) : Representation.invariants (A.ρ.comp N.subtype)) : A) = _`. Rewrite using `[comp_vecCons_mk]`.

Use `set c : A := Y₀ 1 with hcdef`. Establish `hc : c ∈ Representation.invariants (A.ρ.comp N.subtype)`. Use `hY₀ 1 1` as an intermediate fact. Simplify using `only [tgDiff, one_mul, map_one, Module.End.one_apply, sub_self, zero_add] at this`. Rewrite using `[hcdef, this]`.

Conclude with `(Zf.1 _).2`. Set `Y : G → A` to `fun g => Y₀ g - c`. Establish `hYdiff : ∀ g h, tgDiff A Y g h = ZA g h - A.ρ g c`. Introduce `g h`. Rewrite using `[← hY₀]`.

Simplify using `only [tgDiff, Y, map_sub]`. Normalize the expressions using the abelian group laws. Establish `hZA : ∀ g g' h h' : G, (g : G ⧸ N) = g' → (h : G ⧸ N) = h' → ZA g h = ZA g' h'`. Introduce `g g' h h' e1 e2`. Simplify using `only [ZA, e1, e2]`.

Establish `hρc : ∀ (g : G) (n : N), A.ρ (g * n) c = A.ρ g c`. Introduce `g n`. Rewrite using `[map_mul, Module.End.mul_apply]`. Conclude with `congrArg (A.ρ g) (hc n)`. Establish `hY1 : Y 1 = 0` using `sub_self _`.

Establish `hmk : ∀ n : N, ((n : G) : G ⧸ N) = ((1 : G) : G ⧸ N)` using `fun n => by`. Rewrite using `[QuotientGroup.mk_one]`. Conclude with `(QuotientGroup.eq_one_iff _).2 n.2`. Establish `hR : ∀ (g : G) (n : N), tgDiff A Y g n = 0`. Introduce `g n`.

Rewrite using `[hYdiff, hZA g g n 1 rfl (hmk n), ← hYdiff]`. Simplify using `[tgDiff, hY1]`. Establish `hL : ∀ (n : N) (h : G), tgDiff A Y n h = 0`. Introduce `n h`. Rewrite using `[hYdiff, hZA n 1 h h (hmk n) rfl, show A.ρ (n : G) c = A.ρ 1 c by`.

Rewrite using `[map_one]`. Conclude with `hc n, ← hYdiff]`. Simplify using `[tgDiff, hY1]`. Establish `hmr : ∀ (g : G) (n : N), Y (g * n) = Y g + A.ρ g (Y n)`. Introduce `g n`.

Use `hR g n` as an intermediate fact. Simplify using `only [tgDiff] at this`. Rewrite using `[← sub_eq_zero, ← neg_eq_zero, ← this]`. Normalize the expressions using the abelian group laws. Establish `hYc : IsLocallyConstant Y` using `(y₀.2.comp_continuous (continuous_pi fun _ => continuous_id)).sub (IsLocallyConstant.const c)`.

Set `zc : locallyConstantCochains (Rep.res N.subtype A) 1` to `⟨fun g => Y (g 0 : G), hYc.comp_continuous (continuous_subtype_val.comp (continuous_apply 0))⟩`. Establish `hzc : ((cochainsComplex (Rep.res N.subtype A)).d 1 (1 + 1)).hom zc = 0` using `(cochainsComplex_d_one_eq_zero_iff (Rep.res N.subtype A) zc).2 fun a b => hmr a b`. Use `set z := cocycleOf 1 zc hzc with hzdef`. Establish `hX : cocycleOneApply A N z = fun n : N => Y n`. Use function extensionality and compare the values at `n`.

Simplify using `only [cocycleOneApply, hzdef, iCycles_cocycleOf]`. Both sides reduce to the same expression. Establish `hlift : IsTgLift A N (cocycleOneApply A N z) Y`. Rewrite using `[hX]`. Use `⟨hY1, hmr, fun h n => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hL n h`. Establish `e : (n : G) * h = h * (GroundTheory.GroupCoh.conjHom N h n : G)`. Simplify using `only [GroundTheory.GroupCoh.coe_conjHom_apply]`. Use `group`. Simplify using `only [tgDiff] at h1`.

Rewrite `h1` using `[e, hmr]`. Rewrite using `[← sub_eq_zero, ← neg_eq_zero, ← h1]`. Normalize the expressions using the abelian group laws. Establish `hinv : (cohomologyπ _ 1).hom z ∈ cohomologyConjInvariants A N 1` using `fun g => (cohomologyConj_π_eq_iff A N z g).2 ⟨Y g, hlift.conj g⟩`. Use `⟨⟨_, hinv⟩, (transgression_eq_iff A N hN _ _).2 ⟨z, Y, hlift, hYc, rfl, ?_⟩⟩` and prove the remaining obligations.

Set `w : locallyConstantCochains (A.quotientToInvariants N) 1` to `⟨fun _ => ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩, IsLocallyConstant.const _⟩`. Establish `hw : ((cochainsComplex (A.quotientToInvariants N)).d 1 (1 + 1)).hom w = tgCochain (isCocycleOne_cocycleOneApply A N z) hlift hYc - Zf`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `cc`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hd` using `congrArg Subtype.val (cochainsComplex_d_one_apply (A.quotientToInvariants N) w cc)`. Use `hd.trans ?_` and prove the remaining obligations. Establish `hq` using `quotientToInvariants_ρ_apply_coe (A := A) (N := N) (cc 0) ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩`. Simplify using `only [Submodule.coe_add, Submodule.coe_sub]`. Express the relevant statement in the definitionally equal form `_ - (-c) + (-c) = tgDiff A Y (cc 0).out (cc 1).out - ((Zf.1 cc : _) : A)`.

Rewrite using `[hq, hYdiff]`. Establish `ecc : ![((cc 0).out : G ⧸ N), ((cc 1).out : G ⧸ N)] = cc`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> exact QuotientGroup.out_eq' _`. Simplify using `only [ZA, ecc, map_neg]`.

Normalize the expressions using the abelian group laws. Establish `e` using `cohomologyπ_cocycleOf_eq 1 Zf _ (iCycles_d_apply _ 2 3 ζ) (tgCochain_d _ hlift hYc) w hw`. Use `e.trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[cocycleOf_eq_iff]`.
-/
theorem exists_transgression_eq (t : cohomology (A.quotientToInvariants N) 2)
    (ht : (cohomologyInfl A N 2).hom t = 0) : ∃ h, transgression A N hN h = t := by
  obtain ⟨ζ, rfl⟩ := homologyπ_surjective (cochainsComplex (A.quotientToInvariants N)) 2 t
  rw [cohomologyInfl, cohomologyMapAlong] at ht
  erw [homologyMap_homologyπ_apply] at ht
  obtain ⟨y₀, hy₀⟩ := (homologyπ_succ_eq_zero_iff _ 1 _).1 ht
  rw [iCycles_cyclesMap_apply] at hy₀
  set Zf : locallyConstantCochains (A.quotientToInvariants N) 2 :=
    ((cochainsComplex (A.quotientToInvariants N)).iCycles 2).hom ζ with hZf
  let ZA : G → G → A := fun g h =>
    ((Zf.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)
  let Y₀ : G → A := fun g => y₀.1 fun _ => g
  have hY₀ : ∀ g h, tgDiff A Y₀ g h = ZA g h := by
    intro g h
    have e := congrArg (fun v : locallyConstantCochains A 2 => v.1 ![g, h]) hy₀
    have hd := cochainsComplex_d_one_apply A y₀ ![g, h]
    refine hd.symm.trans (e.trans ?_)
    change (((Zf.1 (⇑(QuotientGroup.mk' N) ∘ ![g, h])) :
      Representation.invariants (A.ρ.comp N.subtype)) : A) = _
    rw [comp_vecCons_mk]
  set c : A := Y₀ 1 with hcdef
  have hc : c ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    have := hY₀ 1 1
    simp only [tgDiff, one_mul, map_one, Module.End.one_apply, sub_self, zero_add] at this
    rw [hcdef, this]
    exact (Zf.1 _).2
  let Y : G → A := fun g => Y₀ g - c
  have hYdiff : ∀ g h, tgDiff A Y g h = ZA g h - A.ρ g c := by
    intro g h
    rw [← hY₀]
    simp only [tgDiff, Y, map_sub]
    abel
  have hZA : ∀ g g' h h' : G, (g : G ⧸ N) = g' → (h : G ⧸ N) = h' → ZA g h = ZA g' h' := by
    intro g g' h h' e1 e2
    simp only [ZA, e1, e2]
  have hρc : ∀ (g : G) (n : N), A.ρ (g * n) c = A.ρ g c := by
    intro g n
    rw [map_mul, Module.End.mul_apply]
    exact congrArg (A.ρ g) (hc n)
  have hY1 : Y 1 = 0 := sub_self _
  have hmk : ∀ n : N, ((n : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := fun n => by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).2 n.2
  have hR : ∀ (g : G) (n : N), tgDiff A Y g n = 0 := by
    intro g n
    rw [hYdiff, hZA g g n 1 rfl (hmk n), ← hYdiff]
    simp [tgDiff, hY1]
  have hL : ∀ (n : N) (h : G), tgDiff A Y n h = 0 := by
    intro n h
    rw [hYdiff, hZA n 1 h h (hmk n) rfl, show A.ρ (n : G) c = A.ρ 1 c by
      rw [map_one]; exact hc n, ← hYdiff]
    simp [tgDiff, hY1]
  have hmr : ∀ (g : G) (n : N), Y (g * n) = Y g + A.ρ g (Y n) := by
    intro g n
    have := hR g n
    simp only [tgDiff] at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  have hYc : IsLocallyConstant Y :=
    (y₀.2.comp_continuous (continuous_pi fun _ => continuous_id)).sub (IsLocallyConstant.const c)

  let zc : locallyConstantCochains (Rep.res N.subtype A) 1 :=
    ⟨fun g => Y (g 0 : G), hYc.comp_continuous (continuous_subtype_val.comp (continuous_apply 0))⟩
  have hzc : ((cochainsComplex (Rep.res N.subtype A)).d 1 (1 + 1)).hom zc = 0 :=
    (cochainsComplex_d_one_eq_zero_iff (Rep.res N.subtype A) zc).2 fun a b => hmr a b
  set z := cocycleOf 1 zc hzc with hzdef
  have hX : cocycleOneApply A N z = fun n : N => Y n := by
    funext n
    simp only [cocycleOneApply, hzdef, iCycles_cocycleOf]
    rfl
  have hlift : IsTgLift A N (cocycleOneApply A N z) Y := by
    rw [hX]
    refine ⟨hY1, hmr, fun h n => ?_⟩
    have h1 := hL n h
    have e : (n : G) * h = h * (GroundTheory.GroupCoh.conjHom N h n : G) := by
      simp only [GroundTheory.GroupCoh.coe_conjHom_apply]; group
    simp only [tgDiff] at h1
    rw [e, hmr] at h1
    rw [← sub_eq_zero, ← neg_eq_zero, ← h1]
    abel
  have hinv : (cohomologyπ _ 1).hom z ∈ cohomologyConjInvariants A N 1 := fun g =>
    (cohomologyConj_π_eq_iff A N z g).2 ⟨Y g, hlift.conj g⟩
  refine ⟨⟨_, hinv⟩, (transgression_eq_iff A N hN _ _).2 ⟨z, Y, hlift, hYc, rfl, ?_⟩⟩

  let w : locallyConstantCochains (A.quotientToInvariants N) 1 :=
    ⟨fun _ => ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩,
      IsLocallyConstant.const _⟩
  have hw : ((cochainsComplex (A.quotientToInvariants N)).d 1 (1 + 1)).hom w =
      tgCochain (isCocycleOne_cocycleOneApply A N z) hlift hYc - Zf := by
    apply Subtype.ext
    funext cc
    apply Subtype.ext
    have hd := congrArg Subtype.val (cochainsComplex_d_one_apply (A.quotientToInvariants N) w cc)
    refine hd.trans ?_
    have hq := quotientToInvariants_ρ_apply_coe (A := A) (N := N) (cc 0)
      ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩
    simp only [Submodule.coe_add, Submodule.coe_sub]
    change _ - (-c) + (-c) = tgDiff A Y (cc 0).out (cc 1).out - ((Zf.1 cc : _) : A)
    rw [hq, hYdiff]
    have ecc : ![((cc 0).out : G ⧸ N), ((cc 1).out : G ⧸ N)] = cc := by
      funext i
      fin_cases i <;> exact QuotientGroup.out_eq' _
    simp only [ZA, ecc, map_neg]
    abel
  have e := cohomologyπ_cocycleOf_eq 1 Zf _ (iCycles_d_apply _ 2 3 ζ) (tgCochain_d _ hlift hYc) w hw
  refine e.trans ?_
  congr 1
  rw [cocycleOf_eq_iff]

end Exactness

end GroundTheory.ProfCoh
