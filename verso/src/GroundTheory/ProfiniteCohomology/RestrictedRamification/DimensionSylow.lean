import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.NotDvdSuperIndexBotOfIsProPGroup
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.CdpOpenSubgroupLe
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/- English proof (translation)
Establish `hx : e x = x.val • e 1`. Rewrite using `[← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]`. Rewrite using `[hx, map_nsmul, ← e.apply_symm_apply (f (e 1)), ← map_nsmul, e.symm_apply_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]`.
-/
theorem addMonoidHom_apply_zmod_addEquiv {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A] (e : ZMod ℓ ≃+ A)
    (f : A →+ A) (x : ZMod ℓ) : f (e x) = e (x * e.symm (f (e 1))) := by
  have hx : e x = x.val • e 1 := by
    rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [hx, map_nsmul, ← e.apply_symm_apply (f (e 1)), ← map_nsmul, e.symm_apply_apply, nsmul_eq_mul,
    ZMod.natCast_zmod_val]

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Establish `: NeZero ℓ` using `⟨hℓ.ne_zero⟩`. Set `f : G → A →+ A` to `fun τ => (A.ρ τ).toAddMonoidHom`. Set `c : G → ZMod ℓ` to `fun τ => e.symm (A.ρ τ (e 1))`. Establish `hmul : ∀ (τ : G) (x : ZMod ℓ), A.ρ τ (e x) = e (x * c τ)` using `fun τ x => addMonoidHom_apply_zmod_addEquiv e (f τ) x`.

Establish `hpow : ∀ (j : ℕ) (x : ZMod ℓ), A.ρ (σ ^ j) (e x) = e (x * c σ ^ j)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ j ih`. Introduce `x`. Rewrite using `[pow_succ, map_mul, Module.End.mul_apply, hmul, ih, pow_succ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_stabilizer A (e 1)) (show (1 : G) ∈ (stabilizer A.ρ (e 1) : Set G) from (stabilizer A.ρ (e 1)).one_mem)`. Take `⟨k, hk⟩` from `isProPGroup_subgroup_iff.1 hP U σ hσ`. Establish `hfix : A.ρ (σ ^ ℓ ^ k) (e 1) = e 1`. Conclude with `(mem_stabilizer A.ρ (e 1) _).1 (hU hk)`. Establish `hc : c σ = 1`.

Rewrite `hfix` using `[hpow, one_mul]`. Establish `h1` using `e.injective hfix`. Rewrite `h1` using `[ZMod.pow_card_pow]`. Then use the resulting hypothesis. Rewrite using `[← e.apply_symm_apply a, hmul, hc, mul_one]`.
-/
theorem rho_eq_self_of_isProPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (e : ZMod ℓ ≃+ A) {P : Subgroup G} (hP : IsProPGroup ℓ P) {σ : G} (hσ : σ ∈ P)
    (a : A) : A.ρ σ a = a := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let f : G → A →+ A := fun τ => (A.ρ τ).toAddMonoidHom
  let c : G → ZMod ℓ := fun τ => e.symm (A.ρ τ (e 1))
  have hmul : ∀ (τ : G) (x : ZMod ℓ), A.ρ τ (e x) = e (x * c τ) := fun τ x =>
    addMonoidHom_apply_zmod_addEquiv e (f τ) x
  have hpow : ∀ (j : ℕ) (x : ZMod ℓ), A.ρ (σ ^ j) (e x) = e (x * c σ ^ j) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, map_mul, Module.End.mul_apply, hmul, ih, pow_succ]
      congr 1
      ring
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_stabilizer A (e 1))
    (show (1 : G) ∈ (stabilizer A.ρ (e 1) : Set G) from (stabilizer A.ρ (e 1)).one_mem)
  obtain ⟨k, hk⟩ := isProPGroup_subgroup_iff.1 hP U σ hσ
  have hfix : A.ρ (σ ^ ℓ ^ k) (e 1) = e 1 := by
    exact (mem_stabilizer A.ρ (e 1) _).1 (hU hk)
  have hc : c σ = 1 := by
    rw [hpow, one_mul] at hfix
    have h1 := e.injective hfix
    rwa [ZMod.pow_card_pow] at h1
  rw [← e.apply_symm_apply a, hmul, hc, mul_one]

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Take `⟨P, hP⟩` from `exists_isProSylow (G := G) (p := ℓ)`. Establish `: CompactSpace P` using `isCompact_iff_compactSpace.1 hP.1.isCompact`. Rewrite using `[← cdp_eq_of_isProSylow hℓ hP]`. Rewrite using `[cdp_le_iff_of_isProPGroup hℓ hP.2.1 n]`.

Establish `hA : Subsingleton (cohomology (Rep.res P.subtype A) (n + 1))`. It suffices to establish `h' : ∀ x : cohomology (Rep.res P.subtype A) (n + 1), x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩`. Introduce `x`. Take `⟨U, hU, hPU, y, rfl⟩` from `exists_cohomologyResLE_eq A hP.1 (n + 1) x`. Use `h ⟨U, hU⟩` as an intermediate fact.

Rewrite using `[Subsingleton.elim y 0, map_zero]`. Establish `hfix : ∀ (σ : P) (a : A), (Rep.res P.subtype A).ρ σ a = a` using `fun σ a => rho_eq_self_of_isProPGroup hℓ A e hP.2.1 σ.2 a`. Set `ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶ Rep.res P.subtype A` to `Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom), fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩`. Set `ψ' : Rep.res P.subtype A ⟶ Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ))` to `Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom), fun σ => LinearMap.ext fun x => by`. Express the relevant statement in the definitionally equal form `ULift.up (e.symm ((Rep.res P.subtype A).ρ σ x)) = ULift.up (e.symm x)`.

Rewrite using `[hfix]⟩`. Establish `hcomp : ψ ≫ ψ' = 𝟙 _`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `e.symm (e x.down) = x.down`. Conclude with `e.symm_apply_apply x.down`.

Establish `hinj : Function.Injective (cohomologyMap ψ (n + 1)).hom` using `fun x y hxy => by`. Establish `h'` using `congrArg (cohomologyMap ψ' (n + 1)).hom hxy`. Rewrite `h'` using `[← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp, cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply]`. Then use the resulting hypothesis. Conclude with `hinj.subsingleton`.
-/
theorem cdp_le_of_forall_openSubgroup {ℓ : ℕ} (hℓ : ℓ.Prime) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (e : ZMod ℓ ≃+ A) (n : ℕ)
    (h : ∀ U : OpenSubgroup G, Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype A) (n + 1))) :
    cdp ℓ G ≤ n := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := G) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cdp_eq_of_isProSylow hℓ hP]
  rw [cdp_le_iff_of_isProPGroup hℓ hP.2.1 n]
  have hA : Subsingleton (cohomology (Rep.res P.subtype A) (n + 1)) := by
    suffices h' : ∀ x : cohomology (Rep.res P.subtype A) (n + 1), x = 0 from
      ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ := exists_cohomologyResLE_eq A hP.1 (n + 1) x
    have := h ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]
  have hfix : ∀ (σ : P) (a : A), (Rep.res P.subtype A).ρ σ a = a := fun σ a =>
    rho_eq_self_of_isProPGroup hℓ A e hP.2.1 σ.2 a
  let ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶ Rep.res P.subtype A :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype A ⟶ Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype A).ρ σ x)) = ULift.up (e.symm x)
        rw [hfix]⟩
  have hcomp : ψ ≫ ψ' = 𝟙 _ := by
    ext x
    change e.symm (e x.down) = x.down
    exact e.symm_apply_apply x.down
  have hinj : Function.Injective (cohomologyMap ψ (n + 1)).hom := fun x y hxy => by
    have h' := congrArg (cohomologyMap ψ' (n + 1)).hom hxy
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp,
      cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply] at h'
  exact hinj.subsingleton

end GroundTheory.ProfCoh
