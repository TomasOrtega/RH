import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LatLevEq

/- English proof (translation)
Introduce `i j`. Establish `hw : ∀ k, ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) k ∈ S`. Introduce `k`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Distinguish the cases in `h : k = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Use `hX _ hw i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`.

Conclude with `this`.
-/
theorem conj_apply_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β : GL (Fin n) B)
    (X : Matrix (Fin n) (Fin n) B)
    (hX : ∀ w : Fin n → B, (∀ i, ((β⁻¹).val *ᵥ w) i ∈ S) → ∀ i, ((β⁻¹).val *ᵥ (X *ᵥ w)) i ∈ S) :
    ∀ i j, ((β⁻¹).val * X * β.val) i j ∈ S := by
  intro i j
  have hw : ∀ k, ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) k ∈ S := by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := hX _ hw i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  exact this

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) S` to `Matrix.of fun i j => ⟨_, h1 i j⟩`. Set `M' : Matrix (Fin n) (Fin n) S` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Establish `hM : M.map S.subtype = (β⁻¹).val * x.val * β.val` using `by ext i j; rfl`. Establish `hM' : M'.map S.subtype = (β⁻¹).val * (x⁻¹).val * β.val` using `by ext i j; rfl`. Establish `key : ∀ (P Q : Matrix (Fin n) (Fin n) S), P.map S.subtype * Q.map S.subtype = 1 → P * Q = 1`.

Introduce `P Q h`. Apply `Matrix.map_injective Subtype.val_injective` to reduce the goal to its premises. Establish `e` using `Matrix.map_mul (f := S.subtype) (L := P) (M := Q)`. Establish `e1` using `Matrix.map_one S.subtype (map_zero _) (map_one _) (n := Fin n)`. Conclude with `e.trans (h.trans e1.symm)`.

Establish `hu : ∀ a b : GL (Fin n) B, a * b = 1 → ((β⁻¹).val * a.val * β.val) * ((β⁻¹).val * b.val * β.val) = 1`. Introduce `a b hab`. Establish `: β⁻¹ * a * β * (β⁻¹ * b * β) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify `congrArg Units.val this` using `only [Units.val_mul, Units.val_one]`.

Use `⟨⟨M, M', key M M' ?_, key M' M ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hM, hM']`. Conclude with `hu x x⁻¹ (mul_inv_cancel x)`. Rewrite using `[hM, hM']`. Conclude with `hu x⁻¹ x (inv_mul_cancel x)`.

Use `show β.val * M.map S.subtype * (β⁻¹).val = x.val`. Rewrite using `[hM]`. Establish `: β * (β⁻¹ * x * β) * β⁻¹ = x` using `by group`. Simplify `congrArg Units.val this` using `only [Units.val_mul]`.
-/
theorem exists_integral_conj {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β x : GL (Fin n) B)
    (h1 : ∀ i j, ((β⁻¹).val * x.val * β.val) i j ∈ S) (h2 : ∀ i j, ((β⁻¹).val * (x⁻¹).val * β.val) i j ∈ S) :
    ∃ y : GL (Fin n) S, β.val * y.val.map S.subtype * (β⁻¹).val = x.val := by
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (β⁻¹).val * x.val * β.val := by ext i j; rfl
  have hM' : M'.map S.subtype = (β⁻¹).val * (x⁻¹).val * β.val := by ext i j; rfl
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) S), P.map S.subtype * Q.map S.subtype = 1 → P * Q = 1 := by
    intro P Q h
    apply Matrix.map_injective Subtype.val_injective
    have e := Matrix.map_mul (f := S.subtype) (L := P) (M := Q)
    have e1 := Matrix.map_one S.subtype (map_zero _) (map_one _) (n := Fin n)
    exact e.trans (h.trans e1.symm)
  have hu : ∀ a b : GL (Fin n) B, a * b = 1 → ((β⁻¹).val * a.val * β.val) * ((β⁻¹).val * b.val * β.val) = 1 := by
    intro a b hab
    have : β⁻¹ * a * β * (β⁻¹ * b * β) = 1 := by
      calc β⁻¹ * a * β * (β⁻¹ * b * β) = β⁻¹ * (a * b) * β := by group
        _ = 1 := by rw [hab]; group
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val this
  refine ⟨⟨M, M', key M M' ?_, key M' M ?_⟩, ?_⟩
  · rw [hM, hM']; exact hu x x⁻¹ (mul_inv_cancel x)
  · rw [hM, hM']; exact hu x⁻¹ x (inv_mul_cancel x)
  · show β.val * M.map S.subtype * (β⁻¹).val = x.val
    rw [hM]
    have : β * (β⁻¹ * x * β) * β⁻¹ = x := by group
    simpa only [Units.val_mul] using congrArg Units.val this

end GlobalTheory.LatLevEq

namespace GlobalTheory.LatLevEq

/- English proof (translation)
Introduce `D V β Λ hβ`. Establish `hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1` using `⟨0, by rwa [pow_zero]⟩`. Establish `hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D`. Introduce `z`. Rewrite using `[← GlobalTheory.StdFrameCong.pj_latHat_eq]`.

Conclude with `GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨u, hu, rfl⟩` from `Subgroup.mem_map.1 hx`. Take `⟨g, hg, rfl⟩` from `Subgroup.mem_map.1 hu`.

Use `⟨(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).2, ?_⟩` and prove the remaining obligations. Use `set x : GL (Fin V.rank) (Lev.EAf D) := ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) with hxdef`. Establish `hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val`. Establish `h1` using `congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)`. Conclude with `h1.symm`.

Establish `hst` using `(GlobalTheory.Mass.Levels.mem_latStab V g).1 hg`. Establish `tr : ∀ w : Fin V.rank → Lev.EAf D, (fun i => GlobalTheory.LevelActionPinned.sw D (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ fun i => (GlobalTheory.LevelActionPinned.sw D).symm (w i)) i)) = x.val *ᵥ w`. Introduce `w`. Rewrite using `[GlobalTheory.LevelActionPinned.equiv_mulVec, hmat]`. Simplify using `only [RingEquiv.apply_symm_apply]`.

Establish `hz : ∀ w : Fin V.rank → Lev.EAf D, (fun i => GlobalTheory.LevelActionPinned.sw D ((GlobalTheory.LevelActionPinned.sw D).symm (w i))) = w`. Introduce `w`. Use function extensionality and compare the values at `i`. Simplify using `only [RingEquiv.apply_symm_apply]`. Establish `h1` using `conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β x.val fun w hw => by`.

Establish `hzm` using `(hP _).2 (by rw [hz]; exact hw)`. Use `(hP _).1 ((hst _).1 hzm)` as an intermediate fact. Rewrite `this` using `[tr]`. Then use the resulting hypothesis. Establish `h2` using `conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β (x⁻¹).val fun w hw => by`. Establish `hw' : ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ fun i => (GlobalTheory.LevelActionPinned.sw D).symm (((x⁻¹).val *ᵥ w) i)) i)) i ∈ GlobalTheory.LevelA …`.

Rewrite using `[tr, show x.val *ᵥ ((x⁻¹).val *ᵥ w) = w by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]]`. Conclude with `hw`. Use `(hP _).1 ((hst _).2 ((hP _).2 hw'))` as an intermediate fact. Rewrite `this` using `[hz]`. Then use the resulting hypothesis.

Take `⟨y, hy⟩` from `exists_integral_conj (GlobalTheory.LevelActionPinned.SI D) β x h1 h2`. Conclude with `⟨y, Units.ext hy⟩`. Introduce and unpack `x ⟨hUA, hSt⟩`. Take `⟨t', ht'⟩` from `(Formalism.L2.DIV.St β).inv_mem hSt`. Take `⟨t, ht⟩` from `hSt`.

Set `u : UA D.sp.cm V.gram` to `⟨x, hUA⟩`. Set `g` to `(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u`. Establish `hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x`. Simplify using `only [g, MulEquiv.apply_symm_apply, u]`. Establish `hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val`.

Establish `h1` using `congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)`. Rewrite using `[← hg]`. Conclude with `h1.symm`. Use `⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩` and prove the remaining obligations. Use `(GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val (by rw [hmat, ← ht]; rfl) y hy`. Introduce `hy`. Set `m'` to `(x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm`.

Establish `hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val`. Use extensionality with `i j`. Simplify using `only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]`. Establish `hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1`. Apply `Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective` to reduce the goal to its premises.

Establish `e` using `Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m') (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)`. Establish `e1` using `Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)`. Use `(e.trans ?_).trans e1.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1`. Rewrite using `[hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `h2` using `GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val (by rw [hm', ← ht']; rfl) _ hy`. Rewrite `h2` using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem latLev_eq_UA_inf_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → GlobalTheory.Mass.Levels.latLev V = Formalism.L2.DIV.UA D.sp.cm V.gram ⊓ Formalism.L2.DIV.St β := by
  intro D V β Λ hβ
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hu
    refine ⟨(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).2, ?_⟩
    set x : GL (Fin V.rank) (Lev.EAf D) :=
      ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) :
        GL (Fin V.rank) (Lev.EAf D)) with hxdef
    have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
      have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
      exact h1.symm
    have hst := (GlobalTheory.Mass.Levels.mem_latStab V g).1 hg
    have tr : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (w i)) i)) = x.val *ᵥ w := by
      intro w
      rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hmat]
      simp only [RingEquiv.apply_symm_apply]
    have hz : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D ((GlobalTheory.LevelActionPinned.sw D).symm (w i))) = w := by
      intro w; funext i; simp only [RingEquiv.apply_symm_apply]
    have h1 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β x.val fun w hw => by
      have hzm := (hP _).2 (by rw [hz]; exact hw)
      have := (hP _).1 ((hst _).1 hzm)
      rwa [tr] at this
    have h2 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β (x⁻¹).val fun w hw => by
      have hw' : ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (((x⁻¹).val *ᵥ w) i)) i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
        rw [tr, show x.val *ᵥ ((x⁻¹).val *ᵥ w) = w by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]]
        exact hw
      have := (hP _).1 ((hst _).2 ((hP _).2 hw'))
      rwa [hz] at this
    obtain ⟨y, hy⟩ := exists_integral_conj (GlobalTheory.LevelActionPinned.SI D) β x h1 h2
    exact ⟨y, Units.ext hy⟩
  · rintro x ⟨hUA, hSt⟩
    obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
    obtain ⟨t, ht⟩ := hSt
    let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
    let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
    have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
      simp only [g, MulEquiv.apply_symm_apply, u]
    have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
      have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
      rw [← hg]
      exact h1.symm
    refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
    refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
    constructor
    · intro hy
      exact GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
        (by rw [hmat, ← ht]; rfl) y hy
    · intro hy
      let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
      have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
        ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
      have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
        apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
        have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
          (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
        have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
        refine (e.trans ?_).trans e1.symm
        change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
        rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 := GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
        (by rw [hm', ← ht']; rfl) _ hy
      rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LatLevEq
