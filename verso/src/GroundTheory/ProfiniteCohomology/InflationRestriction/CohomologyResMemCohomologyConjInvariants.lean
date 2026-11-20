import Mathlib
import GroundTheory.TateCohomology.ConjAction
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Formulas

variable (A : Rep.{u} k G) [IsDiscreteRep A]

/- English proof (translation)
Rewrite using `[cochainsComplex_d_zero_one]`. Express the relevant statement in the definitionally equal form `(inhomogeneousCochains.d A 0).hom a.1 g = _`. Rewrite using `[inhomogeneousCochains.d_hom_apply]`. Rewrite using `[Fin.sum_univ_one, Subsingleton.elim (fun i : Fin 0 => g i.succ) Fin.elim0, Subsingleton.elim (Fin.contractNth 0 (fun x1 x2 => x1 * x2) g) Fin.elim0]`. Simplify using `[sub_eq_add_neg]`.
-/
theorem cochainsComplex_d_zero_apply (a : locallyConstantCochains A 0) (g : Fin 1 → G) :
    (((cochainsComplex A).d 0 1).hom a).1 g =
      A.ρ (g 0) (a.1 Fin.elim0) - a.1 Fin.elim0 := by
  rw [cochainsComplex_d_zero_one]
  change (inhomogeneousCochains.d A 0).hom a.1 g = _
  rw [inhomogeneousCochains.d_hom_apply]
  rw [Fin.sum_univ_one, Subsingleton.elim (fun i : Fin 0 => g i.succ) Fin.elim0,
    Subsingleton.elim (Fin.contractNth 0 (fun x1 x2 => x1 * x2) g) Fin.elim0]
  simp [sub_eq_add_neg]

/- English proof (translation)
Establish `h` using `cochainsComplex_d A 1`. Simplify using `only [Nat.reduceAdd] at h`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `(inhomogeneousCochains.d A 1).hom f.1 g = _`. Rewrite using `[inhomogeneousCochains.d_hom_apply, Fin.sum_univ_two]`.

Establish `e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1` using `funext fun i => by`. Rewrite using `[Subsingleton.elim i 0]`. Both sides reduce to the same expression. Establish `e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1` using `funext fun i => by`. Rewrite using `[Subsingleton.elim i 0, Fin.contractNth_apply_of_eq _ _ _ _ rfl]`.

Both sides reduce to the same expression. Establish `e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0` using `funext fun i => by`. Rewrite using `[Subsingleton.elim i 0, Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl`. Rewrite using `[e1, e2, e3]`. Simplify using `only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one, Nat.reduceAdd, even_two, Even.neg_pow, one_pow]`.

Normalize the expressions using the abelian group laws.
-/
theorem cochainsComplex_d_one_apply (f : locallyConstantCochains A 1) (g : Fin 2 → G) :
    (((cochainsComplex A).d 1 2).hom f).1 g =
      A.ρ (g 0) (f.1 fun _ => g 1) - f.1 (fun _ => g 0 * g 1) + f.1 (fun _ => g 0) := by
  have h := cochainsComplex_d A 1
  simp only [Nat.reduceAdd] at h
  rw [h]
  change (inhomogeneousCochains.d A 1).hom f.1 g = _
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_two]
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_eq _ _ _ _ rfl]; rfl
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  rw [e1, e2, e3]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one, Nat.reduceAdd,
    even_two, Even.neg_pow, one_pow]
  abel

omit [IsTopologicalGroup G] in
/- English proof (translation)
The claim follows from `funext fun i => by rw [Subsingleton.elim i 0]`.
-/
theorem fin_one_eq_const (g : Fin 1 → G) : g = fun _ => g 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf g h`. Use `congrArg (fun c : locallyConstantCochains A 2 => c.1 ![g, h]) hf` as an intermediate fact. Simplify using `only [cochainsComplex_d_one_apply] at this`. Express the relevant statement in the definitionally equal form `A.ρ g (f.1 fun _ => h) - f.1 (fun _ => g * h) + f.1 (fun _ => g) = 0 at this`.

Rewrite using `[← sub_eq_zero, ← neg_eq_zero, ← this]`. Normalize the expressions using the abelian group laws. Introduce `hf`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Rewrite using `[cochainsComplex_d_one_apply, hf]`. Express the relevant statement in the definitionally equal form `_ = (0 : A)`. Normalize the expressions using the abelian group laws.
-/
theorem cochainsComplex_d_one_eq_zero_iff (f : locallyConstantCochains A 1) :
    ((cochainsComplex A).d 1 2).hom f = 0 ↔
      ∀ g h : G, f.1 (fun _ => g * h) = f.1 (fun _ => g) + A.ρ g (f.1 fun _ => h) := by
  constructor
  · intro hf g h
    have := congrArg (fun c : locallyConstantCochains A 2 => c.1 ![g, h]) hf
    simp only [cochainsComplex_d_one_apply] at this
    change A.ρ g (f.1 fun _ => h) - f.1 (fun _ => g * h) + f.1 (fun _ => g) = 0 at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  · intro hf
    apply Subtype.ext
    funext x
    rw [cochainsComplex_d_one_apply, hf]
    change _ = (0 : A)
    abel

/- English proof (translation)
Use `(cochainsComplex_d_one_eq_zero_iff A f).1 hf 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, Module.End.one_apply] at this`. Simplify using `using this`.
-/
theorem cocycle_one_apply_one {f : locallyConstantCochains A 1}
    (hf : ((cochainsComplex A).d 1 2).hom f = 0) : f.1 (fun _ => 1) = 0 := by
  have := (cochainsComplex_d_one_eq_zero_iff A f).1 hf 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at this
  simpa using this

end Formulas

section Conj

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

/- English proof (translation)
The claim follows from `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`.
-/
theorem continuous_conjHom (g : G) : Continuous (GroundTheory.GroupCoh.conjHom N g) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

noncomputable def cohomologyConj (n : ℕ) (g : G) :
    cohomology (Rep.res N.subtype A) n ⟶ cohomology (Rep.res N.subtype A) n :=
  cohomologyMapAlong (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (GroundTheory.GroupCoh.conjMor A N g) n

def cohomologyConjInvariants (n : ℕ) : Submodule k (cohomology (Rep.res N.subtype A) n) where
  carrier := {x | ∀ g : G, (cohomologyConj A N n g).hom x = x}
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' r x hx g := by rw [map_smul, hx g]

noncomputable abbrev cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) (n : N) : A :=
  (((cochainsComplex (Rep.res N.subtype A)).iCycles 1).hom z).1 fun _ => n

/- English proof (translation)
Rewrite using `[cohomologyConj, cohomologyπ_cohomologyMapAlong_apply, ← sub_eq_zero, ← map_sub]`. Express the relevant statement in the definitionally equal form `((cochainsComplex (Rep.res N.subtype A)).homologyπ (0 + 1)).hom _ = 0 ↔ _`. Rewrite using `[homologyπ_succ_eq_zero_iff, map_sub, iCycles_cyclesMap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`.

Use `⟨w.1 Fin.elim0, fun n => ?_⟩` and prove the remaining obligations. Use `congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw` as an intermediate fact. Conclude with `this.symm.trans (cochainsComplex_d_zero_apply (Rep.res N.subtype A) w fun _ => n)`. Introduce and unpack `⟨a, ha⟩`. Use `⟨⟨fun _ => a, IsLocallyConstant.const _⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Rewrite using `[cochainsComplex_d_zero_apply, fin_one_eq_const x]`. Conclude with `(ha (x 0)).symm`.
-/
theorem cohomologyConj_π_eq_iff (z : cocycles (Rep.res N.subtype A) 1) (g : G) :
    (cohomologyConj A N 1 g).hom ((cohomologyπ _ 1).hom z) = (cohomologyπ _ 1).hom z ↔
      ∃ a : A, ∀ n : N, A.ρ g (cocycleOneApply A N z (GroundTheory.GroupCoh.conjHom N g n)) -
        cocycleOneApply A N z n = A.ρ n a - a := by
  rw [cohomologyConj, cohomologyπ_cohomologyMapAlong_apply, ← sub_eq_zero, ← map_sub]
  change ((cochainsComplex (Rep.res N.subtype A)).homologyπ (0 + 1)).hom _ = 0 ↔ _
  rw [homologyπ_succ_eq_zero_iff, map_sub, iCycles_cyclesMap_apply]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.1 Fin.elim0, fun n => ?_⟩
    have := congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw
    exact this.symm.trans (cochainsComplex_d_zero_apply (Rep.res N.subtype A) w fun _ => n)
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun _ => a, IsLocallyConstant.const _⟩, ?_⟩
    apply Subtype.ext
    funext x
    rw [cochainsComplex_d_zero_apply, fin_one_eq_const x]
    exact (ha (x 0)).symm

/- English proof (translation)
The claim follows from `(cochainsComplex_d_one_eq_zero_iff (Rep.res N.subtype A) _).1 (iCycles_d_apply _ 1 2 z) a b`.
-/
theorem cocycleOneApply_mul (z : cocycles (Rep.res N.subtype A) 1) (a b : N) :
    cocycleOneApply A N z (a * b) = cocycleOneApply A N z a + A.ρ a (cocycleOneApply A N z b) :=
  (cochainsComplex_d_one_eq_zero_iff (Rep.res N.subtype A) _).1
    (iCycles_d_apply _ 1 2 z) a b

noncomputable abbrev cocycleOneApplyG (y : cocycles A 1) (g : G) : A :=
  (((cochainsComplex A).iCycles 1).hom y).1 fun _ => g

/- English proof (translation)
The claim follows from `(cochainsComplex_d_one_eq_zero_iff A _).1 (iCycles_d_apply _ 1 2 y) a b`.
-/
theorem cocycleOneApplyG_mul (y : cocycles A 1) (a b : G) :
    cocycleOneApplyG A y (a * b) = cocycleOneApplyG A y a + A.ρ a (cocycleOneApplyG A y b) :=
  (cochainsComplex_d_one_eq_zero_iff A _).1 (iCycles_d_apply _ 1 2 y) a b

/- English proof (translation)
Take `⟨y, rfl⟩` from `homologyπ_surjective (cochainsComplex A) 1 h`. Introduce `g`. Rewrite using `[cohomologyRes, cohomologyMapAlong]`. Use `erw [homologyMap_homologyπ_apply]`. Use `(cohomologyConj_π_eq_iff A N _ g).2 ⟨cocycleOneApplyG A y g, fun n => ?_⟩` and prove the remaining obligations.

Establish `hY : ∀ n : N, cocycleOneApply A N ((cocyclesMapAlong N.subtype (continuous_subgroup_subtype N) (𝟙 _) 1).hom y) n = cocycleOneApplyG A y n` using `fun n => by`. Simplify using `only [cocycleOneApply, cocyclesMapAlong, iCycles_cyclesMap_apply]`. Both sides reduce to the same expression. Rewrite using `[hY, hY]`. Establish `e : (g : G) * (GroundTheory.GroupCoh.conjHom N g n : G) = n * g` using `by simp; group`.

Establish `h1` using `cocycleOneApplyG_mul A y g (GroundTheory.GroupCoh.conjHom N g n)`. Rewrite `h1` using `[e, cocycleOneApplyG_mul A y n g]`. Establish `h2 : A.ρ g (cocycleOneApplyG A y (GroundTheory.GroupCoh.conjHom N g n)) = cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y g) - cocycleOneApplyG A y g`. Rewrite using `[h1]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h2]`. Normalize the expressions using the abelian group laws.
-/
theorem cohomologyRes_mem_cohomologyConjInvariants (h : cohomology A 1) :
    (cohomologyRes A N 1).hom h ∈ cohomologyConjInvariants A N 1 := by
  obtain ⟨y, rfl⟩ := homologyπ_surjective (cochainsComplex A) 1 h
  intro g
  rw [cohomologyRes, cohomologyMapAlong]
  erw [homologyMap_homologyπ_apply]
  refine (cohomologyConj_π_eq_iff A N _ g).2 ⟨cocycleOneApplyG A y g, fun n => ?_⟩
  have hY : ∀ n : N, cocycleOneApply A N ((cocyclesMapAlong N.subtype
      (continuous_subgroup_subtype N) (𝟙 _) 1).hom y) n = cocycleOneApplyG A y n := fun n => by
    simp only [cocycleOneApply, cocyclesMapAlong, iCycles_cyclesMap_apply]
    rfl
  rw [hY, hY]
  have e : (g : G) * (GroundTheory.GroupCoh.conjHom N g n : G) = n * g := by simp; group
  have h1 := cocycleOneApplyG_mul A y g (GroundTheory.GroupCoh.conjHom N g n)
  rw [e, cocycleOneApplyG_mul A y n g] at h1
  have h2 : A.ρ g (cocycleOneApplyG A y (GroundTheory.GroupCoh.conjHom N g n)) =
      cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y g) - cocycleOneApplyG A y g := by
    rw [h1]
    abel
  rw [h2]
  abel

end Conj

end GroundTheory.ProfCoh
