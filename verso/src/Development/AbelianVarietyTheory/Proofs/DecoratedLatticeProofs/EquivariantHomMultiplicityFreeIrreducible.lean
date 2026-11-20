import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.EquivHomIrr

/- English proof (translation)
Establish `key : ∀ (z : A ⊗[ℂ] B) (i), TensorProduct.equivFinsuppOfBasisRight b z i = TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) z)`. Introduce `z i`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v w => simp`.

Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Apply `(TensorProduct.equivFinsuppOfBasisRight b).injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[key, key, h]`.
-/
theorem tensor_eq_of_coord_contract {A B ι : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (b : Module.Basis ι ℂ B) (x y : A ⊗[ℂ] B)
    (h : ∀ i, TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) x)
      = TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) y)) : x = y := by
  classical
  have key : ∀ (z : A ⊗[ℂ] B) (i), TensorProduct.equivFinsuppOfBasisRight b z i
      = TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, key, h]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v w => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem contract_map_left {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (l : Module.Dual ℂ B) (f : A →ₗ[ℂ] A) (y : A ⊗[ℂ] B) :
    TensorProduct.rid ℂ A (LinearMap.lTensor A l (TensorProduct.map f LinearMap.id y))
      = f (TensorProduct.rid ℂ A (LinearMap.lTensor A l y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Break down `Representation.IsIrreducible.bijective_or_eq_zero f with h | h` into its components or cases. Conclude with `(hne.false (f.ofBijective h)).elim`. Conclude with `h`.
-/
theorem intertwining_eq_zero_of_isEmpty {G V A : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup A] [Module ℂ A] (ρ : Representation ℂ G V) (α : Representation ℂ G A)
    (hρ : ρ.IsIrreducible) (hα : α.IsIrreducible) (hne : IsEmpty (ρ.Equiv α))
    (f : ρ.IntertwiningMap α) : f = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with h | h
  · exact (hne.false (f.ofBijective h)).elim
  · exact h

/- English proof (translation)
Take `⟨c, hc⟩` from `(Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2 (ι.symm.toIntertwiningMap.comp f)`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun F : ρ.IntertwiningMap ρ => F v) hc`. Simplify using `only [Representation.IntertwiningMap.algebraMap_apply] at h1`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : ι.symm (f v) = c • v` using `h1.symm`. Rewrite using `[h2]`. Use `_ = c • ι v := map_smul _ _ _`.
-/
theorem intertwining_eq_smul {G V A : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup A] [Module ℂ A] (ρ : Representation ℂ G V)
    (α : Representation ℂ G A) (hρ : ρ.IsIrreducible) (ι : ρ.Equiv α)
    (f : ρ.IntertwiningMap α) : ∃ c : ℂ, ∀ v, f v = c • ι v := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (ι.symm.toIntertwiningMap.comp f)
  refine ⟨c, fun v => ?_⟩
  have h1 := congrArg (fun F : ρ.IntertwiningMap ρ => F v) hc
  simp only [Representation.IntertwiningMap.algebraMap_apply] at h1
  calc f v = ι (ι.symm (f v)) := by simp
    _ = ι (c • v) := by
      have h2 : ι.symm (f v) = c • v := h1.symm
      rw [h2]
    _ = c • ι v := map_smul _ _ _

end GlobalTheory.EquivHomIrr

namespace GlobalTheory.EquivHomIrr

/- English proof (translation)
Introduce `G H J _ _ _ A B _ _ _ _ _ _ α β hα hβ hαinj W _ _ ω he V _ _ _ ρ hρ S hSG hSH hS0 Q hQ`. Take `⟨e⟩` from `he`. Use `set R := Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H)) ((β j).comp (MonoidHom.snd G H)) with hR`. Establish `heS : ∀ (x : G × H) (w : W), e.symm (ω x w) = R x (e.symm w)` using `fun x w => LinearMap.congr_fun (e.symm.isIntertwining' x) w`. Establish `heF : ∀ (x : G × H) y, e (R x y) = ω x (e y)` using `fun x y => LinearMap.congr_fun (e.isIntertwining' x) y`.

Set `con : ∀ j, Module.Dual ℂ (B j) → (DirectSum J fun j => A j ⊗[ℂ] B j) →ₗ[ℂ] A j` to `fun j l => (TensorProduct.rid ℂ (A j)).toLinearMap ∘ₗ LinearMap.lTensor (A j) l ∘ₗ DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j`. Establish `hcon : ∀ j l (g : G) y, con j l (R (g, 1) y) = α j g (con j l y)`. Introduce `j l g y`. Establish `h1 : DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (R (g, 1) y) = TensorProduct.map (α j g) LinearMap.id (DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j y)`. Rewrite using `[hR, Representation.directSum_apply]`.

Simplify using `only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, Module.End.one_eq_id]`. Both sides reduce to the same expression. Simplify using `only [con, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[h1, contract_map_left]`. Set `cT : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∀ j, Module.Dual ℂ (B j) → ρ.IntertwiningMap (α j)` to `fun T hT j l => { toLinearMap := con j l ∘ₗ e.symm.toLinearMap ∘ₗ T isIntertwining' := fun g => LinearMap.ext fun v => by`.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hT, Representation.Equiv.coe_toLinearMap, heS, hcon] }`. Establish `hcT : ∀ (T : V →ₗ[ℂ] W) hT j l v, cT T hT j l v = con j l (e.symm (T v))` using `fun _ _ _ _ _ => rfl`. Establish `hzero : ∀ (T : V →ₗ[ℂ] W) (hT : ∀ g v, T (ρ g v) = ω (g, 1) (T v)) j, IsEmpty (ρ.Equiv (α j)) → ∀ v, DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (e.symm (T v)) = 0`. Introduce `T hT j hj v`.

Apply `tensor_eq_of_coord_contract (Module.Free.chooseBasis ℂ (B j))` to reduce the goal to its premises. Introduce `i`. Establish `h0` using `intertwining_eq_zero_of_isEmpty ρ (α j) hρ (hα j) hj (cT T hT j ((Module.Free.chooseBasis ℂ (B j)).coord i))`. Establish `h2` using `congrArg (fun F : ρ.IntertwiningMap (α j) => F v) h0`. Simplify using `only [hcT, Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h2`.

Simplify `h2` using `[con]`. Distinguish the cases in `hex : ∃ j0, Nonempty (ρ.Equiv (α j0))`. Use `swap`. Establish `hQ0 : Q = 0`. Use `LinearMap.ext fun v => (EquivLike.injective e.symm) ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.zero_apply, map_zero]`. Use `DirectSum.ext_component ℂ fun j => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `hzero Q hQ j (not_nonempty_iff.1 fun h => hex ⟨j, h⟩) v`. Rewrite using `[hQ0]`.

Conclude with `S.zero_mem`. Take `⟨j0, ⟨ι⟩⟩` from `hex`. Establish `honly : ∀ j, j ≠ j0 → IsEmpty (ρ.Equiv (α j))` using `fun j hj => ⟨fun κ => hj (hαinj j0 j ⟨ι.symm.trans κ⟩).symm⟩`. Set `Φ : B j0 →ₗ[ℂ] (V →ₗ[ℂ] W)` to `{ toFun := fun b => e.toLinearMap ∘ₗ DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 ∘ₗ (TensorProduct.mk ℂ (A j0) (B j0)).flip b ∘ₗ ι.toLinearMap map_add' := by intros; ext; simp [TensorProduct.tmul_add] map_smul' := by intros; ext; simp }`. Establish `hΦ : ∀ b v, e.symm (Φ b v) = DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 (ι v ⊗ₜ b)`.

Introduce `b v`. Simplify using `[Φ]`. Establish `hrep : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∃ b, Φ b = T`. Introduce `T hT`. Set `bs` to `Module.Free.chooseBasis ℂ (B j0)`.

Use `choose c hc using fun i => intertwining_eq_smul ρ (α j0) hρ ι (cT T hT j0 (bs.coord i))`. Establish `hc' : ∀ i v, con j0 (bs.coord i) (e.symm (T v)) = c i • ι v` using `fun i v => hc i v`. Use `⟨bs.repr.symm (Finsupp.equivFunOnFinite.symm c), LinearMap.ext fun v => (EquivLike.injective e.symm) ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Use `DirectSum.ext_component ℂ fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Rewrite using `[DirectSum.component.lof_self]`. Apply `tensor_eq_of_coord_contract bs` to reduce the goal to its premises. Introduce `i`.

Establish `h3` using `hc' i v`. Simplify using `only [con, LinearMap.comp_apply, LinearEquiv.coe_coe] at h3`. Rewrite using `[h3]`. Simplify using the standard rewrite rules. Rewrite using `[DirectSum.component.of, dif_neg (Ne.symm hj), hzero T hT j (honly j hj) v]`.

Set `S' : Subrepresentation (β j0)` to `{ toSubmodule := S.comap Φ apply_mem_toSubmodule := by`. Introduce `h b hb`. Simplify using `only [Submodule.mem_comap] at hb ⊢`. Establish `hh : Φ (β j0 h b) = (ω (1, h)) ∘ₗ Φ b`. Use `LinearMap.ext fun v => (EquivLike.injective e.symm) ?_` and prove the remaining obligations.

Rewrite using `[hΦ, LinearMap.comp_apply, heS, hΦ, hR, Representation.directSum_apply, DirectSum.lmap_lof]`. Simplify using the standard rewrite rules. Rewrite using `[hh]`. Conclude with `hSH _ hb h }`. Use `haveI := hβ j0`.

Break down `eq_bot_or_eq_top S' with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hS0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `T hT`.

Take `⟨b, rfl⟩` from `hrep T (hSG T hT)`. Establish `hb : b ∈ S'.toSubmodule` using `hT`. Rewrite `hb` using `[h]`. Establish `hb0 : b = 0` using `(Submodule.mem_bot ℂ).1 hb`. Rewrite using `[hb0, map_zero]`.

Conclude with `Submodule.zero_mem _`. Take `⟨b, rfl⟩` from `hrep Q hQ`. Establish `hb : b ∈ S'.toSubmodule` using `by rw [h]; exact Submodule.mem_top`. Conclude with `hb`.
-/
theorem equivariantHom_mem_of_stable : ∀ (G H J : Type) [Group G] [Group H] [DecidableEq J] (A B : J → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, FiniteDimensional ℂ (A j)] [∀ j, FiniteDimensional ℂ (B j)] (α : ∀ j, Representation ℂ G (A j)) (β : ∀ j, Representation ℂ H (B j)), (∀ j, (α j).IsIrreducible) → (∀ j, (β j).IsIrreducible) → (∀ j j', Nonempty ((α j).Equiv (α j')) → j = j') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ω : Representation ℂ (G × H) W), Nonempty ((Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H)) ((β j).comp (MonoidHom.snd G H))).Equiv ω) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → ∀ S : Submodule ℂ (V →ₗ[ℂ] W), (∀ T ∈ S, ∀ g v, T (ρ g v) = ω (g, 1) (T v)) → (∀ T ∈ S, ∀ h, ω (1, h) ∘ₗ T ∈ S) → S ≠ ⊥ → ∀ Q : V →ₗ[ℂ] W, (∀ g v, Q (ρ g v) = ω (g, 1) (Q v)) → Q ∈ S := by
  intro G H J _ _ _ A B _ _ _ _ _ _ α β hα hβ hαinj W _ _ ω he V _ _ _ ρ hρ S hSG hSH hS0 Q hQ
  classical
  obtain ⟨e⟩ := he
  set R := Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H))
    ((β j).comp (MonoidHom.snd G H)) with hR
  have heS : ∀ (x : G × H) (w : W), e.symm (ω x w) = R x (e.symm w) := fun x w =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) w
  have heF : ∀ (x : G × H) y, e (R x y) = ω x (e y) := fun x y =>
    LinearMap.congr_fun (e.isIntertwining' x) y
  let con : ∀ j, Module.Dual ℂ (B j) → (DirectSum J fun j => A j ⊗[ℂ] B j) →ₗ[ℂ] A j := fun j l =>
    (TensorProduct.rid ℂ (A j)).toLinearMap ∘ₗ LinearMap.lTensor (A j) l ∘ₗ
      DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j
  have hcon : ∀ j l (g : G) y, con j l (R (g, 1) y) = α j g (con j l y) := by
    intro j l g y
    have h1 : DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (R (g, 1) y)
        = TensorProduct.map (α j g) LinearMap.id (DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j y) := by
      rw [hR, Representation.directSum_apply]
      simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
        MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, Module.End.one_eq_id]
      rfl
    simp only [con, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, contract_map_left]
  let cT : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∀ j, Module.Dual ℂ (B j) →
      ρ.IntertwiningMap (α j) := fun T hT j l =>
    { toLinearMap := con j l ∘ₗ e.symm.toLinearMap ∘ₗ T
      isIntertwining' := fun g => LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply]
        rw [hT, Representation.Equiv.coe_toLinearMap, heS, hcon] }
  have hcT : ∀ (T : V →ₗ[ℂ] W) hT j l v, cT T hT j l v = con j l (e.symm (T v)) := fun _ _ _ _ _ => rfl
  have hzero : ∀ (T : V →ₗ[ℂ] W) (hT : ∀ g v, T (ρ g v) = ω (g, 1) (T v)) j, IsEmpty (ρ.Equiv (α j)) → ∀ v,
      DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (e.symm (T v)) = 0 := by
    intro T hT j hj v
    apply tensor_eq_of_coord_contract (Module.Free.chooseBasis ℂ (B j))
    intro i
    have h0 := intertwining_eq_zero_of_isEmpty ρ (α j) hρ (hα j) hj
      (cT T hT j ((Module.Free.chooseBasis ℂ (B j)).coord i))
    have h2 := congrArg (fun F : ρ.IntertwiningMap (α j) => F v) h0
    simp only [hcT, Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h2
    simpa [con] using h2
  by_cases hex : ∃ j0, Nonempty (ρ.Equiv (α j0))
  swap
  · have hQ0 : Q = 0 := by
      refine LinearMap.ext fun v => (EquivLike.injective e.symm) ?_
      rw [LinearMap.zero_apply, map_zero]
      refine DirectSum.ext_component ℂ fun j => ?_
      rw [map_zero]
      exact hzero Q hQ j (not_nonempty_iff.1 fun h => hex ⟨j, h⟩) v
    rw [hQ0]
    exact S.zero_mem
  obtain ⟨j0, ⟨ι⟩⟩ := hex
  have honly : ∀ j, j ≠ j0 → IsEmpty (ρ.Equiv (α j)) := fun j hj =>
    ⟨fun κ => hj (hαinj j0 j ⟨ι.symm.trans κ⟩).symm⟩
  let Φ : B j0 →ₗ[ℂ] (V →ₗ[ℂ] W) :=
    { toFun := fun b => e.toLinearMap ∘ₗ DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 ∘ₗ
        (TensorProduct.mk ℂ (A j0) (B j0)).flip b ∘ₗ ι.toLinearMap
      map_add' := by intros; ext; simp [TensorProduct.tmul_add]
      map_smul' := by intros; ext; simp }
  have hΦ : ∀ b v, e.symm (Φ b v) = DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 (ι v ⊗ₜ b) := by
    intro b v
    simp [Φ]
  have hrep : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∃ b, Φ b = T := by
    intro T hT
    let bs := Module.Free.chooseBasis ℂ (B j0)
    choose c hc using fun i => intertwining_eq_smul ρ (α j0) hρ ι (cT T hT j0 (bs.coord i))
    have hc' : ∀ i v, con j0 (bs.coord i) (e.symm (T v)) = c i • ι v := fun i v => hc i v
    refine ⟨bs.repr.symm (Finsupp.equivFunOnFinite.symm c),
      LinearMap.ext fun v => (EquivLike.injective e.symm) ?_⟩
    rw [hΦ]
    refine DirectSum.ext_component ℂ fun j => ?_
    by_cases hj : j = j0
    · subst hj
      rw [DirectSum.component.lof_self]
      apply tensor_eq_of_coord_contract bs
      intro i
      have h3 := hc' i v
      simp only [con, LinearMap.comp_apply, LinearEquiv.coe_coe] at h3
      rw [h3]
      simp
    · rw [DirectSum.component.of, dif_neg (Ne.symm hj), hzero T hT j (honly j hj) v]
  let S' : Subrepresentation (β j0) :=
    { toSubmodule := S.comap Φ
      apply_mem_toSubmodule := by
        intro h b hb
        simp only [Submodule.mem_comap] at hb ⊢
        have hh : Φ (β j0 h b) = (ω (1, h)) ∘ₗ Φ b := by
          refine LinearMap.ext fun v => (EquivLike.injective e.symm) ?_
          rw [hΦ, LinearMap.comp_apply, heS, hΦ, hR, Representation.directSum_apply,
            DirectSum.lmap_lof]
          simp
        rw [hh]
        exact hSH _ hb h }
  haveI := hβ j0
  rcases eq_bot_or_eq_top S' with h | h
  · exfalso
    apply hS0
    rw [eq_bot_iff]
    intro T hT
    obtain ⟨b, rfl⟩ := hrep T (hSG T hT)
    have hb : b ∈ S'.toSubmodule := hT
    rw [h] at hb
    have hb0 : b = 0 := (Submodule.mem_bot ℂ).1 hb
    rw [hb0, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨b, rfl⟩ := hrep Q hQ
    have hb : b ∈ S'.toSubmodule := by rw [h]; exact Submodule.mem_top
    exact hb

end GlobalTheory.EquivHomIrr
