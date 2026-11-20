import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTensHom

variable {k r : ℕ}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons w l ih => simp [Finset.sum_add_distrib, ih]`.
-/
theorem sum_list_comm {α β : Type} [Fintype β] (l : List α) (a : α → β → ℝ) :
    ∑ e, (l.map fun w => a w e).sum = (l.map fun w => ∑ e, a w e).sum := by
  induction l with
  | nil => simp
  | cons w l ih => simp [Finset.sum_add_distrib, ih]

/- English proof (translation)
Simplify using `only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.compLeft_apply, Function.comp_apply]`.
-/
theorem act_apply (X : Obj k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M X) (c : X.1.ι) :
    CompanionTheory.Zuck.act X g x c = ∑ d, X.1.ρ g c d • X.2.sig g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.compLeft_apply, Function.comp_apply]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Rewrite using `[act_apply]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]`. Use `show ∑ d : F.ι × E.ι, _ = _`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Simplify using `[CompanionTheory.Zuck.FRep.tens, mul_comm]`.
-/
theorem act_tens1 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (F.tens E, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (c', e')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens, mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Rewrite using `[act_apply]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]`. Use `show ∑ d : E.ι × F.ι, _ = _`. Rewrite using `[Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Simplify using `[CompanionTheory.Zuck.FRep.tens]`.
-/
theorem act_tens2 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens]

/- English proof (translation)
Simplify using `only [CompanionTheory.Zuck.sn]`. Use `show ∑ d : F.ι × E.ι, _ = _`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_comm]`.
-/
theorem sn_tens1 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (F.tens E, U)) :
    sn (F.tens E, U) W x = ∑ e, sn (F, U) W (fun c => x (c, e)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/- English proof (translation)
Simplify using `only [CompanionTheory.Zuck.sn]`. Use `show ∑ d : E.ι × F.ι, _ = _`. Rewrite using `[Fintype.sum_prod_type]`.
-/
theorem sn_tens2 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]

/- English proof (translation)
Introduce `k r F F' E U U' f hf`. Use `⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `W hW`. Take `⟨C, Ws, hWs, hb⟩` from `hf.cont W hW`. Use `⟨C, Ws, hWs, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[sn_tens1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `_ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum := congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))))`. Use `_ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F.tens E, U) W' x).sum := by`.

Simplify using `only [sn_tens1]`. Introduce `g hg`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Use function extensionality and compare the values at `p`.

Take `⟨c', e⟩` from `p`. Establish `h2` using `act_tens1 F E U g x e`. Establish `h1` using `act_tens1 F' E U' g (CompanionTheory.Zuck.on1 f x) e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun e' _ => ?_` and prove the remaining obligations. Establish `hq` using `LinearMap.congr_fun (hf.equiv g hg) (fun c => x (c, e'))`. Simplify using `only [LinearMap.comp_apply] at hq`. Rewrite using `[hq]`.

Use `_ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on1 f x (c, e'))) c' := by`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Both sides reduce to the same expression. Use `_ = (fun c => CompanionTheory.Zuck.act (F'.tens E, U') g (CompanionTheory.Zuck.on1 f x) (c, e)) c' := (congrFun h1 c').symm`. Use `_ = (CompanionTheory.Zuck.act (F'.tens E, U') g ∘ₗ CompanionTheory.Zuck.on1 f) x (c', e) := rfl`.

Introduce `W hW`. Take `⟨C, Ws, hWs, hb⟩` from `hf.cont W hW`. Use `⟨C, Ws, hWs, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[sn_tens2]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Use `_ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum := congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))))`. Use `_ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (E.tens F, U) W' x).sum := by`. Simplify using `only [sn_tens2]`. Introduce `g hg`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Use function extensionality and compare the values at `p`. Take `⟨e, c'⟩` from `p`. Establish `h2` using `act_tens2 F E U g x e`.

Establish `h1` using `act_tens2 F' E U' g (CompanionTheory.Zuck.on2 f x) e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun e' _ => ?_` and prove the remaining obligations.

Establish `hq` using `LinearMap.congr_fun (hf.equiv g hg) (fun c => x (e', c))`. Simplify using `only [LinearMap.comp_apply] at hq`. Rewrite using `[hq]`. Use `_ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on2 f x (e', c))) c' := by`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`.

Both sides reduce to the same expression. Use `_ = (fun c => CompanionTheory.Zuck.act (E.tens F', U') g (CompanionTheory.Zuck.on2 f x) (e, c)) c' := (congrFun h1 c').symm`. Use `_ = (CompanionTheory.Zuck.act (E.tens F', U') g ∘ₗ CompanionTheory.Zuck.on2 f) x (e, c') := rfl`.
-/
theorem tensHom : TensHom := by
  intro k r F F' E U U' f hf
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens1]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on1 f x (c, e))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (c, e))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F.tens E, U) W' x).sum := by
          simp only [sn_tens1]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨c', e⟩ := p
    have h2 := act_tens1 F E U g x e
    have h1 := act_tens1 F' E U' g (CompanionTheory.Zuck.on1 f x) e
    calc (CompanionTheory.Zuck.on1 f ∘ₗ CompanionTheory.Zuck.act (F.tens E, U) g) x (c', e)
        = f (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (c, e'))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (c, e'))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (c, e'))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on1 f x (c, e'))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (F'.tens E, U') g (CompanionTheory.Zuck.on1 f x) (c, e)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (F'.tens E, U') g ∘ₗ CompanionTheory.Zuck.on1 f) x (c', e) := rfl
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens2]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on2 f x (e, c))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (e, c))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (E.tens F, U) W' x).sum := by
          simp only [sn_tens2]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨e, c'⟩ := p
    have h2 := act_tens2 F E U g x e
    have h1 := act_tens2 F' E U' g (CompanionTheory.Zuck.on2 f x) e
    calc (CompanionTheory.Zuck.on2 f ∘ₗ CompanionTheory.Zuck.act (E.tens F, U) g) x (e, c')
        = f (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (e', c))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (e', c))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (e', c))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on2 f x (e', c))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (E.tens F', U') g (CompanionTheory.Zuck.on2 f x) (e, c)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (E.tens F', U') g ∘ₗ CompanionTheory.Zuck.on2 f) x (e, c') := rfl

end GlobalTheory.CompanionTheory.ZuckTensHom

end
