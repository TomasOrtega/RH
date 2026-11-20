import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupFiltration
import GroundTheory.LocalFields.FormalGroups.Basics

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing GroundTheory.LocalField.FormalGroup

section FormalGroupPoints

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

namespace MaxIdealPoint

variable {F G H : FormalGroup 𝒪}

def homApply (f : Hom F G) (x : MaxIdealPoint F) : MaxIdealPoint G :=
  mk (psEvalAt (f.toPowerSeries : MvPowerSeries Unit 𝒪) fun _ => x.val)
    (psEvalAt_mem (by rw [f.constantCoeff_eq_zero']; exact zero_mem _) fun _ => x.val_mem)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_homApply (f : Hom F G) (x : MaxIdealPoint F) :
    (homApply f x).val = psEvalAt (f.toPowerSeries : MvPowerSeries Unit 𝒪) fun _ => x.val :=
  rfl

/- English proof (translation)
Apply `ext` to reduce the goal to its premises. Rewrite using `[val_homApply, Hom.toPowerSeries_comp, psEvalAt_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero) _ fun _ => x.val_mem]`. Both sides reduce to the same expression.
-/
theorem homApply_comp (g : Hom G H) (f : Hom F G) (x : MaxIdealPoint F) :
    homApply (g.comp f) x = homApply g (homApply f x) := by
  apply ext
  rw [val_homApply, Hom.toPowerSeries_comp, psEvalAt_powerSeries_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero) _ fun _ => x.val_mem]
  rfl

/- English proof (translation)
Apply `ext` to reduce the goal to its premises. Rewrite using `[val_homApply, Hom.toPowerSeries_id]`. Conclude with `psEvalAt_X (fun _ : Unit => x.val) ()`.
-/
theorem homApply_id (x : MaxIdealPoint F) : homApply (Hom.id F) x = x := by
  apply ext
  rw [val_homApply, Hom.toPowerSeries_id]
  exact psEvalAt_X (fun _ : Unit => x.val) ()

/- English proof (translation)
Apply `ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = psEvalAt (PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit 𝒪) f.toPowerSeries) fun _ => x.val`. Rewrite using `[psEvalAt_powerSeries_subst (PowerSeries.HasSubst.X ()) _ fun _ => x.val_mem, psEvalAt_X]`. Both sides reduce to the same expression.
-/
theorem homApply_eq_evalPoint (f : Hom F F) (x : MaxIdealPoint F) :
    homApply f x = evalPoint (fun _ : Unit => x) (f.apply (pointVar ())) := by
  apply ext
  change _ = psEvalAt (PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit 𝒪)
    f.toPowerSeries) fun _ => x.val
  rw [psEvalAt_powerSeries_subst (PowerSeries.HasSubst.X ()) _ fun _ => x.val_mem, psEvalAt_X]
  rfl

def evalPointHom {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) : F.Point σ →+ MaxIdealPoint F :=
  AddMonoidHom.mk' (evalPoint x) (evalPoint_add x)

/- English proof (translation)
Rewrite using `[homApply_eq_evalPoint, Hom.intCast_apply]`. Express the relevant statement in the definitionally equal form `evalPointHom (fun _ : Unit => x) (n • pointVar ()) = _`. Rewrite using `[map_zsmul]`. Express the relevant statement in the definitionally equal form `n • evalPoint (fun _ : Unit => x) (pointVar ()) = _`. Rewrite using `[evalPoint_pointVar]`.
-/
theorem homApply_intCast [F.IsComm] (n : ℤ) (x : MaxIdealPoint F) :
    homApply (n : Hom F F) x = n • x := by
  rw [homApply_eq_evalPoint, Hom.intCast_apply]
  change evalPointHom (fun _ : Unit => x) (n • pointVar ()) = _
  rw [map_zsmul]
  change n • evalPoint (fun _ : Unit => x) (pointVar ()) = _
  rw [evalPoint_pointVar]

/- English proof (translation)
Establish `hc : IsUnit (PowerSeries.coeff 1 (n : Hom F F).toPowerSeries)`. Rewrite using `[← linearCoeff_apply, map_intCast]`. Conclude with `hn`. Use `set e := Iso.ofIsUnit (n : Hom F F) hc`. Establish `he : e.hom = (n : Hom F F)` using `rfl`.

Use `Function.bijective_iff_has_inverse.2 ⟨homApply e.inv, fun x => ?_, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `homApply e.inv (n • x) = x`. Rewrite using `[← homApply_intCast, ← he, ← homApply_comp, e.inv_comp_hom, homApply_id]`. Express the relevant statement in the definitionally equal form `n • homApply e.inv y = y`. Rewrite using `[← homApply_intCast, ← he, ← homApply_comp, e.hom_comp_inv, homApply_id]`.
-/
theorem zsmul_bijective [F.IsComm] {n : ℤ} (hn : IsUnit (n : 𝒪)) :
    Function.Bijective fun x : MaxIdealPoint F => n • x := by
  have hc : IsUnit (PowerSeries.coeff 1 (n : Hom F F).toPowerSeries) := by
    rw [← linearCoeff_apply, map_intCast]
    exact hn
  set e := Iso.ofIsUnit (n : Hom F F) hc
  have he : e.hom = (n : Hom F F) := rfl
  refine Function.bijective_iff_has_inverse.2 ⟨homApply e.inv, fun x => ?_, fun y => ?_⟩
  · change homApply e.inv (n • x) = x
    rw [← homApply_intCast, ← he, ← homApply_comp, e.inv_comp_hom, homApply_id]
  · change n • homApply e.inv y = y
    rw [← homApply_intCast, ← he, ← homApply_comp, e.hom_comp_inv, homApply_id]

/- English proof (translation)
Establish `h` using `zsmul_bijective (F := F) (n := (n : ℤ)) (by simpa using hn)`. Simplify `h` using `only [natCast_zsmul]`.
-/
theorem nsmul_bijective [F.IsComm] {n : ℕ} (hn : IsUnit (n : 𝒪)) :
    Function.Bijective fun x : MaxIdealPoint F => n • x := by
  have h := zsmul_bijective (F := F) (n := (n : ℤ)) (by simpa using hn)
  simpa only [natCast_zsmul] using h

end MaxIdealPoint

end FormalGroupPoints

section E1

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K]

/- English proof (translation)
Establish `h` using `MaxIdealPoint.nsmul_bijective (F := formalGroup W) hn`. Establish `: (fun P : E1 K W => n • P) = (e1Equiv K W) ∘ (fun x : MaxIdealPoint (formalGroup W) => n • x) ∘ (e1Equiv K W).symm`. Use function extensionality and compare the values at `P`. Simplify using `[map_nsmul]`. Rewrite using `[this]`.

Conclude with `(e1Equiv K W).bijective.comp (h.comp (e1Equiv K W).symm.bijective)`.
-/
theorem E1_nsmul_bijective {n : ℕ} (hn : IsUnit (n : 𝒪)) :
    Function.Bijective fun P : E1 K W => n • P := by
  have h := MaxIdealPoint.nsmul_bijective (F := formalGroup W) hn
  have : (fun P : E1 K W => n • P) =
      (e1Equiv K W) ∘ (fun x : MaxIdealPoint (formalGroup W) => n • x) ∘ (e1Equiv K W).symm := by
    funext P
    simp [map_nsmul]
  rw [this]
  exact (e1Equiv K W).bijective.comp (h.comp (e1Equiv K W).symm.bijective)

/- English proof (translation)
Establish `h` using `(E1_nsmul_bijective K W hn).1 (a₁ := ⟨P, hP⟩) (a₂ := 0) (by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hnP])`. Simplify using `using congrArg Subtype.val h`.
-/
theorem eq_zero_of_mem_E1_of_nsmul_eq_zero {n : ℕ} (hn : IsUnit (n : 𝒪))
    {P : (W.map (algebraMap 𝒪 K)).toAffine.Point} (hP : P ∈ E1 K W) (hnP : n • P = 0) : P = 0 := by
  have h := (E1_nsmul_bijective K W hn).1 (a₁ := ⟨P, hP⟩) (a₂ := 0) (by
    apply Subtype.ext
    simp [hnP])
  simpa using congrArg Subtype.val h

end E1

end

end GroundTheory.Arith.Abelian
