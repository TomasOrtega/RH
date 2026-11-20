import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem mt_mul (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

/- English proof (translation)
Unfold `actO`. Rewrite using `[mul_inv_rev, mt_mul, mt_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem actO_actO (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `actO`. Rewrite using `[inv_one, mt_one, mt_one]`. Simplify using the standard rewrite rules.
-/
theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, mt_one, mt_one]
  simp

/- English proof (translation)
Unfold `actO`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`.
-/
theorem actO_add (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Rewrite using `[actO_actO, mul_inv_cancel, mul_inv_cancel, actO_one]`.
-/
theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO, mul_inv_cancel, mul_inv_cancel, actO_one]

/- English proof (translation)
Rewrite using `[actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]`.
-/
theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]

def actOHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T where
  toFun := actO S T g h
  map_zero' := by unfold actO; simp
  map_add' := actO_add S T g h

/- English proof (translation)
Break down `le_or_gt S.rank T.rank with hr | hr` into its components or cases. Take `⟨h1, h2⟩` from `Brg.bridgeSmall S T hr`. Rewrite using `[h1, h1, h2, h2, sympl_actHom]`. Take `⟨h1, h2⟩` from `Brg.bridgeLarge' S T hr`. Rewrite using `[h1, h1, h2, h2, sympl_actHom]`.
-/
theorem symplO_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  rcases le_or_gt S.rank T.rank with hr | hr
  · obtain ⟨h1, h2⟩ := Brg.bridgeSmall S T hr
    rw [h1, h1, h2, h2, sympl_actHom]
  · obtain ⟨h1, h2⟩ := Brg.bridgeLarge' S T hr
    rw [h1, h1, h2, h2, sympl_actHom]

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[symplO_actO]`.
-/
theorem symplOH_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH; rw [symplO_actO]

def pull (S T : HSp D) (g : GA D S) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (actO S T g h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pull_apply (S T : HSp D) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) (w : WO S T) :
    pull S T g h f w = f (actO S T g h w) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [pull_apply, actO_actO]`.
-/
theorem pull_pull (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (f : WO S T → ℂ) :
    pull S T g h (pull S T g' h' f) = pull S T (g' * g) (h' * h) f := by
  funext w; simp only [pull_apply, actO_actO]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [pull_apply, actO_one]`.
-/
theorem pull_one (S T : HSp D) (f : WO S T → ℂ) : pull S T 1 1 f = f := by
  funext w; simp only [pull_apply, actO_one]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [pull_apply, heisO]`. Rewrite using `[actO_add, actO_inv_actO]`. Use `congr 2`. Use `conv_lhs => rw [← actO_inv_actO S T g h w₀]`.

Rewrite using `[symplOH_actO]`.
-/
theorem pull_heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (g : GA D S) (h : GA D T) (w₀ : WO S T)
    (f : WO S T → ℂ) :
    pull S T g h (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g⁻¹ h⁻¹ w₀) (pull S T g h f) := by
  funext w
  simp only [pull_apply, heisO]
  rw [actO_add, actO_inv_actO]
  congr 2
  conv_lhs => rw [← actO_inv_actO S T g h w₀]
  rw [symplOH_actO]

/- English proof (translation)
Simplify using `only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ`. Take `⟨u, -, hu⟩` from `hγ`. Conclude with `⟨u.1, (congrArg Units.val hu).symm⟩`.
-/
theorem mt_GQ (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = M.map (incA D) := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

/- English proof (translation)
Take `⟨M, hM⟩` from `mt_GQ S (inv_mem hγ)`. Take `⟨M', hM'⟩` from `mt_GQ T hγ'`. Use `⟨M' * ξ * M, ?_⟩` and prove the remaining obligations. Unfold `actO ratW`. Rewrite using `[hM, hM', Matrix.map_mul, Matrix.map_mul]`.
-/
theorem actO_ratW (S T : HSp D) {γ : GA D S} {γ' : GA D T} (hγ : γ ∈ GQ S) (hγ' : γ' ∈ GQ T)
    (ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, actO S T γ γ' (ratW T S ξ) = ratW T S ξ' := by
  obtain ⟨M, hM⟩ := mt_GQ S (inv_mem hγ)
  obtain ⟨M', hM'⟩ := mt_GQ T hγ'
  refine ⟨M' * ξ * M, ?_⟩
  unfold actO ratW
  rw [hM, hM', Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Unfold `actO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`.
-/
theorem actO_map {R : Type*} [Semiring R] (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T)
    (φ : AE D →+* R) :
    (actO S T g h x).map φ = (Formalism.L2.Theta.mt T h).map φ * x.map φ * (Formalism.L2.Theta.mt S g⁻¹).map φ := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Unfold `actO`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  unfold actO
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
Introduce `ξ w`. Take `⟨ξ', hξ'⟩` from `actO_ratW S T hγ hγ' ξ`. Simplify using `only [pull_apply]`. Rewrite using `[actO_add, hξ', hf.quasi ξ' (actO S T γ γ' w), ← hξ', symplOH_actO]`. Use `level := by`.

Take `⟨U, hU, hUf⟩` from `hf.level`. Use `⟨U.comap (actOHom S T γ γ'), hU.preimage (continuous_actO S T γ γ'), fun u hu h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : (actO S T γ γ' u).map (infPart D) = 0` using `by rw [actO_map, h0]; simp`. Establish `h2` using `hUf (actO S T γ γ' u) (AddSubgroup.mem_comap.1 hu) h1`. Establish `h3` using `pull_heisO ψ S T γ γ' (actO S T γ γ' u) f`.

Rewrite `h3` using `[actO_actO_inv]`. Rewrite using `[← h3, h2]`. Use `cont := hf.cont.comp (continuous_actO S T γ γ')`. Use `smooth := by`. Introduce `k L hL hL0 w`.

Establish `h` using `hf.smooth k ((actOHom S T γ γ').comp L) ((continuous_actO S T γ γ').comp hL) (fun t => by show (actO S T γ γ' (L t)).map (finPart D) = 0`. Rewrite using `[actO_map, hL0 t]`. Use the proof step `simp) (actO S T γ γ' w)`. Establish `e : (fun t => f (actO S T γ γ' w + ((actOHom S T γ γ').comp L) t)) = fun t => pull S T γ γ' f (w + L t)`. Use function extensionality and compare the values at `t`.

Simplify using `only [pull_apply, actO_add]`. Both sides reduce to the same expression. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem isThetaFunO_pull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {γ : GA D S} {γ' : GA D T}
    (hγ : γ ∈ GQ S) (hγ' : γ' ∈ GQ T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (pull S T γ γ' f) where
  quasi := by
    intro ξ w
    obtain ⟨ξ', hξ'⟩ := actO_ratW S T hγ hγ' ξ
    simp only [pull_apply]
    rw [actO_add, hξ', hf.quasi ξ' (actO S T γ γ' w), ← hξ', symplOH_actO]
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨U.comap (actOHom S T γ γ'), hU.preimage (continuous_actO S T γ γ'), fun u hu h0 => ?_⟩
    have h1 : (actO S T γ γ' u).map (infPart D) = 0 := by rw [actO_map, h0]; simp
    have h2 := hUf (actO S T γ γ' u) (AddSubgroup.mem_comap.1 hu) h1
    have h3 := pull_heisO ψ S T γ γ' (actO S T γ γ' u) f
    rw [actO_actO_inv] at h3
    rw [← h3, h2]
  cont := hf.cont.comp (continuous_actO S T γ γ')
  smooth := by
    intro k L hL hL0 w
    have h := hf.smooth k ((actOHom S T γ γ').comp L) ((continuous_actO S T γ γ').comp hL)
      (fun t => by
        show (actO S T γ γ' (L t)).map (finPart D) = 0
        rw [actO_map, hL0 t]; simp) (actO S T γ γ' w)
    have e : (fun t => f (actO S T γ γ' w + ((actOHom S T γ γ').comp L) t)) =
        fun t => pull S T γ γ' f (w + L t) := by
      funext t; simp only [pull_apply, actO_add]; rfl
    rw [e] at h
    exact h

end Formalism.IndefR.Eqv

end
