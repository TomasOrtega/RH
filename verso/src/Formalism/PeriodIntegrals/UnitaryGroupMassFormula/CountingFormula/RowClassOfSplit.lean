import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabFSymmMemPerp

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Rewrite using `[← (VS D).herm.eq y x, starRingEnd_apply]`.
-/
theorem hT_swap (D : D7) (x y : (VS D).V) : (VS D).hT x y = star ((VS D).hT y x) := by
  rw [← (VS D).herm.eq y x, starRingEnd_apply]

section Frame

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def ycL (f : Fin D.R.rS → (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ b, ((VS D).hT (F0.e b)).smulRight (f b)

def xcL (f : Fin D.R.rS → (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ a, ((VS D).hT (f a)).smulRight (F0.e a)

/- English proof (translation)
Simplify using `[ycL, LinearMap.sum_apply, LinearMap.smulRight_apply]`.
-/
theorem ycL_apply (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) :
    ycL F0 f v = ∑ b, (VS D).hT (F0.e b) v • f b := by
  simp [ycL, LinearMap.sum_apply, LinearMap.smulRight_apply]

/- English proof (translation)
Simplify using `[xcL, LinearMap.sum_apply, LinearMap.smulRight_apply]`.
-/
theorem xcL_apply (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) :
    xcL F0 f v = ∑ a, (VS D).hT (f a) v • F0.e a := by
  simp [xcL, LinearMap.sum_apply, LinearMap.smulRight_apply]

def IsDualF (f : Fin D.R.rS → (VS D).V) : Prop :=
  (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ ∀ a b, (VS D).hT (f a) (f b) = 0

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem e_mem_X (a : Fin D.R.rS) : F0.e a ∈ F0.X := Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨a, rfl⟩` from `hw`. Conclude with `hy a`.

Consider the case `zero => simp`. Consider the case `add w w' _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c w _ h => simp [h]`.
-/
theorem mem_perp_of {y : (VS D).V} (hy : ∀ a, (VS D).hT (F0.e a) y = 0) : y ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hy a
  | zero => simp
  | add w w' _ _ h1 h2 => simp [h1, h2]
  | smul c w _ h => simp [h]

/- English proof (translation)
Introduce `y hy`. Apply `mem_perp_of F0` to reduce the goal to its premises. Introduce `a`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨b, rfl⟩` from `hw`. Conclude with `F0.e_iso a b`. Consider the case `zero => simp`. Consider the case `add w w' _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c w _ h => simp [h]`.
-/
theorem X_le_perp : F0.X ≤ perpS (VS D) F0.X := by
  intro y hy
  apply mem_perp_of F0
  intro a
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    exact F0.e_iso a b
  | zero => simp
  | add w w' _ _ h1 h2 => simp [h1, h2]
  | smul c w _ h => simp [h]

/- English proof (translation)
The claim follows from `X_le_perp F0 hy x hx`.
-/
theorem hX_X {x y : (VS D).V} (hx : x ∈ F0.X) (hy : y ∈ F0.X) : (VS D).hT x y = 0 :=
  X_le_perp F0 hy x hx

/- English proof (translation)
The claim follows from `hy x hx`.
-/
theorem hX_perp {x y : (VS D).V} (hx : x ∈ F0.X) (hy : y ∈ perpS (VS D) F0.X) : (VS D).hT x y = 0 :=
  hy x hx

/- English proof (translation)
Rewrite using `[hT_swap D, show (VS D).hT y x = 0 from hx y hy, star_zero]`.
-/
theorem hperp_X {x y : (VS D).V} (hx : x ∈ perpS (VS D) F0.X) (hy : y ∈ F0.X) : (VS D).hT x y = 0 := by
  rw [hT_swap D, show (VS D).hT y x = 0 from hx y hy, star_zero]

variable {F0}
variable {f : Fin D.R.rS → (VS D).V}

/- English proof (translation)
Rewrite using `[hT_swap D, hf.1 b a]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hT_f_e (hf : IsDualF F0 f) (a b : Fin D.R.rS) :
    (VS D).hT (f a) (F0.e b) = if b = a then 1 else 0 := by
  rw [hT_swap D, hf.1 b a]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[ycL_apply, map_sum]`. Simplify using `[hf.1]`.
-/
theorem hT_e_yc (hf : IsDualF F0 f) (a : Fin D.R.rS) (v : (VS D).V) :
    (VS D).hT (F0.e a) (ycL F0 f v) = (VS D).hT (F0.e a) v := by
  rw [ycL_apply, map_sum]
  simp [hf.1]

/- English proof (translation)
Rewrite using `[xcL_apply, map_sum]`. Simplify using `[hT_f_e hf]`.
-/
theorem hT_f_xc (hf : IsDualF F0 f) (a : Fin D.R.rS) (v : (VS D).V) :
    (VS D).hT (f a) (xcL F0 f v) = (VS D).hT (f a) v := by
  rw [xcL_apply, map_sum]
  simp [hT_f_e hf]

/- English proof (translation)
Rewrite using `[xcL_apply]`. Conclude with `Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X F0 a))`.
-/
theorem xc_mem_X (v : (VS D).V) : xcL F0 f v ∈ F0.X := by
  rw [xcL_apply]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X F0 a))

/- English proof (translation)
Rewrite using `[ycL_apply]`. Conclude with `Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))`.
-/
theorem yc_mem_span (v : (VS D).V) : ycL F0 f v ∈ Submodule.span D.host.E (Set.range f) := by
  rw [ycL_apply]
  exact Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨c, rfl⟩` from `hw`. Rewrite using `[xcL_apply]`. Simplify using `[hT_f_e hf]`.

Consider the case `zero => simp`. Consider the case `add w w' _ _ h1 h2 => rw [map_add, h1, h2]`. Consider the case `smul c w _ h => rw [map_smul, h]`.
-/
theorem xc_of_X (hf : IsDualF F0 f) {x : (VS D).V} (hx : x ∈ F0.X) : xcL F0 f x = x := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, rfl⟩ := hw
    rw [xcL_apply]
    simp [hT_f_e hf]
  | zero => simp
  | add w w' _ _ h1 h2 => rw [map_add, h1, h2]
  | smul c w _ h => rw [map_smul, h]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨c, rfl⟩` from `hw`. Rewrite using `[ycL_apply]`. Simplify using `[hf.1]`.

Consider the case `zero => simp`. Consider the case `add w w' _ _ h1 h2 => rw [map_add, h1, h2]`. Consider the case `smul c w _ h => rw [map_smul, h]`.
-/
theorem yc_of_span (hf : IsDualF F0 f) {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range f)) :
    ycL F0 f y = y := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, rfl⟩ := hw
    rw [ycL_apply]
    simp [hf.1]
  | zero => simp
  | add w w' _ _ h1 h2 => rw [map_add, h1, h2]
  | smul c w _ h => rw [map_smul, h]

/- English proof (translation)
Simplify using `[xcL_apply, hu]`.
-/
theorem xc_of_perpf {u : (VS D).V} (hu : ∀ a, (VS D).hT (f a) u = 0) : xcL F0 f u = 0 := by
  simp [xcL_apply, hu]

/- English proof (translation)
Establish `: ∀ b, (VS D).hT (F0.e b) u = 0` using `fun b => hu _ (e_mem_X F0 b)`. Simplify using `[ycL_apply, this]`.
-/
theorem yc_of_perp {u : (VS D).V} (hu : u ∈ perpS (VS D) F0.X) : ycL F0 f u = 0 := by
  have : ∀ b, (VS D).hT (F0.e b) u = 0 := fun b => hu _ (e_mem_X F0 b)
  simp [ycL_apply, this]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem w' hw`. Take `⟨a, rfl⟩` from `hw`. Conclude with `hT_e_yc hf a w`. Consider the case `zero => simp`.

Consider the case `add w₁ w₂ _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c w₁ _ h => simp [h]`.
-/
theorem hX_yc (hf : IsDualF F0 f) {x : (VS D).V} (hx : x ∈ F0.X) (w : (VS D).V) :
    (VS D).hT x (ycL F0 f w) = (VS D).hT x w := by
  induction hx using Submodule.span_induction with
  | mem w' hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hT_e_yc hf a w
  | zero => simp
  | add w₁ w₂ _ _ h1 h2 => simp [h1, h2]
  | smul c w₁ _ h => simp [h]

/- English proof (translation)
Rewrite using `[hT_swap D]`. It suffices to establish `h : (VS D).hT y p = 0 by rw [h, star_zero]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨a, rfl⟩` from `hw`.

Conclude with `hp a`. Consider the case `zero => simp`. Consider the case `add w₁ w₂ _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c w₁ _ h => simp [h]`.
-/
theorem hperpf_span {p : (VS D).V} (hp : ∀ a, (VS D).hT (f a) p = 0) {y : (VS D).V}
    (hy : y ∈ Submodule.span D.host.E (Set.range f)) : (VS D).hT p y = 0 := by
  rw [hT_swap D]
  suffices h : (VS D).hT y p = 0 by rw [h, star_zero]
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hp a
  | zero => simp
  | add w₁ w₂ _ _ h1 h2 => simp [h1, h2]
  | smul c w₁ _ h => simp [h]

/- English proof (translation)
Apply `hperpf_span _ hy'` to reduce the goal to its premises. Introduce `a`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨b, rfl⟩` from `hw`.

Conclude with `hf.2 a b`. Consider the case `zero => simp`. Consider the case `add w₁ w₂ _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c w₁ _ h => simp [h]`.
-/
theorem hspan_span (hf : IsDualF F0 f) {y y' : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range f))
    (hy' : y' ∈ Submodule.span D.host.E (Set.range f)) : (VS D).hT y y' = 0 := by
  apply hperpf_span _ hy'
  intro a
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    exact hf.2 a b
  | zero => simp
  | add w₁ w₂ _ _ h1 h2 => simp [h1, h2]
  | smul c w₁ _ h => simp [h]

/- English proof (translation)
Establish `hu : ∀ a, (VS D).hT (f a) (p - xcL F0 f p) = 0`. Introduce `a`. Rewrite using `[map_sub, hT_f_xc hf, sub_self]`. Establish `h1 : (VS D).hT (p - xcL F0 f p) (ycL F0 f w) = 0` using `hperpf_span hu (yc_mem_span w)`. Establish `h2 : (VS D).hT (xcL F0 f p) (ycL F0 f w) = (VS D).hT (xcL F0 f p) w` using `hX_yc hf (xc_mem_X p) w`.

Rewrite `h1` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Rewrite using `[h1, h2]`.
-/
theorem hT_yc_right (hf : IsDualF F0 f) (p w : (VS D).V) :
    (VS D).hT p (ycL F0 f w) = (VS D).hT (xcL F0 f p) w := by
  have hu : ∀ a, (VS D).hT (f a) (p - xcL F0 f p) = 0 := by
    intro a
    rw [map_sub, hT_f_xc hf, sub_self]
  have h1 : (VS D).hT (p - xcL F0 f p) (ycL F0 f w) = 0 := hperpf_span hu (yc_mem_span w)
  have h2 : (VS D).hT (xcL F0 f p) (ycL F0 f w) = (VS D).hT (xcL F0 f p) w := hX_yc hf (xc_mem_X p) w
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
  rw [h1, h2]

/- English proof (translation)
Establish `A1` using `hT_yc_right hf (v - ycL F0 f v) w`. Establish `A2 : (VS D).hT (ycL F0 f v) (w - ycL F0 f w) = star ((VS D).hT (xcL F0 f (w - ycL F0 f w)) v)`. Rewrite using `[hT_swap D, hT_yc_right hf]`. Establish `A3 : (VS D).hT (ycL F0 f v) (ycL F0 f w) = 0` using `hspan_span hf (yc_mem_span v) (yc_mem_span w)`. Establish `e : (VS D).hT v w = (VS D).hT ((v - ycL F0 f v) + ycL F0 f v) ((w - ycL F0 f w) + ycL F0 f w)`.

Rewrite using `[sub_add_cancel, sub_add_cancel]`. Rewrite using `[e, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, A1, A2, A3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_split (hf : IsDualF F0 f) (v w : (VS D).V) :
    (VS D).hT v w = (VS D).hT (v - ycL F0 f v) (w - ycL F0 f w) + (VS D).hT (xcL F0 f (v - ycL F0 f v)) w +
      star ((VS D).hT (xcL F0 f (w - ycL F0 f w)) v) := by
  have A1 := hT_yc_right hf (v - ycL F0 f v) w
  have A2 : (VS D).hT (ycL F0 f v) (w - ycL F0 f w) = star ((VS D).hT (xcL F0 f (w - ycL F0 f w)) v) := by
    rw [hT_swap D, hT_yc_right hf]
  have A3 : (VS D).hT (ycL F0 f v) (ycL F0 f w) = 0 := hspan_span hf (yc_mem_span v) (yc_mem_span w)
  have e : (VS D).hT v w = (VS D).hT ((v - ycL F0 f v) + ycL F0 f v) ((w - ycL F0 f w) + ycL F0 f w) := by
    rw [sub_add_cancel, sub_add_cancel]
  rw [e, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, A1, A2, A3]
  ring

/- English proof (translation)
The claim follows from `mem_perp_of F0 (fun a => by rw [map_sub, hT_e_yc hf, sub_self])`.
-/
theorem sub_yc_perp (hf : IsDualF F0 f) (v : (VS D).V) : v - ycL F0 f v ∈ perpS (VS D) F0.X :=
  mem_perp_of F0 (fun a => by rw [map_sub, hT_e_yc hf, sub_self])

end Frame

section Maps

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
variable {f f' : Fin D.R.rS → (VS D).V}

def pL (hf : IsDualF F0 f) : (VS D).V →ₗ[D.host.E] WbQ D F0 :=
  (nX D F0).mkQ ∘ₗ (LinearMap.id - ycL F0 f).codRestrict (perpS (VS D) F0.X) (fun v => sub_yc_perp hf v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pL_apply (hf : IsDualF F0 f) (v : (VS D).V) :
    pL hf v = Submodule.Quotient.mk ⟨v - ycL F0 f v, sub_yc_perp hf v⟩ := rfl

def iotaL (hf' : IsDualF F0 f') : WbQ D F0 →ₗ[D.host.E] (VS D).V :=
  (nX D F0).liftQ ((perpS (VS D) F0.X).subtype - xcL F0 f' ∘ₗ (perpS (VS D) F0.X).subtype) (by
    intro w hw
    have hw' : (w : (VS D).V) ∈ F0.X := Submodule.mem_comap.1 hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      xc_of_X hf' hw', sub_self])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaL_mk (hf' : IsDualF F0 f') (w : perpS (VS D) F0.X) :
    iotaL hf' (Submodule.Quotient.mk w) = w.1 - xcL F0 f' w.1 := rfl

/- English proof (translation)
Proceed by induction on `m using Submodule.Quotient.induction_on with | H w => ?_`. Rewrite using `[iotaL_mk]`. Conclude with `Submodule.sub_mem _ w.2 (X_le_perp F0 (xc_mem_X _))`.
-/
theorem iotaL_perp (hf' : IsDualF F0 f') (m : WbQ D F0) : iotaL hf' m ∈ perpS (VS D) F0.X := by
  induction m using Submodule.Quotient.induction_on with | H w => ?_
  rw [iotaL_mk]
  exact Submodule.sub_mem _ w.2 (X_le_perp F0 (xc_mem_X _))

/- English proof (translation)
Proceed by induction on `m using Submodule.Quotient.induction_on with | H w => ?_`. Rewrite using `[iotaL_mk, map_sub, hT_f_xc hf', sub_self]`.
-/
theorem iotaL_f (hf' : IsDualF F0 f') (m : WbQ D F0) (a : Fin D.R.rS) : (VS D).hT (f' a) (iotaL hf' m) = 0 := by
  induction m using Submodule.Quotient.induction_on with | H w => ?_
  rw [iotaL_mk, map_sub, hT_f_xc hf', sub_self]

/- English proof (translation)
Proceed by induction on `m using Submodule.Quotient.induction_on with | H w => ?_`. Proceed by induction on `m' using Submodule.Quotient.induction_on with | H w' => ?_`. Rewrite using `[iotaL_mk, iotaL_mk, hWb_mk]`. Establish `h1 : (VS D).hT (xcL F0 f' w.1) w'.1 = 0` using `hX_perp F0 (xc_mem_X _) w'.2`. Establish `h2 : (VS D).hT w.1 (xcL F0 f' w'.1) = 0` using `hperp_X F0 w.2 (xc_mem_X _)`.

Establish `h3 : (VS D).hT (xcL F0 f' w.1) (xcL F0 f' w'.1) = 0` using `hX_X F0 (xc_mem_X _) (xc_mem_X _)`. Rewrite using `[map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iotaL_hT (hf' : IsDualF F0 f') (m m' : WbQ D F0) :
    (VS D).hT (iotaL hf' m) (iotaL hf' m') = hWb D F0 m m' := by
  induction m using Submodule.Quotient.induction_on with | H w => ?_
  induction m' using Submodule.Quotient.induction_on with | H w' => ?_
  rw [iotaL_mk, iotaL_mk, hWb_mk]
  have h1 : (VS D).hT (xcL F0 f' w.1) w'.1 = 0 := hX_perp F0 (xc_mem_X _) w'.2
  have h2 : (VS D).hT w.1 (xcL F0 f' w'.1) = 0 := hperp_X F0 w.2 (xc_mem_X _)
  have h3 : (VS D).hT (xcL F0 f' w.1) (xcL F0 f' w'.1) = 0 := hX_X F0 (xc_mem_X _) (xc_mem_X _)
  rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, h1, h2, h3]
  ring

/- English proof (translation)
Rewrite using `[iotaL_mk, xc_of_perpf hw, sub_zero]`.
-/
theorem iotaL_of_perpf (hf' : IsDualF F0 f') (w : perpS (VS D) F0.X) (hw : ∀ a, (VS D).hT (f' a) w.1 = 0) :
    iotaL hf' (Submodule.Quotient.mk w) = w.1 := by
  rw [iotaL_mk, xc_of_perpf hw, sub_zero]

def gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (hf : IsDualF F0 f) (hf' : IsDualF F0 f') :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  xcL F0 f ∘ₗ (LinearMap.id - ycL F0 f) + iotaL hf' ∘ₗ σ ∘ₗ pL hf + ycL F0 f'

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gL_apply (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (hf : IsDualF F0 f) (hf' : IsDualF F0 f') (v : (VS D).V) :
    gL σ hf hf' v = xcL F0 f (v - ycL F0 f v) + iotaL hf' (σ (pL hf v)) + ycL F0 f' v := rfl

variable (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (hf : IsDualF F0 f) (hf' : IsDualF F0 f')

/- English proof (translation)
Rewrite using `[gL_apply, map_add, map_add, yc_of_perp (X_le_perp F0 (xc_mem_X _)), yc_of_perp (iotaL_perp hf' _), yc_of_span hf' (yc_mem_span _), zero_add, zero_add]`.
-/
theorem gL_yc (v : (VS D).V) : ycL F0 f' (gL σ hf hf' v) = ycL F0 f' v := by
  rw [gL_apply, map_add, map_add, yc_of_perp (X_le_perp F0 (xc_mem_X _)), yc_of_perp (iotaL_perp hf' _),
    yc_of_span hf' (yc_mem_span _), zero_add, zero_add]

/- English proof (translation)
Rewrite using `[gL_yc, gL_apply, add_sub_cancel_right]`.
-/
theorem gL_sub_yc (v : (VS D).V) :
    gL σ hf hf' v - ycL F0 f' (gL σ hf hf' v) = xcL F0 f (v - ycL F0 f v) + iotaL hf' (σ (pL hf v)) := by
  rw [gL_yc, gL_apply, add_sub_cancel_right]

/- English proof (translation)
Rewrite using `[map_add, xc_of_X hf' (xc_mem_X _), xc_of_perpf (iotaL_f hf' _), add_zero]`.
-/
theorem gL_xc (v : (VS D).V) :
    xcL F0 f' (xcL F0 f (v - ycL F0 f v) + iotaL hf' (σ (pL hf v))) = xcL F0 f (v - ycL F0 f v) := by
  rw [map_add, xc_of_X hf' (xc_mem_X _), xc_of_perpf (iotaL_f hf' _), add_zero]

/- English proof (translation)
Rewrite using `[gL_apply, map_add, map_add, hX_X F0 hx (xc_mem_X _), hX_perp F0 hx (iotaL_perp hf' _), hX_yc hf' hx, zero_add, zero_add]`.
-/
theorem hX_gL {x : (VS D).V} (hx : x ∈ F0.X) (w : (VS D).V) :
    (VS D).hT x (gL σ hf hf' w) = (VS D).hT x w := by
  rw [gL_apply, map_add, map_add, hX_X F0 hx (xc_mem_X _), hX_perp F0 hx (iotaL_perp hf' _), hX_yc hf' hx,
    zero_add, zero_add]

/- English proof (translation)
Rewrite using `[hT_split hf' (gL σ hf hf' v) (gL σ hf hf' w), hT_split hf v w, gL_sub_yc, gL_sub_yc, gL_xc, gL_xc, hX_gL σ hf hf' (xc_mem_X _), hX_gL σ hf hf' (xc_mem_X _)]`. Use `congr 2`. Establish `h1` using `hX_X F0 (xc_mem_X (f := f) (v - ycL F0 f v)) (xc_mem_X (f := f) (w - ycL F0 f w))`. Establish `h2` using `hX_perp F0 (xc_mem_X (f := f) (v - ycL F0 f v)) (iotaL_perp hf' (σ (pL hf w)))`. Establish `h3` using `hperp_X F0 (iotaL_perp hf' (σ (pL hf v))) (xc_mem_X (f := f) (w - ycL F0 f w))`.

Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, h2, h3, iotaL_hT, hσ, pL_apply, pL_apply, hWb_mk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gL_isom (hσ : ∀ m m', hWb D F0 (σ m) (σ m') = hWb D F0 m m') (v w : (VS D).V) :
    (VS D).hT (gL σ hf hf' v) (gL σ hf hf' w) = (VS D).hT v w := by
  rw [hT_split hf' (gL σ hf hf' v) (gL σ hf hf' w), hT_split hf v w, gL_sub_yc, gL_sub_yc, gL_xc, gL_xc,
    hX_gL σ hf hf' (xc_mem_X _), hX_gL σ hf hf' (xc_mem_X _)]
  congr 2
  have h1 := hX_X F0 (xc_mem_X (f := f) (v - ycL F0 f v)) (xc_mem_X (f := f) (w - ycL F0 f w))
  have h2 := hX_perp F0 (xc_mem_X (f := f) (v - ycL F0 f v)) (iotaL_perp hf' (σ (pL hf w)))
  have h3 := hperp_X F0 (iotaL_perp hf' (σ (pL hf v))) (xc_mem_X (f := f) (w - ycL F0 f w))
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, h2, h3, iotaL_hT, hσ,
    pL_apply, pL_apply, hWb_mk]
  ring

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `m hm`. Apply `(VS D).nondeg.2 m` to reduce the goal to its premises. Introduce `x`. Rewrite using `[← gL_isom σ hf hf' hσ x m, hm, map_zero]`.
-/
theorem gL_inj (hσ : ∀ m m', hWb D F0 (σ m) (σ m') = hWb D F0 m m') : Function.Injective (gL σ hf hf') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  apply (VS D).nondeg.2 m
  intro x
  rw [← gL_isom σ hf hf' hσ x m, hm, map_zero]

/- English proof (translation)
Establish `hp : pL hf x = 0`. Rewrite using `[pL_apply, Submodule.Quotient.mk_eq_zero]`. Use `show x - ycL F0 f x ∈ F0.X`. Rewrite using `[yc_of_perp (X_le_perp F0 hx), sub_zero]`. Conclude with `hx`.

Rewrite using `[gL_apply, hp, map_zero, map_zero, yc_of_perp (X_le_perp F0 hx), yc_of_perp (X_le_perp F0 hx), sub_zero, xc_of_X hf hx, add_zero, add_zero]`.
-/
theorem gL_X {x : (VS D).V} (hx : x ∈ F0.X) : gL σ hf hf' x = x := by
  have hp : pL hf x = 0 := by
    rw [pL_apply, Submodule.Quotient.mk_eq_zero]
    show x - ycL F0 f x ∈ F0.X
    rw [yc_of_perp (X_le_perp F0 hx), sub_zero]
    exact hx
  rw [gL_apply, hp, map_zero, map_zero, yc_of_perp (X_le_perp F0 hx), yc_of_perp (X_le_perp F0 hx), sub_zero,
    xc_of_X hf hx, add_zero, add_zero]

/- English proof (translation)
Establish `hy : ycL F0 f u = 0` using `yc_of_perp (mem_perp_of F0 hue)`. Establish `hy' : ycL F0 f' u = 0` using `yc_of_perp (mem_perp_of F0 hue)`. Establish `hp : pL hf u = Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩`. Rewrite using `[pL_apply]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hy]`. Rewrite using `[gL_apply, hp, hy, hy', sub_zero, xc_of_perpf huf, zero_add, add_zero]`.
-/
theorem gL_perpf {u : (VS D).V} (hue : ∀ a, (VS D).hT (F0.e a) u = 0) (huf : ∀ a, (VS D).hT (f a) u = 0) :
    gL σ hf hf' u = iotaL hf' (σ (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩)) := by
  have hy : ycL F0 f u = 0 := yc_of_perp (mem_perp_of F0 hue)
  have hy' : ycL F0 f' u = 0 := yc_of_perp (mem_perp_of F0 hue)
  have hp : pL hf u = Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ := by
    rw [pL_apply]
    congr 1
    apply Subtype.ext
    simp [hy]
  rw [gL_apply, hp, hy, hy', sub_zero, xc_of_perpf huf, zero_add, add_zero]

/- English proof (translation)
Establish `hp : pL hf y = 0`. Rewrite using `[pL_apply, Submodule.Quotient.mk_eq_zero]`. Use `show y - ycL F0 f y ∈ F0.X`. Rewrite using `[yc_of_span hf hy, sub_self]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[gL_apply, hp, map_zero, map_zero, yc_of_span hf hy, sub_self, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem gL_span {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range f)) :
    gL σ hf hf' y = ycL F0 f' y := by
  have hp : pL hf y = 0 := by
    rw [pL_apply, Submodule.Quotient.mk_eq_zero]
    show y - ycL F0 f y ∈ F0.X
    rw [yc_of_span hf hy, sub_self]
    exact Submodule.zero_mem _
  rw [gL_apply, hp, map_zero, map_zero, yc_of_span hf hy, sub_self, map_zero]
  simp

end Maps

section Split

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def IsSplitF (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f : Fin D.R.rS → (VS D).V) : Prop :=
  IsDualF F0 f ∧ (∀ a, (VS D).hT (f a) F0.z = 0) ∧
    ∀ v ∈ Λ, ∃ x u y : (VS D).V, x ∈ Λ ∧ x ∈ F0.X ∧ u ∈ Λ ∧ (∀ a, (VS D).hT (F0.e a) u = 0) ∧
      (∀ a, (VS D).hT (f a) u = 0) ∧ y ∈ Λ ∧ y ∈ Submodule.span D.host.E (Set.range f) ∧ v = x + u + y

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]`.
-/
theorem mem_dual_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

/- English proof (translation)
Establish `: y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ`. Establish `h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ` using `hΛ`. Rewrite using `[h]`. Conclude with `hy`. Conclude with `mem_dual_iff.1 this x hx`.
-/
theorem int_of_unimod {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {x y : (VS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : (VS D).hT x y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
    have h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hΛ
    rw [h]; exact hy
  exact mem_dual_iff.1 this x hx

variable {F0}

/- English proof (translation)
Establish `h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ₂ = Λ₂` using `hu₂`. Rewrite using `[← h, mem_dual_iff]`. Introduce `l hl`. Take `⟨x, u, y, hxΛ, hxX, _, _, huf, _, hyS, rfl⟩` from `hs.2.2 l hl`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hX_yc hs.1 hxX, hperpf_span huf (yc_mem_span w), hspan_span hs.1 hyS (yc_mem_span w), add_zero, add_zero]`.

Conclude with `int_of_unimod hu₁ (hX x hxΛ hxX) hw`.
-/
theorem yc_mem {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V} {f₂ : Fin D.R.rS → (VS D).V}
    (hs : IsSplitF F0 Λ₂ f₂) (hu₁ : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ₁)
    (hu₂ : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ₂) (hX : ∀ x, x ∈ Λ₂ → x ∈ F0.X → x ∈ Λ₁)
    {w : (VS D).V} (hw : w ∈ Λ₁) : ycL F0 f₂ w ∈ Λ₂ := by
  have h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ₂ = Λ₂ := hu₂
  rw [← h, mem_dual_iff]
  intro l hl
  obtain ⟨x, u, y, hxΛ, hxX, _, _, huf, _, hyS, rfl⟩ := hs.2.2 l hl
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hX_yc hs.1 hxX,
    hperpf_span huf (yc_mem_span w), hspan_span hs.1 hyS (yc_mem_span w), add_zero, add_zero]
  exact int_of_unimod hu₁ (hX x hxΛ hxX) hw

/- English proof (translation)
Take `⟨x, u, y, _, hxX, huΛ, hue, huf, _, hyS, rfl⟩` from `hs.2.2 w hw`. Establish `hup : u ∈ perpS (VS D) F0.X` using `mem_perp_of F0 hue`. Establish `hyp : y ∈ perpS (VS D) F0.X`. Establish `e : y = x + u + y - x - u` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (Submodule.sub_mem _ hwp (X_le_perp F0 hxX)) hup`. Establish `hy0 : y = 0` using `by rw [← yc_of_span hs.1 hyS, yc_of_perp hyp]`. Substitute `hy0` using the available equality. Establish `e : x + u + 0 - xcL F0 f (x + u + 0) = u`. Rewrite using `[add_zero, map_add, xc_of_X hs.1 hxX, xc_of_perpf huf]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `⟨huΛ, hue, huf⟩`.
-/
theorem perp_sub_xc {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f : Fin D.R.rS → (VS D).V}
    (hs : IsSplitF F0 Λ f) {w : (VS D).V} (hw : w ∈ Λ) (hwp : w ∈ perpS (VS D) F0.X) :
    w - xcL F0 f w ∈ Λ ∧ (∀ a, (VS D).hT (F0.e a) (w - xcL F0 f w) = 0) ∧
      ∀ a, (VS D).hT (f a) (w - xcL F0 f w) = 0 := by
  obtain ⟨x, u, y, _, hxX, huΛ, hue, huf, _, hyS, rfl⟩ := hs.2.2 w hw
  have hup : u ∈ perpS (VS D) F0.X := mem_perp_of F0 hue
  have hyp : y ∈ perpS (VS D) F0.X := by
    have e : y = x + u + y - x - u := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hwp (X_le_perp F0 hxX)) hup
  have hy0 : y = 0 := by rw [← yc_of_span hs.1 hyS, yc_of_perp hyp]
  subst hy0
  have e : x + u + 0 - xcL F0 f (x + u + 0) = u := by
    rw [add_zero, map_add, xc_of_X hs.1 hxX, xc_of_perpf huf]
    abel
  rw [e]
  exact ⟨huΛ, hue, huf⟩

end Split

def RowSplitF : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ f : Fin D.R.rS → (VS D).V, IsSplitF F0 Λ f

section Main

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem XLam_mem_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ XLam Λ (lf D F0) ↔ x ∈ Λ ∧ x ∈ F0.X := Iff.rfl

/- English proof (translation)
Introduce `v hv`. Take `⟨x, u, y, hxΛ, hxX, huΛ, hue, huf, hyΛ, hyS, rfl⟩` from `hs.2.2 v hv`. Rewrite using `[map_add, map_add]`. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[gL_X _ hs.1 hs'.1 hxX]`.

Conclude with `(hX x hxX).1 hxΛ`. Rewrite using `[gL_perpf _ hs.1 hs'.1 hue huf]`. Establish `hm : (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ : WbQ D F0) ∈ Mof D F0 Λ` using `Submodule.mem_map.2 ⟨⟨u, mem_perp_of F0 hue⟩, huΛ, rfl⟩`. Establish `hm' : σ (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩) ∈ Mof D F0 Λ'`. Rewrite using `[← hM]`.

Conclude with `Submodule.mem_map.2 ⟨_, hm, rfl⟩`. Take `⟨w, hw, hwm⟩` from `Submodule.mem_map.1 hm'`. Establish `hw' : (w : (VS D).V) ∈ Λ'` using `hw`. Rewrite using `[LinearEquiv.coe_coe, ← hwm]`. Conclude with `(perp_sub_xc hs' hw' w.2).1`.

Rewrite using `[gL_span _ hs.1 hs'.1 hyS]`. Conclude with `yc_mem hs' hu hu' (fun x hx hxX => (hX x hxX).2 hx) hyΛ`.
-/
theorem gL_maps {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {f f' : Fin D.R.rS → (VS D).V}
    (hs : IsSplitF F0 Λ f) (hs' : IsSplitF F0 Λ' f')
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (hu' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ')
    (hX : ∀ x, x ∈ F0.X → (x ∈ Λ ↔ x ∈ Λ'))
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hM : Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ') :
    ∀ v ∈ Λ, gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 v ∈ Λ' := by
  intro v hv
  obtain ⟨x, u, y, hxΛ, hxX, huΛ, hue, huf, hyΛ, hyS, rfl⟩ := hs.2.2 v hv
  rw [map_add, map_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · rw [gL_X _ hs.1 hs'.1 hxX]
    exact (hX x hxX).1 hxΛ
  · rw [gL_perpf _ hs.1 hs'.1 hue huf]
    have hm : (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ : WbQ D F0) ∈ Mof D F0 Λ :=
      Submodule.mem_map.2 ⟨⟨u, mem_perp_of F0 hue⟩, huΛ, rfl⟩
    have hm' : σ (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩) ∈ Mof D F0 Λ' := by
      rw [← hM]
      exact Submodule.mem_map.2 ⟨_, hm, rfl⟩
    obtain ⟨w, hw, hwm⟩ := Submodule.mem_map.1 hm'
    have hw' : (w : (VS D).V) ∈ Λ' := hw
    rw [LinearEquiv.coe_coe, ← hwm]
    exact (perp_sub_xc hs' hw' w.2).1
  · rw [gL_span _ hs.1 hs'.1 hyS]
    exact yc_mem hs' hu hu' (fun x hx hxX => (hX x hxX).2 hx) hyΛ

/- English proof (translation)
Introduce `v' hv'`. Take `⟨x, u, y, hxΛ, hxX, huΛ, hue, huf, hyΛ, hyS, rfl⟩` from `hs'.2.2 v' hv'`. Establish `gx : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 x = x` using `gL_X _ hs.1 hs'.1 hxX`. Establish `hyc : ycL F0 f y ∈ Λ` using `yc_mem hs hu' hu (fun x hx hxX => (hX x hxX).1 hx) hyΛ`. Establish `gy : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 (ycL F0 f y) = y`.

Rewrite using `[gL_span _ hs.1 hs'.1 (yc_mem_span y)]`. Establish `: ycL F0 f' (ycL F0 f y) = ycL F0 f' y`. Rewrite using `[ycL_apply F0 f' (ycL F0 f y), ycL_apply F0 f' y]`. Conclude with `Finset.sum_congr rfl (fun b _ => by rw [hT_e_yc hs.1])`. Rewrite using `[this, yc_of_span hs'.1 hyS]`.

Establish `hm' : (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ : WbQ D F0) ∈ Mof D F0 Λ'` using `Submodule.mem_map.2 ⟨⟨u, mem_perp_of F0 hue⟩, huΛ, rfl⟩`. Rewrite `hm'` using `[← hM]`. Take `⟨m, hm, hmσ⟩` from `Submodule.mem_map.1 hm'`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.1 hm`. Establish `hwΛ : (w : (VS D).V) ∈ Λ` using `hw`.

Take `⟨hu0Λ, hu0e, hu0f⟩` from `perp_sub_xc hs hwΛ w.2`. Establish `hmk : ((nX D F0).mkQ.restrictScalars (𝓞 D.host.E)) w = (Submodule.Quotient.mk ⟨w.1 - xcL F0 f w.1, mem_perp_of F0 hu0e⟩ : WbQ D F0)` using `by show (Submodule.Quotient.mk w : WbQ D F0) = _`. Rewrite using `[Submodule.Quotient.eq]`. Use `show w.1 - (w.1 - xcL F0 f w.1) ∈ F0.X`. Rewrite using `[sub_sub_cancel]`.

Conclude with `xc_mem_X _`. Establish `gu : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 (w.1 - xcL F0 f w.1) = u`. Rewrite using `[gL_perpf _ hs.1 hs'.1 hu0e hu0f]`. Establish `h1 : (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (Submodule.Quotient.mk ⟨w.1 - xcL F0 f w.1, mem_perp_of F0 hu0e⟩) = Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩`. Rewrite using `[← hmk]`.

Conclude with `hmσ`. Rewrite using `[h1, iotaL_of_perpf hs'.1 _ huf]`. Establish `hxΛ' : x ∈ Λ` using `(hX x hxX).2 hxΛ`. Use `⟨x + (w.1 - xcL F0 f w.1) + ycL F0 f y, Submodule.add_mem _ (Submodule.add_mem _ hxΛ' hu0Λ) hyc, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, gx, gu, gy]`.
-/
theorem gL_onto {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {f f' : Fin D.R.rS → (VS D).V}
    (hs : IsSplitF F0 Λ f) (hs' : IsSplitF F0 Λ' f')
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (hu' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ')
    (hX : ∀ x, x ∈ F0.X → (x ∈ Λ ↔ x ∈ Λ'))
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hM : Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ') :
    ∀ v' ∈ Λ', ∃ v ∈ Λ, gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 v = v' := by
  intro v' hv'
  obtain ⟨x, u, y, hxΛ, hxX, huΛ, hue, huf, hyΛ, hyS, rfl⟩ := hs'.2.2 v' hv'

  have gx : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 x = x := gL_X _ hs.1 hs'.1 hxX

  have hyc : ycL F0 f y ∈ Λ := yc_mem hs hu' hu (fun x hx hxX => (hX x hxX).1 hx) hyΛ
  have gy : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 (ycL F0 f y) = y := by
    rw [gL_span _ hs.1 hs'.1 (yc_mem_span y)]
    have : ycL F0 f' (ycL F0 f y) = ycL F0 f' y := by
      rw [ycL_apply F0 f' (ycL F0 f y), ycL_apply F0 f' y]
      exact Finset.sum_congr rfl (fun b _ => by rw [hT_e_yc hs.1])
    rw [this, yc_of_span hs'.1 hyS]

  have hm' : (Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ : WbQ D F0) ∈ Mof D F0 Λ' :=
    Submodule.mem_map.2 ⟨⟨u, mem_perp_of F0 hue⟩, huΛ, rfl⟩
  rw [← hM] at hm'
  obtain ⟨m, hm, hmσ⟩ := Submodule.mem_map.1 hm'
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hm
  have hwΛ : (w : (VS D).V) ∈ Λ := hw
  obtain ⟨hu0Λ, hu0e, hu0f⟩ := perp_sub_xc hs hwΛ w.2
  have hmk : ((nX D F0).mkQ.restrictScalars (𝓞 D.host.E)) w =
      (Submodule.Quotient.mk ⟨w.1 - xcL F0 f w.1, mem_perp_of F0 hu0e⟩ : WbQ D F0) := by
    show (Submodule.Quotient.mk w : WbQ D F0) = _
    rw [Submodule.Quotient.eq]
    show w.1 - (w.1 - xcL F0 f w.1) ∈ F0.X
    rw [sub_sub_cancel]
    exact xc_mem_X _
  have gu : gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 (w.1 - xcL F0 f w.1) = u := by
    rw [gL_perpf _ hs.1 hs'.1 hu0e hu0f]
    have h1 : (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0)
        (Submodule.Quotient.mk ⟨w.1 - xcL F0 f w.1, mem_perp_of F0 hu0e⟩) =
        Submodule.Quotient.mk ⟨u, mem_perp_of F0 hue⟩ := by
      rw [← hmk]
      exact hmσ
    rw [h1, iotaL_of_perpf hs'.1 _ huf]
  have hxΛ' : x ∈ Λ := (hX x hxX).2 hxΛ
  refine ⟨x + (w.1 - xcL F0 f w.1) + ycL F0 f y,
    Submodule.add_mem _ (Submodule.add_mem _ hxΛ' hu0Λ) hyc, ?_⟩
  rw [map_add, map_add, gx, gu, gy]

end Main

/- English proof (translation)
Introduce `D u F0 Λ Λ' hΛ hΛ' σ hσ hM`. Take `⟨f, hs⟩` from `hS D u F0 Λ hΛ`. Take `⟨f', hs'⟩` from `hS D u F0 Λ' hΛ'`. Establish `hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ` using `hΛ.2.1.2.1`. Establish `hu' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ'` using `hΛ'.2.1.2.1`.

Establish `e : XLam Λ (lf D F0) = XLam Λ' (lf D F0)` using `hΛ.2.2.trans hΛ'.2.2.symm`. Establish `hX : ∀ x, x ∈ F0.X → (x ∈ Λ ↔ x ∈ Λ')`. Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : x ∈ XLam Λ (lf D F0)` using `XLam_mem_iff.2 ⟨h, hx⟩`. Rewrite `h1` using `[e]`. Conclude with `(XLam_mem_iff.1 h1).1`. Introduce `h`. Establish `h1 : x ∈ XLam Λ' (lf D F0)` using `XLam_mem_iff.2 ⟨h, hx⟩`.

Rewrite `h1` using `[← e]`. Conclude with `(XLam_mem_iff.1 h1).1`. Establish `hσi : ∀ m m', hWb D F0 ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) m) ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) m') = hWb D F0 m m'` using `fun m m' => hσ.1 m m'`. Establish `hinj` using `gL_inj (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 hσi`. Establish `hco : ⇑(LinearEquiv.ofInjectiveEndo _ hinj) = gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1` using `LinearEquiv.coe_ofInjectiveEndo _ hinj`.

Use `⟨LinearEquiv.ofInjectiveEndo _ hinj, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[hco]`. Conclude with `gL_isom _ hs.1 hs'.1 hσi x y`. Introduce `j`.

Establish `hge : ∀ i, ((LinearEquiv.ofInjectiveEndo _ hinj : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) (F0.e i) = F0.e i`. Introduce `i`. Rewrite using `[LinearEquiv.coe_coe, hco]`. Conclude with `gL_X _ hs.1 hs'.1 (e_mem_X F0 i)`. Rewrite using `[FlagG.Xa, Submodule.map_span, Set.image_image]`.

Use `congr 1`. Conclude with `Set.image_congr (fun i _ => hge i)`. Rewrite using `[hco, gL_perpf _ hs.1 hs'.1 F0.z_orth hs.2.1]`. Establish `hz : (Submodule.Quotient.mk ⟨F0.z, mem_perp_of F0 F0.z_orth⟩ : WbQ D F0) = zbar D F0` using `rfl`. Establish `hσz : (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (zbar D F0) = zbar D F0` using `hσ.2`.

Rewrite using `[hz, hσz, zbar, iotaL_of_perpf hs'.1 _ hs'.2.1]`. Use extensionality with `v'`. Rewrite using `[Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Use `gL_maps hs hs' hu hu' hX σ hM v hv` as an intermediate fact. Rewrite using `[LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hco]`. Conclude with `this`. Introduce `hv'`. Take `⟨v, hv, hgv⟩` from `gL_onto hs hs' hu hu' hX σ hM v' hv'`.

Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hco]`. Conclude with `hgv`.
-/
theorem rowClassBack_of (hS : RowSplitF) : RowClassBack := by
  intro D u F0 Λ Λ' hΛ hΛ' σ hσ hM
  obtain ⟨f, hs⟩ := hS D u F0 Λ hΛ
  obtain ⟨f', hs'⟩ := hS D u F0 Λ' hΛ'
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hu' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ' := hΛ'.2.1.2.1
  have e : XLam Λ (lf D F0) = XLam Λ' (lf D F0) := hΛ.2.2.trans hΛ'.2.2.symm
  have hX : ∀ x, x ∈ F0.X → (x ∈ Λ ↔ x ∈ Λ') := by
    intro x hx
    constructor
    · intro h
      have h1 : x ∈ XLam Λ (lf D F0) := XLam_mem_iff.2 ⟨h, hx⟩
      rw [e] at h1
      exact (XLam_mem_iff.1 h1).1
    · intro h
      have h1 : x ∈ XLam Λ' (lf D F0) := XLam_mem_iff.2 ⟨h, hx⟩
      rw [← e] at h1
      exact (XLam_mem_iff.1 h1).1
  have hσi : ∀ m m', hWb D F0 ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) m) ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) m') =
      hWb D F0 m m' := fun m m' => hσ.1 m m'
  have hinj := gL_inj (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 hσi
  have hco : ⇑(LinearEquiv.ofInjectiveEndo _ hinj) = gL (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) hs.1 hs'.1 :=
    LinearEquiv.coe_ofInjectiveEndo _ hinj
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y
    rw [hco]
    exact gL_isom _ hs.1 hs'.1 hσi x y
  · intro j
    have hge : ∀ i, ((LinearEquiv.ofInjectiveEndo _ hinj : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
        (VS D).V →ₗ[D.host.E] (VS D).V) (F0.e i) = F0.e i := by
      intro i
      rw [LinearEquiv.coe_coe, hco]
      exact gL_X _ hs.1 hs'.1 (e_mem_X F0 i)
    rw [FlagG.Xa, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr (fun i _ => hge i)
  · rw [hco, gL_perpf _ hs.1 hs'.1 F0.z_orth hs.2.1]
    have hz : (Submodule.Quotient.mk ⟨F0.z, mem_perp_of F0 F0.z_orth⟩ : WbQ D F0) = zbar D F0 := rfl
    have hσz : (σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) (zbar D F0) = zbar D F0 := hσ.2
    rw [hz, hσz, zbar, iotaL_of_perpf hs'.1 _ hs'.2.1]
  · ext v'
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := gL_maps hs hs' hu hu' hX σ hM v hv
      rw [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hco]
      exact this
    · intro hv'
      obtain ⟨v, hv, hgv⟩ := gL_onto hs hs' hu hu' hX σ hM v' hv'
      refine ⟨v, hv, ?_⟩
      rw [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hco]
      exact hgv

/- English proof (translation)
The claim follows from `rowClass_of (rowClassBack_of hS)`.
-/
theorem rowClass_of_split (hS : RowSplitF) : RowClass := rowClass_of (rowClassBack_of hS)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
