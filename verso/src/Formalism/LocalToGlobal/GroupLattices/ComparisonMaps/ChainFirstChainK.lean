import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Maps

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpMaps where
  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  li : ∀ j, j ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
    fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a)

variable {c Tw u w h Lv}

/- English proof (translation)
The claim follows from `inj_of_li (M.cmp j) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj)`.
-/
theorem CmpMaps.inj (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j ≤ D.R.m) : Function.Injective (M.cmp j) :=
  inj_of_li (M.cmp j) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj)

variable (Tw u w) in

def KLx (j : ℕ) : ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₗ[D.what₂.LL] ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V :=
  ratMap ((Tw.fm u (D.what₂.muAt w)).emb j) ((Tw.fm u (D.what₂.muAt w)).emb (j + 1))
    ((Tw.fm u (D.what₂.muAt w)).emb_inj (j + 1)) ((D.chTw u (D.what₂.muAt w)).Klin j)

/- English proof (translation)
The claim follows from `ratMap_eq _ _ _ _ x y hxy`.
-/
theorem KLx_eq (j : ℕ) (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V)
    (hxy : (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y =
      (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x)) : KLx Tw u w j x = y :=
  ratMap_eq _ _ _ _ x y hxy

/- English proof (translation)
The claim follows from `LinearMap.ext fun x => KLx_eq j x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)`.
-/
theorem KLx_eq_KL (j : ℕ) (hK : (Tw.fm u (D.what₂.muAt w)).KRat j) :
    KLx Tw u w j = (Tw.fm u (D.what₂.muAt w)).KL j hK :=
  LinearMap.ext fun x => KLx_eq j x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)

variable (Tw) in

def KRatTw : Prop := ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), ∀ j, j < D.R.m → (Tw.fm u (D.what₂.muAt w)).KRat j

open Classical in

def chainFirst (M : CmpMaps c Tw u w h Lv) : Chain Lv where
  Kz j := if hj : j < D.R.m then
      extK (M.cmp j) (M.cmp (j + 1)) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj.le) (KLx Tw u w j)
    else 0

/- English proof (translation)
The claim follows from `dif_pos hj`.
-/
theorem chainFirst_Kz (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j < D.R.m) :
    (chainFirst M).Kz j =
      extK (M.cmp j) (M.cmp (j + 1)) ((Tw.fm u (D.what₂.muAt w)).lat j).b (M.li j hj.le) (KLx Tw u w j) :=
  dif_pos hj

/- English proof (translation)
Rewrite using `[chainFirst_Kz M j hj, extK_apply]`.
-/
theorem chainFirst_apply (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j < D.R.m)
    (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) :
    (chainFirst M).Kz j (M.cmp j x) = M.cmp (j + 1) (KLx Tw u w j x) := by
  rw [chainFirst_Kz M j hj, extK_apply]

/- English proof (translation)
Introduce `j hj x y hxy`. Rewrite using `[chainFirst_apply M j hj, KLx_eq j x y hxy]`.
-/
theorem chainFirst_cmp_K (M : CmpMaps c Tw u w h Lv) : ∀ j, j < D.R.m →
    ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    M.cmp (j + 1) y = (chainFirst M).Kz j (M.cmp j x) := by
  intro j hj x y hxy
  rw [chainFirst_apply M j hj, KLx_eq j x y hxy]

/- English proof (translation)
Rewrite using `[chainFirst_apply M j hj, KLx_eq_KL j hK]`.
-/
theorem chainFirst_KL (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j < D.R.m)
    (hK : (Tw.fm u (D.what₂.muAt w)).KRat j) (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) :
    (chainFirst M).Kz j (M.cmp j x) = M.cmp (j + 1) ((Tw.fm u (D.what₂.muAt w)).KL j hK x) := by
  rw [chainFirst_apply M j hj, KLx_eq_KL j hK]

/- English proof (translation)
Rewrite using `[chainFirst_Kz M j hj]`. Use `extK_unique _ _ _ _ _ (Ch.Kz j) (fun x => ?_) F hF` and prove the remaining obligations. Rewrite using `[KLx_eq_KL j hK]`. Conclude with `(hC x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)).symm`.
-/
theorem chainFirst_unique (M : CmpMaps c Tw u w h Lv) (Ch : Chain Lv) (j : ℕ) (hj : j < D.R.m)
    (hK : (Tw.fm u (D.what₂.muAt w)).KRat j)
    (hC : ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
      (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
      M.cmp (j + 1) y = Ch.Kz j (M.cmp j x))
    (F : Lv.Fm j) (hF : F ∈ spanK (M.cmp j)) : Ch.Kz j F = (chainFirst M).Kz j F := by
  rw [chainFirst_Kz M j hj]
  refine extK_unique _ _ _ _ _ (Ch.Kz j) (fun x => ?_) F hF
  rw [KLx_eq_KL j hK]
  exact (hC x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)).symm

def KLchain : (j : ℕ) → ((Tw.fm u (D.what₂.muAt w)).lat 0).V →ₗ[D.what₂.LL] ((Tw.fm u (D.what₂.muAt w)).lat j).V
  | 0 => LinearMap.id
  | j + 1 => (KLx Tw u w j).comp (KLchain j)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih => show (chainFirst M).Kz j ((chainFirst M).chainK j (M.cmp 0 x)) = _`. Rewrite using `[ih (by omega), chainFirst_apply M j (by omega)]`. Both sides reduce to the same expression.
-/
theorem chainFirst_chainK (M : CmpMaps c Tw u w h Lv) (j : ℕ) (hj : j ≤ D.R.m)
    (x : ((Tw.fm u (D.what₂.muAt w)).lat 0).V) :
    (chainFirst M).chainK j (M.cmp 0 x) = M.cmp j (KLchain j x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (chainFirst M).Kz j ((chainFirst M).chainK j (M.cmp 0 x)) = _
    rw [ih (by omega), chainFirst_apply M j (by omega)]
    rfl

end Maps

section Vram

variable {D : D7} (c : LatCmp D)

def vramC (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn :=
  (Submodule.span (D.gat u w hg).Kf
    (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O

def withVram (Y : LatInst D) : LatInst D := { Y with Vram := vramC c }

/- English proof (translation)
Introduce `_ _ _` and use `rfl`.
-/
theorem withVram_def (Y : LatInst D) : c.VramDef (withVram c Y) := fun _ _ _ => rfl

/- English proof (translation)
Use function extensionality and compare the values at `u w hg`. Conclude with `SetLike.coe_injective (hv u w hg)`.
-/
theorem vram_unique (Y : LatInst D) (hv : c.VramDef Y) : Y.Vram = vramC c := by
  funext u w hg
  exact SetLike.coe_injective (hv u w hg)

end Vram

end Formalism.L2.G.Cmp

end
