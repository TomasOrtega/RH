import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RegSeqKer

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (s : L.Sec)

/- English proof (translation)
The claim follows from `zhom_ext fun V u i => by change _ = zcoord ((mulSecOfEq F (zofSec s) h).app V ((twistZAddIso F hL h').hom.app V u)) i rw [zcoord_map_app, cutHom_app F hL s i inf_le_right, zcoord_mulSecOfEq_app, zcoord_twistZAddIso_hom_app, zchartEquiv_apply, zfun_zofSec]`.
-/
theorem map_cutHom {l m : ℤ} (h : l + 1 = m) (h' : -1 + m = l) :
    Twist.map (lbZPow L m) (GlobalTheory.cutHom F hL s) =
      (twistZAddIso F hL h').hom ≫ mulSecOfEq F (zofSec s) h :=
  zhom_ext fun V u i => by
    change _ = zcoord ((mulSecOfEq F (zofSec s) h).app V ((twistZAddIso F hL h').hom.app V u)) i
    rw [zcoord_map_app, cutHom_app F hL s i inf_le_right, zcoord_mulSecOfEq_app, zcoord_twistZAddIso_hom_app,
      zchartEquiv_apply, zfun_zofSec]

/- English proof (translation)
Establish `h' : -1 + m = l` using `by omega`. Rewrite using `[← cancel_epi (twistZAddIso F hL h').hom, ← Category.assoc, ← map_cutHom hL F s h h', Limits.comp_zero]`. Conclude with `((cutComplex F hL s).map (twistFunctor (lbZPow L m))).zero`.
-/
theorem mul_comp_π {l m : ℤ} (h : l + 1 = m) :
    mulSecOfEq F (zofSec s) h ≫ Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s) = 0 := by
  have h' : -1 + m = l := by omega
  rw [← cancel_epi (twistZAddIso F hL h').hom, ← Category.assoc, ← map_cutHom hL F s h h', Limits.comp_zero]
  exact ((cutComplex F hL s).map (twistFunctor (lbZPow L m))).zero

def twistComplex {l m : ℤ} (h : l + 1 = m) : ShortComplex Y.Modules :=
  .mk (mulSecOfEq F (zofSec s) h) (Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s)) (mul_comp_π hL F s h)

/- English proof (translation)
Establish `h' : -1 + m = l` using `by omega`. Use `ShortComplex.shortExact_of_iso ?_ (Twist.shortExact_map (isLB_lbZPow hL m) (shortExact_cutComplex F hL s))` and prove the remaining obligations. Use `ShortComplex.isoMk (twistZAddIso F hL h') (Iso.refl _) (Iso.refl _) ?_ ?_` and prove the remaining obligations. Conclude with `(map_cutHom hL F s h h').symm.trans (Category.comp_id _).symm`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.
-/
theorem shortExact_twistComplex [Mono (GlobalTheory.cutHom F hL s)] {l m : ℤ} (h : l + 1 = m) :
    (twistComplex hL F s h).ShortExact := by
  have h' : -1 + m = l := by omega
  refine ShortComplex.shortExact_of_iso ?_
    (Twist.shortExact_map (isLB_lbZPow hL m) (shortExact_cutComplex F hL s))
  refine ShortComplex.isoMk (twistZAddIso F hL h') (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (map_cutHom hL F s h h').symm.trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/- English proof (translation)
Introduce `j hj q hq` and use `cohOn.subsingleton₃ (shortExact_twistComplex hL F s (l := j - 1) (m := j) (by omega)) ⊤ q (hv j (by omega) q hq) (hv (j - 1) (by omega) (q + 1) (by omega))`.
-/
theorem vanishFrom_cut [Mono (GlobalTheory.cutHom F hL s)] {j₀ : ℤ} (hv : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL s) (j₀ + 1) := fun j hj q hq =>
  cohOn.subsingleton₃ (shortExact_twistComplex hL F s (l := j - 1) (m := j) (by omega)) ⊤ q
    (hv j (by omega) q hq) (hv (j - 1) (by omega) (q + 1) (by omega))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `t F j₀ l _ _ _ f hf`. Use `⟨fun i => i.elim0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.univ_eq_empty, Finset.sum_empty]`.

Use `section_eq_zero_of_germ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨W, hW, m, hm⟩` from `hf x`. Rewrite `hm` using `[Finset.univ_eq_empty, Finset.sum_empty]`. Rewrite using `[← TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hW, hm, map_zero]`. Consider the case `succ n ih`.

Introduce `t F j₀ l hr hv hj f hf`. Rewrite `hr` using `[List.ofFn_succ, regSeq_cons]`. Take `⟨hm0, hr⟩` from `hr`. Establish `nat : ∀ (a : L.Sec) (W : Y.Opens) (u : Γ(GlobalTheory.twistZ F L l, W)), (Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W ((mulSecOfEq F (zofSec a) rfl).app W u) = (mulSecOfEq (cut F hL (t 0)) (zofSec a) rfl).app W ((Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W u)` using `fun a W u => by`. Rewrite using `[app_app, app_app, mulSecOfEq_naturality]`.

Establish `hS` using `shortExact_twistComplex hL F (t 0) (l := l) rfl`. Use `hS.mono_f` as an intermediate fact. Establish `hex : ∀ W : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) (rfl : l + 1 = l + 1)).app W) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W)` using `exact_app_of_exact_of_mono hS.exact`. Take `⟨m', hm'⟩` from `ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l hr (vanishFrom_cut hL F (t 0) hv) (by push_cast at hj; omega) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app ⊤ f) fun y => by`. Take `⟨W, hW, m, hm⟩` from `hf y`.

Use `⟨W, hW, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W (m i.succ), ?_⟩` and prove the remaining obligations. Rewrite using `[← app_res, hm, Fin.sum_univ_succ, map_add, (hex W).apply_apply_eq_zero, zero_add, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => nat _ _ _`. Establish `hlift : ∀ i, ∃ u : Γ(GlobalTheory.twistZ F L l, ⊤), (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app ⊤ u = m' i` using `fun i => by`. Establish `hi` using `i.pos`.

Conclude with `cohOn.app_surjective (shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)) ⊤ (hv (l - 1) (by push_cast at hj; omega) 1 one_pos) (m' i)`. Use `choose u hu using hlift`. Take `⟨v, hv'⟩` from `(hex ⊤ (f - ∑ i, (mulSecOfEq F (zofSec (t i.succ)) rfl).app ⊤ (u i))).1 (by`. Rewrite using `[map_sub, hm', map_sum, sub_eq_zero]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [nat, hu])`.

Use `⟨Fin.cons v u, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hv', sub_add_cancel]`.
-/
theorem exists_global (n : ℕ) : ∀ (t : Fin n → L.Sec) (F : Y.Modules) (j₀ l : ℤ), RegSeq hL F (List.ofFn t) →
    VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤),
    (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)),
      (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f =
        ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app W (m i)) →
    ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app ⊤ (m i) := by
  induction n with
  | zero =>
    intro t F j₀ l _ _ _ f hf
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    obtain ⟨W, hW, m, hm⟩ := hf x
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hW, hm, map_zero]
  | succ n ih =>
    intro t F j₀ l hr hv hj f hf
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have nat : ∀ (a : L.Sec) (W : Y.Opens) (u : Γ(GlobalTheory.twistZ F L l, W)),
        (Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W ((mulSecOfEq F (zofSec a) rfl).app W u) =
          (mulSecOfEq (cut F hL (t 0)) (zofSec a) rfl).app W
            ((Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W u) := fun a W u => by
      rw [app_app, app_app, mulSecOfEq_naturality]
    have hS := shortExact_twistComplex hL F (t 0) (l := l) rfl
    have := hS.mono_f
    have hex : ∀ W : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) (rfl : l + 1 = l + 1)).app W)
        ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W) := exact_app_of_exact_of_mono hS.exact
    obtain ⟨m', hm'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l hr (vanishFrom_cut hL F (t 0) hv)
      (by push_cast at hj; omega) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app ⊤ f) fun y => by
        obtain ⟨W, hW, m, hm⟩ := hf y
        refine ⟨W, hW, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W (m i.succ), ?_⟩
        rw [← app_res, hm, Fin.sum_univ_succ, map_add, (hex W).apply_apply_eq_zero, zero_add, map_sum]
        exact Finset.sum_congr rfl fun i _ => nat _ _ _
    have hlift : ∀ i, ∃ u : Γ(GlobalTheory.twistZ F L l, ⊤),
        (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app ⊤ u = m' i := fun i => by
      have hi := i.pos
      exact cohOn.app_surjective (shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)) ⊤
        (hv (l - 1) (by push_cast at hj; omega) 1 one_pos) (m' i)
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex ⊤ (f - ∑ i, (mulSecOfEq F (zofSec (t i.succ)) rfl).app ⊤ (u i))).1 (by
      rw [map_sub, hm', map_sum, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [nat, hu])
    refine ⟨Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqKer

/- English proof (translation)
Introduce `_ _ _ _ _ _ hL n t F _ j₀ l` and use `RegSeqKer.exists_global hL n t F j₀ l`.
-/
theorem GlobalTheory.HSCore.exists_global_of_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) :=
  fun _ _ _ _ _ _ hL n t F _ j₀ l => RegSeqKer.exists_global hL n t F j₀ l
