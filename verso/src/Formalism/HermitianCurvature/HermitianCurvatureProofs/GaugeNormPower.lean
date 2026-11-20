import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R

def lstN (K m : ℕ) (y : Fin K → ℝ) : List ℝ :=
  List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

/- English proof (translation)
Unfold `lstN`. Rewrite using `[List.ofFn_succ]`. Use `congr 1`. Rewrite using `[dif_pos (by omega)]`. Establish `e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a` using `Fin.ext (by simp)`.

Rewrite using `[e, Function.update_self]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Rewrite using `[dif_pos (by simp; omega), dif_pos (by omega)]`.

Establish `e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e, Function.update_of_ne]`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem lstN_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    lstN K ((a : ℕ) + 1) (Function.update y a t) = t :: lstN K a y := by
  unfold lstN
  rw [List.ofFn_succ]
  congr 1
  · rw [dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dif_pos (by simp; omega), dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

/- English proof (translation)
Unfold `lstN`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`.

Use `ext`. Simplify using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lstN_full (K : ℕ) (z : Fin K → ℝ) : lstN K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold lstN
  congr 1
  funext b
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

/- English proof (translation)
The claim follows from `| [], h => h | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)`.
-/
theorem cutWord_plusW {P : M.Par} {l0 : ℕ} {w : List C.Letter} :
    ∀ ys : List ℝ, KB.CutWord P l0 (KB.plusW ys w) → KB.CutWord P l0 w
  | [], h => h
  | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def aaIter {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (F0 : B.Mat k r → (Wq →L[ℂ] Wp)) :
    List ℝ → B.Mat k r → (Wq →L[ℂ] Wp)
  | [] => F0
  | y :: ys => aaTop Bs y (aaIter Bs F0 ys)

def aPIter {V : Type} [AddCommGroup V] [Module ℂ V] {r : ℕ} (L : R.LevelData (Q.Pr V) r) : List ℝ → V → V
  | [], Ψ => Ψ
  | y :: ys, Ψ => (TL.aP L (y : ℂ)).1 (aPIter L ys Ψ)

/- English proof (translation)
The claim follows from `| [] => ⟨hF0, hΨ⟩ | y :: ys => by obtain ⟨h1, h2⟩ := aaIter_rad hRA P Bs X μ L st l0 hD hF0 hΨ ys obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1 exact ⟨h3, h4 _ h2⟩`.
-/
theorem aaIter_rad (hRA : RadAATop) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ)
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) {F0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF0 : KB.CptCoef Bs F0) {Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (hΨ : Top.IsRadOf P Bs Ψ F0) :
    ∀ ys : List ℝ, KB.CptCoef Bs (aaIter Bs F0 ys) ∧ Top.IsRadOf P Bs (aPIter L ys Ψ) (aaIter Bs F0 ys)
  | [] => ⟨hF0, hΨ⟩
  | y :: ys => by
    obtain ⟨h1, h2⟩ := aaIter_rad hRA P Bs X μ L st l0 hD hF0 hΨ ys
    obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1
    exact ⟨h3, h4 _ h2⟩

/- English proof (translation)
The claim follows from `| [], _ => rfl | y :: ys, hc => by have ih := rad_plusW hWS P p X μ L st hD w Φ e ys (cutWord_tail hc) have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e) exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) ih)`.
-/
theorem rad_plusW (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter)
    (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (e : Ix (Fin w.length)) :
    ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      P5.act ((Fr.ofWord L st (D.positionted (KB.plusW ys w))).F * P5.bTall L (D.positionted (KB.plusW ys w)))
          (Top.firstStateVector Φ) (KB.firstSt ys e) =
        aPIter L ys (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e)
  | [], _ => rfl
  | y :: ys, hc => by
    have ih := rad_plusW hWS P p X μ L st hD w Φ e ys (cutWord_tail hc)
    have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e)
    exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) ih)

end deg

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

/- English proof (translation)
Introduce `hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut`. Take `⟨X, μ, L, st, hD, hTL⟩` from `p.hΘ`. Establish `hcw : KB.CutWord P p.l0 w` using `cutWord_plusW _ (hcut fun _ => 0)`. Take `⟨F0, hF0, hF0eq, hV0⟩` from `Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw`. Take `⟨Φ, hΦ⟩` from `radExists p hF`.

Establish `hΨ` using `isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq`. Establish `hIt` using `aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ`. Establish `hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) → p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) = p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)])`. Introduce `ys hc`. Take `⟨Fn, hFn, hFneq, hVn⟩` from `Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc`.

Rewrite using `[hVn]`. Establish `hrad` using `isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq`. Rewrite `hrad` using `[rad_plusW hWS P p X μ L st hD w Φ e ys hc]`. Conclude with `vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _`. Use `set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)]) with hW`.

Establish `hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W`. Introduce `a y`. Take `⟨c, hc, hpoly⟩` from `hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1`. Use `⟨c, hc, fun t' => ?_⟩` and prove the remaining obligations. Simplify using `only [hW]`.

Rewrite using `[lstN_succ]`. Conclude with `hpoly t'`. Establish `hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i)` using `fun a => hgrid _`. Establish `hE` using `Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)`. Rewrite `hE` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Establish `hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)])`. Simplify using `only [hW, lstN, List.ofFn_zero, aaIter]`. Rewrite using `[hV0]`. Rewrite `hE` using `[hW0]`. Rewrite using `[hE]`.

Use `Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)` and prove the remaining obligations. Simplify using `only [hW]`. Rewrite using `[lstN_full]`. Establish `e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) = fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b)`. Use function extensionality and compare the values at `b`.

Simplify using `[Equiv.arrowCongr_apply, Fin.revPerm]`. Establish `e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) = ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a)`. Use `Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)` and prove the remaining obligations. Simplify using `[Equiv.arrowCongr_apply, Fin.revPerm]`. Rewrite using `[e1, e2, hVit _ (hcut _)]`.
-/
theorem degree_top_of_parts : PBN.DegTopOfParts := by
  intro hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  have hcw : KB.CutWord P p.l0 w := cutWord_plusW _ (hcut fun _ => 0)
  obtain ⟨F0, hF0, hF0eq, hV0⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw
  obtain ⟨Φ, hΦ⟩ := radExists p hF
  have hΨ := isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq
  have hIt := aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ

  have hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) =
        p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)]) := by
    intro ys hc
    obtain ⟨Fn, hFn, hFneq, hVn⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc
    rw [hVn]
    have hrad := isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq
    rw [rad_plusW hWS P p X μ L st hD w Φ e ys hc] at hrad
    exact vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _
  set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)])
    with hW
  have hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W := by
    intro a y
    obtain ⟨c, hc, hpoly⟩ := hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1
    refine ⟨c, hc, fun t' => ?_⟩
    simp only [hW]
    rw [lstN_succ]
    exact hpoly t'
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hE
  have hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) := by
    simp only [hW, lstN, List.ofFn_zero, aaIter]
    rw [hV0]
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW]
  rw [lstN_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2, hVit _ (hcut _)]

end Formalism.FourierDecayAlt.P
