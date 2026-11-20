import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.Columns.TiedLv

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

open Classical in

/- English proof (translation)
Use `hX.nonempty_Tau` as an intermediate fact. Establish `e : tauOfR hX hPr u w P = tauOfC w P.1`. Unfold `tauOfR`. Rewrite using `[dif_pos hw]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Distinguish the cases in `hs : seenC Pr u w`. Rewrite using `[if_pos hs]`. Conclude with `(tauOfC_spec hX hPr u w hw P).resolve_right (hs.not_bar hPr _ P)`. Rewrite using `[if_neg hs]`.

Use `(tauOfC_spec hX hPr u w hw P).resolve_left fun h => hs (seenC_of_one hPr (τ := tauOfC w P.1) ?_)` and prove the remaining obligations. Rewrite using `[show pullW (tauOfC w P.1) w = P.1 from h]`. Conclude with `P.2`.
-/
theorem th_pull_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) :
    pullW (tauOfR hX hPr u w P) w = if seenC Pr u w then P.1 else conjPrime₂ P.1 := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dif_pos hw]
    rfl
  rw [e]
  by_cases hs : seenC Pr u w
  · rw [if_pos hs]
    exact (tauOfC_spec hX hPr u w hw P).resolve_right (hs.not_bar hPr _ P)
  · rw [if_neg hs]
    refine (tauOfC_spec hX hPr u w hw P).resolve_left fun h => hs (seenC_of_one hPr (τ := tauOfC w P.1) ?_)
    rw [show pullW (tauOfC w P.1) w = P.1 from h]
    exact P.2

end Gen

variable {d : ColDat} (a : ColArgs d)

open Classical in
/- English proof (translation)
Rewrite using `[att_val_pos d.what₂.places d.plEq hH.val_eq w]`. Establish `h1 : d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x ∈ (d.plEq w).asIdeal ↔ x ∈ (pullW (tauOfR d.hX d.hPr u (d.plEq w) v) (d.plEq w)).asIdeal` using `Iff.rfl`. Rewrite using `[h1, th_pull_tauOf d.hX d.hPr u (d.plEq w) hT v]`. Distinguish the cases in `hs : seenC d.Pr u (d.plEq w)`. Rewrite using `[if_pos hs, if_pos (decide_eq_true hs)]`.

Rewrite using `[if_neg hs, if_neg (by simpa using hs), conjIdeal_asIdeal]`.
-/
theorem valuation_pos_iff_mem_seen (hH : HostHyp d) (u : d.what₂.Word) (w : d.what₂.places.Pl) (hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal)
    (v : {P // P ∈ d.Pr.vT u}) (x : 𝓞 d.X.E) :
    (0 : WithTop ℤ) < d.what₂.places.val w ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) ↔
      x ∈ (if decide (seenC d.Pr u (d.plEq w)) = true then v.1.asIdeal else conjIdeal (K := d.X.E) v.1.asIdeal) := by
  rw [att_val_pos d.what₂.places d.plEq hH.val_eq w]
  have h1 : d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x ∈ (d.plEq w).asIdeal ↔
      x ∈ (pullW (tauOfR d.hX d.hPr u (d.plEq w) v) (d.plEq w)).asIdeal := Iff.rfl
  rw [h1, th_pull_tauOf d.hX d.hPr u (d.plEq w) hT v]
  by_cases hs : seenC d.Pr u (d.plEq w)
  · rw [if_pos hs, if_pos (decide_eq_true hs)]
  · rw [if_neg hs, if_neg (by simpa using hs), conjIdeal_asIdeal]

/- English proof (translation)
Introduce `w hw v x y hy`. Establish `hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal`. Use `att_resChar_mem d.what₂.places d.plEq hH.val_eq w` as an intermediate fact. Rewrite `this` using `[hw]`. Conclude with `this`.

Establish `hy' : y = ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K)`. Apply `d.what₂.embLL.injective` to reduce the goal to its premises. Rewrite using `[hy]`. Use `show d.host.φ₀ _ = d.what₂.embLL (d.embE _)`. Rewrite using `[← hH.embE_φ₀]`.

Both sides reduce to the same expression. Establish `hPv : (atTTied a hH u).Pv v = v.1.asIdeal` using `lv_Pv_eq a hH u v`. Rewrite using `[hy', hPv]`. Conclude with `valuation_pos_iff_mem_seen hH u w hT v x`.
-/
theorem th_seen (hH : HostHyp d) (u : d.what₂.Word) : AtTSeen (atTTied a hH u) := by
  intro w hw v x y hy
  have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
    have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
    rw [hw] at this
    exact this
  have hy' : y = ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) := by
    apply d.what₂.embLL.injective
    rw [hy]
    show d.host.φ₀ _ = d.what₂.embLL (d.embE _)
    rw [← hH.embE_φ₀]
    rfl
  have hPv : (atTTied a hH u).Pv v = v.1.asIdeal := lv_Pv_eq a hH u v
  rw [hy', hPv]
  exact valuation_pos_iff_mem_seen hH u w hT v x

end Formalism.L2.Col
