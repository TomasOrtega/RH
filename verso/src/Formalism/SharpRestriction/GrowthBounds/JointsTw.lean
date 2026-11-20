import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

def SysUAt (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (low : ℝ) : Prop :=
  ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
    (dG_spec : _) (om : _) (Y5 : Formalism.MainNotions.FormalGroupSystem.Pend (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg)
      (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
    Formalism.MainNotions.FormalGroupSystem.VolumeRatio₂ D _ Y5 ∧ Formalism.MainNotions.FormalGroupSystem.adm11 D _ Y5 ∧ Formalism.MainNotions.FormalGroupSystem.LowTermBound D _ Y5 ∧
    Function.Injective (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) ∧
    ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
      (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → ∀ j < D.R.m, Y5.LowAt j v (Fn v (j + 1))) ∧
      low ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg),
        Fn v j) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

open Classical in

/- English proof (translation)
Introduce `VVs VV' hVVs hVV' F hF`. Use `set p := D.what₂.places.resChar w with hpdef`. Take `⟨hFact, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hU2, h11, h5D, hinjK, Fn, hFn, hdiv⟩` from `hPuw`. Take `⟨hmm, -, -, -, hinj, -⟩` from `hLT u w hg`. Use `set vOf := Y.vOf u w hg with hvOf`.

Establish `hVVr : VV' ⊆ reps X p` using `hVV'.trans hVVs`. Use `set A : Prop := 1 ≤ Real.logb p (2 * L.sc.a) with hA`. Set `Gn : Fin (D.gat u w hg).P.nV → ℕ → ℝ` to `fun v j => if h : ∃ t0 ∈ VV', vOf t0 = v then (if A then gU X K (aL L) (bL L) p j (Classical.choose h) else min (Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) (Formalism.MainNotions.FormalGroupSy …`. Set `PRn : Fin (D.gat u w hg).P.nV → ℕ → ℝ` to `fun v j => if h : ∃ t0 ∈ VV', vOf t0 = v then (if A then Pr X K (bL L) p j (Classical.choose h) else Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) else 0`. Set `G0n : Fin (D.gat u w hg).P.nV → ℕ → ℝ` to `fun v j => if h : ∃ t0 ∈ reps X p, vOf t0 = v then (if A then max (g0 X K (aL L) (bL L) p j (Classical.choose h)) 0 else 0) else Fn v j`.

Set `S : Fin (D.gat u w hg).P.nV → ℝ` to `fun v => ∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, max (Gn v j - PRn v j - G0n v j) 0`. Set `BB` to `VV'.image vOf`. Establish `chV : ∀ t0 ∈ VV', ∀ h : ∃ t1 ∈ VV', vOf t1 = vOf t0, Classical.choose h = t0`. Introduce `t0 ht0 h`. Take `⟨h1, h2⟩` from `Classical.choose_spec h`.

Conclude with `hinj (hVVr h1) (hVVr ht0) h2`. Establish `chR : ∀ t0 ∈ reps X p, ∀ h : ∃ t1 ∈ reps X p, vOf t1 = vOf t0, Classical.choose h = t0`. Introduce `t0 ht0 h`. Take `⟨h1, h2⟩` from `Classical.choose_spec h`. Conclude with `hinj h1 ht0 h2`.

Establish `hlift : ∀ j, j ∈ SizeData₂.lifts D ↔ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm`. Introduce `j`. Rewrite using `[hmm]`. Both sides reduce to the same expression. Establish `hI : ∀ t0 ∈ VV', ∀ j ∈ SizeData₂.lifts D, max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤ max (Gn (vOf t0) j - PRn (vOf t0) j) (G0n (vOf t0) j)`.

Introduce `t0 ht0 j hj`. Establish `h : ∃ t1 ∈ VV', vOf t1 = vOf t0` using `⟨t0, ht0, rfl⟩`. Establish `h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0` using `⟨t0, hVVr ht0, rfl⟩`. Simplify using `only [Gn, PRn, G0n, dif_pos h, dif_pos h', chV t0 ht0 h, chR t0 (hVVr ht0) h']`. Distinguish the cases in `hAA : A`.

Simplify using `only [if_pos hAA]`. Conclude with `le_rfl`. Simplify using `only [if_neg hAA]`. Take `⟨h1, h2⟩` from `hLarge w (lt_of_not_ge hAA) t0 (hVVr ht0) j hj`. Establish `: max (g0 X K (aL L) (bL L) p j t0) 0 = 0` using `max_eq_right h2`.

Rewrite using `[this]`. Conclude with `le_trans (max_le h1 le_rfl) (le_max_right _ _)`. Establish `hII : ∀ t0 ∈ reps X p, ∀ j ∈ SizeData₂.lifts D, max (g0 X K (aL L) (bL L) p j t0) 0 ≤ G0n (vOf t0) j`. Introduce `t0 ht0 j hj`. Establish `h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0` using `⟨t0, ht0, rfl⟩`.

Simplify using `only [G0n, dif_pos h', chR t0 ht0 h']`. Distinguish the cases in `hAA : A`. Simplify using `only [if_pos hAA]`. Conclude with `le_rfl`. Simplify using `only [if_neg hAA]`.

Conclude with `(max_eq_right (hLarge w (lt_of_not_ge hAA) t0 ht0 j hj).2).le`. Establish `c1 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Gn v j ≤ Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j`. Introduce `v hv j hj`. Take `⟨t0, ht0, rfl⟩` from `Finset.mem_image.1 hv`. Establish `h : ∃ t1 ∈ VV', vOf t1 = vOf t0` using `⟨t0, ht0, rfl⟩`.

Simplify using `only [Gn, dif_pos h, chV t0 ht0 h]`. Distinguish the cases in `hAA : A`. Simplify using `only [if_pos hAA]`. Conclude with `(hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).1`. Simplify using `only [if_neg hAA]`.

Conclude with `min_le_left _ _`. Establish `c2 : ∀ v, ∀ j < (Y.Fl u w hg).mm, Y5.LowAt j v (G0n v (j + 1))`. Introduce `v j hj`. Distinguish the cases in `h : ∃ t0 ∈ reps X p, vOf t0 = v`. Take `⟨t0, ht0, rfl⟩` from `h`.

Use `Formalism.MainNotions.FormalGroupSystem.lowAt_max D _ Y5 hU2 h11 (vOf t0) j hj _ ?_` and prove the remaining obligations. Establish `h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0` using `⟨t0, ht0, rfl⟩`. Simplify using `only [G0n, dif_pos h', chR t0 ht0 h']`. Distinguish the cases in `hAA : A`. Simplify using `only [if_pos hAA]`.

Conclude with `max_le_max ((hNum hT hLT u w hg hAA t0 ht0 (j + 1) ((hlift (j + 1)).2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩))).2.1) le_rfl`. Simplify using `only [if_neg hAA]`. Conclude with `le_max_right _ _`. Simplify using `only [G0n, dif_neg h]`. Use `hFn v (fun hv => h ?_) j (by rw [← hmm]; exact hj)` and prove the remaining obligations.

Take `⟨t0, ht0, h0⟩` from `Finset.mem_image.1 hv`. Conclude with `⟨t0, ht0, h0⟩`. Establish `c3 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j ≤ PRn v j`. Introduce `v hv j hj`. Take `⟨t0, ht0, rfl⟩` from `Finset.mem_image.1 hv`.

Establish `h : ∃ t1 ∈ VV', vOf t1 = vOf t0` using `⟨t0, ht0, rfl⟩`. Simplify using `only [PRn, dif_pos h, chV t0 ht0 h]`. Distinguish the cases in `hAA : A`. Simplify using `only [if_pos hAA]`. Conclude with `(hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).2.2`.

Simplify using `only [if_neg hAA]`. Conclude with `le_rfl`. Establish `hnodup : (VV'.toList.map vOf).Nodup` using `List.Nodup.map_on (fun a ha b hb hab => hinj (hVVr (Finset.mem_toList.1 ha)) (hVVr (Finset.mem_toList.1 hb)) hab) (Finset.nodup_toList VV')`. Establish `hmem : yProd Y u w hg VV' F ∈ (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg) (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om).Iprod S BB`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Establish `heq : yProd Y u w hg VV' F = (VV'.toList.map vOf).foldr (fun v F' => ((D.gat u w hg).yv v)^[(Y.Fl u w hg).mm] F') F`. Unfold `yProd`. Rewrite using `[foldr_map_comp, foldr_map', hmm]`. Use `⟨BB, subset_refl _, VV'.toList.map vOf, hnodup, by ext; simp [BB], F, ?_, heq⟩` and prove the remaining obligations. Rewrite using `[Finset.sdiff_self, Finset.sum_empty, zpow_zero]`.

Conclude with `⟨F, hF, one_smul (D.gat u w hg).Kf F⟩`. Establish `hv` using `h5D Gn G0n PRn S BB c1 c2 c3 (fun v _ => le_rfl) _ hmem`. Establish `hv2 : (Y.Ch u w hg).chainK (Y.Fl u w hg).mm (yProd Y u w hg VV' F) ∈ scale ((algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp) ^ ⌈(∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, (∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ Finset.univ \ BB, G0n v j) - ∑ j ∈ Finset.range (Y.Fl u w hg …` using `hv`. Rewrite `hv2` using `[hmm]`. Establish `hj : ∀ j ∈ SizeData₂.lifts D, (∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) + ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 + ∑ v ∈ Finset.univ \ …`.

Introduce `j hjl`. Establish `e1 : ∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤ ∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j)`. Rewrite using `[Finset.sum_image (fun a ha b hb hab => hinj (hVVr ha) (hVVr hb) hab)]`. Conclude with `Finset.sum_le_sum fun t0 ht0 => hI t0 ht0 j hjl`. Establish `hunion : (VVs \ VV') ∪ (reps X p \ VVs) = reps X p \ VV'`.

Use extensionality with `t`. Simplify using `only [Finset.mem_union, Finset.mem_sdiff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨h1, h2⟩ | ⟨h1, h2⟩)`. Conclude with `⟨hVVs h1, h2⟩`.

Conclude with `⟨h1, fun h => h2 (hVV' h)⟩`. Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `h : t ∈ VVs`. Conclude with `Or.inl ⟨h, h2⟩`. Conclude with `Or.inr ⟨h1, h⟩`.

Establish `hdisj : Disjoint (VVs \ VV') (reps X p \ VVs)`. Rewrite using `[Finset.disjoint_left]`. Introduce `t h1 h2`. Conclude with `(Finset.mem_sdiff.1 h2).2 (Finset.mem_sdiff.1 h1).1`. Establish `e2 : (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) + ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 = ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0`.

Rewrite using `[← Finset.sum_union hdisj, hunion]`. Establish `hinjR : Set.InjOn vOf ↑(reps X p \ VV')` using `fun a ha b hb hab => hinj (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 hb).1 hab`. Establish `e3 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 + ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j ≤ ∑ v ∈ Finset.univ \ BB, G0n v j`. Establish `h1 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 ≤ ∑ v ∈ (reps X p \ VV').image vOf, G0n v j`. Rewrite using `[Finset.sum_image hinjR]`.

Conclude with `Finset.sum_le_sum fun t0 ht0 => hII t0 (Finset.mem_sdiff.1 ht0).1 j hjl`. Establish `h2 : ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j = ∑ v ∈ Finset.univ \ (reps X p).image vOf, G0n v j`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hn : ¬ ∃ t0 ∈ reps X p, vOf t0 = v` using `fun ⟨t0, ht0, h0⟩ => (Finset.mem_sdiff.1 hv).2 (Finset.mem_image.2 ⟨t0, ht0, h0⟩)`. Simplify using `only [G0n, dif_neg hn]`.

Establish `hsplit : Finset.univ \ BB = ((reps X p \ VV').image vOf) ∪ (Finset.univ \ (reps X p).image vOf)`. Use extensionality with `v`. Simplify using `only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, BB]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Distinguish the cases in `h : ∃ t0 ∈ reps X p, vOf t0 = v`. Take `⟨t0, ht0, rfl⟩` from `h`. Conclude with `Or.inl ⟨t0, ⟨ht0, fun h' => hv ⟨t0, h', rfl⟩⟩, rfl⟩`. Conclude with `Or.inr h`. Introduce and unpack `(⟨t0, ⟨ht0, hn⟩, rfl⟩ | h)`.

Introduce and unpack `⟨t1, ht1, h1⟩`. Conclude with `hn (hinj (hVVr ht1) ht0 h1 ▸ ht1)`. Introduce and unpack `⟨t1, ht1, rfl⟩`. Conclude with `h ⟨t1, hVVr ht1, rfl⟩`. Establish `hdisj2 : Disjoint ((reps X p \ VV').image vOf) (Finset.univ \ (reps X p).image vOf)`.

Rewrite using `[Finset.disjoint_left]`. Introduce `v h1 h2`. Take `⟨t0, ht0, rfl⟩` from `Finset.mem_image.1 h1`. Conclude with `(Finset.mem_sdiff.1 h2).2 (Finset.mem_image.2 ⟨t0, (Finset.mem_sdiff.1 ht0).1, rfl⟩)`. Rewrite using `[hsplit, Finset.sum_union hdisj2, h2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTB : (∑ j ∈ SizeData₂.lifts D, ((∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) + ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0)) + low ≤ (∑ j ∈ Fi …`. Establish `h1` using `Finset.sum_le_sum hj`. Establish `h2 : low ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)` using `hdiv`.

Unfold `SizeData₂.lifts at h1`. Unfold `SizeData₂.lifts`. Rewrite `h1` using `[Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hvp0 : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp ≠ 0` using `(map_ne_zero_iff _ hinjK).mpr unif.ne_zero`.

Use `⟨vp, unif, scale_pow_mono vp hvp0 _ (Int.ceil_mono ?_) hv2⟩` and prove the remaining obligations. Rewrite using `[← eO_eq_vUnit (D.gat u w hg) vp unif eO eO_spec]`. Conclude with `mul_le_mul_of_nonneg_right hTB (Nat.cast_nonneg _)`.
-/
theorem UAt_of (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (low : ℝ)
    (hT : GatTies D) (hLT : LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hPuw : SysUAt D L X Y u w hg low)
    (hNum : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K)
    (hLarge : ∀ (w : D.what₂.places.Pl), Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) < 1 →
      ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 - Pr X K (bL L) (D.what₂.places.resChar w) j t0 ≤ 0 ∧
        g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤ 0) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.UAt X Y K low u w hg := by
  intro VVs VV' hVVs hVV' F hF
  set p := D.what₂.places.resChar w with hpdef
  obtain ⟨hFact, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hU2, h11, h5D, hinjK, Fn, hFn, hdiv⟩ := hPuw
  obtain ⟨hmm, -, -, -, hinj, -⟩ := hLT u w hg
  set vOf := Y.vOf u w hg with hvOf
  have hVVr : VV' ⊆ reps X p := hVV'.trans hVVs
  set A : Prop := 1 ≤ Real.logb p (2 * L.sc.a) with hA
  let Gn : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ VV', vOf t0 = v then
      (if A then gU X K (aL L) (bL L) p j (Classical.choose h) else min (Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) (Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j)) else 0
  let PRn : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ VV', vOf t0 = v then (if A then Pr X K (bL L) p j (Classical.choose h) else Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) else 0
  let G0n : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ reps X p, vOf t0 = v then
      (if A then max (g0 X K (aL L) (bL L) p j (Classical.choose h)) 0 else 0) else Fn v j
  let S : Fin (D.gat u w hg).P.nV → ℝ := fun v => ∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, max (Gn v j - PRn v j - G0n v j) 0
  let BB := VV'.image vOf
  have chV : ∀ t0 ∈ VV', ∀ h : ∃ t1 ∈ VV', vOf t1 = vOf t0, Classical.choose h = t0 := by
    intro t0 ht0 h
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    exact hinj (hVVr h1) (hVVr ht0) h2
  have chR : ∀ t0 ∈ reps X p, ∀ h : ∃ t1 ∈ reps X p, vOf t1 = vOf t0, Classical.choose h = t0 := by
    intro t0 ht0 h
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    exact hinj h1 ht0 h2
  have hlift : ∀ j, j ∈ SizeData₂.lifts D ↔ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm := by
    intro j; rw [hmm]; rfl

  have hI : ∀ t0 ∈ VV', ∀ j ∈ SizeData₂.lifts D,
      max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        max (Gn (vOf t0) j - PRn (vOf t0) j) (G0n (vOf t0) j) := by
    intro t0 ht0 j hj
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, hVVr ht0, rfl⟩
    simp only [Gn, PRn, G0n, dif_pos h, dif_pos h', chV t0 ht0 h, chR t0 (hVVr ht0) h']
    by_cases hAA : A
    · simp only [if_pos hAA]; exact le_rfl
    · simp only [if_neg hAA]
      obtain ⟨h1, h2⟩ := hLarge w (lt_of_not_ge hAA) t0 (hVVr ht0) j hj
      have : max (g0 X K (aL L) (bL L) p j t0) 0 = 0 := max_eq_right h2
      rw [this]
      exact le_trans (max_le h1 le_rfl) (le_max_right _ _)
  have hII : ∀ t0 ∈ reps X p, ∀ j ∈ SizeData₂.lifts D, max (g0 X K (aL L) (bL L) p j t0) 0 ≤ G0n (vOf t0) j := by
    intro t0 ht0 j hj
    have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [G0n, dif_pos h', chR t0 ht0 h']
    by_cases hAA : A
    · simp only [if_pos hAA]; exact le_rfl
    · simp only [if_neg hAA]; exact (max_eq_right (hLarge w (lt_of_not_ge hAA) t0 ht0 j hj).2).le

  have c1 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Gn v j ≤ Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j := by
    intro v hv j hj
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [Gn, dif_pos h, chV t0 ht0 h]
    by_cases hAA : A
    · simp only [if_pos hAA]; exact (hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).1
    · simp only [if_neg hAA]; exact min_le_left _ _
  have c2 : ∀ v, ∀ j < (Y.Fl u w hg).mm, Y5.LowAt j v (G0n v (j + 1)) := by
    intro v j hj
    by_cases h : ∃ t0 ∈ reps X p, vOf t0 = v
    · obtain ⟨t0, ht0, rfl⟩ := h
      refine Formalism.MainNotions.FormalGroupSystem.lowAt_max D _ Y5 hU2 h11 (vOf t0) j hj _ ?_
      have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
      simp only [G0n, dif_pos h', chR t0 ht0 h']
      by_cases hAA : A
      · simp only [if_pos hAA]
        exact max_le_max ((hNum hT hLT u w hg hAA t0 ht0 (j + 1)
          ((hlift (j + 1)).2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩))).2.1) le_rfl
      · simp only [if_neg hAA]; exact le_max_right _ _
    · simp only [G0n, dif_neg h]
      refine hFn v (fun hv => h ?_) j (by rw [← hmm]; exact hj)
      obtain ⟨t0, ht0, h0⟩ := Finset.mem_image.1 hv
      exact ⟨t0, ht0, h0⟩
  have c3 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j ≤ PRn v j := by
    intro v hv j hj
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [PRn, dif_pos h, chV t0 ht0 h]
    by_cases hAA : A
    · simp only [if_pos hAA]; exact (hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).2.2
    · simp only [if_neg hAA]; exact le_rfl
  have hnodup : (VV'.toList.map vOf).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab => hinj (hVVr (Finset.mem_toList.1 ha)) (hVVr (Finset.mem_toList.1 hb)) hab)
      (Finset.nodup_toList VV')
  have hmem : yProd Y u w hg VV' F ∈ (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg) (Y.Ch u w hg) std vp unif eO eO_spec dG
      dG_spec om).Iprod S BB := by
    apply Submodule.subset_span
    have heq : yProd Y u w hg VV' F =
        (VV'.toList.map vOf).foldr (fun v F' => ((D.gat u w hg).yv v)^[(Y.Fl u w hg).mm] F') F := by
      unfold yProd
      rw [foldr_map_comp, foldr_map', hmm]
    refine ⟨BB, subset_refl _, VV'.toList.map vOf, hnodup, by ext; simp [BB], F, ?_, heq⟩
    rw [Finset.sdiff_self, Finset.sum_empty, zpow_zero]
    exact ⟨F, hF, one_smul (D.gat u w hg).Kf F⟩
  have hv := h5D Gn G0n PRn S BB c1 c2 c3 (fun v _ => le_rfl) _ hmem
  have hv2 : (Y.Ch u w hg).chainK (Y.Fl u w hg).mm (yProd Y u w hg VV' F) ∈
      scale ((algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp) ^
        ⌈(∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, (∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) +
            ∑ v ∈ Finset.univ \ BB, G0n v j) - ∑ j ∈ Finset.range (Y.Fl u w hg).mm, (dG j : ℝ)) * (eO : ℝ)⌉)
        ((Y.Lv u w hg).Int (Y.Fl u w hg).mm) := hv
  rw [hmm] at hv2

  have hj : ∀ j ∈ SizeData₂.lifts D, (∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0)
        (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 + ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j ≤
      ∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ Finset.univ \ BB, G0n v j := by
    intro j hjl
    have e1 : ∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        ∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) := by
      rw [Finset.sum_image (fun a ha b hb hab => hinj (hVVr ha) (hVVr hb) hab)]
      exact Finset.sum_le_sum fun t0 ht0 => hI t0 ht0 j hjl
    have hunion : (VVs \ VV') ∪ (reps X p \ VVs) = reps X p \ VV' := by
      ext t; simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨hVVs h1, h2⟩
        · exact ⟨h1, fun h => h2 (hVV' h)⟩
      · rintro ⟨h1, h2⟩
        by_cases h : t ∈ VVs
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h1, h⟩
    have hdisj : Disjoint (VVs \ VV') (reps X p \ VVs) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact (Finset.mem_sdiff.1 h2).2 (Finset.mem_sdiff.1 h1).1
    have e2 : (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 =
        ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 := by
      rw [← Finset.sum_union hdisj, hunion]
    have hinjR : Set.InjOn vOf ↑(reps X p \ VV') :=
      fun a ha b hb hab => hinj (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 hb).1 hab
    have e3 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 +
        ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j ≤ ∑ v ∈ Finset.univ \ BB, G0n v j := by
      have h1 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 ≤
          ∑ v ∈ (reps X p \ VV').image vOf, G0n v j := by
        rw [Finset.sum_image hinjR]
        exact Finset.sum_le_sum fun t0 ht0 => hII t0 (Finset.mem_sdiff.1 ht0).1 j hjl
      have h2 : ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j =
          ∑ v ∈ Finset.univ \ (reps X p).image vOf, G0n v j := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hn : ¬ ∃ t0 ∈ reps X p, vOf t0 = v := fun ⟨t0, ht0, h0⟩ =>
          (Finset.mem_sdiff.1 hv).2 (Finset.mem_image.2 ⟨t0, ht0, h0⟩)
        simp only [G0n, dif_neg hn]
      have hsplit : Finset.univ \ BB = ((reps X p \ VV').image vOf) ∪ (Finset.univ \ (reps X p).image vOf) := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, BB]
        constructor
        · intro hv
          by_cases h : ∃ t0 ∈ reps X p, vOf t0 = v
          · obtain ⟨t0, ht0, rfl⟩ := h
            exact Or.inl ⟨t0, ⟨ht0, fun h' => hv ⟨t0, h', rfl⟩⟩, rfl⟩
          · exact Or.inr h
        · rintro (⟨t0, ⟨ht0, hn⟩, rfl⟩ | h)
          · rintro ⟨t1, ht1, h1⟩
            exact hn (hinj (hVVr ht1) ht0 h1 ▸ ht1)
          · rintro ⟨t1, ht1, rfl⟩
            exact h ⟨t1, hVVr ht1, rfl⟩
      have hdisj2 : Disjoint ((reps X p \ VV').image vOf) (Finset.univ \ (reps X p).image vOf) := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 h1
        exact (Finset.mem_sdiff.1 h2).2 (Finset.mem_image.2 ⟨t0, (Finset.mem_sdiff.1 ht0).1, rfl⟩)
      rw [hsplit, Finset.sum_union hdisj2, h2]
      linarith
    linarith
  have hTB : (∑ j ∈ SizeData₂.lifts D, ((∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0)
        (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0)) + low ≤
      (∑ j ∈ Finset.Icc 1 D.R.m, (∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ Finset.univ \ BB, G0n v j)) -
        ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
    have h1 := Finset.sum_le_sum hj
    have h2 : low ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j) -
        ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := hdiv
    unfold SizeData₂.lifts at h1
    unfold SizeData₂.lifts
    rw [Finset.sum_add_distrib] at h1
    linarith
  have hvp0 : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp ≠ 0 :=
    (map_ne_zero_iff _ hinjK).mpr unif.ne_zero
  refine ⟨vp, unif, scale_pow_mono vp hvp0 _ (Int.ceil_mono ?_) hv2⟩
  rw [← eO_eq_vUnit (D.gat u w hg) vp unif eO eO_spec]
  exact mul_le_mul_of_nonneg_right hTB (Nat.cast_nonneg _)

/- English proof (translation)
Introduce `hE μ hUs hT hLT u w hg hq`. Conclude with `UAt_of D L X (W.Yt μ) K _ hT hLT u w hg (hP hE μ hUs hT hLT u w hg hq) hNum hLarge`.
-/
theorem unit_bound_of_local_system (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D)
    (W : Formalism.MainNotions.WeilJacquetShalikaLaw.TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ)
    (hP : Formalism.BasicNotions.ErrDefs D L Xe lev K ce → ∀ μ, Formalism.BasicNotions.DV.Used D μ → ∀ (hT : GatTies D), LatTied hT X (W.Yt μ) →
      ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.places.resChar w ∉ Dx.Qp μ →
      SysUAt D L X (W.Yt μ) u w hg (Formalism.MainNotions.WeilJacquetShalikaLaw.lowS L Xe K ce sp u w))
    (hNum : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K)
    (hLarge : ∀ (w : D.what₂.places.Pl), Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) < 1 →
      ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 - Pr X K (bL L) (D.what₂.places.resChar w) j t0 ≤ 0 ∧
        g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤ 0) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.unitBoundAtTwistedPlaces D L X Y K Dx W lev Xe ce sp := by
  intro hE μ hUs hT hLT u w hg hq
  exact UAt_of D L X (W.Yt μ) K _ hT hLT u w hg (hP hE μ hUs hT hLT u w hg hq) hNum hLarge

/- English proof (translation)
The claim follows from `unit_bound_of_local_system D L X Y K Dx W lev Xe ce sp hP hNum (Formalism.MainNotions.G.TopChoiceBounds.hLarge_proved X K hK hPr1 P)`.
-/
theorem unit_bound_of_local_system' (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D)
    (W : Formalism.MainNotions.WeilJacquetShalikaLaw.TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ)
    (hP : Formalism.BasicNotions.ErrDefs D L Xe lev K ce → ∀ μ, Formalism.BasicNotions.DV.Used D μ → ∀ (hT : GatTies D), LatTied hT X (W.Yt μ) →
      ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.places.resChar w ∉ Dx.Qp μ →
      SysUAt D L X (W.Yt μ) u w hg (Formalism.MainNotions.WeilJacquetShalikaLaw.lowS L Xe K ce sp u w))
    (hNum : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K) (hK : K.Nonneg) (hPr1 : 1 ≤ K.Pr1) (P : ParameterChoice' D L) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.unitBoundAtTwistedPlaces D L X Y K Dx W lev Xe ce sp :=
  unit_bound_of_local_system D L X Y K Dx W lev Xe ce sp hP hNum (Formalism.MainNotions.G.TopChoiceBounds.hLarge_proved X K hK hPr1 P)

open Classical in

/- English proof (translation)
Use `unit_bound_of_local_system D L X Y K Dx W lev Xe ce sp (fun hE μ hUs hT hLT u w hg hq => ?_) hNum hLarge` and prove the remaining obligations. Take `⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, Fn, h1, h2⟩` from `h5 hE μ hUs hT hLT u w hg hq`. Establish `hP` using `hS.1 _ _ Y5 hA`. Establish `hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf` using `((D.gat u w hg).P.setting (Y.vOf u w hg 0)).frac_O`. Conclude with `⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hP.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2.2.2.2.2, hP.2.2.2.2.2.2.2.2.2.2, IsFractionRing.injective _ _, Fn, h1, h2⟩`.
-/
theorem unit_bound_of_sum_over_primes (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D)
    (W : Formalism.MainNotions.WeilJacquetShalikaLaw.TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) (hS : Formalism.MainNotions.FormalGroupSystem.Stmt D)
    (h5 : Formalism.BasicNotions.ErrDefs D L Xe lev K ce → ∀ μ, Formalism.BasicNotions.DV.Used D μ → ∀ (hT : GatTies D), LatTied hT X (W.Yt μ) →
      ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.places.resChar w ∉ Dx.Qp μ →
      ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
        (dG_spec : _) (om : _) (Y5 : Formalism.MainNotions.FormalGroupSystem.Pend (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) ((W.Yt μ).Fl u w hg)
          ((W.Yt μ).Lv u w hg) ((W.Yt μ).Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
        Formalism.MainNotions.FormalGroupSystem.admitted D _ Y5 ∧
        ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
          (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg) → ∀ j < D.R.m,
            Y5.LowAt j v (Fn v (j + 1))) ∧
          Formalism.MainNotions.WeilJacquetShalikaLaw.lowS L Xe K ce sp u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
            ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg), Fn v j) -
              ∑ j ∈ Finset.range D.R.m, (dG j : ℝ))
    (hNum : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K)
    (hLarge : ∀ (w : D.what₂.places.Pl), Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) < 1 →
      ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 - Pr X K (bL L) (D.what₂.places.resChar w) j t0 ≤ 0 ∧
        g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤ 0) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.unitBoundAtTwistedPlaces D L X Y K Dx W lev Xe ce sp := by
  refine unit_bound_of_local_system D L X Y K Dx W lev Xe ce sp (fun hE μ hUs hT hLT u w hg hq => ?_) hNum hLarge
  obtain ⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, Fn, h1, h2⟩ := h5 hE μ hUs hT hLT u w hg hq
  have hP := hS.1 _ _ Y5 hA
  have hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
    ((D.gat u w hg).P.setting (Y.vOf u w hg 0)).frac_O
  exact ⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hP.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2.2.2.2.2,
    hP.2.2.2.2.2.2.2.2.2.2, IsFractionRing.injective _ _, Fn, h1, h2⟩

end Formalism.MainNotions.G.Joints
