import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowAlg

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

open MatrixConvolutionPowers

/- English proof (translation)
Introduce `hA hAtP hC hAct hIdem`. Introduce `E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F m hU₁ hU₂ hL hs ht hbi hF hne w₀`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hne` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Take `⟨p, k⟩` from `i`. Use `choose V₁ V₂ hV₁ hV₂ hVU using fun w => exists_level_prod w (U₁ w) (hU₁.1 w).1 (hU₁.1 w).2`. Use `set V : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w) := fun w => (V₁ w).prod (V₂ w) with hVdef`. Establish `hVo : ∀ w, IsOpen (V w : Set (GLw B.a w × GLw B.b w))` using `fun w => by`.

Rewrite using `[hVdef, Subgroup.coe_prod]`. Conclude with `(hV₁ w).1.prod (hV₂ w).1`. Establish `hVK : ∀ w, V w ≤ K2 B.a B.b w` using `fun w => Subgroup.prod_mono (hV₁ w).2.1 (hV₂ w).2.1`. Establish `hVH : ∀ w, IsHecke (V w) (idem (V w))` using `fun w => isHecke_idem (V₁ w) (V₂ w) (hV₁ w) (hV₂ w)`. Establish `hdgH : ∀ w (x y : κ w), IsHecke (V w) (dg V w x y)` using `fun w x y => by`.

Unfold `dg`. Use `split_ifs`. Conclude with `hVH w`. Conclude with `isHecke_zero _`. Establish `hw₀P : w₀.1 ∈ P` using `w₀.2`.

Use `set L0 := only0 L V w₀.1 with hL0`. Use `set L1 := rest1 L V w₀.1 with hL1`. Establish `hL0s : L0.s = L.s` using `by rw [hL0]; rfl`. Establish `hL0t : L0.t = L.t` using `by rw [hL0]; rfl`. Establish `hL1s : L1.s = L.s` using `by rw [hL1]; rfl`.

Establish `hL1t : L1.t = L.t` using `by rw [hL1]; rfl`. Use `clear_value L0 L1`. Establish `hL0ok : L0.Ok P`. Use `⟨fun x y => isTestFunction_modify (hL.1 x y) (P.erase w₀.1) V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL0t]; exact hL.2⟩` and prove the remaining obligations. Unfold `LM.ent split_ifs with hwP`.

Establish `: w = w₀.1`. Assume the negation of the conclusion as `hne'`. Conclude with `hw (Finset.mem_erase.2 ⟨hne', hwP⟩)`. Substitute `this` using the available equality. Simplify using `[hL0, only0]`.

Rewrite using `[hL0s]`. Take `⟨hne', hwP⟩` from `Finset.mem_erase.1 hw`. Unfold `LM.ent`. Rewrite using `[dif_pos hwP]`. Simplify using `only [hL0, only0, if_neg hne']`.

Conclude with `hdgH w _ _`. Establish `hL1ok : L1.Ok P`. Use `⟨fun x y => isTestFunction_modify (hL.1 x y) {w₀.1} V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL1t]; exact hL.2⟩` and prove the remaining obligations. Establish `hne' : w ≠ w₀.1` using `fun h => hw (Finset.mem_singleton.2 h)`. Unfold `LM.ent`.

Use `split_ifs with hwP`. Simplify using `[hL1, rest1, hne']`. Rewrite using `[hL1s]`. Rewrite using `[Finset.mem_singleton.1 hw]`. Unfold `LM.ent`.

Rewrite using `[dif_pos hw₀P]`. Simplify using `only [hL1, rest1, if_true]`. Conclude with `hdgH _ _ _`. Use `set Φ : ∀ w : Pl E, GLw B.a w × GLw B.b w → ℂ := fun w => if w ∈ P then idem (V w) else L.s w with hΦ`. Establish `hΦt : IsTestP Φ`.

Use `isTestFunction_modify (hL.1 (e k) (e k)) P V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [hΦ, if_neg hw, LM.ent, dif_neg hw]`. Simplify using `only [hΦ, if_pos hw]`. Conclude with `hVH w`. Establish `hΨt : IsTestP L.t` using `hL.2`.

Set `Good : (Unit × B.κ → H E B.a B.b → ℂ) → Prop` to `fun G => ∀ i, HasLev (G i) ∧ ∀ j : Slot S, actS Φ L.t j (G i) = G i`. Use `set i₀ : Slot S := Sum.inl ⟨w₀.1, hP w₀.2⟩ with hi₀`. Establish `hform : ∀ G, Good G → ∀ x, convF B.ν (fm S P B e L0) G ((), x) = ∑ y : κ w₀, actP w₀.1 (L.m w₀.1 (e x w₀) y) (G ((), e.symm (Function.update (e x) w₀ y)))`. Introduce `G hG x`. Establish `hQ : Quiet S P B e L0 i₀ G`.

Use `⟨fun w hwP hw x' y' hxy => ?_, fun j hj q x' y' hag => ?_⟩` and prove the remaining obligations. Establish `hne' : w ≠ w₀.1` using `fun h => hw (hP hwP) (by subst h; rfl)`. Simplify using `only [hL0, only0, if_neg hne', dg, if_neg hxy]`. Both sides reduce to the same expression. Take `⟨⟩` from `q`.

Consider the cases of `j with`. Consider the case `inl w'`. Establish `hent : LM.ent P L0 (e x') (e y') w'.1 = Φ w'.1`. Unfold `LM.ent`. Distinguish the cases in `hwP : w'.1 ∈ P`.

Rewrite using `[dif_pos hwP]`. Establish `hne' : w'.1 ≠ w₀.1` using `fun h => hj (by rw [hi₀]; congr 1; exact Subtype.ext h)`. Establish `hxy : e x' ⟨w'.1, hwP⟩ = e y' ⟨w'.1, hwP⟩` using `hag ⟨w'.1, hwP⟩ fun h he => hne' (congrArg Subtype.val (Sum.inl_injective he)).symm`. Simplify using `only [hL0, only0, if_neg hne', dg, hxy, if_true, hΦ, if_pos hwP]`. Rewrite using `[dif_neg hwP]`.

Simplify using `only [hL0, only0, hΦ, if_neg hwP]`. Use `show actP w'.1 (LM.ent P L0 (e x') (e y') w'.1) (G ((), y')) = G ((), y')`. Rewrite using `[hent]`. Conclude with `(hG ((), y')).2 (Sum.inl w')`. Consider the case `inr w' => show actT w'.1 (L0.t w'.1) (G ((), y')) = G ((), y')`.

Rewrite using `[hL0t]`. Conclude with `(hG ((), y')).2 (Sum.inr w')`. Establish `h` using `hAtP E κ S P B e hS hP Unit L0 w₀ G hL0ok (fun i => (hG i).1) hQ () x`. Rewrite using `[h]`. Simplify using `only [hL0, only0, if_true]`.

Establish `hterm : ∀ (x : B.κ) (y : κ w₀) (g : H E B.a B.b → ℂ), HasLev g → (∀ j : Slot S, actS Φ L.t j g = g) → HasLev (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) ∧ ∀ j : Slot S, actS Φ L.t j (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) = actP w₀.1 (L.m w₀.1 (e x w₀) y) g`. Introduce `x y g hg hfix`. Use `set ψ₁ := LM.ent P L (e x) (Function.update (e x) w₀ y) with hψ₁`. Establish `hψt : IsTestP ψ₁` using `hL.1 _ _`. Establish `hψw : ψ₁ w₀.1 = L.m w₀.1 (e x w₀) y`.

Simplify using `only [hψ₁, LM.ent, dif_pos hw₀P, Function.update_self]`. Establish `hT : actP w₀.1 (L.m w₀.1 (e x w₀) y) g = actS ψ₁ L.t i₀ g` using `by show _ = actP w₀.1 (ψ₁ w₀.1) g`. Rewrite using `[hψw]`. Rewrite using `[hT]`. Use `⟨(hAct E B.a B.b S hS ψ₁ L.t ψ₁ L.t hψt hΨt hψt hΨt g g hg hg i₀ i₀).1, fun j => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Establish `key` using `(hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg i₀ i₀).2.2.2`. Rewrite using `[← key]`. Use `show actP w₀.1 (mconv (Φ w₀.1) (ψ₁ w₀.1)) g = actP w₀.1 (ψ₁ w₀.1) g`.

Establish `hΦw : Φ w₀.1 = idem (V w₀.1)` using `by simp only [hΦ, if_pos hw₀P]`. Rewrite using `[hΦw, mconv_idem_left (hVo _) (hVK _) fun v hv g' => ?_]`. Rewrite using `[hψw]`. Conclude with `((hbi w₀.1 hw₀P (e x w₀) y v (hVU w₀.1 hv) g').1)`. Rewrite using `[(hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg j i₀).2.2.1 hj, hfix j]`.

Establish `hact_sum : ∀ (j : Slot S) (s : Finset (κ w₀)) (T : κ w₀ → H E B.a B.b → ℂ), (∀ y, HasLev (T y)) → actS Φ L.t j (∑ y ∈ s, T y) = ∑ y ∈ s, actS Φ L.t j (T y)`. Introduce `j s T hT`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `h0` using `(hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt 0 0 hasLev_zero hasLev_zero j j).2.1 1`.

Simplify using `only [add_zero, one_smul] at h0`. Simplify using `using h0`. Consider the case `insert z s hz ih`. Rewrite using `[Finset.sum_insert hz, Finset.sum_insert hz]`. Establish `h1` using `(hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt (T z) (∑ y ∈ s, T y) (hT z) (hasLev_sum s T fun y _ => hT y) j j).2.1 1`.

Simplify using `only [one_smul] at h1`. Rewrite using `[h1, ih]`. Establish `hgood : ∀ G, Good G → Good (convF B.ν (fm S P B e L0) G)`. Introduce `G hG i`. Take `⟨⟨⟩, x⟩` from `i`.

Rewrite using `[hform G hG x]`. Establish `hts` using `fun y => hterm x y _ (hG ((), e.symm (Function.update (e x) w₀ y))).1 (hG ((), e.symm (Function.update (e x) w₀ y))).2`. Use `⟨hasLev_sum _ _ fun y _ => (hts y).1, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hact_sum j _ _ fun y => (hts y).1]`. Conclude with `Finset.sum_congr rfl fun y _ => (hts y).2 j`.

Establish `hgoodn : ∀ G, Good G → ∀ n, Good ((convF B.ν (fm S P B e L0))^[n] G)`. Introduce `G hG n`. Proceed by induction on `n with`. Consider the case `zero => exact hG`. Consider the case `succ n ih => rw [Function.iterate_succ_apply']`.

Conclude with `hgood _ ih`. Establish `hslice : ∀ G, Good G → ∀ n (x' : ∀ w : P, κ w) (y : κ w₀), (convF B.ν (fm S P B e L0))^[n] G ((), e.symm (Function.update x' w₀ y)) = (locM w₀.1 (L.m w₀.1))^[n] (fun y => G ((), e.symm (Function.update x' w₀ y))) y`. Introduce `G hG n`. Proceed by induction on `n with`. Consider the case `zero => intro x' y`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `x' y`. Rewrite using `[Function.iterate_succ_apply', hform _ (hgoodn G hG n), Function.iterate_succ_apply']`. Simplify using `only [Equiv.apply_symm_apply, Function.update_self, Function.update_idem, ih]`.

Both sides reduce to the same expression. Use `set Fp : Unit × B.κ → H E B.a B.b → ℂ := fun i => F (p, i.2) with hFp`. Establish `hFgood : Good Fp`. Introduce `i`. Use `⟨(hF (p, i.2)).1, fun j => ?_⟩` and prove the remaining obligations.

Consider the cases of `j with`. Consider the case `inl w' => show actP w'.1 (Φ w'.1) (F (p, i.2)) = F (p, i.2)`. Establish `hfix` using `((hF (p, i.2)).2 w'.1 w'.2).1`. Distinguish the cases in `hwP : w'.1 ∈ P`. Simplify using `only [hΦ, if_pos hwP]`.

Conclude with `((hIdem E B.a B.b w'.1 (V w'.1) (F (p, i.2)) (hVo _) (hVK _) (hF (p, i.2)).1).1).2 (fixed_mono _ (hVU w'.1) hfix)`. Simplify using `only [hΦ, if_neg hwP, hs]`. Conclude with `((hIdem E B.a B.b w'.1 (U₁ w'.1) (F (p, i.2)) (hU₁.1 _).1 (hU₁.1 _).2 (hF (p, i.2)).1).1).2 hfix`. Consider the case `inr w' => show actT w'.1 (L.t w'.1) (F (p, i.2)) = F (p, i.2)`. Rewrite using `[ht]`.

Conclude with `((hIdem E B.a B.b w'.1 (U₂ w'.1) (F (p, i.2)) (hU₂.1 _).1 (hU₂.1 _).2 (hF (p, i.2)).1).2).2 (((hF (p, i.2)).2 w'.1 w'.2.1).2 w'.2.2)`. Establish `hz : (convF B.ν (fm S P B e L0))^[m] Fp = 0`. Use function extensionality and compare the values at `i`. Take `⟨⟨⟩, k'⟩` from `i`. Establish `hk' : k' = e.symm (Function.update (e k') w₀ (e k' w₀))` using `by simp`.

Rewrite using `[hk', hslice Fp hFgood m (e k') (e k' w₀)]`. Use `congrFun (hcon p (e k')) (e k' w₀)` as an intermediate fact. Simplify `this` using `[hFp]`. Rewrite using `[iter_restrict]`. Use `show (convF B.ν (fm S P B e L))^[m] Fp ((), k) = 0`.

Take `⟨U, hU, hUF⟩` from `uniform_lev Fp fun i => (hFgood i).1`. Consider the cases of `m with`. Consider the case `zero => simpa using congrFun hz ((), k)`. Consider the case `succ n`. Establish `hok1` using `pw_ok hA S P B e hS hP L1 hL1ok n`.

Establish `hok0` using `pw_ok hA S P B e hS hP L0 hL0ok n`. Establish `hWs : ∀ w, IsOpen (U₁ w : Set (GLw B.a w × GLw B.b w)) ∧ U₁ w ≤ K2 B.a B.b w` using `hU₁.1`. Establish `hWt : ∀ w, IsOpen (U₂ w : Set (GLw B.a w × GLw B.b w)) ∧ U₂ w ≤ K2 B.a B.b w` using `hU₂.1`. Establish `hent : ∀ x y, LM.ent P (pw L n) x y = LM.ent P ((pw L1 n).mul (pw L0 n)) x y`. Introduce `x y`.

Use function extensionality and compare the values at `w`. Unfold `LM.ent`. Use `split_ifs with hwP`. Distinguish the cases in `hw0 : w = w₀.1`. Substitute `hw0` using the available equality.

Establish `e1 : (pw L1 n).m w₀.1 = dg V w₀.1` using `pw_dg L1 V w₀.1 (hVo _) (hVK _) (by funext x' y'; simp [hL1, rest1]) n`. Establish `e0 : (pw L0 n).m w₀.1 = (pw L n).m w₀.1` using `pw_m_congr L0 L w₀.1 (by funext x' y'; simp [hL0, only0]) n`. Rewrite using `[mul_m]`. Rewrite using `[e1, e0, dg_mul_left V w₀.1 _ (fun z => (pw L n).m w₀.1 z (y ⟨w₀.1, hwP⟩))]`. Use `(mconv_idem_left (hVo _) (hVK _) fun v hv g => ?_).symm` and prove the remaining obligations.

Conclude with `pw_left L w₀.1 (V w₀.1) (fun x' y' v' hv' g' => (hbi w₀.1 hwP x' y' v' (hVU w₀.1 hv') g').1) n _ _ v hv g`. Establish `e1 : (pw L1 n).m w = (pw L n).m w` using `pw_m_congr L1 L w (by funext x' y'; simp [hL1, rest1, hw0]) n`. Establish `e0 : (pw L0 n).m w = dg V w` using `pw_dg L0 V w (hVo _) (hVK _) (by funext x' y'; simp [hL0, only0, hw0]) n`. Rewrite using `[mul_m]`. Rewrite using `[e1, e0, dg_mul_right V w _ (fun z => (pw L n).m w (x ⟨w, hwP⟩) z)]`.

Use `(mconv_idem_right (hVo _) (hVK _) fun v hv g => ?_).symm` and prove the remaining obligations. Conclude with `pw_right L w (V w) (fun x' y' v' hv' g' => (hbi w hwP x' y' v' (hVU w hv') g').2) n _ _ v hv g`. Rewrite using `[mul_s]`. Rewrite using `[stabilizerDilationWeights_dualIsotropicVector L U₁ hWs hs n, stabilizerDilationWeights_dualIsotropicVector L1 U₁ hWs (by rw [hL1s]; exact hs) n, stabilizerDilationWeights_dualIsotropicVector L0 U₁ hWs (by rw [hL0s]; exact hs) n]`. Conclude with `(mconv_idem_left (hWs w).1 (hWs w).2 fun v hv g => idem_left hv g).symm`.

Establish `htt : (pw L n).t = ((pw L1 n).mul (pw L0 n)).t`. Use function extensionality and compare the values at `w`. Rewrite using `[product_torus_component]`. Rewrite using `[power_torus_component_idempotent L U₂ hWt ht n, power_torus_component_idempotent L1 U₂ hWt (by rw [hL1t]; exact ht) n, power_torus_component_idempotent L0 U₂ hWt (by rw [hL0t]; exact ht) n]`. Conclude with `(mconv_idem_left (hWt w).1 (hWt w).2 fun v hv g => idem_left hv g).symm`.

Establish `hfm : fm S P B e (pw L n) = fm S P B e ((pw L1 n).mul (pw L0 n))`. Use function extensionality and compare the values at `x y h`. Simplify using `only [fm, hent, htt]`. Take `⟨hf1, -, hmul, -⟩` from `hA E κ S P B e hS hP (pw L1 n) (pw L0 n) hok1 hok0`. Establish `hf0` using `(hA E κ S P B e hS hP (pw L0 n) (pw L1 n) hok0 hok1).1`.

Rewrite using `[iter_pw hA hC S P B e hS hP L hL Fp U hU hUF n, hfm, ← hmul, (hC E B Unit _ _ U Fp hf1 hf0 hU hUF).1, ← iter_pw hA hC S P B e hS hP L0 hL0ok Fp U hU hUF n, hz, convF_zero]`. Both sides reduce to the same expression.
-/
theorem fmPowOf_holds : FmPowOf := by
  intro hA hAtP hC hAct hIdem
  intro E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F m hU₁ hU₂ hL hs ht hbi hF hne w₀
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  obtain ⟨p, k⟩ := i

  choose V₁ V₂ hV₁ hV₂ hVU using fun w => exists_level_prod w (U₁ w) (hU₁.1 w).1 (hU₁.1 w).2
  set V : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w) := fun w => (V₁ w).prod (V₂ w) with hVdef
  have hVo : ∀ w, IsOpen (V w : Set (GLw B.a w × GLw B.b w)) := fun w => by
    rw [hVdef, Subgroup.coe_prod]; exact (hV₁ w).1.prod (hV₂ w).1
  have hVK : ∀ w, V w ≤ K2 B.a B.b w := fun w => Subgroup.prod_mono (hV₁ w).2.1 (hV₂ w).2.1
  have hVH : ∀ w, IsHecke (V w) (idem (V w)) := fun w => isHecke_idem (V₁ w) (V₂ w) (hV₁ w) (hV₂ w)
  have hdgH : ∀ w (x y : κ w), IsHecke (V w) (dg V w x y) := fun w x y => by
    unfold dg; split_ifs
    · exact hVH w
    · exact isHecke_zero _
  have hw₀P : w₀.1 ∈ P := w₀.2
  set L0 := only0 L V w₀.1 with hL0
  set L1 := rest1 L V w₀.1 with hL1
  have hL0s : L0.s = L.s := by rw [hL0]; rfl
  have hL0t : L0.t = L.t := by rw [hL0]; rfl
  have hL1s : L1.s = L.s := by rw [hL1]; rfl
  have hL1t : L1.t = L.t := by rw [hL1]; rfl
  clear_value L0 L1

  have hL0ok : L0.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) (P.erase w₀.1) V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL0t]; exact hL.2⟩
    · unfold LM.ent
      split_ifs with hwP
      · have : w = w₀.1 := by
          by_contra hne'; exact hw (Finset.mem_erase.2 ⟨hne', hwP⟩)
        subst this
        simp [hL0, only0]
      · rw [hL0s]
    · obtain ⟨hne', hwP⟩ := Finset.mem_erase.1 hw
      unfold LM.ent
      rw [dif_pos hwP]
      simp only [hL0, only0, if_neg hne']
      exact hdgH w _ _
  have hL1ok : L1.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) {w₀.1} V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL1t]; exact hL.2⟩
    · have hne' : w ≠ w₀.1 := fun h => hw (Finset.mem_singleton.2 h)
      unfold LM.ent
      split_ifs with hwP
      · simp [hL1, rest1, hne']
      · rw [hL1s]
    · rw [Finset.mem_singleton.1 hw]
      unfold LM.ent
      rw [dif_pos hw₀P]
      simp only [hL1, rest1, if_true]
      exact hdgH _ _ _

  set Φ : ∀ w : Pl E, GLw B.a w × GLw B.b w → ℂ := fun w => if w ∈ P then idem (V w) else L.s w with hΦ
  have hΦt : IsTestP Φ := by
    refine isTestFunction_modify (hL.1 (e k) (e k)) P V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_)
    · simp only [hΦ, if_neg hw, LM.ent, dif_neg hw]
    · simp only [hΦ, if_pos hw]; exact hVH w
  have hΨt : IsTestP L.t := hL.2
  let Good : (Unit × B.κ → H E B.a B.b → ℂ) → Prop := fun G =>
    ∀ i, HasLev (G i) ∧ ∀ j : Slot S, actS Φ L.t j (G i) = G i
  set i₀ : Slot S := Sum.inl ⟨w₀.1, hP w₀.2⟩ with hi₀

  have hform : ∀ G, Good G → ∀ x, convF B.ν (fm S P B e L0) G ((), x) =
      ∑ y : κ w₀, actP w₀.1 (L.m w₀.1 (e x w₀) y) (G ((), e.symm (Function.update (e x) w₀ y))) := by
    intro G hG x
    have hQ : Quiet S P B e L0 i₀ G := by
      refine ⟨fun w hwP hw x' y' hxy => ?_, fun j hj q x' y' hag => ?_⟩
      · have hne' : w ≠ w₀.1 := fun h => hw (hP hwP) (by subst h; rfl)
        simp only [hL0, only0, if_neg hne', dg, if_neg hxy]
        rfl
      · obtain ⟨⟩ := q
        cases j with
        | inl w' =>
          have hent : LM.ent P L0 (e x') (e y') w'.1 = Φ w'.1 := by
            unfold LM.ent
            by_cases hwP : w'.1 ∈ P
            · rw [dif_pos hwP]
              have hne' : w'.1 ≠ w₀.1 := fun h => hj (by rw [hi₀]; congr 1; exact Subtype.ext h)
              have hxy : e x' ⟨w'.1, hwP⟩ = e y' ⟨w'.1, hwP⟩ := hag ⟨w'.1, hwP⟩ fun h he =>
                hne' (congrArg Subtype.val (Sum.inl_injective he)).symm
              simp only [hL0, only0, if_neg hne', dg, hxy, if_true, hΦ, if_pos hwP]
            · rw [dif_neg hwP]
              simp only [hL0, only0, hΦ, if_neg hwP]
          show actP w'.1 (LM.ent P L0 (e x') (e y') w'.1) (G ((), y')) = G ((), y')
          rw [hent]
          exact (hG ((), y')).2 (Sum.inl w')
        | inr w' =>
          show actT w'.1 (L0.t w'.1) (G ((), y')) = G ((), y')
          rw [hL0t]
          exact (hG ((), y')).2 (Sum.inr w')
    have h := hAtP E κ S P B e hS hP Unit L0 w₀ G hL0ok (fun i => (hG i).1) hQ () x
    rw [h]
    simp only [hL0, only0, if_true]

  have hterm : ∀ (x : B.κ) (y : κ w₀) (g : H E B.a B.b → ℂ), HasLev g → (∀ j : Slot S, actS Φ L.t j g = g) →
      HasLev (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) ∧
        ∀ j : Slot S, actS Φ L.t j (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) = actP w₀.1 (L.m w₀.1 (e x w₀) y) g := by
    intro x y g hg hfix
    set ψ₁ := LM.ent P L (e x) (Function.update (e x) w₀ y) with hψ₁
    have hψt : IsTestP ψ₁ := hL.1 _ _
    have hψw : ψ₁ w₀.1 = L.m w₀.1 (e x w₀) y := by
      simp only [hψ₁, LM.ent, dif_pos hw₀P, Function.update_self]
    have hT : actP w₀.1 (L.m w₀.1 (e x w₀) y) g = actS ψ₁ L.t i₀ g := by
      show _ = actP w₀.1 (ψ₁ w₀.1) g
      rw [hψw]
    rw [hT]
    refine ⟨(hAct E B.a B.b S hS ψ₁ L.t ψ₁ L.t hψt hΨt hψt hΨt g g hg hg i₀ i₀).1, fun j => ?_⟩
    by_cases hj : j = i₀
    · subst hj
      have key := (hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg i₀ i₀).2.2.2
      rw [← key]
      show actP w₀.1 (mconv (Φ w₀.1) (ψ₁ w₀.1)) g = actP w₀.1 (ψ₁ w₀.1) g
      have hΦw : Φ w₀.1 = idem (V w₀.1) := by simp only [hΦ, if_pos hw₀P]
      rw [hΦw, mconv_idem_left (hVo _) (hVK _) fun v hv g' => ?_]
      rw [hψw]
      exact ((hbi w₀.1 hw₀P (e x w₀) y v (hVU w₀.1 hv) g').1)
    · rw [(hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg j i₀).2.2.1 hj, hfix j]

  have hact_sum : ∀ (j : Slot S) (s : Finset (κ w₀)) (T : κ w₀ → H E B.a B.b → ℂ), (∀ y, HasLev (T y)) →
      actS Φ L.t j (∑ y ∈ s, T y) = ∑ y ∈ s, actS Φ L.t j (T y) := by
    intro j s T hT
    induction s using Finset.induction_on with
    | empty =>
      have h0 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt 0 0 hasLev_zero hasLev_zero j j).2.1 1
      simp only [add_zero, one_smul] at h0
      simpa using h0
    | insert z s hz ih =>
      rw [Finset.sum_insert hz, Finset.sum_insert hz]
      have h1 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt (T z) (∑ y ∈ s, T y) (hT z)
        (hasLev_sum s T fun y _ => hT y) j j).2.1 1
      simp only [one_smul] at h1
      rw [h1, ih]

  have hgood : ∀ G, Good G → Good (convF B.ν (fm S P B e L0) G) := by
    intro G hG i
    obtain ⟨⟨⟩, x⟩ := i
    rw [hform G hG x]
    have hts := fun y => hterm x y _ (hG ((), e.symm (Function.update (e x) w₀ y))).1
      (hG ((), e.symm (Function.update (e x) w₀ y))).2
    refine ⟨hasLev_sum _ _ fun y _ => (hts y).1, fun j => ?_⟩
    rw [hact_sum j _ _ fun y => (hts y).1]
    exact Finset.sum_congr rfl fun y _ => (hts y).2 j
  have hgoodn : ∀ G, Good G → ∀ n, Good ((convF B.ν (fm S P B e L0))^[n] G) := by
    intro G hG n
    induction n with
    | zero => exact hG
    | succ n ih => rw [Function.iterate_succ_apply']; exact hgood _ ih

  have hslice : ∀ G, Good G → ∀ n (x' : ∀ w : P, κ w) (y : κ w₀),
      (convF B.ν (fm S P B e L0))^[n] G ((), e.symm (Function.update x' w₀ y)) =
        (locM w₀.1 (L.m w₀.1))^[n] (fun y => G ((), e.symm (Function.update x' w₀ y))) y := by
    intro G hG n
    induction n with
    | zero => intro x' y; rfl
    | succ n ih =>
      intro x' y
      rw [Function.iterate_succ_apply', hform _ (hgoodn G hG n), Function.iterate_succ_apply']
      simp only [Equiv.apply_symm_apply, Function.update_self, Function.update_idem, ih]
      rfl

  set Fp : Unit × B.κ → H E B.a B.b → ℂ := fun i => F (p, i.2) with hFp
  have hFgood : Good Fp := by
    intro i
    refine ⟨(hF (p, i.2)).1, fun j => ?_⟩
    cases j with
    | inl w' =>
      show actP w'.1 (Φ w'.1) (F (p, i.2)) = F (p, i.2)
      have hfix := ((hF (p, i.2)).2 w'.1 w'.2).1
      by_cases hwP : w'.1 ∈ P
      · simp only [hΦ, if_pos hwP]
        exact ((hIdem E B.a B.b w'.1 (V w'.1) (F (p, i.2)) (hVo _) (hVK _) (hF (p, i.2)).1).1).2
          (fixed_mono _ (hVU w'.1) hfix)
      · simp only [hΦ, if_neg hwP, hs]
        exact ((hIdem E B.a B.b w'.1 (U₁ w'.1) (F (p, i.2)) (hU₁.1 _).1 (hU₁.1 _).2 (hF (p, i.2)).1).1).2 hfix
    | inr w' =>
      show actT w'.1 (L.t w'.1) (F (p, i.2)) = F (p, i.2)
      rw [ht]
      exact ((hIdem E B.a B.b w'.1 (U₂ w'.1) (F (p, i.2)) (hU₂.1 _).1 (hU₂.1 _).2 (hF (p, i.2)).1).2).2
        (((hF (p, i.2)).2 w'.1 w'.2.1).2 w'.2.2)
  have hz : (convF B.ν (fm S P B e L0))^[m] Fp = 0 := by
    funext i
    obtain ⟨⟨⟩, k'⟩ := i
    have hk' : k' = e.symm (Function.update (e k') w₀ (e k' w₀)) := by simp
    rw [hk', hslice Fp hFgood m (e k') (e k' w₀)]
    have := congrFun (hcon p (e k')) (e k' w₀)
    simpa [hFp] using this
  rw [iter_restrict]
  show (convF B.ν (fm S P B e L))^[m] Fp ((), k) = 0
  obtain ⟨U, hU, hUF⟩ := uniform_lev Fp fun i => (hFgood i).1
  cases m with
  | zero => simpa using congrFun hz ((), k)
  | succ n =>

    have hok1 := pw_ok hA S P B e hS hP L1 hL1ok n
    have hok0 := pw_ok hA S P B e hS hP L0 hL0ok n
    have hWs : ∀ w, IsOpen (U₁ w : Set (GLw B.a w × GLw B.b w)) ∧ U₁ w ≤ K2 B.a B.b w := hU₁.1
    have hWt : ∀ w, IsOpen (U₂ w : Set (GLw B.a w × GLw B.b w)) ∧ U₂ w ≤ K2 B.a B.b w := hU₂.1
    have hent : ∀ x y, LM.ent P (pw L n) x y = LM.ent P ((pw L1 n).mul (pw L0 n)) x y := by
      intro x y
      funext w
      unfold LM.ent
      split_ifs with hwP
      · by_cases hw0 : w = w₀.1
        · subst hw0
          have e1 : (pw L1 n).m w₀.1 = dg V w₀.1 :=
            pw_dg L1 V w₀.1 (hVo _) (hVK _) (by funext x' y'; simp [hL1, rest1]) n
          have e0 : (pw L0 n).m w₀.1 = (pw L n).m w₀.1 :=
            pw_m_congr L0 L w₀.1 (by funext x' y'; simp [hL0, only0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_left V w₀.1 _ (fun z => (pw L n).m w₀.1 z (y ⟨w₀.1, hwP⟩))]
          refine (mconv_idem_left (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_left L w₀.1 (V w₀.1) (fun x' y' v' hv' g' => (hbi w₀.1 hwP x' y' v' (hVU w₀.1 hv') g').1) n _ _ v hv g
        · have e1 : (pw L1 n).m w = (pw L n).m w :=
            pw_m_congr L1 L w (by funext x' y'; simp [hL1, rest1, hw0]) n
          have e0 : (pw L0 n).m w = dg V w :=
            pw_dg L0 V w (hVo _) (hVK _) (by funext x' y'; simp [hL0, only0, hw0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_right V w _ (fun z => (pw L n).m w (x ⟨w, hwP⟩) z)]
          refine (mconv_idem_right (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_right L w (V w) (fun x' y' v' hv' g' => (hbi w hwP x' y' v' (hVU w hv') g').2) n _ _ v hv g
      · rw [mul_s]
        rw [stabilizerDilationWeights_dualIsotropicVector L U₁ hWs hs n, stabilizerDilationWeights_dualIsotropicVector L1 U₁ hWs (by rw [hL1s]; exact hs) n, stabilizerDilationWeights_dualIsotropicVector L0 U₁ hWs (by rw [hL0s]; exact hs) n]
        exact (mconv_idem_left (hWs w).1 (hWs w).2 fun v hv g => idem_left hv g).symm
    have htt : (pw L n).t = ((pw L1 n).mul (pw L0 n)).t := by
      funext w
      rw [product_torus_component]
      rw [power_torus_component_idempotent L U₂ hWt ht n, power_torus_component_idempotent L1 U₂ hWt (by rw [hL1t]; exact ht) n, power_torus_component_idempotent L0 U₂ hWt (by rw [hL0t]; exact ht) n]
      exact (mconv_idem_left (hWt w).1 (hWt w).2 fun v hv g => idem_left hv g).symm
    have hfm : fm S P B e (pw L n) = fm S P B e ((pw L1 n).mul (pw L0 n)) := by
      funext x y h
      simp only [fm, hent, htt]
    obtain ⟨hf1, -, hmul, -⟩ := hA E κ S P B e hS hP (pw L1 n) (pw L0 n) hok1 hok0
    have hf0 := (hA E κ S P B e hS hP (pw L0 n) (pw L1 n) hok0 hok1).1
    rw [iter_pw hA hC S P B e hS hP L hL Fp U hU hUF n, hfm, ← hmul, (hC E B Unit _ _ U Fp hf1 hf0 hU hUF).1,
      ← iter_pw hA hC S P B e hS hP L0 hL0ok Fp U hU hUF n, hz, convF_zero]
    rfl

end PositivityTheory.Rg.BcB.F.FA

end
