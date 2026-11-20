import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PCandSb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Take `⟨K₁, K₂, h₁, h₂, he⟩` from `LocOk.lev_lv d hd ha w`. Rewrite using `[he]`. Conclude with `LocOk.prod_open_le h₁ h₂`. Use `Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)`.
-/
theorem isLev_lev (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : Tail.IsLev (d.lev a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := LocOk.lev_lv d hd ha w
    rw [he]; exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)

/- English proof (translation)
Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Take `⟨K₁, K₂, h₁, h₂, he⟩` from `LocOk.lev₂_lv d hd ha w`. Rewrite using `[he]`. Conclude with `LocOk.prod_open_le h₁ h₂`. Use `Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hw (LocOk.lev₂_out d (LocOk.out3 d h).2)`.
-/
theorem isLev_lev₂ (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : Tail.IsLev (d.lev₂ a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := LocOk.lev₂_lv d hd ha w
    rw [he]; exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev₂_out d (LocOk.out3 d h).2)

/- English proof (translation)
Use `show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)`. Use `split_ifs with hT`. Rewrite using `[LocOk.level_eq_iwahori_pair_at_bad_places d hT]`. Conclude with `LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y`. Establish `hS : w ∈ d.S₀`.

Simplify using `only [LocData.P, Finset.mem_union] at hw`. The claim follows by propositional logic. Rewrite using `[LocOk.lev_S d hT (Finset.mem_union_left _ hS)]`. Conclude with `LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)`.
-/
theorem betaL_H (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) (hw : w ∈ d.P) (x y : d.kap w) :
    IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih]`. Use function extensionality and compare the values at `x`.

Simplify using `only [locM, Function.comp_apply]`. Conclude with `Equiv.sum_comp σ (fun y => actP w (M (σ x) y) (((locM w M)^[m] G) y))`.
-/
theorem locM_iter_equiv {a b : ℕ} {k k' : Type} [Fintype k] [Fintype k'] (w : Pl E) (σ : k ≃ k')
    (M : k' → k' → LF a b w) (G : k' → H E a b → ℂ) (m : ℕ) :
    (locM w (fun x y => M (σ x) (σ y)))^[m] (G ∘ σ) = ((locM w M)^[m] G) ∘ σ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [locM, Function.comp_apply]
    exact Equiv.sum_comp σ (fun y => actP w (M (σ x) y) (((locM w M)^[m] G) y))

def kapEquiv (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.kap w ≃ d.X w where
  toFun x := ⟨x.1.2, LocOk.kap_X d hT hS x⟩
  invFun y := ⟨(∅, y.1), by unfold LocData.idx; rw [if_neg hT, if_pos hS]; simp [y.2]⟩
  left_inv x := by
    obtain ⟨⟨s, g⟩, hx⟩ := x
    have : s = ∅ := by
      unfold LocData.idx at hx; rw [if_neg hT, if_pos hS] at hx
      simpa using (Finset.mem_product.1 hx).1
    subst this
    rfl
  right_inv y := rfl

end PCandSb

open PCandSb in
/- English proof (translation)
Introduce `hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsp`. Establish `ha : F₀.C.a i ≤ n` using `F₀.C.le i`. Establish `hd : F.d.Ok` using `F.ok`. Establish `hw0 : w ∈ F₀.d₀.S₀` using `F₀.S_le w hwS hsp`. Establish `hwd : w ∈ F.d.S₀` using `F.same.1 ▸ hw0`.

Establish `hwT : w ∉ F.d.T` using `fun h' => Finset.disjoint_left.1 hd.disj.1 h' hwd`. Establish `hwP : w ∈ F.d.P` using `Finset.mem_union_right _ hwd`. Establish `hwSec : w ∈ F₀.Sec` using `(F₀.S₀ w hw0).1`. Establish `hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec`. Introduce `u hu`.

Break down `Finset.mem_union.1 hu with h1 | h1` into its components or cases. Conclude with `(F.T_in u h1).1`. Conclude with `(F₀.S₀ u (F.same.1 ▸ h1)).1`. Take `⟨α, x, hx⟩` from `FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d hd ha) (isLev_lev₂ F.d hd ha) (LocOk.betaL_ok F.d idemAlg PositivityT …`. Take `⟨P, hPc, hkill⟩` from `F.choiceS w hw0`.

Use `⟨P, ?_, hPc⟩` and prove the remaining obligations. Take `⟨hO, hle, hN, hX, hU, hHk⟩` from `hd.K' w hwd`. Establish `hK' : F.d.K' w = F₀.d₀.K' w` using `congrFun F.same.2.2.2.2.1 w`. Establish `hμ : F.d.μ w = F₀.μ.loc w` using `(congrFun F.same.2.2.1 w).trans (F₀.μloc w)`. Establish `hLo : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w))` using `((isLev_lev F.d hd ha).1 w).1`.

Set `σ` to `kapEquiv F.d hwT hwd`. Set `G₀ : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ` to `fun y => G (α, (Equiv.refl _).symm (Function.update x ⟨w, hwP⟩ y))`. Establish `hfix : ∀ y, G₀ y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (F.d.lev (F₀.C.a i) w)` using `fun y => ((hl _).2 w hwSec).1`. Set `M : F.d.X w → F.d.X w → LF (F₀.C.a i) (n - F₀.C.a i) w` to `fun u v => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) u v`. Establish `hm : (F.d.betaL _ ha).m w = fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v)`.

Use function extensionality and compare the values at `u v`. Use `show (if w ∈ F.d.T then _ else _) = _`. Rewrite using `[if_neg hwT]`. Use function extensionality and compare the values at `z`. Use `show _ * phiMu (Nat.add_sub_of_le ha) w (F.d.μ w) (F.d.e w) _ _ z = _`.

Rewrite using `[hμ]`. Both sides reduce to the same expression. Establish `hx' : (locM w fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v))^[F.m] G₀ ≠ 0`. Rewrite using `[← hm]`. Conclude with `hx`.

Establish `h1 : (locM w fun u v => M (σ u) (σ v))^[F.m] G₀ ≠ 0` using `(locPow_holds E _ _ w (F.d.kap w) _ G₀ F.m hLo hfix).1 _ (fun u v => M (σ u) (σ v)) hx'`. Establish `h2 : (locM w M)^[F.m] (G₀ ∘ σ.symm) ≠ 0`. Introduce `h0`. Apply `h1` to reduce the goal to its premises. Establish `e1` using `locM_iter_equiv w σ M (G₀ ∘ σ.symm) F.m`.

Establish `e2 : (G₀ ∘ σ.symm) ∘ σ = G₀` using `by funext y; simp`. Rewrite `e1` using `[e2]`. Rewrite using `[e1, h0]`. Both sides reduce to the same expression. Conclude with `h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.K' w) (F.d.X w) (F.d.lev _ w) (F.d.e w) P F.m (G₀ ∘ σ.symm) hO hle hN hX hU hLo hHk (fun τ hτ hne' v hv => by rw [hK'] at hv ⊢; exact hkill i s₁ s₂ Pa Pb D hc τ hτ hne' v hv) (by rw [hK']; exa …`.
-/
theorem candS_of (h : Tail.ReadS) : CandS := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsp
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hd : F.d.Ok := F.ok
  have hw0 : w ∈ F₀.d₀.S₀ := F₀.S_le w hwS hsp
  have hwd : w ∈ F.d.S₀ := F.same.1 ▸ hw0
  have hwT : w ∉ F.d.T := fun h' => Finset.disjoint_left.1 hd.disj.1 h' hwd
  have hwP : w ∈ F.d.P := Finset.mem_union_right _ hwd
  have hwSec : w ∈ F₀.Sec := (F₀.S₀ w hw0).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (F.same.1 ▸ h1)).1
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d hd ha)
    (isLev_lev₂ F.d hd ha) (LocOk.betaL_ok F.d idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd ha u hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  obtain ⟨P, hPc, hkill⟩ := F.choiceS w hw0
  refine ⟨P, ?_, hPc⟩
  obtain ⟨hO, hle, hN, hX, hU, hHk⟩ := hd.K' w hwd
  have hK' : F.d.K' w = F₀.d₀.K' w := congrFun F.same.2.2.2.2.1 w
  have hμ : F.d.μ w = F₀.μ.loc w := (congrFun F.same.2.2.1 w).trans (F₀.μloc w)
  have hLo : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) :=
    ((isLev_lev F.d hd ha).1 w).1
  let σ := kapEquiv F.d hwT hwd
  let G₀ : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x ⟨w, hwP⟩ y))
  have hfix : ∀ y, G₀ y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (F.d.lev (F₀.C.a i) w) :=
    fun y => ((hl _).2 w hwSec).1
  let M : F.d.X w → F.d.X w → LF (F₀.C.a i) (n - F₀.C.a i) w :=
    fun u v => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) u v
  have hm : (F.d.betaL _ ha).m w = fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v) := by
    funext u v
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_neg hwT]
    funext z
    show _ * phiMu (Nat.add_sub_of_le ha) w (F.d.μ w) (F.d.e w) _ _ z = _
    rw [hμ]
    rfl
  have hx' : (locM w fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v))^[F.m] G₀ ≠ 0 := by
    rw [← hm]; exact hx
  have h1 : (locM w fun u v => M (σ u) (σ v))^[F.m] G₀ ≠ 0 :=
    (locPow_holds E _ _ w (F.d.kap w) _ G₀ F.m hLo hfix).1 _ (fun u v => M (σ u) (σ v)) hx'
  have h2 : (locM w M)^[F.m] (G₀ ∘ σ.symm) ≠ 0 := by
    intro h0
    apply h1
    have e1 := locM_iter_equiv w σ M (G₀ ∘ σ.symm) F.m
    have e2 : (G₀ ∘ σ.symm) ∘ σ = G₀ := by funext y; simp
    rw [e2] at e1
    rw [e1, h0]; rfl
  exact h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.K' w) (F.d.X w)
    (F.d.lev _ w) (F.d.e w) P F.m (G₀ ∘ σ.symm) hO hle hN hX hU hLo hHk
    (fun τ hτ hne' v hv => by rw [hK'] at hv ⊢; exact hkill i s₁ s₂ Pa Pb D hc τ hτ hne' v hv)
    (by rw [hK']; exact (F.choiceM i s₁ s₂ Pa Pb D hc).1 w hw0)
    (fun y => ⟨hG _, hfix _⟩) h2

end PositivityTheory.Rg.BcB.F

end
