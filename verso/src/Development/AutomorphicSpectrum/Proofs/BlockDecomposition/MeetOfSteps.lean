import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.ClosedInvariantMeet

/- English proof (translation)
Take `⟨Y0, c0, s0, m0⟩` from `hG2a E a ψ hψ`. Take `⟨YH, cH, sH, mH⟩` from `hG2b E a μ H hH`. Establish `hw` using `fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)`. Use `choose! Yw cw sw mw using hw`. Establish `mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔ (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w` using `fun φ => by`.

Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf]`. Use `⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩` and prove the remaining obligations. Establish `e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) = ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a))`. Use extensionality with `φ`. Simplify using `only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]`.

Rewrite using `[e]`. Conclude with `(c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)`. Introduce `g hg φ hφ`. Take `⟨⟨h0, h1⟩, h2⟩` from `(mem φ).1 hφ`. Conclude with `(mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩`.

Introduce `φ hφ`. Conclude with `((m0 φ).1 ((mem φ).1 hφ).1.1).1`. Rewrite using `[mem, m0, mH]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h0, h1⟩, h2⟩`.

Conclude with `⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩`. Introduce and unpack `⟨h0, h1, h2⟩`. Conclude with `⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩`.
-/
theorem exists_space (hG2a : G2a) (hG2b : G2b) (hG2c : G2c) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    (S : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (hB : ∀ w, w ∉ S → (B w).card = a)
    (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : IsSubrep (R (latticeGL E a) μ) H) :
    ∃ Y : Submodule ℂ (XB E a), YOK ψ S Y ∧ ∀ φ : XB E a, φ ∈ Y ↔
      (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
        (∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H) ∧ ∀ w, w ∉ S → SatFn w (B w) φ := by
  obtain ⟨Y0, c0, s0, m0⟩ := hG2a E a ψ hψ
  obtain ⟨YH, cH, sH, mH⟩ := hG2b E a μ H hH
  have hw := fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)
  choose! Yw cw sw mw using hw
  have mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔
      (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w := fun φ => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩
  · have e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) =
        ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a)) := by
      ext φ
      simp only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)
  · intro g hg φ hφ
    obtain ⟨⟨h0, h1⟩, h2⟩ := (mem φ).1 hφ
    exact (mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩
  · intro φ hφ
    exact ((m0 φ).1 ((mem φ).1 hφ).1.1).1
  · rw [mem, m0, mH]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩

/- English proof (translation)
Take `⟨Z, hZ⟩` from `hY0`. Establish `d0 : φ - φ' ∈ Z` using `Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)`. Establish `hd` using `(hZ _).1 d0`. Establish `e` using `hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2 (fun w hw => ⟨B w, by`. Take `⟨Z', hZ'⟩` from `hYs w hw`.

Conclude with `(hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)`. Use the proof step `(fun g h1 h2 => by`. Take `⟨Λ, hΛ⟩` from `(hG5 E a ψ hψ).1 g`. Rewrite using `[← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])`. Conclude with `sub_eq_zero.1 e`.
-/
theorem eq_of_wh (hG5 : G5) (hG13 : WhittakerVanishingImpliesZero) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (S : Finset (Pl E)) (hc : ∀ w, w ∉ S → Cond ψ w) (B : Pl E → Multiset ℂˣ)
    (hYs : ∀ w, w ∉ S → ∃ Z : Submodule ℂ (XB E a), ∀ φ, φ ∈ Z ↔ SatFn w (B w) φ)
    (hY0 : ∃ Z : Submodule ℂ (XB E a), ∀ φ : XB E a, φ ∈ Z ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g)
    {φ φ' : XB E a} (h : (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ)
    (h' : (Good ψ (a - 1) φ' ∧ ∀ γ g, φ' (ratGL E a γ * g) = φ' g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ')
    (hW : ∀ g, MirS S g → InS S g → Wh ψ φ g = Wh ψ φ' g) : φ = φ' := by
  obtain ⟨Z, hZ⟩ := hY0
  have d0 : φ - φ' ∈ Z := Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)
  have hd := (hZ _).1 d0
  have e := hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2
    (fun w hw => ⟨B w, by
      obtain ⟨Z', hZ'⟩ := hYs w hw
      exact (hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)
    (fun g h1 h2 => by
      obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 g
      rw [← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])
  exact sub_eq_zero.1 e

/- English proof (translation)
Introduce `_ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss`. Take `⟨ψ, hψ, hcond⟩` from `hG10 E`. Take `⟨φ0, hφ0, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Take `⟨φ0', hφ0', h0'⟩` from `(Submodule.ne_bot_iff _).1 π'.ne_bot`. Take `⟨x, hx, hxs, hxl⟩` from `hG1 E a π hn φ0 hφ0`.

Take `⟨x', hx', hxs', hxl'⟩` from `hG1 E a π' hn' φ0' hφ0'`. Establish `hev` using `hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))`. Take `⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧ (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧ (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x')` from `⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by`. Assume the negation of the conclusion as `h`. Conclude with `hw ((Set.Finite.mem_toFinset _).2 h)⟩`.

Establish `hBex` using `fun w (hw : w ∉ S) => (hS w hw).2.1`. Use `choose! B hB using hBex`. Establish `hcard : ∀ w, w ∉ S → (B w).card = a` using `fun w hw => CG.HasSat.card (hB w hw).1`. Establish `hc : ∀ w, w ∉ S → Cond ψ w` using `fun w hw => (hS w hw).1`. Take `⟨Y, hYok, hY⟩` from `exists_space hG2a hG2b hG2c μ hψ S B hcard H hH`.

Take `⟨Y', hYok', hY'⟩` from `exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'`. Establish `hxY : x ∈ Y`. Use `(hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `_root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)`.

Rewrite using `[hx]`. Conclude with `(π.cusp _ hφ0).1.left`. Rewrite using `[hx]`. Conclude with `hm φ0 hφ0`. Establish `hxY' : x' ∈ Y'`.

Use `(hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩` and prove the remaining obligations. Rewrite using `[hx']`. Conclude with `_root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')`. Rewrite using `[hx']`. Conclude with `(π'.cusp _ hφ0').1.left`.

Rewrite using `[hx']`. Conclude with `hm' φ0' hφ0'`. Establish `hx0 : x ≠ 0` using `fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))`. Establish `hx0' : x' ≠ 0` using `fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))`. Take `⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩` from `hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S) fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩`.

Take `⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩` from `hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S) fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩`. Establish `hst : St ψ S Y Y' 0 (fun _ => 0)`. Use `⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e : g = 1`. Take `⟨-, -, -, -, -, hext, -⟩` from `hG0 E a`.

Use `hext g 1 ?_ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `(hS10 _ a 0).2.1 _ hg.1`. Rewrite using `[map_one]`. Conclude with `(hS10 _ a 0).2.1 _ (hg.2 w)`.

Rewrite using `[e, hw₁, hw₂]`. Take `⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩` from `hG7i E a ψ hψ S Y Y' hYok hYok' hst`. Establish `hφm` using `(hY φ).1 hφ`. Establish `hφm'` using `(hY' φ').1 hφ'`. Take `⟨Z, -, -, hZ⟩` from `hG2a E a ψ hψ`.

Establish `heq : φ = φ'`. Use `eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩ ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩` and prove the remaining obligations. Take `⟨Z', -, -, hZ'⟩` from `hG2c E a w (B w) (hcard w hw)`. Conclude with `⟨Z', hZ'⟩`. Distinguish the cases in `hw : w ∈ S`.

Simplify `hg.2 w hw` using `only [if_pos hw]`. Simplify using `only [if_neg hw]`. Rewrite using `[hi w hw]`. Conclude with `(hS10 _ a 0).2.2.1`. Substitute `heq` using the available equality.

Take `⟨h, hhH⟩` from `hφm.2.1`. Take `⟨h', hhH'⟩` from `hφm'.2.1`. Establish `hφ0 : φ ≠ 0`. Introduce and unpack `rfl`. Take `⟨Λ, hΛ⟩` from `(hG5 E a ψ hψ).1 1`.

Conclude with `hw (by rw [← hΛ _ hφm.1.1, map_zero])`. Establish `hne : h.toL2 ≠ 0` using `toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)`. Introduce `hbot`. Establish `hmem : h.toL2 ∈ H ⊓ H'` using `⟨hhH, hhH'⟩`. Rewrite `hmem` using `[hbot]`.

Conclude with `hne ((Submodule.mem_bot _).1 hmem)`.
-/
theorem meet_of_steps : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet := by
  intro _ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  obtain ⟨φ0, hφ0, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨φ0', hφ0', h0'⟩ := (Submodule.ne_bot_iff _).1 π'.ne_bot
  obtain ⟨x, hx, hxs, hxl⟩ := hG1 E a π hn φ0 hφ0
  obtain ⟨x', hx', hxs', hxl'⟩ := hG1 E a π' hn' φ0' hφ0'
  have hev := hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))
  obtain ⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧
      (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧
      (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x') :=
    ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by
      by_contra h
      exact hw ((Set.Finite.mem_toFinset _).2 h)⟩
  have hBex := fun w (hw : w ∉ S) => (hS w hw).2.1
  choose! B hB using hBex
  have hcard : ∀ w, w ∉ S → (B w).card = a := fun w hw => CG.HasSat.card (hB w hw).1
  have hc : ∀ w, w ∉ S → Cond ψ w := fun w hw => (hS w hw).1
  obtain ⟨Y, hYok, hY⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H hH
  obtain ⟨Y', hYok', hY'⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'

  have hxY : x ∈ Y := by
    refine (hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩
    · rw [hx]; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)
    · rw [hx]; exact (π.cusp _ hφ0).1.left
    · rw [hx]; exact hm φ0 hφ0
  have hxY' : x' ∈ Y' := by
    refine (hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩
    · rw [hx']; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')
    · rw [hx']; exact (π'.cusp _ hφ0').1.left
    · rw [hx']; exact hm' φ0' hφ0'
  have hx0 : x ≠ 0 := fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))
  have hx0' : x' ≠ 0 := fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))
  obtain ⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩ := hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S)
    fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩
  obtain ⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩ := hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S)
    fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩
  have hst : St ψ S Y Y' 0 (fun _ => 0) := by
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩
    have e : g = 1 := by
      obtain ⟨-, -, -, -, -, hext, -⟩ := hG0 E a
      refine hext g 1 ?_ fun w => ?_
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ hg.1
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ (hg.2 w)
    rw [e, hw₁, hw₂]
  obtain ⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩ := hG7i E a ψ hψ S Y Y' hYok hYok' hst
  have hφm := (hY φ).1 hφ
  have hφm' := (hY' φ').1 hφ'
  obtain ⟨Z, -, -, hZ⟩ := hG2a E a ψ hψ
  have heq : φ = φ' := by
    refine eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩
      ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩
    · obtain ⟨Z', -, -, hZ'⟩ := hG2c E a w (B w) (hcard w hw)
      exact ⟨Z', hZ'⟩
    · by_cases hw : w ∈ S
      · simpa only [if_pos hw] using hg.2 w hw
      · simp only [if_neg hw]
        rw [hi w hw]
        exact (hS10 _ a 0).2.2.1
  subst heq
  obtain ⟨h, hhH⟩ := hφm.2.1
  obtain ⟨h', hhH'⟩ := hφm'.2.1
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 1
    exact hw (by rw [← hΛ _ hφm.1.1, map_zero])
  have hne : h.toL2 ≠ 0 := toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)
  intro hbot
  have hmem : h.toL2 ∈ H ⊓ H' := ⟨hhH, hhH'⟩
  rw [hbot] at hmem
  exact hne ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.ClosedInvariantMeet

end
