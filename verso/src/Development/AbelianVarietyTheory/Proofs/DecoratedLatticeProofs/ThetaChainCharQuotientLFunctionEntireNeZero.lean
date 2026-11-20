import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotL

/- English proof (translation)
Establish `ht : (0 : ℚ) ≤ R.t` using `by positivity`. Establish `step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩` using `fun a h => by`. Establish `g1` using `P.gap_eb ⟨a, by omega⟩ h`. Establish `g2` using `P.gap_be ⟨a + 1, h⟩`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨a, ha⟩ ⟨b, hb⟩ hab`. Simplify using `only [Fin.mk_lt_mk] at hab`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hab`. Proceed by induction on `d with`. Consider the case `zero => exact step a hb`.

Consider the case `succ d ih`. Establish `h1` using `ih (by omega) (by omega)`. Establish `h2` using `step (a + d + 1) (by omega)`. Establish `e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e1]`.

Conclude with `h1.trans h2`.
-/
theorem e_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.e := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩ := fun a h => by
    have g1 := P.gap_eb ⟨a, by omega⟩ h
    have g2 := P.gap_be ⟨a + 1, h⟩
    linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction d with
  | zero => exact step a hb
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := step (a + d + 1) (by omega)
    have e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1]
    exact h1.trans h2

variable {D : D7}

/- English proof (translation)
Introduce `a` and use `by obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2 exact (h η hη a).trans (pow_zero _)`.
-/
theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.μ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  exact (h η hη a).trans (pow_zero _)

/- English proof (translation)
The claim follows from `(hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1`.
-/
theorem isHecke {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) : IsHeckeChar D (c.μ k) :=
  (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1

/- English proof (translation)
Introduce `D c hc i j hi hij hj`. Take `⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1` from `⟨i - 1, by omega⟩`. Take `⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1` from `⟨j - 1, by omega⟩`. Take `⟨τ⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm 1⟩`. Establish `hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧ HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e'` using `⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ, (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from Fin.mk_lt_mk.2 (by omega))).ne⟩`.

Take `⟨Λ, ⟨hd, hp⟩, hpos⟩` from `(GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1)) (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega)) (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S`. Use `⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩` and prove the remaining obligations. Establish `hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w` using `fun w hw => (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv`. Establish `hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))` using `fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl`. Set `e` to `Equiv.subtypeEquivRight hoff`.

Establish `k` using `hp z hz`. Rewrite `k` using `[GlobalTheory.HeckeRatio.lfac_eq]`. Establish `k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} => GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F` using `D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by`. Use `(e.hasProd_iff).1 (k.congr_fun fun P => ?_)` and prove the remaining obligations. Establish `hu` using `hunr P.1 ((hoff P.1).1 P.2)`.

Rewrite using `[GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]`. Simplify using `only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL, GlobalTheory.LFun.charFam_of_unrAt hu]`. Conclude with `k2.tprod_eq.symm`. Use `(hpos n h1 h2).2` as an intermediate fact. Rewrite `this` using `[h0, Complex.zero_re]`.

Conclude with `lt_irrefl _ this`.
-/
theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  intro D c hc i j hi hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega))
    (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w := fun w hw =>
      (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.ChainOnto.QuotL
