import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AddPtW
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ReadWHolds

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Unfold `PtW`. Prove the components needed by the constructor for the conclusion. Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Simplify using the standard rewrite rules.
-/
theorem ptW_X {σ : Type} (i : σ) : PtW (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  unfold PtW
  constructor
  · intro n
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp

/- English proof (translation)
The claim follows from `(coefWfRing_holds p σ f g hf hg).1`.
-/
theorem coefWf_add {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f + g) := (coefWfRing_holds p σ f g hf hg).1

/- English proof (translation)
The claim follows from `(coefWfRing_holds p σ f g hf hg).2.1`.
-/
theorem coefWf_sub {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f - g) := (coefWfRing_holds p σ f g hf hg).2.1

/- English proof (translation)
Take `⟨ha1, ha2⟩` from `ha`. Conclude with `substWf_holds p σ g.ph a hph ha1 ha2`.
-/
theorem coefWf_phAt (g : G1 p) (hph : CoefWf g.ph) {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : PtW a) : CoefWf (g.phAt a) := by
  obtain ⟨ha1, ha2⟩ := ha
  exact substWf_holds p σ g.ph a hph ha1 ha2

/- English proof (translation)
Establish `hab : PtW (g.add a b)` using `HA p g hOk hF σ a b ha hb`. Use `show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)`. Conclude with `coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)`.
-/
theorem coefWf_be (HA : AddPtW) (g : G1 p) (hOk : g.Ok) (hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hph : CoefWf g.ph) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]} (ha : PtW a) (hb : PtW b) : CoefWf (g.be a b) := by
  have hab : PtW (g.add a b) := HA p g hOk hF σ a b ha hb
  show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)
  exact coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)

/- English proof (translation)
Take `⟨h0, hI⟩` from `h`. Establish `hr : SimeqW (f - g) 0` using `readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))`. Take `⟨r0, rI⟩` from `hr`. Conclude with `And.intro (by simpa using r0) (by simpa using rI)`.
-/
theorem simeqW_of {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) (h : Simeq f g) : SimeqW f g := by

  obtain ⟨h0, hI⟩ := h
  have hr : SimeqW (f - g) 0 :=
    readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))
  obtain ⟨r0, rI⟩ := hr
  exact And.intro (by simpa using r0) (by simpa using rI)

end

/- English proof (translation)
Introduce `hph _ hadd hend hbi hconj p _ cc δ g hAt hp5 hI hM`. Establish `hOk : g.Ok` using `hAt.2.2.2.2`. Establish `hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])` using `(hadd p cc δ g hAt).2 hM`. Establish `hg : CoefWf g.ph` using `hph p cc δ g hAt hp5 hI hM`. Establish `P : ∀ {σ : Type} (i : σ), PtW (Xv i : MvPowerSeries σ ℂ_[p])` using `fun i => ptW_X i`.

Establish `B : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → CoefWf (g.be a b)` using `fun ha hb => coefWf_be HA g hOk hF hg ha hb`. Establish `S : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → PtW (g.add a b)` using `fun {σ} {a} {b} ha hb => HA p g hOk hF σ a b ha hb`. Use `⟨B (P (0 : Fin 2)) (P (1 : Fin 2)), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `simeqW_of (B (S (P (0 : Fin 3)) (P (1 : Fin 3))) (P (2 : Fin 3))) (coefWf_add (B (P (0 : Fin 3)) (P (2 : Fin 3))) (B (P (1 : Fin 3)) (P (2 : Fin 3)))) (hbi p cc δ g hAt).1`. Conclude with `simeqW_of (B (P (0 : Fin 3)) (S (P (1 : Fin 3)) (P (2 : Fin 3)))) (coefWf_add (B (P (0 : Fin 3)) (P (1 : Fin 3))) (B (P (0 : Fin 3)) (P (2 : Fin 3)))) (hbi p cc δ g hAt).2`.

Introduce `α hα`. Establish `h1 : PtW (g.mulBy α.1 (Xv 0) : MvPowerSeries (Fin 2) ℂ_[p])` using `HM p g hOk α.1 (hend p cc δ g hAt hp5 hI hM α hα) (Fin 2) _ (P 0)`. Establish `h2 : PtW (g.mulBy α.2 (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])` using `HM p g hOk α.2 (hend p cc δ g hAt hp5 hI hM α.swap (hs p g.lam α hα)) (Fin 2) _ (P 1)`. Conclude with `simeqW_of (B h1 (P (1 : Fin 2))) (B (P (0 : Fin 2)) h2) (hconj p cc δ g hAt (by omega) α hα)`.
-/
theorem beW_of (HA : AddPtW) (HM : MulPtW) (D : D7)
    (hs : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (α : ℂ_[p] × ℂ_[p]), α ∈ OKp D lam → α.swap ∈ OKp D lam) :
    StatementBilinearWitt D := by
  intro hph _ hadd hend hbi hconj p _ cc δ g hAt hp5 hI hM
  have hOk : g.Ok := hAt.2.2.2.2
  have hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := (hadd p cc δ g hAt).2 hM
  have hg : CoefWf g.ph := hph p cc δ g hAt hp5 hI hM
  have P : ∀ {σ : Type} (i : σ), PtW (Xv i : MvPowerSeries σ ℂ_[p]) := fun i => ptW_X i
  have B : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → CoefWf (g.be a b) :=
    fun ha hb => coefWf_be HA g hOk hF hg ha hb
  have S : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → PtW (g.add a b) :=
    fun {σ} {a} {b} ha hb => HA p g hOk hF σ a b ha hb
  refine ⟨B (P (0 : Fin 2)) (P (1 : Fin 2)), ?_, ?_, ?_⟩
  · exact simeqW_of (B (S (P (0 : Fin 3)) (P (1 : Fin 3))) (P (2 : Fin 3)))
      (coefWf_add (B (P (0 : Fin 3)) (P (2 : Fin 3))) (B (P (1 : Fin 3)) (P (2 : Fin 3))))
      (hbi p cc δ g hAt).1
  · exact simeqW_of (B (P (0 : Fin 3)) (S (P (1 : Fin 3)) (P (2 : Fin 3))))
      (coefWf_add (B (P (0 : Fin 3)) (P (1 : Fin 3))) (B (P (0 : Fin 3)) (P (2 : Fin 3))))
      (hbi p cc δ g hAt).2
  · intro α hα
    have h1 : PtW (g.mulBy α.1 (Xv 0) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      HM p g hOk α.1 (hend p cc δ g hAt hp5 hI hM α hα) (Fin 2) _ (P 0)
    have h2 : PtW (g.mulBy α.2 (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      HM p g hOk α.2 (hend p cc δ g hAt hp5 hI hM α.swap (hs p g.lam α hα)) (Fin 2) _ (P 1)
    exact simeqW_of (B h1 (P (1 : Fin 2))) (B (P (0 : Fin 2)) h2) (hconj p cc δ g hAt (by omega) α hα)

end Formalism.MainNotions.Ext
