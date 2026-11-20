import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ConjEqConjugate
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.DetGelfandMatrixEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LevIdem
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Substitute `hk` using the available equality. Simplify using `[GlobalTheory.Dec.gelfVal]`.
-/
theorem gelfand_value_fin_zero {k : ℕ} (hk : k = 0) (x y : Fin k → ℂ) (m : ℕ) : GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m := by
  subst hk; simp [GlobalTheory.Dec.gelfVal]

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `hSq hLev hGI _ hR E _ _ _ n hn π S T F₀ F h i χ hχ`. Establish `: Countable (Pl E)` using `Small.countable_pl E`. Establish `hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec` using `fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))`. Take `⟨⟨o₁, c₁⟩, ⟨o₂, c₂⟩, -, hν⟩` from `hLev E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP`. Take `⟨cK, hcK, hψ⟩` from `hν (F.B i).ν (F.B i).hν`.

Take `⟨-, -, hsO, hsop, hsval, -⟩` from `hSq E (F.B i) (F.β i) (F₀.A i).bump (F.m - 1) (h.βok i) (F₀.A i).isBump (fun v => ⟨(F₀.A i).kera [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩) (fun v => ⟨(F₀.A i).kerb [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩)`. Rewrite `hsop`, `hsval` using `[Nat.sub_add_cancel F.m_pos]`. Establish `h0 : χ ⟨(F.g (.inl ()) i).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨.inl (), rfl⟩)⟩ = 1` using `hχ.2.1 (.inl ())`. Establish `hM` using `(hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2`. Use `hM (F.B i) _ _ o₁ c₁ o₂ c₂ F.Γ (fun x => F.g x i) (.inl ()) (F.t₀ i) (F₀.A i).bump cK (fun v s m => (.inr (.inl (i, v, s, m, false)), .inr (.inl (i, v, s, m, true)))) (X F i) ((F.β i).sq (F.m - 1)) (2 * F.m) χ ?_ (fun x => h.ok x i) hsO hsop.symm (fun χa χb => hsval χa χb) rfl (F …` and prove the remaining obligations.

Use `F₀.C.le i show 0 < F₀.C.a i + (n - F₀.C.a i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `(⟨⟩ | x | x) t hx`. Simplify using `only [RunFrame.g, Sum.inr.injEq] at hx`. Substitute `hx` using the available equality.

Conclude with `Or.inr rfl`. Simplify using `only [RunFrame.g] at hx`. Distinguish the cases in `hi : i = x.1`. Rewrite `hx` using `[if_pos hi, Sum.inr.injEq]`. Substitute `hx` using the available equality.

Conclude with `Or.inr rfl`. Rewrite `hx` using `[if_neg hi]`. Consider the cases of `hx`. Simplify using `only [RunFrame.g, Sum.inr.injEq] at hx`. Substitute `hx` using the available equality.

Conclude with `Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩`. Introduce `x y g`. Rewrite using `[show (F.t₀ i).ψ x y g = _ from hψ x y g]`. Apply the tactic sequence `split_ifs <;> rfl`. Introduce `v s m _ _`.

Use `⟨F.tD i v s m false, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v'`. Simplify using `[RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]`. Simplify `(F₀.A i).kera [(s, m)] v` using `[RunFrame.tD, Arch.pt]`. Introduce `v' hv'`.

Simplify using `[RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']`. Introduce `v s m _ _`. Use `⟨F.tD i v s m true, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v'`. Simplify using `[RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]`.

Simplify `(F₀.A i).kerb [(s, m)] v` using `[RunFrame.tD, Arch.pt]`. Introduce `v' hv'`. Simplify using `[RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']`. Introduce `x`. Take `⟨c1, c2⟩` from `h.βcomm i x`.

Establish `c3 : Commute (star (F.β i).op) (F.g x i).op` using `by simpa using c2.star_star`. Establish `c4 : Commute (star (F.β i).op) (star (F.g x i).op)` using `c1.star_star`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _`. Rewrite using `[star_pow]`.

Conclude with `(c3.pow_left _).mul_left (c1.pow_left _)`. Use `show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _`. Rewrite using `[star_pow]`. Conclude with `(c4.pow_left _).mul_left (c2.pow_left _)`. Introduce `χa χb ha hb`.

Establish `hreg` using `gamma_zeta_nabla_cancel.reg_of hGI`. Establish `ka : ∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₁ i) v).w s) m`. Introduce `v s m`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using `[GlobalTheory.Dec.gelfVal]`.

Break down `Nat.eq_zero_or_pos (F₀.C.a i) with ha0 | ha0` into its components or cases. Conclude with `gelfand_value_fin_zero ha0 _ _ m`. Rewrite using `[ha v s m hm ha0]`. Use `(congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, false)))) h0).trans ?_` and prove the remaining obligations. Use `show F.dval (i, v, s, m, false) / 1 = _`.

Simplify using `[RunFrame.dval, zVal, Arch.χa]`. Establish `kb : ∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₂ i) v).w s) m`. Introduce `v s m`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using `[GlobalTheory.Dec.gelfVal]`.

Break down `Nat.eq_zero_or_pos (n - F₀.C.a i) with hb0 | hb0` into its components or cases. Conclude with `gelfand_value_fin_zero hb0 _ _ m`. Rewrite using `[hb v s m hm hb0]`. Use `(congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, true)))) h0).trans ?_` and prove the remaining obligations. Use `show F.dval (i, v, s, m, true) / 1 = _`.

Simplify using `[RunFrame.dval, zVal, Arch.χb]`. Take `⟨r1, g1⟩` from `hreg E _ (F₀.C.l₁ i) χa ka`. Take `⟨r2, g2⟩` from `hreg E _ (F₀.C.l₂ i) χb kb`. Conclude with `⟨r1, r2, fun τ => ⟨g1 τ, g2 τ⟩⟩`.
-/
theorem limAtOf_holds : LimAtOf := by
  intro hSq hLev hGI _ hR E _ _ _ n hn π S T F₀ F h i χ hχ
  have : Countable (Pl E) := Small.countable_pl E
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  obtain ⟨⟨o₁, c₁⟩, ⟨o₂, c₂⟩, -, hν⟩ := hLev E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP
  obtain ⟨cK, hcK, hψ⟩ := hν (F.B i).ν (F.B i).hν
  obtain ⟨-, -, hsO, hsop, hsval, -⟩ := hSq E (F.B i) (F.β i) (F₀.A i).bump (F.m - 1) (h.βok i) (F₀.A i).isBump
    (fun v => ⟨(F₀.A i).kera [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩)
    (fun v => ⟨(F₀.A i).kerb [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩)
  rw [Nat.sub_add_cancel F.m_pos] at hsop hsval
  have h0 : χ ⟨(F.g (.inl ()) i).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨.inl (), rfl⟩)⟩ = 1 := hχ.2.1 (.inl ())
  have hM := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  refine hM (F.B i) _ _ o₁ c₁ o₂ c₂ F.Γ (fun x => F.g x i) (.inl ()) (F.t₀ i) (F₀.A i).bump cK
    (fun v s m => (.inr (.inl (i, v, s, m, false)), .inr (.inl (i, v, s, m, true)))) (X F i) ((F.β i).sq (F.m - 1))
    (2 * F.m) χ ?_ (fun x => h.ok x i) hsO hsop.symm (fun χa χb => hsval χa χb) rfl (F₀.A i).isBump ?_
    (fun v => (F₀.A i).kera [] v) (fun v => (F₀.A i).kerb [] v) hcK ?_ ?_ ?_
    (fun x y => ⟨h.comm x y i, h.commStar x y i⟩) ?_ (IsSelfAdjoint.star_mul_self _) hχ.1 (h0.trans_ne one_ne_zero) ?_
  · have := F₀.C.le i
    show 0 < F₀.C.a i + (n - F₀.C.a i)
    omega
  · rintro (⟨⟩ | x | x) t hx
    · simp only [RunFrame.g, Sum.inr.injEq] at hx
      subst hx
      exact Or.inr rfl
    · simp only [RunFrame.g] at hx
      by_cases hi : i = x.1
      · rw [if_pos hi, Sum.inr.injEq] at hx
        subst hx
        exact Or.inr rfl
      · rw [if_neg hi] at hx
        cases hx
    · simp only [RunFrame.g, Sum.inr.injEq] at hx
      subst hx
      exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro x y g
    rw [show (F.t₀ i).ψ x y g = _ from hψ x y g]
    split_ifs <;> rfl
  · intro v s m _ _
    refine ⟨F.tD i v s m false, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩
    · funext v'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
    · simpa [RunFrame.tD, Arch.pt] using (F₀.A i).kera [(s, m)] v
    · intro v' hv'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']
  · intro v s m _ _
    refine ⟨F.tD i v s m true, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩
    · funext v'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
    · simpa [RunFrame.tD, Arch.pt] using (F₀.A i).kerb [(s, m)] v
    · intro v' hv'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']
  · intro x
    obtain ⟨c1, c2⟩ := h.βcomm i x
    have c3 : Commute (star (F.β i).op) (F.g x i).op := by simpa using c2.star_star
    have c4 : Commute (star (F.β i).op) (star (F.g x i).op) := c1.star_star
    refine ⟨?_, ?_⟩
    · show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _
      rw [star_pow]
      exact (c3.pow_left _).mul_left (c1.pow_left _)
    · show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _
      rw [star_pow]
      exact (c4.pow_left _).mul_left (c2.pow_left _)
  · intro χa χb ha hb
    have hreg := gamma_zeta_nabla_cancel.reg_of hGI
    have ka : ∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₁ i) v).w s) m := by
      intro v s m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [GlobalTheory.Dec.gelfVal]
      rcases Nat.eq_zero_or_pos (F₀.C.a i) with ha0 | ha0
      · exact gelfand_value_fin_zero ha0 _ _ m
      rw [ha v s m hm ha0]
      refine (congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, false)))) h0).trans ?_
      show F.dval (i, v, s, m, false) / 1 = _
      simp [RunFrame.dval, zVal, Arch.χa]
    have kb : ∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₂ i) v).w s) m := by
      intro v s m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [GlobalTheory.Dec.gelfVal]
      rcases Nat.eq_zero_or_pos (n - F₀.C.a i) with hb0 | hb0
      · exact gelfand_value_fin_zero hb0 _ _ m
      rw [hb v s m hm hb0]
      refine (congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, true)))) h0).trans ?_
      show F.dval (i, v, s, m, true) / 1 = _
      simp [RunFrame.dval, zVal, Arch.χb]
    obtain ⟨r1, g1⟩ := hreg E _ (F₀.C.l₁ i) χa ka
    obtain ⟨r2, g2⟩ := hreg E _ (F₀.C.l₂ i) χb kb
    exact ⟨r1, r2, fun τ => ⟨g1 τ, g2 τ⟩⟩

/- English proof (translation)
The claim follows from `limAtOf_holds BlockFiniteConvolution.sqOk₀ (levIdem slots) gamma_zeta_nabla_cancel.gelfInj gamma_zeta_nabla_cancel.regDom`.
-/
theorem limAt_holds : LimAt := limAtOf_holds BlockFiniteConvolution.sqOk₀ (levIdem slots) gamma_zeta_nabla_cancel.gelfInj gamma_zeta_nabla_cancel.regDom

end PositivityTheory.Rg.BcB.F.BC

end
