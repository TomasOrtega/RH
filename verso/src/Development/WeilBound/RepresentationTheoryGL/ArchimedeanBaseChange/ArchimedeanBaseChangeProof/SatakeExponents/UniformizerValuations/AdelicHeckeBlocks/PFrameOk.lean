import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PStruct

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace FrameOk

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Run

variable {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S}
  (F : RunFrame F₀ T)

/- English proof (translation)
Introduce `w hw`. Establish `hw' : w ∈ F.d.T ∪ F.d.S₀` using `hw`. Establish `hT` using `F.T_in`. Establish `hs` using `F.same`. Unfold `RF_T_in at hT`.

Unfold `RF_same at hs`. Break down `Finset.mem_union.1 hw' with h | h` into its components or cases. Conclude with `(hT w h).1`. Conclude with `(F₀.S₀ w (hs.1 ▸ h)).1`.
-/
theorem wirtinger_sub : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
  intro w hw
  have hw' : w ∈ F.d.T ∪ F.d.S₀ := hw
  have hT := F.T_in
  have hs := F.same
  unfold RF_T_in at hT
  unfold RF_same at hs
  rcases Finset.mem_union.1 hw' with h | h
  · exact (hT w h).1
  · exact (F₀.S₀ w (hs.1 ▸ h)).1

/- English proof (translation)
The claim follows from `Or.inl rfl`.
-/
theorem isGen_eL (i : F₀.C.ι) : F.d.IsGen (F₀.C.a i) (F₀.C.le i) (F.d.eL _) := Or.inl rfl

/- English proof (translation)
Break down `x with u | x | x` into its components or cases. Conclude with `Or.inr ⟨F.d.eL _, fun _ => [], fun _ => [], isGen_eL F i, rfl⟩`. Distinguish the cases in `h : i = x.1`. Use `Or.inr ⟨F.d.eL _, fun v' => if v' = x.2.1 ∧ x.2.2.2.2 = false then [(x.2.2.1, x.2.2.2.1)] else [], fun v' => if v' = x.2.1 ∧ x.2.2.2.2 = true then [(x.2.2.1, x.2.2.2.1)] else [], isGen_eL F i, ?_⟩` and prove the remaining obligations. Simplify using `only [RunFrame.g, if_pos h]`.

Both sides reduce to the same expression. Conclude with `Or.inl ⟨F.dval x, by simp only [RunFrame.g, if_neg h]⟩`. Conclude with `Or.inr ⟨_, fun _ => [], fun _ => [], Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩, rfl⟩`.
-/
theorem gen_cases (x : F.Γ) (i : F₀.C.ι) : (∃ c, F.g x i = Sum.inl c) ∨
    ∃ L wa wb, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L ∧
      F.g x i = Sum.inr ((F₀.A i).pt wa wb (F.ψ i L) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i L))) := by
  rcases x with u | x | x
  · exact Or.inr ⟨F.d.eL _, fun _ => [], fun _ => [], isGen_eL F i, rfl⟩
  · by_cases h : i = x.1
    · refine Or.inr ⟨F.d.eL _, fun v' => if v' = x.2.1 ∧ x.2.2.2.2 = false then [(x.2.2.1, x.2.2.2.1)] else [],
        fun v' => if v' = x.2.1 ∧ x.2.2.2.2 = true then [(x.2.2.1, x.2.2.2.1)] else [], isGen_eL F i, ?_⟩
      simp only [RunFrame.g, if_pos h]
      rfl
    · exact Or.inl ⟨F.dval x, by simp only [RunFrame.g, if_neg h]⟩
  · exact Or.inr ⟨_, fun _ => [], fun _ => [], Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩, rfl⟩

/- English proof (translation)
Establish `hS` using `F₀.hSec`. Establish `hP` using `wirtinger_sub F`. Establish `hd` using `F.ok`. Establish `okPT : ∀ i (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) wa wb, F.d.IsGen _ (F₀.C.le i) L → ((F₀.A i).pt wa wb (F.ψ i L) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i L))).Ok` using `fun i L wa wb hL => (oks (A := F₀.A i) hd hS hP (F₀.C.le i) wa wb).1 L hL`. Establish `stE : ∀ i (t : PT (F.B i)), star t.op = ContinuousLinearMap.adjoint t.op` using `fun _ _ => ContinuousLinearMap.star_eq_adjoint _`.

Establish `opS : ∀ i (c : ℂ), BGen.op (Sum.inl c : BGen (F.B i)) = c • (1 : (F.B i).Hb →L[ℂ] (F.B i).Hb)` using `fun _ _ => rfl`. Use `⟨fun x i => ?_, fun i => (oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.1, fun i => ⟨(oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.2.1, (oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.2.2 _ _⟩, fun x y i => ?_, fun x y i => ?_, fun i x => ?_⟩` and prove the remaining obligations. Break down `gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩` into its components or cases. Rewrite using `[hc]`. Conclude with `trivial`.

Rewrite using `[hx]`. Conclude with `okPT i L wa wb hL`. Break down `gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩` into its components or cases. Rewrite using `[hc, opS]`. Conclude with `(Commute.one_left _).smul_left c`.

Break down `gen_cases F y i with ⟨c', hc'⟩ | ⟨L', wa', wb', hL', hy⟩` into its components or cases. Rewrite using `[hc', opS]`. Conclude with `(Commute.one_right _).smul_right c'`. Rewrite using `[hx, hy]`. Conclude with `(comm_gen (A := F₀.A i) hd hS hP (F₀.C.le i) hL hL' wa wb wa' wb').1`.

Break down `gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩` into its components or cases. Rewrite using `[hc, opS]`. Conclude with `(Commute.one_left _).smul_left c`. Break down `gen_cases F y i with ⟨c', hc'⟩ | ⟨L', wa', wb', hL', hy⟩` into its components or cases. Rewrite using `[hc', opS, star_smul, star_one]`.

Conclude with `(Commute.one_right _).smul_right _`. Rewrite using `[hx, hy]`. Use `show Commute (PT.op (B := F.B i) _) (star (PT.op (B := F.B i) _))`. Rewrite using `[stE]`. Conclude with `(comm_gen (A := F₀.A i) hd hS hP (F₀.C.le i) hL hL' wa wb wa' wb').2`.

Break down `gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩` into its components or cases. Rewrite using `[hc, opS, star_smul, star_one]`. Conclude with `⟨(Commute.one_right _).smul_right c, (Commute.one_right _).smul_right _⟩`. Rewrite using `[hx]`. Establish `h` using `comm_beta (A := F₀.A i) hd hS hP (F₀.C.le i) hL (fun _ => []) (fun _ => []) wa wb`.

Use `⟨h.1, ?_⟩` and prove the remaining obligations. Use `show Commute (PT.op (B := F.B i) _) (star (PT.op (B := F.B i) _))`. Rewrite using `[stE]`. Conclude with `h.2`.
-/
theorem struct : F.Struct := by
  have hS := F₀.hSec
  have hP := wirtinger_sub F
  have hd := F.ok
  have okPT : ∀ i (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) wa wb, F.d.IsGen _ (F₀.C.le i) L →
      ((F₀.A i).pt wa wb (F.ψ i L) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i L))).Ok :=
    fun i L wa wb hL => (oks (A := F₀.A i) hd hS hP (F₀.C.le i) wa wb).1 L hL
  have stE : ∀ i (t : PT (F.B i)), star t.op = ContinuousLinearMap.adjoint t.op :=
    fun _ _ => ContinuousLinearMap.star_eq_adjoint _
  have opS : ∀ i (c : ℂ), BGen.op (Sum.inl c : BGen (F.B i)) = c • (1 : (F.B i).Hb →L[ℂ] (F.B i).Hb) := fun _ _ => rfl
  refine ⟨fun x i => ?_, fun i => (oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.1,
    fun i => ⟨(oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.2.1,
      (oks (A := F₀.A i) hd hS hP (F₀.C.le i) _ _).2.2.2 _ _⟩, fun x y i => ?_, fun x y i => ?_, fun i x => ?_⟩
  · rcases gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩
    · rw [hc]; exact trivial
    · rw [hx]; exact okPT i L wa wb hL
  · rcases gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩
    · rw [hc, opS]; exact (Commute.one_left _).smul_left c
    rcases gen_cases F y i with ⟨c', hc'⟩ | ⟨L', wa', wb', hL', hy⟩
    · rw [hc', opS]; exact (Commute.one_right _).smul_right c'
    rw [hx, hy]
    exact (comm_gen (A := F₀.A i) hd hS hP (F₀.C.le i) hL hL' wa wb wa' wb').1
  · rcases gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩
    · rw [hc, opS]; exact (Commute.one_left _).smul_left c
    rcases gen_cases F y i with ⟨c', hc'⟩ | ⟨L', wa', wb', hL', hy⟩
    · rw [hc', opS, star_smul, star_one]; exact (Commute.one_right _).smul_right _
    rw [hx, hy]
    show Commute (PT.op (B := F.B i) _) (star (PT.op (B := F.B i) _))
    rw [stE]
    exact (comm_gen (A := F₀.A i) hd hS hP (F₀.C.le i) hL hL' wa wb wa' wb').2
  · rcases gen_cases F x i with ⟨c, hc⟩ | ⟨L, wa, wb, hL, hx⟩
    · rw [hc, opS, star_smul, star_one]
      exact ⟨(Commute.one_right _).smul_right c, (Commute.one_right _).smul_right _⟩
    rw [hx]
    have h := comm_beta (A := F₀.A i) hd hS hP (F₀.C.le i) hL (fun _ => []) (fun _ => []) wa wb
    refine ⟨h.1, ?_⟩
    show Commute (PT.op (B := F.B i) _) (star (PT.op (B := F.B i) _))
    rw [stE]
    exact h.2

end Run

end FrameOk

/- English proof (translation)
Introduce `hR E _ _ _ _ n _ π S T F₀ F`. Conclude with `FrameOk.struct F`.
-/
theorem frameOk₀ : FrameOk := by
  intro hR E _ _ _ _ n _ π S T F₀ F
  exact FrameOk.struct F

end PositivityTheory.Rg.BcB.F

end
