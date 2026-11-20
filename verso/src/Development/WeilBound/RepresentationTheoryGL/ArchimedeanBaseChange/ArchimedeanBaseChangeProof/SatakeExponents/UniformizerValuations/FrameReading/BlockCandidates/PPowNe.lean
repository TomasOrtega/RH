import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.BetaPow
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg

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
Use `haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩`. Use `haveI := B.hν`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact h`.

Consider the case `succ j ih => exact CG.PMul.mulF_fin B.ν h ih`.
-/
theorem pw_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (t : PT B) (h : IsFinM t.ψ) :
    ∀ j, IsFinM (t.pw j).ψ := by
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  haveI := B.hν
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact CG.PMul.mulF_fin B.ν h ih

/- English proof (translation)
Introduce `x y` and use `⟨Complex.continuous_conj.comp ((h y x).1.comp continuous_inv), ((h y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)⟩`.
-/
theorem adj_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {κ : Type} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (h : IsFinM ψ) : IsFinM (adjF ψ) := fun x y =>
  ⟨Complex.continuous_conj.comp ((h y x).1.comp continuous_inv),
    ((h y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)⟩

/- English proof (translation)
Introduce `hCM E _ _ _ B t m A _ G ht hG hne h0`. Use `choose U hU hF using hG`. Establish `ho : IsOpen ((⨅ j, U j : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b))`. Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite hU`.

Establish `hf : ∀ i, ∀ u ∈ (⨅ j, U j : Subgroup (Hf E B.a B.b)), ∀ x, G i (x * finH u) = G i x` using `fun i u hu => hF i u (Subgroup.mem_iInf.1 hu i)`. Apply `hne` to reduce the goal to its premises. Rewrite using `[R3.sq_psi, (hCM E B A _ _ _ G (pw_fin t.adj' (adj_fin ht) m) (pw_fin t ht m) ho hf).1, R3.convF_pw hCM t _ G ho hf m fun j _ => pw_fin t ht j, h0, R3.convF_zero]`.
-/
theorem powNeOf_holds : PowNeOf := by
  intro hCM E _ _ _ B t m A _ G ht hG hne h0
  choose U hU hF using hG
  have ho : IsOpen ((⨅ j, U j : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  have hf : ∀ i, ∀ u ∈ (⨅ j, U j : Subgroup (Hf E B.a B.b)), ∀ x, G i (x * finH u) = G i x :=
    fun i u hu => hF i u (Subgroup.mem_iInf.1 hu i)
  apply hne
  rw [R3.sq_psi, (hCM E B A _ _ _ G (pw_fin t.adj' (adj_fin ht) m) (pw_fin t ht m) ho hf).1,
    R3.convF_pw hCM t _ G ho hf m fun j _ => pw_fin t ht j, h0, R3.convF_zero]

end PositivityTheory.Rg.BcB.F.BC

end
