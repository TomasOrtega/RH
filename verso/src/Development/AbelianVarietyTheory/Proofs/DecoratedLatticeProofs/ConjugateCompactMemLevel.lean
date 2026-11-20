import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevConj

variable {D : D7}

/- English proof (translation)
Simplify using `only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢`. Conclude with `⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (by rw [hw]; exact hv)⟩⟩`.
-/
theorem mem_idAt_of_eq {P : Pl D → Prop} {v : Pl D} (hv : P v) {a : AE D} (ha : a ∈ idAt D (· = v)) : a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (by rw [hw]; exact hv)⟩⟩

/- English proof (translation)
Establish `hT` using `((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL`. Establish `hV` using `((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL`. Rewrite using `[hT, hV]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h⟩`.

Conclude with `⟨hy, fun w hw e he => h w (by rw [hw]; exact hv) e he⟩`. Introduce and unpack `⟨_, h⟩`. Use `⟨fun i => mem_idAt_of_eq hv (hy i), fun w _ e he => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hwv : w = v`. Conclude with `h w hwv e he`.

Take `⟨ε, -, -, -, hAt, hOff⟩` from `(GlobalTheory.FinPl.localComponents D (· = w)).1`. Establish `hzero : e • y = 0`. Use function extensionality and compare the values at `i`. Establish `hyi : y i ∈ idOff D (· = w)`. Establish `h'` using `hy i`.

Simplify using `only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'`. Simplify using `only [idOff, Submodule.mem_iInf]`. Introduce `u`. Conclude with `h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩`. Establish `h1 : ε * e = e` using `(hAt e).1 he.1`.

Establish `h2 : ε * y i = 0` using `(hOff (y i)).1 hyi`. Use `show e * y i = 0`. Rewrite using `[← h1, mul_comm ε e, mul_assoc, h2, mul_zero]`. Rewrite using `[hzero]`. Conclude with `(latV S L (· = w)).zero_mem`.
-/
theorem latV_supp_iff (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (by rw [hw]; exact hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => mem_idAt_of_eq hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          exact h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

/- English proof (translation)
Introduce `y hy`. Rewrite using `[← latV_supp_iff S L hL hv y hy, ← latV_supp_iff S L hL hv _ (GlobalTheory.FinPl.KOpen.supp_mulVec S _ g hy)]`. Conclude with `h y fun i => mem_idAt_of_eq hv (hy i)`.
-/
theorem moves_at_of_moves {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) {g : GA D S} (h : Moves S g L L P) : Moves S g L L (· = v) := by
  intro y hy
  rw [← latV_supp_iff S L hL hv y hy, ← latV_supp_iff S L hL hv _ (GlobalTheory.FinPl.KOpen.supp_mulVec S _ g hy)]
  exact h y fun i => mem_idAt_of_eq hv (hy i)

end GlobalTheory.LevConj
