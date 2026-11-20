import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvzVal

/- English proof (translation)
Take `⟨a, ha⟩` from `R.t_odd`. Establish `h1 : (R.t + 1) / 2 = a + 1` using `by omega`. Establish `h2 : j * (R.t + 1) / 2 = j * (a + 1)`. Rewrite using `[ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega`. Rewrite using `[h1, h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

/- English proof (translation)
Consider the cases of `a`. Consider the cases of `b`. Simplify using `only at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `domWeight_ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) = (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))`. Rewrite using `[half_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamT_eq_lamT_hcW {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

/- English proof (translation)
Introduce `B X I hI hP l Z u a ψ hψ c`. Establish `h1` using `(hψ ((I.perIn u a).tilC c)).1`. Establish `h2` using `GlobalTheory.Mem.Col2.Law.tr_mem (I.stp u a B.R.m) B.fields.emb B.embLL _ (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) h1`. Take `⟨P, hP, e⟩` from `Submodule.mem_map.1 h2`. Rewrite using `[lamT_eq_lamT_hcW I l Z u B.R.m]`.

Conclude with `⟨P, hP, funext fun y => congrFun e ⟨y.1, y.2⟩⟩`.
-/
theorem evz_mem_valC : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (ψ : ColT I l u a B.R.m), ψ ∈ (I.fm l u a).Fi B.R.m → ∀ c, (fun y : FrN (I.rec7 l Z) (B.R.N B.R.m) => (I.per l u a).evz ψ c ⟨y.1, y.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m) := by
  intro B X I hI hP l Z u a ψ hψ c
  have h1 := (hψ ((I.perIn u a).tilC c)).1
  have h2 := GlobalTheory.Mem.Col2.Law.tr_mem (I.stp u a B.R.m) B.fields.emb B.embLL _ (I.perIn u a).b0
    ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) h1
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 h2
  rw [lamT_eq_lamT_hcW I l Z u B.R.m]
  exact ⟨P, hP, funext fun y => congrFun e ⟨y.1, y.2⟩⟩

end GlobalTheory.EvzVal

end
