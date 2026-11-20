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
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components.
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
