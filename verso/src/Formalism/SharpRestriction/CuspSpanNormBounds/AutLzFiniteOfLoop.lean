import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

section A
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.MainNotions.S.Lem.Comparison₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  have key : ∀ y ∈ Submodule.span E (Set.range F.fl.e), S.hT y F.fl.z = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact F.fl.z_orth b
    | zero => simp
    | add w v _ _ h1 h2 => simp [h1, h2]
    | smul c w _ h => simp [h]
  show F.fl.z ∈ ⨅ x ∈ Xsp F, LinearMap.ker (S.hT x)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  exact key x hx

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem e_mem {T : E} (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xflag F (a.val + 1) := by
  have ha : a ∈ {i : Fin r | i.1 < a.val + 1} := Nat.lt_succ_self _
  show F.fl.e a ∈ Submodule.span E (F.fl.e '' {i | i.1 < a.val + 1})
  exact Submodule.subset_span (Set.mem_image_of_mem _ ha)

end Formalism.MainNotions.S.Lem.Comparison₂

end A

section B
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.MainNotions.S.Lem.Comparison₂

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem one_mem_NLam {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  · exact (Formalism.HermitianLatticesTheory.isom _).one_mem
  · ext x
    simp [Formalism.HermitianLatticesTheory.gmap]

end Formalism.MainNotions.S.Lem.Comparison₂
end B

section C
open scoped Classical
namespace Formalism.MainNotions.S.Lem.Cnt
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cntSW_eq (D : D7) {T : D.host.E} (T' : D.host.E) (F : LFlag (VS D) D.R.rS T) (Λ : LatV D) (Z : GramM D) :
    cntSW D T' F Λ Z =
      cntCl {F' : LFlag (VS D) D.R.rS T' | IsTerm Λ (gS D) F F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) F F' ∧ ZEquiv (ZhatL F F') Z}
        (TEqv D Λ F) := rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem card_le_cntCl {α ι : Type} (X : Set α) (R : α → α → Prop) (hR : ∀ a ∈ X, R a a) (f : ι → α) (hf : ∀ i, f i ∈ X)
    (hinj : ∀ i j, R (f i) (f j) → i = j) : ENat.card ι ≤ cntCl X R := by
  let g : ι → {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} :=
    fun i => ⟨{b | b ∈ X ∧ R (f i) b}, f i, hf i, rfl⟩
  have hg : Function.Injective g := by
    intro i j hij
    have h2 : ({b | b ∈ X ∧ R (f i) b} : Set α) = {b | b ∈ X ∧ R (f j) b} := congrArg Subtype.val hij
    have h3 : f j ∈ ({b | b ∈ X ∧ R (f j) b} : Set α) := ⟨hf j, hR _ (hf j)⟩
    rw [← h2] at h3
    exact hinj i j h3.2
  unfold cntCl
  first
    | exact ENat.card_le_card_of_injective hg
    | (rw [← ENat.card_coe_set_eq]; exact ENat.card_le_card_of_injective hg)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem one_mem_NLam (D : D7) (Λ : LatV D) {T : D.host.E} (F : LFlag (hS D) D.R.rS T) :
    (LinearEquiv.refl D.host.E (hS D).V) ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  · first
      | exact (Formalism.HermitianLatticesTheory.isom _).one_mem
      | exact fun _ _ => rfl
  · ext x
    simp [Formalism.HermitianLatticesTheory.gmap]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem frameEqv_refl (D : D7) {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') :
    FrameEqv D (LinearEquiv.refl D.host.E (VS D).V) F' F' := by
  unfold FrameEqv
  refine ⟨1, fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, ?_⟩
  funext b
  simp only [frameAct, LinearEquiv.refl_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    rw [Matrix.one_apply_ne hab]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/- English proof (translation)
Replace the relevant objects with their definitions. Supply the required witnesses or components.
-/
theorem TEqv_refl (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F' : LFlag (hS D) D.R.rS T') :
    TEqv D Λ F F' F' := by
  unfold TEqv
  exact ⟨LinearEquiv.refl _ _, one_mem_NLam D Λ F, frameEqv_refl D F'⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Supply the required witnesses or components.
-/
theorem PEqv_refl (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (p : Trip D T') :
    PEqv D Λ F p p := by
  unfold PEqv
  exact ⟨LinearEquiv.refl _ _, one_mem_NLam D Λ F, LinearEquiv.refl _ _, one_mem_NLam D Λ F,
    frameEqv_refl D _, frameEqv_refl D _, fun x _ => by simp⟩

end Formalism.MainNotions.S.Lem.Cnt
end C

section E

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.MainNotions.S.Lem.Glob

variable {D : Formalism.BasicNotions.D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem Dmin_eq {n : ℕ} (w : Point D.host.E n) (l : ℕ) : Dmin w l = leadMinorE (ptMat w) l := by
  first
    | rfl
    | (unfold Dmin leadMinorE; by_cases hl : l ≤ n <;> simp [hl])

end Formalism.MainNotions.S.Lem.Glob
end E

end
