import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun continuous_id.matrix_det continuous_const

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (X : Mat n) :
    ∀ x ∈ U, Rd X f x = Rd X f' x := by
  intro x hx
  unfold Rd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (a b : Fin n) :
    ∀ x ∈ U, Eu s a b f x = Eu s a b f' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h (single a b 1) x hx, rd_congr hU h (single a b Complex.I) x hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), ∀ x ∈ U, Epow s m a b f x = Epow s m a b f' x := by
  intro m
  induction m with
  | zero =>
    intro a b x hx
    simp only [Epow.eq_1]
    by_cases hab : a = b <;> simp [hab, h x hx]
  | succ m ih =>
    intro a b x hx
    simp only [Epow.eq_2]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (fun y hy => ih c b y hy) s a c x hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (m : ℕ) :
    ∀ x ∈ U, gel s m f x = gel s m f' x := by
  intro x hx
  simp only [gel]
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU h s m a a x hx

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eigLocal : EigLocal := by
  intro n χ V _ _ f f' h hf s m g hg
  rw [← h g hg, ← gel_congr isOpen_GLs h s m g hg]
  exact hf s m g hg

end PositivityTheory.RgBcC
