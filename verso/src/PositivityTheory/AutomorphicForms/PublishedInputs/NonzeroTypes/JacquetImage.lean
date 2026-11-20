import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
