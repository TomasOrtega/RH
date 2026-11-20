import Formalism.WachLatticeTwists.DenseTopActions.DenseTopActionProofs.OneAddPowSubOne

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem free : StatFree := by
  classical
  intro O A _ _ _ S ι pr D _ _ _ _ W As _ jS κ _ e r₀ r c eq hE hmem hspan hind

  have key : ∀ (cc : Fin r → As) (i : ι),
      (∑ k, jS (cc k) • (fun i => e (eq.symm k).1 • c i (eq.symm k).2 : ι → D)) i
        = ∑ m, (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) i • c i m := by
    intro cc i
    rw [← Equiv.sum_comp eq, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_smul]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro k i
    exact (W.N i).smul_of_tower_mem _ (hmem i _)
  · intro x hx
    choose a ha using fun i => hspan i (x i) (hx i)
    choose d hd _ using fun m => hE (fun i => a i m)
    refine ⟨fun k => d (eq.symm k).2 (eq.symm k).1, ?_⟩
    funext i
    rw [key, ha i]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    have := congrFun (hd m) i
    simpa using this
  · intro cc hcc
    have h1 : ∀ m, (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) = 0 := by
      intro m
      funext i
      have := hind i (fun m => (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) i)
        (by rw [← key, hcc]; rfl)
      exact congrFun this m
    funext k'
    obtain ⟨d, _, hd⟩ := hE 0
    have e1 := hd (fun k => cc (eq (k, (eq.symm k').2))) (h1 _).symm
    have e2 := hd 0 (by simp)
    have := congrFun (e1.trans e2.symm) (eq.symm k').1
    simpa using this
  · intro a
    obtain ⟨d, hd, _⟩ := hE a
    refine ⟨Fintype.card κ, fun j => d ((Fintype.equivFin κ).symm j),
      fun j => e ((Fintype.equivFin κ).symm j), ?_⟩
    rw [hd]
    exact (Equiv.sum_comp (Fintype.equivFin κ).symm
      (fun k => jS (d k) * (fun _ => algebraMap O A (e k) : ι → A))).symm

end Formalism.RepresentationBoundsCohomology.JW
