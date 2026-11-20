import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private noncomputable def densPhi {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) (p : Fin n × Fin n) : ℂ :=
  (1 - (z p.1 : ℂ) / (z p.2 : ℂ)) / (1 - t * ((z p.1 : ℂ) / (z p.2 : ℂ)))

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private lemma half_inv_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    half t z⁻¹ = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), densPhi t z p := by
  unfold half
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    have h : (((z⁻¹) p.1 : ℂˣ) : ℂ) / (((z⁻¹) p.2 : ℂˣ) : ℂ) = (z p.2 : ℂ) / (z p.1 : ℂ) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
      rw [inv_div_inv]
    simp only [densPhi, Prod.fst_swap, Prod.snd_swap, h]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
private lemma dens_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    dens t z = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2), densPhi t z p := by
  have h3 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      prs n ∪ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, prs]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun h => h.ne) (fun h => h.ne')⟩
  have hd : Disjoint (prs n) ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prs] at hp hq
    exact lt_asymm hp hq
  rw [h3, Finset.prod_union hd, ← half_inv_eq]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Gen.densSymm :
    UpperTheory.Gal.Gen.DensSymm := by
  intro n t z σ
  rw [dens_eq, dens_eq]
  refine Finset.prod_nbij' (Prod.map σ σ) (Prod.map σ.symm σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
  · intro p _
    rfl
