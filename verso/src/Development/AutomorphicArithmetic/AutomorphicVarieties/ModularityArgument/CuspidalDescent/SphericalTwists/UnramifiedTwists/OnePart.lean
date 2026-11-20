import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Af.Gu

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Desc.W.onePart :
    UpperTheory.V.Z.Desc.W.OnePart := by
  intro hJS hTw E _ _ _ n c hn a d P π had hw
  obtain ⟨s, -⟩ := hJS E (Σ i : Fin c, Fin (d i)) Unit (fun x => a x.1) (fun _ => n)
    (fun x => CG.mk ((P x.1).twist
      (GlobalTheory.HeckeGal.Model.absPow E (-(((x.2 : ℕ) : ℝ) - ((d x.1 : ℝ) - 1) / 2)))))
    (fun _ => CG.mk π) (fun x => (had x.1).1) (fun _ => hn)
    (hw.mono fun w ⟨S, h1, h2⟩ => ⟨_, fun _ => satTot w d S, fun x => hTw E _ _ _ w _ (h1 x.1), fun _ => h2, by
      simp only [neg_neg, Finset.univ_unique, Finset.sum_singleton, satTot]
      exact Fintype.sum_sigma _⟩)
  have hc : ∑ i, d i = 1 := by simpa using Fintype.card_congr s
  have hle : c ≤ ∑ i, d i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (had i).2)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨by omega, fun i => le_antisymm ?_ (had i).2⟩
  rw [← hc]
  exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
