import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem par_equiv {ι : Type} [Fintype ι] (v : ι → ZMod 2) :
    ∃ (a g : ℕ) (e : Fin a ⊕ Fin g ≃ ι), ∀ s, v (e s) = Space.Loc.par a g s := by
  classical
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {i // v i = 0}).symm
    (Fintype.equivFin {i // ¬ v i = 0}).symm).trans (Equiv.sumCompl fun i => v i = 0), ?_⟩
  have h2 : ∀ j : ZMod 2, ¬ j = 0 → j = 1 := by decide
  rintro (s | s)
  · exact ((Fintype.equivFin {i // v i = 0}).symm s).2
  · exact h2 _ ((Fintype.equivFin {i // ¬ v i = 0}).symm s).2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Fr.ep_basis :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ J N : Ideal R, (∀ y ∈ J, σ y ∈ J) → (∀ y ∈ N, σ y ∈ N) → maximalIdeal R * J ≤ N → ∃ (a g : ℕ) (z : Fin a ⊕ Fin g → R), (∀ s, z s ∈ J ∧ z s ∈ evp σ (Space.Loc.par a g s)) ∧ J ≤ Ideal.span (Set.range z) ⊔ N ∧ ∀ c : Fin a ⊕ Fin g → O, ∑ s, c s • z s ∈ N → ∀ s, c s ∈ maximalIdeal O := by
  classical
  intro O _ _ _ _ h2 R _ _ _ σ hσ J N hJ hN hmJ
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  obtain ⟨u, hu2, hucomm⟩ : ∃ u : R, u * 2 = 1 ∧ ∀ x, σ (u * x) = u * σ x :=
    ⟨algebraMap O R ↑h2.unit⁻¹, by
      rw [← map_ofNat (algebraMap O R) 2, ← map_mul, h2.val_inv_mul, map_one],
      fun x => by rw [map_mul, AlgHom.commutes]⟩
  have hsg : ∀ p : ZMod 2, sg R p * sg R p = 1 := by
    intro p
    simp only [sg, ← pow_add, ← two_mul, pow_mul]
    simp
  have hsgσ : ∀ p : ZMod 2, σ (sg R p) = sg R p := by
    intro p
    simp [sg]
  have s0 : sg R 0 = 1 := by simp [sg]
  have s1 : sg R 1 = -1 := by
    show (-1 : R) ^ ((1 : ZMod 2).val) = -1
    rw [show (1 : ZMod 2).val = 1 from rfl]
    simp
  let w : T × ZMod 2 → R := fun j => u * (j.1.1 + sg R j.2 * σ j.1.1)
  have hwJ : ∀ j, w j ∈ J := by
    intro j
    have ht : (j.1 : R) ∈ J := hT ▸ Submodule.subset_span j.1.2
    exact J.mul_mem_left _ (J.add_mem ht (J.mul_mem_left _ (hJ _ ht)))
  have hwev : ∀ j, w j ∈ evp σ j.2 := by
    intro j
    show σ (w j) = sg R j.2 * w j
    simp only [w, hucomm, map_add, map_mul, hσ, hsgσ]
    linear_combination (-(u * σ j.1.1)) * hsg j.2
  have hmemN : ∀ c ∈ maximalIdeal O, ∀ y ∈ J, c • y ∈ N := by
    intro c hc y hy
    rw [Algebra.smul_def]
    exact hmJ (Ideal.mul_mem_mul (map_nonunit (algebraMap O R) c hc) hy)
  let Indep : Finset (T × ZMod 2) → Prop := fun S =>
    ∀ c : T × ZMod 2 → O, ∑ s ∈ S, c s • w s ∈ N → ∀ s ∈ S, c s ∈ maximalIdeal O
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter Indep) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨by simp, fun c _ s hs => absurd hs (Finset.notMem_empty s)⟩⟩
  have hS' : Indep S := (Finset.mem_filter.mp hS).2
  obtain ⟨a, g, e, he⟩ := par_equiv (ι := S) (fun i => i.1.2)
  refine ⟨a, g, fun s => w (e s).1, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hwJ _, ?_⟩
    rw [← he s]
    exact hwev _
  · have hspan : ∀ j, w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
      intro j
      by_cases hj : j ∈ S
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨e.symm ⟨j, hj⟩, by simp⟩)
      · have hnot : ¬ Indep (insert j S) := by
          intro hI
          have := hmax (insert j S) (Finset.mem_filter.mpr ⟨by simp, hI⟩)
          rw [Finset.card_insert_of_notMem hj] at this
          omega
        simp only [Indep, not_forall] at hnot
        obtain ⟨c, hc, s, hs, hcs⟩ := hnot
        rw [Finset.sum_insert hj] at hc
        have hcj : c j ∉ maximalIdeal O := by
          intro hcj
          have h1 : c j • w j ∈ N := hmemN _ hcj _ (hwJ j)
          have h2' : ∑ s ∈ S, c s • w s ∈ N := by
            have := N.sub_mem hc h1
            simpa using this
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hcs hcj
          · exact hcs (hS' c h2' s hs)
        have hunit : IsUnit (c j) := by
          by_contra h
          exact hcj ((IsLocalRing.mem_maximalIdeal _).mpr h)
        have hsumS : ∑ s ∈ S, c s • w s ∈ Ideal.span (Set.range fun s => w (e s).1) := by
          refine Ideal.sum_mem _ fun s hs => ?_
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e.symm ⟨s, hs⟩, by simp⟩)
        have hcw : c j • w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
          have : c j • w j = (c j • w j + ∑ s ∈ S, c s • w s) - ∑ s ∈ S, c s • w s := by
            abel
          rw [this]
          exact Submodule.sub_mem _ (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hsumS)
        obtain ⟨d, hd⟩ := hunit.exists_left_inv
        have : w j = d • (c j • w j) := by rw [smul_smul, hd, one_smul]
        rw [this, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hcw
    rw [← hT]
    show Submodule.span R (T : Set R) ≤ _
    rw [Submodule.span_le]
    intro t ht
    have : t = w (⟨t, ht⟩, 0) + w (⟨t, ht⟩, 1) := by
      simp only [w, s0, s1]
      linear_combination (-t) * hu2
    rw [this]
    exact Submodule.add_mem _ (hspan _) (hspan _)
  · intro c hc s
    let c' : T × ZMod 2 → O := fun j => if h : j ∈ S then c (e.symm ⟨j, h⟩) else 0
    have hsum : ∑ j ∈ S, c' j • w j = ∑ s, c s • w (e s).1 := by
      rw [← Finset.sum_coe_sort S, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [c']
    have := hS' c' (hsum ▸ hc) (e s).1 (e s).2
    simpa [c'] using this
