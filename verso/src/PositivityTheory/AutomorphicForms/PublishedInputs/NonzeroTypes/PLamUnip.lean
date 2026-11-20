import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamUnip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_eq_one_of_blockTri {ι β : Type} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (M : Matrix ι ι k) (b : ι → β) (hT : M.BlockTriangular b)
    (hD : ∀ i j, b i = b j → M i j = if i = j then 1 else 0) : M.det = 1 := by
  rw [hT.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have h1 : M.toSquareBlock b c = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    change M i j = (1 : Matrix {a' // b a' = c} {a' // b a' = c} k) ⟨i, hi⟩ ⟨j, hj⟩
    rw [one_apply, hD i j (hi.trans hj.symm)]
    simp [Subtype.ext_iff]
  rw [h1, det_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem delta_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0)
    (a : Fin G.s) : G.Δ a g = 1 := by
  unfold Grp.Δ
  refine det_eq_one_of_blockTri _ (fun i : {i : Fin n // G.bl i ≤ a} => b (G.bl i.1)) ?_ ?_
  · intro i j h
    exact hT i.1 j.1 h
  · intro i j h
    change (g : Matrix (Fin n) (Fin n) k) i.1 j.1 = _
    rw [hD i.1 j.1 h]
    simp [Subtype.ext_iff]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem chk_one (μ : kˣ →* ℂˣ) : Grp.chk μ (1 : k) = 1 := by
  unfold Grp.chk
  rw [dif_neg one_ne_zero]
  have h : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
  rw [h, map_one, Units.val_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem lam_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) :
    G.lam g = 1 := by
  unfold Grp.lam
  refine Finset.prod_eq_one fun a _ => ?_
  rw [delta_eq_one G g b hT hD a, chk_one]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem diag_of_unipRad {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (hg : g ∈ unipRad k G.e) :
    ∀ i j, G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  have hD := (mem_unipRad.1 hg).2
  intro i j h
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  have hab : a = b := by simpa [Grp.bl] using h
  subst hab
  rw [hD a i' j', one_apply]
  by_cases hij : i' = j'
  · subst hij; simp
  · rw [if_neg hij, if_neg]
    intro he
    have := G.e.injective he
    simp at this
    exact hij this

end UpperTheory.TNZ.Grp.P_lamUnip

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem step_lamUnip {n : ℕ} (G : Grp k n) : G.LambdaUnipotentProp := by
  refine ⟨fun u hu => ?_, fun u hu _ => ?_⟩
  · obtain ⟨hN, hK⟩ := Subgroup.mem_inf.1 hu
    have hP := (mem_unipRad.1 hN).1
    have hT : ∀ i j, G.bl j < G.bl i → ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 :=
      fun i j h => mem_parab.1 hP i j h
    refine ⟨⟨hK, fun i j hij => ?_⟩, P_lamUnip.lam_eq_one G u (fun a => a) hT
      (P_lamUnip.diag_of_unipRad G u hN)⟩
    rw [hT i j hij]
    exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · exact P_lamUnip.lam_eq_one G u (fun a => OrderDual.toDual a) (fun i j h => (hu i j).1 h)
      (fun i j h => (hu i j).2 h)

end UpperTheory.TNZ.Grp
