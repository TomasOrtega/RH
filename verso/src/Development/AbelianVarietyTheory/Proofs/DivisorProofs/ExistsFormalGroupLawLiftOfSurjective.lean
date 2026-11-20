import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftLaw

def cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) : MvPowerSeries σ S :=
  fun α => g (coeff α f)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) (α : σ →₀ ℕ) :
    coeff α (cmap g f) = g (coeff α f) := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem swap_cmap {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (g : R → S)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (cmap g c) = cmap g (swap c) := by
  ext α
  obtain ⟨⟨a, e⟩, rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm.surjective α
  have h : (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm (a, e) = Finsupp.sumElim a e := rfl
  rw [h, coeff_cmap, SwapCoeff.coeff_swap, SwapCoeff.coeff_swap, coeff_cmap]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem coeff_subst_elim_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (β : Fin d →₀ ℕ) :
    coeff β (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      coeff (Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) β) c := by
  classical
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) :=
    hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
  have hb : HasSubst (X ∘ (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) :
      Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  have hr : rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)
      (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      subst (fun s : Fin d ⊕ Fin d => if s.isLeft then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0) c := by
    rw [rename_eq_subst, subst_comp_subst_apply ha hb]
    congr 1
    funext s
    rcases s with i | i
    · simp [subst_X hb]
    · simp only [Sum.elim_inr, Sum.isLeft_inr]
      rw [← coe_substAlgHom hb, map_zero]
      rfl
  rw [← coeff_embDomain_rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d), hr,
    OnePair.coeff_subst_kill]
  rw [if_pos]
  rintro (i | i) hi
  · simp at hi
  · simp [Finsupp.embDomain_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isLift : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  intro B O _ _ θ hθ d μ hμ
  classical
  by_cases h1 : (1 : O) = 0
  ·
    haveI : Subsingleton O := subsingleton_of_zero_eq_one h1.symm
    have hm : ∀ i, map θ (addLaw B d i) = μ i := fun i => by
      ext α
      exact Subsingleton.elim _ _
    have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) B)) fun (_ : Fin d) => 0) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    have hs : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun i => X (Sum.inl i)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    refine ⟨addLaw B d, ⟨fun i => by simp [addLaw], ?_, fun i => ?_, ?_⟩, hm⟩
    · funext i
      simp only [op, at2, addLaw]
      rw [subst_add ha, subst_X ha, subst_X ha]
      simp
    · simp only [swap, at2, addLaw]
      rw [subst_add hs, subst_X hs, subst_X hs]
      simp [add_comm]
    · have : (fun i => map θ (addLaw B d i)) = μ := funext hm
      rw [this]
      exact hμ
  ·
    let s : O → B := fun x => if x = 0 then 0 else if x = 1 then 1 else (hθ x).choose
    have hs : ∀ x, θ (s x) = x := fun x => by
      simp only [s]
      split_ifs with h h'
      · rw [map_zero, h]
      · rw [map_one, h']
      · exact (hθ x).choose_spec
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s, h1]
    refine ⟨fun i => cmap s (μ i), ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_cmap, coeff_zero_eq_constantCoeff_apply,
        hμ.const i, hs0]
    · funext i
      ext β
      have hu := congrArg (coeff β) (congrFun hμ.unit i)
      simp only [op, at2] at hu ⊢
      rw [coeff_subst_elim_zero] at hu ⊢
      rw [coeff_cmap, hu, coeff_X, coeff_X]
      split_ifs
      · exact hs1
      · exact hs0
    · rw [swap_cmap, hμ.comm i]
    · have : (fun i => map θ (cmap s (μ i))) = μ := funext fun i => by
        ext α
        rw [coeff_map, coeff_cmap, hs]
      rw [this]
      exact hμ
    · ext α
      rw [coeff_map, coeff_cmap, hs]

end GlobalTheory.LiftLaw
