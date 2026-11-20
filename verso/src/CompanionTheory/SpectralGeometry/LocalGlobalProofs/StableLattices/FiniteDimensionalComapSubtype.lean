import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open CompanionTheory.RgExh
open Formalism.REAL (GlRel IsWeight)
open CompanionTheory.D.LK (LocFin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem pathFin : CompanionTheory.RgExh.Fin.PathFin := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    constructor
    · intro h
      first
        | exact (ih _ _).1 (locFin_step ε X _ h)
        | exact locFin_step ε _ _ ((ih X χ).1 h)
        | exact locFin_step ε _ _ ((ih _ _).1 h)
    · intro h
      first
        | exact (ih _ _).2 (intWt_step X _ h)
        | exact intWt_step _ _ ((ih X χ).2 h)
        | exact intWt_step _ _ ((ih _ _).2 h)

end GlobalTheory.CompanionTheory.RgSteps
