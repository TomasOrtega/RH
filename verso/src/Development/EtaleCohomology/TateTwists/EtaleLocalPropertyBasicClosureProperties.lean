import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosure

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
/- English proof (translation)
Supply the required witnesses or components.
-/
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
