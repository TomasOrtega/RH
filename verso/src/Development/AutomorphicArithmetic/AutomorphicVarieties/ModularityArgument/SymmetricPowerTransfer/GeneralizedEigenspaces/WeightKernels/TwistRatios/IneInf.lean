import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem ine_of_emb {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ L Ω] (A : ValuationSubring Ω) (s : G L Ω)
    (h : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A) : s ∈ Ine (F := L) A := h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Ga.ineInf :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∈ Ine (F := L) A ∧ ¬ IsOfFinOrder (cycBar L Ω l s) := by
  intro L Ω _ _ _ _ _ l _ A hA H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L Ω⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  haveI : Finite (G L Ω ⧸ H) := H.quotient_finite_of_isOpen hH
  obtain ⟨hemb, -, hidx⟩ := Base.galEmbTop ℚ L Ω
  have hrange : (Base.galEmb ℚ L Ω).range = Base.galOf ℚ L Ω := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact Base.galEmb_mem ℚ L Ω s
    · intro σ hσ
      refine ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x }, ?_⟩
      ext x
      rw [Base.galEmb_apply]
      rfl
  have hfin : (H.map (Base.galEmb ℚ L Ω)).index ≠ 0 := by
    rw [H.index_map_of_injective hemb.injective, hrange, hidx]
    exact mul_ne_zero Subgroup.index_ne_zero_of_finite Module.finrank_pos.ne'
  haveI : (H.map (Base.galEmb ℚ L Ω)).FiniteIndex := ⟨hfin⟩
  have hu : IsUnit ((1 : ℤ_[l]) + l) := by
    by_contra h
    have h1 : (l : ℤ_[l]) ∣ 1 + l :=
      (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr h))
    have hl : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_one ((dvd_add_left (dvd_refl _)).mp h1)
    have h2 : ‖(l : ℤ_[l])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr (dvd_refl _)
    rw [PadicInt.isUnit_iff.mp hl] at h2
    exact lt_irrefl _ h2
  have hv : ¬ IsOfFinOrder hu.unit := by
    intro hv
    obtain ⟨n, hn, hpow⟩ := hv.exists_pow_eq_one
    have h2 : ((1 : ℤ_[l]) + l) ^ n = 1 := by
      have := congrArg Units.val hpow
      simpa using this
    have h3 : ((1 + l) ^ n : ℕ) = 1 := by
      exact_mod_cast h2
    rcases Nat.pow_eq_one.mp h3 with h4 | h4
    · have := (Fact.out : l.Prime).pos
      omega
    · omega
  obtain ⟨τ, hτ, hτv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  have hpow : τ ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index ∈ H.map (Base.galEmb ℚ L Ω) :=
    Subgroup.normalCore_le _ (Subgroup.pow_index_mem _ τ)
  obtain ⟨s, hs, hsτ⟩ := hpow
  have hsI : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := by
    rw [hsτ]
    exact Subgroup.pow_mem _ hτ _
  refine ⟨s, hs, ine_of_emb A s hsI, ?_⟩
  have hcyc : cycZ L Ω l s = cycZ ℚ Ω l (Base.galEmb ℚ L Ω s) := by
    simp only [cycZ, MonoidHom.comp_apply]
    congr 1
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hmap : Function.Injective (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l)) := by
    intro a b hab
    exact Units.ext (hinj (congrArg Units.val hab))
  intro hfo
  have hval : cycBar L Ω l s = Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l) (hu.unit ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index) := by
    simp only [cycBar, MonoidHom.comp_apply, hcyc, hsτ, map_pow, hτv]
    rfl
  rw [hval, ← orderOf_pos_iff, orderOf_injective _ hmap, orderOf_pos_iff, isOfFinOrder_pow] at hfo
  rcases hfo with h | h
  · exact hv h
  · exact Subgroup.FiniteIndex.index_ne_zero h
