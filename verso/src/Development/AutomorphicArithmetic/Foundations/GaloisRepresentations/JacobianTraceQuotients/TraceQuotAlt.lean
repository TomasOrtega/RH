import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dif_pos hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add, hzero, add_zero]
