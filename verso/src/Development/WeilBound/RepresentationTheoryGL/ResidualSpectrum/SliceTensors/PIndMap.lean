import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapF

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs

namespace InducedTensorMap.Main

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem act_fin_val {a : ℕ} (g : GL (Fin a) (Af E)) (F : Sm E a) :
    (act (.fin g) F).1 = fun y => F.1 (y * cf a 1 g) := by
  funext y
  simp [cf]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem act_cpt_val {a : ℕ} (k : Kinf E a) (F : Sm E a) :
    (act (.cpt k) F).1 = fun y => F.1 (y * cf a k 1) := by
  funext y
  simp [cf]
  rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem finVec_of_equiv {N : ℕ} {V : Submodule ℂ (Sm E N)} {T : Sm E N →ₗ[ℂ] Sm E N}
    (hT : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) {φ : Sm E N} (hφ : φ ∈ V)
    (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k φ))) :
    T φ ∈ finVec (cptRep E N) := by
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (T φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E N k φ)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  exact hT (.cpt k) φ hφ

end InducedTensorMap.Main

open InducedTensorMap InducedTensorMap.Main in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Split into cases according to the possible forms of the given data. Treat this case separately. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Treat this case separately.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem indMap_holds : IndMap := by
  intro E _ _ _ r s V U₁ U₂ T f₁ f₂ hV hVa hU₁ hU₂ hT hTi hf₁ hf₂
  have H : Good U₁ U₂ f₁ f₂ := ⟨hU₁, hU₂, hf₁, hf₂⟩
  have hI : ∀ φ ∈ V, T φ ∈ indSub U₁ U₂ := fun φ hφ => ⟨(hTi φ hφ).1, fun k g => (hTi φ hφ).2 k g⟩
  have hK : ∀ φ ∈ V, T φ ∈ finVec (cptRep E (r + s)) := fun φ hφ => finVec_of_equiv hT hφ (hVa φ hφ).kfin
  let L : V →ₗ[ℂ] Sm E (r + s) :=
    { toFun := fun φ => ⟨ind f₁ f₂ (T φ.1).1, ind_mem_Sm H (hI _ φ.2) (hK _ φ.2)⟩
      map_add' := fun φ ψ => Subtype.ext (by
        change ind f₁ f₂ (T (φ.1 + ψ.1)).1 = ind f₁ f₂ (T φ.1).1 + ind f₁ f₂ (T ψ.1).1
        rw [map_add, Submodule.coe_add, map_add])
      map_smul' := fun c φ => Subtype.ext (by
        change ind f₁ f₂ (T (c • φ.1)).1 = c • ind f₁ f₂ (T φ.1).1
        rw [map_smul, Submodule.coe_smul, map_smul]) }
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend L
  have e : ∀ φ (hφ : φ ∈ V), (T' φ).1 = ind f₁ f₂ (T φ).1 := fun φ hφ =>
    congrArg Subtype.val (LinearMap.congr_fun hT' ⟨φ, hφ⟩)
  refine ⟨T', fun o φ hφ => ?_, fun φ hφ x g => ?_, fun φ hφ k g n ψ₁ ψ₂ _ _ hs m => ?_⟩
  · have ho := hV o φ hφ
    apply Subtype.ext
    rw [e _ ho, hT o φ hφ]
    cases o with
    | fin g =>
      rw [act_fin_val, act_fin_val, e _ hφ]
      funext x
      exact ind_rt H (hI φ hφ) 1 g x
    | cpt k =>
      rw [act_cpt_val, act_cpt_val, e _ hφ]
      funext x
      exact ind_rt H (hI φ hφ) k 1 x
    | lie X =>
      have hX : lie E (r + s) X (T φ) ∈ indSub U₁ U₂ := by
        have := hT (.lie X) φ hφ
        change T (lie E (r + s) X φ) = lie E (r + s) X (T φ) at this
        rw [← this]
        exact hI _ (hV (.lie X) φ hφ)
      change ind f₁ f₂ (lie E (r + s) X (T φ)).1 = lieD X (T' φ).1
      rw [e _ hφ]
      exact ind_lie H (hI φ hφ) (hK φ hφ) X hX
  · rw [e φ hφ]
    exact ind_left H (hI φ hφ) x g
  · rw [e φ hφ]
    have hres : res (cf (r + s) k g) (T φ).1 = fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := funext hs
    have h1 := congrFun (ind_levi H (hI φ hφ) k g) m
    rw [res_apply] at h1
    change ind f₁ f₂ (T φ).1 (lev (Ad E) r s m * cf (r + s) k g) = _
    rw [h1, hres, tensOp_sum]

end PositivityTheory.Rg.Rs

end
