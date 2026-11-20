import Development.EtaleCohomology.WeilConjectures.GluePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Assume the hypotheses and unpack their components. Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
