import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem IsRec.recSupp {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecSupp fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro n s π d σ hs g
  have h1 := (hasSupport_of_isCuspSupport hs).of_equiv (equivRep (toIrrRep π))
  have h2 := H.supp (cls (toIrrRep π)) _ h1 g
  rw [Multiset.map_map] at h2
  exact h2

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem IsRec.recUnit {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsRec.surj {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (n : ℕ) (y : WD h)
    (hy : y.lpDim = n) : ∃ π : Irr (w.adicCompletion E) n, rc (cls (toIrrRep π)) = y := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  subst hy
  obtain ⟨π, hπ⟩ := H.exists_rep y
  exact ⟨Irr.ofIrrRep π, hπ⟩

end GlobalTheory.LocLanglands
