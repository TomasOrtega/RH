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
Rewrite using `[WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]`. Simplify using the standard rewrite rules.
-/
theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

/- English proof (translation)
Take `⟨φ⟩` from `hc`. Establish `h1 : IsSmoothChar (detChar (Fin 1) χ)` using `(isSmooth_ofChar_iff _).1 ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)`. Establish `h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R` using `w.adicCompletion E) (Fin 1)) := Units.continuous_map (continuous_matrix fun i j => by`. Rewrite using `[Subsingleton.elim i j]`. Simplify using `using continuous_id')`.

Establish `h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ`. Use `MonoidHom.ext fun z => congrArg χ ?_` and prove the remaining obligations. Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Conclude with `⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩`.
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
Take `⟨a, ha, ε, -, H⟩` from `H`. Introduce `n s π d σ hs g`. Establish `h1` using `(hasSupport_of_isCuspSupport hs).of_equiv (equivRep (toIrrRep π))`. Establish `h2` using `H.supp (cls (toIrrRep π)) _ h1 g`. Rewrite `h2` using `[Multiset.map_map]`.

Conclude with `h2`.
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
Take `⟨a, ha, ε, -, H⟩` from `H`. Introduce `χ c hu hc g α hα`. Take `⟨hχ, e⟩` from `cls_eq_ofChar χ c hc`. Simplify using `only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα`. Rewrite using `[hα]`.

Conclude with `hu _`.
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
Take `⟨a, ha, ε, -, H⟩` from `H`. Substitute `hy` using the available equality. Take `⟨π, hπ⟩` from `H.exists_rep y`. Conclude with `⟨Irr.ofIrrRep π, hπ⟩`.
-/
theorem IsRec.surj {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (n : ℕ) (y : WD h)
    (hy : y.lpDim = n) : ∃ π : Irr (w.adicCompletion E) n, rc (cls (toIrrRep π)) = y := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  subst hy
  obtain ⟨π, hπ⟩ := H.exists_rep y
  exact ⟨Irr.ofIrrRep π, hπ⟩

end GlobalTheory.LocLanglands
