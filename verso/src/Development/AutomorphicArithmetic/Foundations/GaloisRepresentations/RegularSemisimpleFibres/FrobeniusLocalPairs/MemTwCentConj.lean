import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Unfold `GlobalTheory.LBC.norm normGL twNorm`. Use `congr 1`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`.

Simplify using `only [List.getElem_ofFn, List.getElem_map, List.getElem_range]`. Use `show (sigmaGL (σ ^ i) : Monoid.End (GL (Fin n) E)) δ = _`. Rewrite using `[sigmaGL_pow]`.
-/
private theorem norm_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n : ℕ)
    (δ : GL (Fin n) E) : GlobalTheory.LBC.norm k σ δ = normGL σ δ := by
  unfold GlobalTheory.LBC.norm normGL twNorm
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    show (sigmaGL (σ ^ i) : Monoid.End (GL (Fin n) E)) δ = _
    rw [sigmaGL_pow]

/- English proof (translation)
Use `show ((GeneralLinearGroup.map (algebraMap k E) γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = _`. Rewrite using `[← Matrix.charpoly_map]`. Both sides reduce to the same expression.
-/
private theorem charpoly_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
      (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
  show ((GeneralLinearGroup.map (algebraMap k E) γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = _
  rw [← Matrix.charpoly_map]
  rfl

/- English proof (translation)
Unfold `twConj`. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]`. Use `group`.
-/
private theorem twConj_conj {G : Type} [Group G] (θ : Monoid.End G) (h x δ : G) :
    twConj θ (h⁻¹ * x * h) (twConj θ h δ) = h⁻¹ * twConj θ x δ * θ h := by
  unfold twConj
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group

/- English proof (translation)
Use `show twConj θ x δ = δ ↔ twConj θ (h⁻¹ * x * h) (twConj θ h δ) = twConj θ h δ`. Rewrite using `[twConj_conj]`. Unfold `twConj`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Rewrite using `[hx]`. Introduce `hx`. Use `congrArg (fun y => h * y * (θ h)⁻¹) hx` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
private theorem mem_twCent_conj {G : Type} [Group G] (θ : Monoid.End G) (h x δ : G) :
    x ∈ twCent θ δ ↔ h⁻¹ * x * h ∈ twCent θ (twConj θ h δ) := by
  show twConj θ x δ = δ ↔ twConj θ (h⁻¹ * x * h) (twConj θ h δ) = twConj θ h δ
  rw [twConj_conj]
  unfold twConj
  constructor
  · intro hx
    rw [hx]
  · intro hx
    have := congrArg (fun y => h * y * (θ h)⁻¹) hx
    simpa [mul_assoc] using this

/- English proof (translation)
Use extensionality with `x`. Use `show twConj θ x δ = δ ↔ x * δ = δ * θ x`. Unfold `twConj`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Combine the equalities or inequalities in the displayed calculation. Introduce `hx`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem twCent_eq {G : Type} [Group G] (θ : Monoid.End G) (δ : G) :
    twCent θ δ = GlobalTheory.BCT.twCent θ δ := by
  ext x
  show twConj θ x δ = δ ↔ x * δ = δ * θ x
  unfold twConj
  constructor
  · intro hx
    calc x * δ = x * (x⁻¹ * δ * θ x) := by rw [hx]
      _ = δ * θ x := by group
  · intro hx
    calc x⁻¹ * δ * θ x = x⁻¹ * (δ * θ x) := by group
      _ = x⁻¹ * (x * δ) := by rw [hx]
      _ = δ := by group

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n`. Establish `hcp : ∀ γ : GL (Fin n) k, ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E)` using `fun γ => charpoly_incl γ`. Establish `hconj : ∀ (h a : GL (Fin n) E), ((h * a * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = (a : Matrix (Fin n) (Fin n) E).charpoly`. Introduce `h a`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv]`.

Conclude with `Matrix.charpoly_units_conj h a`. Establish `hpow : sigmaGL σ ^ Module.finrank k E = (1 : Monoid.End (GL (Fin n) E))`. Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`. Use `⟨rfl, fun δ => norm_eq σ n δ, fun δ => twCent_eq _ δ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ`.

Use extensionality with `x`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `Iff.rfl`. Introduce `δ h γ hreg hN`. Establish `heq : (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly`.

Rewrite using `[hN, hconj, hcp]`. Establish `hγ : IsRegSemisimple γ`. Establish `hs : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable` using `hreg`. Rewrite `hs` using `[← heq]`. Conclude with `(Polynomial.separable_map _).mp hs`.

Use `⟨hγ, heq, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hN' : normGL σ (twConj (sigmaGL σ) h δ) = incl γ`. Unfold `normGL`. Rewrite using `[twNorm_twConj_of_pow_eq_one _ hpow]`.

Express the relevant statement in the definitionally equal form `h⁻¹ * normGL σ δ * h = incl γ`. Rewrite using `[hN]`. Use `group`. Take `⟨_, hc⟩` from `twCentImg_holds k E σ hgen n _ γ hγ hN'`. Rewrite using `[mem_twCent_conj (sigmaGL σ) h x δ, hc, Subgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hx⟩`. Conclude with `⟨t, ht, hx.symm⟩`. Introduce and unpack `⟨t, ht, hx⟩`. Conclude with `⟨t, ht, hx.symm⟩`.

Introduce `δ γ hγ heq`. Establish `hs : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable`. Rewrite using `[hcp]`. Conclude with `(Polynomial.separable_map _).mpr hγ`. Take `⟨g, hg⟩` from `GlobalTheory.BCT.ClsFin.conj_of_charpoly (incl γ) (normGL σ δ) hs (by rw [hcp, heq])`.

Conclude with `⟨g⁻¹, by rw [hg, inv_inv]⟩`.
-/
theorem dict : Dict := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n
  have hcp : ∀ γ : GL (Fin n) k,
      ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := fun γ => charpoly_incl γ
  have hconj : ∀ (h a : GL (Fin n) E),
      ((h * a * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
        (a : Matrix (Fin n) (Fin n) E).charpoly := by
    intro h a
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj h a
  have hpow : sigmaGL σ ^ Module.finrank k E = (1 : Monoid.End (GL (Fin n) E)) := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨rfl, fun δ => norm_eq σ n δ, fun δ => twCent_eq _ δ, ?_, ?_, ?_⟩
  · intro γ
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  · intro δ h γ hreg hN
    have heq : (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) =
        ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
      rw [hN, hconj, hcp]
    have hγ : IsRegSemisimple γ := by
      have hs : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := hreg
      rw [← heq] at hs
      exact (Polynomial.separable_map _).mp hs
    refine ⟨hγ, heq, ?_⟩
    intro x
    have hN' : normGL σ (twConj (sigmaGL σ) h δ) = incl γ := by
      unfold normGL
      rw [twNorm_twConj_of_pow_eq_one _ hpow]
      change h⁻¹ * normGL σ δ * h = incl γ
      rw [hN]
      group
    obtain ⟨_, hc⟩ := twCentImg_holds k E σ hgen n _ γ hγ hN'
    rw [mem_twCent_conj (sigmaGL σ) h x δ, hc, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, ht, hx.symm⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, ht, hx.symm⟩
  · intro δ γ hγ heq
    have hs : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
      rw [hcp]
      exact (Polynomial.separable_map _).mpr hγ
    obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly (incl γ) (normGL σ δ) hs (by rw [hcp, heq])
    exact ⟨g⁻¹, by rw [hg, inv_inv]⟩

end UpperTheory.Gal.InertialTypesAlt.L
