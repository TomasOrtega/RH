import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.FrobeniusTrace

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Take `⟨x, hx, hne⟩` from `CentAtP.exists_conj_ne G`. Apply `hne` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises. Establish `a` using `h1 ⟨x, hx⟩`. Establish `b` using `h2 ⟨x, hx⟩`.

Conclude with `b.trans a.symm`.
-/
private theorem not_both (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (h1 : LiesOver G.Kq G.u τ)
    (h2 : LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))) : False := by
  obtain ⟨x, hx, hne⟩ := CentAtP.exists_conj_ne G
  apply hne
  apply τ.injective
  have a := h1 ⟨x, hx⟩
  have b := h2 ⟨x, hx⟩
  exact b.trans a.symm

/- English proof (translation)
Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_splits (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s`. Use `⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.ofBijective_apply]`. Conclude with `congrArg (fun f => f y) hφ`.
-/
private theorem exists_ext (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : E, σ (y : PadicAlgCl p) = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact congrArg (fun f => f y) hφ

/- English proof (translation)
Use `IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p] (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `h x`.
-/
private theorem hom_ext {F : Type} [Field F] (τ : F →+* PadicAlgCl p)
    (s s' : FwOf τ →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (embOf τ x) = s' (embOf τ x)) : s = s' := by
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p]
    (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_ext _ s`. Take `⟨σ', hσ'⟩` from `exists_ext _ s'`. Establish `hw : w = w'`. Use `G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)` and prove the remaining obligations. Establish `e1 : σ (G.emb w x) = s (G.embW w x)` using `hσ (G.embW w x)`.

Establish `e2 : σ' (G.emb w' x) = s' (G.embW w' x)` using `hσ' (G.embW w' x)`. Express the relevant statement in the definitionally equal form `σ'.symm (σ (G.emb w x)) = G.emb w' x`. Rewrite using `[e1, h, ← e2, AlgEquiv.symm_apply_apply]`. Substitute `hw` using the available equality. Rewrite using `[hom_ext (G.emb w) s s' h]`.
-/
private theorem sigma_eq (G : HTGroup p) {w w' : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)
    (s' : G.Fw w' →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (G.embW w x) = s' (G.embW w' x)) :
    (⟨w, s⟩ : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) = ⟨w', s'⟩ := by
  obtain ⟨σ, hσ⟩ := exists_ext _ s
  obtain ⟨σ', hσ'⟩ := exists_ext _ s'
  have hw : w = w' := by
    refine G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)
    have e1 : σ (G.emb w x) = s (G.embW w x) := hσ (G.embW w x)
    have e2 : σ' (G.emb w' x) = s' (G.embW w' x) := hσ' (G.embW w' x)
    change σ'.symm (σ (G.emb w x)) = G.emb w' x
    rw [e1, h, ← e2, AlgEquiv.symm_apply_apply]
  subst hw
  rw [hom_ext (G.emb w) s s' h]

/- English proof (translation)
Introduce `x`. Establish `e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x)` using `Subtype.ext (G.emb_over w x)`. Express the relevant statement in the definitionally equal form `s (G.embW w (x : G.F)) = _`. Rewrite using `[e, s.commutes]`.
-/
private theorem liesOver_comp (G : HTGroup p) {w : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    LiesOver G.Kq G.u ((s : G.Fw w →+* PadicAlgCl p).comp (G.embW w)) := by
  intro x
  have e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x) := Subtype.ext (G.emb_over w x)
  change s (G.embW w (x : G.F)) = _
  rw [e, s.commutes]

private noncomputable def phi (G : HTGroup p) :
    ((Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) ⊕ (Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) →
      (G.F →ₐ[ℚ] PadicAlgCl p)
  | .inl a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1)).toRatAlgHom
  | .inr a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp
      ((G.embW a.1).comp (IsCMField.complexConj G.F : G.F →+* G.F))).toRatAlgHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem phi_inl (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inl a) x = a.2 (G.embW a.1 x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem phi_inr (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inr a) x = a.2 (G.embW a.1 (IsCMField.complexConj G.F x)) := rfl

/- English proof (translation)
Introduce `h`. Use `not_both G _ (liesOver_comp G a.2) fun k => ?_` and prove the remaining obligations. Establish `e` using `DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))`. Rewrite `e` using `[phi_inl, phi_inr, IsCMField.complexConj_apply_apply]`. Conclude with `e.trans (liesOver_comp G b.2 k)`.
-/
private theorem phi_ne (G : HTGroup p) (a b : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    phi G (.inl a) ≠ phi G (.inr b) := by
  intro h
  refine not_both G _ (liesOver_comp G a.2) fun k => ?_
  have e := DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))
  rw [phi_inl, phi_inr, IsCMField.complexConj_apply_apply] at e
  exact e.trans (liesOver_comp G b.2 k)

/- English proof (translation)
Introduce and unpack `(⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab`. Rewrite using `[sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]`. Conclude with `absurd hab (phi_ne G _ _)`. Conclude with `absurd hab.symm (phi_ne G _ _)`. Establish `key : ∀ y, s (G.embW w y) = s' (G.embW w' y)`.

Introduce `y`. Establish `e` using `(phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))`. Rewrite `e` using `[IsCMField.complexConj_apply_apply]`. Then use the resulting hypothesis. Rewrite using `[sigma_eq G s s' key]`.
-/
private theorem phi_injective (G : HTGroup p) : Function.Injective (phi G) := by
  rintro (⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab
  · rw [sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans
      ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]
  · exact absurd hab (phi_ne G _ _)
  · exact absurd hab.symm (phi_ne G _ _)
  · have key : ∀ y, s (G.embW w y) = s' (G.embW w' y) := by
      intro y
      have e := (phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans
        ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))
      rwa [IsCMField.complexConj_apply_apply] at e
    rw [sigma_eq G s s' key]

/- English proof (translation)
Introduce `ψ`. Take `⟨w, σ, h | h⟩` from `hE p G ψ.toRingHom`. Use `⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[phi_inl]`. Conclude with `(h x).symm`.

Use `⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[phi_inr]`. Conclude with `(h x).symm`.
-/
private theorem phi_surjective (hE : EmbAll) (G : HTGroup p) : Function.Surjective (phi G) := by
  intro ψ
  obtain ⟨w, σ, h | h⟩ := hE p G ψ.toRingHom
  · refine ⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inl]
    exact (h x).symm
  · refine ⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inr]
    exact (h x).symm

end UpperTheory.Gal.W2.FrobeniusTrace

open UpperTheory.Gal.W2.FrobeniusTrace in
/- English proof (translation)
Introduce `hE p _ G x`. Apply `(algebraMap ℚ_[p] (PadicAlgCl p)).injective` to reduce the goal to its premises. Rewrite using `[map_add, map_sum, map_sum]`. Establish `hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p]) = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x)`. Simplify using `only [map_ratCast, eq_ratCast]`.

Rewrite using `[hl]`. Repeatedly rewrite using `[trace_eq_sum_embeddings (E := PadicAlgCl p)]`. Rewrite using `[← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩ (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]`. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]`. Simplify using `only [phi_inl, phi_inr]`.
-/
theorem UpperTheory.Gal.W2.fTrace_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FTrace := by
  intro hE p _ G x
  apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  rw [map_add, map_sum, map_sum]
  have hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p])
      = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x) := by
    simp only [map_ratCast, eq_ratCast]
  rw [hl]
  simp_rw [trace_eq_sum_embeddings (E := PadicAlgCl p)]
  rw [← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩
    (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [phi_inl, phi_inr]
