import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinVariety
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinVariety

variable {K : Type} {ι : K → Type}

def varEquiv : Option (Σ k, ι k) ≃ (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) where
  toFun
    | none => ⟨.inr (), (0 : Fin 1)⟩
    | some p => liftVar (ι := ι) ptIdx p
  invFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  left_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
  right_inv := by
    rintro ⟨(k | u), i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl

/- English proof (translation)
The claim follows from `(varEquiv (ι := ι)).injective.comp (Option.some_injective _)`.
-/
theorem liftVar_injective : Function.Injective (liftVar (ι := ι) ptIdx) :=
  (varEquiv (ι := ι)).injective.comp (Option.some_injective _)

def retr (F : Type) [Field F] :
    MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F →ₐ[F] MvPolynomial (Σ k, ι k) F :=
  aeval fun t => match t with
    | ⟨.inl k, i⟩ => X ⟨k, i⟩
    | ⟨.inr _, _⟩ => 1

/- English proof (translation)
Establish `: (retr F).comp (rename (liftVar (ι` using `ι) ptIdx)) = AlgHom.id F _ := by`. Use extensionality with `⟨k, i⟩`. Simplify using `[retr, liftVar]`. Conclude with `congrArg (fun φ => φ p) this`.
-/
theorem retr_rename (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by
  have : (retr F).comp (rename (liftVar (ι := ι) ptIdx)) = AlgHom.id F _ := by
    ext ⟨k, i⟩
    simp [retr, liftVar]
  exact congrArg (fun φ => φ p) this

end JoinVariety

open JoinVariety in
/- English proof (translation)
Introduce `F _ K _ ι _ V n hV`. Take `⟨⟨hprime, ⟨S0, hS0, hspan⟩, hrel⟩, hdim⟩` from `hV`. Use `set V' := V.map (rename (liftVar (ι := ι) ptIdx))`. Set `Φ : Polynomial (MvPolynomial (Σ k, ι k) F) ≃ₐ[F] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F` to `(optionEquivLeft F (Σ k, ι k)).symm.trans (renameEquiv F varEquiv)`. Establish `hΦC : (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _).comp Polynomial.C = (rename (liftVar (ι` using `ι) ptIdx) : MvPolynomial (Σ k, ι k) F →ₐ[F] _).toRingHom := by`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Establish `h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r)) = C r`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Simplify using the standard rewrite rules.

Use `show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r))) = _`. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Introduce `s`. Establish `h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s)) = X (some s)`.

Rewrite using `[AlgEquiv.symm_apply_eq]`. Simplify using the standard rewrite rules. Use `show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s))) = _`. Rewrite using `[h1]`. Simplify using `[varEquiv]`.

Establish `hV' : V' = (V.map (Polynomial.C : MvPolynomial (Σ k, ι k) F →+* Polynomial (MvPolynomial (Σ k, ι k) F))).map (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _)`. Rewrite using `[Ideal.map_map, hΦC]`. Both sides reduce to the same expression. Establish `hmem : ∀ y, y ∈ V' → retr F y ∈ V`. Establish `: V' ≤ V.comap (retr F : _ →ₐ[F] MvPolynomial (Σ k, ι k) F).toRingHom`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `v hv`. Simplify `hv` using `[Ideal.mem_comap, retr_rename]`. Conclude with `fun y hy => this hy`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hV']`. Conclude with `Ideal.map_isPrime_of_equiv _`. Use `⟨rename (liftVar (ι := ι) ptIdx) '' S0, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS0 f hf`.

Use `⟨Sum.elim a 0, ?_⟩` and prove the remaining obligations. Introduce `m hm k`. Rewrite `hm` using `[support_rename_of_injective liftVar_injective]`. Take `⟨m0, hm0, rfl⟩` from `Finset.mem_image.mp hm`. Consider the cases of `k with`.

Consider the case `inl k`. Express the relevant statement in the definitionally equal form `∑ i : ι k, (Finsupp.mapDomain (liftVar (ι := ι) ptIdx) m0) (liftVar (ι := ι) ptIdx ⟨k, i⟩) = a k`. Simplify using `only [Finsupp.mapDomain_apply liftVar_injective]`. Conclude with `ha m0 hm0 k`. Consider the case `inr u`.

Simplify using `only [Sum.elim_inr, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨p, hp⟩`. Consider the cases of `hp`. Express the relevant statement in the definitionally equal form `V.map _ = _`.

Rewrite using `[hspan, Ideal.map_span]`. Introduce and unpack `(k | u)`. Take `⟨i, hi⟩` from `hrel k`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Use `hmem _ h` as an intermediate fact.

Simplify `this` using `[retr]`. Use `⟨(0 : Fin 1), fun h => hprime.ne_top ?_⟩` and prove the remaining obligations. Use `hmem _ h` as an intermediate fact. Rewrite using `[Ideal.eq_top_iff_one]`. Simplify `this` using `[retr]`.

Establish `e1 : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (Sum.elim ι ptIdx) ⧸ V') ≃+* Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)` using `(Ideal.quotientEquiv _ _ Φ.toRingEquiv hV').symm.trans (Ideal.polynomialQuotientEquivQuotientPolynomial V).symm`. Use `(ringKrullDim_eq_of_ringEquiv (S := Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)) e1).trans ?_` and prove the remaining obligations. Rewrite using `[Polynomial.ringKrullDim_of_isNoetherianRing]`. Express the relevant statement in the definitionally equal form `ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) + 1 = _`. Rewrite using `[hdim, Fintype.card_sum, Fintype.card_unit]`.

Use `norm_cast`.
-/
theorem JoinVariety.proof : JoinVariety.Statement := by
  intro F _ K _ ι _ V n hV
  obtain ⟨⟨hprime, ⟨S0, hS0, hspan⟩, hrel⟩, hdim⟩ := hV
  set V' := V.map (rename (liftVar (ι := ι) ptIdx))

  let Φ : Polynomial (MvPolynomial (Σ k, ι k) F) ≃ₐ[F] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F :=
    (optionEquivLeft F (Σ k, ι k)).symm.trans (renameEquiv F varEquiv)
  have hΦC : (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _).comp Polynomial.C =
      (rename (liftVar (ι := ι) ptIdx) : MvPolynomial (Σ k, ι k) F →ₐ[F] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r)) = C r := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r))) = _
      rw [h1]
      simp
    · intro s
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s)) = X (some s) := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s))) = _
      rw [h1]
      simp [varEquiv]
  have hV' : V' = (V.map (Polynomial.C : MvPolynomial (Σ k, ι k) F →+* Polynomial (MvPolynomial (Σ k, ι k) F))).map (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _) := by
    rw [Ideal.map_map, hΦC]
    rfl

  have hmem : ∀ y, y ∈ V' → retr F y ∈ V := by
    have : V' ≤ V.comap (retr F : _ →ₐ[F] MvPolynomial (Σ k, ι k) F).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro v hv
      simpa [Ideal.mem_comap, retr_rename] using hv
    exact fun y hy => this hy
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hV']
    exact Ideal.map_isPrime_of_equiv _
  · refine ⟨rename (liftVar (ι := ι) ptIdx) '' S0, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hS0 f hf
      refine ⟨Sum.elim a 0, ?_⟩
      classical
      intro m hm k
      rw [support_rename_of_injective liftVar_injective] at hm
      obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
      cases k with
      | inl k =>
        change ∑ i : ι k, (Finsupp.mapDomain (liftVar (ι := ι) ptIdx) m0)
          (liftVar (ι := ι) ptIdx ⟨k, i⟩) = a k
        simp only [Finsupp.mapDomain_apply liftVar_injective]
        exact ha m0 hm0 k
      | inr u =>
        simp only [Sum.elim_inr, Pi.zero_apply]
        refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨p, hp⟩
        cases hp
    · change V.map _ = _
      rw [hspan, Ideal.map_span]
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have := hmem _ h
      simpa [retr] using this
    · refine ⟨(0 : Fin 1), fun h => hprime.ne_top ?_⟩
      have := hmem _ h
      rw [Ideal.eq_top_iff_one]
      simpa [retr] using this
  · have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (Sum.elim ι ptIdx) ⧸ V') ≃+*
        Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V) :=
      (Ideal.quotientEquiv _ _ Φ.toRingEquiv hV').symm.trans
        (Ideal.polynomialQuotientEquivQuotientPolynomial V).symm
    refine (ringKrullDim_eq_of_ringEquiv
      (S := Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)) e1).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    change ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) + 1 = _
    rw [hdim, Fintype.card_sum, Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
