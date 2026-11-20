import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Abstract

variable {R R' : Type*} [CommRing R] [CommRing R']

/- English proof (translation)
Set `I : Ideal R'` to `Ideal.span {q}`. Set `π : R' →+* R' ⧸ I` to `Ideal.Quotient.mk I`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Set `ψ : R →+* R' ⧸ I` to `π.comp φ`. Establish `hker : RingHom.ker π = I` using `Ideal.mk_ker`.

Establish `hIW : I ≤ W'` using `hW' ▸ le_sup_right`. Set `P : Ideal (R' ⧸ I)` to `W'.map π`. Establish `hP : P.IsPrime` using `Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)`. Establish `hPc : W' = P.comap π` using `by show W' = (W'.map π).comap π`. Rewrite using `[Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]`.

Establish `hPψ : W = P.comap ψ`. Establish `h : P.comap ψ = (P.comap π).comap φ` using `(Ideal.comap_comap φ π).symm`. Rewrite using `[h, ← hPc, hc]`. Establish `hPmap : W.map ψ = P` using `by show W.map (π.comp φ) = W'.map π`. Rewrite using `[hW', Ideal.map_sup, ← Ideal.map_map]`.

Establish `: (Ideal.span {q} : Ideal R').map π = ⊥` using `Ideal.map_quotient_self I`. Rewrite using `[this, sup_bot_eq]`. Set `L` to `Localization.localRingHom W P ψ hPψ`. Establish `hLflat : L.Flat` using `RingHom.Flat.localRingHom hflat P W hPψ`. Establish `hcomp : L.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ` using `RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z`.

Establish `hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L = IsLocalRing.maximalIdeal (Localization.AtPrime P)`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp, ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]`. Establish `hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L = (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P))`. Rewrite using `[Ideal.map_map, hcomp, ← Ideal.map_map]`. Establish `hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I`.

Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker]`. Use `show ((J.map (π.comp φ))).comap π = _`. Rewrite using `[← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]`. Set `e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ)` to `(Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))`. Establish `he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x`.

Introduce `s x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (J.map ψ) (π (s * y)) = Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)`. Rewrite using `[map_mul, map_mul]`. Rewrite using `[GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _ e.toAddEquiv he, GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplic …`.

Conclude with `GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _`.
-/
theorem length_cut_of_flat (φ : R →+* R') (q : R') (J W : Ideal R) [W.IsPrime]
    (W' : Ideal R') [W'.IsPrime] (hW' : W' = W.map φ ⊔ Ideal.span {q}) (hc : W'.comap φ = W)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {q})).comp φ).Flat) :
    Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (R' ⧸ (J.map φ ⊔ Ideal.span {q}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  let I : Ideal R' := Ideal.span {q}
  let π : R' →+* R' ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ψ : R →+* R' ⧸ I := π.comp φ
  have hker : RingHom.ker π = I := Ideal.mk_ker
  have hIW : I ≤ W' := hW' ▸ le_sup_right
  let P : Ideal (R' ⧸ I) := W'.map π
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)
  have hPc : W' = P.comap π := by
    show W' = (W'.map π).comap π
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]
  have hPψ : W = P.comap ψ := by
    have h : P.comap ψ = (P.comap π).comap φ := (Ideal.comap_comap φ π).symm
    rw [h, ← hPc, hc]
  have hPmap : W.map ψ = P := by
    show W.map (π.comp φ) = W'.map π
    rw [hW', Ideal.map_sup, ← Ideal.map_map]
    have : (Ideal.span {q} : Ideal R').map π = ⊥ := Ideal.map_quotient_self I
    rw [this, sup_bot_eq]
  let L := Localization.localRingHom W P ψ hPψ
  have hLflat : L.Flat := RingHom.Flat.localRingHom hflat P W hPψ
  have hcomp : L.comp (algebraMap R (Localization.AtPrime W)) =
      (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]
  have hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L =
      (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  have hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    show ((J.map (π.comp φ))).comap π = _
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]
  let e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ) :=
    (Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))
  have he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J.map ψ) (π (s * y)) =
      Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)
    rw [map_mul, map_mul]
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _
      e.toAddEquiv he,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ← hJ]
  exact GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _

end Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toPoly : MRing (Tb ι) →+* Polynomial (Polynomial (MRing ι)) :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, j⟩ => (![Polynomial.X, Polynomial.C Polynomial.X] : Fin 2 → _) j
    | ⟨some k, i⟩ => Polynomial.C (Polynomial.C (X ⟨k, i⟩))) :
      MRing (Tb ι) →ₐ[ℤ] Polynomial (Polynomial (MRing ι))).toRingHom

def ofPoly : Polynomial (Polynomial (MRing ι)) →+* MRing (Tb ι) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom inc yN) xN

/- English proof (translation)
Simplify using `only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Both sides reduce to the same expression.
-/
theorem toPoly_xN : toPoly (xN : MRing (Tb ι)) = Polynomial.X := by
  simp only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

/- English proof (translation)
Simplify using `only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Both sides reduce to the same expression.
-/
theorem toPoly_yN : toPoly (yN : MRing (Tb ι)) = Polynomial.C Polynomial.X := by
  simp only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[toPoly, inc]`. Introduce `i`. Simplify using `[toPoly, inc, oldIdx]`.
-/
theorem toPoly_comp_inc : (toPoly.comp inc : MRing ι →+* _) = Polynomial.C.comp Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [toPoly, inc]
  · intro i; simp [toPoly, inc, oldIdx]

/- English proof (translation)
The claim follows from `congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))`.
-/
theorem toPoly_inc (f : MRing ι) : toPoly (inc f) = Polynomial.C (Polynomial.C f) :=
  congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[toPoly, ofPoly]`. Introduce and unpack `⟨o, i⟩`. Consider the cases of `o with`.

Consider the case `none`. Express the relevant statement in the definitionally equal form `Fin 2 at i`. Use `fin_cases i`. Establish `: (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN` using `rfl`. Simplify using `[this, toPoly_xN, ofPoly]`.

Establish `: (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN` using `rfl`. Simplify using `[this, toPoly_yN, ofPoly]`. Consider the case `some k`. Simplify using `[toPoly, ofPoly, inc, oldIdx]`.
-/
theorem ofPoly_comp_toPoly : (ofPoly.comp toPoly : MRing (Tb ι) →+* _) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toPoly, ofPoly]
  · rintro ⟨o, i⟩
    cases o with
    | none =>
      change Fin 2 at i
      fin_cases i
      · have : (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN := rfl
        simp [this, toPoly_xN, ofPoly]
      · have : (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN := rfl
        simp [this, toPoly_yN, ofPoly]
    | some k =>
      simp [toPoly, ofPoly, inc, oldIdx]

/- English proof (translation)
Apply `Polynomial.ringHom_ext'` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext'` to reduce the goal to its premises. Use `RingHom.ext fun f => ?_` and prove the remaining obligations. Simplify using `[ofPoly, toPoly_inc]`. Simplify using `[ofPoly, toPoly_yN]`.

Simplify using `[ofPoly, toPoly_xN]`.
-/
theorem toPoly_comp_ofPoly :
    (toPoly.comp ofPoly : Polynomial (Polynomial (MRing ι)) →+* _) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun f => ?_
      simp [ofPoly, toPoly_inc]
    · simp [ofPoly, toPoly_yN]
  · simp [ofPoly, toPoly_xN]

def polyEquiv : MRing (Tb ι) ≃+* Polynomial (Polynomial (MRing ι)) :=
  RingEquiv.ofRingHom toPoly ofPoly toPoly_comp_ofPoly ofPoly_comp_toPoly

/- English proof (translation)
Use `⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩` and prove the remaining obligations. Establish `h : toPoly (C (p : ℤ) : MRing (Tb ι)) = Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι))`. Simplify `toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)` using `[inc]`. Simplify using `[quad, toPoly_xN, toPoly_yN, h]`.
-/
theorem toPoly_quad (p : ℕ) : ∃ s : Polynomial (MRing ι),
    toPoly (quad p : MRing (Tb ι)) = Polynomial.X ^ 2 + Polynomial.C s := by
  refine ⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩
  have h : toPoly (C (p : ℤ) : MRing (Tb ι)) =
      Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι)) := by
    simpa [inc] using toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)
  simp [quad, toPoly_xN, toPoly_yN, h]

/- English proof (translation)
Take `⟨s, hs⟩` from `toPoly_quad (ι := ι) p`. Set `g : Polynomial (Polynomial (MRing ι))` to `Polynomial.X ^ 2 + Polynomial.C s`. Establish `hg : g.Monic` using `Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))`. Establish `: Module.Free (Polynomial (MRing ι)) (AdjoinRoot g)` using `Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis`. Establish `h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat` using `RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))`.

Establish `h2 : (AdjoinRoot.of g).Flat` using `RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))`. Set `E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g` to `Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `show Ideal.span {g} = Ideal.span {toPoly (quad p)}`. Rewrite using `[hs])`.

Establish `h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat` using `RingHom.Flat.of_bijective E.symm.bijective`. Establish `hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc = (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C)`. Use `RingHom.ext fun f => ?_` and prove the remaining obligations. Use `show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))`. Rewrite using `[RingEquiv.eq_symm_apply]`.

Use `show Ideal.Quotient.mk _ (toPoly (inc f)) = _`. Rewrite using `[toPoly_inc]`. Both sides reduce to the same expression. Rewrite using `[hcomp]`. Conclude with `(h1.comp h2).comp h3`.
-/
theorem flat_quad (p : ℕ) :
    ((Ideal.Quotient.mk (Ideal.span {quad p})).comp inc :
      MRing ι →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat := by
  obtain ⟨s, hs⟩ := toPoly_quad (ι := ι) p
  let g : Polynomial (Polynomial (MRing ι)) := Polynomial.X ^ 2 + Polynomial.C s
  have hg : g.Monic := Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  have : Module.Free (Polynomial (MRing ι)) (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))
  have h2 : (AdjoinRoot.of g).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))
  let E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g :=
    Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by
      rw [Ideal.map_span, Set.image_singleton]
      show Ideal.span {g} = Ideal.span {toPoly (quad p)}
      rw [hs])
  have h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat :=
    RingHom.Flat.of_bijective E.symm.bijective
  have hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc =
      (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C) := by
    refine RingHom.ext fun f => ?_
    show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))
    rw [RingEquiv.eq_symm_apply]
    show Ideal.Quotient.mk _ (toPoly (inc f)) = _
    rw [toPoly_inc]
    rfl
  rw [hcomp]
  exact (h1.comp h2).comp h3

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.1.1`. Unfold `multAt`. Rewrite using `[dif_pos hT, dif_pos hWp]`. Conclude with `congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl (comap_inc_twist p W) (flat_quad p))`.
-/
theorem multAt_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (J W : Ideal (MRing ι)) (hW : W ∈ J.minimalPrimes) (hT : (twist p W).IsPrime) :
    multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  have hWp : W.IsPrime := hW.1.1
  unfold multAt
  rw [dif_pos hT, dif_pos hWp]
  exact congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl
    (comap_inc_twist p W) (flat_quad p))

end GlobalTheory.CompanionTheory.Ar.Tw
