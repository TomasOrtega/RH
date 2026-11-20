import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaC
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBS

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

section Abstract

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime`. Use `next =>`. Introduce `h`. Conclude with `absurd rfl h`. Use `next x hx =>`.

Introduce `_ y hy`. Establish `hy1 : ψ y = 1`. Apply `h1` to reduce the goal to its premises. Introduce `Q`. Rewrite using `[hy Q, UniqueFactorizationMonoid.normalizedFactors_of_isUnit hx]`.

Simplify using the standard rewrite rules. Rewrite using `[Ideal.isUnit_iff.mp hx, Ideal.absNorm_top, hy1]`. Simplify using the standard rewrite rules. Use `next a p ha hp ih =>`. Introduce `_ y hy`.

Set `P : HeightOneSpectrum (𝓞 E)` to `⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩`. Take `⟨z, hzP, hzQ, hzl⟩` from `h3 P`. Establish `hzl' : lam (Ideal.absNorm p) = (ψ z : ℂ) * (Real.sqrt (Ideal.absNorm p) : ℂ)` using `hzl`. Establish `hfac : UniqueFactorizationMonoid.normalizedFactors (p * a) = p ::ₘ UniqueFactorizationMonoid.normalizedFactors a`. Rewrite using `[UniqueFactorizationMonoid.normalizedFactors_mul hp.ne_zero ha, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible, normalize_eq]`.

Both sides reduce to the same expression. Establish `key` using `ih ha (z⁻¹ * y) (by`. Introduce `Q`. Rewrite using `[map_mul, map_inv, hy Q, hfac]`. Distinguish the cases in `hQ : Q = P`.

Establish `hc : Multiset.count Q.asIdeal (p ::ₘ UniqueFactorizationMonoid.normalizedFactors a) = Multiset.count Q.asIdeal (UniqueFactorizationMonoid.normalizedFactors a) + 1`. Rewrite using `[hQ]`. Conclude with `Multiset.count_cons_self _ _`. Rewrite using `[hc, hQ, hzP, ← WithZero.exp_neg, ← WithZero.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : Q.asIdeal ≠ p` using `fun h => hQ (HeightOneSpectrum.ext h)`. Rewrite using `[Multiset.count_cons_of_ne hne, hzQ Q hQ]`. Use the proof step `simp)`.

Establish `hy' : y = z * (z⁻¹ * y)` using `(mul_inv_cancel_left z y).symm`. Rewrite using `[map_mul Ideal.absNorm, map_mul lam, hzl', key]`. Use `conv_rhs => rw [hy', map_mul, Circle.coe_mul]`. Use `push_cast`. Rewrite using `[Real.sqrt_mul (Nat.cast_nonneg _)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lam_absNorm_eq_psi_mul_sqrt {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (ψ : G →* Circle)
    (lam : ℕ →* ℂ)
    (h1 : ∀ y, (∀ Q, w Q y = 1) → ψ y = 1)
    (h3 : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → w Q z = 1) ∧
      lam (Ideal.absNorm P.asIdeal) = (ψ z : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ))
    (I : Ideal (𝓞 E)) : I ≠ 0 → ∀ y : G,
      (∀ Q : HeightOneSpectrum (𝓞 E),
        w Q y = WithZero.exp (-((UniqueFactorizationMonoid.normalizedFactors I).count Q.asIdeal : ℤ))) →
      lam (Ideal.absNorm I) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm I) : ℂ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime
  next =>
    intro h
    exact absurd rfl h
  next x hx =>
    intro _ y hy
    have hy1 : ψ y = 1 := by
      apply h1
      intro Q
      rw [hy Q, UniqueFactorizationMonoid.normalizedFactors_of_isUnit hx]
      simp
    rw [Ideal.isUnit_iff.mp hx, Ideal.absNorm_top, hy1]
    simp
  next a p ha hp ih =>
    intro _ y hy
    let P : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    obtain ⟨z, hzP, hzQ, hzl⟩ := h3 P
    have hzl' : lam (Ideal.absNorm p) = (ψ z : ℂ) * (Real.sqrt (Ideal.absNorm p) : ℂ) := hzl
    have hfac : UniqueFactorizationMonoid.normalizedFactors (p * a) =
        p ::ₘ UniqueFactorizationMonoid.normalizedFactors a := by
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hp.ne_zero ha,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible, normalize_eq]
      rfl
    have key := ih ha (z⁻¹ * y) (by
      intro Q
      rw [map_mul, map_inv, hy Q, hfac]
      by_cases hQ : Q = P
      · have hc : Multiset.count Q.asIdeal (p ::ₘ UniqueFactorizationMonoid.normalizedFactors a) =
            Multiset.count Q.asIdeal (UniqueFactorizationMonoid.normalizedFactors a) + 1 := by
          rw [hQ]
          exact Multiset.count_cons_self _ _
        rw [hc, hQ, hzP, ← WithZero.exp_neg, ← WithZero.exp_add]
        congr 1
        push_cast
        ring
      · have hne : Q.asIdeal ≠ p := fun h => hQ (HeightOneSpectrum.ext h)
        rw [Multiset.count_cons_of_ne hne, hzQ Q hQ]
        simp)
    have hy' : y = z * (z⁻¹ * y) := (mul_inv_cancel_left z y).symm
    rw [map_mul Ideal.absNorm, map_mul lam, hzl', key]
    conv_rhs => rw [hy', map_mul, Circle.coe_mul]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    push_cast
    ring

/- English proof (translation)
Establish `hu : u ≠ 0`. Introduce and unpack `rfl`. Conclude with `k.ne_zero (by simpa using hk)`. Establish `hI : Ideal.span {u} ≠ (0 : Ideal (𝓞 E))`. Simplify `hu` using `[Ideal.zero_eq_bot]`.

Use `lam_absNorm_eq_psi_mul_sqrt w ψ lam h1 h3 (Ideal.span {u}) hI (i k) ?_` and prove the remaining obligations. Introduce `Q`. Rewrite using `[hi, hk, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hu, Ideal.count_associates_factors_eq hI Q.isPrime Q.ne_bot]`.
-/
private theorem hom_fix_all {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (i : Eˣ →* G) (ψ : G →* Circle)
    (lam : ℕ →* ℂ) (hi : ∀ Q k, w Q (i k) = Q.valuation E (k : E))
    (h1 : ∀ y, (∀ Q, w Q y = 1) → ψ y = 1)
    (h3 : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → w Q z = 1) ∧
      lam (Ideal.absNorm P.asIdeal) = (ψ z : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ))
    (u : 𝓞 E) (k : Eˣ) (hk : (k : E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (ψ (i k) : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  have hu : u ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by simpa using hk)
  have hI : Ideal.span {u} ≠ (0 : Ideal (𝓞 E)) := by
    simpa [Ideal.zero_eq_bot] using hu
  refine lam_absNorm_eq_psi_mul_sqrt w ψ lam h1 h3 (Ideal.span {u}) hI (i k) ?_
  intro Q
  rw [hi, hk, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hu,
    Ideal.count_associates_factors_eq hI Q.isPrime Q.ne_bot]

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t`. Rewrite using `[PositivityTheory.ThKW.LatB.liftF_tmul]`. Simplify using `only [infPartF, fstA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`.

Use `erw [Algebra.TensorProduct.map_tmul]`. Conclude with `TensorProduct.zero_tmul _ _`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
private theorem infPart_lift (w : Af F ⊗[F] E) : infPartF F E (PositivityTheory.ThKW.LatB.liftF F E w) = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    rw [PositivityTheory.ThKW.LatB.liftF_tmul]
    simp only [infPartF, fstA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy => simp [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t`. Rewrite using `[PositivityTheory.ThKW.LatB.liftF_tmul]`. Simplify using `only [finPartF, sndA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`.

Use `erw [Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
private theorem finPart_lift (w : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    rw [PositivityTheory.ThKW.LatB.liftF_tmul]
    simp only [finPartF, sndA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [finPartF, rI, sndA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Use `erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
private theorem finPart_rI : finPartF F E (rI F E) = 0 := by
  simp only [finPartF, rI, sndA, pairA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Take `⟨u0, hu0⟩ : ∃ u0 : (HeightOneSpectrum.adicCompletion E P)ˣ, Valued.v (u0 : HeightOneSpectrum.adicCompletion E P) = WithZero.exp (-1 : ℤ)` from `⟨_, Formalism.L2.Host.unif_spec P⟩`. Use `set a1 := Neutral.B1.finiteSingle E P (u0 : HeightOneSpectrum.adicCompletion E P) with ha1`. Use `set a2 := Neutral.B1.finiteSingle E P ((u0⁻¹ : (HeightOneSpectrum.adicCompletion E P)ˣ) : HeightOneSpectrum.adicCompletion E P) with ha2`. Establish `ha : a1 * a2 = 1`. Rewrite using `[ha1, ha2, ← map_mul, Units.mul_inv, map_one]`.

Use `set b1 := (finAdEquiv F E).symm a1 with hb1`. Use `set b2 := (finAdEquiv F E).symm a2 with hb2`. Establish `hb : b1 * b2 = 1`. Rewrite using `[hb1, hb2, ← map_mul, ha, map_one]`. Establish `key : ∀ c : Af F ⊗[F] E, infPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E c) = 1 ∧ finPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E c) = c` using `fun c => ⟨by rw [map_add, infPart_rI, infPart_lift, add_zero], by rw [map_add, finPart_rI, finPart_lift, zero_add]⟩`.

Establish `h12 : (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1) * (rI F E + PositivityTheory.ThKW.LatB.liftF F E b2) = 1`. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `GlobalTheory.SplitDetCharF.adele_tensor_ext` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, (key b1).1, (key b2).1, map_one, mul_one, sub_self]`. Rewrite using `[map_sub, map_mul, (key b1).2, (key b2).2, hb, map_one, sub_self]`.

Establish `hev : ∀ Q, ev F E Q (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1) = evalV E Q a1`. Introduce `Q`. Use `show evalV E Q (finAdEquiv F E (finPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1))) = _`. Rewrite using `[(key b1).2, hb1, RingEquiv.apply_symm_apply]`. Use `⟨⟨rI F E + PositivityTheory.ThKW.LatB.liftF F E b1, rI F E + PositivityTheory.ThKW.LatB.liftF F E b2, h12, by rw [mul_comm, h12]⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[wv_apply] show Valued.v (ev F E P (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1)) = _`. Rewrite using `[hev, ha1]`. Use `show Valued.v ((RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers E w) P (u0 : HeightOneSpectrum.adicCompletion E P)) P) = _`. Rewrite using `[RestrictedProduct.mulSingle_eq_same]`. Conclude with `hu0`.

Introduce `Q hQ`. Rewrite using `[wv_apply]`. Use `show Valued.v (ev F E Q (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1)) = _`. Rewrite using `[hev, ha1]`. Use `show Valued.v ((RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers E w) P (u0 : HeightOneSpectrum.adicCompletion E P)) Q) = _`.

Rewrite using `[RestrictedProduct.mulSingle_eq_of_ne (h := hQ), map_one]`.
-/
private theorem exists_local (P : HeightOneSpectrum (𝓞 E)) :
    ∃ z : (AEF F E)ˣ, wv F E P z = WithZero.exp (-1 : ℤ) ∧ ∀ Q, Q ≠ P → wv F E Q z = 1 := by
  obtain ⟨u0, hu0⟩ : ∃ u0 : (HeightOneSpectrum.adicCompletion E P)ˣ,
      Valued.v (u0 : HeightOneSpectrum.adicCompletion E P) = WithZero.exp (-1 : ℤ) :=
    ⟨_, Formalism.L2.Host.unif_spec P⟩
  set a1 := Neutral.B1.finiteSingle E P (u0 : HeightOneSpectrum.adicCompletion E P) with ha1
  set a2 := Neutral.B1.finiteSingle E P ((u0⁻¹ : (HeightOneSpectrum.adicCompletion E P)ˣ) :
    HeightOneSpectrum.adicCompletion E P) with ha2
  have ha : a1 * a2 = 1 := by
    rw [ha1, ha2, ← map_mul, Units.mul_inv, map_one]
  set b1 := (finAdEquiv F E).symm a1 with hb1
  set b2 := (finAdEquiv F E).symm a2 with hb2
  have hb : b1 * b2 = 1 := by
    rw [hb1, hb2, ← map_mul, ha, map_one]
  have key : ∀ c : Af F ⊗[F] E, infPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E c) = 1 ∧
      finPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E c) = c := fun c =>
    ⟨by rw [map_add, infPart_rI, infPart_lift, add_zero], by rw [map_add, finPart_rI, finPart_lift, zero_add]⟩
  have h12 : (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1) * (rI F E + PositivityTheory.ThKW.LatB.liftF F E b2) = 1 := by
    apply sub_eq_zero.mp
    apply GlobalTheory.SplitDetCharF.adele_tensor_ext
    · rw [map_sub, map_mul, (key b1).1, (key b2).1, map_one, mul_one, sub_self]
    · rw [map_sub, map_mul, (key b1).2, (key b2).2, hb, map_one, sub_self]
  have hev : ∀ Q, ev F E Q (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1) = evalV E Q a1 := by
    intro Q
    show evalV E Q (finAdEquiv F E (finPartF F E (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1))) = _
    rw [(key b1).2, hb1, RingEquiv.apply_symm_apply]
  refine ⟨⟨rI F E + PositivityTheory.ThKW.LatB.liftF F E b1, rI F E + PositivityTheory.ThKW.LatB.liftF F E b2, h12,
    by rw [mul_comm, h12]⟩, ?_, ?_⟩
  · rw [wv_apply]
    show Valued.v (ev F E P (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1)) = _
    rw [hev, ha1]
    show Valued.v ((RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers E w) P
      (u0 : HeightOneSpectrum.adicCompletion E P)) P) = _
    rw [RestrictedProduct.mulSingle_eq_same]
    exact hu0
  · intro Q hQ
    rw [wv_apply]
    show Valued.v (ev F E Q (rI F E + PositivityTheory.ThKW.LatB.liftF F E b1)) = _
    rw [hev, ha1]
    show Valued.v ((RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers E w) P
      (u0 : HeightOneSpectrum.adicCompletion E P)) Q) = _
    rw [RestrictedProduct.mulSingle_eq_of_ne (h := hQ), map_one]

end Local

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Apply `GlobalTheory.SplitDetCharF.adele_tensor_ext w h0` to reduce the goal to its premises. Apply `(finAdEquiv F E).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `Q`.

Conclude with `hQ Q`.
-/
private theorem eq_zero_of_infPart_zero_of_ev_zero (w : AEF F E) (h0 : infPartF F E w = 0)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), ev F E Q w = 0) : w = 0 := by
  apply GlobalTheory.SplitDetCharF.adele_tensor_ext w h0
  apply (finAdEquiv F E).injective
  rw [map_zero]
  apply RestrictedProduct.ext
  intro Q
  exact hQ Q

/- English proof (translation)
Rewrite using `[ev_fin]`. Break down `hι (HeightOneSpectrum.under (𝓞 F) Q) with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Establish `hf : ¬ Fx σ Q` using `fun hf => not_sq_of_fx hcm hd hθ hθ2 hb hf h2`. Rewrite using `[if_neg hf, h1, map_one]`. Establish `hf : Fx σ Q`.

Assume the negation of the conclusion as `hf`. Conclude with `h2 (sq_of_split hcm hd hθ hθ2 hb (isSplit_of_not_fx hcm hf))`. Rewrite using `[if_pos hf, h1, map_zero]`.
-/
private theorem ev_algebraMap_pairA_eq_ite {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {θ : E} {d : 𝓞 F}
    (hd : (d : F) ≠ 0) (hθ : σ θ = -θ) (hθ2 : θ * θ = algebraMap F E d)
    (hb : ∀ x : E, ∃ u w : F, x = u • 1 + w • θ) {ι : Af F}
    (hι : ∀ v : HeightOneSpectrum (𝓞 F), (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) d)) ∨
      (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) d))) (Q : HeightOneSpectrum (𝓞 E)) :
    ev F E Q (algebraMap (AF F) (AEF F E) (pairA F 0 ι)) = if Fx σ Q then 0 else 1 := by
  rw [ev_fin]
  rcases hι (HeightOneSpectrum.under (𝓞 F) Q) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hf : ¬ Fx σ Q := fun hf => not_sq_of_fx hcm hd hθ hθ2 hb hf h2
    rw [if_neg hf, h1, map_one]
  · have hf : Fx σ Q := by
      by_contra hf
      exact h2 (sq_of_split hcm hd hθ hθ2 hb (isSplit_of_not_fx hcm hf))
    rw [if_pos hf, h1, map_zero]

/- English proof (translation)
Use `set v := HeightOneSpectrum.under (𝓞 F) P with hv`. Establish `hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E` using `E) v := fun hs => not_sq_of_fx hcm hd hθ hθ2 hb hP (sq_of_split hcm hd hθ hθ2 hb hs)`. Establish `hunr : Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) v := by`. Introduce `P' _`. Use `haveI := hun`.

Use `haveI := P'.isPrime`. Conclude with `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. Use `set π := Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) with hπdef`. Establish `hπ : Formalism.L2.Host.IsUnifAt v π` using `Formalism.L2.Host.unif_spec v`. Establish `hπv : Valued.v (π : HeightOneSpectrum.adicCompletion F v) = WithZero.exp (-1)` using `hπ`.

Use `⟨idFF F E (Neutral.B1.localIdele F v π), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[wv_apply] show Valued.v (ev F E P (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π)))) = _`. Rewrite using `[ev_alg]`. Establish `hsn : (sndA F (↑(Neutral.B1.localIdele F v π) : AF F)) v = (π : Fv F v)` using `Neutral.B1.localIdele_snd_self F v π`. Rewrite using `[hsn, valued_complMap _ π.ne_zero, hπv, hunr P rfl, pow_one]`.

Introduce `Q hQ show ev F E Q (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π))) = 1`. Rewrite using `[ev_alg]`. Establish `hne : HeightOneSpectrum.under (𝓞 F) Q ≠ v` using `fun h => hQ (eq_of_not_isSplit hns h rfl)`. Establish `h1 : (sndA F (↑(Neutral.B1.localIdele F v π) : AF F)) (HeightOneSpectrum.under (𝓞 F) Q) = 1` using `by show (RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v (π : HeightOneSpectrum.adicCompletion F v)) (HeightOneSpectrum.under (𝓞 F) Q) = 1`. Rewrite using `[RestrictedProduct.mulSingle_eq_of_ne (h := hne)]`.

Rewrite using `[h1, map_one]`. Use `show infPartF F E (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π))) = 1`. Simplify using `only [infPartF, fstA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Use `erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.

Take `⟨⟨η', hη'⟩, hall⟩` from `h2 haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩`. Rewrite using `[hall η' hη', pow_one, GlobalTheory.EtaSignReal.eq_signToCircle η' hη', MonoidHom.comp_apply, normSign_localIdele]`. Establish `hnm` using `not_mem_normGroup_of_inert hcm.2.2.1 hns hunr hπ`. Simplify using `[GlobalTheory.QuadSymbol.eta, hnm, GlobalTheory.IdeleNormChar.signToCircle]`.
-/
private theorem exists_idele_eta_neg_one_at_place {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {θ : E} {d : 𝓞 F}
    (hd : (d : F) ≠ 0) (hθ : σ θ = -θ) (hθ2 : θ * θ = algebraMap F E d)
    (hb : ∀ x : E, ∃ u w : F, x = u • 1 + w • θ)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {η : (AEF F E)ˣ →* Circle} (h2 : ResEtaF η 1)
    (P : HeightOneSpectrum (𝓞 E)) (hP : Fx σ P) :
    ∃ z : (AEF F E)ˣ, wv F E P z = WithZero.exp (-1) ∧ (∀ Q, Q ≠ P → ev F E Q z = 1) ∧
      infPartF F E z = 1 ∧ η z = -1 := by
  set v := HeightOneSpectrum.under (𝓞 F) P with hv
  have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := fun hs =>
    not_sq_of_fx hcm hd hθ hθ2 hb hP (sq_of_split hcm hd hθ hθ2 hb hs)
  have hunr : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    intro P' _
    haveI := hun
    haveI := P'.isPrime
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  set π := Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) with hπdef
  have hπ : Formalism.L2.Host.IsUnifAt v π := Formalism.L2.Host.unif_spec v
  have hπv : Valued.v (π : HeightOneSpectrum.adicCompletion F v) = WithZero.exp (-1) := hπ
  refine ⟨idFF F E (Neutral.B1.localIdele F v π), ?_, ?_, ?_, ?_⟩
  · rw [wv_apply]
    show Valued.v (ev F E P (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π)))) = _
    rw [ev_alg]
    have hsn : (sndA F (↑(Neutral.B1.localIdele F v π) : AF F)) v = (π : Fv F v) :=
      Neutral.B1.localIdele_snd_self F v π
    rw [hsn, valued_complMap _ π.ne_zero, hπv, hunr P rfl, pow_one]
  · intro Q hQ
    show ev F E Q (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π))) = 1
    rw [ev_alg]
    have hne : HeightOneSpectrum.under (𝓞 F) Q ≠ v := fun h => hQ (eq_of_not_isSplit hns h rfl)
    have h1 : (sndA F (↑(Neutral.B1.localIdele F v π) : AF F)) (HeightOneSpectrum.under (𝓞 F) Q) = 1 := by
      show (RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v
        (π : HeightOneSpectrum.adicCompletion F v)) (HeightOneSpectrum.under (𝓞 F) Q) = 1
      rw [RestrictedProduct.mulSingle_eq_of_ne (h := hne)]
    rw [h1, map_one]
  · show infPartF F E (algebraMap (AF F) (AEF F E) (↑(Neutral.B1.localIdele F v π))) = 1
    simp only [infPartF, fstA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    rfl
  · obtain ⟨⟨η', hη'⟩, hall⟩ := h2
    haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
    rw [hall η' hη', pow_one, GlobalTheory.EtaSignReal.eq_signToCircle η' hη', MonoidHom.comp_apply,
      normSign_localIdele]
    have hnm := not_mem_normGroup_of_inert hcm.2.2.1 hns hunr hπ
    simp [GlobalTheory.QuadSymbol.eta, hnm, GlobalTheory.IdeleNormChar.signToCircle]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨θ, d, ε, ι, hd, hθ, hθ2, hbasis, hidem, horth, hfin, hsum, hι, hsplit⟩` from `exists_half hcm`. Use `⟨ε, ⟨hidem, horth, hfin, hsplit⟩, ?_⟩` and prove the remaining obligations. Introduce `x k hx hk y hy`. Establish `hinv : ∀ a : AEF F E, cAF σ (cAF σ a) = a` using `GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hcm)`. Use `set s := ε + cAF σ ε with hs_def`.

Establish `hss : s * s = s`. Establish `h1 : cAF σ ε * cAF σ ε = cAF σ ε` using `by rw [← map_mul, hidem]`. Establish `h2 : cAF σ ε * ε = 0` using `by rw [mul_comm, horth]`. Take the linear combination `hidem + horth + h1 + h2`. Establish `hrs : rI F E * s = 0` using `by rw [hsum]; exact rI_mul_fin ι`.

Establish `hrr : rI F E * rI F E = rI F E` using `rI_idem`. Establish `hg : (1 - rI F E - s) * (1 - rI F E - s) = 1 - rI F E - s`. Take the linear combination `hrr + hss + 2 * hrs`. Establish `evs : ∀ Q, ev F E Q s = if Fx σ Q then 0 else 1`. Introduce `Q`.

Rewrite using `[hsum]`. Conclude with `ev_algebraMap_pairA_eq_ite hcm hd hθ hθ2 hbasis hι Q`. Establish `infs : infPartF F E s = 0` using `by rw [hsum]; exact infPart_fin ι`. Establish `hev_proj : ∀ (e : AEF F E) (he : e * e = e) (t : (AEF F E)ˣ) Q, ev F E Q ↑(GlobalTheory.InertTrivial.proj e he t) = ev F E Q e * ev F E Q t + (1 - ev F E Q e)`. Introduce `e he t Q`.

Rewrite using `[GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one]`. Establish `hinf_proj : ∀ (e : AEF F E) (he : e * e = e) (t : (AEF F E)ˣ), infPartF F E ↑(GlobalTheory.InertTrivial.proj e he t) = infPartF F E e * infPartF F E t + (1 - infPartF F E e)`. Introduce `e he t`. Rewrite using `[GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one]`. Establish `evg : ∀ Q, ev F E Q (1 - rI F E - s) = if Fx σ Q then 1 else 0`.

Introduce `Q`. Rewrite using `[map_sub, map_sub, map_one, ev_rI, evs]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `infg : infPartF F E (1 - rI F E - s) = 0`. Rewrite using `[map_sub, map_sub, map_one, infPart_rI, infs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsplit_g : ∀ e, IsSplitIdemF σ e → e * (1 - rI F E - s) = 0`. Introduce `e he`. Take `⟨he1, he2, v, εv, ⟨α, hα, -, -⟩, hsum'⟩` from `id he`. Establish `hee : e = e * algebraMap (AF F) (AEF F E) εv`.

Rewrite using `[← hsum', mul_add, he1, he2, add_zero]`. Establish `hinfe : infPartF F E e = 0`. Rewrite using `[hee, map_mul, hα, infPart_fin, mul_zero]`. Establish `her : e * rI F E = 0`. Apply `eq_zero_of_infPart_zero_of_ev_zero` to reduce the goal to its premises.

Rewrite using `[map_mul, hinfe, zero_mul]`. Introduce `Q`. Rewrite using `[map_mul, ev_rI, mul_zero]`. Establish `hes : e * s = e`. Break down `hsplit e he with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases.

Establish `hc : cAF σ ε * e = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs_def, mul_add, mul_comm e ε, h1, mul_comm e (cAF σ ε), hc, add_zero]`. Establish `hc : cAF σ ε * e = e`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hs_def, mul_add, mul_comm e ε, h1, mul_comm e (cAF σ ε), hc, zero_add]`. Take the linear combination `-her - hes`. Set `sgn : (AEF F E)ˣ →* Circle` to `η.comp (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg)`. Establish `hint : ∀ t' : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q t' = 1) → finPartF F E ↑(GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg t') ∈ intAEF F E`. Introduce `t' ht'`.

Rewrite using `[int_iff]`. Introduce `Q`. Rewrite using `[hev_proj, evg]`. Use `split_ifs with hQ`. Simplify using `only [one_mul, sub_self, add_zero]`.

Rewrite using `[← wv_apply, ht' Q hQ]`. Simplify using the standard rewrite rules. Establish `hsgn1 : ∀ t : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q t = 1) → sgn t = 1`. Introduce `t ht`. Use `show η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg t) = 1`.

Apply `h4` to reduce the goal to its premises. Rewrite using `[hinf_proj, infg]`. Expand and normalize the polynomial expressions, which then agree. Introduce `e he`. Rewrite using `[GlobalTheory.InertTrivial.proj_val]`.

Take the linear combination `((t : AEF F E) - 1) * hsplit_g e he`. Conclude with `hint t ht`. Rewrite using `[← map_inv]`. Apply `hint` to reduce the goal to its premises. Introduce `Q hQ`.

Rewrite using `[map_inv, ht Q hQ, inv_one]`. Establish `hpsi : ∀ (u : 𝓞 E) (k' : Eˣ), (k' : E) = u → lam (Ideal.absNorm (Ideal.span {u})) = ((κ * sgn) (Units.map ↑(incAF F E) k') : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ)`. Introduce `u k' hk'`. Use `hom_fix_all (fun Q => wv F E Q) (Units.map ↑(incAF F E)) (κ * sgn) lam (fun Q k => wv_inc Q k) ?_ ?_ u k' hk'` and prove the remaining obligations. Introduce `t ht`.

Rewrite using `[MonoidHom.mul_apply, hκ.ker t (fun Q _ => ht Q), hsgn1 t (fun Q _ => ht Q), one_mul]`. Introduce `P`. Distinguish the cases in `hP : Fx σ P`. Take `⟨z, hzP, hzQ, hzinf, hηz⟩` from `exists_idele_eta_neg_one_at_place hcm hd hθ hθ2 hbasis hun h2 P hP`. Establish `hzQ' : ∀ Q, Q ≠ P → wv F E Q z = 1`.

Introduce `Q hQ`. Rewrite using `[wv_apply, hzQ Q hQ, map_one]`. Use `⟨z, hzP, hzQ', ?_⟩` and prove the remaining obligations. Establish `hκz : κ z = 1` using `hκ.ker z (fun Q hQ => hzQ' Q (fun h => hQ (h ▸ hP)))`. Establish `hpz : GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg z = z`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.InertTrivial.proj_val]`. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `eq_zero_of_infPart_zero_of_ev_zero` to reduce the goal to its premises. Simplify using `only [map_sub, map_add, map_mul, map_one, infPart_rI, infs, hzinf]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `Q`. Simplify using `only [map_sub, map_add, map_mul, map_one, ev_rI, evs]`. Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality.

Rewrite using `[if_pos hP]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `rw [hzQ Q hQP] split_ifs <;> ring`. Establish `hsz : sgn z = -1` using `by show η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg z) = -1`. Rewrite using `[hpz, hηz]`.

Take `⟨-, hgn⟩` from `hlam`. Establish `hmax : P.asIdeal.IsMaximal` using `P.isPrime.isMaximal P.ne_bot`. Establish `hfinq : Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Establish `hcard : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Establish `hl` using `((hgn P.asIdeal hmax hfinq).2 hP).1`. Rewrite using `[hcard, hl, MonoidHom.mul_apply, hκz, hsz, one_mul]`. Simplify using the standard rewrite rules. Take `⟨z, hzP, hzQ⟩` from `exists_local (F := F) P`. Use `⟨z, hzP, hzQ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hκ.gen P hP z hzP hzQ, MonoidHom.mul_apply, hsgn1 z (fun Q hQ => hzQ Q (fun h => hP (h ▸ hQ))), mul_one]`. Take `⟨a, b, hb0, hab⟩` from `IsFractionRing.div_surjective (𝓞 E) x`. Establish `hbE : algebraMap (𝓞 E) E b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0`. Establish `haE : algebraMap (𝓞 E) E a ≠ 0`. Introduce `h`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[← hab, h, zero_div]`. Establish `hb0' : b ≠ 0` using `fun h => hbE (by rw [h, map_zero])`. Establish `haxb : algebraMap (𝓞 E) E a = algebraMap (𝓞 E) E b * x`. Rewrite using `[← hab]`.

Clear the denominators using the available nonvanishing facts. Use `set xu : Eˣ := Units.mk0 x hx with hxu`. Use `set au : Eˣ := Units.mk0 _ haE with hau_def`. Use `set bu : Eˣ := Units.mk0 _ hbE with hbu_def`. Establish `hau : au = bu * xu` using `Units.ext (by simp [au, bu, xu, haxb])`.

Establish `hpa` using `hpsi a au rfl`. Establish `hpb` using `hpsi b bu rfl`. Establish `hNb0 : Ideal.absNorm (Ideal.span {b}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb0'`.

Establish `hN : Ideal.absNorm (Ideal.span {a}) = Ideal.absNorm (Ideal.span {b}) * k`. Establish `hq : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) = (Ideal.absNorm (Ideal.span {b}) : ℚ) * (k : ℚ)`. Rewrite using `[Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, hk, Nat.cast_natAbs, Nat.cast_natAbs]`. Use `push_cast`. Rewrite using `[Algebra.coe_norm_int, Algebra.coe_norm_int, ← abs_mul, ← map_mul]`.

Use `congr 2`. Conclude with `hq` after adjusting the coercions. Establish `hlamk : lam k = ((κ * sgn) (Units.map ↑(incAF F E) xu) : ℂ) * (Real.sqrt k : ℂ)`. Establish `hl0 : lam (Ideal.absNorm (Ideal.span {b})) ≠ 0` using `hlam.1 _ hNb0`. Rewrite `hpa` using `[hN, hau]`.

Simplify using `only [map_mul, Circle.coe_mul, Nat.cast_mul] at hpa`. Rewrite `hpa` using `[Real.sqrt_mul (Nat.cast_nonneg _), hpb]`. Move the coercions through the operations in `at hpa`. Apply `mul_left_cancel₀ hl0` to reduce the goal to its premises. Rewrite using `[hpb]`.

Take the linear combination `hpa`. Use `set xA : (AEF F E)ˣ := Units.map ↑(incAF F E) xu with hxA`. Establish `hyA : y = GlobalTheory.InertTrivial.proj s hss xA`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hy, GlobalTheory.InertTrivial.proj_val]`.

Both sides reduce to the same expression. Establish `h3d` using `GlobalTheory.EtaProduct.proj_three hrr hss hrs hg xA`. Establish `hηx : η xA = 1` using `h1.2 xu`. Establish `hη3 : η y * sgn xA * η (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1`. Rewrite using `[hyA]`.

Use `show η (GlobalTheory.InertTrivial.proj s hss xA) * η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg xA) * η (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1`. Rewrite using `[← map_mul, ← map_mul, ← h3d, hηx]`. Establish `hκg : κ (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg xA) = 1`. Apply `hκ.ker` to reduce the goal to its premises. Introduce `Q hQ`.

Rewrite using `[wv_apply, hev_proj, evg, if_neg hQ]`. Simplify using the standard rewrite rules. Establish `hκr : κ (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1`. Apply `hκ.ker` to reduce the goal to its premises. Introduce `Q _`.

Rewrite using `[wv_apply, hev_proj, ev_rI]`. Simplify using the standard rewrite rules. Establish `hκy : κ y = κ xA`. Rewrite using `[hyA]`. Use `conv_rhs => rw [h3d]`.

Rewrite using `[map_mul, map_mul, hκg, hκr, mul_one, mul_one]`. Establish `hreal` using `eta_real h3 xA`. Establish `hτ : ∀ w, (piInf (B.emb w)) (↑xA : AEF F E) = tauB B w x` using `fun w => piInf_inc (B.emb w) x`. Simplify using `only [hτ] at hreal`. Establish `hτ0 : ∀ w, tauB B w x ≠ 0` using `fun w => (map_ne_zero _).mpr hx`.

Establish `hn0 : ∀ w, (‖tauB B w x‖ : ℂ) ≠ 0` using `fun w => by`. Conclude with `(norm_ne_zero_iff.mpr (hτ0 w))` after adjusting the coercions. Establish `hkpos : 0 < k`. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Rewrite `hk` using `[h0, Nat.cast_zero, eq_comm, abs_eq_zero]`. Conclude with `(Algebra.norm_ne_zero_iff.mpr hx) hk`. Conclude with `h0`. Use `⟨Real.sqrt k * ∏ w, ‖tauB B w x‖, ?_, ?_⟩` and prove the remaining obligations. Apply `mul_pos` to reduce the goal to its premises.

Conclude with `Real.sqrt_pos.mpr (by exact_mod_cast hkpos)`. Conclude with `Finset.prod_pos (fun w _ => norm_pos_iff.mpr (hτ0 w))`. Establish `hT : ∏ w, tauB B w x = (∏ w, (tauB B w x / (‖tauB B w x‖ : ℂ))) * ∏ w, (‖tauB B w x‖ : ℂ)`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun w _ => ?_)` and prove the remaining obligations.

Rewrite using `[div_mul_cancel₀ _ (hn0 w)]`. Establish `hX : (η y : ℂ) * (sgn xA : ℂ) * (∏ w, (tauB B w x / (‖tauB B w x‖ : ℂ))) = 1`. Rewrite using `[← hreal, ← Circle.coe_mul, ← Circle.coe_mul, hη3, Circle.coe_one]`. Establish `hY : (κ y : ℂ) * (κ y : ℂ) = 1`. Rewrite using `[← Circle.coe_mul, hκ.sq y, Circle.coe_one]`.

Rewrite using `[MonoidHom.mul_apply, Circle.coe_mul, hlamk, MonoidHom.mul_apply, Circle.coe_mul, ← hκy, hT]`. Use `push_cast`. Take the linear combination `((Real.sqrt k : ℂ) * (∏ w, (‖tauB B w x‖ : ℂ)) * ((κ y : ℂ) * (κ y : ℂ))) * hX + ((Real.sqrt k : ℂ) * (∏ w, (‖tauB B w x‖ : ℂ))) * hY`.
-/
private theorem eta_prod_all {σ : E →ₐ[F] E} {B : Base F E} (hcm : IsCMExt F E σ)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {η : (AEF F E)ˣ →* Circle}
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (h3 : HasExp B.emb η (fun _ => 1)) (h4 : UnramInert σ η)
    {lam : ℕ →* ℂ} (hlam : GoodNorm (sgOF σ) lam) {κ : (AEF F E)ˣ →* Circle} (hκ : IsKap σ lam κ) :
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ ((η * κ) y : ℂ) * lam k * ∏ v, tauB B v x = r := by
  obtain ⟨θ, d, ε, ι, hd, hθ, hθ2, hbasis, hidem, horth, hfin, hsum, hι, hsplit⟩ := exists_half hcm
  refine ⟨ε, ⟨hidem, horth, hfin, hsplit⟩, ?_⟩
  intro x k hx hk y hy
  have hinv : ∀ a : AEF F E, cAF σ (cAF σ a) = a :=
    GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hcm)
  set s := ε + cAF σ ε with hs_def
  have hss : s * s = s := by
    have h1 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hidem]
    have h2 : cAF σ ε * ε = 0 := by rw [mul_comm, horth]
    linear_combination hidem + horth + h1 + h2
  have hrs : rI F E * s = 0 := by rw [hsum]; exact rI_mul_fin ι
  have hrr : rI F E * rI F E = rI F E := rI_idem
  have hg : (1 - rI F E - s) * (1 - rI F E - s) = 1 - rI F E - s := by
    linear_combination hrr + hss + 2 * hrs
  have evs : ∀ Q, ev F E Q s = if Fx σ Q then 0 else 1 := by
    intro Q
    rw [hsum]
    exact ev_algebraMap_pairA_eq_ite hcm hd hθ hθ2 hbasis hι Q
  have infs : infPartF F E s = 0 := by rw [hsum]; exact infPart_fin ι
  have hev_proj : ∀ (e : AEF F E) (he : e * e = e) (t : (AEF F E)ˣ) Q,
      ev F E Q ↑(GlobalTheory.InertTrivial.proj e he t) = ev F E Q e * ev F E Q t + (1 - ev F E Q e) := by
    intro e he t Q
    rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one]
  have hinf_proj : ∀ (e : AEF F E) (he : e * e = e) (t : (AEF F E)ˣ),
      infPartF F E ↑(GlobalTheory.InertTrivial.proj e he t) = infPartF F E e * infPartF F E t + (1 - infPartF F E e) := by
    intro e he t
    rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one]
  have evg : ∀ Q, ev F E Q (1 - rI F E - s) = if Fx σ Q then 1 else 0 := by
    intro Q
    rw [map_sub, map_sub, map_one, ev_rI, evs]
    split_ifs <;> ring
  have infg : infPartF F E (1 - rI F E - s) = 0 := by
    rw [map_sub, map_sub, map_one, infPart_rI, infs]
    ring
  have hsplit_g : ∀ e, IsSplitIdemF σ e → e * (1 - rI F E - s) = 0 := by
    intro e he
    obtain ⟨he1, he2, v, εv, ⟨α, hα, -, -⟩, hsum'⟩ := id he
    have hee : e = e * algebraMap (AF F) (AEF F E) εv := by
      rw [← hsum', mul_add, he1, he2, add_zero]
    have hinfe : infPartF F E e = 0 := by
      rw [hee, map_mul, hα, infPart_fin, mul_zero]
    have her : e * rI F E = 0 := by
      apply eq_zero_of_infPart_zero_of_ev_zero
      · rw [map_mul, hinfe, zero_mul]
      · intro Q
        rw [map_mul, ev_rI, mul_zero]
    have hes : e * s = e := by
      rcases hsplit e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc : cAF σ ε * e = 0 := by
          calc cAF σ ε * e = cAF σ (ε * cAF σ e) := by rw [map_mul, hinv]
            _ = 0 := by rw [h2, map_zero]
        rw [hs_def, mul_add, mul_comm e ε, h1, mul_comm e (cAF σ ε), hc, add_zero]
      · have hc : cAF σ ε * e = e := by
          calc cAF σ ε * e = cAF σ (ε * cAF σ e) := by rw [map_mul, hinv]
            _ = e := by rw [h2, hinv]
        rw [hs_def, mul_add, mul_comm e ε, h1, mul_comm e (cAF σ ε), hc, zero_add]
    linear_combination -her - hes
  let sgn : (AEF F E)ˣ →* Circle := η.comp (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg)
  have hint : ∀ t' : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q t' = 1) →
      finPartF F E ↑(GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg t') ∈ intAEF F E := by
    intro t' ht'
    rw [int_iff]
    intro Q
    rw [hev_proj, evg]
    split_ifs with hQ
    · simp only [one_mul, sub_self, add_zero]
      rw [← wv_apply, ht' Q hQ]
    · simp
  have hsgn1 : ∀ t : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q t = 1) → sgn t = 1 := by
    intro t ht
    show η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg t) = 1
    apply h4
    · rw [hinf_proj, infg]
      ring
    · intro e he
      rw [GlobalTheory.InertTrivial.proj_val]
      linear_combination ((t : AEF F E) - 1) * hsplit_g e he
    · exact hint t ht
    · rw [← map_inv]
      apply hint
      intro Q hQ
      rw [map_inv, ht Q hQ, inv_one]
  have hpsi : ∀ (u : 𝓞 E) (k' : Eˣ), (k' : E) = u → lam (Ideal.absNorm (Ideal.span {u})) =
      ((κ * sgn) (Units.map ↑(incAF F E) k') : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
    intro u k' hk'
    refine hom_fix_all (fun Q => wv F E Q) (Units.map ↑(incAF F E)) (κ * sgn) lam
      (fun Q k => wv_inc Q k) ?_ ?_ u k' hk'
    · intro t ht
      rw [MonoidHom.mul_apply, hκ.ker t (fun Q _ => ht Q), hsgn1 t (fun Q _ => ht Q), one_mul]
    · intro P
      by_cases hP : Fx σ P
      · obtain ⟨z, hzP, hzQ, hzinf, hηz⟩ := exists_idele_eta_neg_one_at_place hcm hd hθ hθ2 hbasis hun h2 P hP
        have hzQ' : ∀ Q, Q ≠ P → wv F E Q z = 1 := by
          intro Q hQ
          rw [wv_apply, hzQ Q hQ, map_one]
        refine ⟨z, hzP, hzQ', ?_⟩
        have hκz : κ z = 1 := hκ.ker z (fun Q hQ => hzQ' Q (fun h => hQ (h ▸ hP)))
        have hpz : GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg z = z := by
          apply Units.ext
          rw [GlobalTheory.InertTrivial.proj_val]
          apply sub_eq_zero.mp
          apply eq_zero_of_infPart_zero_of_ev_zero
          · simp only [map_sub, map_add, map_mul, map_one, infPart_rI, infs, hzinf]
            ring
          · intro Q
            simp only [map_sub, map_add, map_mul, map_one, ev_rI, evs]
            by_cases hQP : Q = P
            · subst hQP
              rw [if_pos hP]
              ring
            · rw [hzQ Q hQP]
              split_ifs <;> ring
        have hsz : sgn z = -1 := by
          show η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg z) = -1
          rw [hpz, hηz]
        obtain ⟨-, hgn⟩ := hlam
        have hmax : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
        have hfinq : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
        have hcard : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal) := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        have hl := ((hgn P.asIdeal hmax hfinq).2 hP).1
        rw [hcard, hl, MonoidHom.mul_apply, hκz, hsz, one_mul]
        simp
      · obtain ⟨z, hzP, hzQ⟩ := exists_local (F := F) P
        refine ⟨z, hzP, hzQ, ?_⟩
        rw [hκ.gen P hP z hzP hzQ, MonoidHom.mul_apply,
          hsgn1 z (fun Q hQ => hzQ Q (fun h => hP (h ▸ hQ))), mul_one]
  obtain ⟨a, b, hb0, hab⟩ := IsFractionRing.div_surjective (𝓞 E) x
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
  have haE : algebraMap (𝓞 E) E a ≠ 0 := by
    intro h
    apply hx
    rw [← hab, h, zero_div]
  have hb0' : b ≠ 0 := fun h => hbE (by rw [h, map_zero])
  have haxb : algebraMap (𝓞 E) E a = algebraMap (𝓞 E) E b * x := by
    rw [← hab]
    field_simp
  set xu : Eˣ := Units.mk0 x hx with hxu
  set au : Eˣ := Units.mk0 _ haE with hau_def
  set bu : Eˣ := Units.mk0 _ hbE with hbu_def
  have hau : au = bu * xu := Units.ext (by simp [au, bu, xu, haxb])
  have hpa := hpsi a au rfl
  have hpb := hpsi b bu rfl
  have hNb0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0'
  have hN : Ideal.absNorm (Ideal.span {a}) = Ideal.absNorm (Ideal.span {b}) * k := by
    have hq : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) =
        (Ideal.absNorm (Ideal.span {b}) : ℚ) * (k : ℚ) := by
      rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, hk, Nat.cast_natAbs, Nat.cast_natAbs]
      push_cast
      rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← abs_mul, ← map_mul]
      congr 2
    exact_mod_cast hq
  have hlamk : lam k = ((κ * sgn) (Units.map ↑(incAF F E) xu) : ℂ) * (Real.sqrt k : ℂ) := by
    have hl0 : lam (Ideal.absNorm (Ideal.span {b})) ≠ 0 := hlam.1 _ hNb0
    rw [hN, hau] at hpa
    simp only [map_mul, Circle.coe_mul, Nat.cast_mul] at hpa
    rw [Real.sqrt_mul (Nat.cast_nonneg _), hpb] at hpa
    push_cast at hpa
    apply mul_left_cancel₀ hl0
    rw [hpb]
    linear_combination hpa
  set xA : (AEF F E)ˣ := Units.map ↑(incAF F E) xu with hxA
  have hyA : y = GlobalTheory.InertTrivial.proj s hss xA := by
    apply Units.ext
    rw [hy, GlobalTheory.InertTrivial.proj_val]
    rfl
  have h3d := GlobalTheory.EtaProduct.proj_three hrr hss hrs hg xA
  have hηx : η xA = 1 := h1.2 xu
  have hη3 : η y * sgn xA * η (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1 := by
    rw [hyA]
    show η (GlobalTheory.InertTrivial.proj s hss xA) * η (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg xA) *
      η (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1
    rw [← map_mul, ← map_mul, ← h3d, hηx]
  have hκg : κ (GlobalTheory.InertTrivial.proj (1 - rI F E - s) hg xA) = 1 := by
    apply hκ.ker
    intro Q hQ
    rw [wv_apply, hev_proj, evg, if_neg hQ]
    simp
  have hκr : κ (GlobalTheory.InertTrivial.proj (rI F E) hrr xA) = 1 := by
    apply hκ.ker
    intro Q _
    rw [wv_apply, hev_proj, ev_rI]
    simp
  have hκy : κ y = κ xA := by
    rw [hyA]
    conv_rhs => rw [h3d]
    rw [map_mul, map_mul, hκg, hκr, mul_one, mul_one]
  have hreal := eta_real h3 xA
  have hτ : ∀ w, (piInf (B.emb w)) (↑xA : AEF F E) = tauB B w x := fun w => piInf_inc (B.emb w) x
  simp only [hτ] at hreal
  have hτ0 : ∀ w, tauB B w x ≠ 0 := fun w => (map_ne_zero _).mpr hx
  have hn0 : ∀ w, (‖tauB B w x‖ : ℂ) ≠ 0 := fun w => by
    exact_mod_cast (norm_ne_zero_iff.mpr (hτ0 w))
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at hk
      exact (Algebra.norm_ne_zero_iff.mpr hx) hk
    · exact h0
  refine ⟨Real.sqrt k * ∏ w, ‖tauB B w x‖, ?_, ?_⟩
  · apply mul_pos
    · exact Real.sqrt_pos.mpr (by exact_mod_cast hkpos)
    · exact Finset.prod_pos (fun w _ => norm_pos_iff.mpr (hτ0 w))
  · have hT : ∏ w, tauB B w x = (∏ w, (tauB B w x / (‖tauB B w x‖ : ℂ))) * ∏ w, (‖tauB B w x‖ : ℂ) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun w _ => ?_)
      rw [div_mul_cancel₀ _ (hn0 w)]
    have hX : (η y : ℂ) * (sgn xA : ℂ) * (∏ w, (tauB B w x / (‖tauB B w x‖ : ℂ))) = 1 := by
      rw [← hreal, ← Circle.coe_mul, ← Circle.coe_mul, hη3, Circle.coe_one]
    have hY : (κ y : ℂ) * (κ y : ℂ) = 1 := by
      rw [← Circle.coe_mul, hκ.sq y, Circle.coe_one]
    rw [MonoidHom.mul_apply, Circle.coe_mul, hlamk, MonoidHom.mul_apply, Circle.coe_mul, ← hκy, hT]
    push_cast
    linear_combination ((Real.sqrt k : ℂ) * (∏ w, (‖tauB B w x‖ : ℂ)) * ((κ y : ℂ) * (κ y : ℂ))) * hX +
      ((Real.sqrt k : ℂ) * (∏ w, (‖tauB B w x‖ : ℂ))) * hY

end Main

end UpperTheory.TP.W

open UpperTheory.TP.W in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hcm hun η h1 h2 h3 h4 lam hlam κ hκ`. Conclude with `eta_prod_all hcm hun h1 h2 h3 h4 hlam hκ`.
-/
theorem UpperTheory.TP.W.etaProdK :
    EtaProdK := by
  intro F E _ _ _ _ _ σ B hcm hun η h1 h2 h3 h4 lam hlam κ hκ
  exact eta_prod_all hcm hun h1 h2 h3 h4 hlam hκ

end
