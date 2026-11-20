import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ev

variable (F E) in

def ev (Q : HeightOneSpectrum (𝓞 E)) : AEF F E →+* Q.adicCompletion E :=
  ((evalV E Q).toRingHom.comp (GlobalTheory.LFun.finAdEquiv F E).toRingHom).comp (finPartF F E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_tmul (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : E) :
    ev F E Q (a ⊗ₜ[F] x) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) * algebraMap E _ x := rfl

/- English proof (translation)
Establish `: incAF F E x = (1 : AF F) ⊗ₜ[F] x` using `rfl`. Rewrite using `[this, ev_tmul, map_one]`. Use `erw [map_one, one_mul]`.
-/
theorem ev_inc (Q : HeightOneSpectrum (𝓞 E)) (x : E) : ev F E Q (incAF F E x) = algebraMap E _ x := by
  have : incAF F E x = (1 : AF F) ⊗ₜ[F] x := rfl
  rw [this, ev_tmul, map_one]
  erw [map_one, one_mul]

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, ev_tmul, map_one, mul_one]`.
-/
theorem ev_alg (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) :
    ev F E Q (algebraMap (AF F) (AEF F E) a) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, ev_tmul, map_one, mul_one]

variable (F E) in

def wv (Q : HeightOneSpectrum (𝓞 E)) : (AEF F E)ˣ →* WithZero (Multiplicative ℤ) :=
  ((Valued.v (R := Q.adicCompletion E)).toMonoidWithZeroHom.toMonoidHom.comp (ev F E Q).toMonoidHom).comp
    (Units.coeHom _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wv_apply (Q : HeightOneSpectrum (𝓞 E)) (y : (AEF F E)ˣ) : wv F E Q y = Valued.v (ev F E Q y) := rfl

/- English proof (translation)
Rewrite using `[wv_apply]`. Express the relevant statement in the definitionally equal form `Valued.v (ev F E Q (incAF F E (k : E))) = _`. Rewrite using `[ev_inc]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : E)`.
-/
theorem wv_inc (Q : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    wv F E Q (Units.map (incAF F E).toMonoidHom k) = Q.valuation E (k : E) := by
  rw [wv_apply]
  change Valued.v (ev F E Q (incAF F E (k : E))) = _
  rw [ev_inc]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : E)

/- English proof (translation)
The claim follows from `GlobalTheory.LFun.mem_int_iff (finPartF F E y)`.
-/
theorem int_iff (y : AEF F E) : finPartF F E y ∈ intAEF F E ↔ ∀ Q, Valued.v (ev F E Q y) ≤ 1 :=
  GlobalTheory.LFun.mem_int_iff (finPartF F E y)

end Ev

section Fix

variable {σ : E →ₐ[F] E}

variable (σ) in

def Fx (Q : HeightOneSpectrum (𝓞 E)) : Prop := ∀ r ∈ Q.asIdeal, sgOF σ r ∈ Q.asIdeal

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (GlobalTheory.SplitDetCharF.sig_invol h (x : E))`.
-/
theorem sgOF_sgOF (h : IsCMExt F E σ) (x : 𝓞 E) : sgOF σ (sgOF σ x) = x :=
  RingOfIntegers.ext (GlobalTheory.SplitDetCharF.sig_invol h (x : E))

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (σ.commutes (a : F))`.
-/
theorem sgOF_alg (a : 𝓞 F) : sgOF σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a :=
  RingOfIntegers.ext (σ.commutes (a : F))

/- English proof (translation)
Establish `hne : Q.asIdeal.comap (sgOF σ) ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot`. Introduce `hb`. Establish `: sgOF σ x ∈ Q.asIdeal.comap (sgOF σ)` using `by show sgOF σ (sgOF σ x) ∈ Q.asIdeal`. Rewrite using `[sgOF_sgOF h]`.

Conclude with `hx`. Rewrite `this` using `[hb, Ideal.mem_bot]`. Conclude with `hx0 (by rw [← sgOF_sgOF h x, this, map_zero])`. Set `Q' : HeightOneSpectrum (𝓞 E)` to `⟨Q.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, hne⟩`. Use `GlobalTheory.LFun.isSplit_iff.2 ⟨Q', Q, fun e => hQ fun r hr => ?_, ?_, rfl⟩` and prove the remaining obligations.

Establish `: r ∈ Q'.asIdeal` using `by rw [e]; exact hr`. Conclude with `this`. Use `HeightOneSpectrum.ext ?_ show (Q.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))` and prove the remaining obligations. Rewrite using `[Ideal.comap_comap]`. Use `congr 1`.

Conclude with `RingHom.ext sgOF_alg`.
-/
theorem isSplit_of_not_fx (h : IsCMExt F E σ) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Fx σ Q) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (Q.under (𝓞 F)) := by
  have hne : Q.asIdeal.comap (sgOF σ) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    intro hb
    have : sgOF σ x ∈ Q.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ Q.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])
  let Q' : HeightOneSpectrum (𝓞 E) := ⟨Q.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, hne⟩
  refine GlobalTheory.LFun.isSplit_iff.2 ⟨Q', Q, fun e => hQ fun r hr => ?_, ?_, rfl⟩
  · have : r ∈ Q'.asIdeal := by rw [e]; exact hr
    exact this
  · refine HeightOneSpectrum.ext ?_
    show (Q.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext sgOF_alg

/- English proof (translation)
Establish `hθ0 : θ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hθθ` using `[zero_mul, eq_comm, map_eq_zero]`. Conclude with `hd0 hθθ`. Use `⟨fun ⟨r, hr⟩ => ?_, by rw [pow_two, hθθ], hσθ, fun x => ?_⟩` and prove the remaining obligations.

Establish `h1 : θ * θ = algebraMap F E r * algebraMap F E r` using `by rw [hθθ, hr, map_mul]`. Break down `mul_self_eq_mul_self_iff.1 h1 with h2 | h2` into its components or cases. Use `hσθ` as an intermediate fact. Rewrite `this` using `[h2, AlgHom.commutes]`. Establish `h4 : (2 : E) * algebraMap F E r = 0` using `by linear_combination this`.

Break down `mul_eq_zero.1 h4 with h3 | h3` into its components or cases. Conclude with `two_ne_zero h3`. Conclude with `hθ0 (h2.trans h3)`. Use `hσθ` as an intermediate fact. Rewrite `this` using `[h2, map_neg, AlgHom.commutes, neg_neg]`.

Establish `h4 : (2 : E) * algebraMap F E r = 0` using `by linear_combination -this`. Break down `mul_eq_zero.1 h4 with h3 | h3` into its components or cases. Conclude with `two_ne_zero h3`. Conclude with `hθ0 (by rw [h2, h3, neg_zero])`. Take `⟨u, w, e⟩` from `hdec x`.

Conclude with `⟨u, w, by rw [e, Algebra.smul_def, Algebra.smul_def, mul_one]⟩`.
-/
theorem isQuad (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) :
    GlobalTheory.QNorm.IsQuad (d : F) θ
      (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))) := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, map_eq_zero] at hθθ
    exact hd0 hθθ
  refine ⟨fun ⟨r, hr⟩ => ?_, by rw [pow_two, hθθ], hσθ, fun x => ?_⟩
  · have h1 : θ * θ = algebraMap F E r * algebraMap F E r := by rw [hθθ, hr, map_mul]
    rcases mul_self_eq_mul_self_iff.1 h1 with h2 | h2
    · have := hσθ
      rw [h2, AlgHom.commutes] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (h2.trans h3)
    · have := hσθ
      rw [h2, map_neg, AlgHom.commutes, neg_neg] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination -this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (by rw [h2, h3, neg_zero])
  · obtain ⟨u, w, e⟩ := hdec x
    exact ⟨u, w, by rw [e, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

/- English proof (translation)
Set `σe : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))`. Set `s : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv (σe : E ≃+* E)`. Establish `hs : ∀ x, ((s x : 𝓞 E) : E) = σe x` using `fun _ => rfl`. Establish `hsg : ∀ x, s x = sgOF σ x` using `fun _ => rfl`. Use `GlobalTheory.FixedPrimeNorm.not_isSquare_of_fixed (isQuad h hd0 hσθ hθθ hdec) s hs Q (le_antisymm ?_ ?_)` and prove the remaining obligations.

Use `Ideal.map_le_iff_le_comap.2 fun r hr => ?_ show s r ∈ Q.asIdeal` and prove the remaining obligations. Rewrite using `[hsg]`. Conclude with `hQ r hr`. Introduce `x hx`. Establish `: x = s (sgOF σ x)` using `by rw [hsg, sgOF_sgOF h]`.

Rewrite using `[this]`. Conclude with `Ideal.mem_map_of_mem _ (hQ x hx)`.
-/
theorem not_sq_of_fx (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Fx σ Q) : ¬ IsSquare (algebraMap F (Fv F (Q.under (𝓞 F))) (d : F)) := by
  let σe : E ≃ₐ[F] E :=
    AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (σe : E ≃+* E)
  have hs : ∀ x, ((s x : 𝓞 E) : E) = σe x := fun _ => rfl
  have hsg : ∀ x, s x = sgOF σ x := fun _ => rfl
  refine GlobalTheory.FixedPrimeNorm.not_isSquare_of_fixed (isQuad h hd0 hσθ hθθ hdec) s hs Q (le_antisymm ?_ ?_)
  · refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    show s r ∈ Q.asIdeal
    rw [hsg]; exact hQ r hr
  · intro x hx
    have : x = s (sgOF σ x) := by rw [hsg, sgOF_sgOF h]
    rw [this]
    exact Ideal.mem_map_of_mem _ (hQ x hx)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SquareOfApproximation.main h hd0 hσθ hθθ hdec hv`.
-/
theorem sq_of_split (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) (d : F)) :=
  _root_.UpperTheory.Reformulated.B.SquareOfApproximation.main h hd0 hσθ hθθ hdec hv

end Fix

end PositivityTheory.ThKW.AutEtaA

end
