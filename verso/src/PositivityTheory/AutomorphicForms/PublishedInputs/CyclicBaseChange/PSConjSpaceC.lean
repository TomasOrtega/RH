import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.CBC.SConjSpaceCAux

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open Classical in

def cc (τ : E →+* ℂ) : Cinf E →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))

/- English proof (translation)
Unfold `cc`. Rewrite using `[if_pos h]`. Both sides reduce to the same expression.
-/
theorem cc_of_eq {τ : E →+* ℂ} (h : (InfinitePlace.mk τ).embedding = τ) (x : Cinf E) :
    cc τ x = x (InfinitePlace.mk τ) := by
  classical
  unfold cc; rw [if_pos h]; rfl

/- English proof (translation)
Unfold `cc`. Rewrite using `[if_neg h]`. Both sides reduce to the same expression.
-/
theorem cc_of_ne {τ : E →+* ℂ} (h : ¬ (InfinitePlace.mk τ).embedding = τ) (x : Cinf E) :
    cc τ x = starRingEnd ℂ (x (InfinitePlace.mk τ)) := by
  classical
  unfold cc; rw [if_neg h]; rfl

/- English proof (translation)
Establish `h : (InfinitePlace.mk w.embedding).embedding = w.embedding` using `by rw [InfinitePlace.mk_embedding]`. Rewrite using `[cc_of_eq h, InfinitePlace.mk_embedding]`.
-/
theorem cc_embedding (w : InfinitePlace E) (x : Cinf E) : cc w.embedding x = x w := by
  have h : (InfinitePlace.mk w.embedding).embedding = w.embedding := by rw [InfinitePlace.mk_embedding]
  rw [cc_of_eq h, InfinitePlace.mk_embedding]

/- English proof (translation)
The claim follows from `funext fun w => (cc_embedding w x).symm.trans ((h _).trans (cc_embedding w y))`.
-/
theorem cc_ext {x y : Cinf E} (h : ∀ τ, cc τ x = cc τ y) : x = y :=
  funext fun w => (cc_embedding w x).symm.trans ((h _).trans (cc_embedding w y))

/- English proof (translation)
Introduce `h` and use `(InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk τ))) (InfinitePlace.isReal_iff.2 (by rcases InfinitePlace.embedding_mk_eq τ with e | e <;> rw [e] <;> [exact ComplexEmbedding.isReal_iff.2 h; exact ComplexEmbedding.isReal_iff.2 (by rw [h]; …`.
-/
theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_iff.2 (by
      rcases InfinitePlace.embedding_mk_eq τ with e | e <;> rw [e] <;>
        [exact ComplexEmbedding.isReal_iff.2 h; exact ComplexEmbedding.isReal_iff.2 (by rw [h]; exact h)]))

/- English proof (translation)
Establish `hm` using `InfinitePlace.mk_conjugate_eq τ`. Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Establish `h' : ¬ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ`. Rewrite using `[hm, h]`. Conclude with `(conj_ne τ).symm`.

Rewrite using `[cc_of_ne h', cc_of_eq h, hm]`. Establish `h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ` using `(InfinitePlace.embedding_mk_eq τ).resolve_left h`. Establish `h' : (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ`. Rewrite using `[hm, h2]`. Rewrite using `[cc_of_eq h', cc_of_ne h, hm, starRingEnd_self_apply]`.
-/
theorem cc_conj (τ : E →+* ℂ) (x : Cinf E) :
    cc (ComplexEmbedding.conjugate τ) x = starRingEnd ℂ (cc τ x) := by
  have hm := InfinitePlace.mk_conjugate_eq τ
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · have h' : ¬ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ := by
      rw [hm, h]; exact (conj_ne τ).symm
    rw [cc_of_ne h', cc_of_eq h, hm]
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left h
    have h' : (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ := by
      rw [hm, h2]
    rw [cc_of_eq h', cc_of_ne h, hm, starRingEnd_self_apply]

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[cc_of_eq h, cc_of_eq h]`. Both sides reduce to the same expression. Rewrite using `[cc_of_ne h, cc_of_ne h]`. Both sides reduce to the same expression.
-/
theorem cc_star (τ : E →+* ℂ) (x : Cinf E) : cc τ (star x) = starRingEnd ℂ (cc τ x) := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, cc_of_eq h]; rfl
  · rw [cc_of_ne h, cc_of_ne h]; rfl

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[cc_of_eq h, cc_of_eq h]`. Both sides reduce to the same expression. Rewrite using `[cc_of_ne h, cc_of_ne h]`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (r • x (InfinitePlace.mk τ)) = _`.

Rewrite using `[Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]`.
-/
theorem cc_smul (τ : E →+* ℂ) (r : ℝ) (x : Cinf E) : cc τ (r • x) = r • cc τ x := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, cc_of_eq h]; rfl
  · rw [cc_of_ne h, cc_of_ne h]
    change starRingEnd ℂ (r • x (InfinitePlace.mk τ)) = _
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Establish `e : (cc τ : Cinf E → ℂ) = fun x => x (InfinitePlace.mk τ)` using `funext (cc_of_eq h)`. Rewrite using `[e]`. Conclude with `continuous_apply _`. Establish `e : (cc τ : Cinf E → ℂ) = fun x => starRingEnd ℂ (x (InfinitePlace.mk τ))` using `funext (cc_of_ne h)`.

Rewrite using `[e]`. Conclude with `Complex.continuous_conj.comp (continuous_apply _)`.
-/
theorem continuous_cc (τ : E →+* ℂ) : Continuous (cc τ) := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · have e : (cc τ : Cinf E → ℂ) = fun x => x (InfinitePlace.mk τ) := funext (cc_of_eq h)
    rw [e]; exact continuous_apply _
  · have e : (cc τ : Cinf E → ℂ) = fun x => starRingEnd ℂ (x (InfinitePlace.mk τ)) := funext (cc_of_ne h)
    rw [e]; exact Complex.continuous_conj.comp (continuous_apply _)

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[cc_of_eq h, pInf_algebraMap, h]`. Establish `h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ` using `(InfinitePlace.embedding_mk_eq τ).resolve_left h`. Rewrite using `[cc_of_ne h, pInf_algebraMap, h2, ComplexEmbedding.conjugate_coe_eq, starRingEnd_self_apply]`.
-/
theorem cc_pInf_alg (τ : E →+* ℂ) (m : E) : cc τ (pInf E (algebraMap E (Ad E) m)) = τ m := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, pInf_algebraMap, h]
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left h
    rw [cc_of_ne h, pInf_algebraMap, h2, ComplexEmbedding.conjugate_coe_eq, starRingEnd_self_apply]

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[cc_of_eq h, hx]`. Rewrite using `[cc_of_ne h, hx, map_zero]`.
-/
theorem cc_eq_zero {τ : E →+* ℂ} {x : Cinf E} (hx : x (InfinitePlace.mk τ) = 0) : cc τ x = 0 := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, hx]
  · rw [cc_of_ne h, hx, map_zero]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `e : atEmb τ z = Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)` using `rfl`. Rewrite using `[e]`. Distinguish the cases in `hw : w = InfinitePlace.mk τ`. Substitute `hw` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[if_pos h, ← h1, cc_of_eq h]`. Rewrite using `[if_neg h, ← h1, cc_of_ne h, starRingEnd_self_apply]`. Rewrite using `[Pi.single_eq_of_ne hw, h0 w hw]`.
-/
theorem eq_atEmb {τ : E →+* ℂ} {z : ℂ} {x : Cinf E} (h0 : ∀ w, w ≠ InfinitePlace.mk τ → x w = 0)
    (h1 : cc τ x = z) : x = atEmb τ z := by
  classical
  funext w
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  rw [e]
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    rw [Pi.single_eq_same]
    by_cases h : (InfinitePlace.mk τ).embedding = τ
    · rw [if_pos h, ← h1, cc_of_eq h]
    · rw [if_neg h, ← h1, cc_of_ne h, starRingEnd_self_apply]
  · rw [Pi.single_eq_of_ne hw, h0 w hw]

/- English proof (translation)
Establish `e : atEmb τ z = Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)` using `rfl`. Rewrite using `[e, Pi.single_eq_of_ne hw]`.
-/
theorem atEmb_apply_ne {τ : E →+* ℂ} (z : ℂ) {w : InfinitePlace E} (hw : w ≠ InfinitePlace.mk τ) :
    atEmb τ z w = 0 := by
  classical
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  rw [e, Pi.single_eq_of_ne hw]

/- English proof (translation)
Establish `e : atEmb τ z = Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)` using `rfl`. Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[cc_of_eq h, e, Pi.single_eq_same, if_pos h]`. Rewrite using `[cc_of_ne h, e, Pi.single_eq_same, if_neg h, starRingEnd_self_apply]`.
-/
theorem cc_atEmb (τ : E →+* ℂ) (z : ℂ) : cc τ (atEmb τ z) = z := by
  classical
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, e, Pi.single_eq_same, if_pos h]
  · rw [cc_of_ne h, e, Pi.single_eq_same, if_neg h, starRingEnd_self_apply]

def Lx (σ : E ≃+* E) : Cinf E →+* Cinf E := RingHom.pi fun w => cc (w.embedding.comp (σ : E →+* E))

/- English proof (translation)
Distinguish the cases in `h : (InfinitePlace.mk ρ).embedding = ρ`. Rewrite using `[cc_of_eq h]`. Express the relevant statement in the definitionally equal form `cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x = _`. Rewrite using `[h]`. Establish `h2 : (InfinitePlace.mk ρ).embedding = ComplexEmbedding.conjugate ρ` using `(InfinitePlace.embedding_mk_eq ρ).resolve_left h`.

Rewrite using `[cc_of_ne h]`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x) = _`. Establish `e : (ComplexEmbedding.conjugate ρ).comp (σ : E →+* E) = ComplexEmbedding.conjugate (ρ.comp (σ : E →+* E))` using `RingHom.ext fun _ => rfl`. Rewrite using `[h2, e, cc_conj, starRingEnd_self_apply]`.
-/
theorem cc_Lx (σ : E ≃+* E) (ρ : E →+* ℂ) (x : Cinf E) : cc ρ (Lx σ x) = cc (ρ.comp (σ : E →+* E)) x := by
  by_cases h : (InfinitePlace.mk ρ).embedding = ρ
  · rw [cc_of_eq h]
    change cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x = _
    rw [h]
  · have h2 : (InfinitePlace.mk ρ).embedding = ComplexEmbedding.conjugate ρ :=
      (InfinitePlace.embedding_mk_eq ρ).resolve_left h
    rw [cc_of_ne h]
    change starRingEnd ℂ (cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x) = _
    have e : (ComplexEmbedding.conjugate ρ).comp (σ : E →+* E) = ComplexEmbedding.conjugate (ρ.comp (σ : E →+* E)) :=
      RingHom.ext fun _ => rfl
    rw [h2, e, cc_conj, starRingEnd_self_apply]

/- English proof (translation)
The claim follows from `cc_ext fun ρ => by have e : (ρ.comp (σ : E →+* E)).comp (σ.symm : E →+* E) = ρ := RingHom.ext fun y => by change ρ (σ (σ.symm y)) = ρ y rw [RingEquiv.apply_symm_apply] rw [cc_Lx, cc_Lx, e]`.
-/
theorem Lx_symm (σ : E ≃+* E) (x : Cinf E) : Lx σ (Lx σ.symm x) = x :=
  cc_ext fun ρ => by
    have e : (ρ.comp (σ : E →+* E)).comp (σ.symm : E →+* E) = ρ := RingHom.ext fun y => by
      change ρ (σ (σ.symm y)) = ρ y
      rw [RingEquiv.apply_symm_apply]
    rw [cc_Lx, cc_Lx, e]

/- English proof (translation)
Simplify using `using Lx_symm σ.symm x`.
-/
theorem Lx_symm' (σ : E ≃+* E) (x : Cinf E) : Lx σ.symm (Lx σ x) = x := by
  simpa using Lx_symm σ.symm x

def LE (σ : E ≃+* E) : Cinf E ≃+* Cinf E where
  toFun := Lx σ
  invFun := Lx σ.symm
  left_inv := Lx_symm' σ
  right_inv := Lx_symm σ
  map_mul' := map_mul _
  map_add' := map_add _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem LE_apply (σ : E ≃+* E) (x : Cinf E) : LE σ x = Lx σ x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem LE_symm_apply (σ : E ≃+* E) (x : Cinf E) : (LE σ).symm x = Lx σ.symm x := rfl

/- English proof (translation)
The claim follows from `continuous_pi fun w => continuous_cc _`.
-/
theorem continuous_Lx (σ : E ≃+* E) : Continuous (Lx σ) :=
  continuous_pi fun w => continuous_cc _

/- English proof (translation)
The claim follows from `funext fun w => cc_smul _ r x`.
-/
theorem Lx_smul (σ : E ≃+* E) (r : ℝ) (x : Cinf E) : Lx σ (r • x) = r • Lx σ x :=
  funext fun w => cc_smul _ r x

/- English proof (translation)
The claim follows from `funext fun w => cc_star _ x`.
-/
theorem Lx_star (σ : E ≃+* E) (x : Cinf E) : Lx σ (star x) = star (Lx σ x) :=
  funext fun w => cc_star _ x

/- English proof (translation)
Establish `hτ : (τ.comp (σ.symm : E →+* E)).comp (σ : E →+* E) = τ` using `RingHom.ext fun y => by`. Express the relevant statement in the definitionally equal form `τ (σ.symm (σ y)) = τ y`. Rewrite using `[RingEquiv.symm_apply_apply]`. Use `eq_atEmb (fun w hw => ?_) (by rw [cc_Lx, hτ, cc_atEmb])` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cc (w.embedding.comp (σ : E →+* E)) (atEmb τ z) = 0`.

Use `cc_eq_zero (atEmb_apply_ne z fun e => hw ?_)` and prove the remaining obligations. Break down `InfinitePlace.mk_eq_iff.1 e with e' | e'` into its components or cases. Rewrite using `[← InfinitePlace.mk_embedding w]`. Use `congr 1`. Use `RingHom.ext fun y => ?_` and prove the remaining obligations.

Use `congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'` as an intermediate fact. Express the relevant statement in the definitionally equal form `w.embedding (σ (σ.symm y)) = τ (σ.symm y) at this`. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Conclude with `this`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_conjugate_eq]`.

Use `congr 1`. Use `RingHom.ext fun y => ?_` and prove the remaining obligations. Use `congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'` as an intermediate fact. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (w.embedding (σ (σ.symm y))) = τ (σ.symm y) at this`. Rewrite `this` using `[RingEquiv.apply_symm_apply]`.

Conclude with `this`.
-/
theorem Lx_atEmb (σ : E ≃+* E) (τ : E →+* ℂ) (z : ℂ) :
    Lx σ (atEmb τ z) = atEmb (τ.comp (σ.symm : E →+* E)) z := by
  have hτ : (τ.comp (σ.symm : E →+* E)).comp (σ : E →+* E) = τ := RingHom.ext fun y => by
    change τ (σ.symm (σ y)) = τ y
    rw [RingEquiv.symm_apply_apply]
  refine eq_atEmb (fun w hw => ?_) (by rw [cc_Lx, hτ, cc_atEmb])
  change cc (w.embedding.comp (σ : E →+* E)) (atEmb τ z) = 0
  refine cc_eq_zero (atEmb_apply_ne z fun e => hw ?_)
  rcases InfinitePlace.mk_eq_iff.1 e with e' | e'
  · rw [← InfinitePlace.mk_embedding w]
    congr 1
    refine RingHom.ext fun y => ?_
    have := congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'
    change w.embedding (σ (σ.symm y)) = τ (σ.symm y) at this
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  · rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_conjugate_eq]
    congr 1
    refine RingHom.ext fun y => ?_
    have := congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'
    change starRingEnd ℂ (w.embedding (σ (σ.symm y))) = τ (σ.symm y) at this
    rw [RingEquiv.apply_symm_apply] at this
    exact this

/- English proof (translation)
Establish `key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E), Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x`. Introduce and unpack `_ v rfl f hf h`. Conclude with `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _`. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pLoc E v (conjFin c.symm (conjFin c x)) = pLoc E v x`.

Rewrite using `[pLoc_conjFin, pLoc_conjFin]`. Use `key v _ ?_ (conjLoc c.symm v ∘ conjLoc c _) ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_` and prove the remaining obligations. Use `(eq_conjSrc (c := c) fun k => ?_).symm` and prove the remaining obligations. Establish `h1` using `(conjLoc_spec c.symm v).2.2 (algebraMap E _ (c k))`. Rewrite `h1` using `[(conjLoc_spec c.symm v).2.1, RingEquiv.symm_apply_apply]`.

Establish `e1 : Valued.v (algebraMap E (v.adicCompletion E) k) = v.valuation E k` using `v.valuedAdicCompletion_eq_valuation' k`. Establish `e2 : Valued.v (algebraMap E ((conjSrc c.symm v).adicCompletion E) (c k)) = (conjSrc c.symm v).valuation E (c k)` using `(conjSrc c.symm v).valuedAdicCompletion_eq_valuation' (c k)`. Rewrite `h1` using `[e1, e2]`. Conclude with `h1.symm`. Rewrite using `[Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1, RingEquiv.symm_apply_apply]`.
-/
theorem conjFin_symm_conjFin (c : E ≃+* E) (x : Af E) : conjFin c.symm (conjFin c x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => ?_
  change pLoc E v (conjFin c.symm (conjFin c x)) = pLoc E v x
  rw [pLoc_conjFin, pLoc_conjFin]
  refine key v _ ?_ (conjLoc c.symm v ∘ conjLoc c _) ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  · refine (eq_conjSrc (c := c) fun k => ?_).symm
    have h1 := (conjLoc_spec c.symm v).2.2 (algebraMap E _ (c k))
    rw [(conjLoc_spec c.symm v).2.1, RingEquiv.symm_apply_apply] at h1
    have e1 : Valued.v (algebraMap E (v.adicCompletion E) k) = v.valuation E k := v.valuedAdicCompletion_eq_valuation' k
    have e2 : Valued.v (algebraMap E ((conjSrc c.symm v).adicCompletion E) (c k)) = (conjSrc c.symm v).valuation E (c k) :=
      (conjSrc c.symm v).valuedAdicCompletion_eq_valuation' (c k)
    rw [e1, e2] at h1
    exact h1.symm
  · rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1, RingEquiv.symm_apply_apply]

structure GD (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] where
  σ : E ≃+* E
  s : Ad E ≃+* Ad E
  c : Af E ≃+* Af E
  cont : Continuous s
  cont' : Continuous s.symm
  contc : Continuous c
  contc' : Continuous c.symm
  inf : ∀ x, pInf E (s x) = Lx σ (pInf E x)
  fin : ∀ x, pFin E (s x) = c (pFin E x)
  rat : ∀ x : E, s (algebraMap E (Ad E) x) = algebraMap E (Ad E) (σ x)

def GD.symm (d : GD E) : GD E where
  σ := d.σ.symm
  s := d.s.symm
  c := d.c.symm
  cont := d.cont'
  cont' := d.cont
  contc := d.contc'
  contc' := d.contc
  inf x := by
    have h := d.inf (d.s.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, Lx_symm']
  fin x := by
    have h := d.fin (d.s.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, RingEquiv.symm_apply_apply]
  rat x := by
    rw [RingEquiv.symm_apply_eq, d.rat, RingEquiv.apply_symm_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GD.symm_alt (d : GD E) : d.symm.s = d.s.symm := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GD.symm_σ (d : GD E) : d.symm.σ = d.σ.symm := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GD.symm_c (d : GD E) : d.symm.c = d.c.symm := rfl

/- English proof (translation)
The claim follows from `(infEq E).symm_apply_apply z`.
-/
theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

/- English proof (translation)
The claim follows from `map_zero (infEq E).symm`.
-/
theorem pInf_sFin (z : Af E) : pInf E (sFin E z) = 0 := map_zero (infEq E).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_sFin (z : Af E) : pFin E (sFin E z) = z := rfl

/- English proof (translation)
The claim follows from `ad_ext (by rw [map_add, pInf_sInf, pInf_sFin, add_zero]) (by rw [map_add, pFin_sInf, pFin_sFin, zero_add])`.
-/
theorem ad_decomp (x : Ad E) : x = sInf E (pInf E x) + sFin E (pFin E x) :=
  ad_ext (by rw [map_add, pInf_sInf, pInf_sFin, add_zero]) (by rw [map_add, pFin_sInf, pFin_sFin, zero_add])

/- English proof (translation)
Take `⟨hc, hr, hf⟩` from `h`. Establish `hfin : ∀ x, pFin E (s x) = conjFin σ (pFin E x)` using `hf`. Take `⟨L0, hL0⟩ : ∃ L0 : Cinf E → Cinf E, ∀ y, L0 y = pInf E (s (sInf E y))` from `⟨_, fun _ => rfl⟩`. Establish `hsInf : ∀ y, s (sInf E y) = sInf E (L0 y)` using `fun y => ad_ext (by rw [pInf_sInf, hL0]) (by rw [hfin, pFin_sInf, pFin_sInf, map_zero])`. Establish `hadd : ∀ y y', L0 (y + y') = L0 y + L0 y'` using `fun y y' => by`.

Rewrite using `[hL0, hL0, hL0, map_add, map_add, map_add]`. Establish `hmul : ∀ y y', L0 (y * y') = L0 y * L0 y'` using `fun y y' => by`. Rewrite using `[hL0, hL0, hL0, map_mul, map_mul, map_mul]`. Establish `hcont : Continuous L0`. Establish `e : L0 = fun y => pInf E (s (sInf E y))` using `funext hL0`.

Rewrite using `[e]`. Conclude with `(GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (hc.comp (GlobalTheory.CuspRep.GASplit.continuous_sInf E))`. Set `A : Cinf E →+ Cinf E` to `{ toFun := L0 map_zero' := by rw [hL0, map_zero, map_zero, map_zero] map_add' := hadd }`. Set `Lin : Cinf E →ₗ[ℝ] Cinf E` to `{ toFun := L0 map_add' := hadd map_smul' := fun r y => map_real_smul A hcont r y }`. Establish `hinj : Function.Injective Lin` using `fun y y' e => by`.

Establish `e1 : s (sInf E y) = s (sInf E y')`. Rewrite using `[hsInf, hsInf]`. Conclude with `congrArg (sInf E) e`. Establish `e2` using `congrArg (pInf E) (s.injective e1)`. Rewrite `e2` using `[pInf_sInf, pInf_sInf]`. Then use the resulting hypothesis.

Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.1 hinj) 1`. Establish `hy' : L0 y = 1` using `hy`. Establish `h1 : L0 1 = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hs1 : s (sInf E 1) = sInf E 1` using `by rw [hsInf, h1]`.

Establish `hsFin : ∀ z, pInf E (s (sFin E z)) = 0` using `fun z => by`. Establish `e : sFin E z = sFin E z * (1 - sInf E 1)` using `ad_ext (by rw [map_mul, pInf_sFin, zero_mul]) (by rw [map_mul, map_sub, map_one, pFin_sFin, pFin_sInf, sub_zero, mul_one])`. Rewrite using `[e, map_mul, map_mul, map_sub, map_one, map_sub, map_one, hs1, pInf_sInf, sub_self, mul_zero]`. Establish `hinf0 : ∀ x, pInf E (s x) = L0 (pInf E x)` using `fun x => by conv_lhs => rw [ad_decomp x]`. Rewrite using `[map_add, map_add, hsFin, add_zero, hL0]`.

Establish `hD : DenseRange fun m : E => pInf E (algebraMap E (Ad E) m)`. Establish `e : (fun m : E => pInf E (algebraMap E (Ad E) m)) = (infEq E).symm ∘ algebraMap E (InfiniteAdeleRing E)` using `rfl`. Rewrite using `[e]`. Conclude with `(infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E)`. Establish `heq : L0 = Lx σ` using `hD.equalizer hcont (continuous_Lx σ) (funext fun m => by`.

Express the relevant statement in the definitionally equal form `L0 (pInf E (algebraMap E (Ad E) m)) = Lx σ (pInf E (algebraMap E (Ad E) m))`. Rewrite using `[← hinf0, hr]`. Use `cc_ext fun ρ => ?_` and prove the remaining obligations. Rewrite using `[cc_Lx, cc_pInf_alg, cc_pInf_alg]`. Use the proof step `rfl)`.

Establish `hinf : ∀ x, pInf E (s x) = Lx σ (pInf E x)` using `fun x => by rw [hinf0, heq]`. Set `c : Af E ≃+* Af E` to `{ toFun := conjFin σ invFun := conjFin σ.symm left_inv := conjFin_symm_conjFin σ right_inv := fun x => by`. Use `conjFin_symm_conjFin σ.symm x` as an intermediate fact. Rewrite `this` using `[RingEquiv.symm_symm]`. Then use the resulting hypothesis. Use the proof step `map_mul' := map_mul _`.

Use the proof step `map_add' := map_add _ }`. Establish `hsymm : ∀ x, s.symm x = sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x))` using `fun x => by`. Rewrite using `[RingEquiv.symm_apply_eq]`. Use `ad_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hinf, map_add, pInf_sInf, pInf_sFin, add_zero, Lx_symm]`.

Rewrite using `[hfin, map_add, pFin_sInf, pFin_sFin, zero_add]`. Use `conjFin_symm_conjFin σ.symm (pFin E x)` as an intermediate fact. Rewrite `this` using `[RingEquiv.symm_symm]`. Conclude with `this.symm`. Establish `hcont' : Continuous s.symm`.

Establish `e : (s.symm : Ad E → Ad E) = fun x => sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x))` using `funext hsymm`. Rewrite using `[e]`. Conclude with `((GlobalTheory.CuspRep.GASplit.continuous_sInf E).comp ((continuous_Lx _).comp (GlobalTheory.CuspRep.GASplit.continuous_pInf E))).add ((GlobalTheory.CuspRep.GASplit.continuous_sFin E).comp ((continuous_conjFin _).comp (GlobalTheory.CuspRep.GASplit.continuous_pFin E)))`. Conclude with `⟨⟨σ, s, c, hc, hcont', continuous_conjFin σ, continuous_conjFin σ.symm, hinf, hfin, hr⟩, rfl, rfl⟩`.
-/
theorem exists_GD (σ : E ≃+* E) (s : Ad E ≃+* Ad E) (h : IsGalAd σ s) : ∃ d : GD E, d.s = s ∧ d.σ = σ := by
  obtain ⟨hc, hr, hf⟩ := h
  have hfin : ∀ x, pFin E (s x) = conjFin σ (pFin E x) := hf
  obtain ⟨L0, hL0⟩ : ∃ L0 : Cinf E → Cinf E, ∀ y, L0 y = pInf E (s (sInf E y)) := ⟨_, fun _ => rfl⟩
  have hsInf : ∀ y, s (sInf E y) = sInf E (L0 y) := fun y =>
    ad_ext (by rw [pInf_sInf, hL0]) (by rw [hfin, pFin_sInf, pFin_sInf, map_zero])
  have hadd : ∀ y y', L0 (y + y') = L0 y + L0 y' := fun y y' => by
    rw [hL0, hL0, hL0, map_add, map_add, map_add]
  have hmul : ∀ y y', L0 (y * y') = L0 y * L0 y' := fun y y' => by
    rw [hL0, hL0, hL0, map_mul, map_mul, map_mul]
  have hcont : Continuous L0 := by
    have e : L0 = fun y => pInf E (s (sInf E y)) := funext hL0
    rw [e]
    exact (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (hc.comp (GlobalTheory.CuspRep.GASplit.continuous_sInf E))
  let A : Cinf E →+ Cinf E :=
    { toFun := L0
      map_zero' := by rw [hL0, map_zero, map_zero, map_zero]
      map_add' := hadd }
  let Lin : Cinf E →ₗ[ℝ] Cinf E :=
    { toFun := L0
      map_add' := hadd
      map_smul' := fun r y => map_real_smul A hcont r y }
  have hinj : Function.Injective Lin := fun y y' e => by
    have e1 : s (sInf E y) = s (sInf E y') := by
      rw [hsInf, hsInf]; exact congrArg (sInf E) e
    have e2 := congrArg (pInf E) (s.injective e1)
    rwa [pInf_sInf, pInf_sInf] at e2
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have hy' : L0 y = 1 := hy
  have h1 : L0 1 = 1 := by
    calc L0 1 = L0 1 * L0 y := by rw [hy', mul_one]
      _ = L0 y := by rw [← hmul, one_mul]
      _ = 1 := hy'
  have hs1 : s (sInf E 1) = sInf E 1 := by rw [hsInf, h1]
  have hsFin : ∀ z, pInf E (s (sFin E z)) = 0 := fun z => by
    have e : sFin E z = sFin E z * (1 - sInf E 1) :=
      ad_ext (by rw [map_mul, pInf_sFin, zero_mul])
        (by rw [map_mul, map_sub, map_one, pFin_sFin, pFin_sInf, sub_zero, mul_one])
    rw [e, map_mul, map_mul, map_sub, map_one, map_sub, map_one, hs1, pInf_sInf, sub_self, mul_zero]
  have hinf0 : ∀ x, pInf E (s x) = L0 (pInf E x) := fun x => by
    conv_lhs => rw [ad_decomp x]
    rw [map_add, map_add, hsFin, add_zero, hL0]
  have hD : DenseRange fun m : E => pInf E (algebraMap E (Ad E) m) := by
    have e : (fun m : E => pInf E (algebraMap E (Ad E) m)) =
        (infEq E).symm ∘ algebraMap E (InfiniteAdeleRing E) := rfl
    rw [e]
    exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E)
      (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E)
  have heq : L0 = Lx σ := hD.equalizer hcont (continuous_Lx σ) (funext fun m => by
    change L0 (pInf E (algebraMap E (Ad E) m)) = Lx σ (pInf E (algebraMap E (Ad E) m))
    rw [← hinf0, hr]
    refine cc_ext fun ρ => ?_
    rw [cc_Lx, cc_pInf_alg, cc_pInf_alg]
    rfl)
  have hinf : ∀ x, pInf E (s x) = Lx σ (pInf E x) := fun x => by rw [hinf0, heq]
  let c : Af E ≃+* Af E :=
    { toFun := conjFin σ
      invFun := conjFin σ.symm
      left_inv := conjFin_symm_conjFin σ
      right_inv := fun x => by
        have := conjFin_symm_conjFin σ.symm x
        rwa [RingEquiv.symm_symm] at this
      map_mul' := map_mul _
      map_add' := map_add _ }
  have hsymm : ∀ x, s.symm x = sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x)) := fun x => by
    rw [RingEquiv.symm_apply_eq]
    refine ad_ext ?_ ?_
    · rw [hinf, map_add, pInf_sInf, pInf_sFin, add_zero, Lx_symm]
    · rw [hfin, map_add, pFin_sInf, pFin_sFin, zero_add]
      have := conjFin_symm_conjFin σ.symm (pFin E x)
      rw [RingEquiv.symm_symm] at this
      exact this.symm
  have hcont' : Continuous s.symm := by
    have e : (s.symm : Ad E → Ad E) =
        fun x => sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x)) := funext hsymm
    rw [e]
    exact ((GlobalTheory.CuspRep.GASplit.continuous_sInf E).comp ((continuous_Lx _).comp (GlobalTheory.CuspRep.GASplit.continuous_pInf E))).add
      ((GlobalTheory.CuspRep.GASplit.continuous_sFin E).comp ((continuous_conjFin _).comp (GlobalTheory.CuspRep.GASplit.continuous_pFin E)))
  exact ⟨⟨σ, s, c, hc, hcont', continuous_conjFin σ, continuous_conjFin σ.symm, hinf, hfin, hr⟩, rfl, rfl⟩

section Pull

variable {a : ℕ} (d : GD E)

def SA (d : GD E) (a : ℕ) : GA E a →* GA E a := GeneralLinearGroup.map d.s.toRingHom

/- English proof (translation)
Use extensionality with `i j : 2`. Conclude with `d.s.apply_symm_apply _`.
-/
theorem SA_SA_symm (g : GA E a) : SA d a (SA d.symm a g) = g := by
  ext i j : 2
  exact d.s.apply_symm_apply _

/- English proof (translation)
Use extensionality with `i j : 2`. Conclude with `d.s.symm_apply_apply _`.
-/
theorem SA_symm_SA (g : GA E a) : SA d.symm a (SA d a g) = g := by
  ext i j : 2
  exact d.s.symm_apply_apply _

def LLm (σ : E ≃+* E) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => Lx σ (X i j)
      map_add' := fun X Y => by funext i j; exact map_add _ _ _
      map_smul' := fun t X => by funext i j; exact Lx_smul σ t (X i j) }

/- English proof (translation)
The claim follows from `ga_ext (by rw [SA, GlobalTheory.BarPull.map_map_comm (pInf E) d.s.toRingHom (Lx d.σ) d.inf, pInf_infGL, pInf_infGL]) (by rw [SA, GlobalTheory.BarPull.map_map_comm (pFin E) d.s.toRingHom d.c.toRingHom d.fin, pFin_infGL, pFin_infGL, map_one])`.
-/
theorem SA_infGL (y : GL (Fin a) (Cinf E)) :
    SA d a (infGL E a y) = infGL E a (GeneralLinearGroup.map (Lx d.σ) y) :=
  ga_ext (by rw [SA, GlobalTheory.BarPull.map_map_comm (pInf E) d.s.toRingHom (Lx d.σ) d.inf, pInf_infGL, pInf_infGL])
    (by rw [SA, GlobalTheory.BarPull.map_map_comm (pFin E) d.s.toRingHom d.c.toRingHom d.fin, pFin_infGL, pFin_infGL, map_one])

/- English proof (translation)
The claim follows from `ga_ext (by rw [SA, GlobalTheory.BarPull.map_map_comm (pInf E) d.s.toRingHom (Lx d.σ) d.inf, pInf_finGL, pInf_finGL, map_one]) (by rw [SA, GlobalTheory.BarPull.map_map_comm (pFin E) d.s.toRingHom d.c.toRingHom d.fin, pFin_finGL, pFin_finGL])`.
-/
theorem SA_finGL (k : GL (Fin a) (Af E)) :
    SA d a (finGL E a k) = finGL E a (GeneralLinearGroup.map d.c.toRingHom k) :=
  ga_ext (by rw [SA, GlobalTheory.BarPull.map_map_comm (pInf E) d.s.toRingHom (Lx d.σ) d.inf, pInf_finGL, pInf_finGL, map_one])
    (by rw [SA, GlobalTheory.BarPull.map_map_comm (pFin E) d.s.toRingHom d.c.toRingHom d.fin, pFin_finGL, pFin_finGL])

/- English proof (translation)
The claim follows from `(GlobalTheory.BarPull.map_map_comm (algebraMap E (Ad E)) d.σ.toRingHom d.s.toRingHom (fun x => (d.rat x).symm) γ).symm`.
-/
theorem SA_ratGL (γ : GL (Fin a) E) :
    SA d a (ratGL E a γ) = ratGL E a (GeneralLinearGroup.map d.σ.toRingHom γ) :=
  (GlobalTheory.BarPull.map_map_comm (algebraMap E (Ad E)) d.σ.toRingHom d.s.toRingHom (fun x => (d.rat x).symm) γ).symm

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx`. Take `rfl : x = toL u.val` from `hu.symm`. Rewrite using `[show LLm d.σ (toL u.val) = toL (GeneralLinearGroup.map (Lx d.σ) u).val from rfl, chart_val, chart_val, map_mul, SA_infGL]`. Conclude with `⟨rfl, val_mem_invSet _⟩`.
-/
theorem chart_pullS (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (SA d a g)) g x = chart φ (SA d a g) (LLm d.σ x) ∧ LLm d.σ x ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show LLm d.σ (toL u.val) = toL (GeneralLinearGroup.map (Lx d.σ) u).val from rfl,
    chart_val, chart_val, map_mul, SA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

/- English proof (translation)
Introduce `g` and use `((hφ (SA d a g)).comp (LLm (a := a) d.σ).contDiff.contDiffOn fun _ hx => (chart_pullS d φ g hx).2).congr fun _ hx => (chart_pullS d φ g hx).1`.
-/
theorem pullS_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (SA d a g)) ∈ Sm E a := fun g =>
  ((hφ (SA d a g)).comp (LLm (a := a) d.σ).contDiff.contDiffOn
    fun _ hx => (chart_pullS d φ g hx).2).congr fun _ hx => (chart_pullS d φ g hx).1

def pull (d : GD E) (a : ℕ) : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (SA d a g), pullS_mem_Sm d φ.2⟩
  invFun φ := ⟨fun g => φ.1 (SA d.symm a g), pullS_mem_Sm d.symm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (SA_SA_symm d g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (SA_symm_SA d g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull d a φ).1 g = φ.1 (SA d a g) := rfl

/- English proof (translation)
The claim follows from `Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (SA d a) g h)`.
-/
theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull d a φ) = pull d a (rt E a (SA d a h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (SA d a) g h)

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `Lx d.σ ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem LLm_one : LLm d.σ (oneL E a) = oneL E a := by
  funext i j
  change Lx d.σ ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `Subtype.ext <| funext fun g => ?_` and prove the remaining obligations. Establish `e : chart (pull d a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (SA d a g) ∘ LLm d.σ` using `Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_pullS d φ.1 g hx).1`. Establish `h2` using `HasFDerivAt.comp (oneL E a) (f := LLm d.σ) (by rw [LLm_one]; exact (differentiableAt_chart φ.2 (SA d a g)).hasFDerivAt) (LLm d.σ).hasFDerivAt`. Express the relevant statement in the definitionally equal form `fderiv ℝ _ _ X = fderiv ℝ _ _ _`. Rewrite using `[e.fderiv_eq, h2.fderiv]`.

Both sides reduce to the same expression.
-/
theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull d a φ) = pull d a (lie E a (LLm d.σ X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull d a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (SA d a g) ∘ LLm d.σ :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_pullS d φ.1 g hx).1
  have h2 := HasFDerivAt.comp (oneL E a) (f := LLm d.σ)
    (by rw [LLm_one]; exact (differentiableAt_chart φ.2 (SA d a g)).hasFDerivAt) (LLm d.σ).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

def kMap (σ : E ≃+* E) (k : Kinf E a) : Kinf E a :=
  ⟨(RingHom.mapMatrix (Lx σ)) k.1, Matrix.mem_unitaryGroup_iff.2 (by
    have e : star ((RingHom.mapMatrix (Lx σ)) k.1) = (RingHom.mapMatrix (Lx σ)) (star k.1) := by
      ext i j : 1
      change star (Lx σ (k.1 j i)) = Lx σ (star (k.1 j i))
      rw [Lx_star]
    rw [e, ← map_mul, Matrix.mem_unitaryGroup_iff.1 k.2, map_one])⟩

def opMap (d : GD E) : Op E a → Op E a
  | .fin k => .fin (GeneralLinearGroup.map d.c.toRingHom k)
  | .cpt k => .cpt (kMap d.σ k)
  | .lie X => .lie (LLm d.σ X)

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact (rt_pull d _ φ).trans (by rw [SA_finGL]; rfl)`. Consider the case `cpt k`. Establish `e : GeneralLinearGroup.map (Lx d.σ) (Unitary.toUnits k) = Unitary.toUnits (kMap d.σ k)` using `Units.ext rfl`. Conclude with `(rt_pull d (infGL E a (Unitary.toUnits k)) φ).trans (by rw [SA_infGL, e]; rfl)`.

Consider the case `lie X => exact lie_pull d X φ`.
-/
theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull d a φ) = pull d a (act (opMap d o) φ) := by
  cases o with
  | fin k => exact (rt_pull d _ φ).trans (by rw [SA_finGL]; rfl)
  | cpt k =>
    have e : GeneralLinearGroup.map (Lx d.σ) (Unitary.toUnits k) = Unitary.toUnits (kMap d.σ k) := Units.ext rfl
    exact (rt_pull d (infGL E a (Unitary.toUnits k)) φ).trans (by rw [SA_infGL, e]; rfl)
  | lie X => exact lie_pull d X φ

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Use `congrArg Op.fin (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Conclude with `d.c.apply_symm_apply _`. Consider the case `cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => Lx_symm d.σ _))`.

Consider the case `lie X => exact congrArg Op.lie (funext fun i => funext fun j => Lx_symm d.σ _)`.
-/
theorem opMap_opMap_symm (o : Op E a) : opMap d (opMap d.symm o) = o := by
  cases o with
  | fin k =>
    refine congrArg Op.fin (Units.ext (Matrix.ext fun i j => ?_))
    exact d.c.apply_symm_apply _
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => Lx_symm d.σ _))
  | lie X => exact congrArg Op.lie (funext fun i => funext fun j => Lx_symm d.σ _)

/- English proof (translation)
Rewrite using `[act_pull, opMap_opMap_symm]`.
-/
theorem pull_act (o : Op E a) (φ : Sm E a) : pull d a (act o φ) = act (opMap d.symm o) (pull d a φ) := by
  rw [act_pull, opMap_opMap_symm]

/- English proof (translation)
Establish `h2 : ∀ z, lieS E a i j (atEmb τ z) (pull d a φ) = pull d a (lieS E a i j (atEmb (τ.comp (d.σ.symm : E →+* E)) z) φ)` using `fun z => by`. Establish `e' : LLm d.σ (toL (Matrix.single i j (atEmb τ z))) = toL (Matrix.single i j (Lx d.σ (atEmb τ z)))`. Use function extensionality and compare the values at `k l`. Express the relevant statement in the definitionally equal form `Lx d.σ (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j (Lx d.σ (atEmb τ z)) k l`. Rewrite using `[Matrix.single_apply, Matrix.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[lieS_apply, lie_pull, e', Lx_atEmb, lieS_apply]`. Simplify using `only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]`.
-/
theorem Eop_pull (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (pull d a φ) = pull d a (Eop (τ.comp (d.σ.symm : E →+* E)) i j φ) := by
  have h2 : ∀ z, lieS E a i j (atEmb τ z) (pull d a φ) =
      pull d a (lieS E a i j (atEmb (τ.comp (d.σ.symm : E →+* E)) z) φ) := fun z => by
    have e' : LLm d.σ (toL (Matrix.single i j (atEmb τ z))) = toL (Matrix.single i j (Lx d.σ (atEmb τ z))) := by
      funext k l
      change Lx d.σ (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j (Lx d.σ (atEmb τ z)) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, lie_pull, e', Lx_atEmb, lieS_apply]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]

/- English proof (translation)
Use `set τ' := τ.comp (d.σ.symm : E →+* E)`. Establish `h` using `GlobalTheory.CuspRep.ConjZalg.map_qdet_semilinear ((pull d a).conjAlgEquiv ℂ).toAlgHom.toRingHom (RingHom.id ℂ) (fun c => AlgHom.commutes _ c) (Eop τ') (u + ((a : ℂ) - 1) / 2)`. Establish `e : (fun i j => ((pull d a).conjAlgEquiv ℂ).toAlgHom.toRingHom (Eop τ' i j)) = Eop τ`. Use function extensionality and compare the values at `i j`. Use `LinearMap.ext fun ψ => ?_` and prove the remaining obligations.

Take `⟨ψ, rfl⟩` from `(pull d a).surjective ψ`. Rewrite using `[Eop_pull]`. Express the relevant statement in the definitionally equal form `pull d a (Eop τ' i j ((pull d a).symm (pull d a ψ))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Rewrite `h` using `[e]`.

Rewrite using `[cap, show u + ((a : ℂ) - 1) / 2 = RingHom.id ℂ (u + ((a : ℂ) - 1) / 2) from rfl, ← h, cap]`. Generalize the expression as in `Formalism.REAL.qdet (Eop (a := a) τ') (u + ((a : ℂ) - 1) / 2) = z`. Express the relevant statement in the definitionally equal form `pull d a (z ((pull d a).symm (pull d a φ))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`.
-/
theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull d a φ) = pull d a (cap (τ.comp (d.σ.symm : E →+* E)) u φ) := by
  set τ' := τ.comp (d.σ.symm : E →+* E)
  have h := GlobalTheory.CuspRep.ConjZalg.map_qdet_semilinear ((pull d a).conjAlgEquiv ℂ).toAlgHom.toRingHom (RingHom.id ℂ)
    (fun c => AlgHom.commutes _ c) (Eop τ') (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((pull d a).conjAlgEquiv ℂ).toAlgHom.toRingHom (Eop τ' i j)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull d a).surjective ψ
    rw [Eop_pull]
    change pull d a (Eop τ' i j ((pull d a).symm (pull d a ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, show u + ((a : ℂ) - 1) / 2 = RingHom.id ℂ (u + ((a : ℂ) - 1) / 2) from rfl, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) τ') (u + ((a : ℂ) - 1) / 2) = z
  change pull d a (z ((pull d a).symm (pull d a φ))) = _
  rw [LinearEquiv.symm_apply_apply]

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨τ, u, rfl⟩` from `hx`. Conclude with `⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull d τ u⟩`. Consider the case `algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩`.
-/
theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull d a φ) = pull d a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull d τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem height_eq (y : GL (Fin a) (Cinf E)) : height y = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖ := rfl

/- English proof (translation)
Rewrite using `[height_eq]`. Combine the linear relations using `[norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]`.
-/
theorem one_le_height (y : GL (Fin a) (Cinf E)) : 1 ≤ height y := by
  rw [height_eq]
  linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]

/- English proof (translation)
Use `⟨max 1 ‖LLm (a := a) d.σ‖, le_max_left _ _, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (Lx d.σ) y).val‖ ≤ ‖LLm (a` using `a) d.σ‖ * ‖toL y.val‖ := fun y => (LLm d.σ).le_opNorm (toL y.val)`. Establish `hK : ‖LLm (a` using `a) d.σ‖ ≤ max 1 ‖LLm (a := a) d.σ‖ := le_max_right _ _`. Establish `hK1 : (1 : ℝ) ≤ max 1 ‖LLm (a` using `a) d.σ‖ := le_max_left _ _`. Rewrite using `[height_eq, height_eq, ← map_inv]`.

Establish `a1` using `h1 y`. Establish `a2` using `h1 y⁻¹`. Establish `n1` using `norm_nonneg (toL y.val)`. Establish `n2` using `norm_nonneg (toL (y⁻¹).val)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem height_map_le : ∃ K : ℝ, 1 ≤ K ∧ ∀ y : GL (Fin a) (Cinf E),
    height (GeneralLinearGroup.map (Lx d.σ) y) ≤ K * height y := by
  refine ⟨max 1 ‖LLm (a := a) d.σ‖, le_max_left _ _, fun y => ?_⟩
  have h1 : ∀ y : GL (Fin a) (Cinf E),
      ‖toL (GeneralLinearGroup.map (Lx d.σ) y).val‖ ≤ ‖LLm (a := a) d.σ‖ * ‖toL y.val‖ := fun y =>
    (LLm d.σ).le_opNorm (toL y.val)
  have hK : ‖LLm (a := a) d.σ‖ ≤ max 1 ‖LLm (a := a) d.σ‖ := le_max_right _ _
  have hK1 : (1 : ℝ) ≤ max 1 ‖LLm (a := a) d.σ‖ := le_max_left _ _
  rw [height_eq, height_eq, ← map_inv]
  have a1 := h1 y
  have a2 := h1 y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  nlinarith

/- English proof (translation)
Rewrite using `[pull_apply, map_mul, SA_ratGL, h.left, pull_apply] level := by`. Use `h.level.preimage (GlobalTheory.BarPull.continuous_mapGL d.c.toRingHom (by exact d.contc)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Conclude with `(Eq.congr_left (act_pull d (.fin k) φ)).trans (pull d a).injective.eq_iff`. Use `kfin := by`.

Use `h.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (pull d a).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull d (.cpt k) φ).symm⟩`. Use `zfin := by`.

Use `h.zfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (pull d a).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨z', h1, h2⟩` from `Zalg_pull d hz`. Conclude with `⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩`.

Use `growth g := by`. Take `⟨C, N, h1⟩` from `h.growth (SA d a g)`. Take `⟨K, hK1, hK⟩` from `height_map_le (a := a) d`. Use `⟨C * K ^ N, N, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[pull_apply, map_mul, SA_infGL]`.

Establish `hy` using `h1 (GeneralLinearGroup.map (Lx d.σ) y)`. Establish `hpos : 0 < height (GeneralLinearGroup.map (Lx d.σ) y) ^ N` using `pow_pos (lt_of_lt_of_le one_pos (one_le_height _)) N`. Establish `hC : 0 ≤ C`. Assume the negation of the conclusion as `hc`. Use `mul_neg_of_neg_of_pos (lt_of_not_ge hc) hpos` as an intermediate fact.

Combine the linear relations using `[norm_nonneg (φ.1 (SA d a g * infGL E a (GeneralLinearGroup.map (Lx d.σ) y)))]`. Use `hy.trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← mul_pow]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans zero_le_one (one_le_height _)) (hK y) N) hC`.
-/
theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull d a φ) where
  left γ g := by rw [pull_apply, map_mul, SA_ratGL, h.left, pull_apply]
  level := by
    convert h.level.preimage (GlobalTheory.BarPull.continuous_mapGL d.c.toRingHom (by exact d.contc)) using 1
    ext k
    exact (Eq.congr_left (act_pull d (.fin k) φ)).trans (pull d a).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (pull d a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull d (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (pull d a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull d hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (SA d a g)
    obtain ⟨K, hK1, hK⟩ := height_map_le (a := a) d
    refine ⟨C * K ^ N, N, fun y => ?_⟩
    rw [pull_apply, map_mul, SA_infGL]
    have hy := h1 (GeneralLinearGroup.map (Lx d.σ) y)
    have hpos : 0 < height (GeneralLinearGroup.map (Lx d.σ) y) ^ N :=
      pow_pos (lt_of_lt_of_le one_pos (one_le_height _)) N
    have hC : 0 ≤ C := by
      by_contra hc
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hc) hpos
      linarith [norm_nonneg (φ.1 (SA d a g * infGL E a (GeneralLinearGroup.map (Lx d.σ) y)))]
    refine hy.trans ?_
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans zero_le_one (one_le_height _)) (hK y) N) hC

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨fun p => d.σ (y p), funext fun p => (d.rat (y p)).symm⟩`.
-/
theorem mem_ratN_alt {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) : (fun p => d.s (x p)) ∈ ratN E a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => d.σ (y p), funext fun p => (d.rat (y p)).symm⟩

open MeasureTheory in
/- English proof (translation)
Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Set `β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E)` to `{ toFun := fun x p => d.s (x p) invFun := fun x p => d.s.symm (x p) left_inv := fun x => funext fun p => d.s.symm_apply_apply _ right_inv := fun x => funext fun p => d.s.apply_symm_apply _ map_add' := fun x y => funext fun p => map_add d.s _ _ continuous_toFun := continuous_pi fu …`. Set `e : ratN E a r ≃ ratN E a r` to `{ toFun := fun y => ⟨β.symm y, mem_ratN_alt d.symm y.2⟩ invFun := fun x => ⟨β x, mem_ratN_alt d x.2⟩ left_inv := fun y => Subtype.ext (β.apply_symm_apply y) right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }`. Set `m` to `β.toHomeomorph.toMeasurableEquiv`. Establish `h2` using `hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ) (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by`.

Express the relevant statement in the definitionally equal form `β (β.symm y + x) = y + β x`. Rewrite using `[map_add, β.apply_symm_apply]) (SA d a g)`. Rewrite `h2` using `[m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]`. Rewrite using `[← h2]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Use `beta_reduce`. Rewrite using `[map_mul, SA, GlobalTheory.BarPull.map_unip]`. Both sides reduce to the same expression.
-/
theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (SA d a g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => d.s (x p)
      invFun := fun x p => d.s.symm (x p)
      left_inv := fun x => funext fun p => d.s.symm_apply_apply _
      right_inv := fun x => funext fun p => d.s.apply_symm_apply _
      map_add' := fun x y => funext fun p => map_add d.s _ _
      continuous_toFun := continuous_pi fun p => d.cont.comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => d.cont'.comp (continuous_apply p) }
  let e : ratN E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, mem_ratN_alt d.symm y.2⟩
      invFun := fun x => ⟨β x, mem_ratN_alt d x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (SA d a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, SA, GlobalTheory.BarPull.map_unip]
  rfl

def pullSub (π : CuspSub E a) : CuspSub E a where
  V := π.V.map (pull d a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull d (π.cusp φ hφ).1, isCuspidal_pull d (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull d o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull d a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull d a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull d a).injective h2]) fun o φ hφ => by
      change pull d a (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pull d a).toLinearMap) (pull d a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

end Pull

end UpperTheory.CBC.SConjSpaceCAux

open UpperTheory.CBC.SConjSpaceCAux in

/- English proof (translation)
Introduce `M _ _ _ σ s hs n P`. Take `⟨d, rfl, rfl⟩` from `exists_GD σ s hs`. Use `⟨pullSub d P, ?_⟩` and prove the remaining obligations. Use extensionality with `f`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨φ, ⟨ψ, hψ, rfl⟩, rfl⟩`. Conclude with `⟨ψ.1, ⟨ψ, hψ, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩`. Conclude with `⟨pull d n ψ, ⟨ψ, hψ, rfl⟩, rfl⟩`.
-/
theorem UpperTheory.CBC.SConjSpaceC_holds : UpperTheory.CBC.SConjSpaceC := by
  intro M _ _ _ σ s hs n P
  obtain ⟨d, rfl, rfl⟩ := exists_GD σ s hs
  refine ⟨pullSub d P, ?_⟩
  ext f
  constructor
  · rintro ⟨φ, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ.1, ⟨ψ, hψ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨pull d n ψ, ⟨ψ, hψ, rfl⟩, rfl⟩
