import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.FiniteProjectionSingleSame
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSqNeg

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical NumberField.LiesOver

namespace UpperTheory.ConvolutionTheory.R2.Ff.NI

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pInf_apply (x : A E) (w : InfinitePlace E) : GlobalTheory.CuspRep.pInf E x w =
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (x.1 w) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(infEq E).symm (1 - infEq E 1 + infEq E s.val) = _`. Simplify using the standard rewrite rules.
-/
private theorem pInf_infId (s : (Cinf E)ˣ) : GlobalTheory.CuspRep.pInf E (infId E s).val = s.val := by
  change (infEq E).symm (1 - infEq E 1 + infEq E s.val) = _
  simp

variable (F) in
/- English proof (translation)
Set `ψ : ℝ →+* ℂ` to `((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toRingHom.comp (algebraMap (w.comap (algebraMap F E)).Completion w.Completion)).comp (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm.toRi …`. Establish `hψ : Continuous ψ` using `((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w))).comp (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebr …`. Use `map_real_smul ψ hψ s 1` as an intermediate fact. Simplify `this` using `[ψ]`.
-/
private theorem real_comp (w : InfinitePlace E) (s : ℝ) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (algebraMap (w.comap (algebraMap F E)).Completion w.Completion
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm s)) = s := by
  let ψ : ℝ →+* ℂ := ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toRingHom.comp
    (algebraMap (w.comap (algebraMap F E)).Completion w.Completion)).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w))).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

/- English proof (translation)
Establish `e : a.1 (w.comap (algebraMap F E)) = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm (TR.pInf F a (w.comap (algebraMap F E)))` using `((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm_apply_apply _).symm`. Rewrite using `[pInf_apply]`. Express the relevant statement in the definitionally equal form `(InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (algebraMap (w.comap (algebraMap F E)).Completion w.Completion (a.1 (w.comap (algebraMap F E)))) = _`. Rewrite using `[e]`. Conclude with `real_comp F w _`.
-/
private theorem pInf_am (a : A F) (w : InfinitePlace E) :
    GlobalTheory.CuspRep.pInf E (am E a) w = ((TR.pInf F a (w.comap (algebraMap F E)) : ℝ) : ℂ) := by
  have e : a.1 (w.comap (algebraMap F E)) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm
        (TR.pInf F a (w.comap (algebraMap F E))) :=
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm_apply_apply _).symm
  rw [pInf_apply]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (algebraMap (w.comap (algebraMap F E)).Completion w.Completion (a.1 (w.comap (algebraMap F E)))) = _
  rw [e]
  exact real_comp F w _

/- English proof (translation)
Establish `h` using `congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F D.δ) v`. Express the relevant statement in the definitionally equal form `TR.pInf F (rt D.δ) v = _ at h`. Rewrite using `[h]`. Conclude with `D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))`.
-/
private theorem rt_δ_neg (D : Dat F E) (v : InfinitePlace F) : TR.pInf F (rt D.δ) v < 0 := by
  have h := congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F D.δ) v
  change TR.pInf F (rt D.δ) v = _ at h
  rw [h]
  exact D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg hr h`.
-/
private theorem conj_of_sq_neg {t : ℂ} {r : ℝ} (hr : r < 0) (h : t ^ 2 = (r : ℂ)) : (starRingEnd ℂ) t = -t :=
  _root_.UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg hr h

/- English proof (translation)
Use `conj_of_sq_neg (rt_δ_neg D (w.comap (algebraMap F E))) ?_` and prove the remaining obligations. Rewrite using `[← pInf_am, ← D.rt_θ_sq, map_pow]`. Both sides reduce to the same expression.
-/
private theorem pInf_rt_conj (D : Dat F E) (w : InfinitePlace E) :
    (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E (rt D.θ) w) = -GlobalTheory.CuspRep.pInf E (rt D.θ) w := by
  refine conj_of_sq_neg (rt_δ_neg D (w.comap (algebraMap F E))) ?_
  rw [← pInf_am, ← D.rt_θ_sq, map_pow]
  rfl

/- English proof (translation)
Take `⟨u, t, rfl⟩` from `D.exists_mkE x`. Rewrite using `[Dat.bar_mkE, Dat.mkE_def, Dat.mkE_def]`. Simplify using `only [map_add, map_mul, map_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, pInf_rt_conj, pInf_am, TR.pInf, Complex.conj_ofReal]`. Simplify using the standard rewrite rules.
-/
private theorem pInf_bar (D : Dat F E) (x : A E) (w : InfinitePlace E) :
    GlobalTheory.CuspRep.pInf E (D.bar x) w = (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E x w) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE x
  rw [Dat.bar_mkE, Dat.mkE_def, Dat.mkE_def]
  simp only [map_add, map_mul, map_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, pInf_rt_conj, pInf_am,
    TR.pInf, Complex.conj_ofReal]
  simp

/- English proof (translation)
Rewrite using `[← pInf_am, D.am_ideleNorm, map_mul, Pi.mul_apply, pInf_bar]`.
-/
private theorem pInf_norm (D : Dat F E) (z : (A E)ˣ) (w : InfinitePlace E) :
    ((TR.pInf F (ideleNorm F E z : (A F)ˣ) (w.comap (algebraMap F E)) : ℝ) : ℂ) =
      GlobalTheory.CuspRep.pInf E z w * (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E z w) := by
  rw [← pInf_am, D.am_ideleNorm, map_mul, Pi.mul_apply, pInf_bar]

/- English proof (translation)
Use `set z : A E := (infId E s).val with hz`. Establish `hz2 : z.2 = 1`. Express the relevant statement in the definitionally equal form `(1 : Af E) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Establish `hf : am E (1 - eInf F) = ((0, 1) : A E)`.

Rewrite using `[map_sub, map_one]`. Establish `h1 : (am E (eInf F)).1 = 1`. Rewrite using `[AdeleBaseChange.adeleMap_apply, show (eInf F).1 = 1 from rfl, map_one]`. Establish `h2 : (am E (eInf F)).2 = 0`. Rewrite using `[AdeleBaseChange.adeleMap_apply, show (eInf F).2 = 0 from rfl, map_zero]`.

Conclude with `Prod.ext (by change (1 : InfiniteAdeleRing E) - (am E (eInf F)).1 = 0; rw [h1]; simp) (by change (1 : FiniteAdeleRing (𝓞 E) E) - (am E (eInf F)).2 = 1; rw [h2]; simp)`. Establish `hfz : am E (1 - eInf F) * z = am E (1 - eInf F)`. Rewrite using `[hf]`. Conclude with `Prod.ext (zero_mul _) (by change (1 : FiniteAdeleRing (𝓞 E) E) * z.2 = 1; rw [hz2, one_mul])`. Establish `hfb : am E (1 - eInf F) * D.bar z = am E (1 - eInf F)`.

Use `congrArg D.bar hfz` as an intermediate fact. Rewrite `this` using `[map_mul, D.bar_am]`. Then use the resulting hypothesis. Establish `key : (1 - eInf F) * ((ideleNorm F E (infId E s) : (A F)ˣ) : A F) = (1 - eInf F) * 1`. Apply `am_injective (E := E)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, D.am_ideleNorm, map_one, mul_one, ← hz, ← mul_assoc, hfz, hfb]`.

Establish `k1` using `one_sub_eInf_mul (F := F) ((ideleNorm F E (infId E s) : (A F)ˣ) : A F)`. Establish `k2` using `one_sub_eInf_mul (F := F) 1`. Conclude with `congrArg Prod.snd (k1.symm.trans (key.trans k2))`.
-/
private theorem fin_norm (D : Dat F E) (s : (Cinf E)ˣ) : ((ideleNorm F E (infId E s) : (A F)ˣ) : A F).2 = 1 := by
  set z : A E := (infId E s).val with hz
  have hz2 : z.2 = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have hf : am E (1 - eInf F) = ((0, 1) : A E) := by
    rw [map_sub, map_one]
    have h1 : (am E (eInf F)).1 = 1 := by
      rw [AdeleBaseChange.adeleMap_apply, show (eInf F).1 = 1 from rfl, map_one]
    have h2 : (am E (eInf F)).2 = 0 := by
      rw [AdeleBaseChange.adeleMap_apply, show (eInf F).2 = 0 from rfl, map_zero]
    exact Prod.ext (by change (1 : InfiniteAdeleRing E) - (am E (eInf F)).1 = 0; rw [h1]; simp)
      (by change (1 : FiniteAdeleRing (𝓞 E) E) - (am E (eInf F)).2 = 1; rw [h2]; simp)
  have hfz : am E (1 - eInf F) * z = am E (1 - eInf F) := by
    rw [hf]
    exact Prod.ext (zero_mul _) (by change (1 : FiniteAdeleRing (𝓞 E) E) * z.2 = 1; rw [hz2, one_mul])
  have hfb : am E (1 - eInf F) * D.bar z = am E (1 - eInf F) := by
    have := congrArg D.bar hfz
    rwa [map_mul, D.bar_am] at this
  have key : (1 - eInf F) * ((ideleNorm F E (infId E s) : (A F)ˣ) : A F) = (1 - eInf F) * 1 := by
    apply am_injective (E := E)
    rw [map_mul, map_mul, D.am_ideleNorm, map_one, mul_one, ← hz, ← mul_assoc, hfz, hfb]
  have k1 := one_sub_eInf_mul (F := F) ((ideleNorm F E (infId E s) : (A F)ˣ) : A F)
  have k2 := one_sub_eInf_mul (F := F) 1
  exact congrArg Prod.snd (k1.symm.trans (key.trans k2))

/- English proof (translation)
Use `⟨D.b.repr x 0, D.b.repr x 1, ?_⟩` and prove the remaining obligations. Establish `h` using `D.b.sum_repr x`. Rewrite `h` using `[Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Conclude with `h.symm`.
-/
private theorem exists_repr (D : Dat F E) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * D.θ := by
  refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
  have h := D.b.sum_repr x
  rw [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact h.symm

/- English proof (translation)
Use `set φ : F →+* ℂ := w.embedding.comp (algebraMap F E) with hφ`. Use `set φ' : F →+* ℂ := w'.embedding.comp (algebraMap F E) with hφ'`. Establish `hm : InfinitePlace.mk φ = InfinitePlace.mk φ'`. Rewrite using `[hφ, hφ', ← InfinitePlace.comap_mk, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding, h]`. Establish `hreal : ComplexEmbedding.IsReal φ` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)`.

Establish `hc : ComplexEmbedding.conjugate φ = φ` using `ComplexEmbedding.isReal_iff.1 hreal`. Establish `he : φ = φ'`. Break down `InfinitePlace.mk_eq_iff.1 hm with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `hc.symm.trans h1`.

Establish `hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = τ (algebraMap F E D.δ)` using `fun τ => by rw [← map_pow, D.sq]`. Establish `hθ : w'.embedding D.θ ^ 2 = w.embedding D.θ ^ 2`. Rewrite using `[hsq, hsq]`. Conclude with `(congrArg (fun f : F →+* ℂ => f D.δ) he).symm`. Establish `hneg : (starRingEnd ℂ) (w.embedding D.θ) = -w.embedding D.θ`.

Use `conj_of_sq_neg (D.neg hreal.embedding) ?_` and prove the remaining obligations. Rewrite using `[hsq, ComplexEmbedding.IsReal.coe_embedding_apply]`. Both sides reduce to the same expression. Establish `hreal_val : ∀ a : F, (starRingEnd ℂ) (w.embedding (algebraMap F E a)) = w.embedding (algebraMap F E a)` using `fun a => congrArg (fun f : F →+* ℂ => f a) hc`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w']`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hθ with h1 | h1` into its components or cases. Use `congr 1`. Use extensionality with `x`. Take `⟨a, b, rfl⟩` from `exists_repr D x`. Establish `ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c)` using `fun c => (congrArg (fun f : F →+* ℂ => f c) he).symm`.

Simplify using `only [map_add, map_mul, ha, h1]`. Establish `: ComplexEmbedding.conjugate w.embedding = w'.embedding`. Use extensionality with `x`. Take `⟨a, b, rfl⟩` from `exists_repr D x`. Establish `ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c)` using `fun c => (congrArg (fun f : F →+* ℂ => f c) he).symm`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Simplify using `only [map_add, map_mul, ha, h1, hneg, hreal_val]`. Rewrite using `[← this, InfinitePlace.mk_conjugate_eq]`.
-/
private theorem place_unique (D : Dat F E) {w w' : InfinitePlace E}
    (h : w.comap (algebraMap F E) = w'.comap (algebraMap F E)) : w = w' := by
  set φ : F →+* ℂ := w.embedding.comp (algebraMap F E) with hφ
  set φ' : F →+* ℂ := w'.embedding.comp (algebraMap F E) with hφ'
  have hm : InfinitePlace.mk φ = InfinitePlace.mk φ' := by
    rw [hφ, hφ', ← InfinitePlace.comap_mk, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding, h]
  have hreal : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  have hc : ComplexEmbedding.conjugate φ = φ := ComplexEmbedding.isReal_iff.1 hreal
  have he : φ = φ' := by
    rcases InfinitePlace.mk_eq_iff.1 hm with h1 | h1
    · exact h1
    · exact hc.symm.trans h1
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = τ (algebraMap F E D.δ) := fun τ => by rw [← map_pow, D.sq]
  have hθ : w'.embedding D.θ ^ 2 = w.embedding D.θ ^ 2 := by
    rw [hsq, hsq]
    exact (congrArg (fun f : F →+* ℂ => f D.δ) he).symm
  have hneg : (starRingEnd ℂ) (w.embedding D.θ) = -w.embedding D.θ := by
    refine conj_of_sq_neg (D.neg hreal.embedding) ?_
    rw [hsq, ComplexEmbedding.IsReal.coe_embedding_apply]
    rfl
  have hreal_val : ∀ a : F, (starRingEnd ℂ) (w.embedding (algebraMap F E a)) = w.embedding (algebraMap F E a) := fun a =>
    congrArg (fun f : F →+* ℂ => f a) hc
  rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w']
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hθ with h1 | h1
  · congr 1
    ext x
    obtain ⟨a, b, rfl⟩ := exists_repr D x
    have ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c) := fun c =>
      (congrArg (fun f : F →+* ℂ => f c) he).symm
    simp only [map_add, map_mul, ha, h1]
  · have : ComplexEmbedding.conjugate w.embedding = w'.embedding := by
      ext x
      obtain ⟨a, b, rfl⟩ := exists_repr D x
      have ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c) := fun c =>
        (congrArg (fun f : F →+* ℂ => f c) he).symm
      rw [ComplexEmbedding.conjugate_coe_eq]
      simp only [map_add, map_mul, ha, h1, hneg, hreal_val]
    rw [← this, InfinitePlace.mk_conjugate_eq]

end UpperTheory.ConvolutionTheory.R2.Ff.NI

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D s`. Use `haveI : Module.Finite F E := Module.Finite.of_basis D.b`. Establish `hsurj : Function.Surjective fun w : InfinitePlace E => w.comap (algebraMap F E)` using `InfinitePlace.comap_surjective`. Set `val : TR.Rinf F` to `fun v => ∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖s.val w‖ ^ 2 else 1`. Establish `hval : ∀ w : InfinitePlace E, val (w.comap (algebraMap F E)) = ‖s.val w‖ ^ 2` using `fun w => by`.

Use `(Finset.prod_eq_single w (fun w' _ hw => if_neg fun e => hw (NI.place_unique D e)) (fun h => absurd (Finset.mem_univ w) h)).trans (if_pos rfl)` and prove the remaining obligations. Establish `hs : ∀ w, s.val w ≠ 0` using `fun w h => by`. Use `congrFun s.mul_inv w` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, h, zero_mul]`. Conclude with `zero_ne_one this`.

Establish `hne : ∀ v, val v ≠ 0` using `fun v => by`. Take `⟨w, rfl⟩` from `hsurj v`. Rewrite using `[hval]`. Conclude with `pow_ne_zero 2 (norm_ne_zero_iff.2 (hs w))`. Set `u : (TR.Rinf F)ˣ` to `⟨val, fun v => (val v)⁻¹, funext fun v => mul_inv_cancel₀ (hne v), funext fun v => inv_mul_cancel₀ (hne v)⟩`.

Use `⟨u, fun v => rfl, Units.ext (TR.ad_ext ?_ ?_)⟩` and prove the remaining obligations. Establish `h1 : TR.pInf F (TR.infId F u).val = u.val`. Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (1 - TR.infEq F 1 + TR.infEq F u.val) = _`. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Use function extensionality and compare the values at `v`. Take `⟨w, rfl⟩` from `hsurj v`. Express the relevant statement in the definitionally equal form `_ = val _`. Rewrite using `[hval]`. Establish `h` using `NI.pInf_norm D (infId E s) w`.

Rewrite `h` using `[NI.pInf_infId, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Conclude with `h` after adjusting the coercions. Establish `h2 : pFin F (TR.infId F u).val = 1`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules.

Rewrite using `[h2]`. Conclude with `NI.fin_norm D s`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.normInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), NormInf F E := by
  intro F E _ _ _ _ _ _ _ D s
  haveI : Module.Finite F E := Module.Finite.of_basis D.b
  have hsurj : Function.Surjective fun w : InfinitePlace E => w.comap (algebraMap F E) :=
    InfinitePlace.comap_surjective
  let val : TR.Rinf F := fun v => ∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖s.val w‖ ^ 2 else 1
  have hval : ∀ w : InfinitePlace E, val (w.comap (algebraMap F E)) = ‖s.val w‖ ^ 2 := fun w => by
    refine (Finset.prod_eq_single w (fun w' _ hw => if_neg fun e => hw (NI.place_unique D e)) (fun h => absurd (Finset.mem_univ w) h)).trans (if_pos rfl)
  have hs : ∀ w, s.val w ≠ 0 := fun w h => by
    have := congrFun s.mul_inv w
    rw [Pi.mul_apply, h, zero_mul] at this
    exact zero_ne_one this
  have hne : ∀ v, val v ≠ 0 := fun v => by
    obtain ⟨w, rfl⟩ := hsurj v
    rw [hval]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hs w))
  let u : (TR.Rinf F)ˣ := ⟨val, fun v => (val v)⁻¹, funext fun v => mul_inv_cancel₀ (hne v), funext fun v => inv_mul_cancel₀ (hne v)⟩
  refine ⟨u, fun v => rfl, Units.ext (TR.ad_ext ?_ ?_)⟩
  · have h1 : TR.pInf F (TR.infId F u).val = u.val := by
      change (TR.infEq F).symm (1 - TR.infEq F 1 + TR.infEq F u.val) = _
      simp
    rw [h1]
    funext v
    obtain ⟨w, rfl⟩ := hsurj v
    change _ = val _
    rw [hval]
    have h := NI.pInf_norm D (infId E s) w
    rw [NI.pInf_infId, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact_mod_cast h
  · have h2 : pFin F (TR.infId F u).val = 1 := by
      change (1 : Af F) - 0 + 0 = 1
      simp
    rw [h2]
    exact NI.fin_norm D s
