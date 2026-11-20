import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis

open scoped TensorProduct NumberField.AdeleRing NumberField.LiesOver
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.RgEis GroundTheory.Automorphic.Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `conv_rhs => rw [← w.mk_embedding, InfinitePlace.comap_mk]`. Conclude with `(InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm`.
-/
theorem embedding_comp [IsTotallyReal F] (w : InfinitePlace E) :
    w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
  conv_rhs => rw [← w.mk_embedding, InfinitePlace.comap_mk]
  exact (InfinitePlace.embedding_mk_eq_of_isReal
    (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm

def embOf [IsTotallyReal F] (w : InfinitePlace E) : EmbOver E (w.comap (algebraMap F E)) :=
  ⟨w.embedding, embedding_comp w⟩

/- English proof (translation)
Establish `hr : w.IsReal` using `IsTotallyReal.isReal w`. Rewrite using `[← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr, Complex.conj_ofReal]`.
-/
theorem conj_ext [IsTotallyReal F] (w : InfinitePlace F) (a : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w a) =
      InfinitePlace.Completion.extensionEmbedding w a := by
  have hr : w.IsReal := IsTotallyReal.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr, Complex.conj_ofReal]

/- English proof (translation)
Establish `c1 : Continuous fun a : (w.comap (algebraMap F E)).Completion => InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a)` using `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (NumberField.LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w))`. Establish `c2` using `(InfinitePlace.Completion.isometry_extensionEmbedding (w.comap (algebraMap F E))).continuous`. Use `congrFun ((InfinitePlace.Completion.denseRange_coe (w.comap (algebraMap F E))).equalizer c1 c2 (funext fun x => ?_)) a` and prove the remaining obligations. Take `⟨k, rfl⟩` from `(WithAbs.equiv (w.comap (algebraMap F E)).1).symm.surjective x`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion (algebraMap F (w.comap (algebraMap F E)).Completion k)) = InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (algebraMap F (w.comap (algebraMap F E)).Completion k)`.

Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E]`. Establish `e1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion (algebraMap F E k)) = w.embedding (algebraMap F E k)` using `InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm (algebraMap F E k))`. Establish `e2 : InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (algebraMap F (w.comap (algebraMap F E)).Completion k) = (w.comap (algebraMap F E)).embedding k` using `InfinitePlace.Completion.extensionEmbedding_coe _ ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k)`. Rewrite using `[e1, e2]`. Conclude with `RingHom.congr_fun (embedding_comp w) k`.
-/
theorem ext_algebraMap [IsTotallyReal F] (w : InfinitePlace E) (a : (w.comap (algebraMap F E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) a := by
  have c1 : Continuous fun a : (w.comap (algebraMap F E)).Completion =>
      InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (NumberField.LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w))
  have c2 := (InfinitePlace.Completion.isometry_extensionEmbedding (w.comap (algebraMap F E))).continuous
  refine congrFun ((InfinitePlace.Completion.denseRange_coe (w.comap (algebraMap F E))).equalizer c1 c2
    (funext fun x => ?_)) a
  obtain ⟨k, rfl⟩ := (WithAbs.equiv (w.comap (algebraMap F E)).1).symm.surjective x
  change InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion
      (algebraMap F (w.comap (algebraMap F E)).Completion k)) =
    InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k)
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E]
  have e1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion (algebraMap F E k)) =
      w.embedding (algebraMap F E k) :=
    InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm (algebraMap F E k))
  have e2 : InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k) = (w.comap (algebraMap F E)).embedding k :=
    InfinitePlace.Completion.extensionEmbedding_coe _ ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k)
  rw [e1, e2]
  exact RingHom.congr_fun (embedding_comp w) k

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x`. Establish `e : eqv F E (a ⊗ₜ x) = algebraMap E 𝔸[E] x * GroundTheory.Global.AdeleBaseChange.adeleMap F E a` using `GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul a x`.

Rewrite using `[e, map_mul]`. Express the relevant statement in the definitionally equal form `_ * InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion (a.1 (w.comap (algebraMap F E)))) = InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (a.1 (w.comap (algebraMap F E))) * w.embedding x`. Rewrite using `[ext_algebraMap, mul_comm]`. Use `congr 1`. Conclude with `InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)`.
-/
theorem phi_eqv [IsTotallyReal F] (w : InfinitePlace E) (z : AE F E) :
    (adStd E).φ w (eqv F E z) = piInf (embOf w) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    have e : eqv F E (a ⊗ₜ x) = algebraMap E 𝔸[E] x * GroundTheory.Global.AdeleBaseChange.adeleMap F E a :=
      GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul a x
    rw [e, map_mul]
    change _ * InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion (a.1 (w.comap (algebraMap F E)))) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (a.1 (w.comap (algebraMap F E))) * w.embedding x
    rw [ext_algebraMap, mul_comm]
    congr 1
    exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ x) = starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x)`.

Rewrite using `[map_mul, conj_ext, h.2.2.2]`. Both sides reduce to the same expression.
-/
theorem piInf_cA [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : piInf τ (cA σ z) = starRingEnd ℂ (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x)
    rw [map_mul, conj_ext, h.2.2.2]
    rfl

/- English proof (translation)
Substitute `hv` using the available equality. Break down `infEmb_eq_or_conj h (embOf w') τ with e | e` into its components or cases. Use `Or.inl fun z => ?_` and prove the remaining obligations. Rewrite using `[phi_eqv]`. Conclude with `RingHom.congr_fun e (compInf F E _ z)`.

Use `Or.inr fun z => ?_` and prove the remaining obligations. Rewrite using `[phi_eqv]`. Conclude with `RingHom.congr_fun e (compInf F E _ z)`.
-/
theorem place_cases [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w' : InfinitePlace E)
    {w : InfinitePlace F} (hv : w'.comap (algebraMap F E) = w) (τ : EmbOver E w) :
    (∀ z, piInf τ z = (adStd E).φ w' (eqv F E z)) ∨
      ∀ z, piInf τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z)) := by
  subst hv
  rcases infEmb_eq_or_conj h (embOf w') τ with e | e
  · refine Or.inl fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)
  · refine Or.inr fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h`. Use `h.1` as an intermediate fact. Use `⟨fun w z => ?_, fun τ => ⟨fun w => ?_, fun w' => ⟨w'.comap (algebraMap F E), place_cases h w' rfl _⟩⟩⟩` and prove the remaining obligations. Rewrite using `[phi_eqv, phi_eqv]`. Conclude with `piInf_cA h _ z`.

Use `⟨InfinitePlace.mk (τ w).1, place_cases h _ ?_ (τ w)⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.comap_mk, (τ w).2, InfinitePlace.mk_embedding]`.
-/
theorem dictInf : DictInf := by
  intro F E _ _ _ _ _ σ h
  have := h.1
  refine ⟨fun w z => ?_, fun τ => ⟨fun w => ?_, fun w' => ⟨w'.comap (algebraMap F E), place_cases h w' rfl _⟩⟩⟩
  · rw [phi_eqv, phi_eqv]
    exact piInf_cA h _ z
  · refine ⟨InfinitePlace.mk (τ w).1, place_cases h _ ?_ (τ w)⟩
    rw [InfinitePlace.comap_mk, (τ w).2, InfinitePlace.mk_embedding]

end GlobalTheory.CompanionTheory.RgEis
