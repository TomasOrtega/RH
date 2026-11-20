import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUniqueStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th IsDedekindDomain NumberField
  Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharInfPlace

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `letI : Algebra F (InfiniteAdeleRing E) := ((algebraMap E (InfiniteAdeleRing E)).comp (algebraMap F E)).toAlgebra`. Set `f : E →ₐ[F] InfiniteAdeleRing E` to `⟨algebraMap E _, fun _ => rfl⟩`. Set `g : Ainf F →ₐ[F] InfiniteAdeleRing E` to `⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E, fun x => congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩`. Conclude with `⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩`.
-/
theorem exists_inf : ∃ Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (InfiniteAdeleRing E) :=
    ((algebraMap E (InfiniteAdeleRing E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] InfiniteAdeleRing E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Ainf F →ₐ[F] InfiniteAdeleRing E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E,
      fun x => congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

/- English proof (translation)
Use `letI : Algebra F (FiniteAdeleRing (𝓞 E) E) := ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra`. Set `f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E` to `⟨algebraMap E _, fun _ => rfl⟩`. Set `g : Af F →ₐ[F] FiniteAdeleRing (𝓞 E) E` to `⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E, fun x => congrArg Prod.snd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩`. Conclude with `⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩`.
-/
theorem exists_fin : ∃ Θ : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Af F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E,
      fun x => congrArg Prod.snd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

variable {F E}

/- English proof (translation)
Set `p : Ainf F ⊗[F] E →+* ℂ` to `(InfinitePlace.Completion.extensionEmbedding w).comp ((Pi.evalRingHom (fun v : InfinitePlace E => v.Completion) w).comp Θ)`. Establish `hp : IsInfEmb w.embedding p`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w (Θ (1 ⊗ₜ[F] x) w) = _`. Rewrite using `[hΘ, map_one, one_mul]`.

Conclude with `InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)`. Establish `: (fun a : Ainf F => p (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a w)`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w (Θ (a ⊗ₜ[F] 1) w) = _`. Rewrite using `[hΘ, map_one, mul_one]`.

Rewrite using `[this]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w)).comp (continuous_apply _))`. Use `(InfinitePlace.Completion.extensionEmbedding w).injective ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p y = p y'`. Break down `InfinitePlace.mk_eq_iff.1 (hw.trans (InfinitePlace.mk_embedding w).symm) with h1 | h1` into its components or cases.

Rewrite `hp` using `[← h1]`. Rewrite using `[GlobalTheory.AutFunCompare.isInfEmb_unique φ p θ hp h]` and apply the resulting hypothesis. Establish `hq : IsInfEmb w.embedding ((starRingEnd ℂ).comp θ)` using `⟨fun x => by rw [← h1, RingHom.comp_apply, h.1]; rfl, Complex.continuous_conj.comp h.2⟩`. Rewrite using `[GlobalTheory.AutFunCompare.isInfEmb_unique _ p _ hp hq, RingHom.comp_apply, RingHom.comp_apply, e]`.
-/
theorem comp_eq [StarRing E] {Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E}
    (hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x)
    {φ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb φ θ) {w : InfinitePlace E}
    (hw : InfinitePlace.mk φ = w) {y y' : Ainf F ⊗[F] E} (e : θ y = θ y') : Θ y w = Θ y' w := by
  let p : Ainf F ⊗[F] E →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace E => v.Completion) w).comp Θ)
  have hp : IsInfEmb w.embedding p := by
    refine ⟨fun x => ?_, ?_⟩
    · change InfinitePlace.Completion.extensionEmbedding w (Θ (1 ⊗ₜ[F] x) w) = _
      rw [hΘ, map_one, one_mul]
      exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    · have : (fun a : Ainf F => p (a ⊗ₜ[F] (1 : E))) = fun a =>
          InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a w) := by
        funext a
        change InfinitePlace.Completion.extensionEmbedding w (Θ (a ⊗ₜ[F] 1) w) = _
        rw [hΘ, map_one, mul_one]
      rw [this]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        ((LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w)).comp
          (continuous_apply _))
  refine (InfinitePlace.Completion.extensionEmbedding w).injective ?_
  change p y = p y'
  rcases InfinitePlace.mk_eq_iff.1 (hw.trans (InfinitePlace.mk_embedding w).symm) with h1 | h1
  · rw [← h1] at hp
    rwa [GlobalTheory.AutFunCompare.isInfEmb_unique φ p θ hp h]
  · have hq : IsInfEmb w.embedding ((starRingEnd ℂ).comp θ) :=
      ⟨fun x => by rw [← h1, RingHom.comp_apply, h.1]; rfl, Complex.continuous_conj.comp h.2⟩
    rw [GlobalTheory.AutFunCompare.isInfEmb_unique _ p _ hp hq, RingHom.comp_apply, RingHom.comp_apply, e]

end General

/- English proof (translation)
Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `hcm` using `H.isCMField_hostE`. Establish `h : IsCMField.complexConj H.E x = H.conj x`. Apply `H.φ₀.injective` to reduce the goal to its premises.

Rewrite using `[IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`. Use `show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)`. Rewrite using `[← h, IsCMField.complexEmbedding_complexConj]`.
-/
theorem conjugate_emb {R : Ranks} (H : Host R) (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 w.embedding`. Establish `e : InfinitePlace.mk (D.host.emb g) = w` using `by rw [hg, InfinitePlace.mk_embedding]`. Distinguish the cases in `h : g ∈ D.R.Psi`. Take `⟨τ, hτ⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D g).2 h`. Conclude with `⟨τ, (congrArg _ hτ.symm).trans e⟩`.

Take `⟨τ, hτ⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 (by_contra fun h' => h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h'))`. Rewrite `hτ` using `[← conjugate_emb]`. Conclude with `⟨τ, (congrArg _ hτ.symm).trans ((InfinitePlace.mk_conjugate_eq _).trans e)⟩`.
-/
theorem exists_mk_tauE (D : D7) (w : InfinitePlace D.host.E) : ∃ τ, InfinitePlace.mk (tauE D τ) = w := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
  have e : InfinitePlace.mk (D.host.emb g) = w := by rw [hg, InfinitePlace.mk_embedding]
  by_cases h : g ∈ D.R.Psi
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 h
    exact ⟨τ, (congrArg _ hτ.symm).trans e⟩
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2
      (by_contra fun h' => h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h'))
    rw [← conjugate_emb] at hτ
    exact ⟨τ, (congrArg _ hτ.symm).trans ((InfinitePlace.mk_conjugate_eq _).trans e)⟩

section Mult

variable {D : D7} {Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E}
  (hΘ : ∀ a x, Θ (a ⊗ₜ[D.host.F] x) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x)

include hΘ

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[hΘ, map_one, one_mul]`.
-/
theorem mult_inc (x : D.host.E) : Θ (incA D x) = algebraMap D.host.E _ x := by
  change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [hΘ, map_one, one_mul]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]`. Both sides reduce to the same expression.

Consider the case `tmul a x => rw [hΘ]`. Conclude with `(hΨ a.1 x).symm`.
-/
theorem mult_fst {Ψ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* InfiniteAdeleRing D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).1 = Ψ (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.1 x).symm

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]`. Both sides reduce to the same expression.

Consider the case `tmul a x => rw [hΘ]`. Conclude with `(hΨ a.2 x).symm`.
-/
theorem mult_snd {Ψ : Af D.host.F ⊗[D.host.F] D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).2 = Ψ (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.2 x).symm

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Take `⟨Ψ, hΨ⟩` from `exists_inf D.host.F D.host.E`. Establish `hfin : ∀ z, (Θ z).2 = Φ z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]`. Both sides reduce to the same expression. Consider the case `tmul a x`. Establish `e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x`.

Express the relevant statement in the definitionally equal form `_ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hΘ, e, RingHom.map_mul, hΦ.inc]`. Use `FiniteAdeleRing.ext _ fun Q => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Φ _ Q * _`.

Rewrite using `[hΦ.base, GlobalTheory.CharTransport.locMap_eq]`. Both sides reduce to the same expression. Take `⟨d0, d1, d2⟩` from `GlobalTheory.CharTransport.isDelta_of_isPlIdem hΦ he`. Establish `hl : Θ (locE D e (k : D.host.E)) = 1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1)` using `(GlobalTheory.CharTransport.map_loc Θ e (incA D (k : D.host.E))).trans (by rw [mult_inc hΘ])`. Rewrite using `[hl]`.

Use `Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `1 + (Θ e).1 * _ = 1`. Rewrite using `[mult_fst hΘ hΨ, d0, RingHom.map_zero, zero_mul, add_zero]`. Express the relevant statement in the definitionally equal form `1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) = Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q`. Rewrite using `[hfin]`.

Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[d1, Function.update_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[d2 Q hQ, Function.update_of_ne hQ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_locE (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D) (he : IsPlIdem D e P) (k : D.host.Eˣ) :
    Θ (locE D e (k : D.host.E)) =
      ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, GlobalTheory.CharTransport.locMap_eq]
      rfl
  obtain ⟨d0, d1, d2⟩ := GlobalTheory.CharTransport.isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (GlobalTheory.CharTransport.map_loc Θ e (incA D (k : D.host.E))).trans (by rw [mult_inc hΘ])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [mult_fst hΘ hΨ, d0, RingHom.map_zero, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `exists_inf D.host.F D.host.E`. Take `⟨Φ, hΦ⟩` from `exists_fin D.host.F D.host.E`. Take `⟨h1, h2, h3⟩` from `hx`. Establish `hpl : InfinitePlace.mk (tauE D τ) = plOf D θ τ` using `congrArg InfinitePlace.mk (RingHom.ext fun y => ((hθ τ).1 y).symm)`. Use `Prod.ext (funext fun w => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(Θ x).1 w = Pi.mulSingle (M := fun w : InfinitePlace D.host.E => w.Completion) (plOf D θ τ) (algebraMap D.host.E (plOf D θ τ).Completion (k : D.host.E)) w`. Rewrite using `[mult_fst hΘ hΨ]`. Distinguish the cases in `hw : w = plOf D θ τ`. Substitute `hw` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, comp_eq hΨ (hθ τ) hpl h3, ← mult_fst hΘ hΨ, mult_inc hΘ]`.

Both sides reduce to the same expression. Take `⟨τ', hτ'⟩` from `exists_mk_tauE D w`. Establish `hne : τ' ≠ τ`. Introduce and unpack `rfl`. Conclude with `hw (hτ'.symm.trans hpl)`.

Rewrite using `[Pi.mulSingle_eq_of_ne hw, comp_eq hΨ (hθ τ') hτ' ((h2 τ' hne).trans (RingHom.map_one _).symm), RingHom.map_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(Θ x).2 = 1`. Rewrite using `[mult_snd hΘ hΦ, h1, RingHom.map_one]`.
-/
theorem mult_infLoc {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam (D := D) θ)
    (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : AE D) (hx : IsInfLoc D θ τ (k : D.host.E) x) :
    Θ x = ((infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) : Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := exists_fin D.host.F D.host.E
  obtain ⟨h1, h2, h3⟩ := hx
  have hpl : InfinitePlace.mk (tauE D τ) = plOf D θ τ :=
    congrArg InfinitePlace.mk (RingHom.ext fun y => ((hθ τ).1 y).symm)
  refine Prod.ext (funext fun w => ?_) ?_
  · change (Θ x).1 w = Pi.mulSingle (M := fun w : InfinitePlace D.host.E => w.Completion) (plOf D θ τ)
      (algebraMap D.host.E (plOf D θ τ).Completion (k : D.host.E)) w
    rw [mult_fst hΘ hΨ]
    by_cases hw : w = plOf D θ τ
    · subst hw
      rw [Pi.mulSingle_eq_same, comp_eq hΨ (hθ τ) hpl h3, ← mult_fst hΘ hΨ, mult_inc hΘ]
      rfl
    · obtain ⟨τ', hτ'⟩ := exists_mk_tauE D w
      have hne : τ' ≠ τ := by
        rintro rfl
        exact hw (hτ'.symm.trans hpl)
      rw [Pi.mulSingle_eq_of_ne hw, comp_eq hΨ (hθ τ') hτ' ((h2 τ' hne).trans (RingHom.map_one _).symm),
        RingHom.map_one]
      rfl
  · change (Θ x).2 = 1
    rw [mult_snd hΘ hΦ, h1, RingHom.map_one]

end Mult

/- English proof (translation)
Introduce `D c χ hcχ θ hθ τ k x hx`. Establish `hχ : χ.IsUnitary` using `(GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.2 c χ hcχ`. Take `⟨Θ, hc, hΘ⟩` from `GlobalTheory.CharTransport.exists_toAdele D.host.F D.host.E`. Set `u : (AE D)ˣ →* Ideles D.host.E` to `Units.map Θ.toMonoidHom`. Establish `hu : Continuous u` using `Continuous.units_map _ hc`.

Set `c' : (AE D)ˣ →* Circle` to `{ toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩ map_one' := Circle.ext (by simp) map_mul' := fun x y => Circle.ext (by`. Express the relevant statement in the definitionally equal form `((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)`. Rewrite using `[map_mul, map_mul, Units.val_mul]) }`. Establish `hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ)` using `fun x => rfl`. Establish `h' : ChrEq c' χ`.

Use `⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _`. Establish `: u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x` using `Units.ext (mult_inc hΘ x)`. Rewrite using `[hcoe, this, χ.2.2]`. Both sides reduce to the same expression.

Establish `: u x = localIdele D.host.E P (atFin P k)`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Θ (x : AE D) = _`. Rewrite using `[hx, mult_locE hΘ P e he]`. Rewrite using `[hcoe, this]`.

Both sides reduce to the same expression. Establish `: u x = infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k)` using `Units.ext (mult_infLoc hΘ hθ τ k x hx)`. Rewrite using `[(GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.1 c c' χ hcχ h', hcoe, this]`. Both sides reduce to the same expression.
-/
theorem chrEq_infLoc : ∀ (D : D7) (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ →
    ∀ θ, IsInfFam (D := D) θ → ∀ (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : (AE D)ˣ),
      Formalism.L2.JoinChr.IsInfLoc D θ τ (k : D.host.E) (x : AE D) → ((c x : Circle) : ℂ) =
        ((χ.locInf (Formalism.L2.JoinChr.plOf D θ τ) (Formalism.L2.Host.atInf (Formalism.L2.JoinChr.plOf D θ τ) k) : ℂˣ) : ℂ) := by
  intro D c χ hcχ θ hθ τ k x hx
  have hχ : χ.IsUnitary := (GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.2 c χ hcχ
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele D.host.F D.host.E
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (mult_inc hΘ x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, mult_locE hΘ P e he]
      rw [hcoe, this]
      rfl
  have : u x = infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) :=
    Units.ext (mult_infLoc hΘ hθ τ k x hx)
  rw [(GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.1 c c' χ hcχ h', hcoe, this]
  rfl

end GlobalTheory.CharInfPlace
