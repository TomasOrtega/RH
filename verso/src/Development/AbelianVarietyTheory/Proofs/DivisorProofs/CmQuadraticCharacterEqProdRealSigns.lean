import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.EtaSignReal

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, h1, h3, h4⟩` from `hη`. Use `eq_signToCircle_comp _ η (fun a ha => ?_) h4` and prove the remaining obligations. Take `⟨t, x, hx⟩` from `(normSign_eq_one_iff E a).1 ha`. Rewrite using `[← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]`. Conclude with `h1 t`.
-/
theorem eq_signToCircle [Algebra.IsQuadraticExtension F E] (η : (AF F)ˣ →* Circle) (hη : IsEtaF E η) :
    η = signToCircle.comp (normSign E) := by
  obtain ⟨-, h1, h3, h4⟩ := hη
  refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
  obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
  exact h1 t

/- English proof (translation)
Establish `h` using `ha ((0 : Ainf F), (1 : Af F)) (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _)`. Establish `h2 : ((a : AF F) - 1).2 = 0`. Use `congrArg Prod.snd h` as an intermediate fact. Express the relevant statement in the definitionally equal form `(1 : Af F) * ((a : AF F) - 1).2 = 0 at this`.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `h3 : (a : AF F).2 = 1` using `sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)`. Use function extensionality and compare the values at `v`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(a : AF F).2 v = 1`.

Rewrite using `[h3]`. Both sides reduce to the same expression.
-/
theorem finComp_eq_one {a : (AF F)ˣ} (ha : At (evI F) ((a : AF F) - 1)) : finComp a = 1 := by
  have h := ha ((0 : Ainf F), (1 : Af F)) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : ((a : AF F) - 1).2 = 0 := by
    have := congrArg Prod.snd h
    change (1 : Af F) * ((a : AF F) - 1).2 = 0 at this
    rwa [one_mul] at this
  have h3 : (a : AF F).2 = 1 := sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)
  funext v
  apply Units.ext
  change (a : AF F).2 v = 1
  rw [h3]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `etaProd F E (finComp a) (infComp a) = _`. Rewrite using `[etaProd, ha]`. Establish `: ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1` using `fun v => eta_eq_one_iff.2 (one_mem _)`. Simplify using `only [this, finprod_one, one_mul]`.
-/
theorem normSign_eq_prod [Algebra.IsQuadraticExtension F E] {a : (AF F)ˣ} (ha : finComp a = 1) :
    normSign E a = ∏ w : InfinitePlace F, eta F E w.Completion (infComp a w) := by
  change etaProd F E (finComp a) (infComp a) = _
  rw [etaProd, ha]
  have : ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1 :=
    fun v => eta_eq_one_iff.2 (one_mem _)
  simp only [this, finprod_one, one_mul]

/- English proof (translation)
Use `set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Use `set z := τ.1 θ`. Establish `hz : star z = -z` using `by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]`. Establish `hre : z.re = 0`. Use `congrArg Complex.re hz` as an intermediate fact.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]`. Establish `h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ` using `InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm δ)`.

Rewrite using `[h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]`. Establish `hr` using `congrArg Complex.re hc`. Simplify using `only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr`. Establish `hne : e (algebraMap F w.Completion δ) ≠ 0` using `(map_ne_zero e).2 ((map_ne_zero _).2 hδ)`. Use `lt_of_le_of_ne ?_ hne` and prove the remaining obligations.

Rewrite using `[hr]`. Use polynomial arithmetic with `[mul_self_nonneg z.im]`.
-/
theorem ringEquivReal_neg {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) {δ : F} (hδ : δ ≠ 0) {θ : E} (hθ : σ θ = -θ) (h1 : θ * θ = algebraMap F E δ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion δ) < 0 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set z := τ.1 θ
  have hz : star z = -z := by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]
  have hre : z.re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ :=
      InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm δ)
    rw [h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr
  have hne : e (algebraMap F w.Completion δ) ≠ 0 := (map_ne_zero e).2 ((map_ne_zero _).2 hδ)
  refine lt_of_le_of_ne ?_ hne
  rw [hr]
  nlinarith [mul_self_nonneg z.im]

/- English proof (translation)
Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])`. Establish `hne : ∃ x, σ x ≠ x`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `haveI := hcm.2.1`.

Use `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1))) (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))` and prove the remaining obligations. Conclude with `(hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])`. Take `⟨δ, b, hδ, h0, hσb, h1⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne`. Establish `hδ0 : δ ≠ 0` using `fun h => hδ (h ▸ IsSquare.zero)`. Establish `hneg` using `ringEquivReal_neg hcm hw τ hδ0 hσb h1`.

Use `set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Rewrite using `[mem_normGroup_iff_form b h0 h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, h⟩`. Establish `hx0 : e (x : w.Completion) ≠ 0` using `(map_ne_zero e).2 x.ne_zero`.

Establish `h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2`. Rewrite using `[h, map_sub, map_mul, map_pow, map_pow]`. Use `lt_of_le_of_ne ?_ hx0.symm` and prove the remaining obligations. Rewrite using `[h2]`. Use polynomial arithmetic with `[sq_nonneg (e p), sq_nonneg (e q)]`.

Introduce `hpos`. Use `⟨e.symm (Real.sqrt (e x)), 0, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Simplify using `[Real.sq_sqrt hpos.le]`.
-/
theorem mem_normGroup_iff_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) (x : (w.Completion)ˣ) :
    x ∈ normGroup F E w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    haveI := hcm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])
  obtain ⟨δ, b, hδ, h0, hσb, h1⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg := ringEquivReal_neg hcm hw τ hδ0 hσb h1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨p, q, h⟩
    have hx0 : e (x : w.Completion) ≠ 0 := (map_ne_zero e).2 x.ne_zero
    have h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2 := by
      rw [h, map_sub, map_mul, map_pow, map_pow]
    refine lt_of_le_of_ne ?_ hx0.symm
    rw [h2]
    nlinarith [sq_nonneg (e p), sq_nonneg (e q)]
  · intro hpos
    refine ⟨e.symm (Real.sqrt (e x)), 0, ?_⟩
    apply e.injective
    simp [Real.sq_sqrt hpos.le]

/- English proof (translation)
Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]`. Express the relevant statement in the definitionally equal form `infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]`. Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _`. Rewrite using `[infEmb_tmul, map_one, mul_one]`.

Both sides reduce to the same expression.
-/
theorem piInf_idFF {w : InfinitePlace F} (hw : w.IsReal) (τ : EmbOver E w) (a : (AF F)ˣ) :
    piInf τ ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion) : ℝ) : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  change infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB η hη a ha`. Establish `hcm` using `hB.cm`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩`. Use `haveI := hcm.1`. Rewrite using `[eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]`.

Rewrite using `[show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) = ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from map_prod Circle.coeHom _ _]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`. Rewrite using `[piInf_idFF hw]`. Use `set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)`.

Establish `hx` using `mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)`. Establish `hr0 : r ≠ 0` using `(map_ne_zero _).2 (infComp a w).ne_zero`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Distinguish the cases in `hpos : 0 < r`. Rewrite using `[eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]`.

Both sides reduce to the same expression. Establish `hneg : r < 0` using `lt_of_le_of_ne (not_lt.1 hpos) hr0`. Rewrite using `[eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]`. Express the relevant statement in the definitionally equal form `((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _`. Rewrite using `[if_neg (by decide)]`.

Use `push_cast`. Rewrite using `[div_neg, div_self (by exact_mod_cast hr0)]`.
-/
theorem eta_eq_prod_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]

end GlobalTheory.EtaSignReal
