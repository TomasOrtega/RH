import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ArchSignChar

def nrm : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)))
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nrm_val (z : ℂˣ) : ((nrm z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

/- English proof (translation)
Rewrite using `[nrm_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]`.
-/
theorem norm_nrm (z : ℂˣ) : ‖((nrm z : ℂˣ) : ℂ)‖ = 1 := by
  rw [nrm_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

/- English proof (translation)
Establish `h0 : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)`. Establish `hc : Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)` using `Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) h0`. Use `Units.continuous_iff.2 ⟨hc, ?_⟩` and prove the remaining obligations. Conclude with `hc.inv₀ fun z => div_ne_zero z.ne_zero (h0 z)`.
-/
theorem continuous_nrm : Continuous nrm := by
  have h0 : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)
  have hc : Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) h0
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  exact hc.inv₀ fun z => div_ne_zero z.ne_zero (h0 z)

def normChar {R : Type} [CommRing R] (θ : R →+* ℂ) : Rˣ →* Circle :=
  GlobalTheory.unitaryCharToCircle (nrm.comp (Units.map θ.toMonoidHom)) fun _ => norm_nrm _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normChar_val {R : Type} [CommRing R] (θ : R →+* ℂ) (x : Rˣ) :
    ((normChar θ x : Circle) : ℂ) = θ x / ((‖θ x‖ : ℝ) : ℂ) := rfl

/- English proof (translation)
The claim follows from `Continuous.subtype_mk (Units.continuous_val.comp (continuous_nrm.comp (Continuous.units_map _ hθ))) _`.
-/
theorem continuous_normChar {R : Type} [CommRing R] [TopologicalSpace R] (θ : R →+* ℂ) (hθ : Continuous θ) :
    Continuous (normChar θ) :=
  Continuous.subtype_mk (Units.continuous_val.comp (continuous_nrm.comp (Continuous.units_map _ hθ))) _

/- English proof (translation)
Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Use `split_ifs with h`. Rewrite using `[abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]`. Rewrite using `[abs_of_pos (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)), div_self (Complex.ofReal_ne_zero.2 hr)]`.
-/
theorem ofReal_div_norm (r : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ)) = if r < 0 then -1 else 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
  · rw [abs_of_pos (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)), div_self (Complex.ofReal_ne_zero.2 hr)]

/- English proof (translation)
Establish `h3 : (z : ℂ) * z = 1` using `by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h`. Break down `mul_self_eq_one_iff.1 h3 with h4 | h4` into its components or cases. Conclude with `Or.inl (Circle.ext h4)`. Conclude with `Or.inr (Circle.ext (by rw [h4]; simp))`.
-/
theorem sq_eq_one (z : Circle) (h : z * z = 1) : z = 1 ∨ z = -1 := by
  have h3 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact Or.inl (Circle.ext h4)
  · exact Or.inr (Circle.ext (by rw [h4]; simp))

/- English proof (translation)
Use `letI : Algebra F ℂ := w.embedding.toAlgebra`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Set `τ : E →ₐ[F] ℂ` to `IsAlgClosed.lift`. Set `g0 : AF F →+* ℂ` to `(InfinitePlace.Completion.extensionEmbedding w).comp ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))`. Set `g : AF F →ₐ[F] ℂ` to `⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩`.

Set `θ : AF F ⊗[F] E →+* ℂ` to `(Algebra.TensorProduct.productMap g τ).toRingHom`. Establish `hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x` using `fun a x => rfl`. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Use `⟨θ, ?_, fun a => ?_⟩` and prove the remaining obligations. Use `IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_` and prove the remaining obligations.

Establish `: Continuous g0` using `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`. Use `this.congr fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = θ (a ⊗ₜ[F] 1)`. Rewrite using `[hθ, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `θ (a ⊗ₜ[F] 1) = _`.

Rewrite using `[hθ, map_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem exists_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) : ∃ θ : AF F ⊗[F] E →+* ℂ, Continuous θ ∧
      ∀ a : AF F, θ (algebraMap (AF F) (AF F ⊗[F] E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AF F ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine ⟨θ, ?_, fun a => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (a ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]; rfl

def archIdele (F : Type) [Field F] [NumberField F] : ((w : InfinitePlace F) → (w.Completion)ˣ) →* (AF F)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.toMonoidHom)

def archPart {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) : (w : InfinitePlace F) → (w.Completion)ˣ :=
  MulEquiv.piUnits (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F) b).1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `Prod.ext rfl ?_` and prove the remaining obligations. Conclude with `hb`.
-/
theorem eq_archIdele {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) :
    b = archIdele F (archPart b) := by
  apply Units.ext
  refine Prod.ext rfl ?_
  exact hb

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

/- English proof (translation)
Use `set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he`. Establish `ht : e (t : w.Completion) ≠ 0` using `(map_ne_zero e).2 t.ne_zero`. Use `split_ifs with h`. Establish `hpos : 0 < -e t` using `neg_pos.2 h`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = -1 * (s * s) := by`.

Establish `hs0 : e.symm (Real.sqrt (-e t)) ≠ 0` using `(map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)`. Use `⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩` and prove the remaining obligations. Simplify using `only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, map_mul, map_neg, map_one, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, map_mul, hχ, mul_one]`.

Establish `hpos : 0 < e t` using `lt_of_le_of_ne (not_lt.1 h) (Ne.symm ht)`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = s * s := by`. Establish `hs0 : e.symm (Real.sqrt (e t)) ≠ 0` using `(map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)`. Use `⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩` and prove the remaining obligations. Simplify using `only [Units.val_mul, Units.val_mk0, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]`.

Rewrite using `[hs, hχ]`.
-/
theorem local_sign {K : Type} [Field K] {w : InfinitePlace K} (hw : w.IsReal) (χ : (w.Completion)ˣ →* Circle)
    (hχ : ∀ s, χ (s * s) = 1) (t : (w.Completion)ˣ) :
    χ t = if InfinitePlace.Completion.ringEquivRealOfIsReal hw (t : w.Completion) < 0 then χ (-1) else 1 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  have ht : e (t : w.Completion) ≠ 0 := (map_ne_zero e).2 t.ne_zero
  split_ifs with h
  · have hpos : 0 < -e t := neg_pos.2 h
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = -1 * (s * s) := by
      have hs0 : e.symm (Real.sqrt (-e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, map_mul, map_neg, map_one,
        RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
      ring
    rw [hs, map_mul, hχ, mul_one]
  · have hpos : 0 < e t := lt_of_le_of_ne (not_lt.1 h) (Ne.symm ht)
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = s * s := by
      have hs0 : e.symm (Real.sqrt (e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_mk0, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
    rw [hs, hχ]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `η (archIdele F (Pi.mulSingle w (s * s))) = 1`. Rewrite using `[Pi.mulSingle_mul, map_mul]`. Conclude with `hsq _) (archPart b w)`.
-/
theorem eta_eq_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (η : (AF F)ˣ →* Circle)
    (hsq : ∀ b, η (b * b) = 1) (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) [DecidableEq (InfinitePlace F)] :
    η b = ∏ w, if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0
      then η (archIdele F (Pi.mulSingle w (-1))) else 1 := by
  calc η b = η (archIdele F (archPart b)) := congrArg η (eq_archIdele b hb)
    _ = η (archIdele F (∏ w, Pi.mulSingle w (archPart b w))) := by rw [Finset.univ_prod_mulSingle]
    _ = ∏ w, η (archIdele F (Pi.mulSingle w (archPart b w))) := by rw [map_prod, map_prod]
    _ = _ := Finset.prod_congr rfl fun w _ =>
      local_sign (IsTotallyReal.isReal w) ((η.comp (archIdele F)).comp (MonoidHom.mulSingle (fun u : InfinitePlace F => (u.Completion)ˣ) w))
        (fun s => by
          change η (archIdele F (Pi.mulSingle w (s * s))) = 1
          rw [Pi.mulSingle_mul, map_mul]
          exact hsq _) (archPart b w)

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm η _ hsq`. Use `haveI : IsTotallyReal F := hcm.1`. Use `choose θ hθc hθ using fun w : InfinitePlace F => exists_coord (F := F) (E := E) w`. Set `c : InfinitePlace F → Circle` to `fun w => η (archIdele F (Pi.mulSingle w (-1)))`. Set `g : InfinitePlace F → ((AF F ⊗[F] E)ˣ →* Circle)` to `fun w => if c w = 1 then 1 else normChar (θ w)`.

Establish `hval : ∀ w b, normChar (θ w) (ideleMap F E b) = if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0 then -1 else 1`. Introduce `w b`. Establish `hne : (b : AF F).1 w ≠ 0` using `(archPart b w).ne_zero`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[normChar_val]`.

Establish `e1 : θ w ((ideleMap F E b : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) : ℝ) : ℂ)`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]`. Conclude with `hθ w b`. Rewrite using `[e1, ofReal_div_norm _ ((map_ne_zero _).2 hne)]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hgc : ∀ w, Continuous (g w)` using `fun w => by`. Distinguish the cases in `h : c w = 1`. Simplify using `only [g, h, if_true]`. Conclude with `continuous_const`. Simplify using `only [g, h, if_false]`.

Conclude with `continuous_normChar _ (hθc w)`. Establish `happ : ∀ x, (∏ w, g w) x = ∏ w, g w x` using `fun x => MonoidHom.finset_prod_apply _ _ _`. Establish `hc2 : ∀ w, c w = 1 ∨ c w = -1` using `fun w => sq_eq_one _ (by simp only [c]; rw [← map_mul]; exact hsq _)`. Use `⟨∏ w, g w, ?_, fun b => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Establish `: ⇑(∏ w, g w) = fun x => ∏ w, g w x` using `funext happ`.

Rewrite using `[this]`. Conclude with `continuous_finset_prod _ fun w _ => hgc w`. Apply `sq_eq_one` to reduce the goal to its premises. Rewrite using `[happ, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : c w = 1`. Simplify using `only [g, h, if_true, MonoidHom.one_apply, mul_one]`. Simplify using `only [g, h, if_false]`. Apply the tactic sequence `rw [hval]; split_ifs <;> simp`. Rewrite using `[happ, eta_eq_prod η hsq b hb]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : c w = 1`. Simplify using `only [g, h, if_true, MonoidHom.one_apply]`. Express the relevant statement in the definitionally equal form `1 = if _ then c w else 1`. Apply the tactic sequence `rw [h]; split_ifs <;> rfl`.

Establish `h' : c w = -1` using `(hc2 w).resolve_left h`. Simplify using `only [g, h, if_false]`. Rewrite using `[hval]`. Express the relevant statement in the definitionally equal form `_ = if _ then c w else 1`. Rewrite using `[h']`.
-/
theorem exists_arch_sign_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  intro F E _ _ _ _ _ σ hcm η _ hsq
  classical
  haveI : IsTotallyReal F := hcm.1
  choose θ hθc hθ using fun w : InfinitePlace F => exists_coord (F := F) (E := E) w
  let c : InfinitePlace F → Circle := fun w => η (archIdele F (Pi.mulSingle w (-1)))
  let g : InfinitePlace F → ((AF F ⊗[F] E)ˣ →* Circle) := fun w => if c w = 1 then 1 else normChar (θ w)
  have hval : ∀ w b, normChar (θ w) (ideleMap F E b) =
      if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0 then -1 else 1 := by
    intro w b
    have hne : (b : AF F).1 w ≠ 0 := (archPart b w).ne_zero
    apply Circle.ext
    rw [normChar_val]
    have e1 : θ w ((ideleMap F E b : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) : ℝ) : ℂ) := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      exact hθ w b
    rw [e1, ofReal_div_norm _ ((map_ne_zero _).2 hne)]
    split_ifs <;> simp
  have hgc : ∀ w, Continuous (g w) := fun w => by
    by_cases h : c w = 1
    · simp only [g, h, if_true]; exact continuous_const
    · simp only [g, h, if_false]; exact continuous_normChar _ (hθc w)
  have happ : ∀ x, (∏ w, g w) x = ∏ w, g w x := fun x => MonoidHom.finset_prod_apply _ _ _
  have hc2 : ∀ w, c w = 1 ∨ c w = -1 := fun w => sq_eq_one _ (by simp only [c]; rw [← map_mul]; exact hsq _)
  refine ⟨∏ w, g w, ?_, fun b => ?_, fun b hb => ?_⟩
  · have : ⇑(∏ w, g w) = fun x => ∏ w, g w x := funext happ
    rw [this]; exact continuous_finset_prod _ fun w _ => hgc w
  · apply sq_eq_one
    rw [happ, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply, mul_one]
    · simp only [g, h, if_false]
      rw [hval]; split_ifs <;> simp
  · rw [happ, eta_eq_prod η hsq b hb]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply]
      change 1 = if _ then c w else 1
      rw [h]; split_ifs <;> rfl
    · have h' : c w = -1 := (hc2 w).resolve_left h
      simp only [g, h, if_false]
      rw [hval]
      change _ = if _ then c w else 1
      rw [h']

end GlobalTheory.ArchSignChar
