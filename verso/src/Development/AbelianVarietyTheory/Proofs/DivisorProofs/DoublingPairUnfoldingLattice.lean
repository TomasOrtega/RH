import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDerivativeExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblPolArch

open scoped Classical
open GlobalTheory.HeisDer GlobalTheory.RealLift GlobalTheory.ThK.PlaneEv

section Gen

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Dop (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) a -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((trL b x : ℝ) : ℂ))

/- English proof (translation)
Establish `htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((trL b x : ℝ) : ℂ)` using `(Complex.ofRealCLM.comp (trL b)).hasTemperateGrowth`. Simplify using `only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]`. Simplify using `only [trL_apply, dotProduct, dH]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dop_apply (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    Dop a b f x = dH a b f x := by
  have htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((trL b x : ℝ) : ℂ) :=
    (Complex.ofRealCLM.comp (trL b)).hasTemperateGrowth
  simp only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sub_apply,
    SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
  simp only [trL_apply, dotProduct, dH]
  ring

/- English proof (translation)
Introduce `g hg l hl`. Take `⟨T, hT⟩` from `hl g hg`. Set `d : Darboux (fun w w' : (κ → AF F) × (κ → AF F) => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ` to `⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩`. Establish `h` using `hasDerivAt_heis (fun i => evI F (w.1 i)) (trL (fun i => evI F (w.2 i))) (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evI F (w.1 i)) ⬝ᵥ (fun i => evI F (w.2 i)))) f T`. Rewrite using `[hT]`.

Use `(h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]`. Use `rho_pureA d ψ hψ w t f g` as an intermediate fact. Express the relevant statement in the definitionally equal form `l (d.rho ψ (realAd F t • w) (pureA F f g)) = _`. Rewrite using `[this, hT]`.

Both sides reduce to the same expression.
-/
theorem sd_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) :
    SD (fun t => schr ψ (realAd F t • w)) f (Dop (fun i => evI F (w.1 i)) (fun i => evI F (w.2 i)) f) := by
  intro g hg l hl
  obtain ⟨T, hT⟩ := hl g hg
  let d : Darboux (fun w w' : (κ → AF F) × (κ → AF F) => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  have h := hasDerivAt_heis (fun i => evI F (w.1 i)) (trL (fun i => evI F (w.2 i)))
    (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evI F (w.1 i)) ⬝ᵥ (fun i => evI F (w.2 i)))) f T
  rw [hT]
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  · have := rho_pureA d ψ hψ w t f g
    change l (d.rho ψ (realAd F t • w) (pureA F f g)) = _
    rw [this, hT]
    rfl

def bx (f₁ f₂ : SInf F κ) : SInf F (κ ⊕ κ) :=
  (GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (GlobalTheory.ConjSch.conjSchwartz f₂)).choose

/- English proof (translation)
The claim follows from `(GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (GlobalTheory.ConjSch.conjSchwartz f₂)).choose_spec x`.
-/
theorem bx_apply (f₁ f₂ : SInf F κ) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    bx f₁ f₂ x = f₁ (x ∘ Sum.inl) * starRingEnd ℂ (f₂ (x ∘ Sum.inr)) :=
  (GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (GlobalTheory.ConjSch.conjSchwartz f₂)).choose_spec x

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SchwartzMap.add_apply, bx_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bx_add_left (f f' g : SInf F κ) : bx (f + f') g = bx f g + bx f' g := by
  ext x; simp only [SchwartzMap.add_apply, bx_apply]; ring

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bx_smul_left (c : ℂ) (f g : SInf F κ) : bx (c • f) g = c • bx f g := by
  ext x; simp only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul]; ring

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SchwartzMap.add_apply, bx_apply, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bx_add_right (f g g' : SInf F κ) : bx f (g + g') = bx f g + bx f g' := by
  ext x; simp only [SchwartzMap.add_apply, bx_apply, map_add]; ring

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bx_smul_right (c : ℂ) (f g : SInf F κ) : bx f (c • g) = starRingEnd ℂ c • bx f g := by
  ext x; simp only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul, map_mul]; ring

/- English proof (translation)
Use extensionality with `x`. Simplify using `[bx_apply]`.
-/
theorem bx_zero_left (g : SInf F κ) : bx 0 g = 0 := by
  ext x; simp [bx_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[bx_apply]`.
-/
theorem bx_zero_right (f : SInf F κ) : bx f 0 = 0 := by
  ext x; simp [bx_apply]

/- English proof (translation)
The claim follows from `HasFDerivAt.comp (g := f) (f := GlobalTheory.SchwartzBox.restr V e) x f.differentiableAt.hasFDerivAt (GlobalTheory.SchwartzBox.restr V e).hasFDerivAt`.
-/
theorem hasFDerivAt_restr {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (x : ι → V) :
    HasFDerivAt (fun y : ι → V => f (y ∘ e)) ((fderiv ℝ f (x ∘ e)).comp (GlobalTheory.SchwartzBox.restr V e)) x :=
  HasFDerivAt.comp (g := f) (f := GlobalTheory.SchwartzBox.restr V e) x
    f.differentiableAt.hasFDerivAt (GlobalTheory.SchwartzBox.restr V e).hasFDerivAt

/- English proof (translation)
Use extensionality with `x`. Establish `e : ⇑(bx f₁ f₂) = fun x => f₁ (x ∘ Sum.inl) * starRingEnd ℂ (f₂ (x ∘ Sum.inr))` using `funext (bx_apply f₁ f₂)`. Establish `h1 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => f₁ (y ∘ Sum.inl)) ((fderiv ℝ f₁ (x ∘ Sum.inl)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inl)) x` using `hasFDerivAt_restr Sum.inl f₁ x`. Establish `h2 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => starRingEnd ℂ (f₂ (y ∘ Sum.inr))) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f₂ (x ∘ Sum.inr)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inr))) x` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x (hasFDerivAt_restr Sum.inr f₂ x)`. Establish `h3` using `(h1.mul h2).fderiv`.

Rewrite using `[SchwartzMap.add_apply, bx_apply, bx_apply, Dop_apply, Dop_apply, Dop_apply, dH, dH, dH, bx_apply, e]`. Use `erw [h3]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, GlobalTheory.SchwartzBox.restr_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, smul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_di …`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dop_bx (a₁ a₂ b₁ b₂ : κ → mixedEmbedding.mixedSpace F) (f₁ f₂ : SInf F κ) :
    Dop (Sum.elim a₁ a₂) (Sum.elim b₁ (-b₂)) (bx f₁ f₂) = bx (Dop a₁ b₁ f₁) f₂ + bx f₁ (Dop a₂ b₂ f₂) := by
  ext x
  have e : ⇑(bx f₁ f₂) = fun x => f₁ (x ∘ Sum.inl) * starRingEnd ℂ (f₂ (x ∘ Sum.inr)) := funext (bx_apply f₁ f₂)
  have h1 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => f₁ (y ∘ Sum.inl))
      ((fderiv ℝ f₁ (x ∘ Sum.inl)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inl)) x :=
    hasFDerivAt_restr Sum.inl f₁ x
  have h2 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => starRingEnd ℂ (f₂ (y ∘ Sum.inr)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f₂ (x ∘ Sum.inr)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inr))) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x
      (hasFDerivAt_restr Sum.inr f₂ x)
  have h3 := (h1.mul h2).fderiv
  rw [SchwartzMap.add_apply, bx_apply, bx_apply, Dop_apply, Dop_apply, Dop_apply, dH, dH, dH, bx_apply, e]
  erw [h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    GlobalTheory.SchwartzBox.restr_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, smul_eq_mul, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_add, map_neg, map_sub, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_ofNat]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[SchwartzMap.neg_apply, Dop_apply, Dop_apply]`. Simplify using `only [dH, map_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dop_neg (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) : Dop (-a) (-b) f = -Dop a b f := by
  ext x
  rw [SchwartzMap.neg_apply, Dop_apply, Dop_apply]
  simp only [dH, map_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Dop_apply]`. Simplify using `[dH]`.
-/
theorem Dop_zero (f : SInf F κ) : Dop 0 0 f = 0 := by
  ext x
  rw [Dop_apply]
  simp [dH]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[pureA, add_mul]`.
-/
theorem pureA_add (f f' : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (f + f') g = pureA F f g + pureA F f' g := by
  funext x; simp [pureA, add_mul]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[pureA, mul_assoc]`.
-/
theorem pureA_smul (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (c • f) g = c • pureA F f g := by
  funext x; simp [pureA, mul_assoc]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

end Gen

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def Dm (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
  Dop (fun i => evI F ((M.co.e u).1 i)) (fun i => evI F ((M.co.e u).2 i))

/- English proof (translation)
Establish `e : M.heisLine ψ u = fun t => schr ψ (realAd F t • M.co.e u)`. Use function extensionality and compare the values at `t`. Simplify using `only [Model.heisLine, Darboux.rho, map_smul]`. Rewrite using `[e]`. Conclude with `sd_schr hψ _ f`.
-/
theorem sd_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : SInf F (Fin n × Fin d)) : SD (M.heisLine ψ u) f (Dm M u f) := by
  have e : M.heisLine ψ u = fun t => schr ψ (realAd F t • M.co.e u) := by
    funext t; simp only [Model.heisLine, Darboux.rho, map_smul]
  rw [e]
  exact sd_schr hψ _ f

/- English proof (translation)
The claim follows from `(actsLaws F _ f (Dm M u f) f).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) (sd_Dm M hψ u f)`.
-/
theorem actsD_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : SInf F (Fin n × Fin d)) : ActsD (evI F) (M.heisLine ψ u) f (Dm M u f) :=
  (actsLaws F _ f (Dm M u f) f).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) (sd_Dm M hψ u f)

/- English proof (translation)
The claim follows from `(actsLaws F _ f f₁ (Dm M u f)).2.2.1 _ h (actsD_Dm M hψ u f)`.
-/
theorem eq_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {u : Matrix (Fin n) (Fin d) (AE F E)}
    {f f₁ : SInf F (Fin n × Fin d)} (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ = Dm M u f :=
  (actsLaws F _ f f₁ (Dm M u f)).2.2.1 _ h (actsD_Dm M hψ u f)

/- English proof (translation)
Rewrite using `[Dm, Dm, ← Dop_neg, map_neg]`. Apply the tactic sequence `congr 2 <;> funext i <;> exact map_neg (evH F) _`.
-/
theorem Dm_neg (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    Dm M (-u) f = -Dm M u f := by
  rw [Dm, Dm, ← Dop_neg, map_neg]
  congr 2 <;> funext i <;> exact map_neg (evH F) _

/- English proof (translation)
Rewrite using `[Dm, map_zero, ← Dop_zero f]`. Apply the tactic sequence `congr 2 <;> funext i <;> exact map_zero (evH F)`.
-/
theorem Dm_zero (M : Model σ X W) (f : SInf F (Fin n × Fin d)) : Dm M 0 f = 0 := by
  rw [Dm, map_zero, ← Dop_zero f]
  congr 2 <;> funext i <;> exact map_zero (evH F)

def algN (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ' | ∃ (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → Af F) → ℂ),
    f ∈ M.Pol ψ τ ∧ g ∈ SB (Fin n × Fin d → Af F) ∧ Φ' = pureA F f g}

/- English proof (translation)
Establish `key : ∃ Ψ₁ ∈ algN M ψ τ, ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Ψ x) (Ψ₁ x) 0` using `by clear h`. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem Ψ hm`. Take `⟨f, g, hf, hg, rfl⟩` from `hm`. Use `⟨pureA F (Dm M u f) g, Submodule.subset_span ⟨_, g, ?_, hg, rfl⟩, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (actsD_Dm M hψ u f)`. Conclude with `sd_Dm M hψ u f g hg _ (eval_mem_adm x)`. Consider the case `zero`. Use `⟨0, zero_mem _, fun x => ?_⟩` and prove the remaining obligations. Simplify `hasDerivAt_const (0 : ℝ) (0 : ℂ)` using `[Model.heisLine, Darboux.rho, schr]`.

Consider the case `add a b _ _ ha hb`. Take `⟨a₁, ha₁, ha⟩` from `ha`. Take `⟨b₁, hb₁, hb⟩` from `hb`. Use `⟨a₁ + b₁, add_mem ha₁ hb₁, fun x => ?_⟩` and prove the remaining obligations. Use `((ha x).add (hb x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `[Model.heisLine, Darboux.rho, schr, mul_add]`. Consider the case `smul c a _ ha`. Take `⟨a₁, ha₁, ha⟩` from `ha`. Use `⟨c • a₁, Submodule.smul_mem _ c ha₁, fun x => ?_⟩` and prove the remaining obligations. Use `((ha x).const_mul c).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `only [Model.heisLine, Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨Ψ₁, h₁, h₂⟩` from `key`. Rewrite using `[show Ψ' = Ψ₁ from funext fun x => (h x).unique (h₂ x)]` and apply the resulting hypothesis.
-/
theorem algN_deriv (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {Ψ Ψ' : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ algN M ψ τ)
    (h : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Ψ x) (Ψ' x) 0) : Ψ' ∈ algN M ψ τ := by
  have key : ∃ Ψ₁ ∈ algN M ψ τ, ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Ψ x) (Ψ₁ x) 0 := by
    clear h
    induction hΨ using Submodule.span_induction with
    | mem Ψ hm =>
      obtain ⟨f, g, hf, hg, rfl⟩ := hm
      refine ⟨pureA F (Dm M u f) g, Submodule.subset_span ⟨_, g, ?_, hg, rfl⟩, fun x => ?_⟩
      · exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (actsD_Dm M hψ u f)
      · exact sd_Dm M hψ u f g hg _ (eval_mem_adm x)
    | zero =>
      refine ⟨0, zero_mem _, fun x => ?_⟩
      simpa [Model.heisLine, Darboux.rho, schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add a b _ _ ha hb =>
      obtain ⟨a₁, ha₁, ha⟩ := ha
      obtain ⟨b₁, hb₁, hb⟩ := hb
      refine ⟨a₁ + b₁, add_mem ha₁ hb₁, fun x => ?_⟩
      refine ((ha x).add (hb x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp [Model.heisLine, Darboux.rho, schr, mul_add]
    | smul c a _ ha =>
      obtain ⟨a₁, ha₁, ha⟩ := ha
      refine ⟨c • a₁, Submodule.smul_mem _ c ha₁, fun x => ?_⟩
      refine ((ha x).const_mul c).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Model.heisLine, Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
      ring
  obtain ⟨Ψ₁, h₁, h₂⟩ := key
  rwa [show Ψ' = Ψ₁ from funext fun x => (h x).unique (h₂ x)]

/- English proof (translation)
Take `⟨m, c, p, hp⟩` from `Submodule.mem_span_set'.mp hΨ`. Use `choose f g hf hg hp₀ using fun i => (p i).2`. Use `⟨m, fun i => c i • f i, g, fun i => ⟨Submodule.smul_mem _ _ (hf i), hg i⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hp₀ i, pureA_smul]`.
-/
theorem algN_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ algN M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (g : Fin m → ((Fin n × Fin d → Af F) → ℂ)),
      (∀ i, f i ∈ M.Pol ψ τ ∧ g i ∈ SB (Fin n × Fin d → Af F)) ∧ Ψ = ∑ i, pureA F (f i) (g i) := by
  obtain ⟨m, c, p, hp⟩ := Submodule.mem_span_set'.mp hΨ
  choose f g hf hg hp₀ using fun i => (p i).2
  refine ⟨m, fun i => c i • f i, g, fun i => ⟨Submodule.smul_mem _ _ (hf i), hg i⟩, ?_⟩
  rw [← hp]
  exact Finset.sum_congr rfl fun i _ => by rw [hp₀ i, pureA_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topC_smul (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : topC (a • u) = a • topC u := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem botC_smul (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : botC (a • u) = a • botC u := rfl

/- English proof (translation)
Simplify using `only [dblE, topC_smul, botC_smul, map_smul]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> funext i <;> rcases i with i | i <;> simp`.
-/
theorem dblE_smul (M : Model σ X W) (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) :
    dblE M.co (a • u) = a • dblE M.co u := by
  simp only [dblE, topC_smul, botC_smul, map_smul]
  refine Prod.ext ?_ ?_ <;> funext i <;> rcases i with i | i <;> simp

/- English proof (translation)
Introduce `a ha` and use `by rw [← topC_smul, hu a ha]; rfl`.
-/
theorem at_topC {u : Matrix (Fin n) (Fin (d + d)) (AE F E)} (hu : At (evI F) u) : At (evI F) (topC u) :=
  fun a ha => by rw [← topC_smul, hu a ha]; rfl

/- English proof (translation)
Introduce `a ha` and use `by rw [← botC_smul, hu a ha]; rfl`.
-/
theorem at_botC {u : Matrix (Fin n) (Fin (d + d)) (AE F E)} (hu : At (evI F) u) : At (evI F) (botC u) :=
  fun a ha => by rw [← botC_smul, hu a ha]; rfl

def glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin (d + d)) (AE F E) :=
  (Matrix.fromCols u₁ u₂).submatrix id finSumFinEquiv.symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[topC, glue]`.
-/
theorem topC_glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : topC (glue u₁ u₂) = u₁ := by
  ext i j; simp [topC, glue]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[botC, glue, -Fin.natAdd_eq_addNat]`.
-/
theorem botC_glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : botC (glue u₁ u₂) = u₂ := by
  ext i j; simp [botC, glue, -Fin.natAdd_eq_addNat]

/- English proof (translation)
Introduce `a ha`. Use extensionality with `i j`. Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective j`. Break down `j with j | j` into its components or cases. Simplify `congrFun (congrFun (h₁ a ha) i) j` using `[glue]`.

Simplify `congrFun (congrFun (h₂ a ha) i) j` using `[glue, -Fin.natAdd_eq_addNat]`.
-/
theorem at_glue {u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)} (h₁ : At (evI F) u₁) (h₂ : At (evI F) u₂) :
    At (evI F) (glue u₁ u₂) := by
  intro a ha
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simpa [glue] using congrFun (congrFun (h₁ a ha) i) j
  · simpa [glue, -Fin.natAdd_eq_addNat] using congrFun (congrFun (h₂ a ha) i) j

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]`. Simplify using `[blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]`.
-/
theorem mul_blk_inl (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin (d + d)) ℂ) (θ θ' : Matrix (Fin d) (Fin d) ℂ) :
    (A * U * (blkMat finSumFinEquiv θ θ')ᵀ).submatrix id (finSumFinEquiv ∘ Sum.inl) =
      A * U.submatrix id (finSumFinEquiv ∘ Sum.inl) * θᵀ := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]
  simp [blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]`. Simplify using `[blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]`.
-/
theorem mul_blk_inr (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin (d + d)) ℂ) (θ θ' : Matrix (Fin d) (Fin d) ℂ) :
    (A * U * (blkMat finSumFinEquiv θ θ')ᵀ).submatrix id (finSumFinEquiv ∘ Sum.inr) =
      A * U.submatrix id (finSumFinEquiv ∘ Sum.inr) * θ'ᵀ := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]
  simp [blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]

end Model

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {W₂ : Spc F E (d + d)} (M : Model σ X W) (M₂ : Model σ X W₂) {ψ : AddChar (AF F) ℂ}
  (τ : ∀ w : InfinitePlace F, EmbOver E w)
  (e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ))

/- English proof (translation)
Establish `h` using `sd_schr hψ (dblE M.co u) (bx f₁ f₂) g hg _ (hadm _ (eval_mem_adm x))`. Establish `e1 : (fun i => evI F ((dblE M.co u).1 i)) = Sum.elim (fun i => evI F ((M.co.e (topC u)).1 i)) (fun i => evI F ((M.co.e (botC u)).1 i))`. Apply the tactic sequence `funext i; rcases i with i | i <;> rfl`. Establish `e2 : (fun i => evI F ((dblE M.co u).2 i)) = Sum.elim (fun i => evI F ((M.co.e (topC u)).2 i)) (-fun i => evI F ((M.co.e (botC u)).2 i))`. Use function extensionality and compare the values at `i`.

Break down `i with i | i` into its components or cases. Both sides reduce to the same expression. Conclude with `map_neg (evH F) _`. Rewrite `h` using `[e1, e2, Dop_bx]`. Use `h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply, Model.heisLine]`. Rewrite using `[← dblE_smul, hint _ _ (pureA_mem _ hg)]`.
-/
theorem hasDerivAt_e (hψ : IsStd ψ)
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) (f₁ f₂ : SInf F (Fin n × Fin d))
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) (x : Fin n × Fin (d + d) → AF F) :
    HasDerivAt (fun t => M₂.heisLine ψ u t (e (pureA F (bx f₁ f₂) g)) x)
      (e (pureA F (bx (Dm M (topC u) f₁) f₂ + bx f₁ (Dm M (botC u) f₂) : SInf F _) g) x) 0 := by
  have h := sd_schr hψ (dblE M.co u) (bx f₁ f₂) g hg _ (hadm _ (eval_mem_adm x))
  have e1 : (fun i => evI F ((dblE M.co u).1 i)) =
      Sum.elim (fun i => evI F ((M.co.e (topC u)).1 i)) (fun i => evI F ((M.co.e (botC u)).1 i)) := by
    funext i; rcases i with i | i <;> rfl
  have e2 : (fun i => evI F ((dblE M.co u).2 i)) =
      Sum.elim (fun i => evI F ((M.co.e (topC u)).2 i)) (-fun i => evI F ((M.co.e (botC u)).2 i)) := by
    funext i
    rcases i with i | i
    · rfl
    · exact map_neg (evH F) _
  rw [e1, e2, Dop_bx] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Model.heisLine]
  rw [← dblE_smul, hint _ _ (pureA_mem _ hg)]

/- English proof (translation)
Distinguish the cases in `h0 : f₁ = 0`. Establish `: pureA F (bx f₁ f₂) g = 0`. Rewrite using `[h0, bx_zero_left]`. Use function extensionality and compare the values at `x`. Simplify using `[pureA]`.

Rewrite using `[this, map_zero]`. Conclude with `zero_mem _`. Take `⟨z, rfl⟩` from `GlobalTheory.RealDict.FockMap.gauss_line M ψ τ hσ hψ hX hW f₂ f₁ h₁ h0 h₂`. Rewrite using `[bx_smul_right, pureA_smul, map_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Use `GlobalTheory.VacFactor.mem_span_of_isGaussEq M₂ ψ τ hψ _ (hmap _ (pureA_mem _ hg)) ?_` and prove the remaining obligations. Take `⟨ε, hε⟩` from `h₁`. Use `⟨ε, fun u u' hu hu' huu x => ?_⟩` and prove the remaining obligations. Rewrite using `[(hasDerivAt_e M M₂ e hψ hadm hint u f₁ f₁ hg x).deriv, (hasDerivAt_e M M₂ e hψ hadm hint u' f₁ f₁ hg x).deriv]`. Establish `a1 : Dm M (topC u') f₁ = Complex.I • Dm M (topC u) f₁`.

Use `hε _ _ (at_topC hu) (at_topC hu') (fun w => ?_) _ _ (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)` and prove the remaining obligations. Use `congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inl)) (huu w)` as an intermediate fact. Simplify using `only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inl] at this`. Conclude with `this`. Establish `a2 : Dm M (-botC u') f₁ = Complex.I • Dm M (botC u) f₁`.

Use `hε _ _ (at_botC hu) (fun a ha => by rw [smul_neg, at_botC hu' a ha, neg_zero]) (fun w => ?_) _ _ (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)` and prove the remaining obligations. Use `congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inr)) (huu w)` as an intermediate fact. Simplify using `only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inr, Matrix.transpose_neg, Matrix.mul_neg, smul_neg] at this`. Rewrite using `[Matrix.map_neg _ (map_neg (piInf (τ w))), neg_eq_iff_eq_neg]`. Conclude with `this`.

Establish `a3 : Dm M (botC u') f₁ = (-Complex.I) • Dm M (botC u) f₁`. Rewrite `a2` using `[Dm_neg, neg_eq_iff_eq_neg]`. Rewrite using `[a2, neg_smul]`. Rewrite using `[a1, a3, bx_smul_left, bx_smul_right, map_neg, Complex.conj_I, neg_neg, ← smul_add, pureA_smul, map_smul]`. Both sides reduce to the same expression.
-/
theorem gauss_mem (hσ : IsCMExt F E σ) (hψ : IsStd ψ) (hX : ∀ w, X.θ w * X.θ w = 1) (hW : ∀ w, W.θ w * W.θ w = 1)
    (hθ : ∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    (hmap : ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e Ψ ∈ schA F (Fin n × Fin (d + d)))
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    {f₁ f₂ : SInf F (Fin n × Fin d)} (h₁ : M.IsGauss ψ τ f₁) (h₂ : M.IsGauss ψ τ f₂)
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) :
    e (pureA F (bx f₁ f₂) g) ∈ algN M₂ ψ τ := by
  by_cases h0 : f₁ = 0
  · have : pureA F (bx f₁ f₂) g = 0 := by
      rw [h0, bx_zero_left]; funext x; simp [pureA]
    rw [this, map_zero]
    exact zero_mem _
  obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M ψ τ hσ hψ hX hW f₂ f₁ h₁ h0 h₂
  rw [bx_smul_right, pureA_smul, map_smul]
  refine Submodule.smul_mem _ _ ?_
  refine GlobalTheory.VacFactor.mem_span_of_isGaussEq M₂ ψ τ hψ _ (hmap _ (pureA_mem _ hg)) ?_
  obtain ⟨ε, hε⟩ := h₁
  refine ⟨ε, fun u u' hu hu' huu x => ?_⟩
  rw [(hasDerivAt_e M M₂ e hψ hadm hint u f₁ f₁ hg x).deriv, (hasDerivAt_e M M₂ e hψ hadm hint u' f₁ f₁ hg x).deriv]
  have a1 : Dm M (topC u') f₁ = Complex.I • Dm M (topC u) f₁ := by
    refine hε _ _ (at_topC hu) (at_topC hu') (fun w => ?_) _ _ (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)
    have := congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inl)) (huu w)
    simp only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inl] at this
    exact this
  have a2 : Dm M (-botC u') f₁ = Complex.I • Dm M (botC u) f₁ := by
    refine hε _ _ (at_botC hu) (fun a ha => by rw [smul_neg, at_botC hu' a ha, neg_zero]) (fun w => ?_) _ _
      (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)
    have := congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inr)) (huu w)
    simp only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inr, Matrix.transpose_neg, Matrix.mul_neg,
      smul_neg] at this
    rw [Matrix.map_neg _ (map_neg (piInf (τ w))), neg_eq_iff_eq_neg]
    exact this
  have a3 : Dm M (botC u') f₁ = (-Complex.I) • Dm M (botC u) f₁ := by
    rw [Dm_neg, neg_eq_iff_eq_neg] at a2
    rw [a2, neg_smul]
  rw [a1, a3, bx_smul_left, bx_smul_right, map_neg, Complex.conj_I, neg_neg, ← smul_add, pureA_smul, map_smul]
  rfl

/- English proof (translation)
Establish `z0 : e (pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g) ∈ algN M₂ ψ τ`. Establish `: pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g = 0` using `by funext x; simp [pureA]`. Rewrite using `[this, map_zero]`. Conclude with `zero_mem _`. Establish `der : ∀ u₁ u₂, At (evI F) u₁ → At (evI F) u₂ → ∀ a b, e (pureA F (bx a b) g) ∈ algN M₂ ψ τ → e (pureA F (bx (Dm M u₁ a) b + bx a (Dm M u₂ b) : SInf F _) g) ∈ algN M₂ ψ τ`.

Introduce `u₁ u₂ hu₁ hu₂ a b hab`. Use `algN_deriv M₂ hψ τ (at_glue hu₁ hu₂) hab fun x => ?_` and prove the remaining obligations. Use `hasDerivAt_e M M₂ e hψ hadm hint (glue u₁ u₂) a b hg x` as an intermediate fact. Rewrite `this` using `[topC_glue, botC_glue]`. Then use the resulting hypothesis. Establish `at0 : At (evI F) (0 : Matrix (Fin n) (Fin d) (AE F E))` using `fun a _ => smul_zero a`.

Establish `step : ∀ a, M.IsGauss ψ τ a → e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ`. Introduce `a ha`. Set `N : Submodule ℂ (SInf F (Fin n × Fin d))` to `{ carrier := {b | e (pureA F (bx a b) g) ∈ algN M₂ ψ τ} add_mem' := fun {b b'} hb hb' => by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx a (b + b')) g) ∈ algN M₂ ψ τ`. Rewrite using `[bx_add_right, pureA_add, map_add]`.

Conclude with `add_mem hb hb'`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx a 0) g) ∈ algN M₂ ψ τ`. Rewrite using `[bx_zero_right]`. Conclude with `z0`.

Use the proof step `smul_mem' := fun c b hb => by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx a (c • b)) g) ∈ algN M₂ ψ τ`. Rewrite using `[bx_smul_right, pureA_smul, map_smul]`. Conclude with `Submodule.smul_mem _ _ hb }`. Use `Submodule.mem_sInf.1 h₂ N ⟨fun b hb => gauss_mem M M₂ τ e hσ hψ hX hW hθ hmap hadm hint ha hb hg, fun u hu b hb b₁ hb₁ => ?_⟩` and prove the remaining obligations.

Use `der 0 u at0 hu a b hb` as an intermediate fact. Rewrite `this` using `[Dm_zero, bx_zero_left, zero_add, ← eq_Dm M hψ hb₁]`. Conclude with `this`. Set `N : Submodule ℂ (SInf F (Fin n × Fin d))` to `{ carrier := {a | e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ} add_mem' := fun {b b'} hb hb' => by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx (b + b') f₂) g) ∈ algN M₂ ψ τ`.

Rewrite using `[bx_add_left, pureA_add, map_add]`. Conclude with `add_mem hb hb'`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx 0 f₂) g) ∈ algN M₂ ψ τ`. Rewrite using `[bx_zero_left]`.

Conclude with `z0`. Use the proof step `smul_mem' := fun c b hb => by`. Express the relevant statement in the definitionally equal form `e (pureA F (bx (c • b) f₂) g) ∈ algN M₂ ψ τ`. Rewrite using `[bx_smul_left, pureA_smul, map_smul]`. Conclude with `Submodule.smul_mem _ _ hb }`.

Use `Submodule.mem_sInf.1 h₁ N ⟨step, fun u hu a ha a₁ ha₁ => ?_⟩` and prove the remaining obligations. Use `der u 0 hu at0 a f₂ ha` as an intermediate fact. Rewrite `this` using `[Dm_zero, bx_zero_right, add_zero, ← eq_Dm M hψ ha₁]`. Conclude with `this`.
-/
theorem pol_mem (hσ : IsCMExt F E σ) (hψ : IsStd ψ) (hX : ∀ w, X.θ w * X.θ w = 1) (hW : ∀ w, W.θ w * W.θ w = 1)
    (hθ : ∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    (hmap : ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e Ψ ∈ schA F (Fin n × Fin (d + d)))
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _)
    {f₁ f₂ : SInf F (Fin n × Fin d)} (h₁ : f₁ ∈ M.Pol ψ τ) (h₂ : f₂ ∈ M.Pol ψ τ) :
    e (pureA F (bx f₁ f₂) g) ∈ algN M₂ ψ τ := by
  have z0 : e (pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g) ∈ algN M₂ ψ τ := by
    have : pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g = 0 := by funext x; simp [pureA]
    rw [this, map_zero]
    exact zero_mem _
  have der : ∀ u₁ u₂, At (evI F) u₁ → At (evI F) u₂ → ∀ a b, e (pureA F (bx a b) g) ∈ algN M₂ ψ τ →
      e (pureA F (bx (Dm M u₁ a) b + bx a (Dm M u₂ b) : SInf F _) g) ∈ algN M₂ ψ τ := by
    intro u₁ u₂ hu₁ hu₂ a b hab
    refine algN_deriv M₂ hψ τ (at_glue hu₁ hu₂) hab fun x => ?_
    have := hasDerivAt_e M M₂ e hψ hadm hint (glue u₁ u₂) a b hg x
    rwa [topC_glue, botC_glue] at this
  have at0 : At (evI F) (0 : Matrix (Fin n) (Fin d) (AE F E)) := fun a _ => smul_zero a
  have step : ∀ a, M.IsGauss ψ τ a → e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ := by
    intro a ha
    let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
      { carrier := {b | e (pureA F (bx a b) g) ∈ algN M₂ ψ τ}
        add_mem' := fun {b b'} hb hb' => by
          change e (pureA F (bx a (b + b')) g) ∈ algN M₂ ψ τ
          rw [bx_add_right, pureA_add, map_add]
          exact add_mem hb hb'
        zero_mem' := by
          change e (pureA F (bx a 0) g) ∈ algN M₂ ψ τ
          rw [bx_zero_right]; exact z0
        smul_mem' := fun c b hb => by
          change e (pureA F (bx a (c • b)) g) ∈ algN M₂ ψ τ
          rw [bx_smul_right, pureA_smul, map_smul]
          exact Submodule.smul_mem _ _ hb }
    refine Submodule.mem_sInf.1 h₂ N ⟨fun b hb => gauss_mem M M₂ τ e hσ hψ hX hW hθ hmap hadm hint ha hb hg,
      fun u hu b hb b₁ hb₁ => ?_⟩
    have := der 0 u at0 hu a b hb
    rw [Dm_zero, bx_zero_left, zero_add, ← eq_Dm M hψ hb₁] at this
    exact this
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {a | e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ}
      add_mem' := fun {b b'} hb hb' => by
        change e (pureA F (bx (b + b') f₂) g) ∈ algN M₂ ψ τ
        rw [bx_add_left, pureA_add, map_add]
        exact add_mem hb hb'
      zero_mem' := by
        change e (pureA F (bx 0 f₂) g) ∈ algN M₂ ψ τ
        rw [bx_zero_left]; exact z0
      smul_mem' := fun c b hb => by
        change e (pureA F (bx (c • b) f₂) g) ∈ algN M₂ ψ τ
        rw [bx_smul_left, pureA_smul, map_smul]
        exact Submodule.smul_mem _ _ hb }
  refine Submodule.mem_sInf.1 h₁ N ⟨step, fun u hu a ha a₁ ha₁ => ?_⟩
  have := der u 0 hu at0 a f₂ ha
  rw [Dm_zero, bx_zero_right, add_zero, ← eq_Dm M hψ ha₁] at this
  exact this

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ hθ co _ _ _ e hbij hadm hint Φ₁ h₁ Φ₂ h₂`. Use `set M₂ : Model σ Xs W₂ := { co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } with hM₂`. Use `algN_sum M₂ B.ψ B.emb ?_` and prove the remaining obligations. Establish `hfin : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → (fun y : Fin n × Fin d → Af F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _` using `fun φ hφ hv =>`. Establish `hstd` using `(hv.and hP.good.std).mono fun v h => h.1.trans h.2`.

Use the proof step `⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hstd⟩`. Proceed by induction on `h₁ using Submodule.span_induction with`. Consider the case `mem Φ₁ h₁`. Take `⟨f₁, hf₁, φ₁, hφ₁, hv₁, rfl⟩` from `h₁`. Proceed by induction on `h₂ using Submodule.span_induction with`.

Consider the case `mem Φ₂ h₂`. Take `⟨f₂, hf₂, φ₂, hφ₂, hv₂, rfl⟩` from `h₂`. Establish `g₁` using `hfin φ₁ hφ₁ hv₁`. Establish `g₂` using `hfin φ₂ hφ₂ hv₂`. Establish `g₂' : (fun y : Fin n × Fin d → Af F => starRingEnd ℂ (∏ᶠ v, φ₂ v fun i => evalV F v (y i))) ∈ SB _` using `⟨g₂.1.comp _, g₂.2.comp_left (map_zero _)⟩`.

Establish `key` using `pol_mem M M₂ B.emb e hP.base.cm hP.base.std (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) hθ (fun Ψ hΨ => hbij.mapsTo hΨ) hadm hint (GlobalTheory.SchwartzBox.sb_box g₁ g₂') hf₁ hf₂`. Use `key using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `only [boxC, boxFun, pureA, bx_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Complex.star_def, map_mul]`. Rewrite using `[mul_mul_mul_comm]`.

Both sides reduce to the same expression. Consider the case `zero`. Establish `: boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) 0 = 0` using `by funext x; simp [boxC, boxFun]`. Rewrite using `[this, map_zero]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb`. Establish `: boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (a + b) = boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a + boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) b`. Use function extensionality and compare the values at `x`. Simplify using `[boxC, boxFun, mul_add]`. Rewrite using `[this, map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `: boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (c • a) = star c • boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a`. Use function extensionality and compare the values at `x`. Simplify using `only [boxC, boxFun, Pi.smul_apply, smul_eq_mul, star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`. Consider the case `zero`. Establish `: boxC 0 Φ₂ = 0` using `by funext x; simp [boxC, boxFun]`.

Rewrite using `[this, map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `: boxC (a + b) Φ₂ = boxC a Φ₂ + boxC b Φ₂` using `by funext x; simp [boxC, boxFun, add_mul]`. Rewrite using `[this, map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `: boxC (c • a) Φ₂ = c • boxC a Φ₂` using `by funext x; simp [boxC, boxFun, mul_assoc]`. Rewrite using `[this, map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem dbl_pol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin (d + d))) (g : Fin m → ((Fin n × Fin (d + d) → Af F) → ℂ)),
        (∀ i, f i ∈ Model.Pol ({ co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } : Model σ Xs W₂) B.ψ B.emb ∧
          g i ∈ SB (Fin n × Fin (d + d) → Af F)) ∧
        e (boxC Φ₁ Φ₂) = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ hθ co _ _ _ e hbij hadm hint Φ₁ h₁ Φ₂ h₂
  set M₂ : Model σ Xs W₂ := { co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } with hM₂
  refine algN_sum M₂ B.ψ B.emb ?_
  have hfin : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      (fun y : Fin n × Fin d → Af F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _ := fun φ hφ hv =>
    have hstd := (hv.and hP.good.std).mono fun v h => h.1.trans h.2
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hstd⟩
  induction h₁ using Submodule.span_induction with
  | mem Φ₁ h₁ =>
    obtain ⟨f₁, hf₁, φ₁, hφ₁, hv₁, rfl⟩ := h₁
    induction h₂ using Submodule.span_induction with
    | mem Φ₂ h₂ =>
      obtain ⟨f₂, hf₂, φ₂, hφ₂, hv₂, rfl⟩ := h₂
      have g₁ := hfin φ₁ hφ₁ hv₁
      have g₂ := hfin φ₂ hφ₂ hv₂
      have g₂' : (fun y : Fin n × Fin d → Af F => starRingEnd ℂ (∏ᶠ v, φ₂ v fun i => evalV F v (y i))) ∈ SB _ :=
        ⟨g₂.1.comp _, g₂.2.comp_left (map_zero _)⟩
      have key := pol_mem M M₂ B.emb e hP.base.cm hP.base.std (fun w => (hP.herm.cartan w).1)
        (fun w => (hP.skew.cartan w).1) hθ (fun Ψ hΨ => hbij.mapsTo hΨ) hadm hint (GlobalTheory.SchwartzBox.sb_box g₁ g₂') hf₁ hf₂
      convert key using 2
      funext x
      simp only [boxC, boxFun, pureA, bx_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Complex.star_def, map_mul]
      rw [mul_mul_mul_comm]
      rfl
    | zero =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) 0 = 0 := by funext x; simp [boxC, boxFun]
      rw [this, map_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (a + b) =
          boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a + boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) b := by
        funext x; simp [boxC, boxFun, mul_add]
      rw [this, map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (c • a) = star c • boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a := by
        funext x; simp only [boxC, boxFun, Pi.smul_apply, smul_eq_mul, star_mul']; ring
      rw [this, map_smul]; exact Submodule.smul_mem _ _ ha
  | zero =>
    have : boxC 0 Φ₂ = 0 := by funext x; simp [boxC, boxFun]
    rw [this, map_zero]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : boxC (a + b) Φ₂ = boxC a Φ₂ + boxC b Φ₂ := by funext x; simp [boxC, boxFun, add_mul]
    rw [this, map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have : boxC (c • a) Φ₂ = c • boxC a Φ₂ := by funext x; simp [boxC, boxFun, mul_assoc]
    rw [this, map_smul]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.DblPolArch

end
