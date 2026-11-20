import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieB
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieD
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock

noncomputable section

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace, Matrix.trace, Rat.cast_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]`.
-/
theorem trace_emb (a : F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F a) =
    (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `(mixedEmbedding.latticeBasis F).ext_elem fun j => ?_` and prove the remaining obligations. Use `h (Pi.single i (mixedEmbedding F ((integralBasis F).traceDual j)))` as an intermediate fact. Rewrite `this` using `[dotProduct_single, ← (mixedEmbedding.latticeBasis F).sum_repr (l i)]`. Simplify using `only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, mixedEmbedding.latticeBasis_apply, ← map_mul, trace_emb, Module.Basis.trace_mul_traceDual] at this`.

Simplify `this` using `[apply_ite]`.
-/
theorem trace_nondeg (l : κ → mixedEmbedding.mixedSpace F)
    (h : ∀ y, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (l ⬝ᵥ y) = 0) : l = 0 := by
  funext i
  refine (mixedEmbedding.latticeBasis F).ext_elem fun j => ?_
  have := h (Pi.single i (mixedEmbedding F ((integralBasis F).traceDual j)))
  rw [dotProduct_single, ← (mixedEmbedding.latticeBasis F).sum_repr (l i)] at this
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, mixedEmbedding.latticeBasis_apply, ← map_mul, trace_emb,
    Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this

variable (F κ) in

structure Co (l : Type) [Fintype l] where
  e1 : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ l
  e2 : (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ l
  pair : ∀ x y, ⟪e2 y, e1 x⟫ = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i)

variable (F κ) in
/- English proof (translation)
Set `e1` to `toEuclidean (E := κ → mixedEmbedding.mixedSpace F)`. Set `L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)))` to `(InnerProductSpace.toDual ℝ _).symm.toLinearEquiv.toLinearMap ∘ₗ ((ContinuousLinearMap.compL ℝ _ _ ℝ).flip (e1.symm : _ →L[ℝ] _)).toLinearMap ∘ₗ (-Fock.trB F κ)`. Establish `hL : ∀ x y, ⟪L y, e1 x⟫ = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i)` using `fun x y => by`. Simplify using `[L, Fock.trB_apply]`. Establish `hi : Function.Injective L` using `(injective_iff_map_eq_zero _).2 fun y hy => trace_nondeg y fun x => by`.

Use `hL x y` as an intermediate fact. Rewrite `this` using `[hy, inner_zero_left, eq_comm, neg_eq_zero]`. Rewrite using `[dotProduct_comm]`. Conclude with `this`. Conclude with `⟨_, ⟨⟨e1, LinearEquiv.ofBijective L ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hi⟩, hL⟩⟩⟩`.
-/
theorem exists_co : ∃ n : ℕ, Nonempty (Co F κ (Fin n)) := by
  let e1 := toEuclidean (E := κ → mixedEmbedding.mixedSpace F)
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) :=
    (InnerProductSpace.toDual ℝ _).symm.toLinearEquiv.toLinearMap ∘ₗ
      ((ContinuousLinearMap.compL ℝ _ _ ℝ).flip (e1.symm : _ →L[ℝ] _)).toLinearMap ∘ₗ (-Fock.trB F κ)
  have hL : ∀ x y, ⟪L y, e1 x⟫ = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := fun x y => by
    simp [L, Fock.trB_apply]
  have hi : Function.Injective L := (injective_iff_map_eq_zero _).2 fun y hy => trace_nondeg y fun x => by
    have := hL x y
    rw [hy, inner_zero_left, eq_comm, neg_eq_zero] at this
    rw [dotProduct_comm]
    exact this
  exact ⟨_, ⟨⟨e1, LinearEquiv.ofBijective L ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp)).1 hi⟩, hL⟩⟩⟩

/- English proof (translation)
The claim follows from `(SeminormBoundRestriction.at_iff _).2 fun _ => rfl`.
-/
theorem at_pt (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (SeminormBoundRestriction.pt y 0) := (SeminormBoundRestriction.at_iff _).2 fun _ => rfl

/- English proof (translation)
The claim follows from `funext fun i => RingEquiv.apply_symm_apply _ _`.
-/
theorem evI_pt (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : (fun i => evI F (SeminormBoundRestriction.pt y z i)) = y :=
  funext fun i => RingEquiv.apply_symm_apply _ _

/- English proof (translation)
Use `h (1 - realAd F 1) (by` as an intermediate fact. Rewrite using `[← Fock.evIh_apply, map_sub, map_one, Fock.evIh_apply, Fock.evI_realAd, map_one, sub_self])`. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero, eq_comm]`. Then use the resulting hypothesis.
-/
theorem realAd_one {M : Type} [AddCommGroup M] [Module (AF F) M] {a : M} (h : At (evI F) a) : realAd F 1 • a = a := by
  have := h (1 - realAd F 1) (by
    rw [← Fock.evIh_apply, map_sub, map_one, Fock.evIh_apply, Fock.evI_realAd, map_one, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at this

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem pure_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

/- English proof (translation)
Take `⟨g, hg, y, hy⟩` from `SeminormBoundRestriction.exists_SB (F := F) (κ := κ)`. Set `ι : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Take `⟨r, hr⟩` from `ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)`. Set `l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ` to `T.toLinearMap ∘ₗ r ∘ₗ LinearMap.funLeft ℂ ℂ fun a => SeminormBoundRestriction.pt a y`. Establish `hl : ∀ (f : SInf F κ) g, l (pureA F f g) = g y • T f` using `fun f g => by`.

Establish `e : LinearMap.funLeft ℂ ℂ (fun a => SeminormBoundRestriction.pt a y) (pureA F f g) = ι (g y • f)`. Use function extensionality and compare the values at `a`. Conclude with `(SeminormBoundRestriction.pureA_pt _ _ _ _).trans (mul_comm _ _)`. Use `show T (r _) = _`. Rewrite using `[e, show r (ι (g y • f)) = g y • f from LinearMap.congr_fun hr _, map_smul]`.

Conclude with `⟨l, fun g _ => ⟨g y • T, fun f => hl f g⟩, g, hg, fun f => by rw [hl, hy, one_smul]⟩`.
-/
theorem exists_adm (T : SInf F κ →L[ℂ] ℂ) : ∃ l ∈ (adeleClass F).adm κ, ∃ g ∈ SB (κ → Af F), ∀ f : SInf F κ,
    l (pureA F f g) = T f := by
  obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
  let ι : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨r, hr⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := T.toLinearMap ∘ₗ r ∘ₗ LinearMap.funLeft ℂ ℂ fun a => SeminormBoundRestriction.pt a y
  have hl : ∀ (f : SInf F κ) g, l (pureA F f g) = g y • T f := fun f g => by
    have e : LinearMap.funLeft ℂ ℂ (fun a => SeminormBoundRestriction.pt a y) (pureA F f g) = ι (g y • f) := by
      funext a
      exact (SeminormBoundRestriction.pureA_pt _ _ _ _).trans (mul_comm _ _)
    show T (r _) = _
    rw [e, show r (ι (g y • f)) = g y • f from LinearMap.congr_fun hr _, map_smul]
  exact ⟨l, fun g _ => ⟨g y • T, fun f => hl f g⟩, g, hg, fun f => by rw [hl, hy, one_smul]⟩

namespace Co

variable {l : Type} [Fintype l] (c : Co F κ l)

def P : Sch l →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.e1

def P' : SInf F κ →L[ℂ] Sch l := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.e1.symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem P_apply (f : Sch l) (x) : c.P f x = f (c.e1 x) := rfl

/- English proof (translation)
The claim follows from `SchwartzMap.ext fun x => congrArg f (c.e1.symm_apply_apply x)`.
-/
theorem P_P' (f : SInf F κ) : c.P (c.P' f) = f := SchwartzMap.ext fun x => congrArg f (c.e1.symm_apply_apply x)

/- English proof (translation)
The claim follows from `SchwartzMap.ext fun x => congrArg f (c.e1.apply_symm_apply x)`.
-/
theorem P'_P (f : Sch l) : c.P' (c.P f) = f := SchwartzMap.ext fun x => congrArg f (c.e1.apply_symm_apply x)

def vec (w : (κ → AF F) × (κ → AF F)) : l ⊕ l → ℝ :=
  Sum.elim (c.e1 fun i => evI F (w.1 i)) (c.e2 fun i => evI F (w.2 i))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pPart_vec (w) : pPart (c.vec w) = c.e1 fun i => evI F (w.1 i) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qPart_vec (w) : qPart (c.vec w) = c.e2 fun i => evI F (w.2 i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `a`. Break down `a with a | a` into its components or cases. Conclude with `congrArg (fun v => v a) h1`. Conclude with `congrArg (fun v => v a) h2`.
-/
theorem vec_ext {w w' : l ⊕ l → ℝ} (h1 : pPart w = pPart w') (h2 : qPart w = qPart w') : w = w' := by
  funext a
  rcases a with a | a
  · exact congrArg (fun v => v a) h1
  · exact congrArg (fun v => v a) h2

/- English proof (translation)
Use `vec_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pPart_add, pPart_vec, pPart_vec, pPart_vec, ← map_add]`. Conclude with `congrArg c.e1 (funext fun i => Fock.evI_add _ _)`. Rewrite using `[qPart_add, qPart_vec, qPart_vec, qPart_vec, ← map_add]`. Conclude with `congrArg c.e2 (funext fun i => Fock.evI_add _ _)`.
-/
theorem vec_add (w w') : c.vec (w + w') = c.vec w + c.vec w' := by
  refine vec_ext ?_ ?_
  · rw [pPart_add, pPart_vec, pPart_vec, pPart_vec, ← map_add]
    exact congrArg c.e1 (funext fun i => Fock.evI_add _ _)
  · rw [qPart_add, qPart_vec, qPart_vec, qPart_vec, ← map_add]
    exact congrArg c.e2 (funext fun i => Fock.evI_add _ _)

/- English proof (translation)
Establish `e : ∀ a : AF F, evI F (realAd F t * a) = t • evI F a` using `fun a => by`. Rewrite using `[Fock.evI_mul, Fock.evI_realAd, Algebra.smul_def]`. Use `vec_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pPart_smul, pPart_vec, pPart_vec, ← map_smul]`. Conclude with `congrArg c.e1 (funext fun i => e _)`.

Rewrite using `[qPart_smul, qPart_vec, qPart_vec, ← map_smul]`. Conclude with `congrArg c.e2 (funext fun i => e _)`.
-/
theorem vec_smul (t : ℝ) (w) : c.vec (realAd F t • w) = t • c.vec w := by
  have e : ∀ a : AF F, evI F (realAd F t * a) = t • evI F a := fun a => by
    rw [Fock.evI_mul, Fock.evI_realAd, Algebra.smul_def]
  refine vec_ext ?_ ?_
  · rw [pPart_smul, pPart_vec, pPart_vec, ← map_smul]
    exact congrArg c.e1 (funext fun i => e _)
  · rw [qPart_smul, qPart_vec, qPart_vec, ← map_smul]
    exact congrArg c.e2 (funext fun i => e _)

/- English proof (translation)
Use `⟨(SeminormBoundRestriction.pt (c.e1.symm (pPart w)) 0, SeminormBoundRestriction.pt (c.e2.symm (qPart w)) 0), fun a ha => Prod.ext (at_pt _ a ha) (at_pt _ a ha), vec_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[pPart_vec, evI_pt, ContinuousLinearEquiv.apply_symm_apply]`. Rewrite using `[qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]`.
-/
theorem exists_vec (w : l ⊕ l → ℝ) : ∃ p : (κ → AF F) × (κ → AF F), At (evI F) p ∧ c.vec p = w := by
  refine ⟨(SeminormBoundRestriction.pt (c.e1.symm (pPart w)) 0, SeminormBoundRestriction.pt (c.e2.symm (qPart w)) 0),
    fun a ha => Prod.ext (at_pt _ a ha) (at_pt _ a ha), vec_ext ?_ ?_⟩
  · rw [pPart_vec, evI_pt, ContinuousLinearEquiv.apply_symm_apply]
  · rw [qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Establish `key : ∀ a : κ → AF F, At (evI F) a → (fun i => evI F (a i)) = 0 → a = 0` using `fun a ha h0 => funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ((SeminormBoundRestriction.at_iff a).1 ha i)`. Use `Prod.ext (key _ (fun a ha => congrArg Prod.fst (hp a ha)) ?_) (key _ (fun a ha => congrArg Prod.snd (hp a ha)) ?_)` and prove the remaining obligations. Conclude with `c.e1.map_eq_zero_iff.1 (congrArg pPart h)`. Conclude with `c.e2.map_eq_zero_iff.1 (congrArg qPart h)`.
-/
theorem eq_zero_of_vec {p : (κ → AF F) × (κ → AF F)} (hp : At (evI F) p) (h : c.vec p = 0) : p = 0 := by
  have key : ∀ a : κ → AF F, At (evI F) a → (fun i => evI F (a i)) = 0 → a = 0 := fun a ha h0 => funext fun i =>
    Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ((SeminormBoundRestriction.at_iff a).1 ha i)
  refine Prod.ext (key _ (fun a ha => congrArg Prod.fst (hp a ha)) ?_) (key _ (fun a ha => congrArg Prod.snd (hp a ha)) ?_)
  · exact c.e1.map_eq_zero_iff.1 (congrArg pPart h)
  · exact c.e2.map_eq_zero_iff.1 (congrArg qPart h)

/- English proof (translation)
Rewrite using `[sympl, real_inner_comm, pPart_vec, qPart_vec, pPart_vec, qPart_vec, c.pair, c.pair, ← Fock.evIh_apply]`. Simplify using `only [dotProduct, map_sub, map_sum, map_mul, Fock.evIh_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_vec (w w') : sympl (c.vec w) (c.vec w') =
    -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) := by
  rw [sympl, real_inner_comm, pPart_vec, qPart_vec, pPart_vec, qPart_vec, c.pair, c.pair, ← Fock.evIh_apply]
  simp only [dotProduct, map_sub, map_sum, map_mul, Fock.evIh_apply]
  ring

/- English proof (translation)
Establish `ha : At (evI F) w.1` using `fun a ha => congrArg Prod.fst (hw a ha)`. Establish `hb : At (evI F) w.2` using `fun a ha => congrArg Prod.snd (hw a ha)`. Use `Der.schr_pure hψ ha hb (c.P f) g 1` as an intermediate fact. Rewrite `this` using `[realAd_one ha, realAd_one hb]`. Rewrite using `[this]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[P_apply, rhoS_apply, Der.hl, phase, real_inner_comm (qPart _), pPart_vec, qPart_vec, c.pair, c.pair, one_smul, P_apply, map_add, Der.linForm_apply, Der.linForm_apply]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_P {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) (f : Sch l)
    (g : (κ → Af F) → ℂ) : schr ψ w (pureA F (c.P f) g) = pureA F (c.P (rhoS (c.vec w) f)) g := by
  have ha : At (evI F) w.1 := fun a ha => congrArg Prod.fst (hw a ha)
  have hb : At (evI F) w.2 := fun a ha => congrArg Prod.snd (hw a ha)
  have := Der.schr_pure hψ ha hb (c.P f) g 1
  rw [realAd_one ha, realAd_one hb] at this
  rw [this]
  congr 1
  funext x
  rw [P_apply, rhoS_apply, Der.hl, phase, real_inner_comm (qPart _), pPart_vec, qPart_vec, c.pair, c.pair, one_smul,
    P_apply, map_add, Der.linForm_apply, Der.linForm_apply]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `: fderiv ℝ (c.P f) x = (fderiv ℝ f (c.e1 x)).comp (c.e1 : _ →L[ℝ] _)` using `c.e1.comp_right_fderiv`. Rewrite using `[P_apply, dRho_apply, pPart_vec, qPart_vec, c.pair, this, P_apply]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem P_dRho (w : (κ → AF F) × (κ → AF F)) (f : Sch l) (x) : c.P (dRho (c.vec w) f) x =
    fderiv ℝ (c.P f) x (fun i => evI F (w.1 i)) - 2 * π * I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (w.2 i)) : ℝ) * c.P f x := by
  have : fderiv ℝ (c.P f) x = (fderiv ℝ f (c.e1 x)).comp (c.e1 : _ →L[ℝ] _) := c.e1.comp_right_fderiv
  rw [P_apply, dRho_apply, pPart_vec, qPart_vec, c.pair, this, P_apply]
  simp
  ring

/- English proof (translation)
Use `letI := fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.LocalData.complRel v`. Set `L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ` to `LinearMap.proj (0 : κ → AF F) ∘ₗ T`. Establish `hl : L ∈ (adeleClass F).adm κ` using `hadm _ (SeminormBoundRestriction.eval_adm 0)`. Set `lf : SInf F κ → ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ` to `fun f => L ∘ₗ { toFun := pureA F f map_add' := fun g g' => by funext x; simp [pureA, mul_add] map_smul' := fun a g => by funext x; simp [pureA, mul_left_comm] }`. Establish `hfi : ∀ f, ∀ g ∈ SB (κ → Af F), g 0 = 0 → lf f g = 0` using `fun f g hg h0 => by`.

Use `eq_zero_of_mul_invariant (lf f) (Set.range fun p : κ × Σ v, Fv F v => fun u => GlobalTheory.VacAny.psiV ψ p.2.1 (evalV F p.2.1 (u p.1) * p.2.2)) ?_ ?_ hg ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨i, v, c⟩, rfl⟩`. Use `GlobalTheory.LocalData.isLocalField v` as an intermediate fact. Use `nonarch_field (Fv F v)` as an intermediate fact. Establish `h1` using `isLocallyConstant_addChar _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v)`.

Conclude with `h1.comp_continuous (((RestrictedProduct.continuous_eval v).comp (continuous_apply i)).mul continuous_const)`. Introduce and unpack `_ ⟨⟨i, v, c⟩, rfl⟩ g hg`. Set `y : κ → AF F` to `Pi.single i (pairA F 0 (singleV F v c))`. Establish `hy : pairA F 0 1 • ((0 : κ → AF F), y) = (0, y)`. Use `Prod.ext (smul_zero _) (funext fun j => ?_)` and prove the remaining obligations.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `only [y, Prod.smul_snd, Pi.smul_apply, Pi.single_eq_same]`. Conclude with `Prod.ext (mul_zero _) (one_mul _)`. Simplify using `[y, h]`.

Establish `h2` using `congrFun (hfin _ hy _ (pure_mem f hg)) 0`. Use `Eq.trans (congrArg L (funext fun x => ?_)) (h2.trans (by simp [schr, lf, L]))` and prove the remaining obligations. Establish `e : x i * pairA F 0 (singleV F v c) = pairA F 0 (singleV F v (evalV F v (x i).2 * c))`. Use `Prod.ext (mul_zero _) (af_ext fun u => ?_)` and prove the remaining obligations. Use `show evalV F u ((x i).2 * singleFin v c) = evalV F u (singleFin v _)`.

Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Rewrite using `[map_mul, evalV_singleFin_self, evalV_singleFin_self]`. Rewrite using `[map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]`. Simplify using `only [schr, y, dotProduct_single, e, Pi.zero_apply, zero_mul, mul_zero, add_zero]`.

Conclude with `mul_left_comm (f _) (ψ _) (g _)`. Introduce `u hu`. Take `⟨i, hi⟩` from `Function.ne_iff.1 (show u ≠ 0 from fun e => hu (e ▸ h0))`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, evalV F v (u i) ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hi (af_ext fun v => (h v).trans (map_zero _).symm)`. Take `⟨y, hy⟩` from `DFunLike.ne_iff.1 (GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v)`. Use `⟨_, ⟨⟨i, v, y / evalV F v (u i)⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.VacAny.psiV ψ v _ ≠ 1`.

Rewrite using `[mul_div_cancel₀ _ hv]` and apply the resulting hypothesis. Establish `hin : ∀ g ∈ SB (κ → Af F), ∃ a : ℂ, ∀ f, lf (c.P (ω f)) g = a * f 0` using `fun g hg => by`. Take `⟨T₀, hT₀⟩` from `hl g hg`. Take `⟨a, ha⟩` from `Delta.eq_delta' (T₀ ∘L c.P ∘L ω) fun m f f' h => by`. Set `q : EuclideanSpace ℝ l` to `(InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap m)`.

Set `w : (κ → AF F) × (κ → AF F)` to `(0, SeminormBoundRestriction.pt (c.e2.symm q) 0)`. Establish `hw : At (evI F) w` using `fun a ha => Prod.ext (smul_zero _) (at_pt _ a ha)`. Establish `h1 : pPart (c.vec w) = 0`. Rewrite using `[pPart_vec, ← map_zero c.e1]`. Conclude with `congrArg c.e1 (funext fun i => Der.evI_zero)`.

Establish `h2 : qPart (c.vec w) = q` using `by rw [qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]`. Establish `e : f' = rhoS (c.vec w) f`. Use extensionality with `x`. Rewrite using `[h, rhoS_apply, phase, h1, h2, add_zero]`. Use `congr 2`.

Simplify using `[q]`. Expand and normalize the polynomial expressions, which then agree. Use `show T₀ _ = T₀ _`. Rewrite using `[← hT₀, ← hT₀, e]`. Conclude with `(congrFun (hinf w hw f g hg) 0).trans (by simp [schr, w, L])`.

Conclude with `⟨a, fun f => (hT₀ _).trans (ha f)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), lf (c.P (ω f)) g = a * (f 0 * g 0) := by`. Distinguish the cases in `h : ∃ g ∈ SB (κ → Af F), g 0 ≠ 0`. Take `⟨g₀, h0, h1⟩` from `h`. Take `⟨a, ha⟩` from `hin g₀ h0`.

Use `⟨a / g₀ 0, fun f g hg => ?_⟩` and prove the remaining obligations. Use `hfi (c.P (ω f)) _ (sub_mem hg (Submodule.smul_mem _ (g 0 / g₀ 0) h0)) (by simp [h1])` as an intermediate fact. Rewrite `this` using `[map_sub, map_smul, sub_eq_zero, ha]`. Rewrite using `[this, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `push Not at h`. Conclude with `⟨0, fun f g hg => by rw [hfi _ g hg (h g hg), zero_mul]⟩`. Use `⟨a, fun f g hg => funext fun x => ?_⟩` and prove the remaining obligations. Set `x1 : κ → AF F` to `SeminormBoundRestriction.pt (fun i => evI F (x i)) 0`. Set `x2 : κ → AF F` to `fun i => pairA F 0 (x i).2`.

Establish `hx : x1 + x2 = x` using `funext fun i => Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)`. Set `g' : (κ → Af F) → ℂ` to `fun u => g (u + fun i => (x i).2)`. Establish `hg' : g' ∈ SB (κ → Af F)` using `⟨hg.1.comp_continuous (continuous_add_const _), hg.2.comp_homeomorph (Homeomorph.addRight _)⟩`. Establish `e1 : ∀ f : SInf F κ, schr ψ (x2, 0) (pureA F f g) = pureA F f g'` using `fun f => by`. Use function extensionality and compare the values at `u`.

Simplify using `only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`. Conclude with `congrArg₂ (· * ·) (congrArg f (funext fun i => congrArg _ (add_zero _))) rfl`. Establish `h1` using `hfin (x2, 0) (Prod.ext (funext fun i => Prod.ext (mul_zero _) (one_mul _)) (smul_zero _)) _ (pure_mem (c.P (ω f)) hg)`. Establish `h2` using `congrFun (hinf (x1, 0) (fun a ha => Prod.ext (at_pt _ a ha) (smul_zero _)) f g' hg') 0`. Rewrite `h2` using `[← e1 (c.P (ω f)), h1]`.

Simplify using `only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, zero_add, hx] at h2`. Rewrite using `[← h2]`. Use `(ha _ g' hg').trans ?_` and prove the remaining obligations. Establish `h3 : qPart (c.vec (x1, 0)) = 0`. Rewrite using `[qPart_vec, ← map_zero c.e2]`.

Conclude with `congrArg c.e2 (funext fun i => Der.evI_zero)`. Rewrite using `[rhoS_apply, phase, h3, pPart_vec, evI_pt]`. Simplify using `[g', pureA, P_apply, evI]`.
-/
theorem schur2 {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) (ω : Sch l →L[ℂ] Sch l)
    (hfin : ∀ w : (κ → AF F) × (κ → AF F), pairA F 0 1 • w = w → ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ))
    (hinf : ∀ w, At (evI F) w → ∀ f, ∀ g ∈ SB (κ → Af F),
      T (pureA F (c.P (ω (rhoS (c.vec w) f))) g) = schr ψ w (T (pureA F (c.P (ω f)) g))) :
    ∃ z : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), T (pureA F (c.P (ω f)) g) = z • pureA F (c.P f) g := by
  letI := fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.LocalData.complRel v
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (0 : κ → AF F) ∘ₗ T
  have hl : L ∈ (adeleClass F).adm κ := hadm _ (SeminormBoundRestriction.eval_adm 0)
  let lf : SInf F κ → ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ := fun f => L ∘ₗ
    { toFun := pureA F f
      map_add' := fun g g' => by funext x; simp [pureA, mul_add]
      map_smul' := fun a g => by funext x; simp [pureA, mul_left_comm] }
  have hfi : ∀ f, ∀ g ∈ SB (κ → Af F), g 0 = 0 → lf f g = 0 := fun f g hg h0 => by
    refine eq_zero_of_mul_invariant (lf f) (Set.range fun p : κ × Σ v, Fv F v => fun u =>
      GlobalTheory.VacAny.psiV ψ p.2.1 (evalV F p.2.1 (u p.1) * p.2.2)) ?_ ?_ hg ?_
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩
      have := GlobalTheory.LocalData.isLocalField v
      have := nonarch_field (Fv F v)
      have h1 := isLocallyConstant_addChar _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v)
      exact h1.comp_continuous (((RestrictedProduct.continuous_eval v).comp (continuous_apply i)).mul continuous_const)
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩ g hg
      let y : κ → AF F := Pi.single i (pairA F 0 (singleV F v c))
      have hy : pairA F 0 1 • ((0 : κ → AF F), y) = (0, y) := by
        refine Prod.ext (smul_zero _) (funext fun j => ?_)
        by_cases h : j = i
        · subst h
          simp only [y, Prod.smul_snd, Pi.smul_apply, Pi.single_eq_same]
          exact Prod.ext (mul_zero _) (one_mul _)
        · simp [y, h]
      have h2 := congrFun (hfin _ hy _ (pure_mem f hg)) 0
      refine Eq.trans (congrArg L (funext fun x => ?_)) (h2.trans (by simp [schr, lf, L]))
      have e : x i * pairA F 0 (singleV F v c) = pairA F 0 (singleV F v (evalV F v (x i).2 * c)) := by
        refine Prod.ext (mul_zero _) (af_ext fun u => ?_)
        show evalV F u ((x i).2 * singleFin v c) = evalV F u (singleFin v _)
        by_cases h : u = v
        · subst h; rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]
        · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]
      simp only [schr, y, dotProduct_single, e, Pi.zero_apply, zero_mul, mul_zero, add_zero]
      exact mul_left_comm (f _) (ψ _) (g _)
    · intro u hu
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (show u ≠ 0 from fun e => hu (e ▸ h0))
      obtain ⟨v, hv⟩ : ∃ v, evalV F v (u i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hi (af_ext fun v => (h v).trans (map_zero _).symm)
      obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 (GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v)
      refine ⟨_, ⟨⟨i, v, y / evalV F v (u i)⟩, rfl⟩, ?_⟩
      show GlobalTheory.VacAny.psiV ψ v _ ≠ 1
      rwa [mul_div_cancel₀ _ hv]
  have hin : ∀ g ∈ SB (κ → Af F), ∃ a : ℂ, ∀ f, lf (c.P (ω f)) g = a * f 0 := fun g hg => by
    obtain ⟨T₀, hT₀⟩ := hl g hg
    obtain ⟨a, ha⟩ := Delta.eq_delta' (T₀ ∘L c.P ∘L ω) fun m f f' h => by
      let q : EuclideanSpace ℝ l := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap m)
      let w : (κ → AF F) × (κ → AF F) := (0, SeminormBoundRestriction.pt (c.e2.symm q) 0)
      have hw : At (evI F) w := fun a ha => Prod.ext (smul_zero _) (at_pt _ a ha)
      have h1 : pPart (c.vec w) = 0 := by
        rw [pPart_vec, ← map_zero c.e1]
        exact congrArg c.e1 (funext fun i => Der.evI_zero)
      have h2 : qPart (c.vec w) = q := by rw [qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]
      have e : f' = rhoS (c.vec w) f := by
        ext x
        rw [h, rhoS_apply, phase, h1, h2, add_zero]
        congr 2
        simp [q]
        ring
      show T₀ _ = T₀ _
      rw [← hT₀, ← hT₀, e]
      exact (congrFun (hinf w hw f g hg) 0).trans (by simp [schr, w, L])
    exact ⟨a, fun f => (hT₀ _).trans (ha f)⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), lf (c.P (ω f)) g = a * (f 0 * g 0) := by
    by_cases h : ∃ g ∈ SB (κ → Af F), g 0 ≠ 0
    · obtain ⟨g₀, h0, h1⟩ := h
      obtain ⟨a, ha⟩ := hin g₀ h0
      refine ⟨a / g₀ 0, fun f g hg => ?_⟩
      have := hfi (c.P (ω f)) _ (sub_mem hg (Submodule.smul_mem _ (g 0 / g₀ 0) h0)) (by simp [h1])
      rw [map_sub, map_smul, sub_eq_zero, ha] at this
      rw [this, smul_eq_mul]; ring
    · push Not at h
      exact ⟨0, fun f g hg => by rw [hfi _ g hg (h g hg), zero_mul]⟩
  refine ⟨a, fun f g hg => funext fun x => ?_⟩
  let x1 : κ → AF F := SeminormBoundRestriction.pt (fun i => evI F (x i)) 0
  let x2 : κ → AF F := fun i => pairA F 0 (x i).2
  have hx : x1 + x2 = x := funext fun i => Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)
  let g' : (κ → Af F) → ℂ := fun u => g (u + fun i => (x i).2)
  have hg' : g' ∈ SB (κ → Af F) :=
    ⟨hg.1.comp_continuous (continuous_add_const _), hg.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have e1 : ∀ f : SInf F κ, schr ψ (x2, 0) (pureA F f g) = pureA F f g' := fun f => by
    funext u
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
    exact congrArg₂ (· * ·) (congrArg f (funext fun i => congrArg _ (add_zero _))) rfl
  have h1 := hfin (x2, 0) (Prod.ext (funext fun i => Prod.ext (mul_zero _) (one_mul _)) (smul_zero _)) _
    (pure_mem (c.P (ω f)) hg)
  have h2 := congrFun (hinf (x1, 0) (fun a ha => Prod.ext (at_pt _ a ha) (smul_zero _)) f g' hg') 0
  rw [← e1 (c.P (ω f)), h1] at h2
  simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, zero_add, hx] at h2
  rw [← h2]
  refine (ha _ g' hg').trans ?_
  have h3 : qPart (c.vec (x1, 0)) = 0 := by
    rw [qPart_vec, ← map_zero c.e2]
    exact congrArg c.e2 (funext fun i => Der.evI_zero)
  rw [rhoS_apply, phase, h3, pPart_vec, evI_pt]
  simp [g', pureA, P_apply, evI]

end Co

end PositivityTheory.RL.Up

end
