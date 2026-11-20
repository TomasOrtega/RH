import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.FockActionFirstEq
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsCharNe

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Comp

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG PositivityTheory.ThKF GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`.
-/
theorem map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

/- English proof (translation)
Establish `h1 : Jm P Q * Jm P Q = 1`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`. Establish `h2 : (Jm P Q)ᴴ = Jm P Q`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`. Establish `h3 : ∀ A : Mat P Q, Jm P Q * (Jm P Q * A) = A` using `fun A => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Use `⟨(1 / 2 : ℂ) • (Y - Jm P Q * Yᴴ * Jm P Q), ?_, (-Complex.I / 2) • (Y + Jm P Q * Yᴴ * Jm P Q), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h3, Matrix.mul_one]`. Rewrite using `[show star (1 / 2 : ℂ) = 1 / 2 by simp]`. Use `module`. Simplify using `only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h1, h3, Matrix.mul_one]`.

Rewrite using `[show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]`. Use `module`. Rewrite using `[smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I] module`.
-/
theorem upq_span {P Q : ℕ} (Y : Mat P Q) : ∃ Y₁ ∈ upq P Q, ∃ Y₂ ∈ upq P Q, Y = Y₁ + Complex.I • Y₂ := by
  have h1 : Jm P Q * Jm P Q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have h2 : (Jm P Q)ᴴ = Jm P Q := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h3 : ∀ A : Mat P Q, Jm P Q * (Jm P Q * A) = A := fun A => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm P Q * Yᴴ * Jm P Q), ?_, (-Complex.I / 2) • (Y + Jm P Q * Yᴴ * Jm P Q), ?_, ?_⟩
  · simp only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h3,
      Matrix.mul_one]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp]
    module
  · simp only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h1, h3,
      Matrix.mul_one]
    rw [show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

/- English proof (translation)
Establish `e : ∀ i, atPl (V` using `fun _ => V) i (L i) (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ (Function.update g i (L i (g i))) := fun i => by`. Rewrite using `[atPl, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hj]`. Rewrite using `[sumPl, LinearMap.sum_apply, Finset.sum_eq_single w (fun i _ hi => by`. Rewrite using `[e, h i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]) (by simp), e]`.
-/
theorem sumPl_single {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (L : ι → Module.End ℂ V) (w : ι)
    (h : ∀ i ≠ w, L i = 0) (g : ι → V) :
    sumPl (V := fun _ => V) L (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ (Function.update g w (L w (g w))) := by
  have e : ∀ i, atPl (V := fun _ => V) i (L i) (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ (Function.update g i (L i (g i))) :=
    fun i => by
      rw [atPl, PiTensorProduct.map_tprod]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
  rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w (fun i _ hi => by
    rw [e, h i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]) (by simp), e]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp m hm hd hr L hinv`. Use `choose A hA' hAθ using fun w => hFr _ _ _ _ _ (hp.herm.sig w) (hp.herm.cartan w)`. Use `choose C hC hCθ using fun w => hFr _ _ _ _ _ (hp.skew.sig w) (hp.skew.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)` using `fun w => by`. Rewrite using `[map_piInf, one_smul]`.

Conclude with `hA' w`. Establish `fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, fun w => by rw [map_piInf]; exact hC w⟩`. Take `⟨Φ, hΦ⟩` from `hFo F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hp.base.cm hp.base.std fr`. Establish `hrg` using `hP F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hp.base.cm hp.base.std fr hAθ hCθ hΦ`. Establish `hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om` using `hp.weil`.

Take `⟨d', hd', hB1⟩` from `hwp.2.1`. Establish `hact` using `hLie F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co d' 1 Complex.I A C Φ _ _ _ hp.base.cm hp.base.std fr hΦ hd' hB1 hm`. Take `⟨l, hl, hl'⟩` from `PositivityTheory.ThKF.A.exists_adm L`. Take `⟨g₀, hg₀, hg₁⟩` from `PositivityTheory.ThKF.A.exists_sb_one (F := F) (κ := Fin n × Fin d)`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `key : ∀ g, L (Φ (PiTensorProduct.tprod ℂ g)) = 0` using `fun g => by`. Set `l₀ : Pol r s r' s' →ₗ[ℂ] ℂ` to `L.toLinearMap ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap g w`. Establish `h1 : ∀ Y ∈ upq r s, ∀ f, l₀ (fockAct1 r s r' s' Y f) = -((m w : ℂ) / 2 * Y.trace) * l₀ f` using `fun Y hY f => by`. Take `⟨γ, hγ, hgen⟩` from `hL F E σ (Fin n) r s B.emb (incM F X.J) 1 A hp.base.cm hA1 (Pi.single w Y) fun v => by`. Distinguish the cases in `hv : v = w`.

Substitute `hv` using the available equality. Simplify using `using hY`. Simplify using `[Pi.single_eq_of_ne hv, upq]`. Establish `h2` using `hact γ hγ _ hgen (PiTensorProduct.tprod ℂ (Function.update g w f)) g₀ hg₀ l hl`. Establish `h3 : (fun t : ℝ => l ((om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t)) (pureA F (Φ (PiTensorProduct.tprod ℂ (Function.update g w f))) g₀))) = fun _ => L (Φ (PiTensorProduct.tprod ℂ (Function.update g w f)))` using `funext fun t => by`.

Take `⟨T, hT, -⟩` from `hA F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 (fun u _ => by simp [mat])`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.inl_apply, hT.1 _ _ hg₀, hl' _ _ hg₀, hg₁, one_mul, hinv _ (hγ.2 (Multiplicative.ofAdd t)) T hT]`. Rewrite `h2` using `[h3]`. Establish `h4` using `h2.unique (hasDerivAt_const _ _)`. Rewrite `h4` using `[hl' _ _ hg₀, hg₁, one_mul, sumPl_single _ w (fun i hi => by simp [Pi.single_eq_of_ne hi]), Function.update_idem, Function.update_self, Pi.single_eq_same]`.

Establish `h5 : l₀ ((fockAct1 r s r' s' Y + ((m w : ℂ) / 2 * Y.trace) • 1 : Module.End ℂ _) f) = 0` using `h4`. Rewrite `h5` using `[LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.one_apply]`. Take the linear combination `h5`. Establish `h0` using `noForm (m w) ((hp.skew.sig w).1 ▸ hd w) hr l₀ fun Y _ f => by`. Take `⟨Y₁, a, Y₂, b, rfl⟩` from `upq_span Y`.

Rewrite using `[map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, h1 _ a, h1 _ b, Matrix.trace_add, Matrix.trace_smul]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify `LinearMap.congr_fun h0 (g w)` using `[l₀]`. Establish `k2 : ∀ T, L (Φ T) = 0` using `fun T => by`.

Proceed by induction on `T using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c g => rw [map_smul, map_smul, key, smul_zero]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`. Use `ContinuousLinearMap.ext fun f => congrFun (Continuous.ext_on (hD F E σ B n d X W M χX χW om r s r' s' hp) L.continuous continuous_zero fun f hf => ?_) f` and prove the remaining obligations. Rewrite `hf` using `[← hrg]`.

Take `⟨T, rfl⟩` from `hf`. Conclude with `k2 T`.
-/
theorem realVanish_of (hA : ArchOp) (hD : PolDense) (hFr : FrameEx) (hFo : FockEx) (hL : LineEx) (hP : PolRange) (hLie : LieFirst) :
    RealVanish := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp m hm hd hr L hinv
  choose A hA' hAθ using fun w => hFr _ _ _ _ _ (hp.herm.sig w) (hp.herm.cartan w)
  choose C hC hCθ using fun w => hFr _ _ _ _ _ (hp.skew.sig w) (hp.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [map_piInf, one_smul]; exact hA' w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, fun w => by rw [map_piInf]; exact hC w⟩
  obtain ⟨Φ, hΦ⟩ := hFo F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hp.base.cm hp.base.std fr
  have hrg := hP F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hp.base.cm hp.base.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hp.weil
  obtain ⟨d', hd', hB1⟩ := hwp.2.1
  have hact := hLie F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co d' 1 Complex.I A C Φ _ _ _ hp.base.cm hp.base.std fr hΦ hd' hB1 hm
  obtain ⟨l, hl, hl'⟩ := PositivityTheory.ThKF.A.exists_adm L
  obtain ⟨g₀, hg₀, hg₁⟩ := PositivityTheory.ThKF.A.exists_sb_one (F := F) (κ := Fin n × Fin d)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : ∀ g, L (Φ (PiTensorProduct.tprod ℂ g)) = 0 := fun g => by
    let l₀ : Pol r s r' s' →ₗ[ℂ] ℂ := L.toLinearMap ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap g w
    have h1 : ∀ Y ∈ upq r s, ∀ f, l₀ (fockAct1 r s r' s' Y f) = -((m w : ℂ) / 2 * Y.trace) * l₀ f := fun Y hY f => by
      obtain ⟨γ, hγ, hgen⟩ := hL F E σ (Fin n) r s B.emb (incM F X.J) 1 A hp.base.cm hA1 (Pi.single w Y) fun v => by
        by_cases hv : v = w
        · subst hv; simpa using hY
        · simp [Pi.single_eq_of_ne hv, upq]
      have h2 := hact γ hγ _ hgen (PiTensorProduct.tprod ℂ (Function.update g w f)) g₀ hg₀ l hl
      have h3 : (fun t : ℝ => l ((om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t))
          (pureA F (Φ (PiTensorProduct.tprod ℂ (Function.update g w f))) g₀))) =
          fun _ => L (Φ (PiTensorProduct.tprod ℂ (Function.update g w f))) := funext fun t => by
        obtain ⟨T, hT, -⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 (fun u _ => by simp [mat])
        rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hT.1 _ _ hg₀, hl' _ _ hg₀, hg₁, one_mul,
          hinv _ (hγ.2 (Multiplicative.ofAdd t)) T hT]
      rw [h3] at h2
      have h4 := h2.unique (hasDerivAt_const _ _)
      rw [hl' _ _ hg₀, hg₁, one_mul, sumPl_single _ w (fun i hi => by simp [Pi.single_eq_of_ne hi]), Function.update_idem,
        Function.update_self, Pi.single_eq_same] at h4
      have h5 : l₀ ((fockAct1 r s r' s' Y + ((m w : ℂ) / 2 * Y.trace) • 1 : Module.End ℂ _) f) = 0 := h4
      rw [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.one_apply] at h5
      linear_combination h5
    have h0 := noForm (m w) ((hp.skew.sig w).1 ▸ hd w) hr l₀ fun Y _ f => by
      obtain ⟨Y₁, a, Y₂, b, rfl⟩ := upq_span Y
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, h1 _ a, h1 _ b, Matrix.trace_add,
        Matrix.trace_smul]
      simp only [smul_eq_mul]
      ring
    simpa [l₀] using LinearMap.congr_fun h0 (g w)
  have k2 : ∀ T, L (Φ T) = 0 := fun T => by
    induction T using PiTensorProduct.induction_on with
    | smul_tprod c g => rw [map_smul, map_smul, key, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  refine ContinuousLinearMap.ext fun f => congrFun (Continuous.ext_on (hD F E σ B n d X W M χX χW om r s r' s' hp)
    L.continuous continuous_zero fun f hf => ?_) f
  rw [← hrg] at hf
  obtain ⟨T, rfl⟩ := hf
  exact k2 T

end PositivityTheory.ThKEnd.Comp

end
