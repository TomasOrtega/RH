import Development.WeilBound.ThetaLifts.LeviDeterminants.CartanPos
import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsGaussBox

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt Lib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ r s r' s' i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {H : Plane E d d₁}

def Dp (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) : SInf F (Fin n × Fin d) :=
  dop (aOf M u) (lOf M u) f

def Gs (B : Base F E) (M : Model σ X W) (e : InfinitePlace F → ℤˣ) (f : SInf F (Fin n × Fin d)) : Prop :=
  ∀ u u', At (evI F) u → At (evI F) u' → Rel B X W e u u' → Dp M u' f = Complex.I • Dp M u f

/- English proof (translation)
The claim follows from `exists_congr fun _ => forall₂_congr fun _ _ => forall₃_congr fun hu hu' _ => ⟨fun h => h _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f), fun h _ _ hg hg' => by rw [actsD_unique M hB.std hu hg, actsD_unique M hB.std hu' hg']; exact h⟩`.
-/
theorem gauss_iff (hB : B.IsGood σ) (M : Model σ X W) (f) : M.IsGauss B.ψ B.emb f ↔ ∃ e, Gs B M e f :=
  exists_congr fun _ => forall₂_congr fun _ _ => forall₃_congr fun hu hu' _ =>
    ⟨fun h => h _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f), fun h _ _ hg hg' => by
      rw [actsD_unique M hB.std hu hg, actsD_unique M hB.std hu' hg']; exact h⟩

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun _ hN => hN.1 f ((gauss_iff hB M f).2 ⟨e, h⟩)`.
-/
theorem pol_gs (hB : B.IsGood σ) {M : Model σ X W} {e f} (h : Gs B M e f) : f ∈ M.Pol B.ψ B.emb :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f ((gauss_iff hB M f).2 ⟨e, h⟩)

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 h N hN) _ (actsD_dop M hB.std hu f)`.
-/
theorem pol_Dp (hB : B.IsGood σ) {M : Model σ X W} {u f} (hu : At (evI F) u) (h : f ∈ M.Pol B.ψ B.emb) :
    Dp M u f ∈ M.Pol B.ψ B.emb :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 h N hN) _ (actsD_dop M hB.std hu f)

/- English proof (translation)
The claim follows from `sInf_le ⟨fun f hf => by obtain ⟨e, he⟩ := (gauss_iff hB M f).1 hf; exact h1 e f he, fun u hu f hf _ h => by rw [actsD_unique M hB.std hu h]; exact h2 u hu f hf⟩`.
-/
theorem pol_le (hB : B.IsGood σ) {M : Model σ X W} {N : Submodule ℂ (SInf F (Fin n × Fin d))} (h1 : ∀ e f, Gs B M e f → f ∈ N)
    (h2 : ∀ u, At (evI F) u → ∀ f ∈ N, Dp M u f ∈ N) : M.Pol B.ψ B.emb ≤ N :=
  sInf_le ⟨fun f hf => by obtain ⟨e, he⟩ := (gauss_iff hB M f).1 hf; exact h1 e f he,
    fun u hu f hf _ h => by rw [actsD_unique M hB.std hu h]; exact h2 u hu f hf⟩

/- English proof (translation)
Rewrite using `[Dp, aOf_add, lOf_add, dop_add]`. Both sides reduce to the same expression.
-/
theorem Dp_add (M : Model σ X W) (u u' f) : Dp M (u + u') f = Dp M u f + Dp M u' f := by
  rw [Dp, aOf_add, lOf_add, dop_add]; rfl

/- English proof (translation)
Use `aOf_add M 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`.
-/
theorem aOf_zero (M : Model σ X W) : aOf M 0 = 0 := by
  have := aOf_add M 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

/- English proof (translation)
The claim follows from `eq_neg_of_add_eq_zero_left (by rw [← aOf_add, neg_add_cancel, aOf_zero])`.
-/
theorem aOf_neg (M : Model σ X W) (u) : aOf M (-u) = -aOf M u :=
  eq_neg_of_add_eq_zero_left (by rw [← aOf_add, neg_add_cancel, aOf_zero])

/- English proof (translation)
Use `lOf_add M 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `eq_neg_of_add_eq_zero_left (by rw [← lOf_add, neg_add_cancel, left_eq_add.1 this])`.
-/
theorem lOf_neg (M : Model σ X W) (u) : lOf M (-u) = -lOf M u := by
  have := lOf_add M 0 0
  rw [add_zero] at this
  exact eq_neg_of_add_eq_zero_left (by rw [← lOf_add, neg_add_cancel, left_eq_add.1 this])

/- English proof (translation)
Rewrite using `[omega, M.co.form u u', evI_sub, map_sub]`. Simplify using `only [lOf, aOf, linForm_apply, dotProduct, evI_sum, evI_mul]`.
-/
theorem omega_co (M : Model σ X W) (u u') : omega σ X W u u' = lOf M u' (aOf M u) - lOf M u (aOf M u') := by
  rw [omega, M.co.form u u', evI_sub, map_sub]
  simp only [lOf, aOf, linForm_apply, dotProduct, evI_sum, evI_mul]

/- English proof (translation)
Rewrite using `[linForm_apply, linForm_apply, linForm_apply, ← map_add]`. Conclude with `congrArg _ (glue_dot ε a q y c)`.
-/
theorem lin_glue {κ κ₀ κ₁ : Type} [Fintype κ] [Fintype κ₀] [Fintype κ₁] (ε : κ ≃ κ₀ ⊕ κ₁) (q a : κ₀ → mixedEmbedding.mixedSpace F)
    (c y : κ₁ → mixedEmbedding.mixedSpace F) : linForm (glue ε q c) (glue ε a y) = linForm q a + linForm c y := by
  rw [linForm_apply, linForm_apply, linForm_apply, ← map_add]
  exact congrArg _ (glue_dot ε a q y c)

/- English proof (translation)
Use extensionality with `y`. Simplify using `[linForm_apply]`.
-/
theorem lin_zero {κ : Type} [Fintype κ] : linForm (0 : κ → mixedEmbedding.mixedSpace F) = 0 := by
  ext y; simp [linForm_apply]

/- English proof (translation)
The claim follows from `funext fun _ => evI_zero`.
-/
theorem evI_fun_zero {κ : Type} : (fun k : κ => evI F ((0 : κ → AF F) k)) = 0 := funext fun _ => evI_zero

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, GlobalTheory.CompanionTheory.Ar.RT.Lie.piInf_inclR]`.
-/
theorem map_pure (w : InfinitePlace F) (a : Fin n → AE F E) (b : Fin d → E) :
    (Matrix.vecMulVec a (incV F b)).map (piInf (B.emb w)) =
      Matrix.vecMulVec (fun i => piInf (B.emb w) (a i)) fun i => (B.emb w).1 (b i) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, GlobalTheory.CompanionTheory.Ar.RT.Lie.piInf_inclR]

/- English proof (translation)
Introduce `t ht` and use `by rw [← Matrix.smul_vecMulVec, ha t ht, Matrix.zero_vecMulVec]`.
-/
theorem at_pure {a : Fin n → AE F E} (ha : At (evI F) a) (b : Fin d → AE F E) : At (evI F) (Matrix.vecMulVec a b) := fun t ht => by
  rw [← Matrix.smul_vecMulVec, ha t ht, Matrix.zero_vecMulVec]

/- English proof (translation)
Introduce `t ht` and use `by rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]`.
-/
theorem at_mul' {α β γ : Type} [Fintype β] {u : Matrix α β (AE F E)} (hu : At (evI F) u) (N : Matrix β γ (AE F E)) :
    At (evI F) (u * N) := fun t ht => by rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

/- English proof (translation)
Take `⟨Q, h1, -, -⟩` from `exists_frame_inv hH hW.lat`. Establish `hw` using `at_mul' hu (incM F Q)ᵀ`. Establish `e : u = u * (incM F Q)ᵀ * (incM F (frame H))ᵀ`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, h1, incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one]`. Generalize the expression as in `u * (incM F Q)ᵀ = w at hw e`.

Use `⟨fun i => w i (.inr 0), w.submatrix id .inl, fun i => w i (.inr 1), fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _, fun t ht => Matrix.ext fun i j => congrFun (congrFun (hw t ht) i) _, fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use extensionality with `i j`. Simplify using `[frame, incM, incV, Matrix.mul_apply, Matrix.vecMulVec_apply, Fintype.sum_sum_type, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    ∃ (a : Fin n → AE F E) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (b : Fin n → AE F E), At (evI F) a ∧ At (evI F) z ∧ At (evI F) b ∧
      u = Matrix.vecMulVec a (incV F H.x) + z * (incM F H.ι)ᵀ + Matrix.vecMulVec b (incV F H.y) := by
  obtain ⟨Q, h1, -, -⟩ := exists_frame_inv hH hW.lat
  have hw := at_mul' hu (incM F Q)ᵀ
  have e : u = u * (incM F Q)ᵀ * (incM F (frame H))ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, h1, incM, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.mul_one]
  generalize u * (incM F Q)ᵀ = w at hw e
  refine ⟨fun i => w i (.inr 0), w.submatrix id .inl, fun i => w i (.inr 1),
    fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _,
    fun t ht => Matrix.ext fun i j => congrFun (congrFun (hw t ht) i) _,
    fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _, ?_⟩
  rw [e]
  ext i j
  simp [frame, incM, incV, Matrix.mul_apply, Matrix.vecMulVec_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

/- English proof (translation)
Introduce `w` and use `by have h1 : ((incM F H.ι)ᵀ).map (piInf (B.emb w)) = (H.ι.map (B.emb w).1)ᵀ := by ext i j; exact GlobalTheory.CompanionTheory.Ar.RT.Lie.piInf_inclR _ _ have h2 := congrArg Matrix.transpose (hH.cartan w).1 rw [Matrix.transpose_mul, Matrix.transpose_mul] at h2 rw [Matrix.map_mul, M …`.
-/
theorem rel_iota (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e} {z z' : Matrix (Fin n) (Fin d₁) (AE F E)} (h : Rel B X W₁ e z z') :
    Rel B X W e (z * (incM F H.ι)ᵀ) (z' * (incM F H.ι)ᵀ) := fun w => by
  have h1 : ((incM F H.ι)ᵀ).map (piInf (B.emb w)) = (H.ι.map (B.emb w).1)ᵀ := by
    ext i j; exact GlobalTheory.CompanionTheory.Ar.RT.Lie.piInf_inclR _ _
  have h2 := congrArg Matrix.transpose (hH.cartan w).1
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, h1, h w, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, h2]

/- English proof (translation)
Take `⟨b, h1, h2⟩` from `exists_vec hB fun w => (((e w : ℤ) : ℂ) * Complex.I * c w) • X.θ w *ᵥ fun i => piInf (B.emb w) (a i)`. Use `⟨b, h1, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[map_pure, map_pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h w]`. Use extensionality with `i j`. Simplify using `only [h2, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_pure (hB : B.IsGood σ) (e) {x y : Fin d → E} (c : InfinitePlace F → ℂ)
    (h : ∀ w, W.θ w *ᵥ (fun i => (B.emb w).1 (x i)) = c w • fun i => (B.emb w).1 (y i)) (a : Fin n → AE F E) :
    ∃ b, At (evI F) b ∧ Rel B X W e (Matrix.vecMulVec a (incV F x)) (Matrix.vecMulVec b (incV F y)) := by
  obtain ⟨b, h1, h2⟩ := exists_vec hB fun w => (((e w : ℤ) : ℂ) * Complex.I * c w) • X.θ w *ᵥ fun i => piInf (B.emb w) (a i)
  refine ⟨b, h1, fun w => ?_⟩
  rw [map_pure, map_pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h w]
  ext i j
  simp only [h2, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `choose c _ hc using fun w => (hH.cartan w).2`. Conclude with `rel_pure hB e c (fun w => by rw [hc w, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (hW.cartan w).1, Matrix.one_mulVec]) b`.
-/
theorem rel_y (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) (e) (b : Fin n → AE F E) :
    ∃ a, At (evI F) a ∧ Rel B X W e (Matrix.vecMulVec b (incV F H.y)) (Matrix.vecMulVec a (incV F H.x)) := by
  choose c _ hc using fun w => (hH.cartan w).2
  exact rel_pure hB e c (fun w => by rw [hc w, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (hW.cartan w).1, Matrix.one_mulVec]) b

/- English proof (translation)
Use `choose c h0 hc using fun w => (hH.cartan w).2`. Conclude with `rel_pure hB e (fun w => (c w)⁻¹) (fun w => by rw [hc w, inv_smul_smul₀ (h0 w)]) a`.
-/
theorem exists_relation_adapted_vector (hB : B.IsGood σ) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (e) (a : Fin n → AE F E) :
    ∃ b, At (evI F) b ∧ Rel B X W e (Matrix.vecMulVec a (incV F H.x)) (Matrix.vecMulVec b (incV F H.y)) := by
  choose c h0 hc using fun w => (hH.cartan w).2
  exact rel_pure hB e (fun w => (c w)⁻¹) (fun w => by rw [hc w, inv_smul_smul₀ (h0 w)]) a

variable {κ₀ : Type} [Fintype κ₀] {ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁} {Ma : Model σ X W} {M₁ : Model σ X W₁}

structure Adp (H : Plane E d d₁) (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁) (Ma : Model σ X W) (M₁ : Model σ X W₁) : Prop where
  i : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), Ma.co.e (z * (incM F H.ι)ᵀ) = (glue ε 0 (M₁.co.e z).1, glue ε 0 (M₁.co.e z).2)
  x : ∀ y, ∃ q, Ma.co.e (Matrix.vecMulVec y (incV F H.x)) = (0, glue ε q 0)
  y : ∀ y, ∃ p, Ma.co.e (Matrix.vecMulVec y (incV F H.y)) = (glue ε p 0, 0)

namespace Adp

variable (h : Adp H ε Ma M₁)
include h

/- English proof (translation)
Unfold `aOf`. Rewrite using `[h.i, glue_map ε (evI F), evI_fun_zero]`.
-/
theorem ai (z : Matrix (Fin n) (Fin d₁) (AE F E)) : aOf Ma (z * (incM F H.ι)ᵀ) = glue ε 0 (aOf M₁ z) := by
  unfold aOf
  rw [h.i, glue_map ε (evI F), evI_fun_zero]

/- English proof (translation)
Unfold `lOf`. Rewrite using `[h.i, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, zero_add]`.
-/
theorem li (z : Matrix (Fin n) (Fin d₁) (AE F E)) (a y) : lOf Ma (z * (incM F H.ι)ᵀ) (glue ε a y) = lOf M₁ z y := by
  unfold lOf
  rw [h.i, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, zero_add]

/- English proof (translation)
Take `⟨q, hq⟩` from `h.x a`. Use `⟨fun k => evI F (q k), ?_, fun t y => ?_⟩` and prove the remaining obligations. Unfold `aOf`. Rewrite using `[hq, evI_fun_zero]`. Unfold `lOf`.

Rewrite using `[hq, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, add_zero]`.
-/
theorem cx (a) : ∃ q, aOf Ma (Matrix.vecMulVec a (incV F H.x)) = 0 ∧
    ∀ t y, lOf Ma (Matrix.vecMulVec a (incV F H.x)) (glue ε t y) = linForm q t := by
  obtain ⟨q, hq⟩ := h.x a
  refine ⟨fun k => evI F (q k), ?_, fun t y => ?_⟩
  · unfold aOf
    rw [hq, evI_fun_zero]
  · unfold lOf
    rw [hq, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, add_zero]

/- English proof (translation)
Take `⟨p, hp⟩` from `h.y b`. Use `⟨fun k => evI F (p k), ?_, ?_⟩` and prove the remaining obligations. Unfold `aOf`. Rewrite using `[hp, glue_map ε (evI F), evI_fun_zero]`. Unfold `lOf`.

Rewrite using `[hp, evI_fun_zero, lin_zero]`.
-/
theorem cy (b) : ∃ p, aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε p 0 ∧ lOf Ma (Matrix.vecMulVec b (incV F H.y)) = 0 := by
  obtain ⟨p, hp⟩ := h.y b
  refine ⟨fun k => evI F (p k), ?_, ?_⟩
  · unfold aOf
    rw [hp, glue_map ε (evI F), evI_fun_zero]
  · unfold lOf
    rw [hp, evI_fun_zero, lin_zero]

/- English proof (translation)
Rewrite using `[Dp, h.ai]`. Conclude with `slice_dop ε f g a hg _ _ (h.li z a) _ y`.
-/
theorem slice {f g a} (hg : ∀ y, g y = f (glue ε a y)) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (y) : Dp Ma (z * (incM F H.ι)ᵀ) f (glue ε a y) = Dp M₁ z g y := by
  rw [Dp, h.ai]
  exact slice_dop ε f g a hg _ _ (h.li z a) _ y

/- English proof (translation)
Establish `h0 : At (evI F) (Ma.co.e.symm (glue ε (pt t 0) 0, 0))` using `fun c hc => by`. Establish `h1 : c.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hc.trans (map_zero _).symm)`. Establish `h2 : c • pt t 0 = 0` using `funext fun k => Prod.ext (by change c.1 * _ = 0; rw [h1, zero_mul]) (by change c.2 * 0 = 0; rw [mul_zero])`. Rewrite using `[← map_smul, Prod.smul_mk, glue_smul, h2, smul_zero, smul_zero, glue_zero, Prod.mk_zero_zero, map_zero]`. Take `⟨a, z, b, -, -, hb, e⟩` from `decomp hW hH h0`.

Establish `h1` using `congrArg (aOf Ma) e`. Take `⟨q, hq, -⟩` from `h.cx a`. Take `⟨p, hp, -⟩` from `h.cy b`. Rewrite `h1` using `[aOf_add, aOf_add, hq, h.ai, hp, zero_add, glue_add, zero_add]`. Use `⟨b, hb, hp.trans ?_⟩` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `k`. Use `congrFun h1 (ε.symm (.inl k))` as an intermediate fact. Rewrite `this` using `[glue_inl, aOf, LinearEquiv.apply_symm_apply]`. Simplify using `only [glue_inl] at this`.

Rewrite using `[← this]`. Conclude with `congrFun (evI_pt t 0) k`.
-/
theorem onto (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : κ₀ → mixedEmbedding.mixedSpace F) :
    ∃ b, At (evI F) b ∧ aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε t 0 := by
  have h0 : At (evI F) (Ma.co.e.symm (glue ε (pt t 0) 0, 0)) := fun c hc => by
    have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hc.trans (map_zero _).symm)
    have h2 : c • pt t 0 = 0 := funext fun k => Prod.ext (by change c.1 * _ = 0; rw [h1, zero_mul]) (by change c.2 * 0 = 0; rw [mul_zero])
    rw [← map_smul, Prod.smul_mk, glue_smul, h2, smul_zero, smul_zero, glue_zero, Prod.mk_zero_zero, map_zero]
  obtain ⟨a, z, b, -, -, hb, e⟩ := decomp hW hH h0
  have h1 := congrArg (aOf Ma) e
  obtain ⟨q, hq, -⟩ := h.cx a
  obtain ⟨p, hp, -⟩ := h.cy b
  rw [aOf_add, aOf_add, hq, h.ai, hp, zero_add, glue_add, zero_add] at h1
  refine ⟨b, hb, hp.trans ?_⟩
  congr 1
  funext k
  have := congrFun h1 (ε.symm (.inl k))
  rw [glue_inl, aOf, LinearEquiv.apply_symm_apply] at this
  simp only [glue_inl] at this
  rw [← this]
  exact congrFun (evI_pt t 0) k

/- English proof (translation)
Introduce `z z' hz hz' hr` and use `by ext y rw [SchwartzMap.smul_apply, ← h.slice hg, ← h.slice hg, hf _ _ (at_mul' hz _) (at_mul' hz' _) (rel_iota hH hr)] rfl`.
-/
theorem gs_slice (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e f g} (hf : Gs B Ma e f) (hg : ∀ y, g y = f (glue ε 0 y)) : Gs B M₁ e g :=
  fun z z' hz hz' hr => by
    ext y
    rw [SchwartzMap.smul_apply, ← h.slice hg, ← h.slice hg, hf _ _ (at_mul' hz _) (at_mul' hz' _) (rel_iota hH hr)]
    rfl

/- English proof (translation)
Set `S : Set (SInf F (Fin n × Fin d))` to `{f | ∃ g ∈ M₁.Pol B.ψ B.emb, ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y}`. Establish `h1 : Ma.Pol B.ψ B.emb ≤ Submodule.span ℂ S`. Use `pol_le hB (fun e f hf => Submodule.subset_span ⟨T f, pol_gs hB (h.gs_slice hH hf (hT f)), fun t => ?_⟩) fun u hu f hf => ?_` and prove the remaining obligations. Take `⟨b, hb, hp⟩` from `h.onto hW hH t`. Take `⟨-, -, hl⟩` from `h.cy b`.

Take `⟨a, ha, hr⟩` from `rel_y (X := X) hB hW hH e b`. Take `⟨q, hq, hq'⟩` from `h.cx a`. Establish `key` using `hf _ _ (at_pure hb _) (at_pure ha _) hr`. Use `⟨_, fun y => (slice_ode ε f t (Real.pi * linForm q t) (fun c y => ?_) y).trans (by rw [hT])⟩` and prove the remaining obligations. Use `DFunLike.congr_fun key (glue ε (c • t) y)` as an intermediate fact.

Simplify using `only [Dp, SchwartzMap.smul_apply, dop_apply, hq, hq', hp, hl, map_zero, map_smul, ContinuousLinearMap.zero_apply, smul_eq_mul] at this`. Move the coercions through the operations in `at this ⊢`. Take the linear combination `Complex.I * this + (fderiv ℝ f (glue ε (c • t) y) (glue ε t 0) + 2 * Real.pi * c * linForm q t * f (glue ε (c • t) y)) * Complex.I_mul_I`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `zero => rw [← zero_smul ℂ (0 : SInf F _), Dp, dop_smul, zero_smul]`.

Conclude with `zero_mem _`. Consider the case `add f g _ _ hf hg => rw [Dp, dop_add']`. Conclude with `add_mem hf hg`. Consider the case `smul c f _ hf => rw [Dp, dop_smul]`. Conclude with `Submodule.smul_mem _ c hf`.

Consider the case `mem f hf`. Take `⟨g, hg, hc⟩` from `hf`. Take `⟨a, z, b, -, hz, -, rfl⟩` from `decomp hW hH hu`. Rewrite using `[Dp_add, Dp_add]`. Use `add_mem (add_mem (Submodule.subset_span ⟨g, hg, fun t => ?_⟩) (Submodule.subset_span ⟨_, pol_Dp hB hz hg, fun t => ?_⟩)) (Submodule.subset_span ⟨g, hg, fun t => ?_⟩)` and prove the remaining obligations.

Take `⟨q, hq, hq'⟩` from `h.cx a`. Take `⟨c, hc⟩` from `hc t`. Use `⟨-(2 * Real.pi * Complex.I) * linForm q t * c, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Dp, dop_apply, hq, hq', map_zero, hc]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨c, hc⟩` from `hc t`. Use `⟨c, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[h.slice (g := c • g) (fun y => (hc y).symm), Dp, dop_smul]`. Both sides reduce to the same expression. Take `⟨p, hp, hl⟩` from `h.cy b`.

Take `⟨c, hc⟩` from `slice_normal ε f g hc p t`. Use `⟨c, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Dp, dop_apply, hp, hl, hc]`. Simplify using the standard rewrite rules. Use `(Submodule.map_mono h1).trans ?_` and prove the remaining obligations.

Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨f, ⟨g, hg, hc⟩, rfl⟩`. Take `⟨c, hc⟩` from `hc 0`. Rewrite using `[show T f = c • g from SchwartzMap.ext fun y => (hT f y).trans (hc y)]`. Conclude with `Submodule.smul_mem _ c hg`.
-/
theorem map_le (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) (hT : ∀ f y, T f y = f (glue ε 0 y)) :
    (Ma.Pol B.ψ B.emb).map T ≤ M₁.Pol B.ψ B.emb := by
  let S : Set (SInf F (Fin n × Fin d)) := {f | ∃ g ∈ M₁.Pol B.ψ B.emb, ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y}
  have h1 : Ma.Pol B.ψ B.emb ≤ Submodule.span ℂ S := by
    refine pol_le hB (fun e f hf => Submodule.subset_span ⟨T f, pol_gs hB (h.gs_slice hH hf (hT f)), fun t => ?_⟩) fun u hu f hf => ?_
    · obtain ⟨b, hb, hp⟩ := h.onto hW hH t
      obtain ⟨-, -, hl⟩ := h.cy b
      obtain ⟨a, ha, hr⟩ := rel_y (X := X) hB hW hH e b
      obtain ⟨q, hq, hq'⟩ := h.cx a
      have key := hf _ _ (at_pure hb _) (at_pure ha _) hr
      refine ⟨_, fun y => (slice_ode ε f t (Real.pi * linForm q t) (fun c y => ?_) y).trans (by rw [hT])⟩
      have := DFunLike.congr_fun key (glue ε (c • t) y)
      simp only [Dp, SchwartzMap.smul_apply, dop_apply, hq, hq', hp, hl, map_zero, map_smul, ContinuousLinearMap.zero_apply,
        smul_eq_mul] at this
      push_cast at this ⊢
      linear_combination Complex.I * this + (fderiv ℝ f (glue ε (c • t) y) (glue ε t 0) +
        2 * Real.pi * c * linForm q t * f (glue ε (c • t) y)) * Complex.I_mul_I
    · induction hf using Submodule.span_induction with
      | zero => rw [← zero_smul ℂ (0 : SInf F _), Dp, dop_smul, zero_smul]; exact zero_mem _
      | add f g _ _ hf hg => rw [Dp, dop_add']; exact add_mem hf hg
      | smul c f _ hf => rw [Dp, dop_smul]; exact Submodule.smul_mem _ c hf
      | mem f hf =>
        obtain ⟨g, hg, hc⟩ := hf
        obtain ⟨a, z, b, -, hz, -, rfl⟩ := decomp hW hH hu
        rw [Dp_add, Dp_add]
        refine add_mem (add_mem (Submodule.subset_span ⟨g, hg, fun t => ?_⟩)
          (Submodule.subset_span ⟨_, pol_Dp hB hz hg, fun t => ?_⟩)) (Submodule.subset_span ⟨g, hg, fun t => ?_⟩)
        · obtain ⟨q, hq, hq'⟩ := h.cx a
          obtain ⟨c, hc⟩ := hc t
          refine ⟨-(2 * Real.pi * Complex.I) * linForm q t * c, fun y => ?_⟩
          rw [Dp, dop_apply, hq, hq', map_zero, hc]
          ring
        · obtain ⟨c, hc⟩ := hc t
          refine ⟨c, fun y => ?_⟩
          rw [h.slice (g := c • g) (fun y => (hc y).symm), Dp, dop_smul]
          rfl
        · obtain ⟨p, hp, hl⟩ := h.cy b
          obtain ⟨c, hc⟩ := slice_normal ε f g hc p t
          refine ⟨c, fun y => ?_⟩
          rw [Dp, dop_apply, hp, hl, hc]
          simp
  refine (Submodule.map_mono h1).trans ?_
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨g, hg, hc⟩, rfl⟩
  obtain ⟨c, hc⟩ := hc 0
  rw [show T f = c • g from SchwartzMap.ext fun y => (hT f y).trans (hc y)]
  exact Submodule.smul_mem _ c hg

/- English proof (translation)
Distinguish the cases in `hne : Nonempty (Fin n × Fin d₁)`. Use `swap`. Conclude with `fun z z' hz hz' _ => hg z z' hz hz' fun w => Matrix.ext fun i j => (hne ⟨(i, j)⟩).elim`. Take `⟨i, j⟩` from `hne`. It suffices to establish `e = 1 from this ▸ hg`.

Use function extensionality and compare the values at `w₀`. Assume the negation of the conclusion as `hw`. Establish `hw' : e w₀ = -1` using `(Int.units_eq_one_or _).resolve_left hw`. Take `⟨a, ha, ha'⟩` from `exists_vec hB fun w (_ : Fin n) => if w = w₀ then 1 else 0`. Take `⟨z', hz', hr⟩` from `exists_rel hB X W₁ e (Matrix.vecMulVec a (incV F (Pi.single j 1)))`.

Establish `hr'` using `rel_iota hH hr`. Establish `e1 : Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ = Matrix.vecMulVec a (incV F (H.ι *ᵥ Pi.single j 1))`. Rewrite using `[Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`. Use `congr 1`. Conclude with `funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) H.ι _ i).symm`.

Establish `hb : H.ι *ᵥ Pi.single j 1 ≠ 0` using `fun hb => by`. Take `⟨Q, -, h2, -⟩` from `exists_frame_inv hH hW.lat`. Establish `h3` using `frame_mulVec H (Sum.elim (Pi.single j 1) 0)`. Simplify using `only [Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_smul, hb, add_zero] at h3`. Establish `h4` using `congrArg (Q *ᵥ ·) h3`.

Simplify using `only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h4`. Simplify using `using congrFun h4 (.inl j)`. Establish `h5` using `omega_co Ma (Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ) (z' * (incM F H.ι)ᵀ)`. Rewrite `h5` using `[h.ai, h.ai, h.li, h.li, e1]`. Rewrite `hr'` using `[e1]`.

Take `⟨p, hp, hp'⟩` from `omega_pure hB hX hW a hb hr'`. Use `h0 (eq_zero_of_neg g _ _ _ _ (hg _ _ (at_pure ha _) hz' hr) ?_)` and prove the remaining obligations. Rewrite using `[← h5, hp, Finset.sum_eq_single w₀ (fun w _ hw => by rw [(hp' w).1 (funext fun k => by simp [ha', hw]), mul_zero]) (by simp), hw']`. Use `(hp' w₀).2 fun h0 => by simpa [ha'] using congrFun h0 i` as an intermediate fact. Simplify using `using this`.
-/
theorem gs_one (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e g}
    (hg : Gs B M₁ e g) (h0 : g ≠ 0) : Gs B M₁ 1 g := by
  by_cases hne : Nonempty (Fin n × Fin d₁)
  swap
  · exact fun z z' hz hz' _ => hg z z' hz hz' fun w => Matrix.ext fun i j => (hne ⟨(i, j)⟩).elim
  obtain ⟨i, j⟩ := hne
  suffices e = 1 from this ▸ hg
  funext w₀
  by_contra hw
  have hw' : e w₀ = -1 := (Int.units_eq_one_or _).resolve_left hw
  obtain ⟨a, ha, ha'⟩ := exists_vec hB fun w (_ : Fin n) => if w = w₀ then 1 else 0
  obtain ⟨z', hz', hr⟩ := exists_rel hB X W₁ e (Matrix.vecMulVec a (incV F (Pi.single j 1)))
  have hr' := rel_iota hH hr
  have e1 : Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ = Matrix.vecMulVec a (incV F (H.ι *ᵥ Pi.single j 1)) := by
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    congr 1
    exact funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) H.ι _ i).symm
  have hb : H.ι *ᵥ Pi.single j 1 ≠ 0 := fun hb => by
    obtain ⟨Q, -, h2, -⟩ := exists_frame_inv hH hW.lat
    have h3 := frame_mulVec H (Sum.elim (Pi.single j 1) 0)
    simp only [Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_smul, hb, add_zero] at h3
    have h4 := congrArg (Q *ᵥ ·) h3
    simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h4
    simpa using congrFun h4 (.inl j)
  have h5 := omega_co Ma (Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ) (z' * (incM F H.ι)ᵀ)
  rw [h.ai, h.ai, h.li, h.li, e1] at h5
  rw [e1] at hr'
  obtain ⟨p, hp, hp'⟩ := omega_pure hB hX hW a hb hr'
  refine h0 (eq_zero_of_neg g _ _ _ _ (hg _ _ (at_pure ha _) hz' hr) ?_)
  rw [← h5, hp, Finset.sum_eq_single w₀ (fun w _ hw => by rw [(hp' w).1 (funext fun k => by simp [ha', hw]), mul_zero]) (by simp), hw']
  have := (hp' w₀).2 fun h0 => by simpa [ha'] using congrFun h0 i
  simpa using this

/- English proof (translation)
Establish `sym : ∀ {b a b' a' p p' q q'}, Rel B X W 1 (Matrix.vecMulVec b (incV F H.y)) (Matrix.vecMulVec a (incV F H.x)) → Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) → aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε p 0 → aOf Ma (Matrix.vecMulVec b' …`. Introduce `b a b' a' p p' q q' h1 h2 h3 h4 h5 h6`. Use `omega_rel hB hX hW h2 (h1.symm hX hW)` as an intermediate fact. Rewrite `this` using `[omega_co Ma, omega_co Ma, aOf_neg, lOf_neg, (h.cy b).choose_spec.2, (h.cy b').choose_spec.2, map_neg, h3, h4, h5, h6]`. Simplify using `using this`.

Use `choose b hb hp using h.onto hW hH`. Use `choose a ha hr using fun t => rel_y (X := X) hB hW hH 1 (b t)`. Use `choose q hq hq' using fun t => h.cx (a t)`. Establish `hs : ∀ t t', linForm (q t') t = linForm (q t) t'` using `fun t t' => sym (hr t) (hr t') (hp t) (hp t') (hq' t) (hq' t')`. Set `Q : (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun t t' => linForm (q t') t) (fun _ _ _ => map_add _ _ _) (fun _ _ _ => map_smul _ _ _) (fun t _ _ => by rw [hs, map_add, hs _ t, hs _ t]) fun c t _ => by rw [hs, map_smul, hs _ t]`.

Establish `hy : H.y ≠ 0` using `fun h0 => by simpa [h0, form, dotProduct, Matrix.mulVec] using hH.xy`. Take `⟨f, f0, f1, f2⟩` from `exists_gauss_box ε Q hs (fun t ht => by`. Take `⟨p, h1, h2⟩` from `omega_pure hB hX hW (b t) hy (hr t)`. Rewrite `h1` using `[omega_co Ma, hp, hq', (h.cy _).choose_spec.2, ContinuousLinearMap.zero_apply, sub_zero]`. Establish `h3 : ∃ w, (fun i => piInf (B.emb w) (b t i)) ≠ 0` using `by by_contra! h4`.

Establish `h5 : b t = 0` using `funext fun i => GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _ (fun c hc => congrFun (hb t c hc) i) fun w => congrFun (h4 w) i`. Establish `h6` using `hp t`. Rewrite `h6` using `[h5, Matrix.zero_vecMulVec, aOf_zero]`. Conclude with `ht (funext fun k => by simpa using (congrFun h6 (ε.symm (.inl k))).symm)`. Take `⟨w, hw⟩` from `h3`.

Use `lt_of_lt_of_eq (Finset.sum_pos' (fun w _ => ?_) ⟨w, Finset.mem_univ _, by simpa using (h2 w).2 hw⟩) h1.symm` and prove the remaining obligations. Distinguish the cases in `h4 : (fun i => piInf (B.emb w) (b t i)) = 0`. Simplify using `[(h2 w).1 h4]`. Simplify using `using ((h2 w).2 h4).le) g`. Establish `K : ∀ b' a', Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) → Dp Ma (Matrix.vecMulVec a' (incV F H.x)) f = Complex.I • Dp Ma (Matrix.vecMulVec b' (incV F H.y)) f` using `fun b' a' h1 => by`.

Take `⟨p', h2, h3⟩` from `h.cy b'`. Take `⟨q', h4, h5⟩` from `h.cx a'`. Use extensionality with `x`. Take `⟨t, y, rfl⟩` from `exists_glue ε x`. Establish `h6 : linForm q' t = Q t p'` using `(sym (hr t) h1 (hp t) h2 (hq' t) h5).trans (hs p' t)`.

Simplify using `only [Dp, SchwartzMap.smul_apply, dop_apply, h2, h3, h4, h5, h6, f2, map_zero, ContinuousLinearMap.zero_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨f, fun u u' hu hu' hrel => ?_, f0⟩` and prove the remaining obligations. Take `⟨a₁, z, b₁, ha₁, hz, hb₁, rfl⟩` from `decomp hW hH hu`.

Take `⟨b₂, hb₂, r1⟩` from `exists_relation_adapted_vector (X := X) hB hH 1 a₁`. Take `⟨z', hz', r2⟩` from `exists_rel hB X W₁ 1 z`. Take `⟨a₂, ha₂, r3⟩` from `rel_y (X := X) hB hW hH 1 b₁`. Rewrite using `[hrel.unique hB ((r1.add (rel_iota hH r2)).add r3) hu' fun c hc => by`. Rewrite using `[smul_add, smul_add, at_pure hb₂ _ c hc, at_mul' hz' _ c hc, at_pure ha₂ _ c hc, add_zero, add_zero]]`.

Establish `k1` using `K b₂ (-a₁) (by rw [Matrix.neg_vecMulVec]; exact r1.symm hX hW)`. Rewrite `k1` using `[Matrix.neg_vecMulVec, Dp, aOf_neg, lOf_neg, dop_neg, neg_eq_iff_eq_neg]`. Establish `k2 : Dp Ma (z' * (incM F H.ι)ᵀ) f = Complex.I • Dp Ma (z * (incM F H.ι)ᵀ) f`. Use extensionality with `x`. Take `⟨t, y, rfl⟩` from `exists_glue ε x`.

Take `⟨c, hc⟩` from `f1 t`. Establish `h1` using `DFunLike.congr_fun (hg z z' hz hz' r2) y`. Rewrite using `[SchwartzMap.smul_apply, h.slice (g := c • g) (fun y => (hc y).symm), h.slice (g := c • g) (fun y => (hc y).symm), Dp, Dp, dop_smul, dop_smul, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_comm]`. Conclude with `congrArg _ h1`. Rewrite using `[Dp_add, Dp_add, Dp_add, Dp_add, K _ _ r3, k2, smul_add, smul_add]`.

Use `congr 2`. Express the relevant statement in the definitionally equal form `_ = Complex.I • dop _ _ f`. Rewrite using `[k1, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]`.
-/
theorem exists_lift (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {g}
    (hg : Gs B M₁ 1 g) : ∃ f, Gs B Ma 1 f ∧ ∀ y, f (glue ε 0 y) = g y := by
  have sym : ∀ {b a b' a' p p' q q'}, Rel B X W 1 (Matrix.vecMulVec b (incV F H.y)) (Matrix.vecMulVec a (incV F H.x)) →
      Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) →
      aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε p 0 → aOf Ma (Matrix.vecMulVec b' (incV F H.y)) = glue ε p' 0 →
      (∀ t y, lOf Ma (Matrix.vecMulVec a (incV F H.x)) (glue ε t y) = linForm q t) →
      (∀ t y, lOf Ma (Matrix.vecMulVec a' (incV F H.x)) (glue ε t y) = linForm q' t) → linForm q' p = linForm q p' := by
    intro b a b' a' p p' q q' h1 h2 h3 h4 h5 h6
    have := omega_rel hB hX hW h2 (h1.symm hX hW)
    rw [omega_co Ma, omega_co Ma, aOf_neg, lOf_neg, (h.cy b).choose_spec.2, (h.cy b').choose_spec.2, map_neg, h3, h4, h5, h6] at this
    simpa using this
  choose b hb hp using h.onto hW hH
  choose a ha hr using fun t => rel_y (X := X) hB hW hH 1 (b t)
  choose q hq hq' using fun t => h.cx (a t)
  have hs : ∀ t t', linForm (q t') t = linForm (q t) t' := fun t t' => sym (hr t) (hr t') (hp t) (hp t') (hq' t) (hq' t')
  let Q : (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun t t' => linForm (q t') t) (fun _ _ _ => map_add _ _ _) (fun _ _ _ => map_smul _ _ _)
      (fun t _ _ => by rw [hs, map_add, hs _ t, hs _ t]) fun c t _ => by rw [hs, map_smul, hs _ t]
  have hy : H.y ≠ 0 := fun h0 => by simpa [h0, form, dotProduct, Matrix.mulVec] using hH.xy
  obtain ⟨f, f0, f1, f2⟩ := exists_gauss_box ε Q hs (fun t ht => by
    obtain ⟨p, h1, h2⟩ := omega_pure hB hX hW (b t) hy (hr t)
    rw [omega_co Ma, hp, hq', (h.cy _).choose_spec.2, ContinuousLinearMap.zero_apply, sub_zero] at h1
    have h3 : ∃ w, (fun i => piInf (B.emb w) (b t i)) ≠ 0 := by
      by_contra! h4
      have h5 : b t = 0 := funext fun i => GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _
        (fun c hc => congrFun (hb t c hc) i) fun w => congrFun (h4 w) i
      have h6 := hp t
      rw [h5, Matrix.zero_vecMulVec, aOf_zero] at h6
      exact ht (funext fun k => by simpa using (congrFun h6 (ε.symm (.inl k))).symm)
    obtain ⟨w, hw⟩ := h3
    refine lt_of_lt_of_eq (Finset.sum_pos' (fun w _ => ?_) ⟨w, Finset.mem_univ _, by simpa using (h2 w).2 hw⟩) h1.symm
    by_cases h4 : (fun i => piInf (B.emb w) (b t i)) = 0
    · simp [(h2 w).1 h4]
    · simpa using ((h2 w).2 h4).le) g
  have K : ∀ b' a', Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) →
      Dp Ma (Matrix.vecMulVec a' (incV F H.x)) f = Complex.I • Dp Ma (Matrix.vecMulVec b' (incV F H.y)) f := fun b' a' h1 => by
    obtain ⟨p', h2, h3⟩ := h.cy b'
    obtain ⟨q', h4, h5⟩ := h.cx a'
    ext x
    obtain ⟨t, y, rfl⟩ := exists_glue ε x
    have h6 : linForm q' t = Q t p' := (sym (hr t) h1 (hp t) h2 (hq' t) h5).trans (hs p' t)
    simp only [Dp, SchwartzMap.smul_apply, dop_apply, h2, h3, h4, h5, h6, f2, map_zero, ContinuousLinearMap.zero_apply, smul_eq_mul]
    push_cast
    ring
  refine ⟨f, fun u u' hu hu' hrel => ?_, f0⟩
  obtain ⟨a₁, z, b₁, ha₁, hz, hb₁, rfl⟩ := decomp hW hH hu
  obtain ⟨b₂, hb₂, r1⟩ := exists_relation_adapted_vector (X := X) hB hH 1 a₁
  obtain ⟨z', hz', r2⟩ := exists_rel hB X W₁ 1 z
  obtain ⟨a₂, ha₂, r3⟩ := rel_y (X := X) hB hW hH 1 b₁
  rw [hrel.unique hB ((r1.add (rel_iota hH r2)).add r3) hu' fun c hc => by
    rw [smul_add, smul_add, at_pure hb₂ _ c hc, at_mul' hz' _ c hc, at_pure ha₂ _ c hc, add_zero, add_zero]]
  have k1 := K b₂ (-a₁) (by rw [Matrix.neg_vecMulVec]; exact r1.symm hX hW)
  rw [Matrix.neg_vecMulVec, Dp, aOf_neg, lOf_neg, dop_neg, neg_eq_iff_eq_neg] at k1
  have k2 : Dp Ma (z' * (incM F H.ι)ᵀ) f = Complex.I • Dp Ma (z * (incM F H.ι)ᵀ) f := by
    ext x
    obtain ⟨t, y, rfl⟩ := exists_glue ε x
    obtain ⟨c, hc⟩ := f1 t
    have h1 := DFunLike.congr_fun (hg z z' hz hz' r2) y
    rw [SchwartzMap.smul_apply, h.slice (g := c • g) (fun y => (hc y).symm), h.slice (g := c • g) (fun y => (hc y).symm), Dp, Dp,
      dop_smul, dop_smul, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_comm]
    exact congrArg _ h1
  rw [Dp_add, Dp_add, Dp_add, Dp_add, K _ _ r3, k2, smul_add, smul_add]
  congr 2
  change _ = Complex.I • dop _ _ f
  rw [k1, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

/- English proof (translation)
Use `le_antisymm (h.map_le hB hW hH T hT) (pol_le hB (fun e g hg => ?_) ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : g = 0`. Conclude with `h0 ▸ zero_mem _`. Take `⟨f, hf, hf'⟩` from `h.exists_lift hB hX hW hH (h.gs_one hB hX hW hH hg h0)`. Conclude with `⟨f, pol_gs hB hf, SchwartzMap.ext fun y => (hT f y).trans (hf' y)⟩`.

Introduce and unpack `z hz _ ⟨f, hf, rfl⟩`. Conclude with `⟨_, pol_Dp hB (at_mul' hz _) hf, SchwartzMap.ext fun y => (hT _ y).trans (h.slice (hT f) z y)⟩`.
-/
theorem map_eq (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) (hT : ∀ f y, T f y = f (glue ε 0 y)) :
    (Ma.Pol B.ψ B.emb).map T = M₁.Pol B.ψ B.emb := by
  refine le_antisymm (h.map_le hB hW hH T hT) (pol_le hB (fun e g hg => ?_) ?_)
  · by_cases h0 : g = 0
    · exact h0 ▸ zero_mem _
    obtain ⟨f, hf, hf'⟩ := h.exists_lift hB hX hW hH (h.gs_one hB hX hW hH hg h0)
    exact ⟨f, pol_gs hB hf, SchwartzMap.ext fun y => (hT f y).trans (hf' y)⟩
  · rintro z hz _ ⟨f, hf, rfl⟩
    exact ⟨_, pol_Dp hB (at_mul' hz _) hf, SchwartzMap.ext fun y => (hT _ y).trans (h.slice (hT f) z y)⟩

end Adp

end PositivityTheory.ThKF0
