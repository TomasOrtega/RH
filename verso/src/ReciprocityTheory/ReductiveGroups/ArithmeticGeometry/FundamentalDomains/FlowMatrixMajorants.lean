import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace FlowMatrixMajorants

open MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)

/- English proof (translation)
Take `⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ, V = Matrix.of fun a b => τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))` from `⟨_, rfl⟩`. Establish `hM : ∀ s : ℂ, X.flowMat ξ τ s = 1 - (I * (X.c τ : ℂ) * s) • V`. Introduce `s`. Use extensionality with `a b`. Simplify using `only [Data.flowMat, hV, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) = 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hermC, Data.emb, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring`.

Use `_ = 0 := hiso`. Establish `hVV : V * V = 0`. Use extensionality with `a b`. Simplify using `only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Use `_ = 0 := by rw [h0, mul_zero]`. Simplify using `only [hM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVV, smul_zero, sub_zero, mul_add, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem flowMat_add (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a b : ℂ) :
    X.flowMat ξ τ (a + b) = X.flowMat ξ τ a * X.flowMat ξ τ b := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ,
      V = Matrix.of fun a b => τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := ⟨_, rfl⟩
  have hM : ∀ s : ℂ, X.flowMat ξ τ s = 1 - (I * (X.c τ : ℂ) * s) • V := by
    intro s
    ext a b
    simp only [Data.flowMat, hV, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  have h0 : ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) = 0 := by
    calc _ = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
          simp only [hermC, Data.emb, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := hiso
  have hVV : V * V = 0 := by
    ext a b
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ k, τ.1 (ξ a) * (∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m))) *
          (τ.1 (ξ k) * ∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m)))
        = τ.1 (ξ a) * (∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m))) *
          ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  simp only [hM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hVV, smul_zero, sub_zero, mul_add, add_smul]
  abel

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Data.flowMat, Matrix.of_apply, mul_zero, zero_mul, sub_zero, Matrix.one_apply]`.
-/
theorem flowMat_zero : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, mul_zero, zero_mul, sub_zero, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hs : I * ((s τ).im : ℂ) + ((s τ).re : ℂ) = s τ`. Rewrite using `[add_comm, mul_comm, Complex.re_add_im]`. Use `show X.flowMat ξ τ (s τ) * mat x τ = X.flowMat ξ τ (I * ((s τ).im : ℂ)) * (X.flowMat ξ τ ((s τ).re : ℂ) * mat x τ)`. Use `conv_lhs => rw [← hs]`.

Rewrite using `[flowMat_add X ξ τ (hiso τ), mul_assoc]`.
-/
theorem flow_split (hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0)
    (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) := by
  funext τ
  have hs : I * ((s τ).im : ℂ) + ((s τ).re : ℂ) = s τ := by
    rw [add_comm, mul_comm, Complex.re_add_im]
  show X.flowMat ξ τ (s τ) * mat x τ =
    X.flowMat ξ τ (I * ((s τ).im : ℂ)) * (X.flowMat ξ τ ((s τ).re : ℂ) * mat x τ)
  conv_lhs => rw [← hs]
  rw [flowMat_add X ξ τ (hiso τ), mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← flowMat_add X ξ τ hiso, add_neg_cancel, flowMat_zero, Matrix.one_mulVec]`.
-/
theorem flowMat_inv (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a : ℂ)
    (w : Fin r → ℂ) : Matrix.mulVec (X.flowMat ξ τ a) (Matrix.mulVec (X.flowMat ξ τ (-a)) w) = w := by
  rw [Matrix.mulVec_mulVec, ← flowMat_add X ξ τ hiso, add_neg_cancel, flowMat_zero,
    Matrix.one_mulVec]

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_sub_smul_left_lemma_8 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (p - a • q) y = hermC σ G p y - a * hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_sub_smul_right_lemma_9 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (p - a • q) = hermC σ G y p - conj a * hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hMv : ∀ w : Fin r → ℂ, Matrix.mulVec (X.flowMat ξ τ t) w = w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ`. Introduce `w`. Use function extensionality and compare the values at `i`. Use `show ∑ b, X.flowMat ξ τ t i b * w b = _`. Simplify using `only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, Data.emb]`.

Use `congr 1`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[hMv u, hMv v, hermC_sub_smul_left_lemma_8, hermC_sub_smul_right_lemma_9, hermC_sub_smul_right_lemma_9, hiso, ← hermC_conj τ.1 X.Gm_herm v (Data.emb τ.1 ξ)]`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowMat_isom_real (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (t : ℝ)
    (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ t) u) (Matrix.mulVec (X.flowMat ξ τ t) v) =
      hermC τ.1 X.Gm u v := by
  have hMv : ∀ w : Fin r → ℂ, Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
    intro w
    funext i
    show ∑ b, X.flowMat ξ τ t i b * w b = _
    simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hermC, Data.emb]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hMv u, hMv v, hermC_sub_smul_left_lemma_8, hermC_sub_smul_right_lemma_9, hermC_sub_smul_right_lemma_9,
    hiso, ← hermC_conj τ.1 X.Gm_herm v (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/- English proof (translation)
Unfold `Data.Hf hermC`. Rewrite using `[X.ppos_add x τ]`. Simplify using `only [smul_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem Hf_add_left (x : Frame X.Ψ r) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by
  unfold Data.Hf hermC
  rw [X.ppos_add x τ]
  simp only [smul_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Unfold `Data.Hf hermC`. Simplify using `only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem Hf_add_right (x : Frame X.Ψ r) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w + w') = X.Hf x τ u w + X.Hf x τ u w' := by
  unfold Data.Hf hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Set `f : (Fin r → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun x => hermC σ G x y map_add' := fun x x' => by`. Simplify using `only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }`.

Establish `h` using `map_sum f (fun k => u k • v k) Finset.univ`. Simplify using `only [map_smul, smul_eq_mul] at h`. Conclude with `h`.
-/
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC σ G (∑ k, u k • v k) y = ∑ k, u k * hermC σ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC σ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

/- English proof (translation)
Set `g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ` to `{ toFun := fun y => hermC σ G x y map_add' := fun y y' => by`. Simplify using `only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c y => by`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }`.

Establish `h` using `map_sum g (fun l => w l • z l) Finset.univ`. Simplify using `only [map_smulₛₗ, smul_eq_mul] at h`. Conclude with `h`.
-/
private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC σ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC σ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC σ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_smul_sub_right_lemma_4 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ`. Use extensionality with `a b`. Conclude with `hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b)) (col (mat x τ) (Fin.castLE X.p0_le a))`. Establish `hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b`. Introduce `a b`.

Establish `h` using `congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by`. Rewrite using `[Matrix.conjTranspose_nonsing_inv, hGp]) a) b`. Conclude with `h`. Unfold `Data.ppos`. Rewrite using `[hermC_sum_left_lemma, hermC_sum_right_lemma_2]`.

Simplify using `only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by
      rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Unfold `Data.jp`. Rewrite using `[hermC_smul_sub_left_lemma_3, hermC_smul_sub_right_lemma_4, hermC_smul_sub_right_lemma_4, hermC_ppos_lemma_5 X τ x u (X.ppos x τ v), X.ppos_ppos hx τ v, hermC_ppos_lemma_5 X τ x u v]`. Establish `h2 : conj (2 : ℂ) = 2` using `map_ofNat (starRingEnd ℂ) 2`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermC_jp_lemma_6 {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) (X.jp x τ v) = hermC τ.1 X.Gm u v := by
  unfold Data.jp
  rw [hermC_smul_sub_left_lemma_3, hermC_smul_sub_right_lemma_4, hermC_smul_sub_right_lemma_4,
    hermC_ppos_lemma_5 X τ x u (X.ppos x τ v), X.ppos_ppos hx τ v, hermC_ppos_lemma_5 X τ x u v]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  rw [h2]
  ring

/- English proof (translation)
Establish `hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))`. Unfold `Data.ppos`. Rewrite using `[hermC_sum_left_lemma]`. Simplify using `only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]`. Use `conv_lhs => rw [Finset.sum_comm]`.

Unfold `Data.maj Data.posPart Data.jp`. Rewrite using `[← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]`. Simplify using the standard rewrite rules.
-/
private lemma maj_eq_lemma_7 (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    X.maj x τ v = (hermC τ.1 X.Gm (X.jp x τ v) v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.jp
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp

/- English proof (translation)
Rewrite using `[maj_eq_lemma_7 X τ x (X.jp x τ v), maj_eq_lemma_7 X τ x v, X.jp_jp hx τ v, ← hermC_conj τ.1 X.Gm_herm v (X.jp x τ v), Complex.conj_re]`.
-/
theorem maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  rw [maj_eq_lemma_7 X τ x (X.jp x τ v), maj_eq_lemma_7 X τ x v, X.jp_jp hx τ v,
    ← hermC_conj τ.1 X.Gm_herm v (X.jp x τ v), Complex.conj_re]

/- English proof (translation)
Conclude with `(hermC_jp_lemma_6 X τ hx u v).symm`.
-/
theorem herm_eq_Hf_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = X.Hf x τ u (X.jp x τ v) := by
  exact (hermC_jp_lemma_6 X τ hx u v).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show ∑ b, X.flowMat ξ τ t i b * w b = _`. Simplify using `only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, Data.emb]`. Use `congr 1`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
private lemma flowMat_mulVec_lemma_10 (t : ℝ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext i
  show ∑ b, X.flowMat ξ τ t i b * w b = _
  simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `hHs : ∀ p q, conj (X.Hf x τ p q) = X.Hf x τ q p`. Introduce `p q`. Unfold `Data.Hf`. Rewrite using `[hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_4, hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X τ x q p, map_ofNat]`. Establish `hN : ∀ v, X.maj x τ v = (X.Hf x τ v v).re` using `fun v => maj_eq_lemma_7 X τ x v`.

Establish `hreal : ∀ v, X.Hf x τ v v = ((X.maj x τ v : ℝ) : ℂ)`. Introduce `v`. Rewrite using `[hN]`. Conclude with `(Complex.conj_eq_iff_re.mp (hHs v v)).symm`. Establish `hnn : ∀ v, 0 ≤ X.maj x τ v`.

Introduce `v`. Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Rewrite using `[hN]`. Simplify using `[Data.Hf, hermC]`.

Conclude with `(X.maj_pos hx τ hv).le`. Establish `hsl : ∀ (a : ℂ) p q, X.Hf x τ (a • p) q = a * X.Hf x τ p q`. Introduce `a p q`. Unfold `Data.Hf`. Rewrite using `[X.ppos_smul_eq x τ]`.

Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hsr : ∀ (a : ℂ) p q, X.Hf x τ p (a • q) = conj a * X.Hf x τ p q`. Introduce `a p q`. Unfold `Data.Hf`.

Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hexp : ∀ (α β : ℂ) p q, X.Hf x τ (α • p + β • q) (α • p + β • q) = α * conj α * X.Hf x τ p p + α * conj β * X.Hf x τ p q + β * conj α * X.Hf x τ q p + β * conj β * X.Hf x τ q q`. Introduce `α β p q`. Simplify using `only [Hf_add_left X τ, Hf_add_right X τ, hsl, hsr]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hCS : ∀ p q, Complex.normSq (X.Hf x τ p q) ≤ X.maj x τ p * X.maj x τ q`. Introduce `p q`. Distinguish the cases in `hq : q = 0`. Substitute `hq` using the available equality.

Establish `h0 : X.Hf x τ p 0 = 0` using `by simp [Data.Hf, hermC]`. Rewrite using `[h0, map_zero]`. Conclude with `mul_nonneg (hnn p) (hnn 0)`. Establish `hn` using `X.maj_pos hx τ hq`. Take `⟨z, hz⟩ : ∃ z, z = X.Hf x τ p q` from `⟨_, rfl⟩`.

Establish `h0` using `hnn (((X.maj x τ q : ℝ) : ℂ) • p + (-z) • q)`. Rewrite `h0` using `[hN, hexp, hreal p, hreal q, ← hHs p q, ← hz]`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im, map_neg] at h0`. Rewrite using `[← hz, Complex.normSq_apply]`. Use polynomial arithmetic with `[h0, hn]`.

Take `⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = hermC τ.1 X.Gm u (Data.emb τ.1 ξ)` from `⟨_, rfl⟩`. Take `⟨β, hβ⟩ : ∃ β : ℂ, β = I * (X.c τ : ℂ) * (t : ℂ) * ℓ` from `⟨_, rfl⟩`. Establish `hMu : Matrix.mulVec (X.flowMat ξ τ t) u = (1 : ℂ) • u + (-β) • Data.emb τ.1 ξ`. Rewrite using `[flowMat_mulVec_lemma_10 X ξ τ t u, ← hℓ, ← hβ, one_smul, neg_smul, sub_eq_add_neg]`. Take `⟨z, hz⟩ : ∃ z, z = X.Hf x τ u (Data.emb τ.1 ξ)` from `⟨_, rfl⟩`.

Establish `hval : X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) = X.maj x τ u - 2 * (conj β * z).re + Complex.normSq β * X.maj x τ (Data.emb τ.1 ξ)`. Rewrite using `[hN, hMu, hexp, hreal u, hreal (Data.emb τ.1 ξ), ← hHs u (Data.emb τ.1 ξ), ← hz]`. Establish `e1 : β * conj z = conj (conj β * z)`. Rewrite using `[map_mul, Complex.conj_conj, mul_comm]`. Establish `e2 : β * conj β = (Complex.normSq β : ℂ)` using `Complex.mul_conj β`.

Simplify using `only [map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg]`. Rewrite using `[e1, e2]`. Simplify using `only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc0 : 0 ≤ X.c τ`.

Unfold `Data.c`. Check the signs of the components of the expression. Establish `hnβ : ‖β‖ = X.c τ * |t| * ‖ℓ‖`. Rewrite using `[hβ, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, one_mul]`. Establish `hL : ‖ℓ‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ)`.

Rewrite using `[hℓ, herm_eq_Hf_jp X τ hx, ← Complex.normSq_eq_norm_sq, ← maj_jp X τ hx (Data.emb τ.1 ξ)]`. Conclude with `hCS _ _`. Establish `hZ : ‖z‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ)`. Rewrite using `[hz, ← Complex.normSq_eq_norm_sq]`. Conclude with `hCS _ _`.

Establish `hre : -(2 * (conj β * z).re) ≤ 2 * ‖β‖ * ‖z‖`. Establish `h1` using `Complex.abs_re_le_norm (conj β * z)`. Rewrite `h1` using `[norm_mul, Complex.norm_conj]`. Combine the linear relations using `[neg_abs_le (conj β * z).re]`. Establish `hLZ : ‖ℓ‖ * ‖z‖ ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ)`.

Use polynomial arithmetic with `[sq_nonneg (‖ℓ‖ - ‖z‖), norm_nonneg ℓ, norm_nonneg z]`. Establish `hk : 0 ≤ X.c τ * |t|` using `mul_nonneg hc0 (abs_nonneg t)`. Establish `hb : 0 ≤ X.maj x τ (Data.emb τ.1 ξ)` using `hnn _`. Establish `h1` using `mul_le_mul_of_nonneg_left hLZ hk`. Establish `h2` using `mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg (X.c τ * |t|)) hb)`.

Rewrite using `[hval, Complex.normSq_eq_norm_sq, hnβ]`. Rewrite `hre` using `[hnβ]`. Use polynomial arithmetic with `[h1, h2, hre]`.
-/
theorem maj_flow_le {x : Frame X.Ψ r} (hx : x ∈ X.dom) (t : ℝ) (u : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) ≤
      (1 + X.c τ * |t| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ u := by
  have hHs : ∀ p q, conj (X.Hf x τ p q) = X.Hf x τ q p := by
    intro p q
    unfold Data.Hf
    rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_4, hermC_smul_sub_left_lemma_3,
      hermC_ppos_lemma_5 X τ x q p, map_ofNat]
  have hN : ∀ v, X.maj x τ v = (X.Hf x τ v v).re := fun v => maj_eq_lemma_7 X τ x v
  have hreal : ∀ v, X.Hf x τ v v = ((X.maj x τ v : ℝ) : ℂ) := by
    intro v
    rw [hN]
    exact (Complex.conj_eq_iff_re.mp (hHs v v)).symm
  have hnn : ∀ v, 0 ≤ X.maj x τ v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [hN]
      simp [Data.Hf, hermC]
    · exact (X.maj_pos hx τ hv).le
  have hsl : ∀ (a : ℂ) p q, X.Hf x τ (a • p) q = a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    rw [X.ppos_smul_eq x τ]
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsr : ∀ (a : ℂ) p q, X.Hf x τ p (a • q) = conj a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : ∀ (α β : ℂ) p q, X.Hf x τ (α • p + β • q) (α • p + β • q) =
      α * conj α * X.Hf x τ p p + α * conj β * X.Hf x τ p q + β * conj α * X.Hf x τ q p +
        β * conj β * X.Hf x τ q q := by
    intro α β p q
    simp only [Hf_add_left X τ, Hf_add_right X τ, hsl, hsr]
    ring
  have hCS : ∀ p q, Complex.normSq (X.Hf x τ p q) ≤ X.maj x τ p * X.maj x τ q := by
    intro p q
    by_cases hq : q = 0
    · subst hq
      have h0 : X.Hf x τ p 0 = 0 := by simp [Data.Hf, hermC]
      rw [h0, map_zero]
      exact mul_nonneg (hnn p) (hnn 0)
    · have hn := X.maj_pos hx τ hq
      obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ p q := ⟨_, rfl⟩
      have h0 := hnn (((X.maj x τ q : ℝ) : ℂ) • p + (-z) • q)
      rw [hN, hexp, hreal p, hreal q, ← hHs p q, ← hz] at h0
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im,
        map_neg] at h0
      rw [← hz, Complex.normSq_apply]
      nlinarith [h0, hn]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = hermC τ.1 X.Gm u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = I * (X.c τ : ℂ) * (t : ℂ) * ℓ := ⟨_, rfl⟩
  have hMu : Matrix.mulVec (X.flowMat ξ τ t) u = (1 : ℂ) • u + (-β) • Data.emb τ.1 ξ := by
    rw [flowMat_mulVec_lemma_10 X ξ τ t u, ← hℓ, ← hβ, one_smul, neg_smul, sub_eq_add_neg]
  obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  have hval : X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) = X.maj x τ u -
      2 * (conj β * z).re + Complex.normSq β * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hN, hMu, hexp, hreal u, hreal (Data.emb τ.1 ξ), ← hHs u (Data.emb τ.1 ξ), ← hz]
    have e1 : β * conj z = conj (conj β * z) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    have e2 : β * conj β = (Complex.normSq β : ℂ) := Complex.mul_conj β
    simp only [map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg]
    rw [e1, e2]
    simp only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hnβ : ‖β‖ = X.c τ * |t| * ‖ℓ‖ := by
    rw [hβ, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, one_mul]
  have hL : ‖ℓ‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hℓ, herm_eq_Hf_jp X τ hx, ← Complex.normSq_eq_norm_sq, ← maj_jp X τ hx (Data.emb τ.1 ξ)]
    exact hCS _ _
  have hZ : ‖z‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hz, ← Complex.normSq_eq_norm_sq]
    exact hCS _ _
  have hre : -(2 * (conj β * z).re) ≤ 2 * ‖β‖ * ‖z‖ := by
    have h1 := Complex.abs_re_le_norm (conj β * z)
    rw [norm_mul, Complex.norm_conj] at h1
    linarith [neg_abs_le (conj β * z).re]
  have hLZ : ‖ℓ‖ * ‖z‖ ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    nlinarith [sq_nonneg (‖ℓ‖ - ‖z‖), norm_nonneg ℓ, norm_nonneg z]
  have hk : 0 ≤ X.c τ * |t| := mul_nonneg hc0 (abs_nonneg t)
  have hb : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := hnn _
  have h1 := mul_le_mul_of_nonneg_left hLZ hk
  have h2 := mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg (X.c τ * |t|)) hb)
  rw [hval, Complex.normSq_eq_norm_sq, hnβ]
  rw [hnβ] at hre
  nlinarith [h1, h2, hre]

end FlowMatrixMajorants

end ReciprocityTheory.ChartRestriction.G.FD
