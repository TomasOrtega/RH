import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace MajorantNormalForms

open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem col_mul_eq (P B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (P * B) a = ∑ k, B k a • col P k := by
  funext i
  simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def jpL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.jp x τ
  map_add' := X.jp_add x τ
  map_smul' := X.jp_smul x τ

noncomputable def pposL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.ppos x τ
  map_add' := X.ppos_add x τ
  map_smul' := X.ppos_smul_eq x τ

/- English proof (translation)
Establish `h` using `map_sum (pposL X x τ) (fun a => c a • u a) Finset.univ`. Simplify using `only [map_smul] at h`. Conclude with `h`.
-/
theorem ppos_sum (x : Frame X.Ψ r) (τ : X.Ψ) (c : Fin r → ℂ) (u : Fin r → Fin r → ℂ) :
    X.ppos x τ (∑ a, c a • u a) = ∑ a, c a • X.ppos x τ (u a) := by
  have h := map_sum (pposL X x τ) (fun a => c a • u a) Finset.univ
  simp only [map_smul] at h
  exact h

/- English proof (translation)
Set `f : (Fin r → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun x => hermC τ G x y map_add' := fun x x' => by`. Simplify using `only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }`.

Establish `h` using `map_sum f (fun k => u k • v k) Finset.univ`. Simplify using `only [map_smul, smul_eq_mul] at h`. Conclude with `h`.
-/
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC τ G (∑ k, u k • v k) y = ∑ k, u k * hermC τ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC τ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

/- English proof (translation)
Set `g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ` to `{ toFun := fun y => hermC τ G x y map_add' := fun y y' => by`. Simplify using `only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c y => by`. Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }`.

Establish `h` using `map_sum g (fun l => w l • z l) Finset.univ`. Simplify using `only [map_smulₛₗ, smul_eq_mul] at h`. Conclude with `h`.
-/
private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC τ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC τ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC τ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h

/- English proof (translation)
Establish `hz : (2 : ℂ) • X.ppos x τ (∑ a, c a • u a) - ∑ a, c a • u a = ∑ a, c a • ((2 : ℂ) • X.ppos x τ (u a) - u a)`. Rewrite using `[ppos_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, smul_comm]`. Unfold `Data.Hf`.

Rewrite using `[hz, hermC_sum_left_lemma]`. Simplify using `only [hermC_sum_right_lemma_2]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Hf_sum_sum (x : Frame X.Ψ r) (τ : X.Ψ) (c d : Fin r → ℂ) (u w : Fin r → Fin r → ℂ) :
    X.Hf x τ (∑ a, c a • u a) (∑ b, d b • w b) =
      ∑ a, ∑ b, c a * conj (d b) * X.Hf x τ (u a) (w b) := by
  have hz : (2 : ℂ) • X.ppos x τ (∑ a, c a • u a) - ∑ a, c a • u a =
      ∑ a, c a • ((2 : ℂ) • X.ppos x τ (u a) - u a) := by
    rw [ppos_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_sub, smul_comm]
  unfold Data.Hf
  rw [hz, hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `hdet : (X.gramPos x τ).det ≠ 0`. Establish `h` using `(hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩`. Introduce `h0`. Establish `h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0` using `h0`. Rewrite `h` using `[h1, Complex.zero_re, mul_zero]`.

Conclude with `lt_irrefl _ h`. Unfold `Data.ppos Data.colP`. Establish `hG : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b)) = X.gramPos x τ a b` using `fun a b => rfl`. Simplify using `only [hG]`. Establish `hmul : ∀ a, ∑ b, X.gramPos x τ d b * (X.gramPos x τ)⁻¹ b a = if d = a then 1 else 0`.

Introduce `a`. Rewrite using `[← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]`. Simplify using `only [hmul, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem ppos_colP {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.ppos x τ (X.colP x τ d) = X.colP x τ d := by
  have hdet : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
    rw [h1, Complex.zero_re, mul_zero] at h
    exact lt_irrefl _ h
  unfold Data.ppos Data.colP
  have hG : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = X.gramPos x τ a b := fun a b => rfl
  simp only [hG]
  have hmul : ∀ a, ∑ b, X.gramPos x τ d b * (X.gramPos x τ)⁻¹ b a = if d = a then 1 else 0 := by
    intro a
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_apply]
  simp only [hmul, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ`. Use extensionality with `a b`. Conclude with `hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b)) (col (mat x τ) (Fin.castLE X.p0_le a))`. Establish `hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b`. Introduce `a b`.

Establish `h` using `congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b`. Conclude with `h`. Unfold `Data.ppos`. Rewrite using `[hermC_sum_left_lemma, hermC_sum_right_lemma_2]`. Simplify using `only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]`.

Use `conv_lhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) =
      (X.gramPos x τ)⁻¹ by rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Establish `hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))`. Unfold `Data.ppos`. Rewrite using `[hermC_sum_left_lemma]`. Simplify using `only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]`. Use `conv_lhs => rw [Finset.sum_comm]`.

Unfold `Data.maj Data.posPart Data.Hf`. Rewrite using `[← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]`. Simplify using the standard rewrite rules.
-/
private lemma maj_eq_lemma_4 (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = (X.Hf x τ v v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.Hf
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private lemma hermC_smul_sub_right_lemma_6 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Unfold `Data.Hf`. Rewrite using `[hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_6, hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X x τ w u, map_ofNat]`.
-/
private lemma Hf_conj_lemma_7 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  unfold Data.Hf
  rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_6, hermC_smul_sub_left_lemma_3,
    hermC_ppos_lemma_5 X x τ w u, map_ofNat]

/- English proof (translation)
Rewrite using `[Matrix.posDef_iff_dotProduct_mulVec]`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Use extensionality with `a c show star (X.Hf x τ (col (mat x τ) c) (col (mat x τ) a)) = X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)`. Rewrite using `[Complex.star_def, Hf_conj_lemma_7]`. Establish `hy : star v ⬝ᵥ ((Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)) *ᵥ v) = X.Hf x τ (∑ a, star (v a) • col (mat x τ) a) (∑ a, star (v a) • col (mat x τ) a)`.

Rewrite using `[Hf_sum_sum]`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Complex.star_def, Complex.conj_conj]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring`. Establish `hy0 : (∑ a, star (v a) • col (mat x τ) a) ≠ 0`. Introduce `h0`.

Establish `hmv : mat x τ *ᵥ (fun a => star (v a)) = ∑ a, star (v a) • col (mat x τ) a`. Use function extensionality and compare the values at `i`. Use `show ∑ k, mat x τ i k * star (v k) = (∑ a, star (v a) • col (mat x τ) a) i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.

Rewrite `h0` using `[← hmv]`. Establish `h1` using `Matrix.eq_zero_of_mulVec_eq_zero (hx τ).1 h0`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `h2` using `congrFun h1 a`.

Simplify using `using h2`. Establish `hpos` using `X.maj_pos hx τ hy0`. Rewrite `hpos` using `[maj_eq_lemma_4 X x τ]`. Establish `him` using `Complex.conj_eq_iff_im.mp (Hf_conj_lemma_7 X x τ (∑ a, star (v a) • col (mat x τ) a) (∑ a, star (v a) • col (mat x τ) a))`. Rewrite using `[hy]`.

Conclude with `Complex.lt_def.mpr ⟨hpos, him.symm⟩`.
-/
theorem hgram_posDef {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    (Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext a c
    show star (X.Hf x τ (col (mat x τ) c) (col (mat x τ) a)) =
      X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)
    rw [Complex.star_def, Hf_conj_lemma_7]
  have hy : star v ⬝ᵥ ((Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)) *ᵥ v) =
      X.Hf x τ (∑ a, star (v a) • col (mat x τ) a) (∑ a, star (v a) • col (mat x τ) a) := by
    rw [Hf_sum_sum]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      Complex.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hy0 : (∑ a, star (v a) • col (mat x τ) a) ≠ 0 := by
    intro h0
    have hmv : mat x τ *ᵥ (fun a => star (v a)) = ∑ a, star (v a) • col (mat x τ) a := by
      funext i
      show ∑ k, mat x τ i k * star (v k) = (∑ a, star (v a) • col (mat x τ) a) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [← hmv] at h0
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hx τ).1 h0
    apply hv
    funext a
    have h2 := congrFun h1 a
    simpa using h2
  have hpos := X.maj_pos hx τ hy0
  rw [maj_eq_lemma_4 X x τ] at hpos
  have him := Complex.conj_eq_iff_im.mp (Hf_conj_lemma_7 X x τ (∑ a, star (v a) • col (mat x τ) a)
    (∑ a, star (v a) • col (mat x τ) a))
  rw [hy]
  exact Complex.lt_def.mpr ⟨hpos, him.symm⟩

/- English proof (translation)
Establish `hH` using `hgram_posDef X hx τ`. Take `⟨H, hHd⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, H = Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)` from `⟨_, rfl⟩`. Rewrite `hH` using `[← hHd]`. Establish `hD` using `LDL.diag_eq_lowerInv_conj hH`. Establish `hLdet : (LDL.lowerInv hH).det ≠ 0` using `(Matrix.isUnit_det_of_invertible _).ne_zero`.

Take `⟨D, hDd⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = LDL.lowerInv hH * H * (LDL.lowerInv hH)ᴴ` from `⟨_, rfl⟩`. Establish `hDoff : ∀ a c, a ≠ c → D a c = 0`. Introduce `a c hac`. Rewrite using `[hDd, ← hD]`. Conclude with `Matrix.diagonal_apply_ne _ hac`.

Establish `hdpos : ∀ i : Fin r, 0 < (D i i).re ∧ (D i i).im = 0`. Introduce `i`. Establish `hx0 : star (LDL.lowerInv hH i) ≠ 0`. Introduce `h0`. Apply `hLdet` to reduce the goal to its premises.

Apply `Matrix.det_eq_zero_of_row_eq_zero i` to reduce the goal to its premises. Introduce `j`. Establish `h1` using `congrFun h0 j`. Simplify using `using h1`. Establish `hp` using `hH.dotProduct_mulVec_pos hx0`.

Establish `he : D i i = star (star (LDL.lowerInv hH i)) ⬝ᵥ (H *ᵥ star (LDL.lowerInv hH i))`. Rewrite using `[hDd]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, star_star, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`.

Rewrite using `[he]`. Conclude with `⟨(Complex.lt_def.mp hp).1, (Complex.lt_def.mp hp).2.symm⟩`. Take `⟨s, hs⟩ : ∃ s : Fin r → ℝ, s = fun c => (Real.sqrt (D c c).re)⁻¹` from `⟨_, rfl⟩`. Establish `hs0 : ∀ c, s c ≠ 0` using `fun c => by`. Rewrite using `[hs]`.

Conclude with `inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdpos c).1)`. Use `⟨(LDL.lowerInv hH)ᵀ * diagonal (fun c => (s c : ℂ)), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Conclude with `mul_ne_zero hLdet (Finset.prod_ne_zero_iff.mpr fun c _ => Complex.ofReal_ne_zero.mpr (hs0 c))`. Introduce `a c hca`.

Rewrite using `[Matrix.mul_diagonal, Matrix.transpose_apply, LDL.lowerInv_triangular hH hca, zero_mul]`. Introduce `a c`. Rewrite using `[col_mul_eq, col_mul_eq, Hf_sum_sum]`. Establish `hHkl : ∀ k l, X.Hf x τ (col (mat x τ) k) (col (mat x τ) l) = H k l` using `fun k l => by`. Rewrite using `[hHd]`.

Both sides reduce to the same expression. Simplify using `only [hHkl, Matrix.mul_diagonal, Matrix.transpose_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hDd]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]`.

Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`. Use `_ = if a = c then 1 else 0 := by`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality.

Rewrite using `[if_pos rfl]`. Establish `hr` using `(hdpos a).1`. Establish `hre : D a a = ((D a a).re : ℂ)` using `Complex.ext rfl (by simp [(hdpos a).2])`. Establish `hsq : Real.sqrt (D a a).re * Real.sqrt (D a a).re = (D a a).re` using `Real.mul_self_sqrt hr.le`. Establish `hne : Real.sqrt (D a a).re ≠ 0` using `Real.sqrt_ne_zero'.mpr hr`.

Establish `h1 : s a * s a * (D a a).re = 1`. Rewrite using `[hs, ← hsq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hre]`. Conclude with `h1` after adjusting the coercions.

Rewrite using `[if_neg hac, hDoff a c hac, mul_zero]`.
-/
theorem exists_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, B.det ≠ 0 ∧ (∀ a c : Fin r, c < a → B a c = 0) ∧
      ∀ a c : Fin r, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) =
        if a = c then 1 else 0 := by
  have hH := hgram_posDef X hx τ
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ,
      H = Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c) := ⟨_, rfl⟩
  rw [← hHd] at hH
  have hD := LDL.diag_eq_lowerInv_conj hH
  have hLdet : (LDL.lowerInv hH).det ≠ 0 := (Matrix.isUnit_det_of_invertible _).ne_zero
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ,
      D = LDL.lowerInv hH * H * (LDL.lowerInv hH)ᴴ := ⟨_, rfl⟩
  have hDoff : ∀ a c, a ≠ c → D a c = 0 := by
    intro a c hac
    rw [hDd, ← hD]
    exact Matrix.diagonal_apply_ne _ hac
  have hdpos : ∀ i : Fin r, 0 < (D i i).re ∧ (D i i).im = 0 := by
    intro i
    have hx0 : star (LDL.lowerInv hH i) ≠ 0 := by
      intro h0
      apply hLdet
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      have h1 := congrFun h0 j
      simpa using h1
    have hp := hH.dotProduct_mulVec_pos hx0
    have he : D i i = star (star (LDL.lowerInv hH i)) ⬝ᵥ (H *ᵥ star (LDL.lowerInv hH i)) := by
      rw [hDd]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
        star_star, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [he]
    exact ⟨(Complex.lt_def.mp hp).1, (Complex.lt_def.mp hp).2.symm⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin r → ℝ, s = fun c => (Real.sqrt (D c c).re)⁻¹ := ⟨_, rfl⟩
  have hs0 : ∀ c, s c ≠ 0 := fun c => by
    rw [hs]
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdpos c).1)
  refine ⟨(LDL.lowerInv hH)ᵀ * diagonal (fun c => (s c : ℂ)), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero hLdet (Finset.prod_ne_zero_iff.mpr fun c _ =>
      Complex.ofReal_ne_zero.mpr (hs0 c))
  · intro a c hca
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, LDL.lowerInv_triangular hH hca, zero_mul]
  · intro a c
    rw [col_mul_eq, col_mul_eq, Hf_sum_sum]
    have hHkl : ∀ k l, X.Hf x τ (col (mat x τ) k) (col (mat x τ) l) = H k l := fun k l => by
      rw [hHd]
      rfl
    simp only [hHkl, Matrix.mul_diagonal, Matrix.transpose_apply]
    calc _ = (s a : ℂ) * (s c : ℂ) * D a c := by
          rw [hDd]
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, map_mul,
            Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      _ = if a = c then 1 else 0 := by
          by_cases hac : a = c
          · subst hac
            rw [if_pos rfl]
            have hr := (hdpos a).1
            have hre : D a a = ((D a a).re : ℂ) := Complex.ext rfl (by simp [(hdpos a).2])
            have hsq : Real.sqrt (D a a).re * Real.sqrt (D a a).re = (D a a).re :=
              Real.mul_self_sqrt hr.le
            have hne : Real.sqrt (D a a).re ≠ 0 := Real.sqrt_ne_zero'.mpr hr
            have h1 : s a * s a * (D a a).re = 1 := by
              rw [hs, ← hsq]
              field_simp
            rw [hre]
            exact_mod_cast h1
          · rw [if_neg hac, hDoff a c hac, mul_zero]

/- English proof (translation)
Unfold `Data.Hf`. Rewrite using `[hu, two_smul, add_sub_cancel_right]`.
-/
theorem Hf_eq_of_pos (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = u)
    (w : Fin r → ℂ) : X.Hf x τ u w = hermC τ.1 X.Gm u w := by
  unfold Data.Hf
  rw [hu, two_smul, add_sub_cancel_right]

/- English proof (translation)
Unfold `Data.Hf`. Rewrite using `[hu, smul_zero, zero_sub]`. Simplify using `only [hermC, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem Hf_eq_of_zero (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = 0)
    (w : Fin r → ℂ) : X.Hf x τ u w = -hermC τ.1 X.Gm u w := by
  unfold Data.Hf
  rw [hu, smul_zero, zero_sub]
  simp only [hermC, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Establish `hpos : ∀ a : Fin r, (a : ℕ) < X.p0 → X.ppos x τ (col (mat x τ * B) a) = col (mat x τ * B) a`. Introduce `a ha`. Rewrite using `[col_mul_eq, ppos_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < X.p0`.

Establish `h` using `ppos_colP X hx τ ⟨k, hk⟩`. Simplify using `only [Data.colP] at h`. Rewrite `h` using `[show Fin.castLE X.p0_le ⟨(k : ℕ), hk⟩ = k from Fin.ext rfl]`. Rewrite using `[h]`. Rewrite using `[hBt k a (Fin.lt_iff_val_lt_val.mpr (by omega))]`.

Simplify using the standard rewrite rules. Establish `hzero : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → X.ppos x τ (col (mat x τ * B) a) = 0`. Introduce `a ha`. Establish `h1 : ∀ j : Fin r, (j : ℕ) < X.p0 → hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) j) = 0`. Introduce `j hj`.

Establish `hne : a ≠ j` using `fun h => by`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h` using `hB a j`. Rewrite `h` using `[if_neg hne]`.

Unfold `Data.Hf at h`. Rewrite `h` using `[hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X x τ, hpos j hj]`. Take the linear combination `h`. Establish `hBinv : ∀ i j : Fin r, j < i → B⁻¹ i j = 0` using `by haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hBd)`. Introduce `i j hij`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i' j' h' => hBt i' j' h' : B.BlockTriangular id) hij`. Establish `hc : ∀ k, col (mat x τ) k = ∑ j, B⁻¹ j k • col (mat x τ * B) j`. Introduce `k`. Establish `hY : mat x τ = (mat x τ * B) * B⁻¹`. Rewrite using `[mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hBd), mul_one]`.

Use `conv_lhs => rw [hY]`. Conclude with `col_mul_eq (mat x τ * B) B⁻¹ k`. Establish `h2 : ∀ b : Fin X.p0, hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0`. Introduce `b`. Rewrite using `[hc, hermC_sum_right_lemma_2]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) < X.p0`. Rewrite using `[h1 j hj, mul_zero]`. Rewrite using `[hBinv j (Fin.castLE X.p0_le b) (Fin.lt_iff_val_lt_val.mpr (by simp only [Fin.coe_castLE]; omega)), map_zero, zero_mul]`. Unfold `Data.ppos`.

Simplify using `only [h2, zero_mul, Finset.sum_const_zero, zero_smul]`. Use extensionality with `a c`. Use `show hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) c) = diagonal _ a c`. Rewrite using `[Matrix.diagonal_apply]`. Establish `hBac` using `hB a c`.

Distinguish the cases in `ha : (a : ℕ) < X.p0`. Rewrite `hBac` using `[Hf_eq_of_pos X x τ (hpos a ha)]`. Rewrite using `[hBac]`. Simplify using `only [sgn, if_pos ha, Complex.ofReal_one]`. Rewrite `hBac` using `[Hf_eq_of_zero X x τ (hzero a (not_lt.mp ha))]`.

Rewrite using `[neg_eq_iff_eq_neg.mp hBac]`. Simplify using `only [sgn, if_neg ha, Complex.ofReal_neg, Complex.ofReal_one]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gram_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0) (hBt : ∀ a c : Fin r, c < a → B a c = 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0) :
    gram τ.1 X.Gm (mat x τ * B) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  have hpos : ∀ a : Fin r, (a : ℕ) < X.p0 →
      X.ppos x τ (col (mat x τ * B) a) = col (mat x τ * B) a := by
    intro a ha
    rw [col_mul_eq, ppos_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0
    · have h := ppos_colP X hx τ ⟨k, hk⟩
      simp only [Data.colP] at h
      rw [show Fin.castLE X.p0_le ⟨(k : ℕ), hk⟩ = k from Fin.ext rfl] at h
      rw [h]
    · rw [hBt k a (Fin.lt_iff_val_lt_val.mpr (by omega))]
      simp
  have hzero : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → X.ppos x τ (col (mat x τ * B) a) = 0 := by
    intro a ha
    have h1 : ∀ j : Fin r, (j : ℕ) < X.p0 →
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) j) = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => by
        subst h
        omega
      have h := hB a j
      rw [if_neg hne] at h
      unfold Data.Hf at h
      rw [hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X x τ, hpos j hj] at h
      linear_combination h
    have hBinv : ∀ i j : Fin r, j < i → B⁻¹ i j = 0 := by
      haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hBd)
      intro i j hij
      exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
        (fun i' j' h' => hBt i' j' h' : B.BlockTriangular id) hij
    have hc : ∀ k, col (mat x τ) k = ∑ j, B⁻¹ j k • col (mat x τ * B) j := by
      intro k
      have hY : mat x τ = (mat x τ * B) * B⁻¹ := by
        rw [mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hBd), mul_one]
      conv_lhs => rw [hY]
      exact col_mul_eq (mat x τ * B) B⁻¹ k
    have h2 : ∀ b : Fin X.p0,
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
      intro b
      rw [hc, hermC_sum_right_lemma_2]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < X.p0
      · rw [h1 j hj, mul_zero]
      · rw [hBinv j (Fin.castLE X.p0_le b)
          (Fin.lt_iff_val_lt_val.mpr (by simp only [Fin.coe_castLE]; omega)), map_zero, zero_mul]
    unfold Data.ppos
    simp only [h2, zero_mul, Finset.sum_const_zero, zero_smul]
  ext a c
  show hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) c) = diagonal _ a c
  rw [Matrix.diagonal_apply]
  have hBac := hB a c
  by_cases ha : (a : ℕ) < X.p0
  · rw [Hf_eq_of_pos X x τ (hpos a ha)] at hBac
    rw [hBac]
    simp only [sgn, if_pos ha, Complex.ofReal_one]
  · rw [Hf_eq_of_zero X x τ (hzero a (not_lt.mp ha))] at hBac
    rw [neg_eq_iff_eq_neg.mp hBac]
    simp only [sgn, if_neg ha, Complex.ofReal_neg, Complex.ofReal_one]
    split_ifs <;> simp

/- English proof (translation)
Establish `hdetY : (mat x τ * B).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hx τ).1 hBd`. Establish `hv : v = ∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a`. Establish `h1 : (mat x τ * B) *ᵥ ((mat x τ * B)⁻¹ *ᵥ v) = v`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]`. Use `conv_lhs => rw [← h1]`. Use function extensionality and compare the values at `i`. Use `show ∑ k, (mat x τ * B) i k * ((mat x τ * B)⁻¹ *ᵥ v) k = (∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a) i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[maj_eq_lemma_4 X x τ v]`. Use `conv_lhs => rw [hv]`. Rewrite using `[Hf_sum_sum]`. Simplify using `only [hB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.
-/
theorem maj_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0)
    (v : Fin r → ℂ) : X.maj x τ v = ∑ a, ‖((mat x τ * B)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hdetY : (mat x τ * B).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hBd
  have hv : v = ∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a := by
    have h1 : (mat x τ * B) *ᵥ ((mat x τ * B)⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext i
    show ∑ k, (mat x τ * B) i k * ((mat x τ * B)⁻¹ *ᵥ v) k =
      (∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [maj_eq_lemma_4 X x τ v]
  conv_lhs => rw [hv]
  rw [Hf_sum_sum]
  simp only [hB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Use `choose B hBd hBt hB using fun τ => exists_normal X hx τ`. Use `⟨fun τ => B τ, fun τ => ⟨hBd τ, hBt τ⟩, fun τ => ⟨?_, fun v => ?_⟩⟩` and prove the remaining obligations. Conclude with `gram_normal X hx τ (hBd τ) (hBt τ) (hB τ)`. Conclude with `maj_normal X hx τ (hBd τ) (hB τ) v`.
-/
theorem exists_normal_frame {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ,
      gram τ.1 X.Gm (mat (rmul x b) τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
      ∀ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  choose B hBd hBt hB using fun τ => exists_normal X hx τ
  refine ⟨fun τ => B τ, fun τ => ⟨hBd τ, hBt τ⟩, fun τ => ⟨?_, fun v => ?_⟩⟩
  · exact gram_normal X hx τ (hBd τ) (hBt τ) (hB τ)
  · exact maj_normal X hx τ (hBd τ) (hB τ) v

end MajorantNormalForms

end ReciprocityTheory.ChartRestriction.G.FD
