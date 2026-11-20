import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.DetToMatrixSq

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticLatticeForms

open Matrix NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `h : τ.1 X.ξ0 ≠ 0` using `(map_ne_zero τ.1).mpr X.ξ0_ne`. Unfold `Data.c`. Conclude with `mul_pos two_pos (norm_pos_iff.mpr h)`.
-/
theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  unfold Data.c
  exact mul_pos two_pos (norm_pos_iff.mpr h)

noncomputable def ip (u w : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, X.c τ * (∑ a, u τ a * conj (w τ a)).re

/- English proof (translation)
Simplify using `only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re, mul_add]`.
-/
theorem ip_add_left (u u' w : X.Ψ → Fin r → ℂ) : ip X (u + u') w = ip X u w + ip X u' w := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re, mul_add]

/- English proof (translation)
Simplify using `only [ip, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, Complex.add_re]`.
-/
theorem ip_add_right (u w w' : X.Ψ → Fin r → ℂ) : ip X u (w + w') = ip X u w + ip X u w' := by
  simp only [ip, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

/- English proof (translation)
Unfold `ip`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h : (∑ a, (k • u) τ a * conj (w τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_smul_left (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X (k • u) w = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, (k • u) τ a * conj (w τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Unfold `ip`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h : (∑ a, u τ a * conj ((k • w) τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_smul_right (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X u (k • w) = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, u τ a * conj ((k • w) τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

noncomputable def ipB : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ip X) (ip_add_left X) (ip_smul_left X) (ip_add_right X) (ip_smul_right X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ipB_apply (u w : X.Ψ → Fin r → ℂ) : ipB X u w = ip X u w := rfl

/- English proof (translation)
Unfold `ip`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Complex.re_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_comm (u w : X.Ψ → Fin r → ℂ) : ip X u w = ip X w u := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Unfold `ip`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.
-/
theorem ip_self (u : X.Ψ → Fin r → ℂ) : ip X u u = ∑ τ, X.c τ * ∑ a, ‖u τ a‖ ^ 2 := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[ip_self]`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, u τ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hu (funext h)`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, u τ a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hτ (funext h)`. Apply `Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X i).le (Finset.sum_nonneg fun b _ => sq_nonneg _))` to reduce the goal to its premises.

Use `⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) ?_⟩` and prove the remaining obligations. Apply `Finset.sum_pos' (fun b _ => sq_nonneg _)` to reduce the goal to its premises. Conclude with `⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩`.
-/
theorem ip_pos {u : X.Ψ → Fin r → ℂ} (hu : u ≠ 0) : 0 < ip X u u := by
  rw [ip_self]
  obtain ⟨τ, hτ⟩ : ∃ τ, u τ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ : ∃ a, u τ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hτ (funext h)
  apply Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X i).le
    (Finset.sum_nonneg fun b _ => sq_nonneg _))
  refine ⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) ?_⟩
  apply Finset.sum_pos' (fun b _ => sq_nonneg _)
  exact ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

noncomputable def Ly (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := (y τ)⁻¹ *ᵥ u τ
  map_add' u w := by funext τ; simp [Matrix.mulVec_add]
  map_smul' k u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Complex.real_smul]

noncomputable def Sg : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sgn_sq (a : ℕ) : sgn X.p0 a * sgn X.p0 a = 1 := by
  unfold sgn
  split_ifs <;> norm_num

noncomputable def Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 v) a‖ ^ 2

/- English proof (translation)
Rewrite using `[ip_self]`. Both sides reduce to the same expression.
-/
theorem ip_Ly_self (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ip X (Ly X y (X.embV v)) (Ly X y (X.embV v)) = Qy X y v := by
  rw [ip_self]
  rfl

/- English proof (translation)
Unfold `Qy`. Conclude with `Finset.sum_nonneg fun τ _ => mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => sq_nonneg _)`.
-/
theorem Qy_nonneg (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : 0 ≤ Qy X y v := by
  unfold Qy
  exact Finset.sum_nonneg fun τ _ => mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => sq_nonneg _)

/- English proof (translation)
Use function extensionality and compare the values at `τ a`. Simplify using `only [Data.embV, Data.emb, Finset.sum_apply, map_sum]`.
-/
theorem embV_sum {ι : Type} (s : Finset ι) (w : ι → Fin r → E) :
    X.embV (∑ i ∈ s, w i) = ∑ i ∈ s, X.embV (w i) := by
  funext τ a
  simp only [Data.embV, Data.emb, Finset.sum_apply, map_sum]

/- English proof (translation)
Use function extensionality and compare the values at `τ a`. Simplify using `only [Data.embV, Data.emb, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, Complex.real_smul, Complex.ofReal_intCast]`.
-/
theorem embV_zsmul (n : ℤ) (w : Fin r → E) : X.embV (n • w) = (n : ℝ) • X.embV w := by
  funext τ a
  simp only [Data.embV, Data.emb, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
    Complex.real_smul, Complex.ofReal_intCast]

/- English proof (translation)
Introduce `u u' h`. Use function extensionality and compare the values at `τ`. Establish `h1 : (y τ)⁻¹ *ᵥ u τ = (y τ)⁻¹ *ᵥ u' τ` using `congrFun h τ`. Establish `hu : IsUnit (y τ).det` using `isUnit_iff_ne_zero.mpr (hy τ)`. Establish `h2` using `congrArg (fun v => y τ *ᵥ v) h1`.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2`. Conclude with `h2`.
-/
theorem Ly_injective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Injective (Ly X y) := by
  intro u u' h
  funext τ
  have h1 : (y τ)⁻¹ *ᵥ u τ = (y τ)⁻¹ *ᵥ u' τ := congrFun h τ
  have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr (hy τ)
  have h2 := congrArg (fun v => y τ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

/- English proof (translation)
Introduce `v`. Use `⟨fun τ => y τ *ᵥ v τ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `(y τ)⁻¹ *ᵥ (y τ *ᵥ v τ) = v τ`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hy τ)), Matrix.one_mulVec]`.
-/
theorem Ly_surjective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Surjective (Ly X y) := by
  intro v
  refine ⟨fun τ => y τ *ᵥ v τ, ?_⟩
  funext τ
  change (y τ)⁻¹ *ᵥ (y τ *ᵥ v τ) = v τ
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hy τ)), Matrix.one_mulVec]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def Am (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ip X (Ly X y (X.embV (g i : Fin r → E))) (Ly X y (X.embV (g j : Fin r → E)))

noncomputable def Bm (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm X.Gm (g i : Fin r → E) (g j : Fin r → E))).re

/- English proof (translation)
Establish `hL : Ly X y (∑ i, x i • X.embV (g i : Fin r → E)) = ∑ i, x i • Ly X y (X.embV (g i : Fin r → E))`. Simplify using `only [map_sum, map_smul]`. Rewrite using `[hL, ← ipB_apply]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ipB_apply]`. Simplify using `only [dotProduct, Matrix.mulVec, Am, Matrix.of_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ip_comm X (Ly X y (X.embV (g j : Fin r → E)))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_eq (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℝ) :
    x ⬝ᵥ (Am X y g *ᵥ x) = ip X (Ly X y (∑ i, x i • X.embV (g i : Fin r → E)))
      (Ly X y (∑ i, x i • X.embV (g i : Fin r → E))) := by
  have hL : Ly X y (∑ i, x i • X.embV (g i : Fin r → E)) =
      ∑ i, x i • Ly X y (X.embV (g i : Fin r → E)) := by
    simp only [map_sum, map_smul]
  rw [hL, ← ipB_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ipB_apply]
  simp only [dotProduct, Matrix.mulVec, Am, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ip_comm X (Ly X y (X.embV (g j : Fin r → E)))]
  ring

/- English proof (translation)
Rewrite using `[quad_eq, ← ip_Ly_self, embV_sum]`. Simplify using `only [embV_zsmul]`.
-/
theorem quad_int (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℤ) :
    (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) =
      Qy X y (∑ i, x i • (g i : Fin r → E)) := by
  rw [quad_eq, ← ip_Ly_self, embV_sum]
  simp only [embV_zsmul]

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, star_trivial, Am, of_apply]`. Conclude with `ip_comm X _ _`. Rewrite using `[star_trivial, quad_eq]`.

Use `ip_pos X fun h0 => hx ?_` and prove the remaining obligations. Establish `h1 : ∑ i, x i • X.embV (g i : Fin r → E) = 0` using `Ly_injective X y hy (by rw [h0, map_zero])`. Conclude with `funext (Fintype.linearIndependent_iff.mp (RealPlaceEmbeddings.linIndR X g) x h1)`.
-/
theorem Am_posDef (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0)
    (g : Basis ι ℤ X.Λ) : (Am X y g).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial, Am, of_apply]
    exact ip_comm X _ _
  · rw [star_trivial, quad_eq]
    refine ip_pos X fun h0 => hx ?_
    have h1 : ∑ i, x i • X.embV (g i : Fin r → E) = 0 := Ly_injective X y hy (by rw [h0, map_zero])
    exact funext (Fintype.linearIndependent_iff.mp (RealPlaceEmbeddings.linIndR X g) x h1)

end QuadraticLatticeForms

end ReciprocityTheory.ChartRestriction.G.FD
