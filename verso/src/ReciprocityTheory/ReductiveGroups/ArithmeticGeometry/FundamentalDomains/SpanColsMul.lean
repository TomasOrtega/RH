import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Am (u : Fin 2 → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin 2) ℂ :=
  Matrix.of fun a i => emb τ.1 (u i) a

noncomputable def Cm (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    Matrix (Fin 2) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

/- English proof (translation)
Use extensionality with `a j`. Simplify using `only [Data.zmat, Data.Am, Data.Cm, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zmat_eq (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 + X.Am u τ * X.Cm u b τ := by
  ext a j
  simp only [Data.zmat, Data.Am, Data.Cm, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Data.Cm, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Cm_add (u : Fin 2 → Fin r → E) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.Cm u (b + b') τ = X.Cm u b τ + X.Cm u b' τ := by
  ext i j
  simp only [Data.Cm, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma Cm_mulVec_apply (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  simp only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Use extensionality with `i i'`. Establish `e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i` using `rfl`. Rewrite using `[e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]`. Simplify using `only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]`.
-/
theorem Cm_mul_Am (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : X.Cm u b τ * X.Am u τ = 0 := by
  ext i i'
  have e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i := rfl
  rw [e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]
  simp only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Establish `h` using `X.Cm_mul_Am u hu b τ`. Rewrite using `[X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Use `_ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by`. Rewrite using `[h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]`.
-/
theorem zmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  have h := X.Cm_mul_Am u hu b τ
  rw [X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]
  calc (1 + X.Am u τ * X.Cm u b τ) * (1 + X.Am u τ * X.Cm u b' τ)
      = 1 + X.Am u τ * X.Cm u b τ + X.Am u τ * X.Cm u b' τ +
          X.Am u τ * (X.Cm u b τ * X.Am u τ) * X.Cm u b' τ := by
        simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
        abel
    _ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by
        rw [h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]

/- English proof (translation)
Rewrite using `[X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]`.
-/
theorem zmat_det (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : (X.zmat u b τ).det = 1 := by
  rw [X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Matrix.mulVec, dotProduct, Data.Am, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem Am_mulVec (u : Fin 2 → Fin r → E) (τ : X.Ψ) (y : Fin 2 → ℂ) :
    X.Am u τ *ᵥ y = ∑ i, y i • emb τ.1 (u i) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Data.Am, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Conclude with `Cm_mulVec_apply X u b τ v i`.
-/
theorem Cm_mulVec (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  exact Cm_mulVec_apply X u b τ v i

/- English proof (translation)
Establish `hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0` using `fun i k => by`. Rewrite using `[hermC_emb, hu, map_zero]`. Establish `hb' : ∀ i k, conj (b τ i k) = b τ k i` using `fun i k => (hb τ i k).symm`. Establish `hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w` using `fun k => hermC_conj τ.1 X.Gm_herm _ _`. Rewrite using `[X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]`.

Simplify using `only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee, X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zmat_unitary (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hb' : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w :=
    fun k => hermC_conj τ.1 X.Gm_herm _ _
  rw [X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]
  simp only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee,
    X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ`. Rewrite using `[X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]`.
-/
theorem Zb_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) :
    X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x := by
  funext τ
  show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ
  rw [X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[col, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
private lemma col_mul_eq_mulVec_col (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = M *ᵥ col N a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Rewrite using `[X.mat_Zb]`. Use extensionality with `a a'`. Simplify using `only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]`. Conclude with `X.zmat_unitary u hu b hb τ _ _`.
-/
theorem gram_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.Zb u b x) τ) = gram τ.1 X.Gm (mat x τ) := by
  rw [X.mat_Zb]
  ext a a'
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]
  exact X.zmat_unitary u hu b hb τ _ _

/- English proof (translation)
Unfold `dmin`. Rewrite using `[X.gram_Zb u hu b hb x τ]`.
-/
theorem dmin_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [X.gram_Zb u hu b hb x τ]

/- English proof (translation)
Simplify using `only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢`. Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[X.mat_Zb, Matrix.det_mul, X.zmat_det u hu, one_mul]`. Conclude with `(hx τ).1`.

Rewrite using `[X.dmin_Zb u hu b hb]`. Conclude with `(hx τ).2 i`.
-/
theorem Zb_dom (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u b x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [X.mat_Zb, Matrix.det_mul, X.zmat_det u hu, one_mul]
    exact (hx τ).1
  · rw [X.dmin_Zb u hu b hb]
    exact (hx τ).2 i

/- English proof (translation)
Simplify using `only [Data.nfac, X.dmin_Zb u hu b hb]`.
-/
theorem nfac_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (X.Zb u b x) = X.nfac la x := by
  simp only [Data.nfac, X.dmin_Zb u hu b hb]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ = X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ`. Use `congr 1`. Use extensionality with `p q`. Establish `hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) = conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l)` using `fun k => by`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Simplify using `only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowV_uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ =
    X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ
  congr 1
  ext p q
  have hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) =
      conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l) := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
