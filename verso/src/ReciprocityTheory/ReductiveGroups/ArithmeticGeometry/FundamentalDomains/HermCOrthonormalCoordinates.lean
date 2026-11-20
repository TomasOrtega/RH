import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def mjip {n : ℕ} (p q : Fin n → ℂ) : ℂ := ∑ i, p i * conj (q i)

/- English proof (translation)
Simplify using `only [mjip, nsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
lemma mjip_self {n : ℕ} (p : Fin n → ℂ) : mjip p p = ((nsq p : ℝ) : ℂ) := by
  simp only [mjip, nsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/- English proof (translation)
Unfold `mjip nsq`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma mjip_norm_le {n : ℕ} (p q : Fin n → ℂ) :
    ‖mjip p q‖ ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) := by
  unfold mjip nsq
  calc ‖∑ i, p i * conj (q i)‖ ≤ ∑ i, ‖p i * conj (q i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖p i‖ * ‖q i‖ := by simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/- English proof (translation)
Unfold `mjip`. Rewrite using `[Finset.sum_eq_single d (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
lemma mjip_single {n : ℕ} (p : Fin n → ℂ) (d : Fin n) : mjip p (Pi.single d 1) = p d := by
  unfold mjip
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

/- English proof (translation)
Simplify using `[mjip]`.
-/
lemma mjip_zero_right {n : ℕ} (p : Fin n → ℂ) : mjip p 0 = 0 := by
  simp [mjip]

/- English proof (translation)
Unfold `nsq mjip`. Rewrite using `[Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mjnsq_sub_smul {n : ℕ} (p q : Fin n → ℂ) (t : ℝ) :
    nsq (p - (t : ℂ) • q) = nsq p - 2 * t * (mjip p q).re + t ^ 2 * nsq q := by
  unfold nsq mjip
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def mjpa (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)

def mjpb (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)

/- English proof (translation)
Simplify using `[nsq]`.
-/
lemma nsq_zero' {n : ℕ} : nsq (0 : Fin n → ℂ) = 0 := by
  simp [nsq]

/- English proof (translation)
Unfold `hermC`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private lemma hermC_fin_sum_smul_left {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (p : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) v = ∑ i, p i * hermC τ G (f i) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Unfold `hermC`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private lemma hermC_fin_sum_smul_right_mul_conj {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (u : Fin r → ℂ)
    (q : Fin n → ℂ) (f : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ j, q j • f j) = ∑ j, hermC τ G u (f j) * conj (q j) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Rewrite using `[hermC_fin_sum_smul_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_fin_sum_smul_right_mul_conj, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
lemma hermC_bilin (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) (∑ j, q j • f j) =
      ∑ i, ∑ j, p i * hermC τ G (f i) (f j) * conj (q j) := by
  rw [hermC_fin_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_fin_sum_smul_right_mul_conj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Set `e : Fin p0 ⊕ Fin (n - p0) ≃ Fin n` to `finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))`. Rewrite using `[← e.sum_comp f, Fintype.sum_sum_type]`. Use `congr 1`. Apply the tactic sequence `all_goals exact Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext (by simp [e]))`.
-/
private lemma sum_fin_eq_sum_castLE_add_sum_shift {M : Type} [AddCommMonoid M] {p0 n : ℕ} (h : p0 ≤ n) (f : Fin n → M) :
    ∑ i, f i = ∑ a : Fin p0, f (Fin.castLE h a) +
      ∑ m : Fin (n - p0), f ⟨p0 + m, by have := m.isLt; omega⟩ := by
  let e : Fin p0 ⊕ Fin (n - p0) ≃ Fin n := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))
  rw [← e.sum_comp f, Fintype.sum_sum_type]
  congr 1
  all_goals exact Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext (by simp [e]))

/- English proof (translation)
Establish `hM : ∀ u : Fin r → ℂ, mat x τ *ᵥ u = ∑ c, u c • col (mat x τ) c`. Introduce `u`. Use extensionality with `k`. Simplify using `[Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]`. Establish `hij : ∀ i j, hermC τ.1 X.Gm (col (mat x τ) i) (col (mat x τ) j) = if i = j then ((sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0`.

Introduce `i j`. Use `congrFun (congrFun (ho τ) i) j` as an intermediate fact. Simplify `this` using `[gram, Matrix.diagonal_apply]`. Rewrite using `[hM p, hM q, hermC_bilin]`. Simplify using `only [hij, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[sum_fin_eq_sum_castLE_add_sum_shift X.p0_le]`. Simplify using `only [mjip, mjpa, mjpb, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[sgn, mjpa, a.isLt]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `[sgn, mjpb, nI]`.
-/
lemma hermC_orthonormal_coordinates {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (p q : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ p) (mat x τ *ᵥ q) =
      mjip (mjpa X p) (mjpa X q) - mjip (mjpb X p) (mjpb X q) := by
  have hM : ∀ u : Fin r → ℂ, mat x τ *ᵥ u = ∑ c, u c • col (mat x τ) c := by
    intro u
    ext k
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hij : ∀ i j, hermC τ.1 X.Gm (col (mat x τ) i) (col (mat x τ) j) =
      if i = j then ((sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun (ho τ) i) j
    simpa [gram, Matrix.diagonal_apply] using this
  rw [hM p, hM q, hermC_bilin]
  simp only [hij, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_fin_eq_sum_castLE_add_sum_shift X.p0_le]
  simp only [mjip, mjpa, mjpb, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [sgn, mjpa, a.isLt]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp [sgn, mjpb, nI]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Both sides reduce to the same expression.
-/
lemma mj_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (c : Fin X.p0) :
    X.colP (X.xZ x Z) τ c = mat x τ *ᵥ col (X.lowBlock Z τ) (Fin.castLE X.p0_le c) := by
  funext k
  rfl

def mjg (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : Fin r → ℂ :=
  ∑ c, δ c • col (X.lowBlock Z τ) (Fin.castLE X.p0_le c)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `ha : ¬ (X.p0 ≤ (a : ℕ))` using `not_le.2 a.isLt`. Simplify using `[mjpa, mjg, Finset.sum_apply, col, Data.lowBlock, ha, Fin.castLE_inj]`.
-/
lemma mjg_pa (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : mjpa X (mjg X Z τ δ) = δ := by
  funext a
  have ha : ¬ (X.p0 ≤ (a : ℕ)) := not_le.2 a.isLt
  simp [mjpa, mjg, Finset.sum_apply, col, Data.lowBlock, ha, Fin.castLE_inj]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [mjpb, mjg, nI, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Data.lowBlock, Matrix.of_apply, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hne : ¬ ((⟨X.p0 + (m : ℕ), by have` using `m.isLt; have := X.p0_le; omega⟩ : Fin r) = Fin.castLE X.p0_le c) := by`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `hlt : X.p0 ≤ X.p0 + (m : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0` using `⟨by omega, by simp⟩`. Rewrite using `[if_neg hne, dif_pos hlt, zero_add, mul_comm]`.

Apply the tactic sequence `congr 2 <;> ext <;> simp`.
-/
lemma mjg_pb (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    mjpb X (mjg X Z τ δ) = Matrix.of (Z τ) *ᵥ δ := by
  funext m
  simp only [mjpb, mjg, nI, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Data.lowBlock, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ¬ ((⟨X.p0 + (m : ℕ), by have := m.isLt; have := X.p0_le; omega⟩ : Fin r) =
      Fin.castLE X.p0_le c) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlt : X.p0 ≤ X.p0 + (m : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := ⟨by omega, by simp⟩
  rw [if_neg hne, dif_pos hlt, zero_add, mul_comm]
  congr 2 <;> ext <;> simp

/- English proof (translation)
Simplify using `only [mj_colP, mjg, Matrix.mulVec_sum, Matrix.mulVec_smul]`.
-/
lemma mj_sum_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    ∑ c, δ c • X.colP (X.xZ x Z) τ c = mat x τ *ᵥ mjg X Z τ δ := by
  simp only [mj_colP, mjg, Matrix.mulVec_sum, Matrix.mulVec_smul]

/- English proof (translation)
Establish `hG` using `X.gramPos_posDef hy τ`. Establish `hdet : IsUnit (X.gramPos (X.xZ x Z) τ).det` using `by open scoped ComplexOrder in exact hG.det_pos.ne'.isUnit`. Establish `hGi : (X.gramPos (X.xZ x Z) τ)⁻¹.IsHermitian` using `(X.gramPos_isHermitian (X.xZ x Z) τ).inv`. Establish `hconj : ∀ a b, conj ((X.gramPos (X.xZ x Z) τ)⁻¹ b a) = (X.gramPos (X.xZ x Z) τ)⁻¹ a b` using `fun a b => hGi.apply a b`. Take `⟨β, hβ⟩ : ∃ β : Fin X.p0 → ℂ, ∀ b, β b = hermC τ.1 X.Gm (mat x τ *ᵥ w) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le b))` from `⟨_, fun _ => rfl⟩`.

Establish `hβ' : ∀ b, β b = hermC τ.1 X.Gm (mat x τ *ᵥ w) (X.colP (X.xZ x Z) τ b)` using `hβ`. Take `⟨γ, hγ⟩ : ∃ γ : Fin X.p0 → ℂ, ∀ a, γ a = ∑ b, β b * (X.gramPos (X.xZ x Z) τ)⁻¹ b a` from `⟨_, fun _ => rfl⟩`. Establish `K : ∀ c, hermC τ.1 X.Gm (∑ a, γ a • X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c) = β c`. Introduce `c`. Rewrite using `[hermC_fin_sum_smul_left]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← X.gramPos_apply, hγ, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring`. Use `_ = β c := by`.

Rewrite using `[Matrix.nonsing_inv_mul _ hdet, Finset.sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Matrix.one_apply_ne hb]`. Simplify using the standard rewrite rules.

Establish `P : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ w) = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)`. Establish `e3` using `hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ γ)`. Simplify using `only [mjg_pa, mjg_pb, mjip_self] at e3`. Rewrite `e3` using `[← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj]`. Simplify using `only [K] at e3`.

Establish `hre : (∑ c, β c * conj (γ c)).re = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)`. Rewrite using `[e3]`. Simplify using the standard rewrite rules. Rewrite using `[← hre, Data.posPart]`. Use `congr 1`.

Simplify using `only [← hβ]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hγ a, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hconj]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨γ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Data.maj, P, hermC_orthonormal_coordinates X ho τ w w, mjip_self, mjip_self]`. Simplify using the standard rewrite rules. Introduce `δ`.

Establish `e1` using `hermC_orthonormal_coordinates X ho τ w (mjg X Z τ δ)`. Establish `e2` using `hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ δ)`. Simplify using `only [mjg_pa, mjg_pb] at e1 e2`. Rewrite using `[← e1, ← e2, ← mj_sum_colP X x Z τ δ, ← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj, hermC_fin_sum_smul_right_mul_conj]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[K c, hβ']`.
-/
lemma mj_coord {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (hy : X.xZ x Z ∈ X.dom)
    (τ : X.Ψ) (w : Fin r → ℂ) : ∃ γ : Fin X.p0 → ℂ,
      X.maj (X.xZ x Z) τ (mat x τ *ᵥ w) =
        2 * (nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) ∧
      ∀ δ, mjip (mjpa X w) δ - mjip (mjpb X w) (Matrix.of (Z τ) *ᵥ δ) =
        mjip γ δ - mjip (Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
  have hG := X.gramPos_posDef hy τ
  have hdet : IsUnit (X.gramPos (X.xZ x Z) τ).det := by open scoped ComplexOrder in exact hG.det_pos.ne'.isUnit
  have hGi : (X.gramPos (X.xZ x Z) τ)⁻¹.IsHermitian := (X.gramPos_isHermitian (X.xZ x Z) τ).inv
  have hconj : ∀ a b, conj ((X.gramPos (X.xZ x Z) τ)⁻¹ b a) = (X.gramPos (X.xZ x Z) τ)⁻¹ a b :=
    fun a b => hGi.apply a b
  obtain ⟨β, hβ⟩ : ∃ β : Fin X.p0 → ℂ, ∀ b, β b =
      hermC τ.1 X.Gm (mat x τ *ᵥ w) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le b)) :=
    ⟨_, fun _ => rfl⟩
  have hβ' : ∀ b, β b = hermC τ.1 X.Gm (mat x τ *ᵥ w) (X.colP (X.xZ x Z) τ b) := hβ
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin X.p0 → ℂ, ∀ a, γ a = ∑ b, β b * (X.gramPos (X.xZ x Z) τ)⁻¹ b a :=
    ⟨_, fun _ => rfl⟩
  have K : ∀ c, hermC τ.1 X.Gm (∑ a, γ a • X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c) = β c := by
    intro c
    rw [hermC_fin_sum_smul_left]
    calc ∑ a, γ a * hermC τ.1 X.Gm (X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c)
        = ∑ b, β b * ((X.gramPos (X.xZ x Z) τ)⁻¹ * X.gramPos (X.xZ x Z) τ) b c := by
          simp only [← X.gramPos_apply, hγ, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
      _ = β c := by
          rw [Matrix.nonsing_inv_mul _ hdet, Finset.sum_eq_single c]
          · simp
          · intro b _ hb
            simp [Matrix.one_apply_ne hb]
          · simp
  have P : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ w) = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
    have e3 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ γ)
    simp only [mjg_pa, mjg_pb, mjip_self] at e3
    rw [← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj] at e3
    simp only [K] at e3
    have hre : (∑ c, β c * conj (γ c)).re = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
      rw [e3]
      simp
    rw [← hre, Data.posPart]
    congr 1
    simp only [← hβ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hγ a, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, hconj]
    ring
  refine ⟨γ, ?_, ?_⟩
  · rw [Data.maj, P, hermC_orthonormal_coordinates X ho τ w w, mjip_self, mjip_self]
    simp
  · intro δ
    have e1 := hermC_orthonormal_coordinates X ho τ w (mjg X Z τ δ)
    have e2 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ δ)
    simp only [mjg_pa, mjg_pb] at e1 e2
    rw [← e1, ← e2, ← mj_sum_colP X x Z τ δ, ← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj, hermC_fin_sum_smul_right_mul_conj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [K c, hβ']

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
