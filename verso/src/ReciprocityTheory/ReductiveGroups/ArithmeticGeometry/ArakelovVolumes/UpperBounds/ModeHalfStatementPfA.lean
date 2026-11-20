import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfA

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)

def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a

noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))

noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]`.
-/
private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b)`. Use function extensionality and compare the values at `b`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Rewrite using `[hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg Matrix.det hY`. Rewrite `h1` using `[gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_diagonal]`. Apply the tactic sequence `exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm`.
-/
private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm

/- English proof (translation)
Establish `hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n`. Introduce `u' n`. Rewrite using `[hermC_mulVec_eq_dotProduct_gram, hY]`. Simplify using `only [sf, dotProduct, Matrix.mulVec_diagonal]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Establish `hdetY` using `det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY`. Establish `hv : v = Y *ᵥ (Y⁻¹ *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]`. Establish `hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a`. Introduce `a`.

Rewrite using `[hw]`. Use function extensionality and compare the values at `k`. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hgp : X.gramPos w τ = Ag X.p0 X.p0_le N`. Use extensionality with `a b`.

Simplify using `only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]`. Rewrite using `[hcol, hcol, hS]`. Unfold `Data.maj Data.posPart Ms`. Rewrite using `[hgp]`. Use `conv_lhs => rw [hv]`.

Simplify using `only [hcol, hS]`.
-/
theorem maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]

/- English proof (translation)
Introduce `τ`. Establish `hY` using `hu τ`. Use `⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩` and prove the remaining obligations. Establish `hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ)`. Unfold `dmin lminor`.

Rewrite using `[hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]`. Simplify using `only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]`. Conclude with `Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i`. Rewrite using `[hd, Complex.ofReal_re]`. Apply the tactic sequence `have hne : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num`.

Conclude with `mul_self_pos.mpr hne`.
-/
theorem dom_of_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) : u ∈ X.dom := by
  intro τ
  have hY := hu τ
  refine ⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩
  have hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

/- English proof (translation)
Establish `hY` using `hu τ`. Use `set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN`. Establish `hw : mat u τ = mat u τ * Matrix.of N`. Rewrite using `[show Matrix.of N = 1 from rfl, Matrix.mul_one]`. Rewrite using `[maj_chart X hY N hw v]`.

Use `set w := (mat u τ)⁻¹ *ᵥ v`. Establish `hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b`. Introduce `α b`. Unfold `sf cl`. Rewrite using `[Finset.sum_eq_single b]`.

Simplify using `[hN]`. Introduce `k _ hk`. Simplify using `[hN, Matrix.one_apply_ne hk]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.

Establish `hAg : Ag X.p0 X.p0_le N = 1`. Use extensionality with `a b`. Simplify using `only [Ag, Matrix.of_apply, hsf]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[cl, hN, sgn]`. Establish `hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a` using `fun h => hab (Fin.castLE_injective _ h).symm`. Simplify using `[cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]`. Establish `hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) = ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0`. Introduce `g`.

Rewrite using `[← Finset.sum_filter]`. Establish `hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) = Finset.univ.map (Fin.castLEEmb X.p0_le)`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `hk`. Conclude with `⟨⟨k, hk⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `a.isLt`. Rewrite using `[hset, Finset.sum_map]`.

Both sides reduce to the same expression. Establish `hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) * (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) = ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ)`. Introduce `a`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul]) (fun h => absurd (Finset.mem_univ a) h)]`. Rewrite using `[Matrix.one_apply_eq, mul_one, hsf]`.

Establish `ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0` using `by simp`. Simplify using `only [sgn, ha, if_true, Complex.ofReal_one, one_mul]`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2`. Unfold `sf`.

Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]`. Unfold `Ms`. Rewrite using `[hAg, inv_one]`.

Simplify using `only [hinner]`. Rewrite using `[← Complex.ofReal_sum, Complex.ofReal_re, hww]`. Establish `hc` using `hcast (fun k => ‖w k‖ ^ 2)`. Use `beta_reduce at hc`. Rewrite using `[hc, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem maj_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj u τ v = ∑ a, ‖((mat u τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hY := hu τ
  set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN
  have hw : mat u τ = mat u τ * Matrix.of N := by
    rw [show Matrix.of N = 1 from rfl, Matrix.mul_one]
  rw [maj_chart X hY N hw v]
  set w := (mat u τ)⁻¹ *ᵥ v
  have hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b := by
    intro α b
    unfold sf cl
    rw [Finset.sum_eq_single b]
    · simp [hN]
    · intro k _ hk
      simp [hN, Matrix.one_apply_ne hk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hAg : Ag X.p0 X.p0_le N = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, hsf]
    by_cases hab : a = b
    · subst hab
      simp [cl, hN, sgn]
    · have hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a :=
        fun h => hab (Fin.castLE_injective _ h).symm
      simp [cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0 := by
    intro g
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) =
        Finset.univ.map (Fin.castLEEmb X.p0_le) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hset, Finset.sum_map]
    rfl
  have hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) =
      ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [Matrix.one_apply_eq, mul_one, hsf]
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp
    simp only [sgn, ha, if_true, Complex.ofReal_one, one_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2 := by
    unfold sf
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold Ms
  rw [hAg, inv_one]
  simp only [hinner]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, hww]
  have hc := hcast (fun k => ‖w k‖ ^ 2)
  beta_reduce at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sgn
  split_ifs <;> ring

end ModeHalfA

end ReciprocityTheory.ChartRestriction.G.AR.Up
