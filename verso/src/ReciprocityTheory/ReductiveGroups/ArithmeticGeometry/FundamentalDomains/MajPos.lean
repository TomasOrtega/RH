import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryComplementMoveOfIsotropic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `hG` using `X.Gm_herm`. Establish `hAi : ((X.gramPos x τ)⁻¹).IsHermitian` using `(X.gramPos_isHermitian x τ).inv`. Establish `hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b` using `fun a b => hAi.apply a b`. Establish `hS : ∀ u : Fin X.p0 → ℂ, conj (∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b)) = ∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b)`. Introduce `u`.

Simplify using `only [map_sum, map_mul, Complex.conj_conj]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[hM]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : (((∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm v (X.colP x τ b))).re : ℝ) : ℂ) = ∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm v (X.colP x τ b))` using `Complex.conj_eq_iff_re.mp (hS _)`.

Establish `e2 : (((hermC τ.1 X.Gm v v).re : ℝ) : ℂ) = hermC τ.1 X.Gm v v` using `Complex.conj_eq_iff_re.mp (ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG v v)`. Establish `hpp : X.posPart x τ v = (∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm v (X.colP x τ b))).re` using `rfl`. Establish `hmj : X.maj x τ v = 2 * X.posPart x τ v - (hermC τ.1 X.Gm v v).re` using `rfl`. Rewrite using `[X.Hf_eq_two_ppos, X.hermC_ppos_self, hmj, hpp, Complex.ofReal_sub, Complex.ofReal_mul, e1, e2]`. Evaluate the numerical expressions.
-/
lemma Hf_self {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.Hf x τ v v = (X.maj x τ v : ℂ) := by
  have hG := X.Gm_herm
  have hAi : ((X.gramPos x τ)⁻¹).IsHermitian := (X.gramPos_isHermitian x τ).inv
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := fun a b => hAi.apply a b
  have hS : ∀ u : Fin X.p0 → ℂ, conj (∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b)) =
      ∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b) := by
    intro u
    simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    rw [hM]
    ring
  have e1 : (((∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b))).re : ℝ) : ℂ) =
      ∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b)) := Complex.conj_eq_iff_re.mp (hS _)
  have e2 : (((hermC τ.1 X.Gm v v).re : ℝ) : ℂ) = hermC τ.1 X.Gm v v :=
    Complex.conj_eq_iff_re.mp (ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG v v)
  have hpp : X.posPart x τ v = (∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b))).re := rfl
  have hmj : X.maj x τ v = 2 * X.posPart x τ v - (hermC τ.1 X.Gm v v).re := rfl
  rw [X.Hf_eq_two_ppos, X.hermC_ppos_self, hmj, hpp, Complex.ofReal_sub, Complex.ofReal_mul, e1, e2]
  norm_num

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hermC_smul_left_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `(Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)` and prove the remaining obligations. Simplify using `only [mul_assoc]`.
-/
private theorem hermC_finset_sum_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i, c i • u i) w = ∑ i, c i * hermC τ G (u i) w := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  simp only [mul_assoc]

/- English proof (translation)
Rewrite using `[← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_finset_sum_left', map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]`.
-/
private theorem hermC_finset_sum_right_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ)
    (w : Fin r → ℂ) : hermC τ G w (∑ i, c i • u i) = ∑ i, conj (c i) * hermC τ G w (u i) := by
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_finset_sum_left', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]

/- English proof (translation)
Rewrite using `[← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_smul_left_embedding, map_mul, ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]`.
-/
private theorem hermC_smul_right_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G w (c • u) = conj c * hermC τ G w u := by
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_smul_left_embedding, map_mul,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]

/- English proof (translation)
Rewrite using `[hermC_finset_sum_left']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_finset_sum_right_of_conj_symm τ hG, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hermC_sum_smul_sum_smul_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ) :
    hermC τ G (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i * hermC τ G (u i) (u j) * conj (c j) := by
  rw [hermC_finset_sum_left']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_finset_sum_right_of_conj_symm τ hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hG` using `X.Gm_herm`. Establish `hApd : (X.gramPos x τ).PosDef` using `X.gramPos_posDef hx τ`. Establish `hAdef : ∀ a b, hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = X.gramPos x τ a b` using `fun a b => rfl`. Establish `hAinv : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hApd.isUnit)`. Establish `hquadP : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) (∑ a, c a • X.colP x τ a) = ∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b)` using `fun c => hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG c (X.colP x τ)`.

Establish `hnnP : ∀ c : Fin X.p0 → ℂ, 0 ≤ (∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b)).re`. Introduce `c`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules.

Conclude with `(ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hc).le`. Establish `hneg : ∀ w : Fin r → ℂ, (∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0) → w ≠ 0 → (hermC τ.1 X.Gm w w).re < 0`. Introduce `w hw0 hwne`. Assume the negation of the conclusion as `hcon`. Establish `hcon'` using `not_lt.mp hcon`.

Take `⟨P, -, hP⟩` from `X.signature τ`. Set `ip : Fin (r - X.p0) → Fin r` to `fun b => ⟨X.p0 + b.1, by have := b.2; omega⟩`. Set `pc : Fin (r - X.p0) → Fin r → ℂ` to `fun b => col P (ip b)`. Establish `hpc : ∀ b b', hermC τ.1 X.Gm (pc b) (pc b') = -(1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b'`. Introduce `b b'`.

Establish `h` using `congrFun (congrFun hP (ip b)) (ip b')`. Express the relevant statement in the definitionally equal form `hermC τ.1 X.Gm (pc b) (pc b') = _ at h`. Rewrite using `[h]`. Distinguish the cases in `hbb : b = b'`. Substitute `hbb` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Simplify using `[ip, sgn]`. Establish `hne : ip b ≠ ip b'`. Introduce `heq`. Conclude with `hbb (Fin.ext (by simpa [ip] using congrArg Fin.val heq))`.

Rewrite using `[Matrix.diagonal_apply_ne _ hne, Matrix.one_apply_ne hbb, neg_zero]`. Establish `hquadN : ∀ d : Fin (r - X.p0) → ℂ, hermC τ.1 X.Gm (∑ b, d b • pc b) (∑ b, d b • pc b) = -(∑ b, ∑ b', d b * (1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b' * conj (d b'))`. Introduce `d`. Rewrite using `[hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[hpc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwY : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm w (∑ a, c a • X.colP x τ a) = 0`.

Introduce `c`. Rewrite using `[hermC_finset_sum_right_of_conj_symm τ.1 hG]`. Simplify using `[hw0]`. Establish `hYw : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) w = 0`. Introduce `c`.

Rewrite using `[← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwY, map_zero]`. Set `f : Option (Fin X.p0) ⊕ Fin (r - X.p0) → Fin r → ℂ` to `Sum.elim (fun o => Option.elim o w (X.colP x τ)) pc`. Establish `hnli : ¬ LinearIndependent ℂ f`. Introduce `hli`. Establish `h` using `hli.fintype_card_le_finrank`.

Establish `hp` using `X.p0_le`. Apply the tactic sequence `simp at h <;> omega`. Take `⟨g, hg, i, hi⟩` from `Fintype.not_linearIndependent_iff.mp hnli`. Rewrite `hg` using `[Fintype.sum_sum_type, Fintype.sum_option]`. Simplify using `only [f, Sum.elim_inl, Sum.elim_inr, Option.elim_none, Option.elim_some] at hg`.

Establish `hu : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a = ∑ b, (-g (Sum.inr b)) • pc b`. Rewrite using `[eq_neg_of_add_eq_zero_left hg]`. Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Establish `hUU : 0 ≤ (hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a) (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)).re`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, hermC_smul_left_embedding, hermC_smul_right_of_conj_symm τ.1 hG, hwY, hYw, mul_zero, add_zero, zero_add]`.

Rewrite using `[Complex.add_re]`. Apply `add_nonneg` to reduce the goal to its premises. Establish `e : (conj (g (Sum.inl none)) * (g (Sum.inl none) * hermC τ.1 X.Gm w w)).re = Complex.normSq (g (Sum.inl none)) * (hermC τ.1 X.Gm w w).re`. Rewrite using `[← mul_assoc, mul_comm (conj (g (Sum.inl none))) (g (Sum.inl none)), Complex.mul_conj]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `mul_nonneg (Complex.normSq_nonneg _) hcon'`. Rewrite using `[hquadP]`. Conclude with `hnnP _`. Establish `hdz : (fun b => -g (Sum.inr b)) = 0`.

Assume the negation of the conclusion as `hd`. Establish `hpos` using `ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos Matrix.PosDef.one hd`. Use `beta_reduce at hpos`. Rewrite `hUU` using `[hu, hquadN, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgb : ∀ b, g (Sum.inr b) = 0` using `fun b => by simpa using congrFun hdz b`. Establish `hu0 : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a = 0`. Rewrite using `[hu]`. Simplify using `[hgb]`. Establish `hYY : hermC τ.1 X.Gm (∑ a, g (Sum.inl (some a)) • X.colP x τ a) (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0`.

Establish `h0 : hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a) (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0`. Rewrite using `[hu0]`. Conclude with `ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _`. Rewrite `h0` using `[ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, hermC_smul_left_embedding, hwY, mul_zero, zero_add]`. Conclude with `h0`.

Establish `hga : (fun a => g (Sum.inl (some a))) = 0`. Assume the negation of the conclusion as `hd`. Establish `hpos` using `ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hd`. Use `beta_reduce at hpos`. Rewrite `hYY` using `[hquadP]`.

Rewrite `hpos` using `[hYY]`. Simplify using `at hpos`. Establish `hgas : ∀ a, g (Sum.inl (some a)) = 0` using `fun a => by simpa using congrFun hga a`. Establish `hg0 : g (Sum.inl none) = 0`. Establish `h` using `hu0`.

Simplify using `only [hgas, zero_smul, Finset.sum_const_zero, add_zero] at h`. Conclude with `(smul_eq_zero.mp h).resolve_right hwne`. Take `(_ | a) | b` from `i`. Conclude with `hi hg0`. Conclude with `hi (hgas a)`.

Conclude with `hi (hgb b)`. Establish `horth : ∀ a, hermC τ.1 X.Gm (v - X.ppos x τ v) (X.colP x τ a) = 0`. Introduce `a`. Establish `hmul : ∀ b, ∑ c, (X.gramPos x τ)⁻¹ b c * X.gramPos x τ c a = if b = a then 1 else 0`. Introduce `b`.

Use `congrFun (congrFun hAinv b) a` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.FD.hermC_sub_left, X.ppos_eq, hermC_finset_sum_left']`. Simplify using `only [hAdef, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, hmul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`. Take `⟨w, hw⟩ : ∃ w, w = v - X.ppos x τ v` from `⟨_, rfl⟩`. Establish `horth' : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0`. Introduce `a`.

Rewrite using `[hw]`. Conclude with `horth a`. Establish `hwy : hermC τ.1 X.Gm w (X.ppos x τ v) = 0`. Rewrite using `[X.ppos_eq x τ v, hermC_finset_sum_right_of_conj_symm τ.1 hG]`. Simplify using `[horth']`.

Establish `hyw : hermC τ.1 X.Gm (X.ppos x τ v) w = 0`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwy, map_zero]`. Establish `hvdec : v = X.ppos x τ v + w`. Rewrite using `[hw]`. Normalize the expressions using the abelian group laws.

Establish `hHf` using `X.Hf_self hx τ v`. Rewrite `hHf` using `[X.Hf_eq_two_ppos]`. Take `⟨y, hy⟩ : ∃ y, y = X.ppos x τ v` from `⟨_, rfl⟩`. Establish `hyq : y = ∑ a, (∑ b, hermC τ.1 X.Gm v (X.colP x τ b) * (X.gramPos x τ)⁻¹ b a) • X.colP x τ a`. Rewrite using `[hy]`.

Conclude with `X.ppos_eq x τ v`. Establish `hyy_nn : 0 ≤ (hermC τ.1 X.Gm y y).re`. Rewrite using `[hyq, hquadP]`. Conclude with `hnnP _`. Establish `hyy_pos : y ≠ 0 → 0 < (hermC τ.1 X.Gm y y).re`.

Introduce `hy0`. Rewrite using `[hyq, hquadP]`. Apply `ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd` to reduce the goal to its premises. Introduce `hc`. Apply `hy0` to reduce the goal to its premises.

Rewrite using `[hyq]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun hc a`. Simplify using `only [Pi.zero_apply] at h`. Rewrite using `[h, zero_smul]`.

Rewrite `hHf`, `hyw`, `hwy`, `hvdec` using `[← hy]`. Rewrite `hHf`, `hv`, the goal using `[hvdec]`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, hyw, hwy, add_zero, zero_add] at hHf`. Establish `hmaj : X.maj x τ (y + w) = (hermC τ.1 X.Gm y y).re - (hermC τ.1 X.Gm w w).re`. Establish `h` using `congrArg Complex.re hHf`.

Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hmaj]`. Distinguish the cases in `hw0 : w = 0`. Establish `hy0 : y ≠ 0`.

Rewrite `hv` using `[hw0, add_zero]`. Conclude with `hv`. Establish `h2 : hermC τ.1 X.Gm w w = 0`. Rewrite using `[hw0]`. Conclude with `ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _`.

Rewrite using `[h2, Complex.zero_re, sub_zero]`. Conclude with `hyy_pos hy0`. Establish `h1` using `hneg w horth' hw0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma maj_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {v : Fin r → ℂ} (hv : v ≠ 0) :
    0 < X.maj x τ v := by
  classical
  have hG := X.Gm_herm
  have hApd : (X.gramPos x τ).PosDef := X.gramPos_posDef hx τ
  have hAdef : ∀ a b, hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = X.gramPos x τ a b :=
    fun a b => rfl
  have hAinv : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hApd.isUnit)

  have hquadP : ∀ c : Fin X.p0 → ℂ,
      hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) (∑ a, c a • X.colP x τ a) =
        ∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b) :=
    fun c => hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG c (X.colP x τ)
  have hnnP : ∀ c : Fin X.p0 → ℂ, 0 ≤ (∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b)).re := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp
    · exact (ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hc).le

  have hneg : ∀ w : Fin r → ℂ, (∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm w w).re < 0 := by
    intro w hw0 hwne
    by_contra hcon
    have hcon' := not_lt.mp hcon
    obtain ⟨P, -, hP⟩ := X.signature τ
    let ip : Fin (r - X.p0) → Fin r := fun b => ⟨X.p0 + b.1, by have := b.2; omega⟩
    let pc : Fin (r - X.p0) → Fin r → ℂ := fun b => col P (ip b)
    have hpc : ∀ b b', hermC τ.1 X.Gm (pc b) (pc b') =
        -(1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b' := by
      intro b b'
      have h := congrFun (congrFun hP (ip b)) (ip b')
      change hermC τ.1 X.Gm (pc b) (pc b') = _ at h
      rw [h]
      by_cases hbb : b = b'
      · subst hbb
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        simp [ip, sgn]
      · have hne : ip b ≠ ip b' := by
          intro heq
          exact hbb (Fin.ext (by simpa [ip] using congrArg Fin.val heq))
        rw [Matrix.diagonal_apply_ne _ hne, Matrix.one_apply_ne hbb, neg_zero]
    have hquadN : ∀ d : Fin (r - X.p0) → ℂ,
        hermC τ.1 X.Gm (∑ b, d b • pc b) (∑ b, d b • pc b) =
          -(∑ b, ∑ b', d b * (1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b' * conj (d b')) := by
      intro d
      rw [hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hpc]
      ring
    have hwY : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm w (∑ a, c a • X.colP x τ a) = 0 := by
      intro c
      rw [hermC_finset_sum_right_of_conj_symm τ.1 hG]
      simp [hw0]
    have hYw : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) w = 0 := by
      intro c
      rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwY, map_zero]

    let f : Option (Fin X.p0) ⊕ Fin (r - X.p0) → Fin r → ℂ :=
      Sum.elim (fun o => Option.elim o w (X.colP x τ)) pc
    have hnli : ¬ LinearIndependent ℂ f := by
      intro hli
      have h := hli.fintype_card_le_finrank
      have hp := X.p0_le
      simp at h <;> omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
    rw [Fintype.sum_sum_type, Fintype.sum_option] at hg
    simp only [f, Sum.elim_inl, Sum.elim_inr, Option.elim_none, Option.elim_some] at hg
    have hu : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a =
        ∑ b, (-g (Sum.inr b)) • pc b := by
      rw [eq_neg_of_add_eq_zero_left hg]
      simp only [neg_smul, Finset.sum_neg_distrib]
    have hUU : 0 ≤ (hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)
        (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)).re := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right,
        hermC_smul_left_embedding, hermC_smul_right_of_conj_symm τ.1 hG, hwY, hYw, mul_zero, add_zero, zero_add]
      rw [Complex.add_re]
      apply add_nonneg
      · have e : (conj (g (Sum.inl none)) * (g (Sum.inl none) * hermC τ.1 X.Gm w w)).re =
            Complex.normSq (g (Sum.inl none)) * (hermC τ.1 X.Gm w w).re := by
          rw [← mul_assoc, mul_comm (conj (g (Sum.inl none))) (g (Sum.inl none)), Complex.mul_conj]
          simp
        rw [e]
        exact mul_nonneg (Complex.normSq_nonneg _) hcon'
      · rw [hquadP]
        exact hnnP _
    have hdz : (fun b => -g (Sum.inr b)) = 0 := by
      by_contra hd
      have hpos := ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos Matrix.PosDef.one hd
      beta_reduce at hpos
      rw [hu, hquadN, Complex.neg_re] at hUU
      linarith
    have hgb : ∀ b, g (Sum.inr b) = 0 := fun b => by simpa using congrFun hdz b
    have hu0 : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a = 0 := by
      rw [hu]
      simp [hgb]
    have hYY : hermC τ.1 X.Gm (∑ a, g (Sum.inl (some a)) • X.colP x τ a)
        (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0 := by
      have h0 : hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)
          (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0 := by
        rw [hu0]
        exact ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _
      rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, hermC_smul_left_embedding, hwY, mul_zero, zero_add] at h0
      exact h0
    have hga : (fun a => g (Sum.inl (some a))) = 0 := by
      by_contra hd
      have hpos := ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hd
      beta_reduce at hpos
      rw [hquadP] at hYY
      rw [hYY] at hpos
      simp at hpos
    have hgas : ∀ a, g (Sum.inl (some a)) = 0 := fun a => by simpa using congrFun hga a
    have hg0 : g (Sum.inl none) = 0 := by
      have h := hu0
      simp only [hgas, zero_smul, Finset.sum_const_zero, add_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hwne
    obtain (_ | a) | b := i
    · exact hi hg0
    · exact hi (hgas a)
    · exact hi (hgb b)

  have horth : ∀ a, hermC τ.1 X.Gm (v - X.ppos x τ v) (X.colP x τ a) = 0 := by
    intro a
    have hmul : ∀ b, ∑ c, (X.gramPos x τ)⁻¹ b c * X.gramPos x τ c a = if b = a then 1 else 0 := by
      intro b
      have := congrFun (congrFun hAinv b) a
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_sub_left, X.ppos_eq, hermC_finset_sum_left']
    simp only [hAdef, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, hmul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]
  obtain ⟨w, hw⟩ : ∃ w, w = v - X.ppos x τ v := ⟨_, rfl⟩
  have horth' : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0 := by
    intro a
    rw [hw]
    exact horth a
  have hwy : hermC τ.1 X.Gm w (X.ppos x τ v) = 0 := by
    rw [X.ppos_eq x τ v, hermC_finset_sum_right_of_conj_symm τ.1 hG]
    simp [horth']
  have hyw : hermC τ.1 X.Gm (X.ppos x τ v) w = 0 := by
    rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwy, map_zero]
  have hvdec : v = X.ppos x τ v + w := by
    rw [hw]
    abel
  have hHf := X.Hf_self hx τ v
  rw [X.Hf_eq_two_ppos] at hHf
  obtain ⟨y, hy⟩ : ∃ y, y = X.ppos x τ v := ⟨_, rfl⟩
  have hyq : y = ∑ a, (∑ b, hermC τ.1 X.Gm v (X.colP x τ b) * (X.gramPos x τ)⁻¹ b a) •
      X.colP x τ a := by
    rw [hy]
    exact X.ppos_eq x τ v
  have hyy_nn : 0 ≤ (hermC τ.1 X.Gm y y).re := by
    rw [hyq, hquadP]
    exact hnnP _
  have hyy_pos : y ≠ 0 → 0 < (hermC τ.1 X.Gm y y).re := by
    intro hy0
    rw [hyq, hquadP]
    apply ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd
    intro hc
    apply hy0
    rw [hyq]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h := congrFun hc a
    simp only [Pi.zero_apply] at h
    rw [h, zero_smul]
  rw [← hy] at hHf hyw hwy hvdec
  rw [hvdec] at hHf hv ⊢
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, hyw, hwy,
    add_zero, zero_add] at hHf
  have hmaj : X.maj x τ (y + w) = (hermC τ.1 X.Gm y y).re - (hermC τ.1 X.Gm w w).re := by
    have h := congrArg Complex.re hHf
    simp at h
    linarith
  rw [hmaj]
  by_cases hw0 : w = 0
  · have hy0 : y ≠ 0 := by
      rw [hw0, add_zero] at hv
      exact hv
    have h2 : hermC τ.1 X.Gm w w = 0 := by
      rw [hw0]
      exact ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _
    rw [h2, Complex.zero_re, sub_zero]
    exact hyy_pos hy0
  · have h1 := hneg w horth' hw0
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.FD
