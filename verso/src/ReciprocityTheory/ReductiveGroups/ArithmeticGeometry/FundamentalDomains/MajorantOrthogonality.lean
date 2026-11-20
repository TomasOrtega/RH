import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def pform (X : Data E r) : ReciprocityTheory.MultiplicativeHeights.HermForm E r where
  c := (IsCMField.complexConj E).toAlgHom.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := X.Gmᵀ
  G_herm a b := X.Gm_herm b a

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ a, ∑ b, cc (x a) * X.Gm b a * y b = ∑ a, ∑ b, y a * X.Gm a b * cc (x b)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pform_h (X : Data E r) (x y : Fin r → E) : (pform X).h x y = herm X.Gm y x := by
  change ∑ a, ∑ b, cc (x a) * X.Gm b a * y b = ∑ a, ∑ b, y a * X.Gm a b * cc (x b)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use `⟨X.L'_fg, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← X.Λ_span, Submodule.span_le]`. Introduce `v hv`. Establish `h` using `X.NA_sub v hv`. Establish `hNA : (X.NA : E) ≠ 0` using `Nat.cast_ne_zero.mpr X.NA_pos.ne'`.

Establish `hv' : v = (X.NA : E)⁻¹ • ((X.NA : E) • v)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hNA, one_smul]`. Rewrite using `[hv']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h)`.
-/
lemma isLattice (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsLattice X.L' := by
  refine ⟨X.L'_fg, ?_⟩
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro v hv
  have h := X.NA_sub v hv
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have hv' : v = (X.NA : E)⁻¹ • ((X.NA : E) • v) := by
    rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [hv']
  exact Submodule.smul_mem _ _ (Submodule.subset_span h)

/- English proof (translation)
Establish `key : ∀ x y, (pform X.toData).h x y = cc (herm X.Gm x y)` using `fun x y => by`. Rewrite using `[pform_h, ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm X.Gm_herm]`. Establish `toI : ∀ z : E, IsIntegral ℤ z → ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z` using `fun z hz => ⟨⟨z, hz⟩, rfl⟩`. Establish `ofI : ∀ z : E, ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z → IsIntegral ℤ z`. Introduce and unpack `z ⟨o, rfl⟩`.

Conclude with `NumberField.RingOfIntegers.isIntegral_coe o`. Establish `ccI : ∀ z : E, IsIntegral ℤ z → IsIntegral ℤ (cc z)` using `fun z hz => hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom`. Use `⟨fun x hx y hy => ?_, fun x hx => X.L'_dual x fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `toI _ (ccI _ (X.L'_int x hx y hy))`.

Establish `h1` using `hx y hy`. Rewrite `h1` using `[key]`. Establish `h2` using `ccI _ (ofI _ h1)`. Simplify `h2` using `[cc, IsCMField.complexConj_apply_apply]`.
-/
lemma selfDual (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsSelfDual (pform X.toData) X.L' := by
  have key : ∀ x y, (pform X.toData).h x y = cc (herm X.Gm x y) := fun x y => by
    rw [pform_h, ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm X.Gm_herm]
  have toI : ∀ z : E, IsIntegral ℤ z → ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have ofI : ∀ z : E, ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z → IsIntegral ℤ z := by
    rintro z ⟨o, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe o
  have ccI : ∀ z : E, IsIntegral ℤ z → IsIntegral ℤ (cc z) := fun z hz =>
    hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  refine ⟨fun x hx y hy => ?_, fun x hx => X.L'_dual x fun y hy => ?_⟩
  · rw [key]
    exact toI _ (ccI _ (X.L'_int x hx y hy))
  · have h1 := hx y hy
    rw [key] at h1
    have h2 := ccI _ (ofI _ h1)
    simpa [cc, IsCMField.complexConj_apply_apply] using h2

/- English proof (translation)
Establish `h2 : M *ᵥ (M⁻¹ *ᵥ w) = w`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]`. Use `conv_rhs => rw [← h2]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]`.
-/
private lemma sum_inv_mulVec_smul_col_of_det_ne_zero (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (w : Fin r → ℂ) :
    ∑ k, (M⁻¹ *ᵥ w) k • col M k = w := by
  have h2 : M *ᵥ (M⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  conv_rhs => rw [← h2]
  funext i
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply (X := X) ho τ k l]`. Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Distinguish the cases in `hk : (k : ℕ) < X.p0`. Simplify using `[hk, sgn]`.

Simplify using `[hk, sgn]`. Simplify using `[hkl]`.
-/
private lemma hermC_col_mat_of_isOrtho (X : Data E r) {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (k l : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) k) (col (mat x τ) l) =
      if k = l then (if (k : ℕ) < X.p0 then (1 : ℂ) else -1) else 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply (X := X) ho τ k l]
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : (k : ℕ) < X.p0
    · simp [hk, sgn]
    · simp [hk, sgn]
  · simp [hkl]

/- English proof (translation)
Establish `hdet : (mat x τ).det ≠ 0` using `((Data.mem_dom_iff X x).mp hx τ).1`. Establish `hf` using `hermC_col_mat_of_isOrtho X ho τ`. Use `set c := (mat x τ)⁻¹ *ᵥ v with hc`. Establish `hv : v = ∑ k, c k • col (mat x τ) k` using `(sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet v).symm`. Establish `hcol : ∀ a, col (mat x τ) a = ∑ l, (Pi.single a 1 : Fin r → ℂ) l • col (mat x τ) l`.

Introduce `a`. Simplify using `[Pi.single_apply]`. Establish `hpair : ∀ a : Fin r, hermC τ.1 X.Gm v (col (mat x τ) a) = ReciprocityTheory.MultiplicativeHeights.sgn X.p0 a * c a`. Introduce `a`. Rewrite using `[hv, hcol a, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]`.

Simplify using `[ReciprocityTheory.MultiplicativeHeights.jForm, Pi.single_apply, apply_ite]`. Establish `hgp : X.gramPos x τ = 1`. Unfold `Data.gramPos`. Rewrite using `[ho τ]`. Use extensionality with `a b`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[Matrix.diagonal_apply, sgn, a.isLt]`. Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, hab, Fin.castLE_inj]`. Establish `hpos : X.posPart x τ v = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2`.

Unfold `Data.posPart`. Rewrite using `[hgp, inv_one]`. Simplify using `only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hpair]`.

Simplify using `[ReciprocityTheory.MultiplicativeHeights.sgn]`. Establish `hself : (hermC τ.1 X.Gm v v).re = ∑ k : Fin r, (if (k : ℕ) < X.p0 then (1 : ℝ) else -1) * ‖c k‖ ^ 2`. Rewrite using `[hv, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]`. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.jForm, Complex.re_sum, ReciprocityTheory.MultiplicativeHeights.sgn]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.conj_mul']`. Establish `hre : (((‖c k‖ : ℝ) : ℂ) ^ 2).re = ‖c k‖ ^ 2`. Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re]`. Apply the tactic sequence `split_ifs <;> simp [hre]`. Unfold `Data.maj`.

Rewrite using `[hpos, hself]`. Unfold `ReciprocityTheory.MultiplicativeHeights.normSq`. Establish `hsplit : ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 = ∑ k : Fin r, if (k : ℕ) < X.p0 then ‖c k‖ ^ 2 else 0` using `Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _ (fun k hk => by`. Rewrite using `[if_neg]`. Introduce `hlt`.

Conclude with `hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩)`. Use the proof step `(fun a => by simp [a.isLt])`. Rewrite using `[hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
lemma maj_ortho (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (v : Fin r → ℂ) : X.maj x τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x τ)⁻¹ *ᵥ v) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  set c := (mat x τ)⁻¹ *ᵥ v with hc
  have hv : v = ∑ k, c k • col (mat x τ) k := (sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet v).symm
  have hcol : ∀ a, col (mat x τ) a = ∑ l, (Pi.single a 1 : Fin r → ℂ) l • col (mat x τ) l := by
    intro a
    simp [Pi.single_apply]
  have hpair : ∀ a : Fin r, hermC τ.1 X.Gm v (col (mat x τ) a) = ReciprocityTheory.MultiplicativeHeights.sgn X.p0 a * c a := by
    intro a
    rw [hv, hcol a, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.single_apply, apply_ite]
  have hgp : X.gramPos x τ = 1 := by
    unfold Data.gramPos
    rw [ho τ]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, sgn, a.isLt]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab, Fin.castLE_inj]
  have hpos : X.posPart x τ v = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 := by
    unfold Data.posPart
    rw [hgp, inv_one]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hpair]
    simp [ReciprocityTheory.MultiplicativeHeights.sgn]
  have hself : (hermC τ.1 X.Gm v v).re = ∑ k : Fin r, (if (k : ℕ) < X.p0 then (1 : ℝ) else -1) * ‖c k‖ ^ 2 := by
    rw [hv, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Complex.re_sum, ReciprocityTheory.MultiplicativeHeights.sgn]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
    have hre : (((‖c k‖ : ℝ) : ℂ) ^ 2).re = ‖c k‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    split_ifs <;> simp [hre]
  unfold Data.maj
  rw [hpos, hself]
  unfold ReciprocityTheory.MultiplicativeHeights.normSq
  have hsplit : ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then ‖c k‖ ^ 2 else 0 :=
    Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _
      (fun k hk => by
        rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩)
      (fun a => by simp [a.isLt])
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Establish `hdet : (mat x τ).det ≠ 0` using `((Data.mem_dom_iff X x).mp hx τ).1`. Establish `hf` using `hermC_col_mat_of_isOrtho X ho τ`. Establish `h1 : τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v)`. Simplify using `only [herm, hermC, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet, sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet]`. Use `_ = _ := ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf _ _`.
-/
lemma herm_coord (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → E) : τ.1 (herm X.Gm u v) = ReciprocityTheory.MultiplicativeHeights.jForm X.p0
      ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  have h1 : τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := by
    simp only [herm, hermC, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
  calc τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := h1
    _ = hermC τ.1 X.Gm (∑ k, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) k • col (mat x τ) k)
          (∑ l, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) l • col (mat x τ) l) := by
        rw [sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet, sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet]
    _ = _ := ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf _ _

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
