import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqProdDiagOfHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongKodairaSpencerDeformationLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLiftStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlagTan

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {K : Type} [Field K]

def movedVert (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (k : VIx Dw) : FIx Dw → K :=
  fun x => x.elim ((Pi.single k.toF (1 : K) : FIx Dw → K) none) fun q =>
    (g' q.1 * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2

/- English proof (translation)
Establish `eM : ∀ k j : HIx Dw Φ, ksChg Φ g (Pi.single k 1) j ≠ 0 → k = j ∨ ((j.2.1 : ℤ) + j.2.2 < (k.2.1 : ℤ) + k.2.2)`. Introduce and unpack `k ⟨τ, a, b⟩ hne`. Rewrite `hne` using `[ksChg_apply]`. Take `⟨a', -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Take `⟨b', -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`.

Choose the witnesses or unpack the hypotheses as in `rfl : ⟨τ, a', b'⟩ = k := by`. Assume the negation of the conclusion as `hk`. Simplify using `[Pi.single_eq_of_ne hk] at hne`. Establish `h1 : ¬ a' < a` using `fun k => by simp [hg _ _ _ k] at hne`. Establish `h2 : ¬ b' < b` using `fun k => by simp [hg _ _ _ k] at hne`.

Distinguish the cases in `h3 : a' = a ∧ b' = b`. Use `left`. Rewrite using `[h3.1, h3.2]`. Use `right`. Simplify using `only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `dM : ∀ k : HIx Dw Φ, ksChg Φ g (Pi.single k 1) k = ((t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩) : Kˣ) : K)`. Introduce and unpack `⟨τ, a, b⟩`. Simplify using `[ksChg_apply, Pi.single_apply, hd, ite_and]`. Establish `fN : ∀ (k : VIx Dw) (σ : E →+* ℂ) (i j : Fin (Dw.mult σ)), (g' σ * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, i, j⟩)) * g σ) i j = ∑ a, ∑ b, g' σ i a * (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, a, b⟩) * g σ b j` using `fun k σ i j => by`.

Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Rewrite using `[det_eq_prod_diag_of_height _ (fun k => (k.2.1 : ℤ) + k.2.2) eM, det_eq_prod_diag_of_height (m := VIx Dw) _ (fun k => (k.2.1.2 : ℤ) - k.2.1.1)]`. Rewrite using `[exOf_kap, ← prod_char_eq hΦ, Units.val_mul, Units.coe_prod, Units.coe_prod]`. Use `congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => dM k) (Finset.prod_congr rfl fun ⟨σ, ⟨i, j⟩, hij⟩ _ => (fN _ σ i j).trans ?_)` and prove the remaining obligations.

Simplify using `[VIx.toF, Pi.single_apply, hd, hd', ite_and]`. Introduce and unpack `⟨σ', ⟨i', j'⟩, hij'⟩ ⟨σ, ⟨i, j⟩, hij⟩ hne`. Establish `hne` using `fun e => hne ((fN _ σ i j).trans e)`. Take `⟨a, -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Take `⟨b, -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`.

Establish `e : (some ⟨σ, a, b⟩ : FIx Dw) = some ⟨σ', i', j'⟩`. Assume the negation of the conclusion as `hk`. Conclude with `hne (by rw [VIx.toF, Pi.single_eq_of_ne hk, mul_zero, zero_mul])`. Take `⟨rfl, e⟩` from `Sigma.mk.inj_iff.1 (Option.some.inj e)`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj (eq_of_heq e)`.

Establish `h1 : ¬ i < a` using `fun k => by simp [hg' _ _ _ k] at hne`. Establish `h2 : ¬ b < j` using `fun k => by simp [hg _ _ _ k] at hne`. Distinguish the cases in `h3 : a = i ∧ b = j`. Use `left`. Take `⟨rfl, rfl⟩` from `h3`.

Both sides reduce to the same expression. Use `right`. Simplify using `only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_moved {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ}
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    (hg : ∀ τ i j, i < j → g τ i j = 0) (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : K))
    (hg' : ∀ τ i j, i < j → g' τ i j = 0) (hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ)) :
    (Matrix.of fun k => ksChg Φ g (Pi.single k 1)).det *
      (Matrix.of fun k j : VIx Dw => movedVert g g' k j.toF).det =
      ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  have eM : ∀ k j : HIx Dw Φ, ksChg Φ g (Pi.single k 1) j ≠ 0 →
      k = j ∨ ((j.2.1 : ℤ) + j.2.2 < (k.2.1 : ℤ) + k.2.2) := by
    rintro k ⟨τ, a, b⟩ hne
    rw [ksChg_apply] at hne
    obtain ⟨a', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain rfl : ⟨τ, a', b'⟩ = k := by
      by_contra hk
      simp [Pi.single_eq_of_ne hk] at hne
    have h1 : ¬ a' < a := fun k => by simp [hg _ _ _ k] at hne
    have h2 : ¬ b' < b := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a' = a ∧ b' = b
    · left; rw [h3.1, h3.2]
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega
  have dM : ∀ k : HIx Dw Φ, ksChg Φ g (Pi.single k 1) k =
      ((t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩) : Kˣ) : K) := by
    rintro ⟨τ, a, b⟩
    simp [ksChg_apply, Pi.single_apply, hd, ite_and]
  have fN : ∀ (k : VIx Dw) (σ : E →+* ℂ) (i j : Fin (Dw.mult σ)),
      (g' σ * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, i, j⟩)) * g σ) i j =
      ∑ a, ∑ b, g' σ i a * (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, a, b⟩) * g σ b j := fun k σ i j => by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [det_eq_prod_diag_of_height _ (fun k => (k.2.1 : ℤ) + k.2.2) eM,
    det_eq_prod_diag_of_height (m := VIx Dw) _ (fun k => (k.2.1.2 : ℤ) - k.2.1.1)]
  · rw [exOf_kap, ← prod_char_eq hΦ, Units.val_mul, Units.coe_prod, Units.coe_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => dM k)
      (Finset.prod_congr rfl fun ⟨σ, ⟨i, j⟩, hij⟩ _ => (fN _ σ i j).trans ?_)
    simp [VIx.toF, Pi.single_apply, hd, hd', ite_and]
  · rintro ⟨σ', ⟨i', j'⟩, hij'⟩ ⟨σ, ⟨i, j⟩, hij⟩ hne
    have hne := fun e => hne ((fN _ σ i j).trans e)
    obtain ⟨a, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have e : (some ⟨σ, a, b⟩ : FIx Dw) = some ⟨σ', i', j'⟩ := by
      by_contra hk
      exact hne (by rw [VIx.toF, Pi.single_eq_of_ne hk, mul_zero, zero_mul])
    obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e)
    have h1 : ¬ i < a := fun k => by simp [hg' _ _ _ k] at hne
    have h2 : ¬ b < j := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a = i ∧ b = j
    · left; obtain ⟨rfl, rfl⟩ := h3; rfl
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F K]

/- English proof (translation)
Take `⟨g, hg, hd, hc⟩` from `(frBor_iff_frChg _ _ _).1 h`. Take `⟨g', a', -, e1, e2⟩` from `exists_frChg_inv hc`. Establish `hg' : ∀ τ i j, i < j → g' τ i j = 0` using `fun τ i j hij => by`. Set `_ : Invertible (g τ)` to `⟨g' τ, e1 τ, e2 τ⟩`. Use `Matrix.blockTriangular_inv_of_blockTriangular (M := g τ) (b := OrderDual.toDual) (fun i j hij => hg τ i j hij)` as an intermediate fact.

Rewrite `this` using `[Matrix.inv_eq_left_inv (e1 τ)]`. Conclude with `this hij`. Establish `hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ)` using `fun τ i => by`. Use `congrFun (congrFun (e1 τ) i) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single i, hd, Matrix.one_apply_eq]`.

Conclude with `(Units.mul_eq_one_iff_eq_inv).1 this`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with k | k` into its components or cases. Rewrite using `[hg τ j i k, mul_zero]`. Rewrite using `[hg' τ i j k, zero_mul]`.

Simplify using the standard rewrite rules. Use `choose w hw hw' using fun k => exists_move hc (hv'.isDef k)`. Use `⟨w, fun k => ksChg Φ g (Pi.single k 1), movedVert g g', fun k => ⟨fun i => Units.map (cst c K).toRingHom.toMonoidHom (t i), (frBor_iff_frChg _ _ _).2 ⟨_, fun τ i j hij => by simp [hg τ i j hij], fun τ i => by simp [hd], hw' k⟩⟩, fun k => ⟨hw _, by rw [← (hw' _).1]; exact (hv'.1 k …` and prove the remaining obligations.
-/
theorem exists_moved_defs {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ} {y y' : FrPt Xo c K}
    (h : FrBor t y y') {v' : TIx Dw Φ → FrPt Xo c (DualNumber K)} (hv' : IsTanFrame Φ y' v') :
    ∃ (w : TIx Dw Φ → FrPt Xo c (DualNumber K)) (M : HIx Dw Φ → HIx Dw Φ → K) (N : VIx Dw → FIx Dw → K),
      (∀ k, ∃ t' : Ix Dw → (DualNumber K)ˣ, FrBor t' (w k) (v' k)) ∧
      (∀ k, IsDef y (w (.inl k)) ∧ IsKS Φ y (w (.inl k)).x (M k)) ∧ (∀ k, IsVert y (N k) (w (.inr k))) ∧
      (Matrix.of M).det * (Matrix.of fun k j : VIx Dw => N k j.toF).det =
        ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  obtain ⟨g, hg, hd, hc⟩ := (frBor_iff_frChg _ _ _).1 h
  obtain ⟨g', a', -, e1, e2⟩ := exists_frChg_inv hc
  have hg' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ i j hij => by
    let _ : Invertible (g τ) := ⟨g' τ, e1 τ, e2 τ⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular (M := g τ) (b := OrderDual.toDual)
      (fun i j hij => hg τ i j hij)
    rw [Matrix.inv_eq_left_inv (e1 τ)] at this
    exact this hij
  have hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ) := fun τ i => by
    have := congrFun (congrFun (e1 τ) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, Matrix.one_apply_eq] at this
    · exact (Units.mul_eq_one_iff_eq_inv).1 this
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with k | k
      · rw [hg τ j i k, mul_zero]
      · rw [hg' τ i j k, zero_mul]
    · simp
  choose w hw hw' using fun k => exists_move hc (hv'.isDef k)
  refine ⟨w, fun k => ksChg Φ g (Pi.single k 1), movedVert g g', fun k =>
    ⟨fun i => Units.map (cst c K).toRingHom.toMonoidHom (t i),
      (frBor_iff_frChg _ _ _).2 ⟨_, fun τ i j hij => by simp [hg τ i j hij], fun τ i => by simp [hd], hw' k⟩⟩,
    fun k => ⟨hw _, by rw [← (hw' _).1]; exact (hv'.1 k).2.of_frChg hc⟩,
    fun k => isVert_move hc e2 (hv'.2 k) (hw' (.inr k)), det_moved hΦ hg hd hg' hd'⟩

end GlobalTheory.FlagTan

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho P Q t hz ht v v' hv hv' zv zv' hl hl' O g hzv hzv'`. Take `⟨w, Mx, N, hb, hM, hN, hdet⟩` from `GlobalTheory.FlagTan.exists_moved_defs (GlobalTheory.FlagTan.isHalf_psiSet H) ht hv`. Establish `hlw : ∀ k, zv k ≫ toFlag M = X.ptY (w k)` using `fun k => by`. Take `⟨_, h⟩` from `hb k`. Rewrite using `[hl, X.ptY_frBor h]`.

Use `choose C hC using fun k => GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho (hKS K Q) hz hv' hl' (hM k).1 (hM k).2 (hlw (.inl k))`. Establish `hV` using `fun k => GlobalTheory.T.derivative_along_vertical_deformation_lift M z ho hz (v := fun j => v' (.inr j)) (fun j => hv'.2 j) (zv := fun j => zv' (.inr j)) (fun j => hl' _) (hN k) (hlw (.inr k))`. Set `T : Matrix (TIx Dw (psiSet H)) (TIx Dw (psiSet H)) K` to `Matrix.fromBlocks (Matrix.of Mx) (Matrix.of C) 0 (Matrix.of fun k j : VIx Dw => N k j.toF)`. Establish `hT : ∀ a b, (evalPt (zv b) O (hzv b) (g a)).snd = ∑ c', T b c' * (evalPt (zv' c') O (hzv' c') (g a)).snd`. Introduce `a b`.

Break down `b with k | k` into its components or cases. Rewrite using `[hC k O (g a) (hzv _) hzv', Fintype.sum_sum_type]`. Simplify using `[T]`. Rewrite using `[hV k O (g a) (hzv _) (fun j => hzv' _), Fintype.sum_sum_type]`. Simplify using `[T]`.

Establish `hA : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) = (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd) * (T.submatrix (tanOrd Dw) (tanOrd Dw)).transpose`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hT]`. Rewrite using `[← (tanOrd Dw).sum_comp]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.

Rewrite using `[hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, hdet, mul_comm]`.
-/
theorem det_der_frBor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho P Q t hz ht v v' hv hv' zv zv' hl hl' O g hzv hzv'
  obtain ⟨w, Mx, N, hb, hM, hN, hdet⟩ := GlobalTheory.FlagTan.exists_moved_defs (GlobalTheory.FlagTan.isHalf_psiSet H) ht hv
  have hlw : ∀ k, zv k ≫ toFlag M = X.ptY (w k) := fun k => by
    obtain ⟨_, h⟩ := hb k
    rw [hl, X.ptY_frBor h]
  choose C hC using fun k => GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho (hKS K Q) hz hv' hl' (hM k).1 (hM k).2 (hlw (.inl k))
  have hV := fun k => GlobalTheory.T.derivative_along_vertical_deformation_lift M z ho hz (v := fun j => v' (.inr j)) (fun j => hv'.2 j)
    (zv := fun j => zv' (.inr j)) (fun j => hl' _) (hN k) (hlw (.inr k))
  let T : Matrix (TIx Dw (psiSet H)) (TIx Dw (psiSet H)) K :=
    Matrix.fromBlocks (Matrix.of Mx) (Matrix.of C) 0 (Matrix.of fun k j : VIx Dw => N k j.toF)
  have hT : ∀ a b, (evalPt (zv b) O (hzv b) (g a)).snd =
      ∑ c', T b c' * (evalPt (zv' c') O (hzv' c') (g a)).snd := by
    intro a b
    rcases b with k | k
    · rw [hC k O (g a) (hzv _) hzv', Fintype.sum_sum_type]
      simp [T]
    · rw [hV k O (g a) (hzv _) (fun j => hzv' _), Fintype.sum_sum_type]
      simp [T]
  have hA : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd) *
        (T.submatrix (tanOrd Dw) (tanOrd Dw)).transpose := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hT]
    rw [← (tanOrd Dw).sum_comp]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, hdet,
    mul_comm]

end GlobalTheory.CompHS
