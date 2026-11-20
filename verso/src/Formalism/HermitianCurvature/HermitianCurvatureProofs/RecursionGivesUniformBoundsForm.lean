import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

/- English proof (translation)
Unfold `TB.PSDOn at *`. Conclude with `hk.hadamard hk'`.
-/
theorem psd_mul {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'

/- English proof (translation)
Unfold `TB.PSDOn at *`. Establish `e : (Matrix.of fun x y : G => k' x y) = (Matrix.of fun x y : F => k x y).submatrix f f`. Use extensionality with `x y`. Conclude with `h x y`. Rewrite using `[e]`.

Conclude with `hk.submatrix f`.
-/
theorem psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : G => k' x y) = (Matrix.of fun x y : F => k x y).submatrix f f := by
    ext x y; exact h x y
  rw [e]; exact hk.submatrix f

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`. Rewrite using `[← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y _`. Simplify using `only [RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadM {α : Type} (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro y _
  simp only [RCLike.star_def]; ring

/- English proof (translation)
Unfold `TB.PSDOn at hk`. Rewrite `hk` using `[Matrix.posSemidef_iff_dotProduct_mulVec]`. Establish `h` using `hk.2 (fun x : F => (fun _ : α => (1 : ℂ)) x)`. Rewrite `h` using `[quadM F k (fun _ => 1)]`. Establish `h2` using `(Complex.le_def.1 h).1`.

Simplify using `using h2`.
-/
theorem sum_nonneg_of_psd {α : Type} {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) :
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y).re := by
  unfold TB.PSDOn at hk
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hk
  have h := hk.2 (fun x : F => (fun _ : α => (1 : ℂ)) x)
  rw [quadM F k (fun _ => 1)] at h
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

/- English proof (translation)
The claim follows from `sum_nonneg_of_psd (psd_mul hk hk')`.
-/
theorem sum_mul_nonneg {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : 0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y * k' x y).re :=
  sum_nonneg_of_psd (psd_mul hk hk')

/- English proof (translation)
Unfold `TB.Data.maj`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`. Conclude with `le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)`. Introduce `v _`.

Conclude with `min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg (h v).1 (hav v)) (div_le_div_of_nonneg_right (h v).2 (hav v)) _)`.
-/
theorem maj_mono {E W : Type} [Field E] (D : TB.Data E W) (ρ ρ' : Fin D.f → ℝ) (l : E)
    (h : ∀ v, 0 ≤ ρ v ∧ ρ v ≤ ρ' v) (hav : ∀ v, 0 ≤ D.av v l) : D.maj ρ l ≤ D.maj ρ' l := by
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    exact min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg (h v).1 (hav v))
      (div_le_div_of_nonneg_right (h v).2 (hav v)) _)

/- English proof (translation)
Unfold `TB.Data.N0`. Conclude with `div_nonneg (sum_mul_nonneg hκ (hG ε hε k w Y)) (hW w).le`.
-/
theorem baseGram_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ := by
  unfold TB.Data.N0
  exact div_nonneg (sum_mul_nonneg hκ (hG ε hε k w Y)) (hW w).le

/- English proof (translation)
Unfold `TB.Data.Nst`. Rewrite using `[Complex.div_ofReal_re]`. Use `div_nonneg (sum_mul_nonneg hκ ?_) (hW w).le` and prove the remaining obligations. Establish `hm : ∀ x ∈ Y, TB.join x s t ∈ Y.image (fun h => TB.join h s t)` using `fun x hx => Finset.mem_image_of_mem _ hx`. Conclude with `psd_pull (F := Y.image (fun h => TB.join h s t)) (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) (hG ε hε i w _)`.
-/
theorem Nst_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) (t : E) : 0 ≤ (D.Nst ε i s w Y κ t t).re := by
  classical
  unfold TB.Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg (sum_mul_nonneg hκ ?_) (hW w).le
  have hm : ∀ x ∈ Y, TB.join x s t ∈ Y.image (fun h => TB.join h s t) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  exact psd_pull (F := Y.image (fun h => TB.join h s t))
    (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) (hG ε hε i w _)

/- English proof (translation)
Establish `hm : ∀ x ∈ Y, TB.join x s t ∈ TB.pts Y s S`. Introduce `x hx`. Unfold `TB.pts`. Conclude with `Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩`. Conclude with `psd_pull (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) hκ`.
-/
theorem blk_psd {E : Type} [Field E] {Y : Finset (TB.Pt E)} {S : Finset E} {s : ℕ}
    {κ : TB.Pt E → TB.Pt E → ℂ} (hκ : TB.PSDOn (TB.pts Y s S) κ) {t : E} (ht : t ∈ S) :
    TB.PSDOn Y (TB.blk κ s t t) := by
  classical
  have hm : ∀ x ∈ Y, TB.join x s t ∈ TB.pts Y s S := by
    intro x hx
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩
  exact psd_pull (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) hκ

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

/- English proof (translation)
Introduce `E W _ D szD' szL' vol' C₄ hC4 hav hD hL hV hG hW`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h ε hε i hi1 hi2 w hw hcnt`. Take `⟨θ, hθ, H⟩` from `h ε hε i hi1 hi2 w hw hcnt`. Use `⟨θ, hθ, ?_⟩` and prove the remaining obligations.

Introduce `Y hY κ hκ`. Take `⟨e0, el⟩` from `H Y hY κ hκ`. Use `⟨e0, fun l hl hl0 => ?_⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `el l hl hl0`. Use `⟨A, le_trans hA ?_⟩` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (maj_mono D (D.szD i) (szD' i) l (fun v => hD i v) (fun v => hav v l)) (Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ A).1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))`. Introduce `h ε hε i s hs hsi hi hns w hw hcnt`. Take `⟨θ, hθ, H⟩` from `h ε hε i s hs hsi hi hns w hw hcnt`. Use `⟨θ, hθ, ?_⟩` and prove the remaining obligations. Introduce `Y S κ hY hκ t ht t' ht' h0 h0' hne`.

Take `⟨π, hπ⟩` from `H Y S κ hY hκ t ht t' ht' h0 h0' hne`. Use `⟨π, le_trans hπ ?_⟩` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (maj_mono D (D.szL (i - s + 1) s) (szL' (i - s + 1) s) _ (fun v => hL _ _ v) (fun v => hav v _)) (Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) (div_nonneg (add_nonneg (Nst_nonneg D hG hW hε i s x.1 Y (blk_psd hκ ht) t) (Nst_nonneg D hG hW hε i s …`. Introduce `h ε hε i s hs hsi hi w hw hcnt hvol`. Take `⟨θ, hθ, H⟩` from `h ε hε i s hs hsi hi w hw hcnt (le_trans (hV _ _).2 hvol)`.

Use `⟨θ, hθ, ?_⟩` and prove the remaining obligations. Introduce `Y hY κ hκ t₀ S hS`. Use `le_trans (H Y hY κ hκ t₀ S hS) ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun s' _ => (hV _ s').1) (fun s' _ => (hV _ s').2)) (pow_nonneg hC4 _)) (Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))`.
-/
theorem estimates_mono : Formalism.FourierDecayAlt.J.EstimatesMono := by
  intro E W _ D szD' szL' vol' C₄ hC4 hav hD hL hV hG hW
  refine ⟨?_, ?_, ?_⟩
  · intro h ε hε i hi1 hi2 w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i hi1 hi2 w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ
    obtain ⟨e0, el⟩ := H Y hY κ hκ
    refine ⟨e0, fun l hl hl0 => ?_⟩
    obtain ⟨A, hA⟩ := el l hl hl0
    refine ⟨A, le_trans hA ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szD i) (szD' i) l (fun v => hD i v) (fun v => hav v l))
      (Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ A).1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))
  · intro h ε hε i s hs hsi hi hns w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi hns w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y S κ hY hκ t ht t' ht' h0 h0' hne
    obtain ⟨π, hπ⟩ := H Y S κ hY hκ t ht t' ht' h0 h0' hne
    refine ⟨π, le_trans hπ ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szL (i - s + 1) s) (szL' (i - s + 1) s) _ (fun v => hL _ _ v)
        (fun v => hav v _))
      (Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) (div_nonneg (add_nonneg
        (Nst_nonneg D hG hW hε i s x.1 Y (blk_psd hκ ht) t)
        (Nst_nonneg D hG hW hε i s x.2 Y (blk_psd hκ ht') t')) (by norm_num)))
  · intro h ε hε i s hs hsi hi w hw hcnt hvol
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi w hw hcnt (le_trans (hV _ _).2 hvol)
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t₀ S hS
    refine le_trans (H Y hY κ hκ t₀ S hS) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun s' _ => (hV _ s').1) (fun s' _ => (hV _ s').2)) (pow_nonneg hC4 _))
      (Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))

/- English proof (translation)
Introduce `r e sd h0 h1`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), h1, Finset.prod_eq_one, one_mul]`. Introduce `i hi`. Rewrite using `[h0 i hi, add_zero]`.
-/
theorem product_of_energies : Formalism.FourierDecayAlt.J.ProductOfE := by
  intro r e sd h0 h1
  rw [Finset.prod_Icc_succ_top (by omega), h1, Finset.prod_eq_one, one_mul]
  intro i hi; rw [h0 i hi, add_zero]

/- English proof (translation)
Introduce `hA C₁ C₄ h1 h4`. Take `⟨C, C', h⟩` from `hA C₁ C₄ h1 h4`. Use `⟨C, C', ?_⟩` and prove the remaining obligations. Introduce `E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B hI hδ hS`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩` from `hyp`.

Unfold `S3.MassData.InTheoremA`. Apply `hS` to reduce the goal to its premises. Introduce `R`. Use `h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R` as an intermediate fact. Rewrite `this` using `[Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one]`.

Rewrite using `[hδ, hI]`. Conclude with `this`.
-/
theorem recursion_gives_explicit_form : Formalism.FourierDecayAlt.J.RecursionGivesBounds := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  unfold S3.MassData.InTheoremA
  apply hS
  intro R
  have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
  rw [Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one] at this
  rw [hδ, hI]; exact this

/- English proof (translation)
Introduce `hA C₁ C₄ h1 h4`. Take `⟨C, C', h⟩` from `hA C₁ C₄ h1 h4`. Use `⟨C, C', ?_⟩` and prove the remaining obligations. Introduce `E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B he1 hI hδ hS`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩` from `hyp`.

Establish `hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1`. Rewrite using `[Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1), Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]`. Establish `key` using `hS ((1 + B.δ) * B.e1 * B.IntN) (fun R => by`. Use `h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R` as an intermediate fact. Rewrite `this` using `[hprod]`.

Rewrite using `[hδ, hI]`. Conclude with `this)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem recursion_gives_form : Formalism.FourierDecayAlt.J.RecursionGivesForm := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B he1 hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1 := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1),
      Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]
  have key := hS ((1 + B.δ) * B.e1 * B.IntN) (fun R => by
    have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
    rw [hprod] at this
    rw [hδ, hI]; exact this)
  calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := key
    _ = _ := by ring

/- English proof (translation)
Introduce `sd e h hs`. Establish `h1 : (1 : ℝ) ≤ max sd 1` using `le_max_right _ _`. Establish `h2 : sd ≤ max sd 1` using `le_max_left _ _`. Establish `h3 : max sd 1 ≤ 2` using `max_le hs (by norm_num)`. Use `⟨by linarith, by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem top_energy : Formalism.FourierDecayAlt.J.TopE := by
  intro sd e h hs
  have h1 : (1 : ℝ) ≤ max sd 1 := le_max_right _ _
  have h2 : sd ≤ max sd 1 := le_max_left _ _
  have h3 : max sd 1 ≤ 2 := max_le hs (by norm_num)
  refine ⟨by linarith, by linarith, by linarith⟩

/- English proof (translation)
Introduce `P _ B hpos hk hA`. Unfold `S3.MassData.InTheoremA S3.MassData.Smod at hA`. Take `⟨hk1, hk2⟩` from `hk`. Establish `hp` using `hpos.2`. Establish `hvN : 0 < B.volN` using `by tauto`.

Establish `hvH : 0 < B.volH` using `by tauto`. Establish `hvN' : 0 < B.volN'` using `by tauto`. Establish `hvH' : 0 < B.volH'` using `by tauto`. Establish `hd : 0 < B.dimπ` using `by tauto`. Establish `hd' : 0 < B.dimπ'` using `by tauto`.

Establish `hn : 0 < B.n0c` using `by tauto`. Establish `hs : 0 ≤ B.supdens` using `by tauto`. Establish `c0 : 0 ≤ B.c0 * B.c0'` using `by unfold S3.MassData.c0 S3.MassData.c0'; positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem each_level_counted_once : Formalism.FourierDecayAlt.J.OnceOnly := by
  intro P _ B hpos hk hA
  unfold S3.MassData.InTheoremA S3.MassData.Smod at hA
  obtain ⟨hk1, hk2⟩ := hk
  have hp := hpos.2
  have hvN : 0 < B.volN := by tauto
  have hvH : 0 < B.volH := by tauto
  have hvN' : 0 < B.volN' := by tauto
  have hvH' : 0 < B.volH' := by tauto
  have hd : 0 < B.dimπ := by tauto
  have hd' : 0 < B.dimπ' := by tauto
  have hn : 0 < B.n0c := by tauto
  have hs : 0 ≤ B.supdens := by tauto
  have c0 : 0 ≤ B.c0 * B.c0' := by unfold S3.MassData.c0 S3.MassData.c0'; positivity
  calc B.c0 * B.c0' * B.KV ≤ B.c0 * B.c0' * (B.supdens * B.n0c * B.KtopV) :=
        mul_le_mul_of_nonneg_left hk1 c0
    _ = B.supdens * B.n0c * (B.c0 * B.c0' * B.KtopV) := by ring
    _ ≤ B.supdens * B.n0c * ((1 + B.δ) * B.IntN) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

/- English proof (translation)
Introduce `hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd`. Take `⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩` from `hPos`. Establish `hn : 0 < B.n0c` using `a33`. Establish `hen : 0 < B.e1 * B.n0c` using `mul_pos he hn`. Establish `key` using `hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) } ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF (by`.

Prove the components needed by the constructor for the conclusion. Use `show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))`. Rewrite using `[mul_div_cancel₀ _ hen.ne']`. Use `show 0 ≤ B.KV / (B.e1 * B.n0c)`. Conclude with `div_nonneg hKV hen.le)`.

Use `hMass`. Use the proof step `(by show B.e1 ≤ B.e1; exact le_refl _)`. Use the proof step `(by show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN`. Rewrite using `[← mul_div_assoc, div_le_iff₀ hen]`. Establish `e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c)` using `by ring`.

Use the proof step `linarith)`. Use `hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd`. Conclude with `key`.
-/
theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      have e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c) := by ring
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
