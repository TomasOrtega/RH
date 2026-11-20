import ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
import ReciprocityTheory.DualLattices.StdJForm4
import ReciprocityTheory.DualLattices.ExistsMatOfEquiv
import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import ReciprocityTheory.DualLattices.MatEquivApply

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

/- English proof (translation)
Use extensionality with `k`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
private lemma smulMV2 {R : Type} [CommRing R] {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R)
    (v : μ → R) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext k; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX`. Use `haveI : IsDomain R := htd_domain hS`. Establish `hv` using `hS.integers`. Establish `hcp : cp ≠ 0` using `htd_cp_ne hS`. Use `set ι := algebraMap ℤ_[p] R with hι`.

Establish `hidw : H.ρ (e w) * H.ρ (e w) = H.ρ (e w)` using `by rw [← map_mul, horth, if_pos rfl]`. Take `⟨L, hLB, hBL⟩` from `PullbackHopfOrder.exists_split (H.ρ (e w)) hidw Bw hrange hker`. Use `set B := Bw.map ι with hB`. Use `set εw := (H.ρ (e w)).map ι with hεw`. Establish `hLB' : L.map ι * B = 1` using `by rw [hB, ← Matrix.map_mul, hLB, Matrix.map_one _ (map_zero ι) (map_one ι)]`.

Establish `hBL' : B * L.map ι = εw` using `by rw [hB, ← Matrix.map_mul, hBL]`. Establish `hεB : εw * B = B`. Rewrite using `[← hBL', Matrix.mul_assoc, hLB', Matrix.mul_one]`. Use `set Φ := phiP H e with hΦ`. Use `set M := Φ * B with hM`.

Take `⟨hform, hblock, hPblock⟩` from `btP_facts hS H e π horth hσ hsT hPT hsL hPL`. Establish `hJ` using `phiP_J hS H e π horth hσ hsT hPT hsL hPL`. Take `⟨-, -, hEdet⟩` from `htd_E H`. Use `set E' := H.E.map ι with hE'`. Establish `hdetΦ : Φ.det ≠ 0`.

Introduce `h0`. Establish `h` using `det_sq_eq E' Φ cp hJ`. Rewrite `h` using `[h0, zero_pow two_ne_zero]`. Establish `hne : cp ^ (2 * g) * (E'.det * (stdJ R g).det) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hcp) (mul_ne_zero hEdet.ne_zero isUnit_det_stdJ.ne_zero)`. Conclude with `hne h.symm`.

Establish `hΦinj : ∀ x, Φ *ᵥ x = 0 → x = 0`. Introduce `x hx`. Establish `h1 : Φ.det • x = 0`. Establish `h2 : (Φ.adjugate * Φ) *ᵥ x = Φ.det • x` using `by rw [adjugate_mul, smulMV2, one_mulVec]`. Rewrite using `[← h2, ← mulVec_mulVec, hx, mulVec_zero]`.

Conclude with `(smul_eq_zero.1 h1).resolve_left hdetΦ`. Establish `hMinj : ∀ t, M *ᵥ t = 0 → t = 0`. Introduce `t ht`. Establish `h1 : B *ᵥ t = 0` using `hΦinj _ (by rw [mulVec_mulVec]; exact ht)`. Rewrite using `[← one_mulVec t, ← hLB', ← mulVec_mulVec, h1, mulVec_zero]`.

Use `set Φp := E'⁻¹ * Φᵀ * stdJ R g with hΦp`. Establish `hΦpΦ : Φp * Φ = cp • (1 : Matrix (Ix g) (Ix g) R)`. Rewrite using `[hΦp, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hJ, Matrix.mul_smul, nonsing_inv_mul _ hEdet]`. Establish `hΦΦp : Φ * Φp = cp • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R)`. Establish `h1 : (Φ * Φp - cp • 1) * Φ = 0`.

Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, hΦpΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]`. Establish `h2 : Φ.det • (Φ * Φp - cp • 1) = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_smul, Matrix.mul_one]`. Use `_ = (Φ * Φp - cp • 1) * (Φ * Φ.adjugate) := by rw [mul_adjugate]`.

Use `_ = ((Φ * Φp - cp • 1) * Φ) * Φ.adjugate := by rw [Matrix.mul_assoc]`. Use `_ = 0 := by rw [h1, Matrix.zero_mul]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdetΦ)`. Use `set Pw : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R := fromBlocks (H.ρL (e (π w)))ᵀ 0 0 (H.ρL (e w)) with hPw`. Establish `hidL : ∀ a : O, a * a = a → H.ρL a * H.ρL a = H.ρL a` using `fun a ha => by rw [← map_mul, ha]`.

Establish `hidwL` using `hidL (e w) (by rw [horth, if_pos rfl])`. Establish `hidwbL` using `hidL (e (π w)) (by rw [horth, if_pos rfl])`. Establish `hPwmv : ∀ q, Pw *ᵥ q = Sum.elim ((H.ρL (e (π w)))ᵀ *ᵥ (q ∘ Sum.inl)) (H.ρL (e w) *ᵥ (q ∘ Sum.inr))`. Introduce `q`. Rewrite using `[hPw, ← Sum.elim_comp_inl_inr q, fromBlocks_mulVec]`.

Simplify using the standard rewrite rules. Establish `hΦεw : Φ * εw = Pw * Φ`. Establish `e1 : H.Ht * εw = (H.ρL (e (π w)))ᵀ * H.Ht` using `by rw [hεw, H.Ht_equivariant.1 (e w), hσ w]`. Rewrite using `[hΦ, phiP, fromRows_mul, e1, hblock w]`. Use extensionality with `i j`.

Break down `i with i | i` into its components or cases. Simplify using `[hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]`. Simplify using `[hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]`. Establish `hrangeP : ∀ (P : Matrix (Fin g) (Fin g) R), P * P = P → ∀ x, x ∈ LinearMap.range (Matrix.mulVecLin P) ↔ P *ᵥ x = x`. Introduce `P hP x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ show P *ᵥ (P *ᵥ y) = P *ᵥ y`. Rewrite using `[mulVec_mulVec, hP]`. Introduce `hx`. Conclude with `⟨x, hx⟩`.

Establish `hidT : (H.ρL (e (π w)))ᵀ * (H.ρL (e (π w)))ᵀ = (H.ρL (e (π w)))ᵀ`. Rewrite using `[← transpose_mul, hidwbL]`. Establish `hQw : ∀ q, q ∈ qW H (e w) (e (π w)) ↔ Pw *ᵥ q = q`. Introduce `q`. Use `show (q ∘ Sum.inl ∈ lieDPart H (e (π w)) ∧ q ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (H.ρL (e w)))) ↔ _`.

Rewrite using `[show lieDPart H (e (π w)) = LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))ᵀ) from rfl, hrangeP _ hidT, hrangeP _ hidwL, hPwmv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Rewrite using `[h1, h2]`. Conclude with `Sum.elim_comp_inl_inr q`.

Introduce `h`. Conclude with `⟨by rw [← h] at *; funext k; exact (congrFun h (Sum.inl k)), by funext k; exact congrFun h (Sum.inr k)⟩`. Establish `hmapT : (tPart H (e w)).map (Matrix.mulVecLin Φ) = LinearMap.range (Matrix.mulVecLin M)`. Use extensionality with `q`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Use `⟨L.map ι *ᵥ x, ?_⟩` and prove the remaining obligations. Use `show M *ᵥ (L.map ι *ᵥ x) = Φ *ᵥ (εw *ᵥ x)`. Rewrite using `[hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL']`. Introduce and unpack `⟨t, rfl⟩`.

Use `⟨εw *ᵥ (B *ᵥ t), ⟨B *ᵥ t, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show Φ *ᵥ (εw *ᵥ (B *ᵥ t)) = M *ᵥ t`. Rewrite using `[mulVec_mulVec (M := εw), hεB, hM, mulVec_mulVec]`. Establish `hMQ : ∀ t, Pw *ᵥ (M *ᵥ t) = M *ᵥ t`. Introduce `t`.

Rewrite using `[hM, ← mulVec_mulVec, mulVec_mulVec (M := Pw), ← hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := εw), hεB]`. Establish `hkillQ : ∀ q, Pw *ᵥ q = q → ∃ t, M *ᵥ t = cp • q`. Introduce `q hq`. Use `⟨L.map ι *ᵥ (εw *ᵥ (Φp *ᵥ q)), ?_⟩` and prove the remaining obligations. Establish `hεε : εw * εw = εw` using `by rw [hεw, ← Matrix.map_mul, hidw]`.

Rewrite using `[hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL', mulVec_mulVec (M := εw), hεε, mulVec_mulVec (M := Φ), hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := Φ), hΦΦp, smulMV2, one_mulVec, mulVec_smul, hq]`. Establish `hsat : ∀ q (c : R), c ≠ 0 → Pw *ᵥ (c • q) = c • q → Pw *ᵥ q = q`. Introduce `q c hc h`. Rewrite `h` using `[mulVec_smul]`. Conclude with `smul_right_injective _ hc h`.

Use `set e2 : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he2`. Use `set M' : Matrix (Fin (g + g)) (Fin r) R := M.submatrix e2.symm id with hM'`. Establish `hM'v : ∀ t, M' *ᵥ t = (M *ᵥ t) ∘ e2.symm` using `fun t => by`. Use function extensionality and compare the values at `j`. Simplify using `[hM', Matrix.mulVec, dotProduct]`.

Take `⟨P, Q, a, hPu, hQu, hD⟩` from `Smith.smith_mat hv (g + g) r M'`. Use `set D := P * M' * Q with hDdef`. Establish `hDv : ∀ t (j : Fin (g + g)), (D *ᵥ t) j = if h : (j : ℕ) < r then a j * t ⟨j, h⟩ else 0`. Introduce `t j`. Simplify using `only [Matrix.mulVec, dotProduct, hD, ite_mul, zero_mul]`.

Conclude with `sum_val_eq (j : ℕ) (fun k => a j * t k)`. Establish `hQQ : ∀ t, Q *ᵥ (Q⁻¹ *ᵥ t) = t` using `fun t => by`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]`. Establish `hQQ' : ∀ t, Q⁻¹ *ᵥ (Q *ᵥ t) = t` using `fun t => by`. Rewrite using `[mulVec_mulVec, nonsing_inv_mul _ hQu, one_mulVec]`.

Establish `hPP : ∀ t, P *ᵥ (P⁻¹ *ᵥ t) = t` using `fun t => by`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]`. Establish `hPP' : ∀ t, P⁻¹ *ᵥ (P *ᵥ t) = t` using `fun t => by`. Rewrite using `[mulVec_mulVec, nonsing_inv_mul _ hPu, one_mulVec]`. Establish `hM'D : ∀ t, P *ᵥ (M' *ᵥ t) = D *ᵥ (Q⁻¹ *ᵥ t)` using `fun t => by`.

Rewrite using `[hDdef, ← mulVec_mulVec, ← mulVec_mulVec, hQQ]`. Establish `hMzero : ∀ t, M' *ᵥ t = 0 → t = 0`. Introduce `t ht`. Apply `hMinj` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Establish `h1` using `congrFun ht (e2 x)`. Rewrite `h1` using `[hM'v]`. Simplify using `using h1`. Establish `hDz : ∀ s, D *ᵥ s = 0 → s = 0`. Introduce `s hs`.

Establish `h1 : M' *ᵥ (Q *ᵥ s) = 0`. Rewrite using `[← hPP' (M' *ᵥ (Q *ᵥ s)), hM'D, hQQ', hs, mulVec_zero]`. Rewrite using `[← hQQ' s, hMzero _ h1, mulVec_zero]`. Establish `hsingle_ne : ∀ {n : ℕ} (k : Fin n), (Pi.single k (1 : R) : Fin n → R) ≠ 0`. Introduce `n k h`.

Establish `h1` using `congrFun h k`. Simplify using `at h1`. Establish `hrle : ∀ k : Fin r, (k : ℕ) < g + g`. Introduce `k`. Assume the negation of the conclusion as `hk`.

Apply `hsingle_ne k` to reduce the goal to its premises. Apply `hDz` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Rewrite using `[hDv]`. Use `split_ifs with h`.

Rewrite using `[Pi.single_eq_of_ne]`. Simplify using the standard rewrite rules. Introduce `hjk`. Apply `hk` to reduce the goal to its premises. Rewrite using `[← hjk]`.

Conclude with `j.isLt`. Both sides reduce to the same expression. Use `set dj : Fin r → R := fun k => a ⟨k, hrle k⟩ with hdj`. Establish `hDsingle : ∀ k : Fin r, D *ᵥ Pi.single k 1 = dj k • Pi.single (⟨k, hrle k⟩ : Fin (g + g)) 1`. Introduce `k`.

Use function extensionality and compare the values at `j`. Rewrite using `[hDv]`. Distinguish the cases in `hjk : (j : ℕ) = k`. Establish `hj : j = ⟨k, hrle k⟩` using `Fin.ext hjk`. Substitute `hj` using the available equality.

Rewrite using `[dif_pos k.isLt]`. Simplify using `[hdj]`. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne (fun h => hjk (by rw [h])), smul_zero] split_ifs with h`. Rewrite using `[Pi.single_eq_of_ne (fun h' => hjk (by rw [← h'])), mul_zero]`. Both sides reduce to the same expression.

Establish `ha0 : ∀ k, dj k ≠ 0`. Introduce `k hk`. Apply `hsingle_ne k` to reduce the goal to its premises. Apply `hDz` to reduce the goal to its premises. Rewrite using `[hDsingle, hk, zero_smul]`.

Use `⟨Q⁻¹, dj, isUnit_nonsing_inv_det Q hQu, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Establish `hDQ : D * Q⁻¹ = P * M'`. Rewrite using `[hDdef, Matrix.mul_assoc, mul_nonsing_inv _ hQu, Matrix.mul_one]`. Establish `h1 : dj k • (Q⁻¹) k = (D * Q⁻¹) ⟨k, hrle k⟩`.

Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mul_apply, hD, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[hdj]`. Introduce `b _ hb`.

Rewrite using `[if_neg (fun h => hb (Fin.ext h)), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`. Rewrite using `[h1, hDQ]`. Establish `h3 : (P * M') ⟨k, hrle k⟩ = ∑ l, P ⟨k, hrle k⟩ l • (fun i => M (e2.symm l) i)`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mul_apply, Finset.sum_apply, hM']`. Rewrite using `[h3]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e2.symm l, rfl⟩)`. Introduce `k`.

Use `set j : Fin (g + g) := ⟨k, hrle k⟩`. Use `set u := P⁻¹ *ᵥ Pi.single j 1`. Establish `hu : M *ᵥ (Q *ᵥ Pi.single k 1) = dj k • (u ∘ e2)`. Use function extensionality and compare the values at `x`. Establish `h1 : M' *ᵥ (Q *ᵥ Pi.single k 1) = dj k • u`.

Rewrite using `[← hPP' (M' *ᵥ _), hM'D, hQQ', hDsingle, mulVec_smul]`. Establish `h2` using `congrFun h1 (e2 x)`. Rewrite `h2` using `[hM'v]`. Simplify using `using h2`. Establish `hsatu : Pw *ᵥ (u ∘ e2) = u ∘ e2` using `hsat (u ∘ e2) (dj k) (ha0 k) (by rw [← hu]; exact hMQ _)`.

Take `⟨t, ht⟩` from `hkillQ _ hsatu`. Establish `h3 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • Pi.single j 1`. Rewrite using `[← hM'D, hM'v, ht]`. Establish `: (cp • (u ∘ ⇑e2)) ∘ ⇑e2.symm = cp • u` using `by funext y; simp`. Rewrite using `[this, mulVec_smul, hPP]`.

Establish `h4` using `congrFun h3 j`. Rewrite `h4` using `[hDv, dif_pos k.isLt]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4`. Apply `hv.le_of_dvd` to reduce the goal to its premises. Conclude with `⟨_, h4.symm⟩`.

Set `F : qW H (e w) (e (π w)) →ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k})` to `LinearMap.pi fun k => (Submodule.mkQ (Ideal.span {dj k})) ∘ₗ (LinearMap.proj (⟨k, hrle k⟩ : Fin (g + g))) ∘ₗ P.mulVecLin ∘ₗ (LinearMap.funLeft R R e2.symm) ∘ₗ (qW H (e w) (e (π w))).subtype`. Establish `hF : ∀ q k, F q k = Ideal.Quotient.mk _ ((P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩)` using `fun q k => rfl`. Establish `hker : LinearMap.ker F = (LinearMap.range (Matrix.mulVecLin M)).comap (qW H (e w) (e (π w))).subtype`. Use extensionality with `q`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_comap]`.

Prove the components needed by the constructor for the conclusion. Introduce `hq`. Establish `hq' : ∀ k, (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩ ∈ Ideal.span {dj k}` using `fun k => Ideal.Quotient.eq_zero_iff_mem.1 ((hF q k).symm.trans (congrFun hq k))`. Use `choose s hs using fun k => Ideal.mem_span_singleton'.1 (hq' k)`. Take `⟨t, ht⟩` from `hkillQ q ((hQw q).1 q.2)`.

Establish `hhigh : ∀ j : Fin (g + g), ¬ (j : ℕ) < r → (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) j = 0`. Introduce `j hj`. Establish `h1 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm))`. Rewrite using `[← hM'D, hM'v, ht, ← mulVec_smul]`. Both sides reduce to the same expression.

Establish `h2` using `congrFun h1 j`. Rewrite `h2` using `[hDv, dif_neg hj, Pi.smul_apply, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h2.symm).resolve_left hcp`. Establish `hPq : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ s`. Use function extensionality and compare the values at `j`.

Rewrite using `[hDv]`. Use `split_ifs with h`. Rewrite using `[← hs ⟨j, h⟩, mul_comm]`. Conclude with `hhigh j h`. Use `⟨Q *ᵥ s, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Establish `h1 : M' *ᵥ (Q *ᵥ s) = (q : Fin g ⊕ Fin g → R) ∘ e2.symm`. Rewrite using `[← hPP' (M' *ᵥ _), hM'D, hQQ', ← hPq, hPP']`. Establish `h2` using `congrFun h1 (e2 x)`. Rewrite `h2` using `[hM'v]`.

Simplify using `using h2`. Introduce and unpack `⟨t, ht⟩`. Use function extensionality and compare the values at `k`. Rewrite using `[hF]`. Apply `Ideal.Quotient.eq_zero_iff_mem.2` to reduce the goal to its premises.

Establish `h1 : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ (Q⁻¹ *ᵥ t)`. Rewrite using `[← hM'D, hM'v]`. Use `congr 1`. Conclude with `congrArg (· ∘ e2.symm) ht.symm`. Rewrite using `[h1, hDv, dif_pos k.isLt]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`. Establish `hsurj : Function.Surjective F`. Introduce `z`. Use `set y : Fin r → R := fun k => Quotient.out (z k)`. Use `set α : R := ∏ k, dj k`.

Establish `hα : α ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => ha0 k`. Use `set yt : Fin (g + g) → R := fun j => if h : (j : ℕ) < r then y ⟨j, h⟩ else 0`. Use `set u := P⁻¹ *ᵥ yt`. Use `set s : Fin r → R := fun k => (∏ l ∈ Finset.univ.erase k, dj l) * y k`. Establish `hDs : D *ᵥ s = α • yt`.

Use function extensionality and compare the values at `j`. Rewrite using `[hDv]`. Use `split_ifs with h`. Simplify using `only [Pi.smul_apply, smul_eq_mul, yt, dif_pos h, s, α]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ dj (Finset.mem_univ ⟨j, h⟩)]`.

Simplify using `only [hdj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[yt, dif_neg h]`. Establish `hαu : M *ᵥ (Q *ᵥ s) = α • (u ∘ e2)`. Use function extensionality and compare the values at `x`.

Establish `h1 : M' *ᵥ (Q *ᵥ s) = α • u`. Rewrite using `[← hPP' (M' *ᵥ _), hM'D, hQQ', hDs, mulVec_smul]`. Establish `h2` using `congrFun h1 (e2 x)`. Rewrite `h2` using `[hM'v]`. Simplify using `using h2`.

Establish `hu : Pw *ᵥ (u ∘ e2) = u ∘ e2` using `hsat _ α hα (by rw [← hαu]; exact hMQ _)`. Use `⟨⟨u ∘ e2, (hQw _).2 hu⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[hF]`. Establish `h1 : ((u ∘ ⇑e2) ∘ ⇑e2.symm) = u` using `by funext j; simp`.

Use `show Ideal.Quotient.mk _ ((P *ᵥ ((u ∘ ⇑e2) ∘ ⇑e2.symm)) ⟨k, hrle k⟩) = z k`. Rewrite using `[h1, hPP]`. Simplify using `only [yt, dif_pos k.isLt, Fin.eta, y]`. Conclude with `Ideal.Quotient.mk_out (z k)`. Establish `heq : xMod H e π w ≃ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k})` using `(Submodule.quotEquivOfEq _ _ (by rw [hmapT, hker])).trans (F.quotKerEquivOfSurjective hsurj)`.

Conclude with `hasLen_unique hv hX ⟨r, dj, ⟨heq⟩, rfl⟩`.
-/
theorem smith_normal_form_statement : EigenQuotientSmithStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker X hX
  haveI : IsDomain R := htd_domain hS
  have hv := hS.integers
  have hcp : cp ≠ 0 := htd_cp_ne hS
  set ι := algebraMap ℤ_[p] R with hι
  have hidw : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, horth, if_pos rfl]
  obtain ⟨L, hLB, hBL⟩ := PullbackHopfOrder.exists_split (H.ρ (e w)) hidw Bw hrange hker
  set B := Bw.map ι with hB
  set εw := (H.ρ (e w)).map ι with hεw
  have hLB' : L.map ι * B = 1 := by rw [hB, ← Matrix.map_mul, hLB, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hBL' : B * L.map ι = εw := by rw [hB, ← Matrix.map_mul, hBL]
  have hεB : εw * B = B := by
    rw [← hBL', Matrix.mul_assoc, hLB', Matrix.mul_one]
  set Φ := phiP H e with hΦ
  set M := Φ * B with hM
  obtain ⟨hform, hblock, hPblock⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  have hJ := phiP_J hS H e π horth hσ hsT hPT hsL hPL
  obtain ⟨-, -, hEdet⟩ := htd_E H
  set E' := H.E.map ι with hE'
  have hdetΦ : Φ.det ≠ 0 := by
    intro h0
    have h := det_sq_eq E' Φ cp hJ
    rw [h0, zero_pow two_ne_zero] at h
    have hne : cp ^ (2 * g) * (E'.det * (stdJ R g).det) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hcp) (mul_ne_zero hEdet.ne_zero isUnit_det_stdJ.ne_zero)
    exact hne h.symm
  have hΦinj : ∀ x, Φ *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h1 : Φ.det • x = 0 := by
      have h2 : (Φ.adjugate * Φ) *ᵥ x = Φ.det • x := by rw [adjugate_mul, smulMV2, one_mulVec]
      rw [← h2, ← mulVec_mulVec, hx, mulVec_zero]
    exact (smul_eq_zero.1 h1).resolve_left hdetΦ
  have hMinj : ∀ t, M *ᵥ t = 0 → t = 0 := by
    intro t ht
    have h1 : B *ᵥ t = 0 := hΦinj _ (by rw [mulVec_mulVec]; exact ht)
    rw [← one_mulVec t, ← hLB', ← mulVec_mulVec, h1, mulVec_zero]

  set Φp := E'⁻¹ * Φᵀ * stdJ R g with hΦp
  have hΦpΦ : Φp * Φ = cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [hΦp, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hJ, Matrix.mul_smul,
      nonsing_inv_mul _ hEdet]
  have hΦΦp : Φ * Φp = cp • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) := by
    have h1 : (Φ * Φp - cp • 1) * Φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hΦpΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : Φ.det • (Φ * Φp - cp • 1) = 0 := by
      calc Φ.det • (Φ * Φp - cp • 1) = (Φ * Φp - cp • 1) * (Φ.det • 1) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Φ * Φp - cp • 1) * (Φ * Φ.adjugate) := by rw [mul_adjugate]
        _ = ((Φ * Φp - cp • 1) * Φ) * Φ.adjugate := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.zero_mul]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdetΦ)

  set Pw : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fromBlocks (H.ρL (e (π w)))ᵀ 0 0 (H.ρL (e w)) with hPw
  have hidL : ∀ a : O, a * a = a → H.ρL a * H.ρL a = H.ρL a := fun a ha => by rw [← map_mul, ha]
  have hidwL := hidL (e w) (by rw [horth, if_pos rfl])
  have hidwbL := hidL (e (π w)) (by rw [horth, if_pos rfl])
  have hPwmv : ∀ q, Pw *ᵥ q = Sum.elim ((H.ρL (e (π w)))ᵀ *ᵥ (q ∘ Sum.inl))
      (H.ρL (e w) *ᵥ (q ∘ Sum.inr)) := by
    intro q
    rw [hPw, ← Sum.elim_comp_inl_inr q, fromBlocks_mulVec]
    simp
  have hΦεw : Φ * εw = Pw * Φ := by
    have e1 : H.Ht * εw = (H.ρL (e (π w)))ᵀ * H.Ht := by rw [hεw, H.Ht_equivariant.1 (e w), hσ w]
    rw [hΦ, phiP, fromRows_mul, e1, hblock w]
    ext i j
    rcases i with i | i
    · simp [hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
    · simp [hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have hrangeP : ∀ (P : Matrix (Fin g) (Fin g) R), P * P = P → ∀ x,
      x ∈ LinearMap.range (Matrix.mulVecLin P) ↔ P *ᵥ x = x := by
    intro P hP x
    constructor
    · rintro ⟨y, rfl⟩
      show P *ᵥ (P *ᵥ y) = P *ᵥ y
      rw [mulVec_mulVec, hP]
    · intro hx; exact ⟨x, hx⟩
  have hidT : (H.ρL (e (π w)))ᵀ * (H.ρL (e (π w)))ᵀ = (H.ρL (e (π w)))ᵀ := by
    rw [← transpose_mul, hidwbL]
  have hQw : ∀ q, q ∈ qW H (e w) (e (π w)) ↔ Pw *ᵥ q = q := by
    intro q
    show (q ∘ Sum.inl ∈ lieDPart H (e (π w)) ∧ q ∘ Sum.inr ∈
      LinearMap.range (Matrix.mulVecLin (H.ρL (e w)))) ↔ _
    rw [show lieDPart H (e (π w)) = LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))ᵀ) from rfl,
      hrangeP _ hidT, hrangeP _ hidwL, hPwmv]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, h2]; exact Sum.elim_comp_inl_inr q
    · intro h
      exact ⟨by rw [← h] at *; funext k; exact (congrFun h (Sum.inl k)),
        by funext k; exact congrFun h (Sum.inr k)⟩

  have hmapT : (tPart H (e w)).map (Matrix.mulVecLin Φ) = LinearMap.range (Matrix.mulVecLin M) := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨L.map ι *ᵥ x, ?_⟩
      show M *ᵥ (L.map ι *ᵥ x) = Φ *ᵥ (εw *ᵥ x)
      rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL']
    · rintro ⟨t, rfl⟩
      refine ⟨εw *ᵥ (B *ᵥ t), ⟨B *ᵥ t, rfl⟩, ?_⟩
      show Φ *ᵥ (εw *ᵥ (B *ᵥ t)) = M *ᵥ t
      rw [mulVec_mulVec (M := εw), hεB, hM, mulVec_mulVec]
  have hMQ : ∀ t, Pw *ᵥ (M *ᵥ t) = M *ᵥ t := by
    intro t
    rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := Pw), ← hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := εw), hεB]
  have hkillQ : ∀ q, Pw *ᵥ q = q → ∃ t, M *ᵥ t = cp • q := by
    intro q hq
    refine ⟨L.map ι *ᵥ (εw *ᵥ (Φp *ᵥ q)), ?_⟩
    have hεε : εw * εw = εw := by rw [hεw, ← Matrix.map_mul, hidw]
    rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL', mulVec_mulVec (M := εw), hεε, mulVec_mulVec (M := Φ),
      hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := Φ), hΦΦp, smulMV2, one_mulVec, mulVec_smul, hq]
  have hsat : ∀ q (c : R), c ≠ 0 → Pw *ᵥ (c • q) = c • q → Pw *ᵥ q = q := by
    intro q c hc h
    rw [mulVec_smul] at h
    exact smul_right_injective _ hc h

  set e2 : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he2
  set M' : Matrix (Fin (g + g)) (Fin r) R := M.submatrix e2.symm id with hM'
  have hM'v : ∀ t, M' *ᵥ t = (M *ᵥ t) ∘ e2.symm := fun t => by
    funext j; simp [hM', Matrix.mulVec, dotProduct]
  obtain ⟨P, Q, a, hPu, hQu, hD⟩ := Smith.smith_mat hv (g + g) r M'
  set D := P * M' * Q with hDdef
  have hDv : ∀ t (j : Fin (g + g)), (D *ᵥ t) j = if h : (j : ℕ) < r then a j * t ⟨j, h⟩ else 0 := by
    intro t j
    simp only [Matrix.mulVec, dotProduct, hD, ite_mul, zero_mul]
    exact sum_val_eq (j : ℕ) (fun k => a j * t k)
  have hQQ : ∀ t, Q *ᵥ (Q⁻¹ *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
  have hQQ' : ∀ t, Q⁻¹ *ᵥ (Q *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hQu, one_mulVec]
  have hPP : ∀ t, P *ᵥ (P⁻¹ *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]
  have hPP' : ∀ t, P⁻¹ *ᵥ (P *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hPu, one_mulVec]
  have hM'D : ∀ t, P *ᵥ (M' *ᵥ t) = D *ᵥ (Q⁻¹ *ᵥ t) := fun t => by
    rw [hDdef, ← mulVec_mulVec, ← mulVec_mulVec, hQQ]
  have hMzero : ∀ t, M' *ᵥ t = 0 → t = 0 := by
    intro t ht
    apply hMinj
    funext x
    have h1 := congrFun ht (e2 x)
    rw [hM'v] at h1
    simpa using h1
  have hDz : ∀ s, D *ᵥ s = 0 → s = 0 := by
    intro s hs
    have h1 : M' *ᵥ (Q *ᵥ s) = 0 := by
      rw [← hPP' (M' *ᵥ (Q *ᵥ s)), hM'D, hQQ', hs, mulVec_zero]
    rw [← hQQ' s, hMzero _ h1, mulVec_zero]
  have hsingle_ne : ∀ {n : ℕ} (k : Fin n), (Pi.single k (1 : R) : Fin n → R) ≠ 0 := by
    intro n k h
    have h1 := congrFun h k
    simp at h1
  have hrle : ∀ k : Fin r, (k : ℕ) < g + g := by
    intro k
    by_contra hk
    apply hsingle_ne k
    apply hDz
    funext j
    rw [hDv]
    split_ifs with h
    · rw [Pi.single_eq_of_ne]
      · simp
      · intro hjk; apply hk; rw [← hjk]; exact j.isLt
    · rfl
  set dj : Fin r → R := fun k => a ⟨k, hrle k⟩ with hdj
  have hDsingle : ∀ k : Fin r, D *ᵥ Pi.single k 1 = dj k • Pi.single (⟨k, hrle k⟩ : Fin (g + g)) 1 := by
    intro k
    funext j
    rw [hDv]
    by_cases hjk : (j : ℕ) = k
    · have hj : j = ⟨k, hrle k⟩ := Fin.ext hjk
      subst hj
      rw [dif_pos k.isLt]
      simp [hdj]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hjk (by rw [h])), smul_zero]
      split_ifs with h
      · rw [Pi.single_eq_of_ne (fun h' => hjk (by rw [← h'])), mul_zero]
      · rfl
  have ha0 : ∀ k, dj k ≠ 0 := by
    intro k hk
    apply hsingle_ne k
    apply hDz
    rw [hDsingle, hk, zero_smul]
  refine ⟨Q⁻¹, dj, isUnit_nonsing_inv_det Q hQu, ?_, ?_, ?_⟩
  ·
    intro k
    have hDQ : D * Q⁻¹ = P * M' := by
      rw [hDdef, Matrix.mul_assoc, mul_nonsing_inv _ hQu, Matrix.mul_one]
    have h1 : dj k • (Q⁻¹) k = (D * Q⁻¹) ⟨k, hrle k⟩ := by
      funext i
      simp only [Matrix.mul_apply, hD, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · simp [hdj]
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [h1, hDQ]
    have h3 : (P * M') ⟨k, hrle k⟩ = ∑ l, P ⟨k, hrle k⟩ l • (fun i => M (e2.symm l) i) := by
      funext i
      simp [Matrix.mul_apply, Finset.sum_apply, hM']
    rw [h3]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e2.symm l, rfl⟩)
  ·
    intro k
    set j : Fin (g + g) := ⟨k, hrle k⟩
    set u := P⁻¹ *ᵥ Pi.single j 1
    have hu : M *ᵥ (Q *ᵥ Pi.single k 1) = dj k • (u ∘ e2) := by
      funext x
      have h1 : M' *ᵥ (Q *ᵥ Pi.single k 1) = dj k • u := by
        rw [← hPP' (M' *ᵥ _), hM'D, hQQ', hDsingle, mulVec_smul]
      have h2 := congrFun h1 (e2 x)
      rw [hM'v] at h2
      simpa using h2
    have hsatu : Pw *ᵥ (u ∘ e2) = u ∘ e2 :=
      hsat (u ∘ e2) (dj k) (ha0 k) (by rw [← hu]; exact hMQ _)
    obtain ⟨t, ht⟩ := hkillQ _ hsatu
    have h3 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • Pi.single j 1 := by
      rw [← hM'D, hM'v, ht]
      have : (cp • (u ∘ ⇑e2)) ∘ ⇑e2.symm = cp • u := by funext y; simp
      rw [this, mulVec_smul, hPP]
    have h4 := congrFun h3 j
    rw [hDv, dif_pos k.isLt] at h4
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4
    apply hv.le_of_dvd
    exact ⟨_, h4.symm⟩
  ·
    let F : qW H (e w) (e (π w)) →ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k}) :=
      LinearMap.pi fun k => (Submodule.mkQ (Ideal.span {dj k})) ∘ₗ
        (LinearMap.proj (⟨k, hrle k⟩ : Fin (g + g))) ∘ₗ P.mulVecLin ∘ₗ
        (LinearMap.funLeft R R e2.symm) ∘ₗ (qW H (e w) (e (π w))).subtype
    have hF : ∀ q k, F q k = Ideal.Quotient.mk _
        ((P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩) := fun q k => rfl
    have hker : LinearMap.ker F =
        (LinearMap.range (Matrix.mulVecLin M)).comap (qW H (e w) (e (π w))).subtype := by
      ext q
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      constructor
      · intro hq
        have hq' : ∀ k, (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩ ∈ Ideal.span {dj k} :=
          fun k => Ideal.Quotient.eq_zero_iff_mem.1 ((hF q k).symm.trans (congrFun hq k))
        choose s hs using fun k => Ideal.mem_span_singleton'.1 (hq' k)
        obtain ⟨t, ht⟩ := hkillQ q ((hQw q).1 q.2)
        have hhigh : ∀ j : Fin (g + g), ¬ (j : ℕ) < r →
            (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) j = 0 := by
          intro j hj
          have h1 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) := by
            rw [← hM'D, hM'v, ht, ← mulVec_smul]
            rfl
          have h2 := congrFun h1 j
          rw [hDv, dif_neg hj, Pi.smul_apply, smul_eq_mul] at h2
          exact (mul_eq_zero.1 h2.symm).resolve_left hcp
        have hPq : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ s := by
          funext j
          rw [hDv]
          split_ifs with h
          · rw [← hs ⟨j, h⟩, mul_comm]
          · exact hhigh j h
        refine ⟨Q *ᵥ s, ?_⟩
        funext x
        have h1 : M' *ᵥ (Q *ᵥ s) = (q : Fin g ⊕ Fin g → R) ∘ e2.symm := by
          rw [← hPP' (M' *ᵥ _), hM'D, hQQ', ← hPq, hPP']
        have h2 := congrFun h1 (e2 x)
        rw [hM'v] at h2
        simpa using h2
      · rintro ⟨t, ht⟩
        funext k
        rw [hF]
        apply Ideal.Quotient.eq_zero_iff_mem.2
        have h1 : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ (Q⁻¹ *ᵥ t) := by
          rw [← hM'D, hM'v]
          congr 1
          exact congrArg (· ∘ e2.symm) ht.symm
        rw [h1, hDv, dif_pos k.isLt]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hsurj : Function.Surjective F := by
      intro z
      set y : Fin r → R := fun k => Quotient.out (z k)
      set α : R := ∏ k, dj k
      have hα : α ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha0 k
      set yt : Fin (g + g) → R := fun j => if h : (j : ℕ) < r then y ⟨j, h⟩ else 0
      set u := P⁻¹ *ᵥ yt
      set s : Fin r → R := fun k => (∏ l ∈ Finset.univ.erase k, dj l) * y k
      have hDs : D *ᵥ s = α • yt := by
        funext j
        rw [hDv]
        split_ifs with h
        · simp only [Pi.smul_apply, smul_eq_mul, yt, dif_pos h, s, α]
          rw [← Finset.mul_prod_erase Finset.univ dj (Finset.mem_univ ⟨j, h⟩)]
          simp only [hdj]
          ring
        · simp [yt, dif_neg h]
      have hαu : M *ᵥ (Q *ᵥ s) = α • (u ∘ e2) := by
        funext x
        have h1 : M' *ᵥ (Q *ᵥ s) = α • u := by
          rw [← hPP' (M' *ᵥ _), hM'D, hQQ', hDs, mulVec_smul]
        have h2 := congrFun h1 (e2 x)
        rw [hM'v] at h2
        simpa using h2
      have hu : Pw *ᵥ (u ∘ e2) = u ∘ e2 := hsat _ α hα (by rw [← hαu]; exact hMQ _)
      refine ⟨⟨u ∘ e2, (hQw _).2 hu⟩, ?_⟩
      funext k
      rw [hF]
      have h1 : ((u ∘ ⇑e2) ∘ ⇑e2.symm) = u := by funext j; simp
      show Ideal.Quotient.mk _ ((P *ᵥ ((u ∘ ⇑e2) ∘ ⇑e2.symm)) ⟨k, hrle k⟩) = z k
      rw [h1, hPP]
      simp only [yt, dif_pos k.isLt, Fin.eta, y]
      exact Ideal.Quotient.mk_out (z k)
    have heq : xMod H e π w ≃ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k}) :=
      (Submodule.quotEquivOfEq _ _ (by rw [hmapT, hker])).trans (F.quotKerEquivOfSurjective hsurj)
    exact hasLen_unique hv hX ⟨r, dj, ⟨heq⟩, rfl⟩

end ReciprocityTheory.PGsh.Up
