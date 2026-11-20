import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MonomialMemPolKSg

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

/- English proof (translation)
Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe n => exact le_rfl`.
-/
theorem coe_untopD_le (x : WithTop ℤ) : ((x.untopD 0 : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n => exact le_rfl

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def pullL : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K :=
  lsup fun ζ => monomial (D.pullE j ζ) 1

/- English proof (translation)
Unfold `coefOut`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[pullL, lsup_monomial, pullE_eIn, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[map_zero]`.
-/
theorem pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.pullL j (coefOut (D.outSeg j) μ Z) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then monomial (D.pullE j α) (Z.coeff α) else 0 := by
  unfold coefOut
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [pullL, lsup_monomial, pullE_eIn, smul_monomial, smul_eq_mul, mul_one]
  · rw [map_zero]

/- English proof (translation)
Rewrite using `[pullL_coefOut, map_sum]`. Unfold `coefOut`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[rename_monomial, mapDomain_pullE]`.

Rewrite using `[map_zero]`.
-/
theorem rename_pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    rename (Prod.map (D.e0 j) id) (D.pullL j (coefOut (D.outSeg j) μ Z)) = coefOut (D.outSeg j) μ Z := by
  rw [pullL_coefOut, map_sum]
  unfold coefOut
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [rename_monomial, mapDomain_pullE]
  · rw [map_zero]

variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

/- English proof (translation)
Establish `h : ∀ μ, D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) = ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then Z.coeff α • D.TT j cc PP (monomial (D.pullE j α) 1) else 0`. Introduce `μ`. Rewrite using `[pullL_coefOut, map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Establish `: monomial (D.pullE j α) (Z.coeff α) = Z.coeff α • monomial (D.pullE j α) (1 : K)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul]`. Rewrite using `[map_zero]`. Repeatedly rewrite using `[h, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm, Th, lsup_apply]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (eOut (D.outSeg j) α)]`. Rewrite using `[if_pos rfl, mul_smul_comm]`. Introduce `μ _ hμ`.

Rewrite using `[if_neg (Ne.symm hμ), mul_zero]`. Introduce `h2`. Conclude with `absurd (Finset.mem_image_of_mem _ hα) h2`.
-/
theorem Th_eq (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.Th j cc PP Z = ∑ μ ∈ Z.support.image (eOut (D.outSeg j)),
      monomial μ 1 * D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) := by
  have h : ∀ μ, D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then
        Z.coeff α • D.TT j cc PP (monomial (D.pullE j α) 1) else 0 := by
    intro μ
    rw [pullL_coefOut, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · have : monomial (D.pullE j α) (Z.coeff α) = Z.coeff α • monomial (D.pullE j α) (1 : K) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul]
    · rw [map_zero]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm, Th, lsup_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.sum_eq_single (eOut (D.outSeg j) α)]
  · rw [if_pos rfl, mul_smul_comm]
  · intro μ _ hμ
    rw [if_neg (Ne.symm hμ), mul_zero]
  · intro h2
    exact absurd (Finset.mem_image_of_mem _ hα) h2

/- English proof (translation)
Rewrite using `[Th_eq]`. Use `vala_sum _ _ fun μ hμ => ?_` and prove the remaining obligations. Take `⟨α0, hα0, rfl⟩` from `Finset.mem_image.mp hμ`. Use `vala_mul_left_nonneg ?_ ?_` and prove the remaining obligations. Apply `valS_nonneg_of_free` to reduce the goal to its premises.

Introduce `α hα i hi a`. Establish `h1` using `support_monomial_subset hα`. Rewrite `h1` using `[Finset.mem_singleton]`. Rewrite using `[h1, eOut_apply]`. Simplify using `only [YPset, Finset.mem_union, Finset.mem_image] at hi`.

Break down `hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩` into its components or cases. Rewrite using `[if_neg]`. Conclude with `not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))`. Use `split_ifs`. Conclude with `(hpre α0 hα0).2.2 m' a`.

Both sides reduce to the same expression. Use `set Q := D.pullL j (coefOut (D.outSeg j) (eOut (D.outSeg j) α0) Z) with hQdef`. Establish `hQK : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k))`. Rewrite using `[hQdef, pullL_coefOut]`. Use `Submodule.sum_mem _ fun α hα => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `monomial_mem_PolK_sg _ _ _ (D.pullE_deg j α (hpre α hα))`. Conclude with `Submodule.zero_mem _`. Establish `hQint : Integral v Q`. Rewrite using `[hQdef, pullL_coefOut]`.

Use `integral_sum' _ _ fun α _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `integral_monomial' _ (hZ α)`. Conclude with `integral_zero'`. Establish `hout : ∀ i ∈ D.TLset j m, ¬ D.outSeg j i`.

Introduce `i hi`. Simplify using `only [TLset, Finset.mem_union, Finset.mem_image] at hi`. Break down `hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩` into its components or cases. Conclude with `not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))`. Conclude with `not_not.mpr ((D.range_first_embedding j _).mpr (Or.inr ⟨m', rfl⟩))`.

Establish `hQval : ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) Q`. Establish `h1` using `valS_rename (D.e0 j) (D.index_embedding_injective j) D.msg (D.TLset j m) Q`. Rewrite `h1` using `[hQdef, rename_pullL_coefOut, TL_preimage, ← hQdef]`. Rewrite using `[← h1]`. Conclude with `le_trans ((vala_iff _ _ _ _).mp hθ) (valS_coefOut_le (D.outSeg j) D.msg _ hout _ Z)`.

Establish `hlt : D.stg j m < D.nB j + D.r + 1` using `by unfold stg; omega`. Set `i0 : Fin (D.nB j + D.r + 1)` to `⟨D.stg j m, hlt⟩`. Set `th : Fin (D.nB j + D.r + 1) → ℤ` to `fun i => if i = i0 then ⌈θ⌉ else (valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) Q).untopD 0`. Establish `hmem : ∀ i : Fin (D.nB j + D.r + 1), Q ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i)`. Introduce `i`.

Use `show ((th i : ℤ) : WithTop ℤ) ≤ _`. Distinguish the cases in `hi : i = i0`. Simplify using `only [th, if_pos hi]`. Rewrite using `[hi]`. Conclude with `hQval`.

Simplify using `only [th, if_neg hi]`. Conclude with `coe_untopD_le _`. Take `⟨c, -, hc1, hc2⟩` from `(h7 th Q) ⟨⟨hQK, hQint⟩, hmem⟩`. Rewrite using `[D.TT_expand j cc PP Ψ hli hcc Q hQK c hc2]`. Use `vala_sum _ _ fun b _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hcb : c b = 0`. Rewrite using `[hcb, zero_smul]`. Conclude with `vala_zero θ`. Use `vala_smul _ ?_` and prove the remaining obligations. Rewrite using `[vala_iff]`.

Establish `h2` using `hc1 b hcb i0`. Simplify using `only [th, if_true] at h2`. Conclude with `le_trans (WithTop.coe_le_coe.mpr h2) (hPPval b m i0 rfl)`.
-/
theorem Th_val [NeZero D.r] {v : AddValuation K (WithTop ℚ)}
    (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (path : ι → Fin (D.nB j + D.r + 1) → Fin D.r → ℤ)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (h7 : ∀ (th : Fin (D.nB j + D.r + 1) → ℤ) (F : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K),
      (F ∈ PolO v D.r (fun k => D.dO (D.eA j k)) ∧ ∀ i : Fin (D.nB j + D.r + 1),
        F ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i)) →
        ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ (∀ b, c b ≠ 0 → ∀ i, th i ≤ path b i (lastIdx D.r)) ∧
          F = ∑ b, c b • Ψ b)
    (hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : Integral v Z) (hpre : ∀ ζ ∈ Z.support, D.PreE j ζ)
    (m : Fin D.r) (θ : ℝ) (hθ : vala D.msg (D.TLset j m) θ Z) :
    vala D.msg (D.YPset j m) θ (D.Th j cc PP Z) := by
  rw [Th_eq]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α0, hα0, rfl⟩ := Finset.mem_image.mp hμ
  refine vala_mul_left_nonneg ?_ ?_
  · apply valS_nonneg_of_free
    intro α hα i hi a
    have h1 := support_monomial_subset hα
    rw [Finset.mem_singleton] at h1
    rw [h1, eOut_apply]
    simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
    · rw [if_neg]
      exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
    · split_ifs
      · exact (hpre α0 hα0).2.2 m' a
      · rfl
  · set Q := D.pullL j (coefOut (D.outSeg j) (eOut (D.outSeg j) α0) Z) with hQdef
    have hQK : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k)) := by
      rw [hQdef, pullL_coefOut]
      refine Submodule.sum_mem _ fun α hα => ?_
      split_ifs
      · exact monomial_mem_PolK_sg _ _ _ (D.pullE_deg j α (hpre α hα))
      · exact Submodule.zero_mem _
    have hQint : Integral v Q := by
      rw [hQdef, pullL_coefOut]
      refine integral_sum' _ _ fun α _ => ?_
      split_ifs
      · exact integral_monomial' _ (hZ α)
      · exact integral_zero'
    have hout : ∀ i ∈ D.TLset j m, ¬ D.outSeg j i := by
      intro i hi
      simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
      rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inr ⟨m', rfl⟩))
    have hQval : ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤
        valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) Q := by
      have h1 := valS_rename (D.e0 j) (D.index_embedding_injective j) D.msg (D.TLset j m) Q
      rw [hQdef, rename_pullL_coefOut, TL_preimage, ← hQdef] at h1
      rw [← h1]
      exact le_trans ((vala_iff _ _ _ _).mp hθ) (valS_coefOut_le (D.outSeg j) D.msg _ hout _ Z)
    have hlt : D.stg j m < D.nB j + D.r + 1 := by unfold stg; omega
    let i0 : Fin (D.nB j + D.r + 1) := ⟨D.stg j m, hlt⟩
    let th : Fin (D.nB j + D.r + 1) → ℤ := fun i =>
      if i = i0 then ⌈θ⌉ else (valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) Q).untopD 0
    have hmem : ∀ i : Fin (D.nB j + D.r + 1),
        Q ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i) := by
      intro i
      show ((th i : ℤ) : WithTop ℤ) ≤ _
      by_cases hi : i = i0
      · simp only [th, if_pos hi]
        rw [hi]
        exact hQval
      · simp only [th, if_neg hi]
        exact coe_untopD_le _
    obtain ⟨c, -, hc1, hc2⟩ := (h7 th Q) ⟨⟨hQK, hQint⟩, hmem⟩
    rw [D.TT_expand j cc PP Ψ hli hcc Q hQK c hc2]
    refine vala_sum _ _ fun b _ => ?_
    by_cases hcb : c b = 0
    · rw [hcb, zero_smul]; exact vala_zero θ
    · refine vala_smul _ ?_
      rw [vala_iff]
      have h2 := hc1 b hcb i0
      simp only [th, if_true] at h2
      exact le_trans (WithTop.coe_le_coe.mpr h2) (hPPval b m i0 rfl)

end TwistData

/- English proof (translation)
Introduce `hD D hr _ j`. Use `haveI : NeZero D.r := ⟨hr.ne'⟩`. Take `⟨ι, hι, Ψ, path, ncol, col, cidx, hts, occ, h3, h4, h5, h7, h8, h10, h11, h14, h16, h17⟩` from `hS hD (D.nB j + D.r) D.r (D.msg ∘ D.e0 j) (fun k => D.dO (D.eA j k))`. Establish `hmon : ∀ lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k))` using `fun lam h => ⟨monomial_mem_PolK_sg _ _ _ h, integral_monomial' _ (by simp)⟩`. Set `cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K` to `fun lam => if h : monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) then (h5 _ h).choose else 0`.

Establish `hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b`. Introduce `lam h`. Simplify using `only [cc, dif_pos (hmon lam h)]`. Conclude with `(h5 _ (hmon lam h)).choose_spec.2`. Establish `hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b)`.

Introduce `lam h b`. Simplify using `only [cc, dif_pos (hmon lam h)]`. Conclude with `(h5 _ (hmon lam h)).choose_spec.1 b`. Set `PP : ι → MvPolynomial (D.ML × Fin D.r) K` to `fun b => D.PsiP j (col b) (occ b)`. Establish `hPPint : ∀ b, Integral v (PP b)` using `fun b => D.PsiP_integral j (col b) (occ b) (h8 b ▸ (h3 b).2)`.

Establish `hPPph : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b)`. Introduce `b`. Rewrite using `[h8 b]`. Conclude with `D.PsiP_ph j p (col b) (occ b)`. Establish `hPPsupp : ∀ b, ∀ ξ ∈ (PP b).support, D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0` using `fun b ξ hξ => D.PsiP_support j (col b) (occ b) (h10 b) (h11 b) ξ hξ`.

Establish `hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m → ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b)`. Introduce `b m i0 hi0`. Rewrite using `[h17 b i0]`. Use `D.PsiP_val j (col b) (occ b) (h10 b) (cidx b) (fun k => hts b k i0) m ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Use `h14 b k i0 hk` as an intermediate fact. Rewrite `this` using `[hi0]`. Then use the resulting hypothesis. Introduce `k`. Use `h16 b k i0` as an intermediate fact. Rewrite `this` using `[hi0]`. Then use the resulting hypothesis.

Use `⟨D.Th j cc PP, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun ζ hζ => D.Th_integral j cc PP hccint hPPint ζ hζ`. Conclude with `fun ζ hζ => D.Th_ph j cc PP p Ψ hcc hPPph ζ hζ`. Conclude with `fun ζ hζ ζ' hζ' => D.Th_post j cc PP hPPsupp ζ hζ ζ' hζ'`. Conclude with `fun Z hZ hpre m θ _ hθ => D.Th_val j cc PP Ψ path h4 hcc h7 hPPval Z hZ hpre m θ hθ`.

Conclude with `fun S hS' Z => D.Th_away j cc PP (fun b ξ hξ => (hPPsupp b ξ hξ).2) S hS' Z`.
-/
theorem segStep_of {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
    (hS : SPAN K v p) : SegStep K v p := by
  classical
  intro hD D hr _ j
  haveI : NeZero D.r := ⟨hr.ne'⟩
  obtain ⟨ι, hι, Ψ, path, ncol, col, cidx, hts, occ, h3, h4, h5, h7, h8, h10, h11,
    h14, h16, h17⟩ := hS hD (D.nB j + D.r) D.r (D.msg ∘ D.e0 j) (fun k => D.dO (D.eA j k))
  have hmon : ∀ lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) := fun lam h =>
    ⟨monomial_mem_PolK_sg _ _ _ h, integral_monomial' _ (by simp)⟩
  let cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K := fun lam =>
    if h : monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) then (h5 _ h).choose else 0
  have hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) = ∑ b, cc lam b • Ψ b := by
    intro lam h
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.2
  have hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b) := by
    intro lam h b
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.1 b
  let PP : ι → MvPolynomial (D.ML × Fin D.r) K := fun b => D.PsiP j (col b) (occ b)
  have hPPint : ∀ b, Integral v (PP b) := fun b =>
    D.PsiP_integral j (col b) (occ b) (h8 b ▸ (h3 b).2)
  have hPPph : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b) := by
    intro b
    rw [h8 b]
    exact D.PsiP_ph j p (col b) (occ b)
  have hPPsupp : ∀ b, ∀ ξ ∈ (PP b).support,
      D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := fun b ξ hξ =>
    D.PsiP_support j (col b) (occ b) (h10 b) (h11 b) ξ hξ
  have hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b) := by
    intro b m i0 hi0
    rw [h17 b i0]
    refine D.PsiP_val j (col b) (occ b) (h10 b) (cidx b) (fun k => hts b k i0) m ?_ ?_
    · intro k hk
      have := h14 b k i0 hk
      rwa [hi0] at this
    · intro k
      have := h16 b k i0
      rwa [hi0] at this
  refine ⟨D.Th j cc PP, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ζ hζ => D.Th_integral j cc PP hccint hPPint ζ hζ
  · exact fun ζ hζ => D.Th_ph j cc PP p Ψ hcc hPPph ζ hζ
  · exact fun ζ hζ ζ' hζ' => D.Th_post j cc PP hPPsupp ζ hζ ζ' hζ'
  · exact fun Z hZ hpre m θ _ hθ => D.Th_val j cc PP Ψ path h4 hcc h7 hPPval Z hZ hpre m θ hθ
  · exact fun S hS' Z => D.Th_away j cc PP (fun b ξ hξ => (hPPsupp b ξ hξ).2) S hS' Z

end Formalism.MainNotions.PlaneGram
