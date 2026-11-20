import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace NormAverageBound

/- English proof (translation)
Unfold `GlobalTheory.CuspGeneric.avg`. Use `split_ifs with hex`. Take `⟨-, -, h1⟩` from `hex.choose_spec`. Establish `hfin : hex.choose.1 hex.choose.2 < ⊤` using `by rw [h1]; exact ENNReal.one_lt_top`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `using hC`.
-/
theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, ‖Φ x‖ ≤ C) : ‖avg Γ Φ‖ ≤ C := by
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with hex
  · obtain ⟨-, -, h1⟩ := hex.choose_spec
    have hfin : hex.choose.1 hex.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    calc ‖∫ x in hex.choose.2, Φ x ∂hex.choose.1‖ ≤ C * hex.choose.1.real hex.choose.2 :=
          norm_setIntegral_le_of_norm_le_const hfin (fun x _ => h x)
      _ = C := by simp [Measure.real, h1]
  · simpa using hC

end NormAverageBound

open NormAverageBound in
/- English proof (translation)
Introduce `hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g`. Take `⟨hFc, hFl, hFlaw, hFvan⟩` from `hF`. Establish `hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F` using `⟨hFc, hFl, hFlaw⟩`. Take `⟨hcolPre, hcoef, -, -⟩` from `hP1 E m ψ hψ k hk hkm F hPre`. Take `⟨-, hcolL, -⟩` from `hcolPre`.

Take `⟨hgamM, huniqM, -⟩` from `hN0 E m k hk hkm.le`. Take `⟨hgamK, -⟩` from `hN0 E k k hk le_rfl`. Take `⟨hex, hprops⟩` from `hK5e E m k hkm.le`. Take `⟨ιE, hιE⟩` from `hex E`. Take `⟨-, -, -, -, -, -, hrat, -⟩` from `hprops ι hι`.

Establish `hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m, Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0`. Introduce `ρ`. Use `⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩, fun i => rfl⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Function.ne_iff.1 (Subtype.property ρ).1`. Introduce `h0`.

Apply `hc` to reduce the goal to its premises. Establish `h1` using `congrFun h0 ⟨c, lt_trans c.isLt hkm⟩`. Simplify `h1` using `[c.isLt]`. Introduce `i hi`. Simplify using `[show ¬ (i : ℕ) < k by omega]`.

Use `choose lift hlift using hlift`. Establish `hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) = colT ψ k F (ι (ratGL E k (gam ρ) * g))`. Introduce `ρ`. Rewrite using `[hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]`. Establish `hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ))`.

Introduce `i c hic`. Rewrite using `[hιE (gam ρ)]`. Simplify using `only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]`. Rewrite using `[dif_neg (by omega)]`. Take `⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩` from `huniqM _ hBlk`.

Establish `hξ : ξ'' = lift ρ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Establish `hrow` using `congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ`. Simplify using `only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow`.

Establish `hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l = (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l` using `fun l => hp _ _ (Or.inl le_rfl)`. Simplify using `only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hrow`. Rewrite `hrow` using `[(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)]`. Rewrite using `[← hrow, hlift ρ c]`. Simplify using `only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]`.

Distinguish the cases in `hc : (c : ℕ) < k`. Rewrite using `[dif_pos ⟨by show k - 1 < k; omega, hc⟩, dif_pos hc]`. Conclude with `(hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)`. Rewrite using `[dif_neg (fun h => hc h.2), dif_neg hc, Matrix.one_apply, if_neg]`. Introduce `h`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[← h]`. Use `show k - 1 < k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hγ, map_mul, mul_assoc, hcolL p hp, hξ]`.

Establish `hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0`. Establish `h0` using `hFvan k (by omega) le_rfl (ι g)`. Simplify `h0` using `[GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot]`. Establish `hinj : Function.Injective (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)`. Introduce `ρ₁ ρ₂ h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)`. Use `beta_reduce at h1`. Rewrite `h1` using `[hlift, hlift, dif_pos j.isLt, dif_pos j.isLt]`.

Conclude with `h1`. Establish `hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)`. Introduce `t`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises.

Both sides reduce to the same expression. Apply `Fin.ext show ((Subtype.val t).2 : ℕ) = k` to reduce the goal to its premises. Establish `h2` using `Subtype.property t`. Use linear arithmetic over natural numbers and integers. Establish `hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k, (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c`.

Introduce `c hc`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j = c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by`. Use `⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)) ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩` and prove the remaining obligations. Introduce `h0`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `t`. Rewrite using `[hkey t]`. Conclude with `congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩`. Use `⟨ρ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`.

Use `show Subtype.val (lift ρ) (Subtype.val t).1 = c t`. Rewrite using `[hlift, dif_pos (Subtype.property t).1, hρ]`. Conclude with `congrArg c (hkey t).symm`. Establish `hoff : ∀ c : UnipotentBlockColumnIndex m k k → E, c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) → coefF ψ k c F (ι g) = 0`. Introduce `c hc`.

Distinguish the cases in `hc0 : c = 0`. Rewrite using `[hc0]`. Conclude with `hcoef0`. Conclude with `absurd (hsurj c hc0) (fun h => hc h)`. Establish `hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g))` using `per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)`.

Take `⟨-, hP0b, hP0c⟩` from `hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `B hB`. Establish `hB0 : 0 ≤ B` using `le_trans (norm_nonneg _) (hB 0)`. Establish `hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g))) (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g)))` using `hP0b _ _ hper hper`.

Establish `hS` using `(hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g))) (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar`. Establish `hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2` using `norm_avg_le _ _ _ (sq_nonneg B) (fun x => by`. Simplify `mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)` using `[norm_mul, sq]`. Establish `hre` using `((Complex.hasSum_iff _ _).1 hS).1`. Simplify using `only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre`.

Simplify using `only [Complex.mul_conj] at hSle`. Establish `hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 = ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g)))`. Introduce `ρ`. Rewrite using `[hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hre.tsum_eq]`. Conclude with `ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)`. Introduce `hfin`. Establish `hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite`. Use `(hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_` and prove the remaining obligations.

Introduce `c hc`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hc hcoef0`. Take `⟨ρ, rfl⟩` from `hsurj c hc0`.

Use `⟨ρ, ?_, rfl⟩` and prove the remaining obligations. Use `show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0`. Rewrite using `[← hA ρ]`. Conclude with `hc`. Establish `hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g))` using `hP0c _ hper hfin'`.

Establish `hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1`. Unfold `GlobalTheory.CuspGeneric.blkU`. Conclude with `GlobalTheory.CuspGeneric.posU_zero _`. Rewrite `hs` using `[hb0, one_mul]`. Establish `hs2` using `(hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs`.

Use `show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)`. Rewrite using `[← hs2.tsum_eq]`. Conclude with `tsum_congr fun ρ => (hA ρ).symm`.
-/
theorem fourier_column_of : N0 → P0 → P1 → CornerEmbedding → FourierSeriesColumn := by
  intro hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g
  obtain ⟨hFc, hFl, hFlaw, hFvan⟩ := hF
  have hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F := ⟨hFc, hFl, hFlaw⟩
  obtain ⟨hcolPre, hcoef, -, -⟩ := hP1 E m ψ hψ k hk hkm F hPre
  obtain ⟨-, hcolL, -⟩ := hcolPre
  obtain ⟨hgamM, huniqM, -⟩ := hN0 E m k hk hkm.le
  obtain ⟨hgamK, -⟩ := hN0 E k k hk le_rfl
  obtain ⟨hex, hprops⟩ := hK5e E m k hkm.le
  obtain ⟨ιE, hιE⟩ := hex E
  obtain ⟨-, -, -, -, -, -, hrat, -⟩ := hprops ι hι
  have hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m,
      Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0 := by
    intro ρ
    refine ⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩,
      fun i => rfl⟩
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 (Subtype.property ρ).1
      intro h0
      apply hc
      have h1 := congrFun h0 ⟨c, lt_trans c.isLt hkm⟩
      simpa [c.isLt] using h1
    · intro i hi
      simp [show ¬ (i : ℕ) < k by omega]
  choose lift hlift using hlift
  have hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) =
      colT ψ k F (ι (ratGL E k (gam ρ) * g)) := by
    intro ρ
    rw [hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]
    have hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ)) := by
      intro i c hic
      rw [hιE (gam ρ)]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      rw [dif_neg (by omega)]
    obtain ⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩ := huniqM _ hBlk
    have hξ : ξ'' = lift ρ := by
      apply Subtype.ext
      funext c
      have hrow := congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ
      simp only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow
      have hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l =
          (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l := fun l => hp _ _ (Or.inl le_rfl)
      simp only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hrow
      rw [(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)] at hrow
      rw [← hrow, hlift ρ c]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      by_cases hc : (c : ℕ) < k
      · rw [dif_pos ⟨by show k - 1 < k; omega, hc⟩, dif_pos hc]
        exact (hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)
      · rw [dif_neg (fun h => hc h.2), dif_neg hc, Matrix.one_apply, if_neg]
        intro h
        apply hc
        rw [← h]
        show k - 1 < k
        omega
    rw [hγ, map_mul, mul_assoc, hcolL p hp, hξ]
  have hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0 := by
    have h0 := hFvan k (by omega) le_rfl (ι g)
    simpa [GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot] using h0
  have hinj : Function.Injective
      (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) := by
    intro ρ₁ ρ₂ h
    apply Subtype.ext
    funext j
    have h1 := congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m))
      ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)
    beta_reduce at h1
    rw [hlift, hlift, dif_pos j.isLt, dif_pos j.isLt] at h1
    exact h1
  have hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m),
      (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show ((Subtype.val t).2 : ℕ) = k
      have h2 := Subtype.property t
      omega
  have hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k,
      (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c := by
    intro c hc
    obtain ⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j =
        c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ :
          UnipotentBlockColumnIndex m k k) := by
      refine ⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m),
        (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k))
        ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩
      intro h0
      apply hc
      funext t
      rw [hkey t]
      exact congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩
    refine ⟨ρ, ?_⟩
    funext t
    show Subtype.val (lift ρ) (Subtype.val t).1 = c t
    rw [hlift, dif_pos (Subtype.property t).1, hρ]
    exact congrArg c (hkey t).symm
  have hoff : ∀ c : UnipotentBlockColumnIndex m k k → E,
      c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) →
        coefF ψ k c F (ι g) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact hcoef0
    · exact absurd (hsurj c hc0) (fun h => hc h)
  have hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g)) :=
    per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)
  obtain ⟨-, hP0b, hP0c⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)
  refine ⟨?_, ?_⟩
  · intro B hB
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
        (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))) :=
      hP0b _ _ hper hper
    have hS := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
      (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar
    have hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2 :=
      norm_avg_le _ _ _ (sq_nonneg B) (fun x => by
        simpa [norm_mul, sq] using mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)
    have hre := ((Complex.hasSum_iff _ _).1 hS).1
    simp only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre
    simp only [Complex.mul_conj] at hSle
    have hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 =
        ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := by
      intro ρ
      rw [hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]
    calc ∑' ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2
        = ∑' ρ : RowT E k k, ENNReal.ofReal (Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' ρ : RowT E k k, Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Complex.normSq_nonneg _) hre.summable).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          rw [hre.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)
  · intro hfin
    have hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite := by
      refine (hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc hcoef0
      obtain ⟨ρ, rfl⟩ := hsurj c hc0
      refine ⟨ρ, ?_, rfl⟩
      show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0
      rw [← hA ρ]
      exact hc
    have hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g)) :=
      hP0c _ hper hfin'
    have hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1 := by
      unfold GlobalTheory.CuspGeneric.blkU
      exact GlobalTheory.CuspGeneric.posU_zero _
    rw [hb0, one_mul] at hs
    have hs2 := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs
    show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)
    rw [← hs2.tsum_eq]
    exact tsum_congr fun ρ => (hA ρ).symm

end PositivityTheory.AdelicQuotientData

end
