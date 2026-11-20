import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula

noncomputable section

namespace LevelTowerAlt.Comparison₂

open MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot

/- English proof (translation)
Take `⟨⟨α, γ, hfα, hgγ, hdeg⟩, hU⟩` from `hIso`. Establish `hfP : f ∉ P` using `hU.1`. Establish `hgP : g ∉ P` using `hU.2.1`. Use `set M' : HermLine ι := fsOfDeg γ with hM'def`. Use `set M : HermLine ι := twist M' A B with hMdef`.

Establish `hM' : IsSmoothHerm M'` using `isSmoothHerm_fsOfDeg γ`. Establish `hM : IsSmoothHerm M` using `isSmoothHerm_twist hM' hA hB`. Establish `hMa : ∀ k, M.a k = α k`. Introduce `k`. Establish `h` using `hdeg k`.

Establish `e1 : M.a k = (γ k : ℤ) + A.a k + -B.a k` using `rfl`. Rewrite using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM'a : ∀ k, M'.a k = γ k` using `fun _ => rfl`. Establish `a1` using `hI.2.1 P e L M B hP hL hM hB`.

Establish `a2` using `hI.2.1 P e L M' A hP hL hM' hA`. Establish `ht : M.tensor B = M'.tensor A` using `twist_tensor (fun z hz => fsOfDeg_h_of_notMem γ hz) A B`. Rewrite `a1` using `[ht]`. Establish `r1` using `hI.2.2 P e L M f α hP hL hM hMa hfα hfP`. Establish `r2` using `hI.2.2 P e L M' g γ hP hL hM' hM'a hgγ hgP`.

Rewrite `r1`, `r2` using `[recR_eq]`. Establish `hc` using `GlobalTheory.T.unit_ratio_same_divisor_multiplicities K ι P f g hU`. Establish `hcyc : cycR I P L f = cycR I P L g`. Unfold `cycR`. Use `finsum_mem_congr hc.1 fun W hW => ?_` and prove the remaining obligations.

Rewrite using `[hc.2 W (hc.1 ▸ hW)]`. Establish `hsf : IsSectionOn P M f` using `⟨α, hMa, hfα, hfP⟩`. Establish `hsg : IsSectionOn P M' g` using `⟨γ, hM'a, hgγ, hgP⟩`. Rewrite `r1` using `[arInt_eq_mInt hBr hG R hP hL hM hsf]`. Rewrite `r2` using `[arInt_eq_mInt hBr hG R hP hL hM' hsg]`.

Establish `hpot : ∀ i, IsPotential R.A (potOf R (L i))` using `fun i => potOf_isPotential R (L i) (hL i)`. Establish `hlin` using `mIntLinear R.A (fun j => potOf R (L j)) hpot (-1) (fun x => logNorm M' g (R.lift x x)) (fun x => logNorm M f (R.lift x x)) (brIntegrable R L M' g hP hL hM' hsg) (brIntegrable R L M f hP hL hM hsf)`. Take `⟨Ψ, hΨ⟩` from `hG K ι P e hP`. Establish `hw' : mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) = mInt R.A (fun j => potOf R (L j)) (fun x => -1 * logNorm M' g (R.lift x x) + logNorm M f (R.lift x x))`. Use `mInt_congr_null _ _ fun j => ?_` and prove the remaining obligations.

Use `measure_mono_null ?_ (measure_union_null (zeros_null R Ψ hP hΨ hfα hfP j) (zeros_null R Ψ hP hΨ hgγ hgP j))` and prove the remaining obligations. Introduce and unpack `y ⟨hyt, hy⟩`. Assume the negation of the conclusion as `hcon`. Establish `hnf : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) f ≠ 0` using `fun h => hcon (Or.inl ⟨hyt, h⟩)`. Establish `hng : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) g ≠ 0` using `fun h => hcon (Or.inr ⟨hyt, h⟩)`.

Establish `hmem` using `R.mem ((R.A.chart j).symm y) _ (R.mem_U ((R.A.chart j).symm y))`. Apply `hy` to reduce the goal to its premises. Establish `hd` using `hw _ hmem g f (by rw [mul_comm, sub_self]; exact P.zero_mem) hng`. Use `logNorm_sub_eq (M := M') (A := A) (B := B) (show _ ∈ blockSet ι from hmem.1) hnf hng` as an intermediate fact. Use `show w _ = -1 * logNorm M' g _ + logNorm M f _`.

Rewrite using `[hd, ← this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw', hlin]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_coord₂ (hBr : ResBridgeStatement) (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hIso : IsLineIso P A.a B.a f g) (hw : IsDefectOn P (mcPts P) f g A B w) :
    I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) =
      -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  obtain ⟨⟨α, γ, hfα, hgγ, hdeg⟩, hU⟩ := hIso
  have hfP : f ∉ P := hU.1
  have hgP : g ∉ P := hU.2.1
  set M' : HermLine ι := fsOfDeg γ with hM'def
  set M : HermLine ι := twist M' A B with hMdef
  have hM' : IsSmoothHerm M' := isSmoothHerm_fsOfDeg γ
  have hM : IsSmoothHerm M := isSmoothHerm_twist hM' hA hB
  have hMa : ∀ k, M.a k = α k := by
    intro k
    have h := hdeg k
    have e1 : M.a k = (γ k : ℤ) + A.a k + -B.a k := rfl
    rw [e1]
    linarith
  have hM'a : ∀ k, M'.a k = γ k := fun _ => rfl

  have a1 := hI.2.1 P e L M B hP hL hM hB
  have a2 := hI.2.1 P e L M' A hP hL hM' hA
  have ht : M.tensor B = M'.tensor A := twist_tensor (fun z hz => fsOfDeg_h_of_notMem γ hz) A B
  rw [ht] at a1

  have r1 := hI.2.2 P e L M f α hP hL hM hMa hfα hfP
  have r2 := hI.2.2 P e L M' g γ hP hL hM' hM'a hgγ hgP
  rw [recR_eq] at r1 r2

  have hc := GlobalTheory.T.unit_ratio_same_divisor_multiplicities K ι P f g hU
  have hcyc : cycR I P L f = cycR I P L g := by
    unfold cycR
    refine finsum_mem_congr hc.1 fun W hW => ?_
    rw [hc.2 W (hc.1 ▸ hW)]

  have hsf : IsSectionOn P M f := ⟨α, hMa, hfα, hfP⟩
  have hsg : IsSectionOn P M' g := ⟨γ, hM'a, hgγ, hgP⟩
  rw [arInt_eq_mInt hBr hG R hP hL hM hsf] at r1
  rw [arInt_eq_mInt hBr hG R hP hL hM' hsg] at r2
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => potOf_isPotential R (L i) (hL i)
  have hlin := mIntLinear R.A (fun j => potOf R (L j)) hpot (-1)
    (fun x => logNorm M' g (R.lift x x)) (fun x => logNorm M f (R.lift x x))
    (brIntegrable R L M' g hP hL hM' hsg) (brIntegrable R L M f hP hL hM hsf)
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  have hw' : mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) =
      mInt R.A (fun j => potOf R (L j))
        (fun x => -1 * logNorm M' g (R.lift x x) + logNorm M f (R.lift x x)) := by
    refine mInt_congr_null _ _ fun j => ?_
    refine measure_mono_null ?_ (measure_union_null (zeros_null R Ψ hP hΨ hfα hfP j)
      (zeros_null R Ψ hP hΨ hgγ hgP j))
    rintro y ⟨hyt, hy⟩
    by_contra hcon
    have hnf : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) f ≠ 0 :=
      fun h => hcon (Or.inl ⟨hyt, h⟩)
    have hng : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) g ≠ 0 :=
      fun h => hcon (Or.inr ⟨hyt, h⟩)
    have hmem := R.mem ((R.A.chart j).symm y) _ (R.mem_U ((R.A.chart j).symm y))
    apply hy
    have hd := hw _ hmem g f (by rw [mul_comm, sub_self]; exact P.zero_mem) hng
    have := logNorm_sub_eq (M := M') (A := A) (B := B) (show _ ∈ blockSet ι from hmem.1) hnf hng
    show w _ = -1 * logNorm M' g _ + logNorm M f _
    rw [hd, ← this]
    ring
  rw [hw', hlin]
  linarith

end LevelTowerAlt.Comparison₂
