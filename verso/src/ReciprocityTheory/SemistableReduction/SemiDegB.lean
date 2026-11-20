import ReciprocityTheory.SemistableReduction.SemiDegBB

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

/- English proof (translation)
Introduce `K _ _ r k H B b b' hH hB hb hb'`. Take `⟨hbB, hbli, hbsp⟩` from `hb`. Take `⟨hb'B, hb'li, hb'sp⟩` from `hb'`. Use `set P := Submodule.span (𝓞 K) (Set.range b) with hP`. Use `set P' := Submodule.span (𝓞 K) (Set.range b') with hP'`.

Take `⟨D, hD, hDB⟩` from `exists_smul_le_span b B hB hbsp`. Establish `hcoef : ∀ j, ∃ c : Fin k → 𝓞 K, ∑ i, c i • b i = D • b' j` using `fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hDB _ (hb'B j))`. Use `choose m hm using hcoef`. Use `set M : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of fun i j => m j i with hMdef`. Use `set Dm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.diagonal fun _ => D with hDm`.

Establish `hcM : (fun j => ∑ i, M i j • b i) = fun j => D • b' j`. Use function extensionality and compare the values at `j`. Conclude with `hm j`. Establish `hcD : (fun j => ∑ i, Dm i j • b' i) = fun j => D • b' j` using `comb_diagonal b' D`. Use `set NK := M.map (algebraMap (𝓞 K) K) with hNK`.

Use `set DK := Dm.map (algebraMap (𝓞 K) K) with hDK`. Establish `hcMK : (fun j => ∑ i, NK i j • b i) = fun j => D • b' j`. Rewrite using `[← hcM]`. Use function extensionality and compare the values at `j`. Simplify using `[NK, algebraMap_smul]`.

Establish `hcDK : (fun j => ∑ i, DK i j • b' i) = fun j => D • b' j`. Rewrite using `[← hcD]`. Use function extensionality and compare the values at `j`. Simplify using `[DK, algebraMap_smul]`. Establish `hNKdet : NK.det = algebraMap (𝓞 K) K M.det` using `(RingHom.map_det _ M).symm`.

Establish `hDKdet : DK.det = algebraMap (𝓞 K) K Dm.det` using `(RingHom.map_det _ Dm).symm`. Establish `hgc : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det = ((Complex.normSq (σ NK.det) : ℝ) : ℂ) * (gramC (H σ) σ b).det` using `fun σ => by`. Rewrite using `[← hcMK]`. Conclude with `det_gramC_comb _ _ _ _`. Establish `hgc' : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det = ((Complex.normSq (σ DK.det) : ℝ) : ℂ) * (gramC (H σ) σ b').det` using `fun σ => by`.

Rewrite using `[← hcDK]`. Conclude with `det_gramC_comb _ _ _ _`. Establish `hpos : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b).det.re` using `fun σ => gramC_det_re_pos (H σ) σ b (hH σ) hbli`. Establish `hpos' : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b').det.re` using `fun σ => gramC_det_re_pos (H σ) σ b' (hH σ) hb'li`. Establish `hDmdet : Dm.det ≠ 0`.

Simplify using `[Dm, Matrix.det_diagonal, hD]`. Establish `hinj` using `FaithfulSMul.algebraMap_injective (𝓞 K) K`. Establish `hDKne : DK.det ≠ 0`. Rewrite using `[hDKdet, ← map_zero (algebraMap (𝓞 K) K)]`. Conclude with `hinj.ne hDmdet`.

Establish `hre : ∀ σ : K →+* ℂ, Complex.normSq (σ NK.det) * (gramC (H σ) σ b).det.re = Complex.normSq (σ DK.det) * (gramC (H σ) σ b').det.re` using `fun σ => by`. Use `congrArg Complex.re ((hgc σ).symm.trans (hgc' σ))` as an intermediate fact. Simplify `this` using `[Complex.re_ofReal_mul]`. Establish `hNKne : NK.det ≠ 0`. Introduce `h0`.

Establish `h` using `hre (Classical.arbitrary (K →+* ℂ))`. Rewrite `h` using `[h0, map_zero, map_zero, zero_mul]`. Establish `h1 : 0 < Complex.normSq ((Classical.arbitrary (K →+* ℂ)) DK.det)` using `Complex.normSq_pos.mpr (by simpa using hDKne)`. Establish `h2` using `hpos' (Classical.arbitrary (K →+* ℂ))`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hMdet : M.det ≠ 0`. Introduce `h0`. Apply `hNKne` to reduce the goal to its premises. Rewrite using `[hNKdet, h0, map_zero]`. Use `set C := Submodule.span (𝓞 K) (Set.range (fun j => D • b' j)) with hC`.

Establish `hIdx1` using `relIndex_span_comb b hbli M hMdet`. Rewrite `hIdx1` using `[hcM]`. Establish `hIdx2` using `relIndex_span_comb b' hb'li Dm hDmdet`. Rewrite `hIdx2` using `[hcD]`. Establish `hPB : P ≤ B` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)`.

Establish `hP'B : P' ≤ B` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr hb'B)`. Establish `hCP : C ≤ P` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hDB _ (hb'B j))`. Establish `hCP' : C ≤ P'` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => Submodule.smul_mem _ D (Submodule.subset_span ⟨j, rfl⟩))`. Establish `mul1` using `AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P.toAddSubgroup B.toAddSubgroup hCP hPB`. Establish `mul2` using `AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P'.toAddSubgroup B.toAddSubgroup hCP' hP'B`.

Establish `hI` using `relIndex_span_ne_zero b hbli B hbB D hD hDB`. Establish `e1 : ((Algebra.norm ℤ M.det : ℤ) : ℝ) = ((Algebra.norm ℚ NK.det : ℚ) : ℝ)`. Use `congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int M.det)` as an intermediate fact. Simplify using `only [Rat.cast_intCast] at this`. Rewrite using `[hNKdet]`.

Use `this using 3` and compare the differences between its conclusion and the goal. Establish `e2 : ((Algebra.norm ℤ Dm.det : ℤ) : ℝ) = ((Algebra.norm ℚ DK.det : ℚ) : ℝ)`. Use `congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int Dm.det)` as an intermediate fact. Simplify using `only [Rat.cast_intCast] at this`. Rewrite using `[hDKdet]`.

Use `this using 3` and compare the differences between its conclusion and the goal. Establish `hcP : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) = |((Algebra.norm ℚ NK.det : ℚ) : ℝ)|`. Use `congrArg (fun z : ℤ => (z : ℝ)) hIdx1` as an intermediate fact. Simplify using `only [Int.cast_natCast, Int.cast_abs] at this`. Rewrite using `[this, e1]`.

Establish `hcP' : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) = |((Algebra.norm ℚ DK.det : ℚ) : ℝ)|`. Use `congrArg (fun z : ℤ => (z : ℝ)) hIdx2` as an intermediate fact. Simplify using `only [Int.cast_natCast, Int.cast_abs] at this`. Rewrite using `[this, e2]`. Establish `hnM : ((Algebra.norm ℚ NK.det : ℚ) : ℝ) ≠ 0` using `Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hNKne)`.

Establish `hnD : ((Algebra.norm ℚ DK.det : ℚ) : ℝ) ≠ 0` using `Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDKne)`. Establish `hmulR : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) * ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) = ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) * ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ)`. Conclude with `mul1.trans mul2.symm` after adjusting the coercions. Establish `hcPne : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) ≠ 0`. Rewrite using `[hcP]`.

Conclude with `abs_ne_zero.mpr hnM`. Establish `hcP'ne : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) ≠ 0`. Rewrite using `[hcP']`. Conclude with `abs_ne_zero.mpr hnD`. Establish `hIne : ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hI`.

Establish `hI'ne : ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0`. Introduce `h0`. Rewrite `hmulR` using `[h0, mul_zero]`. Conclude with `mul_ne_zero hcPne hIne hmulR`. Establish `hlog : Real.log ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) + Real.log ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) = Real.log ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) + Real.log ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ)`.

Rewrite using `[← Real.log_mul hcPne hIne, ← Real.log_mul hcP'ne hI'ne, hmulR]`. Rewrite `hlog` using `[hcP, hcP']`. Establish `hsum : ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ NK.det)) + Real.log (gramC (H σ) σ b).det.re) = ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ DK.det)) + Real.log (gramC (H σ) σ b').det.re)`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `h1 : Complex.normSq (σ NK.det) ≠ 0` using `(Complex.normSq_pos.mpr (by simpa using hNKne)).ne'`.

Establish `h2 : Complex.normSq (σ DK.det) ≠ 0` using `(Complex.normSq_pos.mpr (by simpa using hDKne)).ne'`. Rewrite using `[← Real.log_mul h1 (hpos σ).ne', ← Real.log_mul h2 (hpos' σ).ne', hre σ]`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_normSq _ hNKne, sum_log_normSq _ hDKne]`. Simplify using `only [latDeg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem latDegBasis_holds : LatDegBasisStatement := by
  intro K _ _ r k H B b b' hH hB hb hb'
  obtain ⟨hbB, hbli, hbsp⟩ := hb
  obtain ⟨hb'B, hb'li, hb'sp⟩ := hb'
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  set P' := Submodule.span (𝓞 K) (Set.range b') with hP'
  obtain ⟨D, hD, hDB⟩ := exists_smul_le_span b B hB hbsp
  have hcoef : ∀ j, ∃ c : Fin k → 𝓞 K, ∑ i, c i • b i = D • b' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hDB _ (hb'B j))
  choose m hm using hcoef
  set M : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of fun i j => m j i with hMdef
  set Dm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.diagonal fun _ => D with hDm
  have hcM : (fun j => ∑ i, M i j • b i) = fun j => D • b' j := by
    funext j
    exact hm j
  have hcD : (fun j => ∑ i, Dm i j • b' i) = fun j => D • b' j := comb_diagonal b' D
  set NK := M.map (algebraMap (𝓞 K) K) with hNK
  set DK := Dm.map (algebraMap (𝓞 K) K) with hDK
  have hcMK : (fun j => ∑ i, NK i j • b i) = fun j => D • b' j := by
    rw [← hcM]
    funext j
    simp [NK, algebraMap_smul]
  have hcDK : (fun j => ∑ i, DK i j • b' i) = fun j => D • b' j := by
    rw [← hcD]
    funext j
    simp [DK, algebraMap_smul]
  have hNKdet : NK.det = algebraMap (𝓞 K) K M.det := (RingHom.map_det _ M).symm
  have hDKdet : DK.det = algebraMap (𝓞 K) K Dm.det := (RingHom.map_det _ Dm).symm
  have hgc : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ NK.det) : ℝ) : ℂ) * (gramC (H σ) σ b).det := fun σ => by
    rw [← hcMK]
    exact det_gramC_comb _ _ _ _
  have hgc' : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ DK.det) : ℝ) : ℂ) * (gramC (H σ) σ b').det := fun σ => by
    rw [← hcDK]
    exact det_gramC_comb _ _ _ _
  have hpos : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b).det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b (hH σ) hbli
  have hpos' : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b').det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b' (hH σ) hb'li
  have hDmdet : Dm.det ≠ 0 := by
    simp [Dm, Matrix.det_diagonal, hD]
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hDKne : DK.det ≠ 0 := by
    rw [hDKdet, ← map_zero (algebraMap (𝓞 K) K)]
    exact hinj.ne hDmdet
  have hre : ∀ σ : K →+* ℂ, Complex.normSq (σ NK.det) * (gramC (H σ) σ b).det.re =
      Complex.normSq (σ DK.det) * (gramC (H σ) σ b').det.re := fun σ => by
    have := congrArg Complex.re ((hgc σ).symm.trans (hgc' σ))
    simpa [Complex.re_ofReal_mul] using this
  have hNKne : NK.det ≠ 0 := by
    intro h0
    have h := hre (Classical.arbitrary (K →+* ℂ))
    rw [h0, map_zero, map_zero, zero_mul] at h
    have h1 : 0 < Complex.normSq ((Classical.arbitrary (K →+* ℂ)) DK.det) :=
      Complex.normSq_pos.mpr (by simpa using hDKne)
    have h2 := hpos' (Classical.arbitrary (K →+* ℂ))
    nlinarith
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hNKne
    rw [hNKdet, h0, map_zero]
  set C := Submodule.span (𝓞 K) (Set.range (fun j => D • b' j)) with hC
  have hIdx1 := relIndex_span_comb b hbli M hMdet
  rw [hcM] at hIdx1
  have hIdx2 := relIndex_span_comb b' hb'li Dm hDmdet
  rw [hcD] at hIdx2
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hP'B : P' ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hb'B)
  have hCP : C ≤ P := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hDB _ (hb'B j))
  have hCP' : C ≤ P' := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
    Submodule.smul_mem _ D (Submodule.subset_span ⟨j, rfl⟩))
  have mul1 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P.toAddSubgroup B.toAddSubgroup
    hCP hPB
  have mul2 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P'.toAddSubgroup B.toAddSubgroup
    hCP' hP'B
  have hI := relIndex_span_ne_zero b hbli B hbB D hD hDB
  have e1 : ((Algebra.norm ℤ M.det : ℤ) : ℝ) = ((Algebra.norm ℚ NK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int M.det)
    simp only [Rat.cast_intCast] at this
    rw [hNKdet]
    convert this using 3
  have e2 : ((Algebra.norm ℤ Dm.det : ℤ) : ℝ) = ((Algebra.norm ℚ DK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int Dm.det)
    simp only [Rat.cast_intCast] at this
    rw [hDKdet]
    convert this using 3
  have hcP : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ NK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx1
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e1]
  have hcP' : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ DK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx2
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e2]
  have hnM : ((Algebra.norm ℚ NK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hNKne)
  have hnD : ((Algebra.norm ℚ DK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDKne)
  have hmulR : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) *
      ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) *
      ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    exact_mod_cast mul1.trans mul2.symm
  have hcPne : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP]
    exact abs_ne_zero.mpr hnM
  have hcP'ne : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP']
    exact abs_ne_zero.mpr hnD
  have hIne : ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  have hI'ne : ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulR
    exact mul_ne_zero hcPne hIne hmulR
  have hlog : Real.log ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      Real.log ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    rw [← Real.log_mul hcPne hIne, ← Real.log_mul hcP'ne hI'ne, hmulR]
  rw [hcP, hcP'] at hlog
  have hsum : ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ NK.det)) +
      Real.log (gramC (H σ) σ b).det.re) = ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ DK.det)) +
      Real.log (gramC (H σ) σ b').det.re) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : Complex.normSq (σ NK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hNKne)).ne'
    have h2 : Complex.normSq (σ DK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hDKne)).ne'
    rw [← Real.log_mul h1 (hpos σ).ne', ← Real.log_mul h2 (hpos' σ).ne', hre σ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_normSq _ hNKne,
    sum_log_normSq _ hDKne] at hsum
  simp only [latDeg]
  linarith

end ReciprocityTheory.MultiplicativeHeights
