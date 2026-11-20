import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsIbp

namespace ReciprocityTheory.AnForm.A

/- English proof (translation)
The claim follows from `mulVec_one_sub_idempotent_of_split_sum_identity`.
-/
theorem parts_thm : PartsStatement := mulVec_one_sub_idempotent_of_split_sum_identity

/- English proof (translation)
Establish `hsum : ∀ S : Finset (Fin (n + 1)), ∑ k ∈ S.erase 0, A k = ∑ k ∈ S, A k` using `fun S => Finset.sum_erase S hA`. Establish `hle : ∀ S : Finset (Fin (n + 1)), S.card ≤ n + 1` using `fun S => by`. Simplify using `using Finset.card_le_univ S`. Establish `key : ∀ S : Finset (Fin (n + 1)), 0 ∈ S → (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, A k).det + (-1 : ℂ) ^ (n + 1 - (S.erase 0).card) * (∑ k ∈ S.erase 0, A k).det = 0`. Introduce `S h0`.

Establish `h1` using `Finset.card_erase_add_one h0`. Establish `h2` using `hle S`. Establish `he : n + 1 - (S.erase 0).card = (n + 1 - S.card) + 1` using `by omega`. Rewrite using `[hsum, he, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `mdisc`. It suffices to establish `h : ∑ S : Finset (Fin (n + 1)), (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, A k).det = 0 by`. Rewrite using `[h, mul_zero]`. Use `Finset.sum_involution (fun S _ => if (0 : Fin (n + 1)) ∈ S then S.erase 0 else insert 0 S) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `S _`.

Distinguish the cases in `h0 : (0 : Fin (n + 1)) ∈ S`. Simplify using `only [h0, ↓reduceIte]`. Conclude with `key S h0`. Simplify using `only [h0, ↓reduceIte]`. Establish `h3 : (insert 0 S).erase 0 = S` using `Finset.erase_insert h0`.

Establish `h4` using `key (insert 0 S) (Finset.mem_insert_self _ _)`. Rewrite `h4` using `[h3]`. Rewrite using `[add_comm]`. Conclude with `h4`. Introduce `S _ _`.

Distinguish the cases in `h0 : (0 : Fin (n + 1)) ∈ S`. Simplify using `only [h0, ↓reduceIte]`. Introduce `h`. Establish `h5` using `congrArg (fun T => (0 : Fin (n + 1)) ∈ T) h`. Simplify using `[h0] at h5`.

Simplify using `only [h0, ↓reduceIte]`. Introduce `h`. Establish `h5` using `congrArg (fun T => (0 : Fin (n + 1)) ∈ T) h`. Simplify using `[h0] at h5`. Introduce `S _`.

Distinguish the cases in `h0 : (0 : Fin (n + 1)) ∈ S`. Simplify using `[h0, Finset.insert_erase h0]`. Simplify using `[h0, Finset.erase_insert h0]`.
-/
private lemma mdisc_eq_zero_of_zeroth_eq_zero {n : ℕ} (A : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A 0 = 0) : mdisc A = 0 := by
  have hsum : ∀ S : Finset (Fin (n + 1)), ∑ k ∈ S.erase 0, A k = ∑ k ∈ S, A k :=
    fun S => Finset.sum_erase S hA
  have hle : ∀ S : Finset (Fin (n + 1)), S.card ≤ n + 1 := fun S => by
    simpa using Finset.card_le_univ S
  have key : ∀ S : Finset (Fin (n + 1)), 0 ∈ S →
      (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, A k).det +
        (-1 : ℂ) ^ (n + 1 - (S.erase 0).card) * (∑ k ∈ S.erase 0, A k).det = 0 := by
    intro S h0
    have h1 := Finset.card_erase_add_one h0
    have h2 := hle S
    have he : n + 1 - (S.erase 0).card = (n + 1 - S.card) + 1 := by omega
    rw [hsum, he, pow_succ]
    ring
  unfold mdisc
  suffices h : ∑ S : Finset (Fin (n + 1)), (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, A k).det = 0 by
    rw [h, mul_zero]
  refine Finset.sum_involution
    (fun S _ => if (0 : Fin (n + 1)) ∈ S then S.erase 0 else insert 0 S) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro S _
    by_cases h0 : (0 : Fin (n + 1)) ∈ S
    · simp only [h0, ↓reduceIte]
      exact key S h0
    · simp only [h0, ↓reduceIte]
      have h3 : (insert 0 S).erase 0 = S := Finset.erase_insert h0
      have h4 := key (insert 0 S) (Finset.mem_insert_self _ _)
      rw [h3] at h4
      rw [add_comm]
      exact h4
  · intro S _ _
    by_cases h0 : (0 : Fin (n + 1)) ∈ S
    · simp only [h0, ↓reduceIte]
      intro h
      have h5 := congrArg (fun T => (0 : Fin (n + 1)) ∈ T) h
      simp [h0] at h5
    · simp only [h0, ↓reduceIte]
      intro h
      have h5 := congrArg (fun T => (0 : Fin (n + 1)) ∈ T) h
      simp [h0] at h5
  · intro S _
    by_cases h0 : (0 : Fin (n + 1)) ∈ S
    · simp [h0, Finset.insert_erase h0]
    · simp [h0, Finset.erase_insert h0]

/- English proof (translation)
Introduce `n φ v U h`. Establish `h5` using `(parts_thm n φ v (fun _ => 1) U h).2.2.2.2`. Establish `hz : ∀ z, maDens (Fin.cons (fun _ => (1 : ℝ)) φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) z = 0`. Introduce `z`. Establish `hH : hessC (fun _ : Fin (n + 1) → ℂ => (1 : ℝ)) z = 0`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Simplify using `[hessC]`. Unfold `maDens`. Rewrite using `[mdisc_eq_zero_of_zeroth_eq_zero _ ?_]`. Simplify using the standard rewrite rules.

Simplify using `using hH`. Unfold `maInt at h5`. Simplify `h5` using `[hz]`.
-/
theorem massZero_thm : MassZeroStatement := by
  intro n φ v U h
  have h5 := (parts_thm n φ v (fun _ => 1) U h).2.2.2.2
  have hz : ∀ z, maDens (Fin.cons (fun _ => (1 : ℝ)) φ :
      Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) z = 0 := by
    intro z
    have hH : hessC (fun _ : Fin (n + 1) → ℂ => (1 : ℝ)) z = 0 := by
      refine Matrix.ext fun a b => ?_
      simp [hessC]
    unfold maDens
    rw [mdisc_eq_zero_of_zeroth_eq_zero _ ?_]
    · simp
    · simpa using hH
  unfold maInt at h5
  simpa [hz] using h5

/- English proof (translation)
Introduce `n φ U j hU hφ y hy`. Take `⟨Lc, hLc⟩ : ∃ Lc : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ), ∀ y, Lc y = Fin.insertNth (α` from `fun _ => ℂ) j 0 y := by`. Use `⟨ContinuousLinearMap.pi fun i => Fin.insertNth (α := fun _ => (Fin n → ℂ) →L[ℝ] ℂ) j 0 (fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k) i, ?_⟩` and prove the remaining obligations. Introduce `y`. Use function extensionality and compare the values at `m`.

Distinguish the cases in `hm : m = j`. Rewrite using `[hm]`. Simplify using the standard rewrite rules. Take `⟨k, rfl⟩` from `Fin.exists_succAbove_eq hm`. Simplify using the standard rewrite rules.

Establish `hs : ∀ (c : ℂ) (i : Fin n), Lc (c • Pi.single i 1) = c • Pi.single (j.succAbove i) 1`. Introduce `c i`. Rewrite using `[hLc]`. Use function extensionality and compare the values at `m`. Distinguish the cases in `hm : m = j`.

Rewrite using `[hm]`. Simplify using `[Pi.single_apply, (Fin.succAbove_ne j i).symm]`. Take `⟨k, rfl⟩` from `Fin.exists_succAbove_eq hm`. Simplify using `[Pi.single_apply]`. Establish `hs1 : ∀ i : Fin n, Lc (Pi.single i 1) = Pi.single (j.succAbove i) 1`.

Introduce `i`. Simplify using `using hs 1 i`. Establish `hfun : (fun y' => φ (Fin.insertNth (α` using `fun _ => ℂ) j 0 y')) = φ ∘ Lc := by`. Use function extensionality and compare the values at `y'`. Simplify using `only [Function.comp_apply, hLc]`.

Rewrite using `[hfun, ← hLc y]`. Rewrite `hy` using `[← hLc y]`. Establish `hφa : ∀ x ∈ U, ContDiffAt ℝ 2 φ x` using `fun x hx => hφ.contDiffAt (hU.mem_nhds hx)`. Establish `hev : fderiv ℝ (φ ∘ Lc) =ᶠ[nhds y] fun y' => (fderiv ℝ φ (Lc y')).comp Lc`. Establish `hU' : ∀ᶠ y' in nhds y, Lc y' ∈ U` using `Lc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hy)`.

Use `filter_upwards [hU'] with y' hy'`. Apply the tactic sequence `rw [fderiv_comp y' ((hφa _ hy').differentiableAt (by first | exact one_le_two | exact two_ne_zero | norm_num)) Lc.differentiableAt, Lc.fderiv]`. Apply the tactic sequence `have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (Lc y) := ((hφa _ hy).fderiv_right (m := 1) (by first | exact le_rfl | exact one_add_one_eq_two.le | norm_num)).differentiableAt (by first | exact le_rfl | exact one_ne_zero)`. Establish `hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (Lc y')) y` using `hd1.comp y Lc.differentiableAt`. Establish `hH : ∀ v w, fderiv ℝ (fderiv ℝ (φ ∘ Lc)) y v w = fderiv ℝ (fderiv ℝ φ) (Lc y) (Lc v) (Lc w)`.

Introduce `v w`. Rewrite using `[hev.fderiv_eq, fderiv_clm_comp (c := fun y' => fderiv ℝ φ (Lc y')) (d := fun _ => Lc) hc (differentiableAt_const Lc), fderiv_comp' y hd1 Lc.differentiableAt, Lc.fderiv]`. Simplify using the standard rewrite rules. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Simplify using `only [hessC, Matrix.submatrix_apply, hH, hs, hs1]`.
-/
theorem hessCRestrict_thm : HessCRestrictStatement := by
  intro n φ U j hU hφ y hy
  obtain ⟨Lc, hLc⟩ : ∃ Lc : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ),
      ∀ y, Lc y = Fin.insertNth (α := fun _ => ℂ) j 0 y := by
    refine ⟨ContinuousLinearMap.pi fun i => Fin.insertNth
      (α := fun _ => (Fin n → ℂ) →L[ℝ] ℂ) j 0
      (fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k) i, ?_⟩
    intro y
    funext m
    by_cases hm : m = j
    · rw [hm]; simp
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp
  have hs : ∀ (c : ℂ) (i : Fin n), Lc (c • Pi.single i 1) = c • Pi.single (j.succAbove i) 1 := by
    intro c i
    rw [hLc]
    funext m
    by_cases hm : m = j
    · rw [hm]; simp [Pi.single_apply, (Fin.succAbove_ne j i).symm]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp [Pi.single_apply]
  have hs1 : ∀ i : Fin n, Lc (Pi.single i 1) = Pi.single (j.succAbove i) 1 := by
    intro i; simpa using hs 1 i
  have hfun : (fun y' => φ (Fin.insertNth (α := fun _ => ℂ) j 0 y')) = φ ∘ Lc := by
    funext y'; simp only [Function.comp_apply, hLc]
  rw [hfun, ← hLc y]
  rw [← hLc y] at hy
  have hφa : ∀ x ∈ U, ContDiffAt ℝ 2 φ x := fun x hx => hφ.contDiffAt (hU.mem_nhds hx)
  have hev : fderiv ℝ (φ ∘ Lc) =ᶠ[nhds y] fun y' => (fderiv ℝ φ (Lc y')).comp Lc := by
    have hU' : ∀ᶠ y' in nhds y, Lc y' ∈ U :=
      Lc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
    filter_upwards [hU'] with y' hy'
    rw [fderiv_comp y' ((hφa _ hy').differentiableAt
      (by first | exact one_le_two | exact two_ne_zero | norm_num)) Lc.differentiableAt,
      Lc.fderiv]
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (Lc y) :=
    ((hφa _ hy).fderiv_right (m := 1)
      (by first | exact le_rfl | exact one_add_one_eq_two.le | norm_num)).differentiableAt
      (by first | exact le_rfl | exact one_ne_zero)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (Lc y')) y :=
    hd1.comp y Lc.differentiableAt
  have hH : ∀ v w, fderiv ℝ (fderiv ℝ (φ ∘ Lc)) y v w =
      fderiv ℝ (fderiv ℝ φ) (Lc y) (Lc v) (Lc w) := by
    intro v w
    rw [hev.fderiv_eq, fderiv_clm_comp (c := fun y' => fderiv ℝ φ (Lc y')) (d := fun _ => Lc) hc
      (differentiableAt_const Lc), fderiv_comp' y hd1 Lc.differentiableAt, Lc.fderiv]
    simp
  refine Matrix.ext fun a b => ?_
  simp only [hessC, Matrix.submatrix_apply, hH, hs, hs1]

end ReciprocityTheory.AnForm.A
