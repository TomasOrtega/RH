import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a0, h1, h2⟩ : ∃ a0 : ℝ, (∀ a ∈ A, a ≤ a0) ∧ ∀ b ∈ B, a0 < b := by`. Break down `A.eq_empty_or_nonempty with rfl | hne` into its components or cases. Take `⟨m, hm⟩` from `hB.bddBelow`. Conclude with `⟨m - 1, by simp, fun b hb => by linarith [hm hb]⟩`. Take `⟨a0, ha0, hmax⟩` from `Set.exists_max_image A id hA hne`.

Conclude with `⟨a0, hmax, h a0 ha0⟩`. Choose the witnesses or unpack the hypotheses as in `⟨b0, h3, h4⟩ : ∃ b0 : ℝ, a0 < b0 ∧ ∀ b ∈ B, b0 ≤ b := by`. Break down `B.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨a0 + 1, by linarith, by simp⟩`. Take `⟨b0, hb0, hmin⟩` from `Set.exists_min_image B id hB hne`.

Conclude with `⟨b0, h2 b0 hb0, hmin⟩`. Take `⟨x, hx, h5, h6⟩` from `hD a0 b0 h3`. Conclude with `⟨x, hx, fun a ha => lt_of_le_of_lt (h1 a ha) h5, fun b hb => lt_of_lt_of_le h6 (h4 b hb)⟩`.
-/
private theorem between_fin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b)
    (A B : Set ℝ) (hA : A.Finite) (hB : B.Finite) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x ∈ D, (∀ a ∈ A, a < x) ∧ ∀ b ∈ B, x < b := by
  obtain ⟨a0, h1, h2⟩ : ∃ a0 : ℝ, (∀ a ∈ A, a ≤ a0) ∧ ∀ b ∈ B, a0 < b := by
    rcases A.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨m, hm⟩ := hB.bddBelow
      exact ⟨m - 1, by simp, fun b hb => by linarith [hm hb]⟩
    · obtain ⟨a0, ha0, hmax⟩ := Set.exists_max_image A id hA hne
      exact ⟨a0, hmax, h a0 ha0⟩
  obtain ⟨b0, h3, h4⟩ : ∃ b0 : ℝ, a0 < b0 ∧ ∀ b ∈ B, b0 ≤ b := by
    rcases B.eq_empty_or_nonempty with rfl | hne
    · exact ⟨a0 + 1, by linarith, by simp⟩
    · obtain ⟨b0, hb0, hmin⟩ := Set.exists_min_image B id hB hne
      exact ⟨b0, h2 b0 hb0, hmin⟩
  obtain ⟨x, hx, h5, h6⟩ := hD a0 b0 h3
  exact ⟨x, hx, fun a ha => lt_of_le_of_lt (h1 a ha) h5, fun b hb => lt_of_lt_of_le h6 (h4 b hb)⟩

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1` from `⟨(k - 1).toNat, by omega⟩`. Use `clear hk`. Proceed by induction on `n with`. Consider the case `zero => simpa using hv`. Consider the case `succ n ih`.

Establish `: (((n + 1 : ℕ) : ℤ) + 1) • v = ((n : ℤ) + 1) • v + v` using `by push_cast; rw [add_smul ((n : ℤ) + 1) 1 v, one_smul]`. Rewrite using `[this]`. Conclude with `hH _ ih _ hv`.
-/
private theorem zsmul_mem_pos {M : Type} [AddCommGroup M] (H : Set M)
    (hH : ∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) (v : M) (hv : v ∈ H) (k : ℤ) (hk : 0 < k) : k • v ∈ H := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  clear hk
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have : (((n + 1 : ℕ) : ℤ) + 1) • v = ((n : ℤ) + 1) • v + v := by
      push_cast; rw [add_smul ((n : ℤ) + 1) 1 v, one_smul]
    rw [this]; exact hH _ ih _ hv

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `F H _ hFH _ h0`. Use `⟨Fin.elim0, fun i => i.elim0, fun v hv => ?_⟩` and prove the remaining obligations.

Simplify using `using h0 v (hFH hv) (Subsingleton.elim _ _)`. Consider the case `succ d ih`. Introduce `F H hF hFH hadd h0`. Set `π : (Fin (d + 1) → ℤ) × ℝ → (Fin d → ℤ) × ℝ` to `fun v => (fun i => v.1 i.succ, v.2)`. Set `cmb : ((Fin (d + 1) → ℤ) × ℝ) × ((Fin (d + 1) → ℤ) × ℝ) → (Fin (d + 1) → ℤ) × ℝ` to `fun p => (-p.2.1 0) • p.1 + (p.1.1 0) • p.2`.

Set `G : Set ((Fin (d + 1) → ℤ) × ℝ)` to `{v ∈ F | v.1 0 = 0} ∪ cmb '' ({v ∈ F | 0 < v.1 0} ×ˢ {v ∈ F | v.1 0 < 0})`. Establish `hG : G.Finite` using `(hF.subset (Set.sep_subset _ _)).union (((hF.subset (Set.sep_subset _ _)).prod (hF.subset (Set.sep_subset _ _))).image _)`. Establish `hGH : G ⊆ {v ∈ H | v.1 0 = 0}`. Introduce and unpack `v (⟨hv, hv0⟩ | ⟨⟨s, t⟩, ⟨⟨hs, hs0⟩, ht, ht0⟩, rfl⟩)`. Conclude with `⟨hFH hv, hv0⟩`.

Use `⟨hadd _ (zsmul_mem_pos H hadd _ (hFH hs) _ (neg_pos.2 ht0)) _ (zsmul_mem_pos H hadd _ (hFH ht) _ hs0), ?_⟩` and prove the remaining obligations. Simplify using `only [cmb, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨φ, hφD, hφ⟩` from `ih (π '' G) (π '' {v ∈ H | v.1 0 = 0}) (hG.image _) (Set.image_mono hGH) (by`. Introduce and unpack `_ ⟨u, ⟨hu, hu0⟩, rfl⟩ _ ⟨v, ⟨hv, hv0⟩, rfl⟩`.

Conclude with `⟨u + v, ⟨hadd u hu v hv, by simp [hu0, hv0]⟩, rfl⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨u, ⟨hu, hu0⟩, rfl⟩ h`. Use `h0 u hu (funext fun i => ?_)` and prove the remaining obligations. Use `Fin.cases hu0 (fun j => ?_) i` and prove the remaining obligations.

Conclude with `congrFun h j)`. Set `r : (Fin (d + 1) → ℤ) × ℝ → ℝ` to `fun v => ∑ i : Fin d, (v.1 i.succ : ℝ) * φ i + v.2`. Establish `hr : ∀ v ∈ G, r v < 0` using `fun v hv => hφ (π v) ⟨v, hv, rfl⟩`. Establish `hrc : ∀ s t, r (cmb (s, t)) = (-(t.1 0 : ℝ)) * r s + (s.1 0 : ℝ) * r t`. Introduce `s t`.

Simplify using `only [r, cmb, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]`. Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Simplify using `only [add_mul, Finset.sum_add_distrib, mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨x, hxD, hlo, hhi⟩` from `between_fin D hD ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | v.1 0 < 0}) ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | 0 < v.1 0}) ((hF.subset (Set.sep_subset _ _)).image _) ((hF.subset (Set.sep_subset _ _)).image _) (by`. Introduce and unpack `_ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩`. Establish `h1` using `hr _ (Or.inr ⟨(s, t), ⟨hs, ht⟩, rfl⟩)`. Rewrite `h1` using `[hrc]`. Establish `hs0 : (0 : ℝ) < s.1 0` using `by exact_mod_cast hs.2`.

Establish `ht0 : (t.1 0 : ℝ) < 0` using `by exact_mod_cast ht.2`. Use `show -r t / (t.1 0 : ℝ) < -r s / (s.1 0 : ℝ)`. Rewrite using `[← neg_div_neg_eq, div_lt_div_iff₀ (neg_pos.2 ht0) hs0]`. Use the proof step `linarith)`. Use `⟨Fin.cons x φ, fun i => Fin.cases hxD hφD i, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `hsum : ∑ i, (v.1 i : ℝ) * (Fin.cons x φ : Fin (d + 1) → ℝ) i + v.2 = (v.1 0 : ℝ) * x + r v`. Simplify using `only [r, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]`. Rewrite using `[hsum]`. Break down `lt_trichotomy (v.1 0) 0 with h | h | h` into its components or cases. Establish `h1` using `hlo _ ⟨v, ⟨hv, h⟩, rfl⟩`.

Establish `h2 : (v.1 0 : ℝ) < 0` using `by exact_mod_cast h`. Rewrite `h1` using `[div_lt_iff_of_neg h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hr v (Or.inl ⟨hv, h⟩)`. Rewrite using `[h]`.

Simplify using `using h1`. Establish `h1` using `hhi _ ⟨v, ⟨hv, h⟩, rfl⟩`. Establish `h2 : (0 : ℝ) < v.1 0` using `by exact_mod_cast h`. Rewrite `h1` using `[lt_div_iff₀ h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem fourier_motzkin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b) :
    ∀ (d : ℕ) (F H : Set ((Fin d → ℤ) × ℝ)), F.Finite → F ⊆ H → (∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) →
      (∀ v ∈ H, v.1 = 0 → v.2 < 0) →
      ∃ φ : Fin d → ℝ, (∀ i, φ i ∈ D) ∧ ∀ v ∈ F, ∑ i, (v.1 i : ℝ) * φ i + v.2 < 0 := by
  intro d
  induction d with
  | zero =>
    intro F H _ hFH _ h0
    refine ⟨Fin.elim0, fun i => i.elim0, fun v hv => ?_⟩
    simpa using h0 v (hFH hv) (Subsingleton.elim _ _)
  | succ d ih =>
    intro F H hF hFH hadd h0
    let π : (Fin (d + 1) → ℤ) × ℝ → (Fin d → ℤ) × ℝ := fun v => (fun i => v.1 i.succ, v.2)
    let cmb : ((Fin (d + 1) → ℤ) × ℝ) × ((Fin (d + 1) → ℤ) × ℝ) → (Fin (d + 1) → ℤ) × ℝ :=
      fun p => (-p.2.1 0) • p.1 + (p.1.1 0) • p.2
    let G : Set ((Fin (d + 1) → ℤ) × ℝ) :=
      {v ∈ F | v.1 0 = 0} ∪ cmb '' ({v ∈ F | 0 < v.1 0} ×ˢ {v ∈ F | v.1 0 < 0})
    have hG : G.Finite :=
      (hF.subset (Set.sep_subset _ _)).union
        (((hF.subset (Set.sep_subset _ _)).prod (hF.subset (Set.sep_subset _ _))).image _)
    have hGH : G ⊆ {v ∈ H | v.1 0 = 0} := by
      rintro v (⟨hv, hv0⟩ | ⟨⟨s, t⟩, ⟨⟨hs, hs0⟩, ht, ht0⟩, rfl⟩)
      · exact ⟨hFH hv, hv0⟩
      · refine ⟨hadd _ (zsmul_mem_pos H hadd _ (hFH hs) _ (neg_pos.2 ht0)) _
          (zsmul_mem_pos H hadd _ (hFH ht) _ hs0), ?_⟩
        simp only [cmb, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    obtain ⟨φ, hφD, hφ⟩ := ih (π '' G) (π '' {v ∈ H | v.1 0 = 0}) (hG.image _)
      (Set.image_mono hGH)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ _ ⟨v, ⟨hv, hv0⟩, rfl⟩
        exact ⟨u + v, ⟨hadd u hu v hv, by simp [hu0, hv0]⟩, rfl⟩)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ h
        refine h0 u hu (funext fun i => ?_)
        refine Fin.cases hu0 (fun j => ?_) i
        exact congrFun h j)
    let r : (Fin (d + 1) → ℤ) × ℝ → ℝ := fun v => ∑ i : Fin d, (v.1 i.succ : ℝ) * φ i + v.2
    have hr : ∀ v ∈ G, r v < 0 := fun v hv => hφ (π v) ⟨v, hv, rfl⟩
    have hrc : ∀ s t, r (cmb (s, t)) = (-(t.1 0 : ℝ)) * r s + (s.1 0 : ℝ) * r t := by
      intro s t
      simp only [r, cmb, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
      simp only [zsmul_eq_mul]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
      ring
    obtain ⟨x, hxD, hlo, hhi⟩ := between_fin D hD
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | v.1 0 < 0})
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | 0 < v.1 0})
      ((hF.subset (Set.sep_subset _ _)).image _) ((hF.subset (Set.sep_subset _ _)).image _)
      (by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
        have h1 := hr _ (Or.inr ⟨(s, t), ⟨hs, ht⟩, rfl⟩)
        rw [hrc] at h1
        have hs0 : (0 : ℝ) < s.1 0 := by exact_mod_cast hs.2
        have ht0 : (t.1 0 : ℝ) < 0 := by exact_mod_cast ht.2
        show -r t / (t.1 0 : ℝ) < -r s / (s.1 0 : ℝ)
        rw [← neg_div_neg_eq, div_lt_div_iff₀ (neg_pos.2 ht0) hs0]
        linarith)
    refine ⟨Fin.cons x φ, fun i => Fin.cases hxD hφD i, fun v hv => ?_⟩
    have hsum : ∑ i, (v.1 i : ℝ) * (Fin.cons x φ : Fin (d + 1) → ℝ) i + v.2 = (v.1 0 : ℝ) * x + r v := by
      simp only [r, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
    rw [hsum]
    rcases lt_trichotomy (v.1 0) 0 with h | h | h
    · have h1 := hlo _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (v.1 0 : ℝ) < 0 := by exact_mod_cast h
      rw [div_lt_iff_of_neg h2] at h1
      linarith
    · have h1 := hr v (Or.inl ⟨hv, h⟩)
      rw [h]; simpa using h1
    · have h1 := hhi _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (0 : ℝ) < v.1 0 := by exact_mod_cast h
      rw [lt_div_iff₀ h2] at h1
      linarith

/- English proof (translation)
Establish `hL : Real.log ‖p‖ ≠ 0` using `Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 hp) hp1`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq1, hq2⟩ : ∃ q : ℚ, a < q * Real.log ‖p‖ ∧ q * Real.log ‖p‖ < b := by`. Break down `lt_or_gt_of_ne hL with h | h` into its components or cases. Take `⟨q, h1, h2⟩` from `exists_rat_btwn ((div_lt_div_right_of_neg h).2 hab)`. Rewrite `h1` using `[div_lt_iff_of_neg h]`.

Rewrite `h2` using `[lt_div_iff_of_neg h]`. Conclude with `⟨q, h2, h1⟩`. Take `⟨q, h1, h2⟩` from `exists_rat_btwn (div_lt_div_of_pos_right hab h)`. Rewrite `h1` using `[div_lt_iff₀ h]`. Rewrite `h2` using `[lt_div_iff₀ h]`.

Conclude with `⟨q, h1, h2⟩`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_pow_nat_eq p q.den_pos`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `hr` using `[zero_pow q.den_nz]`.

Conclude with `hp hr.symm`. Use `⟨_, ⟨Units.mk0 r hr0 ^ q.num, ?_⟩, hq1, hq2⟩` and prove the remaining obligations. Establish `hd : (q.den : ℝ) ≠ 0` using `by exact_mod_cast q.den_nz`. Simplify using `only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Real.log_zpow]`. Rewrite using `[← hr, norm_pow, Real.log_pow, Rat.cast_def]`.

Clear the denominators using the available nonvanishing facts.
-/
private theorem log_norm_dense (K : Type) [NormedField K] [IsAlgClosed K] (p : K) (hp : p ≠ 0)
    (hp1 : ‖p‖ ≠ 1) (a b : ℝ) (hab : a < b) :
    ∃ x ∈ Set.range (fun u : Kˣ => Real.log ‖(u : K)‖), a < x ∧ x < b := by
  have hL : Real.log ‖p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 hp) hp1
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ, a < q * Real.log ‖p‖ ∧ q * Real.log ‖p‖ < b := by
    rcases lt_or_gt_of_ne hL with h | h
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn ((div_lt_div_right_of_neg h).2 hab)
      rw [div_lt_iff_of_neg h] at h1
      rw [lt_div_iff_of_neg h] at h2
      exact ⟨q, h2, h1⟩
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (div_lt_div_of_pos_right hab h)
      rw [div_lt_iff₀ h] at h1
      rw [lt_div_iff₀ h] at h2
      exact ⟨q, h1, h2⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq p q.den_pos
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_nz] at hr
    exact hp hr.symm
  refine ⟨_, ⟨Units.mk0 r hr0 ^ q.num, ?_⟩, hq1, hq2⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Real.log_zpow]
  rw [← hr, norm_pow, Real.log_pow, Rat.cast_def]
  field_simp

/- English proof (translation)
Introduce `σ _ X _ _ _ wt K _ _ z ⟨p, hp, hp1⟩ hz`. Set `e` to `(Module.finBasis ℤ X).equivFun`. Set `g : (σ →₀ ℕ) → K` to `fun n => n.prod fun s k => z s ^ k`. Establish `hg : ∀ m n, g (m + n) = g m * g n` using `fun m n => Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)`. Establish `hg1 : ∀ s, g (Finsupp.single s 1) = z s` using `fun s => by`.

Simplify using `[g, Finsupp.prod_single_index]`. Take `⟨φ, hφD, hφ⟩` from `fourier_motzkin _ (log_norm_dense K p hp hp1) (Module.finrank ℤ X) ((fun s => (e (wt s), Real.log ‖z s‖)) '' {s | z s ≠ 0}) ((fun n => (e (Finsupp.weight wt n), Real.log ‖g n‖)) '' {n | n ≠ 0 ∧ g n ≠ 0}) ((Set.toFinite _).image _) (by`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `⟨Finsupp.single s 1, ⟨by simp, by rw [hg1]; exact hs⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hg1, Finsupp.weight_single])`.

Use the proof step `(by`. Introduce and unpack `_ ⟨m, ⟨hm, hm'⟩, rfl⟩ _ ⟨n, ⟨hn, hn'⟩, rfl⟩`. Use `⟨m + n, ⟨fun h => hm (add_eq_zero.1 h).1, by rw [hg]; exact mul_ne_zero hm' hn'⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hg, map_add, norm_mul, Prod.mk_add_mk, Real.log_mul (norm_ne_zero_iff.2 hm') (norm_ne_zero_iff.2 hn')])`. Use the proof step `(by`.

Introduce and unpack `_ ⟨n, ⟨hn, hn'⟩, rfl⟩ h`. Conclude with `Real.log_neg (norm_pos_iff.2 hn') (hz n hn (e.map_eq_zero_iff.1 h)))`. Use `choose u hu using hφD`. Set `t : Multiplicative X →* Kˣ` to `{ toFun := fun x => ∏ i, u i ^ (e x.toAdd i) map_one' := by simp map_mul' := fun x y => by simp [zpow_add, Finset.prod_mul_distrib] }`. Use `⟨t, fun s => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hs : z s = 0`. Simplify using `[hs]`. Establish `h1` using `hφ _ ⟨s, hs, rfl⟩`. Establish `h2 : Real.log ‖(t (Multiplicative.ofAdd (wt s)) : K)‖ = ∑ i, (e (wt s) i : ℝ) * φ i` using `by show Real.log ‖((∏ i, u i ^ (e (wt s) i) : Kˣ) : K)‖ = _`. Rewrite using `[Units.coe_prod, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.2 (Units.ne_zero _))]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, ← hu i]`. Rewrite using `[← Real.log_neg_iff (norm_pos_iff.2 (mul_ne_zero (Units.ne_zero _) hs)), norm_mul, Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 hs), h2]`. Conclude with `h1`.
-/
theorem UpperTheory.V.Alg.carver :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (K : Type) [NormedField K] [IsAlgClosed K] (z : σ → K), (∃ p : K, p ≠ 0 ∧ ‖p‖ ≠ 1) →
      (∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → ‖n.prod fun s k => z s ^ k‖ < 1) →
      ∃ t : Multiplicative X →* Kˣ, ∀ s, ‖(t (Multiplicative.ofAdd (wt s)) : K) * z s‖ < 1 := by
  intro σ _ X _ _ _ wt K _ _ z ⟨p, hp, hp1⟩ hz
  let e := (Module.finBasis ℤ X).equivFun
  let g : (σ →₀ ℕ) → K := fun n => n.prod fun s k => z s ^ k
  have hg : ∀ m n, g (m + n) = g m * g n := fun m n =>
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  have hg1 : ∀ s, g (Finsupp.single s 1) = z s := fun s => by
    simp [g, Finsupp.prod_single_index]
  obtain ⟨φ, hφD, hφ⟩ := fourier_motzkin _ (log_norm_dense K p hp hp1) (Module.finrank ℤ X)
    ((fun s => (e (wt s), Real.log ‖z s‖)) '' {s | z s ≠ 0})
    ((fun n => (e (Finsupp.weight wt n), Real.log ‖g n‖)) '' {n | n ≠ 0 ∧ g n ≠ 0})
    ((Set.toFinite _).image _)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨Finsupp.single s 1, ⟨by simp, by rw [hg1]; exact hs⟩, ?_⟩
      simp [hg1, Finsupp.weight_single])
    (by
      rintro _ ⟨m, ⟨hm, hm'⟩, rfl⟩ _ ⟨n, ⟨hn, hn'⟩, rfl⟩
      refine ⟨m + n, ⟨fun h => hm (add_eq_zero.1 h).1, by rw [hg]; exact mul_ne_zero hm' hn'⟩, ?_⟩
      simp only [hg, map_add, norm_mul, Prod.mk_add_mk,
        Real.log_mul (norm_ne_zero_iff.2 hm') (norm_ne_zero_iff.2 hn')])
    (by
      rintro _ ⟨n, ⟨hn, hn'⟩, rfl⟩ h
      exact Real.log_neg (norm_pos_iff.2 hn') (hz n hn (e.map_eq_zero_iff.1 h)))
  choose u hu using hφD
  let t : Multiplicative X →* Kˣ :=
    { toFun := fun x => ∏ i, u i ^ (e x.toAdd i)
      map_one' := by simp
      map_mul' := fun x y => by simp [zpow_add, Finset.prod_mul_distrib] }
  refine ⟨t, fun s => ?_⟩
  by_cases hs : z s = 0
  · simp [hs]
  have h1 := hφ _ ⟨s, hs, rfl⟩
  have h2 : Real.log ‖(t (Multiplicative.ofAdd (wt s)) : K)‖ = ∑ i, (e (wt s) i : ℝ) * φ i := by
    show Real.log ‖((∏ i, u i ^ (e (wt s) i) : Kˣ) : K)‖ = _
    rw [Units.coe_prod, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.2 (Units.ne_zero _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, ← hu i]
  rw [← Real.log_neg_iff (norm_pos_iff.2 (mul_ne_zero (Units.ne_zero _) hs)), norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 hs), h2]
  exact h1
