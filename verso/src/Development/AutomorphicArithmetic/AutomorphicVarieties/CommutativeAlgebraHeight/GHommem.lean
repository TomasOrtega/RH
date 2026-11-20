import Mathlib

open IsLocalRing

/- English proof (translation)
Use `haveI : Fintype σ := Fintype.ofFinite σ`. Use `set D : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => d) with hD`. Use `⟨∑ m ∈ Finset.Iic D, MvPolynomial.monomial m (if m.degree ≤ d then MvPowerSeries.coeff m F else 0), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `h : m.degree ≤ d`. Establish `hm : m ∈ Finset.Iic D`. Use `Finset.mem_Iic.mpr (Finsupp.le_def.mpr fun i => (Finsupp.le_degree i m).trans (h.trans ?_))` and prove the remaining obligations. Simplify using `[hD]`.

Rewrite using `[if_pos hm]`. Simplify using `[h]`.
-/
private theorem UpperTheory.V.CA.exists_part {R σ : Type} [CommRing R] [Finite σ]
    (F : MvPowerSeries σ R) (d : ℕ) :
    ∃ g : MvPolynomial σ R, ∀ m : σ →₀ ℕ,
      g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m F else 0 := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  set D : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => d) with hD
  refine ⟨∑ m ∈ Finset.Iic D, MvPolynomial.monomial m
    (if m.degree ≤ d then MvPowerSeries.coeff m F else 0), fun m => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : m.degree ≤ d
  · have hm : m ∈ Finset.Iic D := by
      refine Finset.mem_Iic.mpr (Finsupp.le_def.mpr fun i => (Finsupp.le_degree i m).trans (h.trans ?_))
      simp [hD]
    rw [if_pos hm]
  · simp [h]

/- English proof (translation)
Introduce `R σ _ _ _ P hP F`. Establish `hsumco : ∀ (f : MvPolynomial σ R) (d : ℕ) (m : σ →₀ ℕ), MvPolynomial.coeff m (∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f) = if m.degree ≤ d then MvPolynomial.coeff m f else 0`. Introduce `f d m`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_homogeneousComponent]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_range, Nat.lt_succ_iff]`. Establish `htr` using `UpperTheory.V.CA.exists_part (R := R) (σ := σ)`. Establish `hpolyQ : ∀ f ∈ P, ∀ (d : ℕ) (g : MvPolynomial σ R), (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPolynomial.coeff m f else 0) → g ∈ P`. Introduce `f hf d g hg`.

Establish `hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f`. Use extensionality with `m`. Rewrite using `[hg, hsumco]`. Rewrite using `[hgeq]`. Conclude with `Ideal.sum_mem _ fun k _ => hP f hf k`.

Establish `hRQ : ∀ G : MvPowerSeries σ R, ((∀ (d : ℕ) (g : MvPolynomial σ R), (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m G else 0) → g ∈ P) ↔ (∀ (d : ℕ) (g : MvPolynomial σ R), (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m G else 0) → g ∈ P …`. Introduce `G`. Prove the components needed by the constructor for the conclusion. Introduce `h d g hg`. Establish `hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k g`.

Use extensionality with `m`. Rewrite using `[hsumco]`. Distinguish the cases in `hm : m.degree ≤ d`. Rewrite using `[if_pos hm]`. Rewrite using `[if_neg hm, hg, if_neg hm]`.

Rewrite using `[hgeq]`. Use `Ideal.sum_mem _ fun k hk => h k _ fun m => ?_` and prove the remaining obligations. Establish `hk' : k ≤ d` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Rewrite using `[MvPolynomial.coeff_homogeneousComponent, hg]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.

Introduce `h d g hg`. Take `⟨T, hT⟩` from `htr G d`. Establish `hTP : T ∈ P` using `h d T hT`. Establish `hgeq : g = MvPolynomial.homogeneousComponent d T`. Use extensionality with `m`.

Rewrite using `[hg, MvPolynomial.coeff_homogeneousComponent, hT]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[hgeq]`. Conclude with `hP T hTP d`. Use `Iff.trans ?_ (hRQ F).symm` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `hF`. Establish `hF' : F ∈ Submodule.span (MvPowerSeries σ R) (MvPolynomial.coeToMvPowerSeries.ringHom (σ` using `σ) (R := R) '' (P : Set (MvPolynomial σ R))) := hF`. Use `Submodule.span_induction (p := fun x _ => ∀ (d : ℕ) (g : MvPolynomial σ R), (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m x else 0) → g ∈ P) ?_ ?_ ?_ ?_ hF'` and prove the remaining obligations. Introduce and unpack `x ⟨f, hf, rfl⟩ d g hg`.

Use `hpolyQ f hf d g fun m => ?_` and prove the remaining obligations. Rewrite using `[hg, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]`. Introduce `d g hg`. Establish `hg0 : g = 0`. Use extensionality with `m`.

Simplify using `[hg]`. Rewrite using `[hg0]`. Conclude with `P.zero_mem`. Introduce `x y _ _ hx hy d g hg`. Take `⟨gx, hgx⟩` from `htr x d`.

Take `⟨gy, hgy⟩` from `htr y d`. Establish `hgeq : g = gx + gy`. Use extensionality with `m`. Rewrite using `[hg, MvPolynomial.coeff_add, hgx, hgy, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hgeq]`. Conclude with `P.add_mem (hx d gx hgx) (hy d gy hgy)`. Introduce `a x _ hx d g hg`. Take `⟨Ta, hTa⟩` from `htr a d`. Take `⟨Tx, hTx⟩` from `htr x d`.

Establish `hTxP` using `hx d Tx hTx`. Establish `hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k (Ta * Tx)`. Use extensionality with `m`. Rewrite using `[hsumco, hg, smul_eq_mul]`. Distinguish the cases in `hm : m.degree ≤ d`.

Rewrite using `[if_pos hm, if_pos hm, MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hpm : p.1 + p.2 = m` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Establish `hdeg : p.1.degree + p.2.degree = m.degree` using `by rw [← map_add, hpm]`. Rewrite using `[hTa, hTx, if_pos (by omega), if_pos (by omega)]`.

Rewrite using `[if_neg hm, if_neg hm]`. Rewrite using `[hgeq]`. Conclude with `Ideal.sum_mem _ fun k _ => hP _ (P.mul_mem_left Ta hTxP) k`. Introduce `hQ`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian P : P.FG)`.

Use `set D := s.sup MvPolynomial.totalDegree with hD`. Set `h : ↥s × Fin (D + 1) → MvPolynomial σ R` to `fun i => MvPolynomial.homogeneousComponent i.2.val i.1.val`. Establish `hhP : ∀ i, h i ∈ P`. Introduce `i`. Establish `hi : (i.1 : MvPolynomial σ R) ∈ P`.

Rewrite using `[← hs]`. Conclude with `Submodule.subset_span i.1.2`. Conclude with `hP _ hi _`. Establish `hPspan : P ≤ Ideal.span (Set.range h)`. Rewrite using `[← hs, Submodule.span_le]`.

Introduce `f hf`. Establish `hf' : f ∈ s` using `Finset.mem_coe.mp hf`. Establish `hfsum : f = ∑ k ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent k f`. Rewrite using `[← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (Finset.le_sup (f := MvPolynomial.totalDegree) hf'))) ?_, MvPolynomial.sum_homogeneousComponent]`. Introduce `k _ hk`.

Simplify using `only [Finset.mem_range] at hk`. Conclude with `MvPolynomial.homogeneousComponent_eq_zero k f (by omega)`. Rewrite using `[SetLike.mem_coe, hfsum]`. Conclude with `Ideal.sum_mem _ fun k hk => Ideal.subset_span ⟨(⟨f, hf'⟩, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩`. Establish `hcomp : ∀ d : ℕ, ∃ c : ↥s × Fin (D + 1) → MvPolynomial σ R, ∑ i, c i • h i = MvPolynomial.homogeneousComponent d (Classical.choose (htr F d))`.

Introduce `d`. Establish `hmem : MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) ∈ P` using `hP _ (hQ d _ (Classical.choose_spec (htr F d))) d`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).mp (hPspan hmem)`. Use `choose c hc using hcomp`. Establish `hcoefF : ∀ m : σ →₀ ℕ, MvPolynomial.coeff m (∑ i, c m.degree i • h i) = MvPowerSeries.coeff m F`.

Introduce `m`. Rewrite using `[hc, MvPolynomial.coeff_homogeneousComponent, if_pos rfl, Classical.choose_spec (htr F m.degree) m, if_pos le_rfl]`. Set `C : ↥s × Fin (D + 1) → MvPowerSeries σ R` to `fun i p => MvPolynomial.coeff p (c (p.degree + i.2.val) i)`. Establish `hFeq : F = ∑ i, C i * MvPolynomial.coeToMvPowerSeries.ringHom (σ` using `σ) (R := R) (h i) := by`. Use extensionality with `m`.

Rewrite using `[← hcoefF m, map_sum, MvPolynomial.coeff_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_mul, smul_eq_mul, MvPolynomial.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]`.

Establish `hpm : p.1 + p.2 = m` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Establish `hdeg : p.1.degree + p.2.degree = m.degree` using `by rw [← map_add, hpm]`. Use `show MvPolynomial.coeff p.1 (c m.degree i) * MvPolynomial.coeff p.2 (h i) = MvPolynomial.coeff p.1 (c (p.1.degree + i.2.val) i) * MvPolynomial.coeff p.2 (h i)`. Distinguish the cases in `h2 : p.2.degree = i.2.val`. Rewrite using `[← h2, hdeg]`.

Establish `h0 : MvPolynomial.coeff p.2 (h i) = 0` using `by show MvPolynomial.coeff p.2 (MvPolynomial.homogeneousComponent i.2.val i.1.val) = 0`. Rewrite using `[MvPolynomial.coeff_homogeneousComponent, if_neg h2]`. Rewrite using `[h0, mul_zero, mul_zero]`. Rewrite using `[hFeq]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hhP i))`.
-/
theorem UpperTheory.V.CA.g_hommem :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (P : Ideal (MvPolynomial σ R)),
      (∀ f ∈ P, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ P) → ∀ F : MvPowerSeries σ R,
        F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) ↔
          ∀ (d : ℕ) (g : MvPolynomial σ R),
            (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0) → g ∈ P := by
  intro R σ _ _ _ P hP F
  classical
  have hsumco : ∀ (f : MvPolynomial σ R) (d : ℕ) (m : σ →₀ ℕ),
      MvPolynomial.coeff m (∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f) =
        if m.degree ≤ d then MvPolynomial.coeff m f else 0 := by
    intro f d m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_homogeneousComponent]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have htr := UpperTheory.V.CA.exists_part (R := R) (σ := σ)
  have hpolyQ : ∀ f ∈ P, ∀ (d : ℕ) (g : MvPolynomial σ R),
      (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPolynomial.coeff m f else 0) → g ∈ P := by
    intro f hf d g hg
    have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f := by
      ext m
      rw [hg, hsumco]
    rw [hgeq]
    exact Ideal.sum_mem _ fun k _ => hP f hf k
  have hRQ : ∀ G : MvPowerSeries σ R,
      ((∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m G else 0) → g ∈ P) ↔
      (∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m G else 0) → g ∈ P)) := by
    intro G
    constructor
    · intro h d g hg
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k g := by
        ext m
        rw [hsumco]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm]
        · rw [if_neg hm, hg, if_neg hm]
      rw [hgeq]
      refine Ideal.sum_mem _ fun k hk => h k _ fun m => ?_
      have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [MvPolynomial.coeff_homogeneousComponent, hg]
      split_ifs <;> first | rfl | (exfalso; omega)
    · intro h d g hg
      obtain ⟨T, hT⟩ := htr G d
      have hTP : T ∈ P := h d T hT
      have hgeq : g = MvPolynomial.homogeneousComponent d T := by
        ext m
        rw [hg, MvPolynomial.coeff_homogeneousComponent, hT]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hgeq]
      exact hP T hTP d
  refine Iff.trans ?_ (hRQ F).symm
  constructor
  · intro hF
    have hF' : F ∈ Submodule.span (MvPowerSeries σ R)
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) '' (P : Set (MvPolynomial σ R))) := hF
    refine Submodule.span_induction (p := fun x _ => ∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m x else 0) → g ∈ P)
      ?_ ?_ ?_ ?_ hF'
    · rintro x ⟨f, hf, rfl⟩ d g hg
      refine hpolyQ f hf d g fun m => ?_
      rw [hg, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
    · intro d g hg
      have hg0 : g = 0 := by
        ext m
        simp [hg]
      rw [hg0]
      exact P.zero_mem
    · intro x y _ _ hx hy d g hg
      obtain ⟨gx, hgx⟩ := htr x d
      obtain ⟨gy, hgy⟩ := htr y d
      have hgeq : g = gx + gy := by
        ext m
        rw [hg, MvPolynomial.coeff_add, hgx, hgy, map_add]
        split_ifs <;> simp
      rw [hgeq]
      exact P.add_mem (hx d gx hgx) (hy d gy hgy)
    · intro a x _ hx d g hg
      obtain ⟨Ta, hTa⟩ := htr a d
      obtain ⟨Tx, hTx⟩ := htr x d
      have hTxP := hx d Tx hTx
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k (Ta * Tx) := by
        ext m
        rw [hsumco, hg, smul_eq_mul]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm, if_pos hm, MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add, hpm]
          rw [hTa, hTx, if_pos (by omega), if_pos (by omega)]
        · rw [if_neg hm, if_neg hm]
      rw [hgeq]
      exact Ideal.sum_mem _ fun k _ => hP _ (P.mul_mem_left Ta hTxP) k
  · intro hQ
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
    set D := s.sup MvPolynomial.totalDegree with hD
    let h : ↥s × Fin (D + 1) → MvPolynomial σ R := fun i =>
      MvPolynomial.homogeneousComponent i.2.val i.1.val
    have hhP : ∀ i, h i ∈ P := by
      intro i
      have hi : (i.1 : MvPolynomial σ R) ∈ P := by
        rw [← hs]
        exact Submodule.subset_span i.1.2
      exact hP _ hi _
    have hPspan : P ≤ Ideal.span (Set.range h) := by
      rw [← hs, Submodule.span_le]
      intro f hf
      have hf' : f ∈ s := Finset.mem_coe.mp hf
      have hfsum : f = ∑ k ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent k f := by
        rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (Finset.le_sup (f := MvPolynomial.totalDegree) hf'))) ?_,
          MvPolynomial.sum_homogeneousComponent]
        intro k _ hk
        simp only [Finset.mem_range] at hk
        exact MvPolynomial.homogeneousComponent_eq_zero k f (by omega)
      rw [SetLike.mem_coe, hfsum]
      exact Ideal.sum_mem _ fun k hk =>
        Ideal.subset_span ⟨(⟨f, hf'⟩, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
    have hcomp : ∀ d : ℕ, ∃ c : ↥s × Fin (D + 1) → MvPolynomial σ R,
        ∑ i, c i • h i = MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) := by
      intro d
      have hmem : MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) ∈ P :=
        hP _ (hQ d _ (Classical.choose_spec (htr F d))) d
      exact (Submodule.mem_span_range_iff_exists_fun _).mp (hPspan hmem)
    choose c hc using hcomp
    have hcoefF : ∀ m : σ →₀ ℕ,
        MvPolynomial.coeff m (∑ i, c m.degree i • h i) = MvPowerSeries.coeff m F := by
      intro m
      rw [hc, MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
        Classical.choose_spec (htr F m.degree) m, if_pos le_rfl]
    let C : ↥s × Fin (D + 1) → MvPowerSeries σ R := fun i p =>
      MvPolynomial.coeff p (c (p.degree + i.2.val) i)
    have hFeq : F = ∑ i, C i * MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) (h i) := by
      ext m
      rw [← hcoefF m, map_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_mul, smul_eq_mul, MvPolynomial.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
      have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add, hpm]
      show MvPolynomial.coeff p.1 (c m.degree i) * MvPolynomial.coeff p.2 (h i) =
        MvPolynomial.coeff p.1 (c (p.1.degree + i.2.val) i) * MvPolynomial.coeff p.2 (h i)
      by_cases h2 : p.2.degree = i.2.val
      · rw [← h2, hdeg]
      · have h0 : MvPolynomial.coeff p.2 (h i) = 0 := by
          show MvPolynomial.coeff p.2 (MvPolynomial.homogeneousComponent i.2.val i.1.val) = 0
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h2]
        rw [h0, mul_zero, mul_zero]
    rw [hFeq]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hhP i))
