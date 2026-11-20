import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLengthStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets

noncomputable section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

namespace GlobalTheory.UnramDoublingProof

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h` using `iUnion_cell (k := k) (N := N) hϖ`. Conclude with `Set.mem_iUnion.1 (h ▸ Set.mem_univ g)`.
-/
theorem exists_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) :
    ∃ e : {e : Fin N → ℤ // Antitone e}, g ∈ cell k (Fin N) ϖ e := by
  have h := iUnion_cell (k := k) (N := N) hϖ
  exact Set.mem_iUnion.1 (h ▸ Set.mem_univ g)

def cellLen {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) : ℕ :=
  (∑ i, |(exists_cell hϖ g).choose.1 i|).toNat

/- English proof (translation)
Establish `h` using `(exists_cell hϖ g).choose_spec`. Establish `h' : (exists_cell hϖ g).choose = ⟨e, he⟩`. Assume the negation of the conclusion as `hne`. Conclude with `Set.disjoint_left.1 (pairwise_disjoint_cell hϖ hne) h hg`. Simplify using `only [cellLen, h']`.
-/
theorem cellLen_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (g : GL (Fin N) k) (hg : g ∈ cell k (Fin N) ϖ e) : cellLen hϖ g = (∑ i, |e i|).toNat := by
  have h := (exists_cell hϖ g).choose_spec
  have h' : (exists_cell hϖ g).choose = ⟨e, he⟩ := by
    by_contra hne
    exact Set.disjoint_left.1 (pairwise_disjoint_cell hϖ hne) h hg
  simp only [cellLen, h']

/- English proof (translation)
Take `⟨⟨e, he⟩, hg⟩` from `exists_cell hϖ g`. Rewrite using `[cellLen_eq hϖ e he g hg]`. Take `⟨x, hx, y, hy, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hg`. Rewrite using `[sphSection_io_biinv s _ hx hy, sphSection_torusElt hϖ, Fintype.card_fin, ← Complex.cpow_nat_mul]`. Establish `h0 : 0 ≤ ∑ i, |e i|` using `Finset.sum_nonneg fun i _ => abs_nonneg _`.

Establish `hc : (((∑ i, |e i|).toNat : ℕ) : ℂ) = ((∑ i, |e i| : ℤ) : ℂ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h0]`. Rewrite using `[hc]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sphSection_eq_pow {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ)
    (g : GL (Fin N) k) :
    sphSection k (Fin N) s (io k (Fin N) (g, 1)) =
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s))) ^ cellLen hϖ g := by
  obtain ⟨⟨e, he⟩, hg⟩ := exists_cell hϖ g
  rw [cellLen_eq hϖ e he g hg]
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [sphSection_io_biinv s _ hx hy, sphSection_torusElt hϖ, Fintype.card_fin, ← Complex.cpow_nat_mul]
  have h0 : 0 ≤ ∑ i, |e i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc : (((∑ i, |e i|).toNat : ℕ) : ℂ) = ((∑ i, |e i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hc]
  congr 1
  ring

/- English proof (translation)
Introduce `x`. Establish `hmo : IsOpen (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k))`. Establish `hset : (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) = (fun y => x⁻¹ * y * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))`. Use extensionality with `y`. Simplify using `only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Simplify `hz` using `[mul_assoc]`. Introduce `h`. Conclude with `⟨_, h, by group⟩`.

Rewrite using `[hset]`. Conclude with `SplitFlip.isOpen_KO.preimage (by fun_prop)`. Establish `: CompactSpace (KO k (Fin N))` using `isCompact_iff_compactSpace.mp SplitFlip.isCompact_KO`. Establish `hso : IsOpen ((((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)) : Subgroup (KO k (Fin N))) : Set (KO k (Fin N)))`. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `hmo.preimage continuous_subtype_val`. Establish `: Finite ((KO k (Fin N)) ⧸ ((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)))` using `Subgroup.quotient_finite_of_isOpen _ hso`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem isCommensurated_KO {N : ℕ} : Formalism.UG.IsCommensurated (KO k (Fin N)) := by
  intro x
  have hmo : IsOpen (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
      Set (GL (Fin N) k)) := by
    have hset : (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) = (fun y => x⁻¹ * y * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact SplitFlip.isOpen_KO.preimage (by fun_prop)
  have : CompactSpace (KO k (Fin N)) := isCompact_iff_compactSpace.mp SplitFlip.isCompact_KO
  have hso : IsOpen ((((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)) :
      Subgroup (KO k (Fin N))) : Set (KO k (Fin N))) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite ((KO k (Fin N)) ⧸ ((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N))) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

end Cells

section Factors

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq.ne'`. Establish `hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ)`. Use `i.2` as an intermediate fact. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, hc, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_one {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (n - 1 - (i : ℕ)) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, hc,
    mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq.ne'`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, mul_inv, ← Complex.cpow_neg, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qpow_mul_inv_mul_qpow_eq {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (i : ℕ) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a⁻¹ * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, mul_inv,
    ← Complex.cpow_neg, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq.ne'`. Unfold `invNormFactor`. Use `Finset.prod_bij' (fun i _ => n - (i : ℕ)) (fun j hj => ⟨n - j, by have := Finset.mem_Icc.1 hj; omega⟩) (fun i _ => ?_) (fun _ _ => Finset.mem_univ _) (fun i _ => ?_) (fun j hj => ?_) (fun i _ => ?_)` and prove the remaining obligations. Use `i.2` as an intermediate fact. Conclude with `Finset.mem_Icc.2 ⟨by omega, by omega⟩`.

Use `i.2` as an intermediate fact. Conclude with `Fin.ext (by simp only; omega)`. Use `Finset.mem_Icc.1 hj` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, Nat.cast_sub i.2.le]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_one_sub_eq_invNormFactor {q n : ℕ} (hq : 0 < q) (s : ℂ) :
    ∏ i : Fin n, (1 - (q : ℂ) ^ (i : ℕ) * ((q : ℂ) ^ (-((n : ℂ) / 2 + s))) ^ 2) = invNormFactor q n s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  unfold invNormFactor
  refine Finset.prod_bij' (fun i _ => n - (i : ℕ))
    (fun j hj => ⟨n - j, by have := Finset.mem_Icc.1 hj; omega⟩) (fun i _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun i _ => ?_) (fun j hj => ?_) (fun i _ => ?_)
  · have := i.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · have := i.2
    exact Fin.ext (by simp only; omega)
  · have := Finset.mem_Icc.1 hj
    simp only
    omega
  · rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, Nat.cast_sub i.2.le]
    congr 2
    push_cast
    ring

end Factors

/- English proof (translation)
Introduce `k _ _ _ _ _ n _ _ μ _ hμ V _ _ π α hπ ω hω`. Choose the witnesses or unpack the hypotheses as in `⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by`. Take `⟨x, hx⟩` from `valuation_surjective (K := k) (uniformizer k)`. Establish `h0 : x ≠ 0`. Introduce and unpack `rfl`.

Conclude with `uniformizer_ne_zero (R := k) (by simpa using hx.symm)`. Conclude with `⟨Units.mk0 x h0, hx⟩`. Establish `hq1 : 1 < resCard k` using `one_lt_resCard k`. Establish `hq : 0 < resCard k` using `zero_lt_one.trans hq1`. Establish `hqR : (1 : ℝ) < resCard k` using `by exact_mod_cast hq1`.

Establish `hqR0 : (0 : ℝ) < resCard k` using `zero_lt_one.trans hqR`. Take `⟨φ, hφ, hsum⟩` from `GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal k n V π α hπ ω hω`. Take `⟨δ, hδ, hmain⟩` from `GlobalTheory.T.hasSum_sphericalFunction_doublingLength k n _ φ hφ (fun i => mul_ne_zero (α i).ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hqR0 _).ne')) ϖ hϖ (cellLen hϖ) (cellLen_eq hϖ)`. Use `⟨-Real.logb (resCard k) δ - n / 2, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hX : ‖(resCard k : ℂ) ^ (-((n : ℂ) / 2 + s))‖ < δ`.

Rewrite using `[Complex.norm_natCast_cpow_of_pos hq]`. Use `(Real.rpow_lt_rpow_of_exponent_lt hqR (?_ : _ < Real.logb (resCard k) δ)).trans_eq (Real.rpow_logb hqR0 hqR.ne' hδ)` and prove the remaining obligations. Establish `: (-((n : ℂ) / 2 + s)).re = -((n : ℝ) / 2 + s.re)` using `by simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `hmain _ hX`. Simplify using `only [← sphSection_eq_pow hϖ s, factor_one hq, qpow_mul_inv_mul_qpow_eq hq, prod_one_sub_eq_invNormFactor hq] at h1`. Establish `h2` using `GlobalTheory.InertZeta.dosetSwap (GL (Fin n) k) (KO k (Fin n)) isCommensurated_KO (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1))) ω φ _ (fun a b g => sphSection_io_biinv s g a.2 b.2) (fun a b g => zonal_biinv hω g a.2 b.2) hsum h1`. Establish `h3` using `GlobalTheory.InertZeta.cosetIntegral_holds (GL (Fin n) k) μ (KO k (Fin n)) SplitFlip.isOpen_KO hμ (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) _ (fun g y hy => by`. Establish `e1` using `sphSection_io_biinv s g (one_mem (KO k (Fin n))) hy`.

Establish `e2` using `zonal_biinv hω g (one_mem (KO k (Fin n))) hy`. Rewrite `e1`, `e2` using `[one_mul]`. Simplify using `only [e1, e2]) h2`. Use `⟨h3.1, h3.2.trans ?_⟩` and prove the remaining obligations. Simplify using `only [lFactor, Pi.inv_apply, Units.val_inv_eq_inv_val]`.
-/
theorem unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL := by
  intro k _ _ _ _ _ n _ _ μ _ hμ V _ _ π α hπ ω hω
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hq1 : 1 < resCard k := one_lt_resCard k
  have hq : 0 < resCard k := zero_lt_one.trans hq1
  have hqR : (1 : ℝ) < resCard k := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < resCard k := zero_lt_one.trans hqR
  obtain ⟨φ, hφ, hsum⟩ := GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal k n V π α hπ ω hω
  obtain ⟨δ, hδ, hmain⟩ := GlobalTheory.T.hasSum_sphericalFunction_doublingLength k n _ φ hφ
    (fun i => mul_ne_zero (α i).ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hqR0 _).ne'))
    ϖ hϖ (cellLen hϖ) (cellLen_eq hϖ)
  refine ⟨-Real.logb (resCard k) δ - n / 2, fun s hs => ?_⟩
  have hX : ‖(resCard k : ℂ) ^ (-((n : ℂ) / 2 + s))‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    refine (Real.rpow_lt_rpow_of_exponent_lt hqR (?_ : _ < Real.logb (resCard k) δ)).trans_eq
      (Real.rpow_logb hqR0 hqR.ne' hδ)
    have : (-((n : ℂ) / 2 + s)).re = -((n : ℝ) / 2 + s.re) := by simp
    rw [this]
    linarith
  have h1 := hmain _ hX
  simp only [← sphSection_eq_pow hϖ s, factor_one hq, qpow_mul_inv_mul_qpow_eq hq, prod_one_sub_eq_invNormFactor hq] at h1
  have h2 := GlobalTheory.InertZeta.dosetSwap (GL (Fin n) k) (KO k (Fin n)) isCommensurated_KO
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1))) ω φ _
    (fun a b g => sphSection_io_biinv s g a.2 b.2) (fun a b g => zonal_biinv hω g a.2 b.2) hsum h1
  have h3 := GlobalTheory.InertZeta.cosetIntegral_holds (GL (Fin n) k) μ (KO k (Fin n)) SplitFlip.isOpen_KO hμ
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) _ (fun g y hy => by
      have e1 := sphSection_io_biinv s g (one_mem (KO k (Fin n))) hy
      have e2 := zonal_biinv hω g (one_mem (KO k (Fin n))) hy
      rw [one_mul] at e1 e2
      simp only [e1, e2]) h2
  refine ⟨h3.1, h3.2.trans ?_⟩
  simp only [lFactor, Pi.inv_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.UnramDoublingProof
