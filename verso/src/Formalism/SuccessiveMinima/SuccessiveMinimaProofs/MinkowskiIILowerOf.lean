import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN.LowerVolumeBound

/- English proof (translation)
Use `set s := ∑ i, |c i| with hsdef`. Set `p : Fin n → E` to `fun i => if 0 ≤ c i then w i else -w i`. Establish `hp : ∀ i, p i ∈ K` using `fun i => by dsimp only [p]; split_ifs`. Conclude with `hw i`. Conclude with `hs _ (hw i)`.

Establish `hcp : ∀ i, c i • w i = |c i| • p i` using `fun i => by dsimp only [p]; split_ifs with h`. Rewrite using `[abs_of_nonneg h]`. Rewrite using `[abs_of_neg (not_le.mp h), neg_smul, smul_neg, neg_neg]`. Establish `hs_nonneg : 0 ≤ s` using `Finset.sum_nonneg (fun i _ => abs_nonneg (c i))`. Break down `hs_nonneg.eq_or_lt with hs0 | hs0` into its components or cases.

Establish `hz : ∀ i, c i = 0` using `fun i => abs_eq_zero.mp (le_antisymm ((Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans hs0.symm.le) (abs_nonneg _))`. Simplify `h0` using `[hz]`. Establish `hx : ∑ i, (|c i| / s) • p i ∈ K` using `hK.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hs0.le) (by rw [← Finset.sum_div, div_self hs0.ne']) (fun i _ => hp i)`. Establish `h2` using `hK.smul_mem_of_zero_mem h0 hx ⟨hs0.le, hc⟩`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_div_cancel₀ _ hs0.ne', hcp]`.
-/
lemma cross_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ K) {n : ℕ} (w : Fin n → E) (hw : ∀ i, w i ∈ K)
    (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) : ∑ i, c i • w i ∈ K := by
  classical
  set s := ∑ i, |c i| with hsdef
  let p : Fin n → E := fun i => if 0 ≤ c i then w i else -w i
  have hp : ∀ i, p i ∈ K := fun i => by
    dsimp only [p]; split_ifs
    · exact hw i
    · exact hs _ (hw i)
  have hcp : ∀ i, c i • w i = |c i| • p i := fun i => by
    dsimp only [p]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), neg_smul, smul_neg, neg_neg]
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  rcases hs_nonneg.eq_or_lt with hs0 | hs0
  · have hz : ∀ i, c i = 0 := fun i => abs_eq_zero.mp (le_antisymm
      ((Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans hs0.symm.le)
      (abs_nonneg _))
    simpa [hz] using h0
  · have hx : ∑ i, (|c i| / s) • p i ∈ K :=
      hK.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hs0.le)
        (by rw [← Finset.sum_div, div_self hs0.ne']) (fun i _ => hp i)
    have h2 := hK.smul_mem_of_zero_mem h0 hx ⟨hs0.le, hc⟩
    convert h2 using 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hs0.ne', hcp]

/- English proof (translation)
Establish `hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin (finrank ℝ E))`. Rewrite using `[← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Fintype.card_fin]`. Set `bz : Basis (Fin (finrank ℝ E)) ℤ L` to `(Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)`. Set `b' : Basis (Fin (finrank ℝ E)) ℝ E` to `bz.ofZLatticeBasis ℝ L`. Establish `hb' : ((↑) : L → E) ∘ bz = ⇑b'`.

Use function extensionality and compare the values at `i`. Simplify using `[b']`. Establish `hk : ∃ k : ℤ, b'.det bv = k`. Use `⟨(Matrix.of fun i j => bz.repr ⟨bv j, hv j⟩ i).det, ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.det_apply, Int.cast_det]`.

Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Basis.toMatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Conclude with `bz.ofZLatticeBasis_repr_apply ℝ L ⟨bv j, hv j⟩ i`. Take `⟨k, hk⟩` from `hk`.

Establish `hprod : bv.det b' * b'.det bv = 1`. Rewrite using `[Basis.det_mul_det, Basis.det_self]`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `[hk] at hprod`.

Establish `hdet : |bv.det b'| ≤ 1`. Establish `h1 : (1 : ℝ) ≤ |(k : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hk0` after adjusting the coercions. Establish `h2 : |bv.det b'| * |(k : ℝ)| = 1` using `by rw [← abs_mul, ← hk, hprod, abs_one]`.

Use polynomial arithmetic with `[abs_nonneg (bv.det b')]`. Rewrite using `[ZLattice.covolume_eq_det_mul_measureReal L μ bz bv, hb', measureReal_congr (fundamentalDomain_ae_parallelepiped bv μ)]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma covol_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (bv : Basis (Fin (finrank ℝ E)) ℝ E) (hv : ∀ i, bv i ∈ L) :
    ZLattice.covolume L μ ≤ μ.real (parallelepiped bv) := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin (finrank ℝ E)) := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Fintype.card_fin]
  let bz : Basis (Fin (finrank ℝ E)) ℤ L :=
    (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)
  let b' : Basis (Fin (finrank ℝ E)) ℝ E := bz.ofZLatticeBasis ℝ L
  have hb' : ((↑) : L → E) ∘ bz = ⇑b' := by
    funext i; simp [b']
  have hk : ∃ k : ℤ, b'.det bv = k := by
    refine ⟨(Matrix.of fun i j => bz.repr ⟨bv j, hv j⟩ i).det, ?_⟩
    rw [Basis.det_apply, Int.cast_det]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact bz.ofZLatticeBasis_repr_apply ℝ L ⟨bv j, hv j⟩ i
  obtain ⟨k, hk⟩ := hk
  have hprod : bv.det b' * b'.det bv = 1 := by
    rw [Basis.det_mul_det, Basis.det_self]
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [hk] at hprod
  have hdet : |bv.det b'| ≤ 1 := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have h2 : |bv.det b'| * |(k : ℝ)| = 1 := by rw [← abs_mul, ← hk, hprod, abs_one]
    nlinarith [abs_nonneg (bv.det b')]
  rw [ZLattice.covolume_eq_det_mul_measureReal L μ bz bv, hb',
    measureReal_congr (fundamentalDomain_ae_parallelepiped bv μ)]
  calc |bv.det b'| * μ.real (parallelepiped bv) ≤ 1 * μ.real (parallelepiped bv) := by
        gcongr
    _ = μ.real (parallelepiped bv) := one_mul _

end Formalism.FN.LowerVolumeBound
