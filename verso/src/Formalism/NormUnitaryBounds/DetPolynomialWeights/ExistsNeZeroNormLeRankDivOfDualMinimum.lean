import Formalism.NormUnitaryBounds.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector

open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Rewrite using `[discreteTopology_iff_isOpen_singleton_zero]`. Establish `hball : ({0} : Set L) = Metric.ball (0 : L) ε`. Use extensionality with `x`. Simplify using `only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Simplify using `using hε`. Introduce `hx`. Assume the negation of the conclusion as `hne`. Establish `hx0 : (x : E) ≠ 0` using `fun h0 => hne (Subtype.ext h0)`.

Use `h x x.2 hx0` as an intermediate fact. Rewrite `hx` using `[Submodule.coe_norm]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hball]`. Conclude with `Metric.isOpen_ball`.
-/
theorem discreteTopology_of_norm_ge (L : Submodule ℤ E) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ L, x ≠ 0 → ε ≤ ‖x‖) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hball : ({0} : Set L) = Metric.ball (0 : L) ε := by
    ext x
    simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have hx0 : (x : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have := h x x.2 hx0
      rw [Submodule.coe_norm] at hx
      linarith
  rw [hball]
  exact Metric.isOpen_ball

/- English proof (translation)
Use `set k := Module.finrank ℤ Q with hk`. Set `b` to `Module.finBasis ℤ Q`. Set `v : Fin k → E` to `fun i => (b i : E)`. Set `G` to `Matrix.gram ℝ v`. Establish `hcovQ : Formalism.F.covol Q = Real.sqrt G.det` using `Formalism.F.covol_eq_gram E Q (Fin k) b`.

Establish `hpos : 0 < Formalism.F.covol Q` using `Formalism.F.covol_pos' E Q hQd`. Establish `hdet : 0 < G.det` using `Real.sqrt_pos.mp (hcovQ ▸ hpos)`. Establish `hdetu : IsUnit G.det` using `hdet.ne'.isUnit`. Set `P` to `G⁻¹`. Set `w : Fin k → E` to `fun j => ∑ i, P i j • v i`.

Establish `hGP : G * P = 1` using `Matrix.mul_nonsing_inv G hdetu`. Establish `hbi : ∀ l j, inner ℝ (v l) (w j) = if l = j then 1 else 0`. Introduce `l j`. Establish `h1 : inner ℝ (v l) (w j) = (G * P) l j`. Simplify using `only [w, inner_sum, real_inner_smul_right, Matrix.mul_apply, G, Matrix.gram_apply]`.

Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`. Rewrite using `[h1, hGP, Matrix.one_apply]`. Establish `hQv : ∀ x ∈ Q, ∃ a : Fin k → ℤ, x = ∑ i, (a i : ℝ) • v i`. Introduce `x hx`. Use `⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`. Establish `h2 : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) = x` using `h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Int.cast_smul_eq_zsmul, v]`.

Apply the tactic sequence `try rfl`. Set `D` to `Submodule.span ℤ (Set.range w)`. Establish `hint : ∀ y ∈ D, ∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Introduce `x hx`. Take `⟨a, rfl⟩` from `hQv x hx`. Use `⟨a j, ?_⟩` and prove the remaining obligations.

Simplify using `only [sum_inner, real_inner_smul_left, hbi]`. Simplify using the standard rewrite rules. Consider the case `zero => exact fun x _ => ⟨0, by simp⟩`. Consider the case `add y y' _ _ h1 h2`. Introduce `x hx`.

Take `⟨z1, e1⟩` from `h1 x hx`. Take `⟨z2, e2⟩` from `h2 x hx`. Conclude with `⟨z1 + z2, by rw [inner_add_right, e1, e2]; push_cast; ring⟩`. Consider the case `smul c y _ h1`. Introduce `x hx`.

Take `⟨z1, e1⟩` from `h1 x hx`. Conclude with `⟨c * z1, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, e1]; push_cast; ring⟩`. Establish `hDV : ∀ y ∈ D, y ∈ span ℝ (Q : Set E)`. Introduce `y hy`. Establish `hle : D ≤ (span ℝ (Q : Set E)).restrictScalars ℤ`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (b i).2))`. Conclude with `hle hy`. Establish `hDl : ∀ y ∈ D, y ≠ 0 → l ≤ ‖y‖` using `fun y hy hy0 => hdual y (hDV y hy) hy0 (hint y hy)`.

Establish `hDd : DiscreteTopology D` using `discreteTopology_of_norm_ge D hl hDl`. Establish `hli : LinearIndependent ℤ w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg l`. Establish `h1` using `congrArg (fun y => inner ℝ (v l) y) hg`.

Simplify using `only [inner_sum, inner_zero_right] at h1`. Simplify using `only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbi, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1`. Conclude with `h1` after adjusting the coercions. Set `bw` to `Basis.span hli`. Establish `hcovD : Formalism.F.covol D = Real.sqrt (Matrix.gram ℝ w).det`.

Rewrite using `[Formalism.F.covol_eq_gram E D (Fin k) bw]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (Basis.span_apply hli i)`. Establish `hgw : Matrix.gram ℝ w = P.transpose * G * P` using `Formalism.F.gram_sum_smul_eq_transpose_mul v P`.

Establish `hdetw : (Matrix.gram ℝ w).det = G.det⁻¹`. Rewrite using `[hgw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Clear the denominators using the available nonvanishing facts. Establish `hrkD : Formalism.F.rk D = k`. Simplify using `only [Formalism.F.rk]`.

Rewrite using `[Module.finrank_eq_card_basis bw, Fintype.card_fin]`. Establish `hrkQ : Formalism.F.rk Q = k` using `rfl`. Establish `hkpos : 0 < k`. Establish `: Nontrivial Q` using `Submodule.nontrivial_iff_ne_bot.mpr hQ`. Conclude with `Module.finrank_pos`.

Establish `hD0 : D ≠ ⊥`. Introduce `h`. Establish `hw0 : w ⟨0, hkpos⟩ ∈ D` using `Submodule.subset_span ⟨_, rfl⟩`. Rewrite `hw0` using `[h, Submodule.mem_bot]`. Establish `h2` using `hbi ⟨0, hkpos⟩ ⟨0, hkpos⟩`.

Rewrite `h2` using `[hw0, inner_zero_right]`. Simplify using `at h2`. Take `⟨q, hqQ, hq0, hqn⟩` from `Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E Q hQd hQ`. Take `⟨y, hyD, hy0, hyn⟩` from `Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E D hDd hD0`. Use `⟨q, hqQ, hq0, ?_⟩` and prove the remaining obligations.

Establish `hly` using `hDl y hyD hy0`. Rewrite `hyn` using `[hrkD, hcovD, hdetw, Real.sqrt_inv, ← hcovQ]`. Rewrite `hqn`, the goal using `[hrkQ]`. Establish `ht : 0 < Formalism.F.covol Q ^ ((1 : ℝ) / k)` using `Real.rpow_pos_of_pos hpos _`. Rewrite `hyn` using `[Real.inv_rpow hpos.le]`.

Establish `hsk : Real.sqrt k * Real.sqrt k = k` using `Real.mul_self_sqrt (Nat.cast_nonneg k)`. Establish `h1 : l * Formalism.F.covol Q ^ ((1 : ℝ) / k) ≤ Real.sqrt k`. Establish `h2` using `hly.trans hyn`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[le_div_iff₀ hl]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_ne_zero_norm_le_rank_div_of_dualMinimum (Q : Submodule ℤ E) [hQd : DiscreteTopology Q] (hQ : Q ≠ ⊥) {l : ℝ}
    (hl : 0 < l)
    (hdual : ∀ y ∈ span ℝ (Q : Set E), y ≠ 0 →
      (∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∃ q ∈ Q, q ≠ 0 ∧ ‖q‖ ≤ (Formalism.F.rk Q : ℝ) / l := by
  classical
  set k := Module.finrank ℤ Q with hk
  let b := Module.finBasis ℤ Q
  let v : Fin k → E := fun i => (b i : E)
  let G := Matrix.gram ℝ v
  have hcovQ : Formalism.F.covol Q = Real.sqrt G.det := Formalism.F.covol_eq_gram E Q (Fin k) b
  have hpos : 0 < Formalism.F.covol Q := Formalism.F.covol_pos' E Q hQd
  have hdet : 0 < G.det := Real.sqrt_pos.mp (hcovQ ▸ hpos)
  have hdetu : IsUnit G.det := hdet.ne'.isUnit
  let P := G⁻¹
  let w : Fin k → E := fun j => ∑ i, P i j • v i
  have hGP : G * P = 1 := Matrix.mul_nonsing_inv G hdetu
  have hbi : ∀ l j, inner ℝ (v l) (w j) = if l = j then 1 else 0 := by
    intro l j
    have h1 : inner ℝ (v l) (w j) = (G * P) l j := by
      simp only [w, inner_sum, real_inner_smul_right, Matrix.mul_apply, G, Matrix.gram_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hGP, Matrix.one_apply]
  have hQv : ∀ x ∈ Q, ∃ a : Fin k → ℤ, x = ∑ i, (a i : ℝ) • v i := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    have h2 : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) = x := h1
    calc x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) := h2.symm
      _ = _ := by
        simp only [Int.cast_smul_eq_zsmul, v]
        try rfl
  let D := Submodule.span ℤ (Set.range w)
  have hint : ∀ y ∈ D, ∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      obtain ⟨a, rfl⟩ := hQv x hx
      refine ⟨a j, ?_⟩
      simp only [sum_inner, real_inner_smul_left, hbi]
      simp
    | zero => exact fun x _ => ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      obtain ⟨z2, e2⟩ := h2 x hx
      exact ⟨z1 + z2, by rw [inner_add_right, e1, e2]; push_cast; ring⟩
    | smul c y _ h1 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      exact ⟨c * z1, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, e1]; push_cast; ring⟩
  have hDV : ∀ y ∈ D, y ∈ span ℝ (Q : Set E) := by
    intro y hy
    have hle : D ≤ (span ℝ (Q : Set E)).restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (b i).2))
    exact hle hy
  have hDl : ∀ y ∈ D, y ≠ 0 → l ≤ ‖y‖ := fun y hy hy0 => hdual y (hDV y hy) hy0 (hint y hy)
  have hDd : DiscreteTopology D := discreteTopology_of_norm_ge D hl hDl
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun y => inner ℝ (v l) y) hg
    simp only [inner_sum, inner_zero_right] at h1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbi, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact_mod_cast h1
  let bw := Basis.span hli
  have hcovD : Formalism.F.covol D = Real.sqrt (Matrix.gram ℝ w).det := by
    rw [Formalism.F.covol_eq_gram E D (Fin k) bw]
    congr 3
    funext i
    exact congrArg Subtype.val (Basis.span_apply hli i)
  have hgw : Matrix.gram ℝ w = P.transpose * G * P := Formalism.F.gram_sum_smul_eq_transpose_mul v P
  have hdetw : (Matrix.gram ℝ w).det = G.det⁻¹ := by
    rw [hgw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    field_simp
  have hrkD : Formalism.F.rk D = k := by
    simp only [Formalism.F.rk]
    rw [Module.finrank_eq_card_basis bw, Fintype.card_fin]
  have hrkQ : Formalism.F.rk Q = k := rfl
  have hkpos : 0 < k := by
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact Module.finrank_pos
  have hD0 : D ≠ ⊥ := by
    intro h
    have hw0 : w ⟨0, hkpos⟩ ∈ D := Submodule.subset_span ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hw0
    have h2 := hbi ⟨0, hkpos⟩ ⟨0, hkpos⟩
    rw [hw0, inner_zero_right] at h2
    simp at h2
  obtain ⟨q, hqQ, hq0, hqn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E Q hQd hQ
  obtain ⟨y, hyD, hy0, hyn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E D hDd hD0
  refine ⟨q, hqQ, hq0, ?_⟩
  have hly := hDl y hyD hy0
  rw [hrkD, hcovD, hdetw, Real.sqrt_inv, ← hcovQ] at hyn
  rw [hrkQ] at hqn ⊢
  have ht : 0 < Formalism.F.covol Q ^ ((1 : ℝ) / k) := Real.rpow_pos_of_pos hpos _
  rw [Real.inv_rpow hpos.le] at hyn
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h1 : l * Formalism.F.covol Q ^ ((1 : ℝ) / k) ≤ Real.sqrt k := by
    have h2 := hly.trans hyn
    calc l * Formalism.F.covol Q ^ ((1 : ℝ) / k)
        ≤ Real.sqrt k * (Formalism.F.covol Q ^ ((1 : ℝ) / k))⁻¹ * Formalism.F.covol Q ^ ((1 : ℝ) / k) :=
          mul_le_mul_of_nonneg_right h2 ht.le
      _ = Real.sqrt k := by field_simp
  rw [le_div_iff₀ hl]
  calc ‖q‖ * l ≤ Real.sqrt k * Formalism.F.covol Q ^ ((1 : ℝ) / k) * l :=
        mul_le_mul_of_nonneg_right hqn hl.le
    _ = Real.sqrt k * (l * Formalism.F.covol Q ^ ((1 : ℝ) / k)) := by ring
    _ ≤ Real.sqrt k * Real.sqrt k := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = k := hsk

end Formalism.NormUnitaryCountingLemmas
