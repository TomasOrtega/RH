import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceB

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

/- English proof (translation)
Establish `hA' : A * lam ≤ m ^ 2` using `by rwa [le_div_iff₀ hlam] at hA`. Establish `hN' : N * lam ≤ m + 1` using `by rwa [le_div_iff₀ hlam] at hN`. Establish `h1 : (A * lam) ^ 2 ≤ (m ^ 2) ^ 2` using `pow_le_pow_left₀ (by positivity) hA' 2`. Establish `hBN : Bt * (N * lam) ≤ 1 / 2 * (m + 1)` using `mul_le_mul hBt hN' (by positivity) (by norm_num)`. Establish `h2 : (Bt * (N * lam)) ^ 2 ≤ (1 / 2 * (m + 1)) ^ 2` using `pow_le_pow_left₀ (by positivity) hBN 2`.

Establish `h3 : (m ^ 2) ^ 2 + (1 / 2 * (m + 1)) ^ 2 ≤ ((m + 1) ^ 2) ^ 2`. Use polynomial arithmetic with `[pow_nonneg hm 3, sq_nonneg m, hm]`. Rewrite using `[div_pow, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gtE_bound (m lam A Bt N : ℝ) (hm : 0 ≤ m) (hlam : 0 < lam) (hA0 : 0 ≤ A)
    (hA : A ≤ m ^ 2 / lam) (hB0 : 0 ≤ Bt) (hBt : Bt ≤ 1 / 2) (hN0 : 0 ≤ N)
    (hN : N ≤ (m + 1) / lam) : A ^ 2 + (Bt * N) ^ 2 ≤ ((m + 1) ^ 2 / lam) ^ 2 := by
  have hA' : A * lam ≤ m ^ 2 := by rwa [le_div_iff₀ hlam] at hA
  have hN' : N * lam ≤ m + 1 := by rwa [le_div_iff₀ hlam] at hN
  have h1 : (A * lam) ^ 2 ≤ (m ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hA' 2
  have hBN : Bt * (N * lam) ≤ 1 / 2 * (m + 1) :=
    mul_le_mul hBt hN' (by positivity) (by norm_num)
  have h2 : (Bt * (N * lam)) ^ 2 ≤ (1 / 2 * (m + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hBN 2
  have h3 : (m ^ 2) ^ 2 + (1 / 2 * (m + 1)) ^ 2 ≤ ((m + 1) ^ 2) ^ 2 := by
    nlinarith [pow_nonneg hm 3, sq_nonneg m, hm]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (A ^ 2 + (Bt * N) ^ 2) * lam ^ 2 = (A * lam) ^ 2 + (Bt * (N * lam)) ^ 2 := by ring
    _ ≤ ((m + 1) ^ 2) ^ 2 := by linarith

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hv`. Use `choose f hf using h`. Use `⟨∑ j, c j * f j, ?_⟩` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hf j]`.
-/
private theorem exists_int_inner_of_mem_span_int' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (y : E) (h : ∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) (v : E)
    (hv : v ∈ span ℤ (Set.range b)) : ∃ m : ℤ, inner ℝ y v = m := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  choose f hf using h
  refine ⟨∑ j, c j * f j, ?_⟩
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hf j]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `b lam hlam hmin`. Conclude with `⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩`. Consider the case `succ m ih`.

Introduce `b lam hlam hmin`. Take `⟨y1, hy1, hint1, hy1n⟩` from `gtB_dual_short (Nat.succ_pos m) b lam hlam hmin`. Take `⟨y0, xu, hxu, hy0, hint0, hy0n, h01⟩` from `gtC_prim b y1 hy1 hint1`. Take `⟨bW, hWL, hproj⟩` from `gtD_lat b y0 xu hy0 hxu h01 hint0`. Establish `hfin : Module.finrank ℝ (ℝ ∙ y0)ᗮ = m`.

Rewrite using `[Module.finrank_eq_card_basis bW, Fintype.card_fin]`. Use `set φ : (ℝ ∙ y0)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) := ((stdOrthonormalBasis ℝ (ℝ ∙ y0)ᗮ).reindex (finCongr hfin)).repr with hφ`. Use `set bE : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) := bW.map φ.toLinearEquiv with hbEdef`. Establish `hbE : ∀ j, bE j = φ (bW j)` using `fun j ↦ rfl`. Establish `hspanφ : ∀ p : (ℝ ∙ y0)ᗮ, p ∈ span ℤ (Set.range bW) → φ p ∈ span ℤ (Set.range bE)`.

Introduce `p hp`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hp`. Use `(Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hbE]`.

Establish `hspanφ' : ∀ x, x ∈ span ℤ (Set.range bE) → φ.symm x ∈ span ℤ (Set.range bW)`. Introduce `x hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx`. Use `(Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ ↦ by`. Rewrite using `[map_zsmul, hbE, LinearIsometryEquiv.symm_apply_apply]`. Establish `hminE : ∀ x ∈ span ℤ (Set.range bE), x ≠ 0 → lam ≤ ‖x‖`. Introduce `x hx hx0`. Establish `h1` using `hmin _ (hWL _ (hspanφ' x hx)) (by`.

Introduce `h`. Apply `hx0` to reduce the goal to its premises. Establish `h2 : φ.symm x = 0` using `Subtype.ext h`. Simplify using `using congrArg φ h2)`. Conclude with `h1.trans (le_of_eq (φ.symm.norm_map x))`.

Take `⟨z, hzli, hzint, hzn⟩` from `ih bE lam hlam hminE`. Use `set w : Fin m → EuclideanSpace ℝ (Fin (m + 1)) := fun i ↦ ((φ.symm (z i) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) with hw`. Establish `hwy0 : ∀ i, inner ℝ y0 (w i) = 0` using `fun i ↦ Submodule.mem_orthogonal_singleton_iff_inner_right.mp (φ.symm (z i)).2`. Establish `hwn : ∀ i, ‖w i‖ = ‖z i‖` using `fun i ↦ φ.symm.norm_map (z i)`. Establish `hwli : LinearIndependent ℝ w` using `(hzli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker).map' (ℝ ∙ y0)ᗮ.subtype (Submodule.ker_subtype _)`.

Use `set u : Fin m → EuclideanSpace ℝ (Fin (m + 1)) := fun i ↦ w i - (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) • y0 with hu`. Use `⟨Fin.cons y0 u, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hg`. Establish `hexp : ∑ i : Fin m, g i.succ • u i = ∑ i : Fin m, g i.succ • w i - (∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) • y0`. Simplify using `only [hu, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]`. Rewrite `hg` using `[hexp]`. Establish `hin` using `congrArg (fun v ↦ inner ℝ y0 v) hg`.

Simplify using `only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right, hwy0, mul_zero, Finset.sum_const_zero, inner_zero_right, real_inner_self_eq_norm_sq] at hin`. Establish `hy0sq : ‖y0‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.mpr hy0)`. Establish `hg0 : g 0 = ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))`. Establish `h3 : (g 0 - ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) * ‖y0‖ ^ 2 = 0` using `by linear_combination hin`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h hy0sq`. Establish `hX : ∑ i : Fin m, g i.succ • w i = 0`. Establish `h4` using `hg`. Rewrite `h4` using `[hg0]`.

Simplify using `using h4`. Establish `hsucc : ∀ i : Fin m, g i.succ = 0` using `Fintype.linearIndependent_iff.mp hwli _ hX`. Introduce `i`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => rw [hg0]`.

Simplify using `[hsucc]`. Consider the case `succ k => exact hsucc k`. Introduce `i j`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => simpa using hint0 j`.

Consider the case `succ k`. Simplify using `only [Fin.cons_succ]`. Take `⟨p, hp, hpeq⟩` from `hproj (b j) (Submodule.subset_span ⟨j, rfl⟩)`. Take `⟨k0, hk0⟩` from `hint0 j`. Take `⟨mp, hmp⟩` from `exists_int_inner_of_mem_span_int' bE (z k) (hzint k) (φ p) (hspanφ p hp)`.

Use `⟨mp + k0 * round (inner ℝ (w k) xu), ?_⟩` and prove the remaining obligations. Establish `hb : b j = (p : EuclideanSpace ℝ (Fin (m + 1))) + inner ℝ y0 (b j) • xu`. Rewrite using `[hpeq]`. Normalize the expressions using the abelian group laws. Establish `hwp : inner ℝ (w k) (p : EuclideanSpace ℝ (Fin (m + 1))) = inner ℝ (z k) (φ p)` using `by show inner ℝ ((φ.symm (z k) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) (p : EuclideanSpace ℝ (Fin (m + 1))) = _`.

Rewrite using `[← Submodule.coe_inner, ← φ.inner_map_map, LinearIsometryEquiv.apply_symm_apply]`. Establish `h1 : inner ℝ (w k) (b j) = mp + k0 * inner ℝ (w k) xu` using `by conv_lhs => rw [hb]`. Rewrite using `[inner_add_right, real_inner_smul_right, hk0, hwp, hmp]`. Establish `h2 : inner ℝ (u k) (b j) = inner ℝ (w k) (b j) - (inner ℝ (w k) xu - round (inner ℝ (w k) xu)) * inner ℝ y0 (b j)`. Simplify using `only [hu, inner_sub_left, real_inner_smul_left]`.

Rewrite using `[h2, h1, hk0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Establish `h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)`.

Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Simplify using `only [Fin.cons_zero]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `succ k`.

Simplify using `only [Fin.cons_succ]`. Establish `hc' : |inner ℝ (w k) xu - round (inner ℝ (w k) xu)| ≤ 1 / 2` using `abs_sub_round _`. Establish `hwy0' : inner ℝ (w k) y0 = 0` using `by rw [real_inner_comm]; exact hwy0 k`. Establish `hsq : ‖u k‖ ^ 2 = ‖w k‖ ^ 2 + (|inner ℝ (w k) xu - round (inner ℝ (w k) xu)| * ‖y0‖) ^ 2`. Simplify using `only [hu]`.

Rewrite using `[norm_sub_sq_real, real_inner_smul_right, hwy0', norm_smul, Real.norm_eq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ‖w k‖ ≤ (m : ℝ) ^ 2 / lam` using `by rw [hwn]; exact hzn k`. Establish `hN : ‖y0‖ ≤ ((m : ℝ) + 1) / lam`. Use `hy0n.trans hy1n` as an intermediate fact.

Simplify using `using this`. Establish `hbd` using `gtE_bound m lam ‖w k‖ _ ‖y0‖ (Nat.cast_nonneg m) hlam (norm_nonneg _) hA (abs_nonneg _) hc' (norm_nonneg _) hN`. Rewrite `hbd` using `[← hsq]`. Establish `h5 : ‖u k‖ ≤ ((m : ℝ) + 1) ^ 2 / lam` using `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd`. Simplify using `using h5`.
-/
theorem gtE_main (n : ℕ) : ∀ (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : ℝ), 0 < lam →
    (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) →
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam := by
  induction n with
  | zero =>
    intro b lam hlam hmin
    exact ⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    intro b lam hlam hmin
    classical
    obtain ⟨y1, hy1, hint1, hy1n⟩ := gtB_dual_short (Nat.succ_pos m) b lam hlam hmin
    obtain ⟨y0, xu, hxu, hy0, hint0, hy0n, h01⟩ := gtC_prim b y1 hy1 hint1
    obtain ⟨bW, hWL, hproj⟩ := gtD_lat b y0 xu hy0 hxu h01 hint0
    have hfin : Module.finrank ℝ (ℝ ∙ y0)ᗮ = m := by
      rw [Module.finrank_eq_card_basis bW, Fintype.card_fin]
    set φ : (ℝ ∙ y0)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((stdOrthonormalBasis ℝ (ℝ ∙ y0)ᗮ).reindex (finCongr hfin)).repr with hφ
    set bE : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) := bW.map φ.toLinearEquiv with hbEdef
    have hbE : ∀ j, bE j = φ (bW j) := fun j ↦ rfl
    have hspanφ : ∀ p : (ℝ ∙ y0)ᗮ, p ∈ span ℤ (Set.range bW) → φ p ∈ span ℤ (Set.range bE) := by
      intro p hp
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hbE]
    have hspanφ' : ∀ x, x ∈ span ℤ (Set.range bE) → φ.symm x ∈ span ℤ (Set.range bW) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_zsmul, hbE, LinearIsometryEquiv.symm_apply_apply]
    have hminE : ∀ x ∈ span ℤ (Set.range bE), x ≠ 0 → lam ≤ ‖x‖ := by
      intro x hx hx0
      have h1 := hmin _ (hWL _ (hspanφ' x hx)) (by
        intro h
        apply hx0
        have h2 : φ.symm x = 0 := Subtype.ext h
        simpa using congrArg φ h2)
      exact h1.trans (le_of_eq (φ.symm.norm_map x))
    obtain ⟨z, hzli, hzint, hzn⟩ := ih bE lam hlam hminE
    set w : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ ((φ.symm (z i) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) with hw
    have hwy0 : ∀ i, inner ℝ y0 (w i) = 0 := fun i ↦
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (φ.symm (z i)).2
    have hwn : ∀ i, ‖w i‖ = ‖z i‖ := fun i ↦ φ.symm.norm_map (z i)
    have hwli : LinearIndependent ℝ w :=
      (hzli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker).map'
        (ℝ ∙ y0)ᗮ.subtype (Submodule.ker_subtype _)
    set u : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ w i - (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) • y0 with hu
    refine ⟨Fin.cons y0 u, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hexp : ∑ i : Fin m, g i.succ • u i = ∑ i : Fin m, g i.succ • w i -
          (∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) • y0 := by
        simp only [hu, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
      rw [hexp] at hg
      have hin := congrArg (fun v ↦ inner ℝ y0 v) hg
      simp only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right, hwy0,
        mul_zero, Finset.sum_const_zero, inner_zero_right, real_inner_self_eq_norm_sq] at hin
      have hy0sq : ‖y0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy0)
      have hg0 : g 0 = ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) := by
        have h3 : (g 0 - ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) *
            ‖y0‖ ^ 2 = 0 := by linear_combination hin
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · exact absurd h hy0sq
      have hX : ∑ i : Fin m, g i.succ • w i = 0 := by
        have h4 := hg
        rw [hg0] at h4
        simpa using h4
      have hsucc : ∀ i : Fin m, g i.succ = 0 := Fintype.linearIndependent_iff.mp hwli _ hX
      intro i
      cases i using Fin.cases with
      | zero => rw [hg0]; simp [hsucc]
      | succ k => exact hsucc k
    · intro i j
      cases i using Fin.cases with
      | zero => simpa using hint0 j
      | succ k =>
        simp only [Fin.cons_succ]
        obtain ⟨p, hp, hpeq⟩ := hproj (b j) (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨k0, hk0⟩ := hint0 j
        obtain ⟨mp, hmp⟩ := exists_int_inner_of_mem_span_int' bE (z k) (hzint k) (φ p) (hspanφ p hp)
        refine ⟨mp + k0 * round (inner ℝ (w k) xu), ?_⟩
        have hb : b j = (p : EuclideanSpace ℝ (Fin (m + 1))) + inner ℝ y0 (b j) • xu := by
          rw [hpeq]; abel
        have hwp : inner ℝ (w k) (p : EuclideanSpace ℝ (Fin (m + 1))) = inner ℝ (z k) (φ p) := by
          show inner ℝ ((φ.symm (z k) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1)))
            (p : EuclideanSpace ℝ (Fin (m + 1))) = _
          rw [← Submodule.coe_inner, ← φ.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
        have h1 : inner ℝ (w k) (b j) = mp + k0 * inner ℝ (w k) xu := by
          conv_lhs => rw [hb]
          rw [inner_add_right, real_inner_smul_right, hk0, hwp, hmp]
        have h2 : inner ℝ (u k) (b j) = inner ℝ (w k) (b j) -
            (inner ℝ (w k) xu - round (inner ℝ (w k) xu)) * inner ℝ y0 (b j) := by
          simp only [hu, inner_sub_left, real_inner_smul_left]
        rw [h2, h1, hk0]
        push_cast
        ring
    · intro i
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        calc ‖y0‖ ≤ ‖y1‖ := hy0n
          _ ≤ ((m + 1 : ℕ) : ℝ) / lam := hy1n
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / lam := by gcongr; exact le_self_pow₀ h1 two_ne_zero
      | succ k =>
        simp only [Fin.cons_succ]
        have hc' : |inner ℝ (w k) xu - round (inner ℝ (w k) xu)| ≤ 1 / 2 := abs_sub_round _
        have hwy0' : inner ℝ (w k) y0 = 0 := by rw [real_inner_comm]; exact hwy0 k
        have hsq : ‖u k‖ ^ 2 = ‖w k‖ ^ 2 +
            (|inner ℝ (w k) xu - round (inner ℝ (w k) xu)| * ‖y0‖) ^ 2 := by
          simp only [hu]
          rw [norm_sub_sq_real, real_inner_smul_right, hwy0', norm_smul, Real.norm_eq_abs]
          ring
        have hA : ‖w k‖ ≤ (m : ℝ) ^ 2 / lam := by rw [hwn]; exact hzn k
        have hN : ‖y0‖ ≤ ((m : ℝ) + 1) / lam := by
          have := hy0n.trans hy1n
          simpa using this
        have hbd := gtE_bound m lam ‖w k‖ _ ‖y0‖ (Nat.cast_nonneg m) hlam (norm_nonneg _) hA
          (abs_nonneg _) hc' (norm_nonneg _) hN
        rw [← hsq] at hbd
        have h5 : ‖u k‖ ≤ ((m : ℝ) + 1) ^ 2 / lam :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd
        simpa using h5

/- English proof (translation)
The claim follows from `gtE_main n b lam hlam hmin`.
-/
theorem transference_dual {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam :=
  gtE_main n b lam hlam hmin

end ReciprocityTheory.ChartRestriction.G.T0
