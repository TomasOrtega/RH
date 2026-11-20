import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionSupport
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFFour

open Ad3 Ad3.LFS Topology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hU`. Establish `ht' : ∀ i, t i ∈ 𝓝 (0 : F)` using `fun i ↦ by simpa using ht i`. Use `choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)`. Take `⟨N, hN⟩` from `(Finset.univ.image n).exists_le`.

Use `⟨N, fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩` and prove the remaining obligations. Conclude with `valBall_antitone (hN _ (Finset.mem_image_of_mem n (Finset.mem_univ i))) (hx i)`.
-/
theorem exists_ball_subset {ι : Type} [Fintype ι] {U : Set (ι → F)} (hU : U ∈ 𝓝 (0 : ι → F)) :
    ∃ n : ℤ, ∀ x : ι → F, (∀ i, x i ∈ valBall F n) → x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have ht' : ∀ i, t i ∈ 𝓝 (0 : F) := fun i ↦ by simpa using ht i
  choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)
  obtain ⟨N, hN⟩ := (Finset.univ.image n).exists_le
  refine ⟨N, fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩
  exact valBall_antitone (hN _ (Finset.mem_image_of_mem n (Finset.mem_univ i))) (hx i)

def bx (ι : Type) (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) : Set (ι → F) :=
  Set.pi Set.univ fun _ ↦ (valBall F n : Set F)

/- English proof (translation)
Simplify using `[bx, Set.mem_univ_pi]`.
-/
theorem mem_bx {ι : Type} {n : ℤ} {x : ι → F} : x ∈ bx ι F n ↔ ∀ i, x i ∈ valBall F n := by
  simp [bx, Set.mem_univ_pi]

/- English proof (translation)
The claim follows from `isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n`.
-/
theorem isOpen_bx {ι : Type} [Fintype ι] (n : ℤ) : IsOpen (bx ι F n) :=
  isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ bx ι F (-(m : ℤ)) := by`. Use `hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ bx ι F (-(m : ℤ))) (fun m ↦ isOpen_bx _) ?_ ?_` and prove the remaining obligations. Introduce `x _`. Simplify using `only [Set.mem_iUnion]`. Use `choose a ha using fun i ↦ exists_mem_valBall_neg_nat (x i)`.

Use `⟨Finset.univ.sup a, mem_bx.2 fun i ↦ valBall_antitone ?_ (ha i)⟩` and prove the remaining obligations. Establish `: a i ≤ Finset.univ.sup a` using `Finset.le_sup (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Conclude with `Monotone.directed_le fun a b hab x hx ↦ mem_bx.2 fun i ↦ valBall_antitone (by omega) (mem_bx.1 hx i)`. Establish `hloc : ∀ x : ι → F, ∃ n : ℤ, ∀ h, (∀ i, h i ∈ valBall F n) → Φ (x + h) = Φ x`.

Introduce `x`. Establish `ho : IsOpen {h : ι → F | Φ (x + h) = Φ x}` using `(hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)`. Take `⟨n, hn⟩` from `exists_ball_subset (ho.mem_nhds (by simp))`. Conclude with `⟨n, fun h hh ↦ hn h hh⟩`. Use `choose n hn using hloc`.

Take `⟨t, -, ht⟩` from `hcs.isCompact.elim_nhds_subcover (fun x ↦ {z : ι → F | z - x ∈ bx ι F (n x)}) (fun x _ ↦ ((isOpen_bx _).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [mem_bx, zero_mem]))`. Take `⟨N₀, hN⟩` from `(t.image n).exists_le`. Establish `hval : ∀ y ∈ tsupport Φ, ∀ h, (∀ i, h i ∈ valBall F N₀) → Φ (y + h) = Φ y`. Introduce `y hy h hh`. Use `ht hy` as an intermediate fact.

Simplify using `only [Set.mem_iUnion] at this`. Take `⟨x, hxt, hyx⟩` from `this`. Establish `hyx'` using `mem_bx.1 hyx`. Establish `hN' : ∀ i, h i ∈ valBall F (n x)` using `fun i ↦ valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt)) (hh i)`. Establish `e1 : Φ y = Φ x`.

Use `hn x (y - x) hyx'` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `e2 : Φ (y + h) = Φ x`. Use `hn x (y + h - x) (fun i ↦ by` as an intermediate fact. Rewrite using `[show (y + h - x) i = (y - x) i + h i by simp; abel]`.

Conclude with `add_mem (hyx' i) (hN' i))`. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[e1, e2]`. Use `⟨N₀, -(m : ℤ), fun y h hh ↦ ?_, fun x hx ↦ mem_bx.1 (hm (subset_tsupport Φ hx))⟩` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ tsupport Φ`.

Conclude with `hval y hy h hh`. Distinguish the cases in `hyh : y + h ∈ tsupport Φ`. Use `hval (y + h) hyh (-h) (fun i ↦ by simpa using neg_mem (hh i))` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`. Conclude with `this.symm`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]`.
-/
theorem exists_invariant {ι : Type} [Fintype ι] {Φ : (ι → F) → ℂ} (hlc : IsLocallyConstant Φ)
    (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ x h, (∀ i, h i ∈ valBall F N) → Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → ∀ i, x i ∈ valBall F M := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ bx ι F (-(m : ℤ)) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ bx ι F (-(m : ℤ)))
      (fun m ↦ isOpen_bx _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      choose a ha using fun i ↦ exists_mem_valBall_neg_nat (x i)
      refine ⟨Finset.univ.sup a, mem_bx.2 fun i ↦ valBall_antitone ?_ (ha i)⟩
      have : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
      omega
    · exact Monotone.directed_le fun a b hab x hx ↦
        mem_bx.2 fun i ↦ valBall_antitone (by omega) (mem_bx.1 hx i)
  have hloc : ∀ x : ι → F, ∃ n : ℤ, ∀ h, (∀ i, h i ∈ valBall F n) → Φ (x + h) = Φ x := by
    intro x
    have ho : IsOpen {h : ι → F | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_ball_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh ↦ hn h hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x ↦ {z : ι → F | z - x ∈ bx ι F (n x)})
    (fun x _ ↦ ((isOpen_bx _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp [mem_bx, zero_mem]))
  obtain ⟨N₀, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport Φ, ∀ h, (∀ i, h i ∈ valBall F N₀) → Φ (y + h) = Φ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hyx' := mem_bx.1 hyx
    have hN' : ∀ i, h i ∈ valBall F (n x) := fun i ↦
      valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt)) (hh i)
    have e1 : Φ y = Φ x := by
      have := hn x (y - x) hyx'
      rwa [add_sub_cancel] at this
    have e2 : Φ (y + h) = Φ x := by
      have := hn x (y + h - x) (fun i ↦ by
        rw [show (y + h - x) i = (y - x) i + h i by simp; abel]
        exact add_mem (hyx' i) (hN' i))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N₀, -(m : ℤ), fun y h hh ↦ ?_, fun x hx ↦ mem_bx.1 (hm (subset_tsupport Φ hx))⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) (fun i ↦ by simpa using neg_mem (hh i))
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

def mh : (Fin 2 × Fin 3 → F) ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun f := Matrix.of fun i j ↦ f (i, j)
  invFun X p := X p.1 p.2
  left_inv f := rfl
  right_inv X := rfl
  continuous_toFun := continuous_matrix fun i j ↦ continuous_apply (i, j)
  continuous_invFun := continuous_pi fun p ↦ continuous_id.matrix_elem p.1 p.2

/- English proof (translation)
Take `⟨N, M, h1, h2⟩` from `exists_invariant (Φ := Φ ∘ (mh (F := F))) (hlc.comp_continuous (mh (F := F)).continuous) (hcs.comp_homeomorph (mh (F := F)))`. Use `⟨N, M, fun X Y hY ↦ ?_, fun X hX a b ↦ ?_⟩` and prove the remaining obligations. Conclude with `h1 (mh.symm X) (mh.symm Y) (fun p ↦ hY p.1 p.2)`. Conclude with `h2 (mh.symm X) (by simpa using hX) (a, b)`.
-/
theorem exists_invariant_matrix {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X) ∧
      ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M := by
  obtain ⟨N, M, h1, h2⟩ := exists_invariant (Φ := Φ ∘ (mh (F := F)))
    (hlc.comp_continuous (mh (F := F)).continuous) (hcs.comp_homeomorph (mh (F := F)))
  refine ⟨N, M, fun X Y hY ↦ ?_, fun X hX a b ↦ ?_⟩
  · exact h1 (mh.symm X) (mh.symm Y) (fun p ↦ hY p.1 p.2)
  · exact h2 (mh.symm X) (by simpa using hX) (a, b)

/- English proof (translation)
Establish `hq : (1 : ℝ) ≤ residueCard F` using `by exact_mod_cast one_lt_residueCard.le`. Distinguish the cases in `h0 : x = 0`. Substitute `h0` using the available equality. Simplify using `only [modulus_zero, NNReal.coe_zero]`. Check the signs of the components of the expression.

Rewrite using `[modulus_of_ne_zero h0, NNReal.coe_zpow, NNReal.coe_natCast]`. Conclude with `zpow_le_zpow_right₀ hq (by have := (mem_valBall_iff_le_ord h0).mp hx; omega)`.
-/
theorem modulus_le_zpow_of_mem {M : ℤ} {x : F} (hx : x ∈ valBall F M) :
    (GroundTheory.LocalField.modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (-M) := by
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  by_cases h0 : x = 0
  · subst h0
    simp only [modulus_zero, NNReal.coe_zero]
    positivity
  rw [modulus_of_ne_zero h0, NNReal.coe_zpow, NNReal.coe_natCast]
  exact zpow_le_zpow_right₀ hq (by have := (mem_valBall_iff_le_ord h0).mp hx; omega)

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [col3]`.
-/
theorem column_three_add (k : Matrix (Fin 2) (Fin 2) F) (y e : Fin 2 → F) :
    col3 k (y + e) = col3 k y + col3 0 e := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [col3]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> simp [col3]`.
-/
theorem three_column_matrix_last (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a : Fin 2) :
    col3 k y a 2 = y a := by
  fin_cases a <;> simp [col3]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [col3]`.
-/
theorem three_column_matrix_left (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a b : Fin 2) :
    col3 k y a b.castSucc = k a b := by
  fin_cases a <;> fin_cases b <;> simp [col3]

/- English proof (translation)
Establish `h0 : (0 : F) ∈ valBall F N` using `zero_mem _`. Establish `h1` using `he 0`. Establish `h2` using `he 1`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simpa [col3] using (by assumption)`.
-/
theorem three_column_zero_mem_ball {N : ℤ} (e : Fin 2 → F) (he : ∀ a, e a ∈ valBall F N) (a : Fin 2) (b : Fin 3) :
    col3 (0 : Matrix (Fin 2) (Fin 2) F) e a b ∈ valBall F N := by
  have h0 : (0 : F) ∈ valBall F N := zero_mem _
  have h1 := he 0
  have h2 := he 1
  fin_cases a <;> fin_cases b <;> simpa [col3] using (by assumption)

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hv : (vol2 ψ).IsAddHaarMeasure` using `by unfold vol2; infer_instance`. Establish `hmem : ∀ a b, col3 (0 : Matrix (Fin 2) (Fin 2) F) (Pi.single j c) a b ∈ valBall F N` using `three_column_zero_mem_ball _ fun a ↦ by`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `hc`.

Conclude with `zero_mem _`. Establish `h` using `integral_add_right_eq_self (μ := vol2 ψ) (fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) (Pi.single j c)`. Unfold `pft`. Rewrite using `[← integral_const_mul, ← h]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)` and prove the remaining obligations.

Establish `e1 : ∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i = ∑ i, ξ i * y i + ξ j * c`. Simplify using `[mul_add, Finset.sum_add_distrib, Pi.single_apply]`. Use `show Φ (col3 k (y + (Pi.single j c : Fin 2 → F))) * (ψ (-(∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i)) : ℂ) = _`. Rewrite using `[column_three_add, hinv _ _ hmem, e1, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pft_eq_mul (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {N : ℤ}
    (hinv : ∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) (j : Fin 2) {c : F} (hc : c ∈ valBall F N) :
    pft ψ Φ k ξ = (ψ (-(ξ j * c)) : ℂ) * pft ψ Φ k ξ := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hmem : ∀ a b, col3 (0 : Matrix (Fin 2) (Fin 2) F) (Pi.single j c) a b ∈ valBall F N :=
    three_column_zero_mem_ball _ fun a ↦ by
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
  have h := integral_add_right_eq_self (μ := vol2 ψ)
    (fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) (Pi.single j c)
  unfold pft
  rw [← integral_const_mul, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  have e1 : ∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i = ∑ i, ξ i * y i + ξ j * c := by
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  show Φ (col3 k (y + (Pi.single j c : Fin 2 → F))) *
    (ψ (-(∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i)) : ℂ) = _
  rw [column_three_add, hinv _ _ hmem, e1, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/- English proof (translation)
Establish `hv : (vol2 ψ).IsAddHaarMeasure` using `by unfold vol2; infer_instance`. Establish `hS : MeasurableSet (bx (Fin 2) F M)` using `MeasurableSet.univ_pi fun _ ↦ (isClosed_valBall M).measurableSet`. Establish `hfin : vol2 ψ (bx (Fin 2) F M) ≠ ⊤` using `(IsCompact.measure_lt_top (isCompact_univ_pi fun _ ↦ isCompact_valBall M)).ne`. Establish `hint : Integrable ((bx (Fin 2) F M).indicator fun _ ↦ B) (vol2 ψ)` using `(integrable_indicator_iff hS).2 (integrableOn_const hfin)`. Use `norm_integral_le_of_norm_le (μ := vol2 ψ) (f := fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) hint (Filter.Eventually.of_forall fun y ↦ ?_)` as an intermediate fact.

Rewrite `this` using `[integral_indicator_const _ hS, smul_eq_mul]`. Conclude with `this`. Rewrite using `[norm_mul, Circle.norm_coe, mul_one]`. Distinguish the cases in `hy : y ∈ bx (Fin 2) F M`. Rewrite using `[Set.indicator_of_mem hy]`.

Conclude with `hB _`. Rewrite using `[Set.indicator_of_notMem hy]`. Distinguish the cases in `h0 : Φ (col3 k y) = 0`. Simplify using `[h0]`. Conclude with `absurd (mem_bx.2 fun a ↦ by`.

Simplify `hs _ h0 a 2) hy` using `[three_column_matrix_last]`.
-/
theorem norm_pft_le (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {M : ℤ} {B : ℝ}
    (hB : ∀ X, ‖Φ X‖ ≤ B) (hs : ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) :
    ‖pft ψ Φ k ξ‖ ≤ (vol2 ψ).real (bx (Fin 2) F M) * B := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hS : MeasurableSet (bx (Fin 2) F M) :=
    MeasurableSet.univ_pi fun _ ↦ (isClosed_valBall M).measurableSet
  have hfin : vol2 ψ (bx (Fin 2) F M) ≠ ⊤ :=
    (IsCompact.measure_lt_top (isCompact_univ_pi fun _ ↦ isCompact_valBall M)).ne
  have hint : Integrable ((bx (Fin 2) F M).indicator fun _ ↦ B) (vol2 ψ) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hfin)
  have := norm_integral_le_of_norm_le (μ := vol2 ψ)
    (f := fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) hint
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · rw [integral_indicator_const _ hS, smul_eq_mul] at this
    exact this
  · rw [norm_mul, Circle.norm_coe, mul_one]
    by_cases hy : y ∈ bx (Fin 2) F M
    · rw [Set.indicator_of_mem hy]
      exact hB _
    · rw [Set.indicator_of_notMem hy]
      by_cases h0 : Φ (col3 k y) = 0
      · simp [h0]
      · exact absurd (mem_bx.2 fun a ↦ by
          simpa [three_column_matrix_last] using hs _ h0 a 2) hy

end GlobalTheory.CompanionTheory.LFFour

open GlobalTheory.CompanionTheory.LFFour in

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ Φ hΦ`. Take `⟨N, M, hinv, hsupp⟩` from `exists_invariant_matrix hΦ.1 hΦ.2`. Take `⟨B, hB⟩` from `hΦ.2.exists_bound_of_continuous hΦ.1.continuous`. Take `⟨hc, h1, h0⟩` from `hψ`. Establish `hnot` using `not_isTrivialOn_addCharConductor_sub_one hc h1`.

Rewrite `hnot` using `[h0]`. Simplify using `only [IsTrivialOn, not_forall] at hnot`. Take `⟨y, hy, hy1⟩` from `hnot`. Establish `hy' : y ∈ valBall F (-1)` using `by simpa using hy`. Use `⟨(Ad3.LFS.vol2 ψ).real (bx (Fin 2) F M) * B, max ((residueCard F : ℝ) ^ (-M)) (((residueCard F : NNReal) ^ (N + 1) : NNReal) : ℝ), fun k ξ ↦ ⟨norm_pft_le ψ hB hsupp k ξ, fun hne ↦ ⟨fun i j ↦ ?_, fun j ↦ ?_⟩⟩⟩` and prove the remaining obligations.

Establish `hex : ∃ y, Φ (Ad3.LFS.col3 k y) ≠ 0`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hne (by simp [Ad3.LFS.pft, hno])`. Take `⟨z, hz⟩` from `hex`.

Use `hsupp _ hz i j.castSucc` as an intermediate fact. Rewrite `this` using `[three_column_matrix_left]`. Conclude with `(modulus_le_zpow_of_mem this).trans (le_max_left _ _)`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Distinguish the cases in `hξ : ξ j = 0`.

Simplify using `[hξ]`. Check the signs of the components of the expression. Use `NNReal.coe_le_coe.mpr (GlobalTheory.CompanionTheory.LFSupp.modulus_le_of_trivial hy' hy1 (Units.mk0 (ξ j) hξ) fun x hx ↦ ?_)` and prove the remaining obligations. Establish `e` using `pft_eq_mul ψ hinv k ξ j (neg_mem hx)`. Establish `e2 : (ψ (-(ξ j * -x)) : ℂ) = 1` using `mul_right_cancel₀ hne (by rw [← e, one_mul])`.

Establish `e3` using `Circle.coe_eq_one.mp e2`. Simplify using `using e3`.
-/
theorem GlobalTheory.CompanionTheory.LFFour.gFour : Ad3.LFS.GFour := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨N, M, hinv, hsupp⟩ := exists_invariant_matrix hΦ.1 hΦ.2
  obtain ⟨B, hB⟩ := hΦ.2.exists_bound_of_continuous hΦ.1.continuous
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(Ad3.LFS.vol2 ψ).real (bx (Fin 2) F M) * B,
    max ((residueCard F : ℝ) ^ (-M))
      (((residueCard F : NNReal) ^ (N + 1) : NNReal) : ℝ),
    fun k ξ ↦ ⟨norm_pft_le ψ hB hsupp k ξ, fun hne ↦ ⟨fun i j ↦ ?_, fun j ↦ ?_⟩⟩⟩
  · have hex : ∃ y, Φ (Ad3.LFS.col3 k y) ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hne (by simp [Ad3.LFS.pft, hno])
    obtain ⟨z, hz⟩ := hex
    have := hsupp _ hz i j.castSucc
    rw [three_column_matrix_left] at this
    exact (modulus_le_zpow_of_mem this).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    by_cases hξ : ξ j = 0
    · simp [hξ]
      positivity
    · refine NNReal.coe_le_coe.mpr
        (GlobalTheory.CompanionTheory.LFSupp.modulus_le_of_trivial hy' hy1 (Units.mk0 (ξ j) hξ) fun x hx ↦ ?_)
      have e := pft_eq_mul ψ hinv k ξ j (neg_mem hx)
      have e2 : (ψ (-(ξ j * -x)) : ℂ) = 1 :=
        mul_right_cancel₀ hne (by rw [← e, one_mul])
      have e3 := Circle.coe_eq_one.mp e2
      simpa using e3
