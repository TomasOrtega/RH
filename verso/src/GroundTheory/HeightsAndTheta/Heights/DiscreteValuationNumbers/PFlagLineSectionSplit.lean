import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `h : chartZ y c (b i) ∈ degLat F y (b i) c` using `⟨1, one_mem _, by simp [chartZ]⟩`. Rewrite `h` using `[← hB.graded c hc i]`. Take `⟨v, hv, h1, h2⟩` from `h`. Conclude with `⟨v, hv, h1, h2⟩`.
-/
theorem exists_adapted (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by
  have h : chartZ y c (b i) ∈ degLat F y (b i) c := ⟨1, one_mem _, by simp [chartZ]⟩
  rw [← hB.graded c hc i] at h
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, hv, h1, h2⟩

/- English proof (translation)
Establish `hlive` using `live_of_segreVec_ne_zero hc`. Use `choose e he hup hdiag using exists_adapted y B w b hB c hc`. Establish `hm : ∀ i, chartZ y c (b i) ≠ 0` using `fun i => chartZ_ne_zero hlive _`. Establish `hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e)`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `i hi`. Establish `hsum` using `w.sum_repr (e i)`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`.

Establish `hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈ Submodule.span Ω (Set.range e)`. Use `Submodule.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt` into its components or cases. Conclude with `Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)`. Rewrite using `[hup i j hgt, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Establish `hei : e i ∈ Submodule.span Ω (Set.range e)` using `Submodule.subset_span ⟨i, rfl⟩`. Establish `h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e)`. Rewrite using `[eq_sub_of_add_eq hsum]`. Conclude with `Submodule.sub_mem _ hei hrest`.

Rewrite `h1` using `[hdiag]`. Establish `h2` using `Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ (hm i), one_smul]`. Then use the resulting hypothesis. Establish `htop : ⊤ ≤ Submodule.span Ω (Set.range e)`. Rewrite using `[← w.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hspan i i rfl`. Establish `hcard : Fintype.card (Fin N) = Module.finrank Ω E`. Rewrite using `[Module.finrank_eq_card_basis w]`. Use `set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def`.

Establish `heb : ∀ i, eb i = e i` using `fun i => by`. Rewrite using `[heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]`. Use `set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def`. Establish `hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c`. Introduce `i`.

Rewrite using `[← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) → ψ v ∈ chartRing F (segreVec y) c`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_ v _ hv`. Establish `: v = 0` using `w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])`.

Simplify using `[this]`. Consider the case `succ n ih`. Introduce `hn v hvB hv`. Use `set i : Fin N := ⟨n, hn⟩ with hi_def`. Establish `hmem : w.repr v i ∈ degLat F y (b i) c`.

Rewrite using `[← hB.graded c hc i]`. Use `⟨v, hvB, fun j hj => hv j ?_, rfl⟩` and prove the remaining obligations. Rewrite `hj` using `[Fin.lt_def]`. Simplify using `only [hi_def] at hj`. Use linear arithmetic over natural numbers and integers.

Take `⟨α, hα, hαv⟩` from `hmem`. Establish `hv' : v - α • e i ∈ B.lat c` using `(B.lat c).sub_mem hvB (B.stable c α hα _ (he i))`. Establish `hrec` using `ih (by omega) _ hv' (fun j hj => by`. Rewrite using `[map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]`. Break down `Nat.lt_or_ge n (j : ℕ) with hlt | hge` into its components or cases.

Rewrite using `[hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]`. Establish `hji : j = i` using `Fin.ext (by simp only [hi_def]; omega)`. Rewrite using `[hji, hdiag, hαv]`. Simplify using `[chartZ])`. Establish `hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i)`.

Simplify using `[map_sub, smul_eq_mul]`. Rewrite using `[hsplit]`. Conclude with `add_mem hrec (mul_mem hα (hψe i))`. Use `⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩` and prove the remaining obligations. Establish `he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩` using `by conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]`.

Rewrite using `[Finset.sum_eq_single ⟨0, h0⟩]`. Rewrite using `[hdiag]`. Introduce `j _ hj`. Rewrite using `[hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]`. Simplify using the standard rewrite rules.

Establish `h1 : ψ (e ⟨0, h0⟩) = 1`. Rewrite using `[← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`. Rewrite `h1` using `[he0, map_smul, smul_eq_mul]`. Rewrite using `[mul_comm]`. Conclude with `h1`.
-/
theorem exists_dual_first (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  choose e he hup hdiag using exists_adapted y B w b hB c hc
  have hm : ∀ i, chartZ y c (b i) ≠ 0 := fun i => chartZ_ne_zero hlive _
  have hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hsum := w.sum_repr (e i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈
          Submodule.span Ω (Set.range e) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt
        · exact Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)
        · rw [hup i j hgt, zero_smul]
          exact Submodule.zero_mem _
      have hei : e i ∈ Submodule.span Ω (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
      have h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e) := by
        rw [eq_sub_of_add_eq hsum]
        exact Submodule.sub_mem _ hei hrest
      rw [hdiag] at h1
      have h2 := Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (hm i), one_smul] at h2
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hspan i i rfl
  have hcard : Fintype.card (Fin N) = Module.finrank Ω E := by
    rw [Module.finrank_eq_card_basis w]
  set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def
  have heb : ∀ i, eb i = e i := fun i => by
    rw [heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]
  set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def
  have hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c := by
    intro i
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ψ v ∈ chartRing F (segreVec y) c := by
    intro n
    induction n with
    | zero =>
      intro _ v _ hv
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ n ih =>
      intro hn v hvB hv
      set i : Fin N := ⟨n, hn⟩ with hi_def
      have hmem : w.repr v i ∈ degLat F y (b i) c := by
        rw [← hB.graded c hc i]
        refine ⟨v, hvB, fun j hj => hv j ?_, rfl⟩
        rw [Fin.lt_def] at hj
        simp only [hi_def] at hj
        omega
      obtain ⟨α, hα, hαv⟩ := hmem
      have hv' : v - α • e i ∈ B.lat c := (B.lat c).sub_mem hvB (B.stable c α hα _ (he i))
      have hrec := ih (by omega) _ hv' (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
        · rw [hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]
        · have hji : j = i := Fin.ext (by simp only [hi_def]; omega)
          rw [hji, hdiag, hαv]
          simp [chartZ])
      have hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i) := by
        simp [map_sub, smul_eq_mul]
      rw [hsplit]
      exact add_mem hrec (mul_mem hα (hψe i))
  refine ⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩
  have he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
    conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [hdiag]
    · intro j _ hj
      rw [hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
    · simp
  have h1 : ψ (e ⟨0, h0⟩) = 1 := by
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [he0, map_smul, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1

/- English proof (translation)
Establish `hlive` using `live_of_segreVec_ne_zero hc`. Establish `hsplit : chartZ y c (b ⟨0, h0⟩ - a) = chartZ y c (b ⟨0, h0⟩) * chartZ y c (-a)`. Rewrite using `[sub_eq_add_neg, chartZ_add hlive]`. Establish `hinv : chartZ y c a * chartZ y c (-a) = 1`. Rewrite using `[← chartZ_add hlive, add_neg_cancel]`.

Simplify using `[chartZ]`. Use `⟨fun l => ?_, ?_⟩` and prove the remaining obligations. Take `⟨v0, hv0, hup, hdiag⟩` from `exists_adapted y B w b hB c hc ⟨0, h0⟩`. Establish `hv0eq : v0 = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩` using `by conv_lhs => rw [← w.sum_repr v0]`. Rewrite using `[Finset.sum_eq_single ⟨0, h0⟩]`.

Rewrite using `[hdiag]`. Introduce `j _ hj`. Rewrite using `[hup j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]`. Simplify using the standard rewrite rules. Take `⟨α, hα, hαe⟩` from `hφ.sections c hc l v0 hv0`.

Rewrite `hαe` using `[hv0eq, map_smul, smul_eq_mul]`. Establish `hαe' : chartZ y c (b ⟨0, h0⟩) * φ l (w ⟨0, h0⟩) = α * chartZ y c a` using `hαe`. Establish `: φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) = α`. Rewrite using `[hsplit]`. Take the linear combination `chartZ y c (-a) * hαe' + α * hinv`.

Rewrite using `[this]`. Conclude with `hα`. Take `⟨ψ, hψ, hψ1⟩` from `exists_dual_first y B w b hB c hc h0`. Take `⟨u, hu, hψeq⟩` from `hφ.generate c hc ψ hψ`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Establish `h` using `LinearMap.congr_fun hψeq (w ⟨0, h0⟩)`. Rewrite `h` using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h`. Rewrite using `[← hψ1, h, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hsplit]`. Simplify using `only [chartZ, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_data (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) {M : ℕ}
    (a : K → ℤ) (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    (∀ l, φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) ∈ chartRing F (segreVec y) c) ∧
      ∃ v : Fin M → Ω, (∀ l, v l ∈ chartRing F (segreVec y) c) ∧
        ∑ l, v l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  have hsplit : chartZ y c (b ⟨0, h0⟩ - a) = chartZ y c (b ⟨0, h0⟩) * chartZ y c (-a) := by
    rw [sub_eq_add_neg, chartZ_add hlive]
  have hinv : chartZ y c a * chartZ y c (-a) = 1 := by
    rw [← chartZ_add hlive, add_neg_cancel]
    simp [chartZ]
  refine ⟨fun l => ?_, ?_⟩
  · obtain ⟨v0, hv0, hup, hdiag⟩ := exists_adapted y B w b hB c hc ⟨0, h0⟩
    have hv0eq : v0 = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
      conv_lhs => rw [← w.sum_repr v0]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · rw [hdiag]
      · intro j _ hj
        rw [hup j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
      · simp
    obtain ⟨α, hα, hαe⟩ := hφ.sections c hc l v0 hv0
    rw [hv0eq, map_smul, smul_eq_mul] at hαe
    have hαe' : chartZ y c (b ⟨0, h0⟩) * φ l (w ⟨0, h0⟩) = α * chartZ y c a := hαe
    have : φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) = α := by
      rw [hsplit]
      linear_combination chartZ y c (-a) * hαe' + α * hinv
    rw [this]
    exact hα
  · obtain ⟨ψ, hψ, hψ1⟩ := exists_dual_first y B w b hB c hc h0
    obtain ⟨u, hu, hψeq⟩ := hφ.generate c hc ψ hψ
    refine ⟨u, hu, ?_⟩
    have h := LinearMap.congr_fun hψeq (w ⟨0, h0⟩)
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hψ1, h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsplit]
    simp only [chartZ, Pi.neg_apply]
    ring

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
