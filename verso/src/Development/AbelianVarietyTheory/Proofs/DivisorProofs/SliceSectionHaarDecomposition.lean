import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Introduce `k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq`. Use `set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a d, Y = x.val * Z} with hTdef`. Use `set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef`. Establish `hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J` using `fun J => by`. Unfold `minor`.

Conclude with `(continuous_id.matrix_submatrix id J).matrix_det`. Establish `hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K)`. Introduce `Y hY`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, Z, hZ, rfl⟩`.

Establish `h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice k a d`. Rewrite using `[Units.val_mul, Matrix.mul_assoc]`. Conclude with `hsec _ hY`. Establish `h2` using `huniq Z _ hZ h1`. Establish `h3 : x = s (x.val * Z)`.

Use `congrArg (fun g => s (x.val * Z) * g) h2` as an intermediate fact. Simplify `this` using `[← mul_assoc]`. Rewrite using `[← h3]`. Conclude with `hx`. Introduce `h`.

Use `⟨s Y, h, _, hsec Y hY, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1`. Introduce and unpack `Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩`. Use `⟨J, ?_⟩` and prove the remaining obligations.

Rewrite using `[minor_mul, minor, hJ, Matrix.det_one, mul_one]`. Use `valuation_gdet_of_mem_KO (hKO hx)` as an intermediate fact. Simplify `this` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hTO : T ⊆ O`. Introduce `Y hY`.

Take `⟨J, hJ⟩` from `hTmin Y hY`. Use `(hrank Y).2 ⟨J, fun h => ?_⟩` and prove the remaining obligations. Rewrite `hJ` using `[h, map_zero]`. Conclude with `zero_ne_one hJ`. Establish `hOopen : IsOpen O`.

Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `Y hY`. Take `⟨J, hJ⟩` from `(hrank Y).1 hY`. Establish `hv : valuation k (minor Y J) ≠ 0` using `by simpa using hJ`. Establish `hn` using `(valuation k).locally_const hv`.

Use `(hmc J).continuousAt.preimage_mem_nhds hn` as an intermediate fact. Use `Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, h0, map_zero] at hY'`. Conclude with `hv hY'.symm`. Establish `hKc : IsClosed (K : Set (GL (Fin a) k))` using `Subgroup.isClosed_of_isOpen K hKo`.

Establish `hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k))`. Use extensionality with `Y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨hTO h, (hT Y (hTO h)).1 h⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `(hT Y h1).2 h2`. Establish `hTopen : IsOpen T`. Rewrite using `[hTeq]`. Conclude with `hs.isOpen_inter_preimage hOopen hKo`.

Establish `h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k)`. Use `(IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial` as an intermediate fact. Simplify using `using this`. Establish `hTclosed : IsClosed T`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`.

Introduce `Y hY`. Distinguish the cases in `hYO : Y ∈ O`. Establish `hsY : s Y ∉ K` using `fun h => hY ((hT Y hYO).2 h)`. Establish `ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ)` using `hs.isOpen_inter_preimage hOopen hKc.isOpen_compl`. Use `Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_` and prove the remaining obligations.

Conclude with `(hT Y' hY'.1).1 hT'`. Establish `hz : ∀ J, minor Y J = 0`. Introduce `J`. Assume the negation of the conclusion as `hne`. Conclude with `hYO ((hrank Y).2 ⟨J, hne⟩)`.

Establish `hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y`. Use `Filter.iInter_mem.2 fun J => ?_` and prove the remaining obligations. Use `(hmc J).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[hz J]`. Conclude with `h0`.

Use `Filter.mem_of_superset hW fun Y' hY' hT' => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `hTmin Y' hT'`. Use `Set.mem_iInter.1 hY' J` as an intermediate fact. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, hJ] at this`. Conclude with `lt_irrefl _ this`.

Conclude with `(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant`.
-/
theorem indicator_slice_orbit_isLocallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (K : Subgroup (GL (Fin a) k)), IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a ↔ ∃ J, minor Y J ≠ 0) →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    IsLocallyConstant (Set.indicator {Y : Matrix (Fin a) (Fin d) k | ∃ x ∈ K, ∃ Z ∈ slice k a d, Y = x.val * Z}
      (1 : Matrix (Fin a) (Fin d) k → ℂ)) := by
  intro k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq
  set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a d, Y = x.val * Z} with hTdef
  set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef
  have hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J := fun J => by
    unfold minor
    exact (continuous_id.matrix_submatrix id J).matrix_det

  have hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K) := by
    intro Y hY
    constructor
    · rintro ⟨x, hx, Z, hZ, rfl⟩
      have h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice k a d := by
        rw [Units.val_mul, Matrix.mul_assoc]; exact hsec _ hY
      have h2 := huniq Z _ hZ h1
      have h3 : x = s (x.val * Z) := by
        have := congrArg (fun g => s (x.val * Z) * g) h2
        simpa [← mul_assoc] using this
      rw [← h3]; exact hx
    · intro h
      refine ⟨s Y, h, _, hsec Y hY, ?_⟩
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1 := by
    rintro Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩
    refine ⟨J, ?_⟩
    rw [minor_mul, minor, hJ, Matrix.det_one, mul_one]
    have := valuation_gdet_of_mem_KO (hKO hx)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hTO : T ⊆ O := by
    intro Y hY
    obtain ⟨J, hJ⟩ := hTmin Y hY
    refine (hrank Y).2 ⟨J, fun h => ?_⟩
    rw [h, map_zero] at hJ
    exact zero_ne_one hJ
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Y hY
    obtain ⟨J, hJ⟩ := (hrank Y).1 hY
    have hv : valuation k (minor Y J) ≠ 0 := by simpa using hJ
    have hn := (valuation k).locally_const hv
    have := (hmc J).continuousAt.preimage_mem_nhds hn
    refine Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, h0, map_zero] at hY'
    exact hv hY'.symm
  have hKc : IsClosed (K : Set (GL (Fin a) k)) := Subgroup.isClosed_of_isOpen K hKo
  have hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k)) := by
    ext Y
    constructor
    · intro h; exact ⟨hTO h, (hT Y (hTO h)).1 h⟩
    · rintro ⟨h1, h2⟩; exact (hT Y h1).2 h2
  have hTopen : IsOpen T := by
    rw [hTeq]; exact hs.isOpen_inter_preimage hOopen hKo
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) := by
    have := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using this
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Y hY
    by_cases hYO : Y ∈ O
    · have hsY : s Y ∉ K := fun h => hY ((hT Y hYO).2 h)
      have ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ) := hs.isOpen_inter_preimage hOopen hKc.isOpen_compl
      refine Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_
      exact (hT Y' hY'.1).1 hT'
    · have hz : ∀ J, minor Y J = 0 := by
        intro J; by_contra hne; exact hYO ((hrank Y).2 ⟨J, hne⟩)
      have hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y := by
        refine Filter.iInter_mem.2 fun J => ?_
        refine (hmc J).continuousAt.preimage_mem_nhds ?_
        rw [hz J]; exact h0
      refine Filter.mem_of_superset hW fun Y' hY' hT' => ?_
      obtain ⟨J, hJ⟩ := hTmin Y' hT'
      have := Set.mem_iInter.1 hY' J
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hJ] at this
      exact lt_irrefl _ this
  exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant

end GlobalTheory.RankFibreKer
