import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

/- English proof (translation)
Simplify using `only [Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h`.
-/
theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

/- English proof (translation)
Introduce `_ hY i j` and use `(hY i j).trans (val_unif_pow_le hϖ h)`.
-/
theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

/- English proof (translation)
Introduce `i j` and use `by simp`.
-/
theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

/- English proof (translation)
Use extensionality with `i j`. Assume the negation of the conclusion as `hne`. Establish `h0 : valuation k (Y i j - X i j) ≠ 0` using `by simpa [sub_eq_zero] using hne`. Take `⟨n, hn⟩` from `exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)`. Use `h n i j` as an intermediate fact.

Simplify using `only [Units.val_pow_eq_pow_val, map_pow] at this`. Conclude with `absurd this (not_le.2 hn)`.
-/
theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

/- English proof (translation)
Use `exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n)) (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _) (fun n => (isClopen_box ϖ X _).isClosed) ?_` and prove the remaining obligations. Introduce `Y hY`. Rewrite using `[eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)]`. Conclude with `hU`.
-/
theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  intro Y hY
  rw [eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)]
  exact hU

/- English proof (translation)
Introduce `Φ hΦ`. Take `⟨hlc, hcs⟩` from `hΦ`. Establish `hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X}` using `fun X => exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)`. Use `choose n hn using hrad`. Take `⟨t, ht⟩` from `IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X)) (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)`.

Use `⟨t.sup n, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y`. Introduce `Y hY Z hZ`. Take `⟨X, hXt, hYX⟩` from `Set.mem_iUnion₂.1 (ht hY)`. Establish `hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X)`.

Rewrite using `[← box_eq_of_mem hYX]`. Conclude with `box_mono hϖ Y ((Finset.le_sup hXt).trans hm)`. Establish `h1 : Φ Z = Φ X` using `hn X (hsub hZ)`. Establish `h2 : Φ Y = Φ X` using `hn X (hsub (mem_box_self ϖ Y _))`. Rewrite using `[h1, h2]`.

Set `rep : Set (Matrix A D k) → Matrix A D k` to `fun B => if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0`. Establish `hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m)`. Introduce `Y`. Establish `h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m)` using `⟨Y, rfl⟩`. Rewrite using `[show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]`.

Conclude with `h.choose_spec`. Take `⟨s₀, hs₀⟩` from `IsCompact.elim_finite_subcover hcs (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m)) (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)`. Set `s : Finset (Matrix A D k)` to `s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))`. Establish `hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m))`. Introduce `c hc`.

Take `⟨Y, -, rfl⟩` from `Finset.mem_image.1 hc`. Conclude with `⟨Y, Y.2, rfl⟩`. Establish `hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c`. Introduce `c hc Z hZ`. Take `⟨Y, hY, rfl⟩` from `hs c hc`.

Rewrite `hZ` using `[hrep]`. Establish `hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m)`. Use `mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)` as an intermediate fact. Rewrite `this` using `[hrep]`. Then use the resulting hypothesis. Rewrite using `[hconst Y hY Z hZ, hconst Y hY _ hcY]`.

Establish `huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c'`. Introduce `c hc c' hc' Z hZ hZ'`. Take `⟨Y, -, rfl⟩` from `hs c hc`. Take `⟨Y', -, rfl⟩` from `hs c' hc'`. Establish `e1` using `box_eq_of_mem hZ`.

Establish `e2` using `box_eq_of_mem hZ'`. Rewrite `e1`, `e2` using `[hrep]`. Rewrite using `[← e1, ← e2]`. Establish `hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)`. Introduce `Z hZ`.

Take `⟨Y, hY, hZY⟩` from `Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))`. Use `⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩` and prove the remaining obligations. Rewrite using `[hrep]`. Conclude with `hZY`. Use `⟨s, ?_, hval⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `Z`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]`. Distinguish the cases in `h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)`. Take `⟨c, hc, hZ⟩` from `h`. Rewrite using `[Finset.sum_eq_single c]`.

Rewrite using `[Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]`. Introduce `c' hc' hne`. Rewrite using `[Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]`. Introduce `hcs'`. Conclude with `absurd hc hcs'`.

Use `push_neg at h`. Rewrite using `[Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]`. Assume the negation of the conclusion as `hZ`. Take `⟨c, hc, hZc⟩` from `hcov Z hZ`. Conclude with `h c hc hZc`.
-/
theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
