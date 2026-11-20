import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

section Minors

variable {N : ℕ}

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, Matrix.det_of_lowerTriangular]`. Conclude with `Finset.prod_eq_one fun i _ => hL.1 _`. Introduce `a b hab`. Conclude with `hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)`.
-/
theorem minor_self_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (C : Finset (Fin N)) :
    minorIJ L C C = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hL.1 _
  · intro a b hab
    exact hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)

/- English proof (translation)
Establish `hrn : r ∉ C.erase s` using `fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)`. Establish `hcard : (insert r (C.erase s)).card = C.card`. Rewrite using `[Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]`. Use `Finset.card_pos.2 ⟨s, hs⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Unfold `minorIJ`. Rewrite using `[dif_pos hcard]`. Use `set e := C.orderEmbOfFin rfl with he`. Establish `hmem : ∀ i, e i ∈ C` using `fun i => Finset.orderEmbOfFin_mem C rfl i`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, e m = s := by`.

Establish `: s ∈ Set.range e`. Rewrite using `[he, Finset.range_orderEmbOfFin]`. Conclude with `hs`. Conclude with `this`. Establish `hle : ∀ i, i ≤ m` using `fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))`.

Set `f : Fin C.card → Fin N` to `fun i => if i = m then r else e i`. Establish `hf_ne : ∀ i, i ≠ m → f i = e i` using `fun i h => if_neg h`. Establish `hf_m : f m = r` using `if_pos rfl`. Establish `hmono : StrictMono f`. Introduce `a b hab`.

Establish `ham : a ≠ m` using `fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)`. Rewrite using `[hf_ne a ham]`. Distinguish the cases in `hb : b = m`. Rewrite using `[hb, hf_m]`. Conclude with `lt_of_le_of_lt (hmax _ (hmem a)) hr`.

Rewrite using `[hf_ne b hb]`. Conclude with `e.strictMono hab`. Establish `hin : ∀ i, f i ∈ insert r (C.erase s)`. Introduce `i`. Distinguish the cases in `hi : i = m`.

Rewrite using `[hi, hf_m]`. Conclude with `Finset.mem_insert_self _ _`. Rewrite using `[hf_ne i hi]`. Use `Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)` and prove the remaining obligations. Conclude with `e.injective (h.trans hm.symm)`.

Establish `hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard` using `Finset.orderEmbOfFin_unique hcard hin hmono`. Rewrite using `[← hfe, Matrix.det_of_lowerTriangular]`. Rewrite using `[Finset.prod_eq_single m]`. Rewrite using `[Matrix.submatrix_apply, hf_m, hm]`. Introduce `i _ hi`.

Rewrite using `[Matrix.submatrix_apply, hf_ne i hi]`. Conclude with `hL.1 _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ m) h`. Introduce `a b hab`.

Establish `hab' : a < b` using `hab`. Establish `ham : a ≠ m` using `fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')`. Rewrite using `[Matrix.submatrix_apply, hf_ne a ham]`. Conclude with `hL.2 _ _ (e.strictMono hab')`.
-/
theorem minor_insert_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) {C : Finset (Fin N)} {s r : Fin N}
    (hs : s ∈ C) (hmax : ∀ a ∈ C, a ≤ s) (hr : s < r) : minorIJ L (insert r (C.erase s)) C = L r s := by
  have hrn : r ∉ C.erase s := fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)
  have hcard : (insert r (C.erase s)).card = C.card := by
    rw [Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]
    have := Finset.card_pos.2 ⟨s, hs⟩
    omega
  unfold minorIJ
  rw [dif_pos hcard]
  set e := C.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ C := fun i => Finset.orderEmbOfFin_mem C rfl i
  obtain ⟨m, hm⟩ : ∃ m, e m = s := by
    have : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hs
    exact this
  have hle : ∀ i, i ≤ m := fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))
  let f : Fin C.card → Fin N := fun i => if i = m then r else e i
  have hf_ne : ∀ i, i ≠ m → f i = e i := fun i h => if_neg h
  have hf_m : f m = r := if_pos rfl
  have hmono : StrictMono f := by
    intro a b hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)
    rw [hf_ne a ham]
    by_cases hb : b = m
    · rw [hb, hf_m]
      exact lt_of_le_of_lt (hmax _ (hmem a)) hr
    · rw [hf_ne b hb]
      exact e.strictMono hab
  have hin : ∀ i, f i ∈ insert r (C.erase s) := by
    intro i
    by_cases hi : i = m
    · rw [hi, hf_m]
      exact Finset.mem_insert_self _ _
    · rw [hf_ne i hi]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)
      exact e.injective (h.trans hm.symm)
  have hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard := Finset.orderEmbOfFin_unique hcard hin hmono
  rw [← hfe, Matrix.det_of_lowerTriangular]
  · rw [Finset.prod_eq_single m]
    · rw [Matrix.submatrix_apply, hf_m, hm]
    · intro i _ hi
      rw [Matrix.submatrix_apply, hf_ne i hi]
      exact hL.1 _
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a b hab
    have hab' : a < b := hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')
    rw [Matrix.submatrix_apply, hf_ne a ham]
    exact hL.2 _ _ (e.strictMono hab')

end Minors

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho`. Take `⟨hβ, hg, -, -⟩` from `bvec_good K ι Φ y Ψ N j M n BM l b hb`. Take `⟨c, -, ez⟩` from `ho`. Establish `hjN` using `M.j_le`. Establish `key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I, minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i)`.

Introduce `τ' i hi`. Take `⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k` from `Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi`. Use `⟨c k, fun I => ?_⟩` and prove the remaining obligations. Establish `h0` using `FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i)) (fun I hI => by show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0`. Rewrite using `[FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]`.

Use the proof step `ring)`. Use the proof step `(fun m => by`. Establish `x` using `congrFun ez ⟨k, m⟩`. Simplify using `only at x`. Rewrite `x` using `[flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m]`.

Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[x, Finset.mul_sum, sub_eq_zero]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring) I`. Conclude with `sub_eq_zero.1 h0`. Establish `ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i → (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s`.

Introduce `τ' i s r hi hs hmax hr`. Take `⟨a, ha⟩` from `key τ' i hi`. Establish `h1` using `ha (stepCols N j i)`. Rewrite `h1` using `[minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one]`. Establish `h2` using `ha (insert r ((stepCols N j i).erase s))`.

Rewrite `h2` using `[minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1, one_mul]`. Conclude with `h2`. Use function extensionality and compare the values at `τ'`. Use extensionality with `r s`. Break down `lt_trichotomy s r with hsr | hsr | hsr` into its components or cases.

Establish `hsr' : (s : ℕ) < r` using `hsr`. Distinguish the cases in `hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)`. Distinguish the cases in `hs : (s : ℕ) < N - j`. Establish `hr : (r : ℕ) < N - j` using `hblk.2 hs`. Use `ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr` and prove the remaining obligations.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha`.

Rewrite `ha` using `[if_neg (by omega)]`. Conclude with `Fin.le_def.2 (by omega)`. Establish `hr : ¬ (r : ℕ) < N - j` using `fun h => hs (hblk.1 h)`. Establish `hrN` using `r.2`. Use `ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr` and prove the remaining obligations.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha`.

Rewrite `ha` using `[if_pos (by omega)]`. Conclude with `Fin.le_def.2 (by omega)`. Rewrite using `[(hL τ').1 r s hblk, (hL' τ').1 r s hblk]`. Rewrite using `[hsr, (hL τ').2.1, (hL' τ').2.1]`. Rewrite using `[(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]`.
-/
theorem flag_uniq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho
  obtain ⟨hβ, hg, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  obtain ⟨c, -, ez⟩ := ho
  have hjN := M.j_le
  have key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I,
      minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i) := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    refine ⟨c k, fun I => ?_⟩
    have h0 := FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk
      (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i))
      (fun I hI => by
        show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0
        rw [FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]
        ring)
      (fun m => by
        have x := congrFun ez ⟨k, m⟩
        simp only at x
        rw [flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m] at x
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [x, Finset.mul_sum, sub_eq_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring) I
    exact sub_eq_zero.1 h0
  have ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i →
      (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s := by
    intro τ' i s r hi hs hmax hr
    obtain ⟨a, ha⟩ := key τ' i hi
    have h1 := ha (stepCols N j i)
    rw [minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one] at h1
    have h2 := ha (insert r ((stepCols N j i).erase s))
    rw [minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1,
      one_mul] at h2
    exact h2
  funext τ'
  ext r s
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hsr' : (s : ℕ) < r := hsr
    by_cases hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · by_cases hs : (s : ℕ) < N - j
      · have hr : (r : ℕ) < N - j := hblk.2 hs
        refine ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_neg (by omega)] at ha
          exact Fin.le_def.2 (by omega)
      · have hr : ¬ (r : ℕ) < N - j := fun h => hs (hblk.1 h)
        have hrN := r.2
        refine ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_pos (by omega)] at ha
          exact Fin.le_def.2 (by omega)
    · rw [(hL τ').1 r s hblk, (hL' τ').1 r s hblk]
  · rw [hsr, (hL τ').2.1, (hL' τ').2.1]
  · rw [(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
