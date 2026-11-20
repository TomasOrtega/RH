import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CChartLimit

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]`.
-/
theorem smod_span_iff {R : Type} [CommRing R] (a x y : R) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

/- English proof (translation)
Introduce `p O σ _ _ _ A _ _ hH x E t hE hs hstep hker`. Use `choose g hg using hs`. Establish `hdown : ∀ n d f, E (n + d) f = t (n + d) → E n f = t n`. Introduce `n d f`. Proceed by induction on `d with`.

Consider the case `zero => exact id`. Consider the case `succ d ih => exact fun hf => ih (hstep (n + d) f hf)`. Establish `hgk : ∀ n k, n ≤ k → E n (g k) = t n`. Introduce `n k hnk`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnk`.

Conclude with `hdown n d _ (hg _)`. Use `choose K hK using hker`. Set `K' : ℕ → ℕ` to `fun j => (Finset.range (j + 1)).sup (fun i => max i (K i i))`. Establish `hK'mono : Monotone K'` using `fun a b hab => Finset.sup_mono (Finset.range_subset_range.mpr (by omega))`. Establish `hK'ge : ∀ j, j ≤ K' j ∧ K j j ≤ K' j` using `fun j => by`.

Use `Finset.le_sup (f := fun i => max i (K i i)) (Finset.mem_range.mpr (Nat.lt_succ_self j))` as an intermediate fact. Conclude with `⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩`. Set `h : ℕ → MvPowerSeries σ O` to `fun j => g (K' j)`. Establish `hcau : ∀ j j', j ≤ j' → ∀ α : σ →₀ ℕ, α.degree < j → (p : O) ^ j ∣ coeff α (h j) - coeff α (h j')`. Introduce `j j' hjj α hα`.

Establish `h0 : E (K j j) (h j - h j') = 0`. Rewrite using `[map_sub, hgk _ _ (hK'ge j).2, hgk _ _ ((hK'ge j).2.trans (hK'mono hjj)), sub_self]`. Use `hK j j _ h0 α hα` as an intermediate fact. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis. Establish `hc : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ n, (p : O) ^ n ∣ coeff α (h (n + α.degree + 1)) - L`.

Introduce `α`. Establish `hpre : IsPrecomplete (Ideal.span {(p : O)}) O` using `inferInstance`. Take `⟨L, hL⟩` from `hpre.prec (f := fun n => coeff α (h (n + α.degree + 1))) (by`. Introduce `m n hmn`. Rewrite using `[smod_span_iff]`.

Use `hcau (m + α.degree + 1) (n + α.degree + 1) (by omega) α (by omega)` as an intermediate fact. Conclude with `(pow_dvd_pow _ (by omega)).trans this)`. Conclude with `⟨L, fun n => (smod_span_iff _ _ _ _).1 (hL n)⟩`. Use `choose L hL using hc`. Set `μ : MvPowerSeries σ O` to `L`.

Establish `hμ : ∀ α, coeff α μ = L α` using `fun α => rfl`. Use `⟨μ, fun n => ?_⟩` and prove the remaining obligations. Use `haveI := hH n`. Apply `(IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A n)})).2` to reduce the goal to its premises. Introduce `m`.

Rewrite using `[smod_span_iff]`. Take `⟨N, hN⟩` from `(hE n).2 m`. Establish `hj : E n (h (m + N + n)) = t n` using `hgk n (K' (m + N + n)) (le_trans (by omega) (hK'ge (m + N + n)).1)`. Establish `hd : ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α μ - coeff α (h (m + N + n))`. Introduce `α hα`.

Establish `h1` using `hL α m`. Establish `h2` using `hcau (m + α.degree + 1) (m + N + n) (by omega) α (by omega)`. Establish `h2' : (p : O) ^ m ∣ coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))` using `(pow_dvd_pow _ (by omega)).trans h2`. Establish `e : coeff α μ - coeff α (h (m + N + n)) = (coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))) - (coeff α (h (m + α.degree + 1)) - L α)` using `by rw [hμ]; ring`. Rewrite using `[e]`.

Conclude with `dvd_sub h2' h1`. Use `choose q hq using hd`. Set `Q : MvPowerSeries σ O` to `fun α => if hα : α.degree < N then q α hα else 0`. Establish `hQ : ∀ α (hα : α.degree < N), coeff α Q = q α hα` using `fun α hα => by show (if hα : α.degree < N then q α hα else 0) = q α hα`. Rewrite using `[dif_pos hα]`.

Set `R` to `μ - h (m + N + n) - (p : O) ^ m • Q`. Establish `hR : ∀ α : σ →₀ ℕ, α.degree < N → coeff α R = 0`. Introduce `α hα`. Simplify using `only [R, map_sub, MvPowerSeries.coeff_smul, hQ α hα, smul_eq_mul, hq α hα, sub_self]`. Establish `hER` using `hN R hR`.

Establish `hsplit : E n μ - t n = E n R + (p : A n) ^ m * E n Q`. Establish `hμeq : μ = h (m + N + n) + ((p : O) ^ m • Q + R)` using `by simp only [R]; abel`. Rewrite using `[hμeq, map_add, map_add, hj, map_smul, Algebra.smul_def, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`.

Conclude with `dvd_add hER (dvd_mul_right _ _)`.
-/
theorem exists_series_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) →
    ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n),
    (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) →
    (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) →
    (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
    ∃ g, ∀ n, E n g = t n := by
  intro p O σ _ _ _ A _ _ hH x E t hE hs hstep hker
  classical
  choose g hg using hs
  have hdown : ∀ n d f, E (n + d) f = t (n + d) → E n f = t n := by
    intro n d f
    induction d with
    | zero => exact id
    | succ d ih => exact fun hf => ih (hstep (n + d) f hf)
  have hgk : ∀ n k, n ≤ k → E n (g k) = t n := by
    intro n k hnk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact hdown n d _ (hg _)
  choose K hK using hker
  let K' : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup (fun i => max i (K i i))
  have hK'mono : Monotone K' := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hK'ge : ∀ j, j ≤ K' j ∧ K j j ≤ K' j := fun j => by
    have := Finset.le_sup (f := fun i => max i (K i i)) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  let h : ℕ → MvPowerSeries σ O := fun j => g (K' j)
  have hcau : ∀ j j', j ≤ j' → ∀ α : σ →₀ ℕ, α.degree < j →
      (p : O) ^ j ∣ coeff α (h j) - coeff α (h j') := by
    intro j j' hjj α hα
    have h0 : E (K j j) (h j - h j') = 0 := by
      rw [map_sub, hgk _ _ (hK'ge j).2, hgk _ _ ((hK'ge j).2.trans (hK'mono hjj)), sub_self]
    have := hK j j _ h0 α hα
    rwa [map_sub] at this
  have hc : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ n, (p : O) ^ n ∣ coeff α (h (n + α.degree + 1)) - L := by
    intro α
    have hpre : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
    obtain ⟨L, hL⟩ := hpre.prec (f := fun n => coeff α (h (n + α.degree + 1))) (by
      intro m n hmn
      rw [smod_span_iff]
      have := hcau (m + α.degree + 1) (n + α.degree + 1) (by omega) α (by omega)
      exact (pow_dvd_pow _ (by omega)).trans this)
    exact ⟨L, fun n => (smod_span_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  let μ : MvPowerSeries σ O := L
  have hμ : ∀ α, coeff α μ = L α := fun α => rfl
  refine ⟨μ, fun n => ?_⟩
  haveI := hH n
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A n)})).2
  intro m
  rw [smod_span_iff]
  obtain ⟨N, hN⟩ := (hE n).2 m
  have hj : E n (h (m + N + n)) = t n :=
    hgk n (K' (m + N + n)) (le_trans (by omega) (hK'ge (m + N + n)).1)
  have hd : ∀ α : σ →₀ ℕ, α.degree < N →
      (p : O) ^ m ∣ coeff α μ - coeff α (h (m + N + n)) := by
    intro α hα
    have h1 := hL α m
    have h2 := hcau (m + α.degree + 1) (m + N + n) (by omega) α (by omega)
    have h2' : (p : O) ^ m ∣ coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n)) :=
      (pow_dvd_pow _ (by omega)).trans h2
    have e : coeff α μ - coeff α (h (m + N + n)) =
        (coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))) -
          (coeff α (h (m + α.degree + 1)) - L α) := by rw [hμ]; ring
    rw [e]; exact dvd_sub h2' h1
  choose q hq using hd
  let Q : MvPowerSeries σ O := fun α => if hα : α.degree < N then q α hα else 0
  have hQ : ∀ α (hα : α.degree < N), coeff α Q = q α hα := fun α hα => by
    show (if hα : α.degree < N then q α hα else 0) = q α hα
    rw [dif_pos hα]
  let R := μ - h (m + N + n) - (p : O) ^ m • Q
  have hR : ∀ α : σ →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro α hα
    simp only [R, map_sub, MvPowerSeries.coeff_smul, hQ α hα, smul_eq_mul, hq α hα, sub_self]
  have hER := hN R hR
  have hsplit : E n μ - t n = E n R + (p : A n) ^ m * E n Q := by
    have hμeq : μ = h (m + N + n) + ((p : O) ^ m • Q + R) := by simp only [R]; abel
    rw [hμeq, map_add, map_add, hj, map_smul, Algebra.smul_def, map_pow, map_natCast]
    ring
  rw [hsplit]
  exact dvd_add hER (dvd_mul_right _ _)

end GlobalTheory.CChartLimit
