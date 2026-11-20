import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBound

/- English proof (translation)
Set `b` to `Module.finBasis K W`. Set `M₀ : Matrix (Fin n) (Fin (Module.finrank K W)) K` to `Matrix.of fun i j => (b j : Fin n → K) i`. Establish `hli0 : LinearIndependent K M₀ᵀ` using `b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)`. Establish `hsp0 : Submodule.span K (Set.range M₀ᵀ) = W`. Establish `h : Set.range M₀ᵀ = W.subtype '' Set.range b`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hrk : M₀.rank = Module.finrank K W`. Rewrite using `[← Matrix.rank_transpose, LinearIndependent.rank_matrix (M := M₀ᵀ) hli0, Fintype.card_fin]`.

Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' K M₀.row`. Use `haveI : Finite κ := Finite.of_injective a ha`. Use `letI : Fintype κ := Fintype.ofFinite κ`. Establish `hκ : Fintype.card κ = Module.finrank K W`. Rewrite using `[← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]`.

Set `f : Fin (Module.finrank K W) ≃ κ` to `(Fintype.equivFinOfCardEq hκ).symm`. Set `Q : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K` to `M₀.submatrix (a ∘ f) id`. Establish `hQ : IsUnit Q` using `Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp f f.injective)`. Establish `hdet : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hQ`. Set `M : Matrix (Fin n) (Fin (Module.finrank K W)) K` to `M₀ * Q⁻¹`.

Establish `hs : M.submatrix (a ∘ f) id = 1`. Establish `h : M.submatrix (a ∘ f) id = Q * Q⁻¹`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h, Matrix.mul_nonsing_inv _ hdet]`.

Establish `hinj : Function.Injective M.mulVec`. Introduce `u v huv`. Use function extensionality and compare the values at `i`. Establish `h1 : ∀ t : Fin (Module.finrank K W) → K, (M.submatrix (a ∘ f) id) *ᵥ t = fun i => (M *ᵥ t) (a (f i))`. Introduce `t`.

Use extensionality with `i`. Both sides reduce to the same expression. Establish `h2` using `h1 u`. Establish `h3` using `h1 v`. Rewrite `h2`, `h3` using `[hs, Matrix.one_mulVec]`.

Rewrite using `[h2, h3, huv]`. Establish `hr : LinearMap.range M.mulVecLin = LinearMap.range M₀.mulVecLin`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`.

Conclude with `⟨Q⁻¹ *ᵥ v, by simp [M, Matrix.mulVec_mulVec]⟩`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨Q *ᵥ v, by simp [M, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]⟩`. Use `⟨Module.finrank K W, M, a ∘ f, ?_, hs, Matrix.mulVec_injective_iff.1 hinj, ?_⟩` and prove the remaining obligations. Simplify using `using W.finrank_le`.

Establish `h1` using `Matrix.range_mulVecLin M`. Establish `h2` using `Matrix.range_mulVecLin M₀`. Rewrite `h1` using `[hr, h2]`. Conclude with `h1.symm.trans hsp0`.
-/
theorem exists_normal_basis {K : Type} [Field K] {n : ℕ} (W : Submodule K (Fin n → K)) :
    ∃ (k : ℕ) (M : Matrix (Fin n) (Fin k) K) (s : Fin k → Fin n), k ≤ n ∧ M.submatrix s id = 1 ∧
      LinearIndependent K Mᵀ ∧ Submodule.span K (Set.range Mᵀ) = W := by
  classical
  let b := Module.finBasis K W
  let M₀ : Matrix (Fin n) (Fin (Module.finrank K W)) K := Matrix.of fun i j => (b j : Fin n → K) i
  have hli0 : LinearIndependent K M₀ᵀ := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hsp0 : Submodule.span K (Set.range M₀ᵀ) = W := by
    have h : Set.range M₀ᵀ = W.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hrk : M₀.rank = Module.finrank K W := by
    rw [← Matrix.rank_transpose, LinearIndependent.rank_matrix (M := M₀ᵀ) hli0, Fintype.card_fin]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M₀.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = Module.finrank K W := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
  let f : Fin (Module.finrank K W) ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  let Q : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K := M₀.submatrix (a ∘ f) id
  have hQ : IsUnit Q := Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp f f.injective)
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).1 hQ
  let M : Matrix (Fin n) (Fin (Module.finrank K W)) K := M₀ * Q⁻¹
  have hs : M.submatrix (a ∘ f) id = 1 := by
    have h : M.submatrix (a ∘ f) id = Q * Q⁻¹ := by
      ext i j; rfl
    rw [h, Matrix.mul_nonsing_inv _ hdet]
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    funext i
    have h1 : ∀ t : Fin (Module.finrank K W) → K, (M.submatrix (a ∘ f) id) *ᵥ t = fun i => (M *ᵥ t) (a (f i)) := by
      intro t; ext i; rfl
    have h2 := h1 u
    have h3 := h1 v
    rw [hs, Matrix.one_mulVec] at h2 h3
    rw [h2, h3, huv]
  have hr : LinearMap.range M.mulVecLin = LinearMap.range M₀.mulVecLin := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Q⁻¹ *ᵥ v, by simp [M, Matrix.mulVec_mulVec]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Q *ᵥ v, by simp [M, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]⟩
  refine ⟨Module.finrank K W, M, a ∘ f, ?_, hs, Matrix.mulVec_injective_iff.1 hinj, ?_⟩
  · simpa using W.finrank_le
  · have h1 := Matrix.range_mulVecLin M
    have h2 := Matrix.range_mulVecLin M₀
    rw [hr, h2] at h1
    exact h1.symm.trans hsp0

/- English proof (translation)
Establish `h1` using `(hF K (Fin n) (Fin k) (Fin k) A).1 Y`. Establish `h2` using `(hF K (Fin n) (Fin k) (Fin k) A).2.2 1`. Rewrite `h1` using `[h, h2]`. Simplify using `using h1`.
-/
theorem one_le_fin (hF : MulF) {K : Type} [NormedField K] [IsUltrametricDist K] {n k : ℕ}
    (Y : Matrix (Fin k) (Fin n) K) (A : Matrix (Fin n) (Fin k) K) (h : Y * A = 1) :
    1 ≤ sz Y ^ k * nF A := by
  have h1 := (hF K (Fin n) (Fin k) (Fin k) A).1 Y
  have h2 := (hF K (Fin n) (Fin k) (Fin k) A).2.2 1
  rw [h, h2] at h1
  simpa using h1

/- English proof (translation)
Establish `h1` using `(hI (Fin n) (Fin k) (Fin k) A).1 Y`. Establish `h2` using `(hI (Fin n) (Fin k) (Fin k) A).2.2 1`. Rewrite `h1` using `[h, h2]`. Simplify using `using h1`.
-/
theorem one_le_inf (hI : MulI) {n k : ℕ} (Y : Matrix (Fin k) (Fin n) ℂ) (A : Matrix (Fin n) (Fin k) ℂ)
    (h : Y * A = 1) : 1 ≤ (((n : ℝ) * k) * sz Y ^ 2) ^ k * nI A := by
  have h1 := (hI (Fin n) (Fin k) (Fin k) A).1 Y
  have h2 := (hI (Fin n) (Fin k) (Fin k) A).2.2 1
  rw [h, h2] at h1
  simpa using h1

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
The claim follows from `Real.iSup_le (fun p => le_ciSup (f := fun p : Fin n × Fin n => ‖X p.1 p.2‖) (Set.finite_range _).bddAbove (s p.1, p.2)) (sz_nonneg X)`.
-/
theorem sz_rows_le {K : Type} [NormedField K] {n k : ℕ} (X : Matrix (Fin n) (Fin n) K) (s : Fin k → Fin n) :
    sz (X.submatrix s id) ≤ sz X :=
  Real.iSup_le (fun p => le_ciSup (f := fun p : Fin n × Fin n => ‖X p.1 p.2‖)
    (Set.finite_range _).bddAbove (s p.1, p.2)) (sz_nonneg X)

/- English proof (translation)
Establish `hT : 0 ≤ ⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2` using `Real.iSup_nonneg fun _ => by positivity`. Establish `h : sz X ≤ Real.sqrt (⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2)` using `Real.iSup_le (fun p => Real.le_sqrt_of_sq_le (le_ciSup (f := fun p : Fin n × Fin n => ‖X p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p)) (Real.sqrt_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sz_nonneg X`. Use `_ = _ := Real.sq_sqrt hT`.
-/
theorem sz_sq_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : sz X ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2 := by
  have hT : 0 ≤ ⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2 := Real.iSup_nonneg fun _ => by positivity
  have h : sz X ≤ Real.sqrt (⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2) :=
    Real.iSup_le (fun p => Real.le_sqrt_of_sq_le (le_ciSup (f := fun p : Fin n × Fin n => ‖X p.1 p.2‖ ^ 2)
      (Set.finite_range _).bddAbove p)) (Real.sqrt_nonneg _)
  calc sz X ^ 2 ≤ Real.sqrt (⨆ p : Fin n × Fin n, ‖X p.1 p.2‖ ^ 2) ^ 2 := by
        gcongr
        exact sz_nonneg X
    _ = _ := Real.sq_sqrt hT

/- English proof (translation)
Establish `hp : 0 ≤ t ^ k` using `pow_nonneg ht k`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht0 : t ^ k ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0]`. Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : 0 ≤ Real.log (t ^ k * a)` using `Real.log_nonneg h`. Rewrite `h1` using `[Real.log_mul ht0 ha0, Real.log_pow]`. Establish `h2 : Real.log t ≤ Real.posLog t`. Rewrite using `[Real.posLog_def]`. Conclude with `le_max_right _ _`.

Establish `h3 : (k : ℝ) * Real.log t ≤ k * Real.posLog t` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_log_le {t a : ℝ} {k : ℕ} (ht : 0 ≤ t) (ha : 0 ≤ a) (h : 1 ≤ t ^ k * a) :
    -Real.log a ≤ k * Real.posLog t := by
  have hp : 0 ≤ t ^ k := pow_nonneg ht k
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at h
    linarith
  have ht0 : t ^ k ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
    linarith
  have h1 : 0 ≤ Real.log (t ^ k * a) := Real.log_nonneg h
  rw [Real.log_mul ht0 ha0, Real.log_pow] at h1
  have h2 : Real.log t ≤ Real.posLog t := by
    rw [Real.posLog_def]
    exact le_max_right _ _
  have h3 : (k : ℝ) * Real.log t ≤ k * Real.posLog t := by gcongr
  linarith

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ}

/- English proof (translation)
Establish `h : x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = M.map (algebraMap E (Ad E))`. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `h2 : (x.val.submatrix s id * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))) = (x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))).submatrix s id`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[h2, h]`. Establish `h3 : (M.map (algebraMap E (Ad E))).submatrix s id = (M.submatrix s id).map (algebraMap E (Ad E))` using `rfl`. Rewrite using `[h3, hs]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem rows_mul_frame (x : GA E n) (M : Matrix (Fin n) (Fin k) E) (s : Fin k → Fin n)
    (hs : M.submatrix s id = 1) :
    x.val.submatrix s id * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = 1 := by
  have h : x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = M.map (algebraMap E (Ad E)) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have h2 : (x.val.submatrix s id * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))) =
      (x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))).submatrix s id := by
    ext i j; rfl
  rw [h2, h]
  have h3 : (M.map (algebraMap E (Ad E))).submatrix s id = (M.submatrix s id).map (algebraMap E (Ad E)) := rfl
  rw [h3, hs]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Establish `h1 : (x.val.map (cW w)).submatrix s id * A.map (cW w) = 1`. Establish `h : ((x.val.submatrix s id) * A).map (cW w) = (1 : Matrix (Fin k) (Fin k) (Ad E)).map (cW w)` using `by rw [hY]`. Rewrite `h` using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h`. Establish `h2` using `one_le_fin hF _ _ h1`.

Establish `h3 : sz ((x.val.map (cW w)).submatrix s id) ^ k ≤ sz (x.val.map (cW w)) ^ k` using `pow_le_pow_left₀ (sz_nonneg _) (sz_rows_le _ s) k`. Establish `h4 : 1 ≤ sz (x.val.map (cW w)) ^ k * nF (A.map (cW w))` using `h2.trans (mul_le_mul_of_nonneg_right h3 (nF_nonneg _))`. Use `(neg_log_le (sz_nonneg _) (nF_nonneg _) h4).trans ?_` and prove the remaining obligations. Establish `: (k : ℝ) ≤ n` using `by exact_mod_cast hk`. Conclude with `mul_le_mul_of_nonneg_right this Real.posLog_nonneg`.
-/
theorem neg_log_fin (hF : MulF) (x : GA E n) (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (s : Fin k → Fin n) (hY : x.val.submatrix s id * A = 1) (hk : k ≤ n) :
    -Real.log (nF (A.map (cW w))) ≤ n * Real.posLog (sz (x.val.map (cW w))) := by
  have h1 : (x.val.map (cW w)).submatrix s id * A.map (cW w) = 1 := by
    have h : ((x.val.submatrix s id) * A).map (cW w) = (1 : Matrix (Fin k) (Fin k) (Ad E)).map (cW w) := by rw [hY]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have h2 := one_le_fin hF _ _ h1
  have h3 : sz ((x.val.map (cW w)).submatrix s id) ^ k ≤ sz (x.val.map (cW w)) ^ k :=
    pow_le_pow_left₀ (sz_nonneg _) (sz_rows_le _ s) k
  have h4 : 1 ≤ sz (x.val.map (cW w)) ^ k * nF (A.map (cW w)) :=
    h2.trans (mul_le_mul_of_nonneg_right h3 (nF_nonneg _))
  refine (neg_log_le (sz_nonneg _) (nF_nonneg _) h4).trans ?_
  have : (k : ℝ) ≤ n := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this Real.posLog_nonneg

/- English proof (translation)
Establish `h1 : (x.val.map (cV v)).submatrix s id * A.map (cV v) = 1`. Establish `h : ((x.val.submatrix s id) * A).map (cV v) = (1 : Matrix (Fin k) (Fin k) (Ad E)).map (cV v)` using `by rw [hY]`. Rewrite `h` using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h`. Establish `hkn : (k : ℝ) ≤ n` using `by exact_mod_cast hk`.

Establish `hT : 0 ≤ ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2` using `Real.iSup_nonneg fun _ => by positivity`. Establish `h2` using `one_le_inf hI _ _ h1`. Establish `hN : 0 ≤ nI (A.map (cV v))` using `(hW (Fin n)).nonneg (Fin k) (A.map (cV v))`. Establish `h3 : sz ((x.val.map (cV v)).submatrix s id) ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2` using `(pow_le_pow_left₀ (sz_nonneg _) (sz_rows_le _ s) 2).trans (sz_sq_le (x.val.map (cV v)))`. Establish `h4 : 1 ≤ (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2) ^ k * nI (A.map (cV v))`.

Use `h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ k) hN)` and prove the remaining obligations. Conclude with `mul_le_mul (by gcongr) h3 (by positivity) (by positivity)`. Use `(neg_log_le (by positivity) hN h4).trans ?_` and prove the remaining obligations. Establish `h5 : Real.posLog (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2) ≤ _` using `Real.posLog_mul`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem neg_log_inf (hI : MulI) (hW : WedgeI) (x : GA E n) (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E))
    (s : Fin k → Fin n) (hY : x.val.submatrix s id * A = 1) (hk : k ≤ n) :
    -Real.log (nI (A.map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2)) := by
  have h1 : (x.val.map (cV v)).submatrix s id * A.map (cV v) = 1 := by
    have h : ((x.val.submatrix s id) * A).map (cV v) = (1 : Matrix (Fin k) (Fin k) (Ad E)).map (cV v) := by rw [hY]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hT : 0 ≤ ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2 := Real.iSup_nonneg fun _ => by positivity
  have h2 := one_le_inf hI _ _ h1
  have hN : 0 ≤ nI (A.map (cV v)) := (hW (Fin n)).nonneg (Fin k) (A.map (cV v))
  have h3 : sz ((x.val.map (cV v)).submatrix s id) ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2 :=
    (pow_le_pow_left₀ (sz_nonneg _) (sz_rows_le _ s) 2).trans (sz_sq_le (x.val.map (cV v)))
  have h4 : 1 ≤ (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2) ^ k * nI (A.map (cV v)) := by
    refine h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ k) hN)
    exact mul_le_mul (by gcongr) h3 (by positivity) (by positivity)
  refine (neg_log_le (by positivity) hN h4).trans ?_
  have h5 : Real.posLog (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2) ≤ _ := Real.posLog_mul
  calc (k : ℝ) * Real.posLog (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2)
      ≤ n * Real.posLog (((n : ℝ) * n) * ⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hkn Real.posLog_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)

/- English proof (translation)
Establish `hY` using `rows_mul_frame x M s hs`. Use `set A := (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) with hA`. Establish `hfin1 : (Function.support fun w => -Real.log (nF (A.map (cW w)))).Finite`. Use `((hFS E (Fin n) (Fin k) A _ hY).2.2).subset fun w hw => ?_` and prove the remaining obligations. Introduce `h1`.

Apply `hw` to reduce the goal to its premises. Simplify using `[h1]`. Establish `hfin2 : (Function.support fun w : HeightOneSpectrum (𝓞 E) => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)).Finite`. Use `(hS E (Fin n) (Fin n) x.val).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Apply `hw` to reduce the goal to its premises. Establish `h0 : 0 ≤ sz (x.val.map (cW w))` using `sz_nonneg _`. Establish `h1 : |sz (x.val.map (cW w))| ≤ 1`. Rewrite using `[abs_of_nonneg h0]`. Conclude with `not_lt.1 hlt`.

Conclude with `(Real.posLog_eq_zero_iff _).2 h1`. Establish `hfin3 : (Function.support fun w : HeightOneSpectrum (𝓞 E) => (n : ℝ) * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)).Finite` using `hfin2.subset (Function.support_const_smul_subset (n : ℝ) _)`. Establish `e1 : degG x M = ∑ v, -Real.log (nI (A.map (cV v))) + ∑ᶠ w, -Real.log (nF (A.map (cW w)))`. Rewrite using `[degG, finsum_neg_distrib, Finset.sum_neg_distrib, neg_add]`. Establish `b1 : ∑ v, -Real.log (nI (A.map (cV v))) ≤ ∑ v : InfinitePlace E, (n : ℝ) * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2))` using `Finset.sum_le_sum fun v _ => neg_log_inf hI hW x v A s hY hk`.

Establish `b2 : ∑ᶠ w, -Real.log (nF (A.map (cW w))) ≤ ∑ᶠ w : HeightOneSpectrum (𝓞 E), (n : ℝ) * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)` using `finsum_le_finsum' hfin1 hfin3 fun w => neg_log_fin hF x w A s hY hk`. Rewrite using `[e1]`. Use `(add_le_add b1 b2).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[logSizeM, ← mul_finsum (fun w : HeightOneSpectrum (𝓞 E) => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)) (n : ℝ), ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degG_le (hF : MulF) (hI : MulI) (hW : WedgeI) (hS : SzFin) (hFS : FinSupp) (x : GA E n)
    (M : Matrix (Fin n) (Fin k) E) (s : Fin k → Fin n) (hs : M.submatrix s id = 1) (hk : k ≤ n) :
    degG x M ≤ n * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n) + logSizeM x.val) := by
  have hY := rows_mul_frame x M s hs
  set A := (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) with hA
  have hfin1 : (Function.support fun w => -Real.log (nF (A.map (cW w)))).Finite := by
    refine ((hFS E (Fin n) (Fin k) A _ hY).2.2).subset fun w hw => ?_
    intro h1
    apply hw
    simp [h1]
  have hfin2 : (Function.support fun w : HeightOneSpectrum (𝓞 E) =>
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)).Finite := by
    refine (hS E (Fin n) (Fin n) x.val).subset fun w hw => ?_
    by_contra hlt
    apply hw
    have h0 : 0 ≤ sz (x.val.map (cW w)) := sz_nonneg _
    have h1 : |sz (x.val.map (cW w))| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact not_lt.1 hlt
    exact (Real.posLog_eq_zero_iff _).2 h1
  have hfin3 : (Function.support fun w : HeightOneSpectrum (𝓞 E) =>
      (n : ℝ) * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)).Finite :=
    hfin2.subset (Function.support_const_smul_subset (n : ℝ) _)
  have e1 : degG x M = ∑ v, -Real.log (nI (A.map (cV v))) + ∑ᶠ w, -Real.log (nF (A.map (cW w))) := by
    rw [degG, finsum_neg_distrib, Finset.sum_neg_distrib, neg_add]
  have b1 : ∑ v, -Real.log (nI (A.map (cV v))) ≤
      ∑ v : InfinitePlace E, (n : ℝ) * (Real.posLog ((n : ℝ) * n) +
        Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2)) :=
    Finset.sum_le_sum fun v _ => neg_log_inf hI hW x v A s hY hk
  have b2 : ∑ᶠ w, -Real.log (nF (A.map (cW w))) ≤
      ∑ᶠ w : HeightOneSpectrum (𝓞 E), (n : ℝ) * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖) :=
    finsum_le_finsum' hfin1 hfin3 fun w => neg_log_fin hF x w A s hY hk
  rw [e1]
  refine (add_le_add b1 b2).trans (le_of_eq ?_)
  rw [logSizeM, ← mul_finsum (fun w : HeightOneSpectrum (𝓞 E) =>
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖)) (n : ℝ), ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ]
  ring

/- English proof (translation)
The claim follows from `(continuous_apply v).comp (continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst))`.
-/
theorem continuous_cV (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (continuous_apply v).comp (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst))

def intAd (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : Set (Ad E) :=
  {a | ∀ w : HeightOneSpectrum (𝓞 E), ‖cW w a‖ ≤ 1}

/- English proof (translation)
Establish `h : IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E}` using `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))`. Establish `h2 : intAd E = (pFin E) ⁻¹' {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E}`. Use extensionality with `a`. Use `forall_congr' fun w => ?_` and prove the remaining obligations. Conclude with `(Valued.toNormedField.norm_le_one_iff).trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm`.

Rewrite using `[h2]`. Conclude with `h.preimage continuous_snd`.
-/
theorem isOpen_intAd : IsOpen (intAd E) := by
  have h : IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))
  have h2 : intAd E = (pFin E) ⁻¹' {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} := by
    ext a
    refine forall_congr' fun w => ?_
    exact (Valued.toNormedField.norm_le_one_iff).trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  rw [h2]
  exact h.preimage continuous_snd

def intGA (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) : Set (GA E n) :=
  {u | (∀ i j, u.val i j ∈ intAd E) ∧ ∀ i j, (u⁻¹ : GA E n).val i j ∈ intAd E}

/- English proof (translation)
Establish `h1 : IsOpen {u : GA E n | ∀ i j, u.val i j ∈ intAd E}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_intAd.preimage (Units.continuous_val.matrix_elem i j)`. Establish `h2 : IsOpen {u : GA E n | ∀ i j, (u⁻¹ : GA E n).val i j ∈ intAd E}`. Simplify using `only [Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_intAd.preimage ((Units.continuous_val.comp continuous_inv).matrix_elem i j)`. Conclude with `h1.inter h2`.
-/
theorem isOpen_intGA : IsOpen (intGA E n) := by
  have h1 : IsOpen {u : GA E n | ∀ i j, u.val i j ∈ intAd E} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_intAd.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : IsOpen {u : GA E n | ∀ i j, (u⁻¹ : GA E n).val i j ∈ intAd E} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_intAd.preimage ((Units.continuous_val.comp continuous_inv).matrix_elem i j)
  exact h1.inter h2

/- English proof (translation)
Establish `h : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ intAd E`. Introduce `i j w`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_one]`. Conclude with `h`.
-/
theorem one_mem_intGA : (1 : GA E n) ∈ intGA E n := by
  have h : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ intAd E := by
    intro i j w
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨h, ?_⟩
  rw [inv_one]
  exact h

/- English proof (translation)
Rewrite using `[Matrix.map_mul]`. Establish `h1` using `(hF _ (Fin n) (Fin n) (Fin k) (B.map (cW w))).1 (g.map (cW w))`. Establish `h2 : sz (g.map (cW w)) ≤ 1` using `Real.iSup_le (fun p => hg p.1 p.2 w) zero_le_one`. Establish `h3 : sz (g.map (cW w)) ^ Fintype.card (Fin k) ≤ 1` using `pow_le_one₀ (sz_nonneg _) h2`. Conclude with `h1.trans (mul_le_of_le_one_left (nF_nonneg _) h3)`.
-/
theorem nF_mul_le (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (g : Matrix (Fin n) (Fin n) (Ad E))
    (hg : ∀ i j, g i j ∈ intAd E) (B : Matrix (Fin n) (Fin k) (Ad E)) :
    nF ((g * B).map (cW w)) ≤ nF (B.map (cW w)) := by
  rw [Matrix.map_mul]
  have h1 := (hF _ (Fin n) (Fin n) (Fin k) (B.map (cW w))).1 (g.map (cW w))
  have h2 : sz (g.map (cW w)) ≤ 1 := Real.iSup_le (fun p => hg p.1 p.2 w) zero_le_one
  have h3 : sz (g.map (cW w)) ^ Fintype.card (Fin k) ≤ 1 := pow_le_one₀ (sz_nonneg _) h2
  exact h1.trans (mul_le_of_le_one_left (nF_nonneg _) h3)

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `h` using `nF_mul_le hF w _ hx.1 ((x⁻¹ : GA E n).val * C)`. Rewrite `h` using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]`. Then use the resulting hypothesis. Establish `h` using `nF_mul_le hF w _ hx.2 ((x₀⁻¹ : GA E n).val * C)`. Establish `e : (x₀⁻¹ * x)⁻¹ * x₀⁻¹ = x⁻¹` using `by group`.

Rewrite `h` using `[← Matrix.mul_assoc, ← Units.val_mul, e]`. Then use the resulting hypothesis.
-/
theorem nF_eq_of_mem (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (x₀ x : GA E n) (hx : x₀⁻¹ * x ∈ intGA E n)
    (C : Matrix (Fin n) (Fin k) (Ad E)) :
    nF (((x₀⁻¹ : GA E n).val * C).map (cW w)) = nF (((x⁻¹ : GA E n).val * C).map (cW w)) := by
  refine le_antisymm ?_ ?_
  · have h := nF_mul_le hF w _ hx.1 ((x⁻¹ : GA E n).val * C)
    rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right] at h
  · have h := nF_mul_le hF w _ hx.2 ((x₀⁻¹ : GA E n).val * C)
    have e : (x₀⁻¹ * x)⁻¹ * x₀⁻¹ = x⁻¹ := by group
    rwa [← Matrix.mul_assoc, ← Units.val_mul, e] at h

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun x : GA E n => x₀⁻¹ * x) x₀` using `(continuous_const.mul continuous_id).continuousAt`. Establish `hm : intGA E n ∈ 𝓝 (x₀⁻¹ * x₀)`. Rewrite using `[inv_mul_cancel]`. Conclude with `isOpen_intGA.mem_nhds one_mem_intGA`.

Establish `hnb : ∀ᶠ x in 𝓝 x₀, x₀⁻¹ * x ∈ intGA E n` using `hc hm`. Use `ContinuousAt.congr (continuousAt_const (y := ∑ᶠ w, Real.log (nF (((x₀⁻¹ : GA E n).val * C).map (cW w))))) ?_` and prove the remaining obligations. Use `filter_upwards [hnb] with x hx`. Conclude with `finsum_congr fun w => by rw [nF_eq_of_mem hF w x₀ x hx C]`.
-/
theorem continuous_fin_part (hF : MulF) (C : Matrix (Fin n) (Fin k) (Ad E)) :
    Continuous fun x : GA E n => ∑ᶠ w, Real.log (nF (((x⁻¹ : GA E n).val * C).map (cW w))) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hc : ContinuousAt (fun x : GA E n => x₀⁻¹ * x) x₀ := (continuous_const.mul continuous_id).continuousAt
  have hm : intGA E n ∈ 𝓝 (x₀⁻¹ * x₀) := by
    rw [inv_mul_cancel]
    exact isOpen_intGA.mem_nhds one_mem_intGA
  have hnb : ∀ᶠ x in 𝓝 x₀, x₀⁻¹ * x ∈ intGA E n := hc hm
  refine ContinuousAt.congr (continuousAt_const (y := ∑ᶠ w, Real.log (nF (((x₀⁻¹ : GA E n).val * C).map (cW w))))) ?_
  filter_upwards [hnb] with x hx
  exact finsum_congr fun w => by rw [nF_eq_of_mem hF w x₀ x hx C]

/- English proof (translation)
Establish `hB : Continuous fun x : GA E n => (((x⁻¹ : GA E n).val * C).map (cV v))` using `((Units.continuous_val.comp continuous_inv).matrix_mul continuous_const).matrix_map (continuous_cV v)`. Use `Continuous.log ?_ h` and prove the remaining obligations. Conclude with `Complex.continuous_re.comp (hB.matrix_conjTranspose.matrix_mul hB).matrix_det`.
-/
theorem continuous_inf_part (v : InfinitePlace E) (C : Matrix (Fin n) (Fin k) (Ad E))
    (h : ∀ x : GA E n, nI (((x⁻¹ : GA E n).val * C).map (cV v)) ≠ 0) :
    Continuous fun x : GA E n => Real.log (nI (((x⁻¹ : GA E n).val * C).map (cV v))) := by
  have hB : Continuous fun x : GA E n => (((x⁻¹ : GA E n).val * C).map (cV v)) :=
    ((Units.continuous_val.comp continuous_inv).matrix_mul continuous_const).matrix_map (continuous_cV v)
  refine Continuous.log ?_ h
  exact Complex.continuous_re.comp (hB.matrix_conjTranspose.matrix_mul hB).matrix_det

end Adelic

/- English proof (translation)
Introduce `_ hW hF hI hS hFS _ hDB E _ _ _ n`. Use `⟨fun x => ⟨n * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n) + logSizeM x.val), ?_⟩, fun W => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨W, rfl⟩`. Take `⟨k, M, s, hk, hs, hli, hsp⟩` from `exists_normal_basis W`. Establish `h` using `hDB E n (Fin k) x M hli`.

Rewrite `h` using `[hsp]`. Rewrite using `[← h]`. Conclude with `degG_le hF hI hW hS hFS x M s hs hk`. Take `⟨k, M, s, hk, hs, hli, hsp⟩` from `exists_normal_basis W`. Establish `h : (fun x : GA E n => deg x W) = fun x => degG x M`.

Use function extensionality and compare the values at `x`. Establish `h` using `hDB E n (Fin k) x M hli`. Rewrite `h` using `[hsp]`. Conclude with `h.symm`. Rewrite using `[h]`.

Use `((continuous_finset_sum _ fun v _ => ?_).add (continuous_fin_part hF _)).neg` and prove the remaining obligations. Conclude with `continuous_inf_part v _ fun x => (hFS E (Fin n) (Fin k) _ _ (rows_mul_frame x M s hs)).1 v`.
-/
theorem degBdd_of : WedgeF → WedgeI → MulF → MulI → SzFin → FinSupp → LogAbsBasic → DegBasisG → DegBdd := by
  intro _ hW hF hI hS hFS _ hDB E _ _ _ n
  refine ⟨fun x => ⟨n * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n) + logSizeM x.val), ?_⟩, fun W => ?_⟩
  · rintro _ ⟨W, rfl⟩
    obtain ⟨k, M, s, hk, hs, hli, hsp⟩ := exists_normal_basis W
    have h := hDB E n (Fin k) x M hli
    rw [hsp] at h
    rw [← h]
    exact degG_le hF hI hW hS hFS x M s hs hk
  · obtain ⟨k, M, s, hk, hs, hli, hsp⟩ := exists_normal_basis W
    have h : (fun x : GA E n => deg x W) = fun x => degG x M := by
      funext x
      have h := hDB E n (Fin k) x M hli
      rw [hsp] at h
      exact h.symm
    rw [h]
    refine ((continuous_finset_sum _ fun v _ => ?_).add (continuous_fin_part hF _)).neg
    exact continuous_inf_part v _ fun x =>
      (hFS E (Fin n) (Fin k) _ _ (rows_mul_frame x M s hs)).1 v

end GlobalTheory.CompanionTheory.DegBound
end
