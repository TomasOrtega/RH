import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransvMemZGam
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.MaxCuspCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.CuspCentre.latZ E r ρ Unit (fun _ => X) ⟨(), cu⟩`.
-/
theorem basis_exists (X : Data E r) (cu : CuspFD X ρ) : ∃ bs, IsZBasis X cu bs :=
  GlobalTheory.CuspCentre.latZ E r ρ Unit (fun _ => X) ⟨(), cu⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.FJCuspCheck.cuspOfIso X ξ h.2.2 h.2.1, Submodule.subset_span ⟨0, rfl⟩⟩`.
-/
theorem cover_one (X : Data E r) (ξ : Fin r → E) (h : X.IsIso ξ) :
    ∃ cu : CuspFD X 1, ξ ∈ Submodule.span E (Set.range cu.e) :=
  ⟨GlobalTheory.FJCuspCheck.cuspOfIso X ξ h.2.2 h.2.1, Submodule.subset_span ⟨0, rfl⟩⟩

/- English proof (translation)
Take `⟨n, hn, h⟩` from `X.χ_fin 0`. Establish `h1` using `X.χ_add 0 0 γ hγ`. Rewrite `h1` using `[add_zero]`. Establish `h0 : X.χ 0 γ ≠ 0` using `fun h0 => by`. Use `h γ hγ` as an intermediate fact.

Rewrite `this` using `[h0, zero_pow hn.ne']`. Conclude with `zero_ne_one this`. Establish `h2 : X.χ 0 γ * 1 = X.χ 0 γ * X.χ 0 γ` using `by rw [mul_one]; exact h1`. Conclude with `(mul_left_cancel₀ h0 h2).symm`.
-/
theorem chi_zero (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  have h0 : X.χ 0 γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h2 : X.χ 0 γ * 1 = X.χ 0 γ * X.χ 0 γ := by rw [mul_one]; exact h1
  exact (mul_left_cancel₀ h0 h2).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => by simp [cc], fun k => ⟨0, by simp [phZ, prE]⟩⟩`.
-/
theorem isExpo_zero (X : Data E r) (cu : CuspFD X ρ) : IsExpoFD X cu 0 :=
  ⟨fun a b => by simp [cc], fun k => ⟨0, by simp [phZ, prE]⟩⟩

/- English proof (translation)
Take `⟨a, ha, hΛ⟩` from `exists_smul_mem X (cu.e 0)`. Use `⟨Pi.single 0 (a : E), ?_, ?_, by simpa [hq] using hc⟩` and prove the remaining obligations. Introduce `h`. Use `congrFun h 0` as an intermediate fact. Simplify using `only [Pi.single_eq_same, Pi.zero_apply] at this`.

Conclude with `ha (by exact_mod_cast this)`. Rewrite using `[Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using `using hΛ`.
-/
theorem killed_zero (X : Data E r) (cu : CuspFD X (ρ + 1)) {c : ℝ} (hc : 0 ≤ c) :
    KilledFD X cu 0 c := by
  obtain ⟨a, ha, hΛ⟩ := exists_smul_mem X (cu.e 0)
  refine ⟨Pi.single 0 (a : E), ?_, ?_, by simpa [hq] using hc⟩
  · intro h
    have := congrFun h 0
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact ha (by exact_mod_cast this)
  · rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]
    simpa using hΛ

/- English proof (translation)
Establish `h1 : IsHermE (1 : Matrix (Fin ρ) (Fin ρ) E)` using `fun a b => by`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[cc]`. Simplify using `[cc, Matrix.one_apply, h, Ne.symm h]`.

Establish `hq' : ∀ k, ∃ q : ℚ, phZ X cu 1 k = q` using `fun k => by`. Establish `hr` using `GlobalTheory.FJCuspCheck.pair_real X 1 (zBas X cu k) h1 (zBas_skew X cu (basis_exists X cu) k)`. Use `set y := Matrix.trace ((1 : Matrix (Fin ρ) (Fin ρ) E).transpose * zBas X cu k) / (X.κ0 / 2)`. Use `⟨Algebra.trace ℚ E (y / 2), ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.HermExpo.sum_re_eq_trace X]`.

Establish `: y / 2 + cc (y / 2) = y`. Unfold `cc at hr ⊢`. Rewrite using `[map_div₀, hr, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `choose q hq'' using hq'`. Use `⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).den_pos, fun a b => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `h1 a b` as an intermediate fact. Unfold `cc at this ⊢`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, this]`. Establish `e : ∀ n : ℕ, phZ X cu ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) k = n * phZ X cu 1 k`. Introduce `n`. Simplify using `only [phZ, prE, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, mul_div_assoc, map_mul, map_natCast]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)`. Use `⟨d * (q k).num, ?_⟩` and prove the remaining obligations. Establish `hk : ((q k : ℚ) : ℝ) * ((q k).den : ℝ) = ((q k).num : ℝ)`. Conclude with `Rat.mul_den_eq_num (q k)` after adjusting the coercions.

Rewrite using `[e, hq'', hd]`. Use `push_cast`. Rewrite using `[← hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_expo_scalar (X : Data E r) (cu : CuspFD X ρ) :
    ∃ n : ℕ, 0 < n ∧ IsExpoFD X cu ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) := by
  have h1 : IsHermE (1 : Matrix (Fin ρ) (Fin ρ) E) := fun a b => by
    by_cases h : a = b
    · subst h; simp [cc]
    · simp [cc, Matrix.one_apply, h, Ne.symm h]
  have hq' : ∀ k, ∃ q : ℚ, phZ X cu 1 k = q := fun k => by
    have hr := GlobalTheory.FJCuspCheck.pair_real X 1 (zBas X cu k) h1
      (zBas_skew X cu (basis_exists X cu) k)
    set y := Matrix.trace ((1 : Matrix (Fin ρ) (Fin ρ) E).transpose * zBas X cu k) / (X.κ0 / 2)
    refine ⟨Algebra.trace ℚ E (y / 2), ?_⟩
    rw [← GlobalTheory.HermExpo.sum_re_eq_trace X]
    have : y / 2 + cc (y / 2) = y := by
      unfold cc at hr ⊢
      rw [map_div₀, hr, map_ofNat]; ring
    rw [this]
    rfl
  choose q hq'' using hq'
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).den_pos, fun a b => ?_, fun k => ?_⟩
  · have := h1 a b
    unfold cc at this ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, this]
  · have e : ∀ n : ℕ, phZ X cu ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) k = n * phZ X cu 1 k := by
      intro n
      simp only [phZ, prE, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
        Finset.mul_sum, mul_div_assoc, map_mul, map_natCast]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
    refine ⟨d * (q k).num, ?_⟩
    have hk : ((q k : ℚ) : ℝ) * ((q k).den : ℝ) = ((q k).num : ℝ) := by
      exact_mod_cast Rat.mul_den_eq_num (q k)
    rw [e, hq'', hd]
    push_cast
    rw [← hk]
    ring

/- English proof (translation)
Introduce and unpack `⟨η, hη, -, h⟩`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hη`. Establish `hne : Nonempty X.Ψ`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `hτ : τ ∈ X.Ψ`.

Conclude with `⟨⟨τ, hτ⟩⟩`. Assume the negation of the conclusion as `h'`. Conclude with `hτ ((X.cmType τ).2 fun h'' => h' ⟨⟨_, h''⟩⟩)`. Establish `hv : ∀ τ : X.Ψ, (τ.1 (hq ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) η)).re = ∑ b, n * Complex.normSq (τ.1 (η b))` using `fun τ => by`. Simplify using `only [hq, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul, map_natCast, GlobalTheory.FJCuspCheck.emb_cc, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, Complex.mul_conj]`. Simplify using `[mul_comm]`. Establish `hpos : 0 < ∑ τ : X.Ψ, (τ.1 (hq ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) η)).re`. Use `Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty` and prove the remaining obligations.

Rewrite using `[hv]`. Use `Finset.sum_pos' (fun b _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) ⟨a, Finset.mem_univ _, mul_pos (Nat.cast_pos.2 hn) (Complex.normSq_pos.2 ?_)⟩` and prove the remaining obligations. Simplify using `using ha`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_killed_scalar (X : Data E r) (cu : CuspFD X ρ) {n : ℕ} (hn : 0 < n) {c : ℝ}
    (hc : c ≤ 0) : ¬ KilledFD X cu ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) c := by
  rintro ⟨η, hη, -, h⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hη
  have hne : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ X.Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · by_contra h'
      exact hτ ((X.cmType τ).2 fun h'' => h' ⟨⟨_, h''⟩⟩)
  have hv : ∀ τ : X.Ψ, (τ.1 (hq ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) η)).re =
      ∑ b, n * Complex.normSq (τ.1 (η b)) := fun τ => by
    simp only [hq, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      map_natCast, GlobalTheory.FJCuspCheck.emb_cc, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_right_comm, Complex.mul_conj]
    simp [mul_comm]
  have hpos : 0 < ∑ τ : X.Ψ, (τ.1 (hq ((n : E) • (1 : Matrix (Fin ρ) (Fin ρ) E)) η)).re := by
    refine Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty
    rw [hv]
    refine Finset.sum_pos' (fun b _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
      ⟨a, Finset.mem_univ _, mul_pos (Nat.cast_pos.2 hn) (Complex.normSq_pos.2 ?_)⟩
    simpa using ha
  linarith

/- English proof (translation)
Take `⟨X, -, -, hd, ⟨ξ, hξ⟩, -⟩` from `GlobalTheory.exists_cuspData_hyperbolic`. Take `⟨cu, -⟩` from `cover_one X.toData ξ hξ`. Take `⟨n, hn, he⟩` from `exists_expo_scalar X.toData cu`. Conclude with `⟨_, _, _, _, X.toData, hd, ⟨ξ, hξ⟩, cover_one _, basis_exists _, chi_zero _, cu, 0, _, isExpo_zero _ cu, killed_zero _ cu le_rfl, he, not_killed_scalar _ cu hn le_rfl⟩`.
-/
theorem premises_model : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
    (X : Data E 2), X.dom.Nonempty ∧ (∃ ξ, X.IsIso ξ) ∧
    (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X 1, ξ ∈ Submodule.span E (Set.range cu.e)) ∧
    (∀ cu : CuspFD X 1, ∃ bs, IsZBasis X cu bs) ∧
    (∀ γ ∈ X.Γ, X.χ 0 γ = 1) ∧
    ∃ (cu : CuspFD X 1) (χ χ' : Matrix (Fin 1) (Fin 1) E), IsExpoFD X cu χ ∧ KilledFD X cu χ 0 ∧
      IsExpoFD X cu χ' ∧ ¬ KilledFD X cu χ' 0 := by
  obtain ⟨X, -, -, hd, ⟨ξ, hξ⟩, -⟩ := GlobalTheory.exists_cuspData_hyperbolic
  obtain ⟨cu, -⟩ := cover_one X.toData ξ hξ
  obtain ⟨n, hn, he⟩ := exists_expo_scalar X.toData cu
  exact ⟨_, _, _, _, X.toData, hd, ⟨ξ, hξ⟩, cover_one _, basis_exists _, chi_zero _, cu, 0, _,
    isExpo_zero _ cu, killed_zero _ cu le_rfl, he, not_killed_scalar _ cu hn le_rfl⟩

end GlobalTheory.MaxCuspCheck
