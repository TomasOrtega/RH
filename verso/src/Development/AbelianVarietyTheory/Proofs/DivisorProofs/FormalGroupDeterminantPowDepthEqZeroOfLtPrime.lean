import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `(le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)`.
-/
theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Rewrite using `[Int.cast_natCast]`. Conclude with `val_natCast_nonneg v m`. Rewrite using `[Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]`. Conclude with `val_natCast_nonneg v m`.
-/
theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

/- English proof (translation)
Establish `h0` using `val_natCast_nonneg v n`. Use `le_antisymm ?_ h0` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hb` using `Nat.gcd_eq_gcd_ab p n`.

Rewrite `hb` using `[((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one]`. Establish `key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C)`. Use `congrArg (fun z : ℤ => (z : C)) hb` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `one_pos' : (0 : WithTop ℝ) < 1` using `by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)`. Establish `h1 : 0 < v ((p : C) * (Nat.gcdA p n : C))`. Rewrite using `[AddValuation.map_mul, hv]`. Conclude with `add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)`. Establish `h2 : 0 < v ((n : C) * (Nat.gcdB p n : C))`.

Rewrite using `[AddValuation.map_mul]`. Conclude with `add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)`. Establish `hsum` using `AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))`. Rewrite `hsum` using `[← key, AddValuation.map_one]`. Conclude with `absurd hsum (not_le.2 (lt_min h1 h2))`.
-/
theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

/- English proof (translation)
Introduce `C _ _ v p hp hv i d c G u hu hc`. Take `⟨hlo, hcont, -⟩` from `GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu`. Take `⟨-, -, hone, hrow⟩` from `GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c`. Use `set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀`. Establish `hmem : α₀ ∈ (detPow C i c).support`.

Rewrite using `[MvPolynomial.mem_support_iff, hone]`. Conclude with `one_ne_zero`. Establish `hfact : v (mfact α₀ : C) = 0`. Establish `hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C)`. Unfold `mfact`.

Rewrite using `[Nat.cast_finsuppProd]`. Rewrite using `[hcast]`. Apply `val_natCast_eq_zero v p hp hv` to reduce the goal to its premises. Introduce `hdvd`. Rewrite `hdvd` using `[Finsupp.prod]`.

Take `⟨x, -, hx⟩` from `(Prime.dvd_finsetProd_iff hp.prime _).1 hdvd`. Rewrite `hx` using `[hp.dvd_factorial]`. Take `⟨b, a⟩` from `x`. Establish `hle : α₀ ⟨b, a⟩ ≤ c`. Rewrite using `[← (hrow α₀ hmem).1 a]`.

Conclude with `Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)`. Use linear arithmetic over natural numbers and integers. Establish `hle : content v (detPow C i c) ≤ 0`. Unfold `content`. Use `(iInf₂_le α₀ hmem).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hone, one_mul, hfact]`. Both sides reduce to the same expression. Conclude with `le_antisymm (hcont.trans hle) hlo`.
-/
theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
