import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistAbsPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SegExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [nabs]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]`.
-/
theorem nabs_pow_nat (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]

/- English proof (translation)
Establish `h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ)` using `by push_cast; rfl`. Rewrite using `[h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _), Real.rpow_natCast]`.
-/
theorem norm_absPow_nat (n : ℕ) (u : kˣ) : ‖((absPow k ((n : ℕ) : ℂ) u : ℂˣ) : ℂ)‖ = nabs k u ^ n := by
  have h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; rfl
  rw [h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _),
    Real.rpow_natCast]

/- English proof (translation)
Establish `h2 : 2 ∣ l * (l - 1)` using `(Nat.even_mul_pred_self l).two_dvd`. Rewrite using `[Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]`. Evaluate the numerical expressions.
-/
theorem cast_tri (l : ℕ) (hl : 0 < l) : (((l * (l - 1) / 2 : ℕ)) : ℝ) = (l : ℝ) * ((l : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ l * (l - 1) := (Nat.even_mul_pred_self l).two_dvd
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]
  norm_num

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc`. Establish `h2` using `hy t _ h1`. Establish `hdeg : y.1 = Δ.len * Δ.d` using `hL.deg_eq.symm`. Establish `hα : 0 < nabs k t` using `nabs_pos' k t`. Establish `hlog : Real.log (nabs k t) ≠ 0` using `Real.log_ne_zero_of_pos_of_ne_one hα ht.ne`.

Rewrite `h2` using `[norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le, ← Real.rpow_add hα]`. Establish `h3` using `congrArg Real.log h2`. Rewrite `h3` using `[Real.log_rpow hα, Real.log_rpow hα]`. Establish `h4` using `mul_right_cancel₀ hlog h3`. Rewrite `h4` using `[cast_tri _ Δ.len_pos, hdeg]`.

Establish `hl : (0 : ℝ) < Δ.len` using `by exact_mod_cast Δ.len_pos`. Establish `hd : (0 : ℝ) < Δ.d` using `by exact_mod_cast Δ.d_pos`. Move the coercions through the operations in `at h4`. Establish `h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0` using `by linear_combination -h4`. Establish `h6` using `(mul_eq_zero.1 h5).resolve_left (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponent_lseg (Δ : Segment k) (y : IrrGL k) (s e : ℝ) (t : kˣ) (c : ℂ) (ht : nabs k t < 1)
    (hL : IsLSeg Δ y.rep) (hc : Zl.ScalarBy Δ.first t c) (hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e))
    (hy : ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) :
    s = e + ((Δ.len : ℝ) - 1) / 2 := by
  have h1 := GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc
  have h2 := hy t _ h1
  have hdeg : y.1 = Δ.len * Δ.d := hL.deg_eq.symm
  have hα : 0 < nabs k t := nabs_pos' k t
  have hlog : Real.log (nabs k t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hα ht.ne
  rw [norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le,
    ← Real.rpow_add hα] at h2
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow hα, Real.log_rpow hα] at h3
  have h4 := mul_right_cancel₀ hlog h3
  rw [cast_tri _ Δ.len_pos, hdeg] at h4
  have hl : (0 : ℝ) < Δ.len := by exact_mod_cast Δ.len_pos
  have hd : (0 : ℝ) < Δ.d := by exact_mod_cast Δ.d_pos
  push_cast at h4
  have h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0 := by linear_combination -h4
  have h6 := (mul_eq_zero.1 h5).resolve_left (by positivity)
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `hl.2.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `Segment.mem_carrier.1 hx`. Use `Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, IrrGL.nu_nu]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem len_lt_of_precedes {Δ Δ' : Segment k} {j : ℕ} (hl : Δ.Linked Δ') (hf : Δ'.first = Δ.first.nu j) :
    Δ.len < j + Δ'.len := by
  by_contra hcon
  refine hl.2.2 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
  refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
  rw [hf, IrrGL.nu_nu]
  push_cast
  rfl

/- English proof (translation)
Introduce `k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP`. Take `⟨hlink, j, hj, hf⟩` from `hP`. Take `⟨t, ht⟩` from `GlobalTheory.T.exists_unit_pow_tendsto_zero' k`. Establish `hα1 : nabs k t < 1` using `GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht`. Establish `hα : 0 < nabs k t` using `nabs_pos' k t`.

Take `⟨e, he⟩` from `GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1`. Take `⟨c, hc⟩` from `GlobalTheory.T.central_character_exists k Δ.first t`. Establish `hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e)` using `he t c hc`. Establish `hdd : Δ'.d = Δ.d` using `congrArg Sigma.fst hf`. Establish `hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ))`.

Rewrite using `[hf]`. Conclude with `GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc`. Establish `hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ = nabs k t ^ ((Δ'.d : ℝ) * (e + j))`. Rewrite using `[norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_add hα]`. Use `congr 1`.

Use `show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `exponent_lseg Δ y s e t c hα1 hL hc hcn hy`. Establish `h2` using `exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'`. Establish `h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len` using `by exact_mod_cast len_lt_of_precedes hlink hf`.

Establish `h4 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Rewrite using `[h1, h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponent_lt_of_precedes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL k) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  intro k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP
  obtain ⟨hlink, j, hj, hf⟩ := hP
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hα1 : nabs k t < 1 := GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have hα : 0 < nabs k t := nabs_pos' k t
  obtain ⟨e, he⟩ := GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.central_character_exists k Δ.first t
  have hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e) := he t c hc
  have hdd : Δ'.d = Δ.d := congrArg Sigma.fst hf
  have hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)) := by
    rw [hf]
    exact GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc
  have hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((Δ'.d : ℝ) * (e + j)) := by
    rw [norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_add hα]
    congr 1
    show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _
    ring
  have h1 := exponent_lseg Δ y s e t c hα1 hL hc hcn hy
  have h2 := exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'
  have h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast len_lt_of_precedes hlink hf
  have h4 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [h1, h2]
  linarith

end GlobalTheory.CompanionTheory.SegExp
