import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.SelCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogH

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ N hN hE l hl D e`. Establish `hl2 : 2 ≤ l` using `hl.out.two_le`. Take `⟨hdeg, hζ, hemb⟩` from `fnOne E Ω l`. Take `⟨f, hf⟩` from `unrInj E Ω l D e`. Take `⟨f', hf'⟩` from `unrSel (Fn E Ω l 1) Ω l hζ`.

Take `⟨hfin, hcard⟩` from `selCard (Fn E Ω l 1) l`. Establish `hH` using `logH (Fn E Ω l 1) (l * N) (by nlinarith) (hemb N hN hE)`. Use `haveI := Finite.of_injective _ (hf'.comp hf)`. Take `⟨k, hk, hc⟩` from `lenOfCard l (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))`. Establish `h1` using `(Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard`.

Rewrite `h1` using `[hc]`. Establish `hn : Module.finrank ℚ (Fn E Ω l 1) ≤ l * Module.finrank ℚ E`. Rewrite using `[← Module.finrank_mul_finrank ℚ E (Fn E Ω l 1), mul_comm]`. Conclude with `Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))`. Use `⟨k, hk.le, ?_⟩` and prove the remaining obligations.

Establish `hh : (0 : ℝ) < classNumber (Fn E Ω l 1)` using `by exact_mod_cast classNumber_pos _`. Generalize the expression as in `Module.finrank ℚ (Fn E Ω l 1) = m at *`. Generalize the expression as in `classNumber (Fn E Ω l 1) = h at *`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl2`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h` using `by exact_mod_cast h1`. Establish `h3` using `Real.log_le_log (by positivity) h2`. Rewrite `h3` using `[Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow]`. Move the coercions through the operations in `at h3 hH`. Establish `ha : Real.log 2 ≤ Real.log l` using `Real.log_le_log (by norm_num) hl'`.

Establish `hb : Real.log l ≤ Real.log ((l : ℝ) * N)` using `Real.log_le_log (by positivity) (by nlinarith)`. Establish `h2'` using `Real.log_two_gt_d9`. Establish `hn' : (m : ℝ) ≤ l * Module.finrank ℚ E` using `by exact_mod_cast hn`. Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`.

Establish `h4` using `mul_le_mul_of_nonneg_left hb hm`. Establish `h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l` using `mul_le_mul_of_nonneg_left (by linarith) hk0`. Establish `h6` using `mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Odd.gen :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N) := by
  intro E Ω _ _ _ _ _ N hN hE l hl D e
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨hdeg, hζ, hemb⟩ := fnOne E Ω l
  obtain ⟨f, hf⟩ := unrInj E Ω l D e
  obtain ⟨f', hf'⟩ := unrSel (Fn E Ω l 1) Ω l hζ
  obtain ⟨hfin, hcard⟩ := selCard (Fn E Ω l 1) l
  have hH := logH (Fn E Ω l 1) (l * N) (by nlinarith) (hemb N hN hE)
  haveI := Finite.of_injective _ (hf'.comp hf)
  obtain ⟨k, hk, hc⟩ := lenOfCard l (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))
  have h1 := (Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard
  rw [hc] at h1
  have hn : Module.finrank ℚ (Fn E Ω l 1) ≤ l * Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ E (Fn E Ω l 1), mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))
  refine ⟨k, hk.le, ?_⟩
  have hh : (0 : ℝ) < classNumber (Fn E Ω l 1) := by exact_mod_cast classNumber_pos _
  generalize Module.finrank ℚ (Fn E Ω l 1) = m at *
  generalize classNumber (Fn E Ω l 1) = h at *
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow] at h3
  push_cast at h3 hH
  have ha : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl'
  have hb : Real.log l ≤ Real.log ((l : ℝ) * N) := Real.log_le_log (by positivity) (by nlinarith)
  have h2' := Real.log_two_gt_d9
  have hn' : (m : ℝ) ≤ l * Module.finrank ℚ E := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hb hm
  have h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l := mul_le_mul_of_nonneg_left (by linarith) hk0
  have h6 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)
  nlinarith
