import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAddChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AtTypeExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Compl
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, hs, e⟩`. Establish `h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_eq_one_iff).2 hs`.

Establish `h2` using `congrArg (P.valuation E) e`. Rewrite `h2` using `[map_mul, h1, one_mul]`. Rewrite using `[h2]`. Conclude with `HeightOneSpectrum.valuation_le_one P r`. Introduce `h`.

Take `⟨r, s, e⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h`. Conclude with `⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩`.
-/
theorem intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, e⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
    have h2 := congrArg (P.valuation E) e
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one P r
  · intro h
    obtain ⟨r, s, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h
    exact ⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩

/- English proof (translation)
Establish `hm : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal` using `Ideal.absNorm_mem _`. Establish `e : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E)` using `by simp`. Rewrite using `[e, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h1` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 1).2 (by simpa using hm)`. Establish `h2` using `mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 2).1 h`.

Establish `h0 : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0` using `fun h0 => h2 (by rw [h0]; exact zero_le')`. Rewrite `h1`, `h2`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h1`, `h2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Move the coercions through the operations in `at h1 h2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_norm (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    P.valuation E ((qOf P : ℕ) : E) = WithZero.exp (-1 : ℤ) := by
  have hm : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E) := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 1).2 (by simpa using hm)
  have h2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 2).1 h
  have h0 : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField P ∃ ϖ : (P.adicCompletion E)ˣ, IsCompl P (qOf P) (algebraMap E (P.adicCompletion E)) ϖ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by letI := GlobalTheory.LocalData.complRel P haveI := GlobalTheory.LocalData.isLocalFi …`.
-/
theorem exists_compl (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    letI := GlobalTheory.LocalData.complRel P
    haveI := GlobalTheory.LocalData.isLocalField P
    ∃ ϖ : (P.adicCompletion E)ˣ, IsCompl P (qOf P) (algebraMap E (P.adicCompletion E)) ϖ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hq := valuation_norm P h
  have hv : Valued.v (algebraMap E (P.adicCompletion E) ((qOf P : ℕ) : E)) = WithZero.exp (-1 : ℤ) := by
    rw [← hq]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  have h0 : algebraMap E (P.adicCompletion E) ((qOf P : ℕ) : E) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hE : (valuation (P.adicCompletion E)).IsEquiv (Valued.v : Valuation (P.adicCompletion E) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  refine ⟨Units.mk0 _ h0, ⟨fun a => ?_, HeightOneSpectrum.denseRange_algebraMap E P, rfl, rfl⟩, fun x => ?_⟩
  · rw [intAt_iff, Valuation.mem_integer_iff, hE.le_one_iff_le_one,
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P a]
    rfl
  · rw [hE.lt_one_iff_lt_one, hE x, Units.val_mk0, hv]
    by_cases hx : Valued.v x = 0
    · simp [hx]
    · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
      omega

end Compl

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P s hP hs hok hsh hA hpsi hq`. Use `letI := GlobalTheory.LocalData.complRel P.1`. Use `haveI := GlobalTheory.LocalData.isLocalField P.1`. Take `⟨ϖ, hc, hu⟩` from `exists_compl P.1 hq`. Establish `hne : psi0P Ch P.1 ≠ 1` using `fun h => by`.

Establish `h1` using `hpsi 1 ((intAt_iff P.1 1).2 (by simp))`. Rewrite `h1` using `[h, one_div]`. Conclude with `hok.psi_ne P (by simpa using h1)`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, rfl⟩ : ∃ ρ, s = 2 * ρ := by`. Take `⟨b, hb⟩` from `R.m_even`.

Conclude with `⟨b - 1, by omega⟩`. Take `⟨S, hS⟩` from `GlobalTheory.SymTieExists.exists_tie X.E X.K (P.1.adicCompletion X.E) P.1 (qOf P.1) _ ϖ σ₀ (psi0P Ch P.1) (chiP Ch P.1) ρ R.k hc hu hne`. Conclude with `⟨_, _, _, _, inferInstance, _, S, hP, hs, hok, hsh, hA, hpsi, hS⟩`.
-/
theorem exists_atType : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (s : ℕ), P.1 ∈ Pr.vGs → R.m = s + 2 → cst.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ a, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : X.E →+* k) (S : SymData k s R.k), AtType Ch sel mu cst σ₀ P ι S := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P s hP hs hok hsh hA hpsi hq
  letI := GlobalTheory.LocalData.complRel P.1
  haveI := GlobalTheory.LocalData.isLocalField P.1
  obtain ⟨ϖ, hc, hu⟩ := exists_compl P.1 hq
  have hne : psi0P Ch P.1 ≠ 1 := fun h => by
    have h1 := hpsi 1 ((intAt_iff P.1 1).2 (by simp))
    rw [h, one_div] at h1
    exact hok.psi_ne P (by simpa using h1)
  obtain ⟨ρ, rfl⟩ : ∃ ρ, s = 2 * ρ := by
    obtain ⟨b, hb⟩ := R.m_even
    exact ⟨b - 1, by omega⟩
  obtain ⟨S, hS⟩ := GlobalTheory.SymTieExists.exists_tie X.E X.K (P.1.adicCompletion X.E) P.1 (qOf P.1) _ ϖ σ₀ (psi0P Ch P.1)
    (chiP Ch P.1) ρ R.k hc hu hne
  exact ⟨_, _, _, _, inferInstance, _, S, hP, hs, hok, hsh, hA, hpsi, hS⟩

/- English proof (translation)
Use `⟨fun κ τ j => ?_, fun κ τ l j => ?_, fun A n c pos d hd => ?_, fun A n N pos d hd hN => ?_⟩` and prove the remaining obligations. Use `⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr (by ring)), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro ((i | i) | ⟨i, i'⟩) <;> simp [xPos, finProdFinEquiv]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rintro ((i | i) | ⟨i, i'⟩) <;> simp [zPos, finProdFinEquiv]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(Equiv.sumCongr d (Equiv.refl _)).trans finSumFinEquiv, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i)`. Simplify `hd i` using `[yPos]`.

Simplify using `[yPos]`. Substitute `hN` using the available equality. Use `⟨(Equiv.sumCongr d (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i)`. Simplify using `using hd i`.

Simplify using the standard rewrite rules.
-/
theorem exists_ord : (∀ κ τ j : ℕ, ∃ e : XIx (Fin κ) (Fin τ) j ≃ Fin (κ + j * (τ + 1)), IsOrd xPos e) ∧ (∀ κ τ l j : ℕ, ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ), IsOrd zPos e) ∧ (∀ (A : Type) (n c : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → ∃ e : A ⊕ Fin c ≃ Fin (n + c), IsOrd (yPos pos n) e) ∧ (∀ (A : Type) (n N : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → N = n + 1 → ∃ e : A ⊕ Unit ≃ Fin N, IsOrd (Sum.elim pos fun _ => N - 1) e) := by
  refine ⟨fun κ τ j => ?_, fun κ τ l j => ?_, fun A n c pos d hd => ?_, fun A n N pos d hd hN => ?_⟩
  · refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr (by ring)), ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [xPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [zPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr d (Equiv.refl _)).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa [yPos] using hd i
    · simp [yPos]
  · subst hN
    refine ⟨(Equiv.sumCongr d (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa using hd i
    · simp

end GlobalTheory.AtTypeExists
