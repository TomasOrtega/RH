import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

/- English proof (translation)
Establish `hinj` using `D.R.toFrame.tau1_injective`. Establish `hP` using `factPlaces D.R.toFrame`. Establish `h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z` using `by simp [tauPl]`. Unfold `topsOf`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Rewrite using `[h0]`. Unfold `Host.topPlaces`. Rewrite using `[Finset.mem_image]`. Take `⟨b, t⟩` from `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t', ht, h⟩`. Apply the tactic sequence `cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h`. Conclude with `⟨rfl, (hinj h) ▸ ht⟩`. Conclude with `absurd h (hP.2 _ _)`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨t, h2, ?_⟩` and prove the remaining obligations. Simplify using `only at h1`. Simplify using `[Formalism.MainNotions.G.plGG, h1]`.
-/
theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

/- English proof (translation)
Introduce and unpack `D large₂ EX ⟨n, hn⟩ u`. Establish `hfl : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del` using `by rw [hn, Nat.floor_natCast]`. Use `⟨⟨fun τ => ⟨D.hc τ, rfl⟩, BadPrimesPeriodBound.recWts_row EX, ?_, ?_⟩, fun z => mem_tops_rec D z, fun z => ⟨BadPrimesPeriodBound.recWts_row EX u _, fun i => ?_⟩⟩` and prove the remaining obligations. Introduce `a b τ h`. Conclude with `(D.hcW_first a τ h).trans (D.hcW_first b τ h).symm`.

Introduce `a b τ h`. Establish `h' : D.R.k - 1 < D.R.k` using `h`. Establish `h0 : 0 < D.R.k` using `by omega`. Conclude with `(D.hcW_last a τ h0).trans (D.hcW_last b τ h0).symm`. Use `show (D.hcW u (tauPl D z)).u i = _`.

Unfold `NumDatum.uW`. Take `⟨i, hi⟩` from `i`. Establish `hi' : i < D.R.k` using `hi`. Distinguish the cases in `h : 1 ≤ i ∧ i + 1 < D.R.k`. Rewrite using `[dif_pos h]`.

Take `⟨l, rfl⟩ : ∃ l, i = l + 1` from `⟨i - 1, by omega⟩`. Establish `hl : l < D.R.k - 2` using `by omega`. Establish `a` using `D.s.u_letter u (tauPl D z) l hl`. Rewrite `a` using `[D.hcW_v, ← hfl]`. Conclude with `a`.

Rewrite using `[dif_neg h]`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality. Conclude with `D.hcW_first u _ hi'`. Establish `h1 : i = D.R.k - 1` using `by omega`.

Substitute `h1` using the available equality. Conclude with `D.hcW_last u _ (by omega)`.
-/
theorem weightTie_rec : ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), (∃ n : ℕ, D.s.Del = n) → ∀ (u : D.what₂.Word),
    PlaceLogThetaBounds.WeightTie (numDatumOfParameters D large₂) (Pr := recPrimes EX) (recWts EX) (plRec D) u (codeRec large₂ u) := by
  rintro D large₂ EX ⟨n, hn⟩ u
  have hfl : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨⟨fun τ => ⟨D.hc τ, rfl⟩, BadPrimesPeriodBound.recWts_row EX, ?_, ?_⟩, fun z => mem_tops_rec D z,
    fun z => ⟨BadPrimesPeriodBound.recWts_row EX u _, fun i => ?_⟩⟩
  · intro a b τ h
    exact (D.hcW_first a τ h).trans (D.hcW_first b τ h).symm
  · intro a b τ h
    have h' : D.R.k - 1 < D.R.k := h
    have h0 : 0 < D.R.k := by omega
    exact (D.hcW_last a τ h0).trans (D.hcW_last b τ h0).symm
  · show (D.hcW u (tauPl D z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < D.R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < D.R.k
    · rw [dif_pos h]
      obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      have hl : l < D.R.k - 2 := by omega
      have a := D.s.u_letter u (tauPl D z) l hl
      rw [D.hcW_v, ← hfl] at a
      exact a
    · rw [dif_neg h]
      by_cases h0 : i = 0
      · subst h0
        exact D.hcW_first u _ hi'
      · have h1 : i = D.R.k - 1 := by omega
        subst h1
        exact D.hcW_last u _ (by omega)

end GlobalTheory.ColumnNormCompare
