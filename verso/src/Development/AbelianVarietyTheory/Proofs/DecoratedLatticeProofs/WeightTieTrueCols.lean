import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

/- English proof (translation)
Introduce `B X I _ l Z L hD u`. Take `⟨n, hn⟩` from `hD`. Establish `hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del` using `by rw [hn, Nat.floor_natCast]`. Use `⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z`.

Conclude with `B.wts_isOk.hc_row u _`. Express the relevant statement in the definitionally equal form `((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _`. Unfold `NumDatum.uW`. Take `⟨i, hi⟩` from `i`. Establish `hi' : i < (I.rec7 l Z).R.k` using `hi`.

Distinguish the cases in `h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k`. Rewrite using `[dif_pos h]`. Take `⟨k, rfl⟩ : ∃ k, i = k + 1` from `⟨i - 1, by omega⟩`. Establish `hk : k < (I.rec7 l Z).R.k - 2` using `by omega`. Establish `a` using `(I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk`.

Establish `hv` using `(I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)`. Rewrite using `[a, hv, ← hfl]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h]`. Distinguish the cases in `h0 : i = 0`.

Substitute `h0` using the available equality. Conclude with `(I.rec7 l Z).hcW_first u _ hi'`. Establish `h1 : i = (I.rec7 l Z).R.k - 1` using `by omega`. Substitute `h1` using the available equality. Conclude with `(I.rec7 l Z).hcW_last u _ (by omega)`.
-/
theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), DelNat (I.rec7 l Z) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (I.rec7 l Z) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (I.rec7 l Z)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z
  · exact B.wts_isOk.hc_row u _
  · change ((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (I.rec7 l Z).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k
    · rw [dif_pos h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (I.rec7 l Z).R.k - 2 := by omega
      have a := (I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk
      have hv := (I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dif_neg h]
      by_cases h0 : i = 0
      · subst h0
        exact (I.rec7 l Z).hcW_first u _ hi'
      · have h1 : i = (I.rec7 l Z).R.k - 1 := by omega
        subst h1
        exact (I.rec7 l Z).hcW_last u _ (by omega)

end GlobalTheory.CoreHt
