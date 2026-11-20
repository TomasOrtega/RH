import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex`. Establish `hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr` using `Pr) cst.sharp i P.1 a a := fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩`. Break down `j with _ | i` into its components or cases. Take `⟨b, hb⟩` from `hL.zero_uniq`. Use `⟨b, fun P => ?_, fun b' _ => hb b'⟩` and prove the remaining obligations.

Take `⟨b₀, hb₀⟩` from `hex P`. Rewrite using `[← hb₀, hL.zero_h, hL.zero_h]`. Establish `hi : i < s` using `by omega choose bP hbP using hex`. Take `⟨b, hb⟩` from `hL.surj i hi hh (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg) (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg) (fun P => by`. Take `⟨al, hal⟩` from `hL.nonvan i hi (bP P) P`.

Conclude with `⟨al, hbP P ▸ hal⟩)`. Use `⟨b, fun P => ?_, fun b' hb' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hb P`. Rewrite `h1`, the goal using `[← hbP P]`. Conclude with `hP (i + 1) b (bP P) P h1`.

Use `hL.inj i hi b' b (fun P => ?_)` and prove the remaining obligations. Establish `e : L.h (i + 1) b' P = L.h (i + 1) b P`. Establish `h1` using `hb P`. Rewrite `*` using `[hb' P, ← hbP P]`. Conclude with `(hP (i + 1) b (bP P) P h1).symm`.

Rewrite using `[e]`. Conclude with `hrefl _ _ _`.
-/
theorem idxIsProd_of_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  intro X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex
  have hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr := Pr) cst.sharp i P.1 a a :=
    fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  rcases j with _ | i
  · obtain ⟨b, hb⟩ := hL.zero_uniq
    refine ⟨b, fun P => ?_, fun b' _ => hb b'⟩
    obtain ⟨b₀, hb₀⟩ := hex P
    rw [← hb₀, hL.zero_h, hL.zero_h]
  · have hi : i < s := by omega
    choose bP hbP using hex
    obtain ⟨b, hb⟩ := hL.surj i hi hh
      (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg)
      (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg)
      (fun P => by
        obtain ⟨al, hal⟩ := hL.nonvan i hi (bP P) P
        exact ⟨al, hbP P ▸ hal⟩)
    refine ⟨b, fun P => ?_, fun b' hb' => ?_⟩
    · have h1 := hb P
      rw [← hbP P] at h1 ⊢
      exact hP (i + 1) b (bP P) P h1
    · refine hL.inj i hi b' b (fun P => ?_)
      have e : L.h (i + 1) b' P = L.h (i + 1) b P := by
        have h1 := hb P
        rw [hb' P, ← hbP P] at *
        exact (hP (i + 1) b (bP P) P h1).symm
      rw [e]; exact hrefl _ _ _

end GlobalTheory.TwBridge
