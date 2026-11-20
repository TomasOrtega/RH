import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.DualLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Rewrite using `[← algebraMap_smul E c z, map_smul, algebraMap_smul]`.
-/
theorem hStd_osmul_right (y : Sp E n) (c : 𝓞 E) (z : Sp E n) :
    hStd E n y (c • z) = c • hStd E n y z := by
  rw [← algebraMap_smul E c z, map_smul, algebraMap_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Take `⟨s, hs, hsx⟩` from `(mem_locP Q _ x).1 hx`. Take `⟨t, ht, hty⟩` from `(mem_locP (conjPrime₂ Q) L y).1 hy`. Rewrite `ht` using `[mem_conjP]`.

Establish `h1` using `(mem_dual L (s • x)).1 hsx (t • y) hty`. Rewrite `h1` using `[hStd_osmul_left, smul_smul, hStd_osmul_right]`. Use `(mem_locP Q _ _).2 ⟨cO E t * s, ?_, h1⟩` and prove the remaining obligations. Introduce `hm`. Break down `Q.isPrime.mem_or_mem hm with h | h` into its components or cases.

Conclude with `ht h`. Conclude with `hs h`. Introduce `H`. Take `⟨S, hS⟩` from `hL`. Establish `H' : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • hStd E n y x ∈ (1 : Submodule (𝓞 E) E)`.

Introduce `y hy`. Establish `hyL : y ∈ L` using `hS ▸ Submodule.subset_span hy`. Conclude with `(mem_locP Q _ _).1 (H y (Formalism.L2.DIV.lc_le_locP (conjPrime₂ Q) L hyL))`. Use `choose f hf hfx using H'`. Use `(mem_locP Q _ x).2 ⟨∏ y ∈ S.attach, f y.1 y.2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hm`. Take `⟨a, _, ha⟩` from `(Q.isPrime.prod_mem_iff).1 hm`. Conclude with `hf a.1 a.2 ha`. Rewrite using `[mem_dual]`. Introduce `y hy`.

Rewrite `hy` using `[← hS]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Rewrite using `[hStd_osmul_right, ← Finset.prod_erase_mul S.attach (fun a => f a.1 a.2) (Finset.mem_attach S ⟨z, hz⟩), mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hfx z hz)`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]`. Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha`. Rewrite using `[hStd_osmul_left, hStd_osmul_right]`.

Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem mem_localization_dual_iff (Q : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Sp E n)) (hL : L.FG) (x : Sp E n) :
    x ∈ localization₂ Q.asIdeal (dual (hStd E n) L) ↔
      ∀ y ∈ localization₂ (conjPrime₂ Q).asIdeal L, hStd E n y x ∈ localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP Q _ x).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP (conjPrime₂ Q) L y).1 hy
    rw [mem_conjP] at ht
    have h1 := (mem_dual L (s • x)).1 hsx (t • y) hty
    rw [hStd_osmul_left, smul_smul, hStd_osmul_right] at h1
    refine (mem_locP Q _ _).2 ⟨cO E t * s, ?_, h1⟩
    intro hm
    rcases Q.isPrime.mem_or_mem hm with h | h
    · exact ht h
    · exact hs h
  · intro H
    obtain ⟨S, hS⟩ := hL
    have H' : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
      intro y hy
      have hyL : y ∈ L := hS ▸ Submodule.subset_span hy
      exact (mem_locP Q _ _).1 (H y (Formalism.L2.DIV.lc_le_locP (conjPrime₂ Q) L hyL))
    choose f hf hfx using H'
    refine (mem_locP Q _ x).2 ⟨∏ y ∈ S.attach, f y.1 y.2, ?_, ?_⟩
    · intro hm
      obtain ⟨a, _, ha⟩ := (Q.isPrime.prod_mem_iff).1 hm
      exact hf a.1 a.2 ha
    · rw [mem_dual]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        rw [hStd_osmul_right, ← Finset.prod_erase_mul S.attach (fun a => f a.1 a.2) (Finset.mem_attach S ⟨z, hz⟩),
          mul_smul]
        exact Submodule.smul_mem _ _ (hfx z hz)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul r a _ ha =>
        rw [hStd_osmul_left, hStd_osmul_right]
        exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_localization_dual_iff Q A hA.fg, mem_localization_dual_iff Q B hB.fg, h]`.
-/
theorem use₅ (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n))
    (hA : Submodule.IsLattice E A) (hB : Submodule.IsLattice E B)
    (h : localization₂ (conjPrime₂ Q).asIdeal A = localization₂ (conjPrime₂ Q).asIdeal B) :
    localization₂ Q.asIdeal (dual (hStd E n) A) = localization₂ Q.asIdeal (dual (hStd E n) B) := by
  ext x
  rw [mem_localization_dual_iff Q A hA.fg, mem_localization_dual_iff Q B hB.fg, h]

end GlobalTheory.DualLoc
