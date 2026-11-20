import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

noncomputable section

open NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.W2 (rts)

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `p _ D G L ha i₀ v hv hinv P hP`. Take `⟨i, rfl⟩` from `(L.sig v).1 hv`. Establish `hi : i = i₀`. Establish `: Subsingleton (Fin D.a)` using `by rw [ha]; infer_instance`. Conclude with `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Use `set φ : G.F →+* ℂ := G.iotaC.comp (L.s i) with hφ`. Establish `hφe : ∀ x : D.F, φ (L.e x) = D.tau i x` using `fun x => L.s_C i x`. Establish `hcomp : (D.tau i).comp (L.e.symm : G.F →+* D.F) = φ`. Use extensionality with `x`.

Rewrite using `[RingHom.comp_apply, ← hφe]`. Simplify using the standard rewrite rules. Establish `hP' : (map (L.e.symm : G.F →+* D.F) P).coeff 0 ≠ 0`. Rewrite using `[coeff_map]`. Simplify using `using hP`.

Establish `hR : rts (endPol L P) (D.tau i) = Multiset.map (fun z : ℂ => z⁻¹) (map φ P).roots` using `by show rts (invPol (map (L.e.symm : G.F →+* D.F) P)) (D.tau i) = _`. Rewrite using `[hinv D.F _ hP' (D.tau i)]`. Simplify using `only [rts, Polynomial.map_map, hcomp]`. Rewrite using `[hR]`. Establish `hω : φ (L.e D.ω) = D.ρc` using `by rw [hφe]; exact D.tau_ω i`.

Establish `hρ : (starRingEnd ℂ) D.ρc ≠ D.ρc`. Introduce `h`. Take `⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = D.ρc` from `⟨D.ρc.re, Complex.conj_eq_iff_re.mp h⟩`. Establish `h0` using `D.ρc_root`. Rewrite `h0` using `[← hr]`.

Establish `h1 : r ^ 2 - (D.tr : ℝ) * r + (D.nm : ℝ) = 0`. Use `congrArg Complex.re h0` as an intermediate fact. Simplify `this` using `[sq]`. Establish `h2 : ((D.tr : ℝ) ^ 2 - 4 * (D.nm : ℝ)) < 0` using `by exact_mod_cast D.disc_neg`. Use polynomial arithmetic with `[sq_nonneg (2 * r - (D.tr : ℝ))]`.

Break down `InfinitePlace.embedding_mk_eq φ with h | h` into its components or cases. Rewrite using `[h]`. Use `Multiset.map_congr rfl (fun μ _ => ?_)` and prove the remaining obligations. Simplify using `[markOf, h, hω]`. Rewrite using `[h]`.

Establish `hmap : map (ComplexEmbedding.conjugate φ) P = map (starRingEnd ℂ) (map φ P)`. Rewrite using `[Polynomial.map_map]`. Both sides reduce to the same expression. Rewrite using `[hmap, (IsAlgClosed.splits (map φ P)).roots_map, Multiset.map_map]`. Use `Multiset.map_congr rfl (fun μ _ => ?_)` and prove the remaining obligations.

Simplify using `[markOf, h, hω, hρ]`.
-/
theorem markRoots_of : MarkRoots := by
  intro p _ D G L ha i₀ v hv hinv P hP
  obtain ⟨i, rfl⟩ := (L.sig v).1 hv
  have hi : i = i₀ := by
    have : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hi
  set φ : G.F →+* ℂ := G.iotaC.comp (L.s i) with hφ
  have hφe : ∀ x : D.F, φ (L.e x) = D.tau i x := fun x => L.s_C i x
  have hcomp : (D.tau i).comp (L.e.symm : G.F →+* D.F) = φ := by
    ext x
    rw [RingHom.comp_apply, ← hφe]
    simp
  have hP' : (map (L.e.symm : G.F →+* D.F) P).coeff 0 ≠ 0 := by
    rw [coeff_map]
    simpa using hP
  have hR : rts (endPol L P) (D.tau i) = Multiset.map (fun z : ℂ => z⁻¹) (map φ P).roots := by
    show rts (invPol (map (L.e.symm : G.F →+* D.F) P)) (D.tau i) = _
    rw [hinv D.F _ hP' (D.tau i)]
    simp only [rts, Polynomial.map_map, hcomp]
  rw [hR]
  have hω : φ (L.e D.ω) = D.ρc := by rw [hφe]; exact D.tau_ω i
  have hρ : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
    intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = D.ρc := ⟨D.ρc.re, Complex.conj_eq_iff_re.mp h⟩
    have h0 := D.ρc_root
    rw [← hr] at h0
    have h1 : r ^ 2 - (D.tr : ℝ) * r + (D.nm : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa [sq] using this
    have h2 : ((D.tr : ℝ) ^ 2 - 4 * (D.nm : ℝ)) < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * r - (D.tr : ℝ))]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω]
  · rw [h]
    have hmap : map (ComplexEmbedding.conjugate φ) P = map (starRingEnd ℂ) (map φ P) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, (IsAlgClosed.splits (map φ P)).roots_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω, hρ]

end UpperTheory.Gal.LocalSmoothExtension
