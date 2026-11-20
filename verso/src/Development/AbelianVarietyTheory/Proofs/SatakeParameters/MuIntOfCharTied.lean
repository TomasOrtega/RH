import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

/- English proof (translation)
Introduce `D C nch Tp hT i τ z hz`. Establish `hj` using `D.nd.j_range i`. Set `j : Fin D.R.m` to `⟨D.nd.j i - 1, by omega⟩`. Establish `hjj : j.1 + 1 = D.nd.j i` using `by simp only [j]; omega`. Establish `hmu` using `hT.muC i j hjj`.

Use `haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1`. Take `⟨n, hn, ho⟩` from `Tp.xi_fin (D.nd.mu i)`. Establish `hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g)` using `(C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)`. Rewrite `hinf` using `[← hmu]`. Establish `key` using `hT.infG _ _ hinf`.

Take `⟨ρ, hρ⟩` from `(GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)`. Take `⟨m, hm⟩` from `(D.hc (D.eTau.symm (D.eTau ρ))).e_int j`. Establish `hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m` using `hm`. Break down `InfinitePlace.mk_eq_iff.1 hρ with h | h` into its components or cases. Establish `ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ)` using `h.symm`.

Rewrite `hz` using `[ht, (key (D.eTau ρ)).1]`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz`. Rewrite using `[hz, hm']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ))`. Rewrite using `[← h]`. Use extensionality with `x`. Both sides reduce to the same expression.

Rewrite `hz` using `[ht, (key (D.eTau ρ)).2]`. Use `⟨m, ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz`. Rewrite using `[hz, hm']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Formalism.L2.Host.NCharTied D C nch Tp → MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
