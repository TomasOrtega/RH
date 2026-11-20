import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.SplitElementExistsHolds

noncomputable section

namespace GlobalTheory.EqOffSplitOfSplit

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

/- English proof (translation)
Take `⟨a, b, hab, ha, hb⟩` from `hP`. Establish `hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a` using `Subtype.ext (hab.trans rfl)`. Use `⟨b, a, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hab]`. Conclude with `(Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm`.

Rewrite using `[hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]`. Conclude with `ha`. Rewrite using `[hQ, ← hb']`. Conclude with `hb`.
-/
theorem isSplit_conj (D : D7) {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : GL3Theta.SplitP D P)
    (hQ : ∀ x : 𝓞 D.host.E, x ∈ Q.asIdeal ↔ Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ P.asIdeal) : GL3Theta.SplitP D Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := hP
  have hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a := Subtype.ext (hab.trans rfl)
  refine ⟨b, a, ?_, ?_, ?_⟩
  · rw [hab]; exact (Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm
  · rw [hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]; exact ha
  · rw [hQ, ← hb']; exact hb

/- English proof (translation)
Introduce `D P n L L₀ hP hoff`. Take `⟨m, hm⟩` from `hoff`. Take `⟨x, hx0, hxP, hxM⟩` from `Formalism.L2.PairingIndexBounds.Rec.genPow D P`. Establish `hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0` using `fun y hy h => hy (by`. Rewrite using `[← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])`.

Establish `hg0 : x ^ m ≠ 0` using `pow_ne_zero m hx0`. Take `⟨h1, h2⟩` from `hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)`. Use `⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩` and prove the remaining obligations. Break down `Q.isPrime.mem_or_mem hQ with h | h` into its components or cases. Establish `e : P.asIdeal = Q.asIdeal` using `hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)`.

Establish `e' : P = Q` using `HeightOneSpectrum.ext e`. Conclude with `e' ▸ hP`. Rewrite `h` using `[map_pow]`. Establish `h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal` using `Q.isPrime.mem_of_pow_mem m h`. Establish `e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal` using `hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)`.

Use `isSplit_conj D hP fun y => ?_` and prove the remaining obligations. Rewrite using `[e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]`.
-/
theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ)
    (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  intro D P n L L₀ hP hoff
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨x, hx0, hxP, hxM⟩ := Formalism.L2.PairingIndexBounds.Rec.genPow D P
  have hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0 := fun y hy h => hy (by
    rw [← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])
  have hg0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  obtain ⟨h1, h2⟩ := hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)
  refine ⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have e : P.asIdeal = Q.asIdeal := hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)
    have e' : P = Q := HeightOneSpectrum.ext e
    exact e' ▸ hP
  · rw [map_pow] at h
    have h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal := Q.isPrime.mem_of_pow_mem m h
    have e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal :=
      hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)
    refine isSplit_conj D hP fun y => ?_
    rw [e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]

end GlobalTheory.EqOffSplitOfSplit
