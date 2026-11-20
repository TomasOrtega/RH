import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LshOffLevel

/- English proof (translation)
Unfold `divs at h`. Use `split_ifs at h with hf`. Conclude with `(hf.mem_toFinset.1 h)`. Simplify using `at h`.
-/
theorem mem_divs_of' {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

/- English proof (translation)
Introduce `B X I hOk hPins l Z Y u μ w hw j hj c`. Establish `hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime` using `(I.rec7 l Z).what₂.places.resChar_prime w`. Establish `hTP : (B.T u).Prime` using `l.pr.T_prime u`. Establish `hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u` using `fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)`. Use `set d := ((I.stp u μ j).rep c).1.1.deco with hd`.

Establish `hE : (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c) = d.1.Lsh` using `rfl`. Rewrite using `[hE]`. Establish `hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal`. Introduce `P`. Establish `hpi` using `mem_divs_of' P.2`.

Rewrite using `[← l.pr.piT_norm u]`. Conclude with `Ideal.mul_mem_right _ _ hpi`. Establish `hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N`. Introduce `x hx`. Use `d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx` as an intermediate fact.

Rewrite `this` using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E]`. Then use the resulting hypothesis. Use `⟨d.2.Lsh_lattice, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨s, hs, hx⟩`. Use `⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩` and prove the remaining obligations. Establish `h3` using `hLN _ hx`.

Establish `e : ((B.T u * s : ℕ) : B.fields.E) • x = ((B.T u : ℕ) : B.fields.E) • ((s : B.fields.E) • x)`. Rewrite using `[smul_smul, ← Nat.cast_mul]`. Conclude with `e ▸ h3`. Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `⟨s, hs, d.2.N_le_Lsh hx⟩`.
-/
theorem lsh_lattice_and_loc_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  intro B X I hOk hPins l Z Y u μ w hw j hj c
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  set d := ((I.stp u μ j).rep c).1.1.deco with hd
  have hE : (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c) = d.1.Lsh := rfl
  rw [hE]
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of' P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  refine ⟨d.2.Lsh_lattice, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : B.fields.E) • x = ((B.T u : ℕ) : B.fields.E) • ((s : B.fields.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.LshOffLevel
