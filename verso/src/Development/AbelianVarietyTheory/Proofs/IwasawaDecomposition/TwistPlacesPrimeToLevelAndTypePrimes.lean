import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabCardOfStabTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `hv`. Establish `key : ∀ p : ℕ, p.Prime → p ∈ I.S → ((p : ℕ) : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal`. Introduce `p hp hS hm`. Apply `GlobalTheory.KFormsCmp.notMem_of_QE hI.sel_ok (I.tup a) hP hp hS` to reduce the goal to its premises. Use `Ideal.mem_comap.1 hm` as an intermediate fact.

Simplify using `using this`. Conclude with `⟨key _ (l.pr.T_prime u) (hI.T_mem u), fun j => key _ (l.pr.g_prime j) (hI.g_mem j)⟩`.
-/
theorem underQ_notMem {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : I.UnderQ a v) :
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  obtain ⟨P, hP, rfl⟩ := hv
  have key : ∀ p : ℕ, p.Prime → p ∈ I.S → ((p : ℕ) : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
    intro p hp hS hm
    apply GlobalTheory.KFormsCmp.notMem_of_QE hI.sel_ok (I.tup a) hP hp hS
    have := Ideal.mem_comap.1 hm
    simpa using this
  exact ⟨key _ (l.pr.T_prime u) (hI.T_mem u), fun j => key _ (l.pr.g_prime j) (hI.g_mem j)⟩

/- English proof (translation)
Introduce `I hI l u a v hv` and use `underQ_notMem I hI l u a v hv`.
-/
theorem underQ_prime_to_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v →
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
  fun I hI l u a v hv => underQ_notMem I hI l u a v hv

end GlobalTheory.Mem.Col2.TC
