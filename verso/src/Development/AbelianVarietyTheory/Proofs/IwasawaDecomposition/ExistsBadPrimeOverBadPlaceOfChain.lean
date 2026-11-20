import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
