import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.DecoFin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in

/- English proof (translation)
Establish `h1 : P.asIdeal ∣ Ideal.span {q}` using `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)`. Take `⟨J, hJ⟩` from `h1`. Establish `h2 : ¬ J ≤ P.asIdeal`. Introduce `h`. Apply `hq2` to reduce the goal to its premises.

Establish `: q ∈ P.asIdeal * J` using `hJ ▸ Ideal.mem_span_singleton_self q`. Rewrite using `[sq]`. Conclude with `Ideal.mul_mono_right h this`. Take `⟨s, hs, hsP⟩` from `SetLike.not_le_iff_exists.1 h2`. Use `⟨s, hsP, fun r hr => ?_⟩` and prove the remaining obligations.

Establish `: r * s ∈ Ideal.span {q}` using `hJ ▸ Ideal.mul_mem_mul hr hs`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩`.
-/
theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

/- English proof (translation)
The claim follows from `LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x`.
-/
theorem ufGL_mulVec (γ : UF E n) (x : Sp E n) :
    Matrix.mulVec ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

/- English proof (translation)
The claim follows from `dif_pos ⟨p.1.1.2, p.2⟩`.
-/
theorem mv_dia {y : Ys X n} (p : PtY ST SG Q y) (c : DiaG X.E ST) :
    p.mv (DecoSet.dia c p.1.1.deco) =
      ⟨(⟨(DecoSet.dia c p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩

end GlobalTheory.Mem.Col2.LevLaws
