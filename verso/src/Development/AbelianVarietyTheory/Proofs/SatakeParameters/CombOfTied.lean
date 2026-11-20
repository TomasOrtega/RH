import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap

noncomputable section

namespace GlobalTheory.Ggeo.KerComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

/- English proof (translation)
Introduce `hAlg D L hT Gi Gl K Y cX ex t hH u μ w hw i hi c c'`. Establish `hEven : ∀ j, Even (D.R.N j)` using `fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)`. Establish `hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1` using `⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩`. Use `⟨hAdm, ?_⟩` and prove the remaining obligations. Establish `hTA : TransAlg D t.B.tor (t.B.eNat t.χ)` using `transcendence_algebraic_eigen D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok (KS.Lat.delta_ne t.cc_ok t.δ_ok) (t.B.stdOK t.cc_ok t.δ_ok) (hAlg D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok)`.

Establish `hS : D.what₂.places.resChar w ∉ (t.O u μ).S`. Take `⟨h1, h2, h3⟩` from `hw`. Rewrite using `[t.O_S u μ]`. Introduce `hm`. Simplify using `only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, not_or] at h2 hm`.

Break down `hm with h | (h | h) | h` into its components or cases. Use `exacts [h1 h, h2.1 h, h2.2 h, h3 h]`. Establish `hA'` using `hAdm`. Rewrite `hA'`, the goal using `[t.O_lat u μ i c, t.O_lat u μ (i + 1) c']`. Rewrite using `[t.O_Th u μ i c c']`.

Conclude with `first_kernel_law_reading D t.X u (D.chTw u μ) (t.rd u μ) t.seam t.amb t.cc t.δ (t.B.eNat t.χ) (t.O u μ).S i (hH u μ i hi) hTA c c' hA' _ (t.ent.lam w) hS`.
-/
theorem comb_of_tied : Formalism.L2.KerInert.AlgTAll → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → ∀ u μ w, LevFree Y u μ w → ∀ i < D.R.m, ∀ c c', TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 ∧ TaylorLogMetric.IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 (TaylorLogMetric.pSer D (t.ent.lam w) ((t.O u μ).Th i c c')) := by
  intro hAlg D L hT Gi Gl K Y cX ex t hH u μ w hw i hi c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  refine ⟨hAdm, ?_⟩
  have hTA : TransAlg D t.B.tor (t.B.eNat t.χ) :=
    transcendence_algebraic_eigen D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok (KS.Lat.delta_ne t.cc_ok t.δ_ok) (t.B.stdOK t.cc_ok t.δ_ok)
      (hAlg D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok)
  have hS : D.what₂.places.resChar w ∉ (t.O u μ).S := by
    obtain ⟨h1, h2, h3⟩ := hw
    rw [t.O_S u μ]
    intro hm
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, not_or] at h2 hm
    rcases hm with h | (h | h) | h
    exacts [h1 h, h2.1 h, h2.2 h, h3 h]
  have hA' := hAdm
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hA' ⊢
  rw [t.O_Th u μ i c c']
  exact first_kernel_law_reading D t.X u (D.chTw u μ) (t.rd u μ) t.seam t.amb t.cc t.δ (t.B.eNat t.χ) (t.O u μ).S i (hH u μ i hi) hTA c c' hA' _ (t.ent.lam w) hS

end GlobalTheory.Ggeo.KerComb
