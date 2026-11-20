import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanGlue
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

/- English proof (translation)
Introduce `f`. Establish `h0 : (f : Rul Xo c) ∈ cusp Xo c U a n` using `f.2`. Establish `h1` using `(Submodule.mem_inf.mp h0).2`. Rewrite `h1` using `[Submodule.mem_iInf]`. Establish `h2` using `h1 σ`.

Rewrite `h2` using `[Submodule.mem_iInf]`. Establish `hf : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n)` using `h2 hσ`. Set `K : Submodule ℂ (FDSec (U σ).X)` to `{ carrier := {P | IsHolCusp (U σ).X (laU (U σ) a n) P} zero_mem' := by`. Introduce `k`. Conclude with `((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).1`.

Use the proof step `add_mem' := by`. Introduce `P Q hP hQ k`. Conclude with `((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.1 _ (hP k) _ (hQ k)`. Use the proof step `smul_mem' := by`. Introduce `z P hP k`.

Conclude with `((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.2 z _ (hP k) }`. Establish `hle : holSub (U σ).X (laU (U σ) a n) ≤ K` using `Submodule.span_le.mpr (fun P hP => hP)`. Conclude with `hle hf`.
-/
theorem readings_holomorphic_cuspForms (hM5 : SiegelSpaceAlgebra (E := E)) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : RdHolCusp σ (laU (U σ) a n) (rdC U σ a n) := by
  intro f
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  have hf : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := h2 hσ
  let K : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | IsHolCusp (U σ).X (laU (U σ) a n) P}
      zero_mem' := by
        intro k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).1
      add_mem' := by
        intro P Q hP hQ k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.1 _ (hP k) _ (hQ k)
      smul_mem' := by
        intro z P hP k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.2 z _ (hP k) }
  have hle : holSub (U σ).X (laU (U σ) a n) ≤ K := Submodule.span_le.mpr (fun P hP => hP)
  exact hle hf

/- English proof (translation)
Establish `h0 : (f : Rul Xo c) ∈ cusp Xo c U a n` using `f.2`. Establish `h1` using `(Submodule.mem_inf.mp h0).2`. Rewrite `h1` using `[Submodule.mem_iInf]`. Establish `h2` using `h1 σ`. Rewrite `h2` using `[Submodule.mem_iInf]`.

Conclude with `h2 hσ`.
-/
theorem rdC_mem_holSub {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := by
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  exact h2 hσ

/- English proof (translation)
Use `Submodule.mem_inf.mpr ⟨rdC_mem_holSub hσ a n f, ?_⟩` and prove the remaining obligations. Introduce `k x hx`. Simplify using `[rdC, rdU, hx]`.
-/
theorem rdC_mem_holSub0 {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub0 (U σ).X (laU (U σ) a n) := by
  refine Submodule.mem_inf.mpr ⟨rdC_mem_holSub hσ a n f, ?_⟩
  intro k x hx
  simp [rdC, rdU, hx]

end Read

def JInjAt {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hd : Dom a n) : Prop :=
  JInj (T.V j T.σ₀) T.σ₀ (rdC (T.U j) T.σ₀ a n) (T.dict j T.σ₀) (T.mu j T.σ₀) (h.cuspidalL2Subspace j hj T.σ₀ T.good_σ₀ a n hd)

def JInjRd {D : D7} (T : Top D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  IndepToC (rdC (T.U j) T.σ₀ a n)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
