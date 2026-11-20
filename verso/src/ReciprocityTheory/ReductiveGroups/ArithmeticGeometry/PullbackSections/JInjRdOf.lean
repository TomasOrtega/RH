import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

open Classical in

/- English proof (translation)
Use `show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _`. Rewrite using `[dif_pos x.2]`.
-/
theorem rdU_apply_dom {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
  show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _
  rw [dif_pos x.2]

/- English proof (translation)
Take `⟨k, x, t, hbor⟩` from `hU3 z`. Use `letI : Field (CAt σ) := inferInstanceAs (Field ℂ)`. Establish `hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x)` using `fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`.

Use `_ = 0 := by rw [hrel k x, mul_zero]`.
-/
theorem rel_of_frames {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hU3 : ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x))
    (hF : WtField Xo c) {m : ℕ} (fs : Fin m → Rul Xo c) (hfs : ∀ i, fs i ∈ sec Xo c a n) (g : Fin m → ℂ)
    (hrel : ∀ k (x : (U.X k).dom), ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) = 0)
    (z : FrPt Xo c (CAt σ)) (hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z) :
    ∑ i, g i * toC (evR Xo c (fs i) z) = 0 := by
  obtain ⟨k, x, t, hbor⟩ := hU3 z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x) :=
    fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor
  calc ∑ i, g i * toC (evR Xo c (fs i) z)
      = ∑ i, g i * (toC (wchar (ex Dw a n) t) * toC (evR Xo c (fs i) (U.un k x))) :=
        Finset.sum_congr rfl fun i _ => by rw [hv i]; rfl
    _ = toC (wchar (ex Dw a n) t) * ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hrel k x, mul_zero]

end Frames

/- English proof (translation)
Introduce `m b hb`. Establish `hU : IsUnf (T.U j T.σ₀)` using `hM.unf j hj T.σ₀ T.good_σ₀`. Establish `hb'` using `hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)`. Establish `hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n` using `fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Establish `hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom), ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i) ((T.U j T.σ₀).un k x)) = 0`. Introduce `k x`. Establish `h` using `congrFun (congrFun hg k) x.1`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h`.

Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[← rdU_apply_dom (T.U j T.σ₀) _ k x]`. Both sides reduce to the same expression. Establish `hall` using `rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel`.

Set `_ : Algebra T.Q.c.F ℂ` to `T.σ₀.toAlgebra`. Establish `hc` using `indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ) _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)`. Introduce `i`. Conclude with `congrFun hc i`.
-/
theorem jInjRd_of_wt {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hF : WtField (T.Q.Xo j) T.Q.c) :
    JInjRd T j a n := by
  intro m b hb
  have hU : IsUnf (T.U j T.σ₀) := hM.unf j hj T.σ₀ T.good_σ₀
  have hb' := hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i)
        ((T.U j T.σ₀).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← rdU_apply_dom (T.U j T.σ₀) _ k x]; rfl
  have hall := rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := T.σ₀.toAlgebra
  have hc := indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

/- English proof (translation)
The claim follows from `jInjRd_of_wt T hM hj a n hA (wtField_of hD)`.
-/
theorem jInjRd_of_bcex {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hD : BorDesc (T.Q.Xo j) T.Q.c) : JInjRd T j a n :=
  jInjRd_of_wt T hM hj a n hA (wtField_of hD)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
