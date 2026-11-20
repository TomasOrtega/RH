import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord

noncomputable section

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

/- English proof (translation)
Introduce `i hi`. Take `⟨h1, h2⟩` from `Formalism.FourierDecayAlt.P.Topx1.vecw_rho_bounds h ρ hi`. Unfold `M.Par.lo at h1`. Unfold `M.Par.hi at h2`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the linear relations using `[min_le_left (P.u i) (P.u' i)]`. Combine the linear relations using `[min_le_right (P.u i) (P.u' i)]`. Combine the linear relations using `[le_max_left (P.u (i + 1)) (P.u' (i + 1))]`. Combine the linear relations using `[le_max_right (P.u (i + 1)) (P.u' (i + 1))]`.
-/
theorem interlaces_rho {P : M.Par} (h : P.OK) (ρ : M.Ty P) : I.Interlaces P.k P.u P.u' (M.rho P ρ) := by
  intro i hi
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_rho_bounds h ρ hi
  unfold M.Par.lo at h1
  unfold M.Par.hi at h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [min_le_left (P.u i) (P.u' i)]
  · linarith [min_le_right (P.u i) (P.u' i)]
  · linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1))]
  · linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]

/- English proof (translation)
Simplify using `[M.xC, I.xpoly]`.
-/
theorem xC_ofReal (P : M.Par) (ρ : M.Ty P) (y : ℝ) :
    M.xC P ρ (y : ℂ) = ((I.xpoly P.k (M.rho P ρ) y : ℝ) : ℂ) := by
  simp [M.xC, I.xpoly]

/- English proof (translation)
Simplify using `[M.qC, I.qpoly]`.
-/
theorem qC_ofReal (P : M.Par) (y : ℝ) : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]

def AdmOfCutRange : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : Q.ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π')))
    (l0 : ℕ) (w : List C.Letter), 1 ≤ l0 → l0 ≤ P.k →
    P5.IsData P z z' π π' X μ L st l0 → KB.CutWord P l0 w → Fr.admitted st (D.positionted w)

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 w hl1 hl2 hD hcut`. Take `⟨hPl, -, -, -, hq, hinv, -, -⟩` from `hD`. Establish `hOK : P.OK` using `hPl.1`. Set `ρ0 : M.Ty P` to `fun _ => 0`. Establish `hint0` using `PBI.interlaces_rho hOK ρ0`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [D.positionted, List.map_ofFn]`. Conclude with `List.nodup_ofFn.2 (fun a b h => h)`. Introduce `l hl`. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hl`.

Simplify using `[Complex.conj_ofReal]`. Introduce `l hl`. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hl`. Use `set y := (w.get a).2 with hy`. Establish `hca : I.OnCut P.u P.u' l0 y` using `hcut.1 a`.

Establish `hx : ∀ ρ : M.Ty P, ∀ e ∈ ({-1, 0, 1} : Finset ℝ), I.xpoly P.k (M.rho P ρ) (y + e) ≠ 0`. Introduce `ρ e he h0`. Use `Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P ρ) l0 y hl1 hl2 (PBI.interlaces_rho hOK ρ) hca e he` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `lt_irrefl _ this`.

Rewrite using `[hinv, hq]`. Simplify using `only [Set.mem_setOf_eq]`. Use `⟨fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PBI.xC_ofReal]`. Use `hx ρ 0 (by simp)` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `this` after adjusting the coercions. Establish `e : ((y : ℝ) : ℂ) + 1 = ((y + 1 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, PBI.xC_ofReal]`. Conclude with `hx ρ 1 (by simp)` after adjusting the coercions.

Establish `e : ((y : ℝ) : ℂ) - 1 = ((y + -1 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, PBI.xC_ofReal]`. Conclude with `hx ρ (-1) (by simp)` after adjusting the coercions. Rewrite using `[PBI.qC_ofReal]`. Use `Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca hOK.T_pos hOK.T'_pos` as an intermediate fact.

Conclude with `this.ne'` after adjusting the coercions. Establish `e : ((y : ℝ) : ℂ) - 1 = ((y - 1 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, PBI.qC_ofReal]`. Use `Formalism.FourierDecayAlt.P.q_positive_shift P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca hOK.T_pos hOK.T'_pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions.

Simplify using `only [D.positionted]`. Rewrite using `[List.pairwise_ofFn]`. Introduce `i j hij n hn h`. Establish `hne : i ≠ j` using `ne_of_lt hij`. Establish `hd` using `hcut.2 i j hne`.

Establish `h' : (w.get i).2 - (w.get j).2 = (n : ℝ)`. Establish `h2` using `h`. Simplify using `only at h2`. Conclude with `h2` after adjusting the coercions. Rewrite `hd` using `[h']`.

Establish `: |((n : ℤ) : ℝ)| ≤ 2` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem admissible_of_range : PBI.AdmOfCutRange := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 w hl1 hl2 hD hcut
  obtain ⟨hPl, -, -, -, hq, hinv, -, -⟩ := hD
  have hOK : P.OK := hPl.1
  let ρ0 : M.Ty P := fun _ => 0
  have hint0 := PBI.interlaces_rho hOK ρ0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [D.positionted, List.map_ofFn]
    exact List.nodup_ofFn.2 (fun a b h => h)
  · intro l hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    simp [Complex.conj_ofReal]
  · intro l hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    set y := (w.get a).2 with hy
    have hca : I.OnCut P.u P.u' l0 y := hcut.1 a
    have hx : ∀ ρ : M.Ty P, ∀ e ∈ ({-1, 0, 1} : Finset ℝ), I.xpoly P.k (M.rho P ρ) (y + e) ≠ 0 := by
      intro ρ e he h0
      have := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P ρ) l0 y hl1 hl2 (PBI.interlaces_rho hOK ρ) hca e he
      rw [h0, mul_zero] at this
      exact lt_irrefl _ this
    rw [hinv, hq]
    simp only [Set.mem_setOf_eq]
    refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, ?_, ?_⟩
    · rw [PBI.xC_ofReal]
      have := hx ρ 0 (by simp)
      rw [add_zero] at this
      exact_mod_cast this
    · have e : ((y : ℝ) : ℂ) + 1 = ((y + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.xC_ofReal]
      exact_mod_cast hx ρ 1 (by simp)
    · have e : ((y : ℝ) : ℂ) - 1 = ((y + -1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.xC_ofReal]
      exact_mod_cast hx ρ (-1) (by simp)
    · rw [PBI.qC_ofReal]
      have := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca hOK.T_pos hOK.T'_pos
      exact_mod_cast this.ne'
    · have e : ((y : ℝ) : ℂ) - 1 = ((y - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, PBI.qC_ofReal]
      have := Formalism.FourierDecayAlt.P.q_positive_shift P.k P.u P.u' (M.rho P ρ0) l0 y P.T P.T' hl1 hl2 hint0 hca
        hOK.T_pos hOK.T'_pos
      exact_mod_cast this.ne'
  · simp only [D.positionted]
    rw [List.pairwise_ofFn]
    intro i j hij n hn h
    have hne : i ≠ j := ne_of_lt hij
    have hd := hcut.2 i j hne
    have h' : (w.get i).2 - (w.get j).2 = (n : ℝ) := by
      have h2 := h
      simp only at h2
      exact_mod_cast h2
    rw [h'] at hd
    have : |((n : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast hn
    linarith

end Formalism.FourierDecayAlt.P
