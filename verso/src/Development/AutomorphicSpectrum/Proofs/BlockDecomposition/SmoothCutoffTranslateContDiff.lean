import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

/- English proof (translation)
Unfold `lastEnt`. Use `ContDiff.sum fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (c : ℕ) + 1 = k`. Simplify using `only [if_pos h]`. Conclude with `contDiff_apply ℝ (Cinf E) c`.

Simplify using `only [if_neg h]`. Conclude with `contDiff_const`.
-/
theorem contDiff_lastEnt : ContDiff ℝ ∞ (lastEnt : (Fin k → Cinf E) → Cinf E) := by
  unfold lastEnt
  refine ContDiff.sum fun c _ => ?_
  by_cases h : (c : ℕ) + 1 = k
  · simp only [if_pos h]
    exact contDiff_apply ℝ (Cinf E) c
  · simp only [if_neg h]
    exact contDiff_const

/- English proof (translation)
The claim follows from `(Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous`.
-/
theorem isOpen_lastEnt_unit : IsOpen {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
  (Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous

/- English proof (translation)
Introduce `x hx`. Take `⟨u, hu⟩` from `hx`. Establish `h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x)`. Rewrite using `[← hu]`. Conclude with `contDiffAt_ringInverse ℝ u`.

Conclude with `(h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt`.
-/
theorem contDiffOn_inverse_lastEnt :
    ContDiffOn ℝ ∞ (fun x : Fin k → Cinf E => Ring.inverse (lastEnt x))
      {x | IsUnit (lastEnt x)} := by
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact (h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt

def tauM (x : Fin k → Cinf E) : LieI (InfinitePlace E) k := Matrix.of.symm (rowM (rowI x))

/- English proof (translation)
Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_` and prove the remaining obligations. Establish `hinv` using `contDiffOn_inverse_lastEnt (E := E) (k := k)`. Distinguish the cases in `hi : (i : ℕ) + 1 = k`. Establish `e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c` using `fun x => rowM_apply_last _ i c hi`. Simplify using `only [e]`.

Distinguish the cases in `hc : (c : ℕ) + 1 = k`. Simplify using `only [rowI, if_pos hc]`. Conclude with `hinv`. Simplify using `only [rowI, if_neg hc]`. Conclude with `((contDiff_apply ℝ (Cinf E) c).contDiffOn.mul hinv).neg`.

Establish `e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c` using `fun x => rowM_apply_ne _ i c hi`. Simplify using `only [e]`. Conclude with `contDiffOn_const`.
-/
theorem contDiffOn_tauM :
    ContDiffOn ℝ ∞ (tauM : (Fin k → Cinf E) → LieI (InfinitePlace E) k)
      {x | IsUnit (lastEnt x)} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_
  have hinv := contDiffOn_inverse_lastEnt (E := E) (k := k)
  by_cases hi : (i : ℕ) + 1 = k
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c := fun x => rowM_apply_last _ i c hi
    simp only [e]
    by_cases hc : (c : ℕ) + 1 = k
    · simp only [rowI, if_pos hc]
      exact hinv
    · simp only [rowI, if_neg hc]
      exact ((contDiff_apply ℝ (Cinf E) c).contDiffOn.mul hinv).neg
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c :=
      fun x => rowM_apply_ne _ i c hi
    simp only [e]
    exact contDiffOn_const

/- English proof (translation)
Establish `e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E))` using `(rowGL_inv_val h).symm`. Rewrite using `[e]`. Conclude with `Units.isUnit _`.
-/
theorem tauM_isUnit {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    IsUnit (Matrix.of (tauM x)) := by
  have e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E)) :=
    (rowGL_inv_val h).symm
  rw [e]
  exact Units.isUnit _

/- English proof (translation)
Establish `hu` using `tauM_isUnit h`. Establish `e : hu.unit = (rowGL x)⁻¹` using `Units.ext (by`. Rewrite using `[IsUnit.unit_spec]`. Conclude with `(rowGL_inv_val h).symm)`. Rewrite using `[orb, dif_pos hu, e]`.

Express the relevant statement in the definitionally equal form `_ = Rt E k (infGL E k (rowGL x)⁻¹) φ`. Rewrite using `[map_inv (infGL E k)]`.
-/
theorem rt_inv_eq_orb (φ : XB E k) {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    Rt E k (infGL E k (rowGL x))⁻¹ φ = orb (repI E k) φ (tauM x) := by
  have hu := tauM_isUnit h
  have e : hu.unit = (rowGL x)⁻¹ := Units.ext (by
    rw [IsUnit.unit_spec]; exact (rowGL_inv_val h).symm)
  rw [orb, dif_pos hu, e]
  change _ = Rt E k (infGL E k (rowGL x)⁻¹) φ
  rw [map_inv (infGL E k)]

/- English proof (translation)
Establish `hO` using `isOpen_lastEnt_unit (E := E) (k := k)`. Establish `hbc : ContDiff ℝ ∞ fun x => (b x : ℂ)` using `Complex.ofRealCLM.contDiff.comp hb`. Establish `horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)}` using `ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx`. Establish `hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) {x : Fin k → Cinf E | IsUnit (lastEnt x)}` using `(hbc.contDiffOn.smul horb).congr fun x hx => by`. Rewrite using `[rt_inv_eq_orb φ hx]`.

Both sides reduce to the same expression. Use `contDiff_iff_contDiffAt.2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ tsupport b`. Conclude with `hF.contDiffAt (hO.mem_nhds (hs x hx))`. Establish `e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0` using `by filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy`.

Simplify using `[hy]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq e`.
-/
theorem contDiff_cut_orbit {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hs : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) :
    ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  have hO := isOpen_lastEnt_unit (E := E) (k := k)
  have hbc : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx
  have hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ)
      {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    (hbc.contDiffOn.smul horb).congr fun x hx => by
      rw [rt_inv_eq_orb φ hx]
      rfl
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport b
  · exact hF.contDiffAt (hO.mem_nhds (hs x hx))
  · have e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq e

end GlobalTheory.CompanionTheory.CutOff

end
