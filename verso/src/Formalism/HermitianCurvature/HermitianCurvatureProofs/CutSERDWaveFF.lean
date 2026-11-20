import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section WaveFF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩`.
-/
theorem rdb_one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩`.
-/
theorem rdb_n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, hh, 1, (nSubgroup k r).1, by simp⟩`.
-/
theorem rdb_h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

/- English proof (translation)
Establish `e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g => Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g)`. Use function extensionality and compare the values at `fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1`. Rewrite using `[e]`. Conclude with `Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)`.
-/
theorem rdb_fsv_dmin_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (h1 : 1 < r + 2) :
    ContDiff ℝ ∞ (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) := by
  have e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g =>
      Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) :=
    funext fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1
  rw [e]
  exact Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)

/- English proof (translation)
Establish `h1 : 1 < r + 2` using `by omega`. Establish `inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r, Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩` using `fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _`. Take `⟨hS, hL, hR, hU⟩` from `hJ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`.

Take `⟨U, F, hU, hgU, hF, hFJ⟩` from `hS g₀ hg₀`. Use `⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU, (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩` and prove the remaining obligations. Use `show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _`. Rewrite using `[hFJ g hgU hgG]`. Introduce `g hg n hn`.

Establish `e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩`. Use `inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g` as an intermediate fact. Simplify using `using this`. Use `show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)`. Rewrite using `[e, hL g hg n hn, smul_comm]`.

Introduce `g hg n hn`. Establish `e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩`. Use `inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g` as an intermediate fact. Simplify using `using this`. Use `show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)`.

Rewrite using `[e, hR g hg n hn, smul_comm]`. Introduce `g hg h hh h' hh' show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') = (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))`. Rewrite using `[inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]`.
-/
theorem rdb_wvG_mem_FFl {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (s : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' 0 Dm) : wvG z z' s J ∈ FFl k r z z' π π' 0 Dm := by
  have h1 : 1 < r + 2 := by omega
  have inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r,
      Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ :=
    fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU,
      (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩
    show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _
    rw [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g
      simpa using this
    show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hL g hg n hn, smul_comm]
  · intro g hg n hn
    have e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g
      simpa using this
    show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') =
      (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))
    rw [inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end WaveFF

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ`. Establish `hz : inWb P.k P.r z` using `hD.1.2.1`. Establish `hz' : inWb P.k P.r z'` using `hD.1.2.2.1`. Establish `h1 : 1 < P.r + 2` using `by omega`. Use `⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩` and prove the remaining obligations.

Simplify using `only [resG, wvG]`. Rewrite using `[Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]`. Conclude with `smul_comm _ _ _`.
-/
theorem radial_wave_function_field : RDWaveFF := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  have h1 : 1 < P.r + 2 := by omega
  refine ⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩
  simp only [resG, wvG]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
