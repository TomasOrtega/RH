import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.DSSmLin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Simplify using `only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem_UJset {n : ℕ} (ε : Fin n → Bool) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

/- English proof (translation)
The claim follows from `Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t`.
-/
theorem ex_mem_UJset {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    ex X t ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

/- English proof (translation)
Unfold `inG at *`. Rewrite using `[Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]`.
-/
theorem inG_add {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

/- English proof (translation)
Unfold `inG at *`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]`.
-/
theorem inG_smul {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    inG ε ((s : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
    ← smul_add, hX, smul_zero]

/- English proof (translation)
Introduce `n ε H _ _ σ hσ`. Take `⟨⟨h1, hm⟩, -, -⟩` from `hσ`. Establish `h : RepOn (UJset ε) σ` using `⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩`. Use `⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_, fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩` and prove the remaining obligations. Conclude with `IsSm.add (G := UJset ε) hv hw`.

Conclude with `IsSm.smul (G := UJset ε) hv c`. Conclude with `IsSm.apply h hv hg`. Establish `hv' : IsSm (UJset ε) σ v` using `hv`. Use `⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩` and prove the remaining obligations. Rewrite using `[List.mem_singleton.1 hY]`.

Conclude with `ex_mem_UJset hX t`. Establish `hv' : IsSm (UJset ε) σ v` using `hv`. Take `⟨U, F, hU, h1U, hF, hfF⟩` from `hv' 1 h.one_mem`. Establish `key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z` using `fun Z hZ => by`. Establish `hd : HasDerivAt (fun t => ex Z t) Z 0` using `by simpa using hasDerivAt_mul_ex 1 Z`.

Conclude with `(hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv`. Use `⟨?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[key _ (inG_add hX hY), key _ hX, key _ hY, map_add]`. Rewrite using `[key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]`.
-/
theorem smLin : CompanionTheory.D.DSIC.SmLin := by
  intro n ε H _ _ σ hσ
  obtain ⟨⟨h1, hm⟩, -, -⟩ := hσ
  have h : RepOn (UJset ε) σ := ⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩
  refine ⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_,
    fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩
  · exact IsSm.add (G := UJset ε) hv hw
  · exact IsSm.smul (G := UJset ε) hv c
  · exact IsSm.apply h hv hg
  · have hv' : IsSm (UJset ε) σ v := hv
    refine ⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩
    rw [List.mem_singleton.1 hY]
    exact ex_mem_UJset hX t
  · have hv' : IsSm (UJset ε) σ v := hv
    obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv' 1 h.one_mem
    have key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z := fun Z hZ => by
      have hd : HasDerivAt (fun t => ex Z t) Z 0 := by simpa using hasDerivAt_mul_ex 1 Z
      exact (hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv
    refine ⟨?_, fun s => ?_⟩
    · rw [key _ (inG_add hX hY), key _ hX, key _ hY, map_add]
    · rw [key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]

end GlobalTheory.CompanionTheory.DSSmLin
