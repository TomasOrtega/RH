import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar

/- English proof (translation)
Establish `hd : ∀ v s, HasDerivAt (fun t : ℝ => U t (ι v)) (U s (ι (a v))) s`. Introduce `v s`. Establish `h1 : HasDerivAt (fun t : ℝ => U (t - s) (ι v)) (ι (a v)) s`. Use `(show HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) (s - s) by` as an intermediate fact. Rewrite using `[sub_self]`.

Conclude with `hder v)`. Conclude with `this.comp_sub_const s s`. Establish `h2` using `((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1`. Establish `h3 : (fun t : ℝ => U t (ι v)) = ((U s).restrictScalars ℝ) ∘ fun t : ℝ => U (t - s) (ι v)`. Use extensionality with `r`.

Use `hadd s (r - s)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Simplify using `[this]`. Rewrite using `[h3]`. Conclude with `h2`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Rewrite using `[← (W.map ι).orthogonal_orthogonal, Submodule.mem_orthogonal]`. Introduce `y hy`. Set `b` to `Module.finBasis ℂ W`. Set `f : ℝ → Fin (Module.finrank ℂ W) → ℂ` to `fun s i => inner ℂ y (U s (ι (b i)))`.

Establish `hf : ∀ s (u : W), inner ℂ y (U s (ι u)) = ∑ j, b.repr u j * f s j`. Introduce `s u`. Establish `h3 : (u : V) = ∑ j, b.repr u j • (b j : V)`. Use `congrArg W.subtype (b.sum_repr u)` as an intermediate fact. Rewrite `this` using `[map_sum]`.

Conclude with `this.symm`. Rewrite using `[h3]`. Simplify using `only [f, map_sum, map_smul, inner_sum, inner_smul_right]`. Set `M : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ` to `fun i j => b.repr ⟨a (b i), hW _ (b i).2⟩ j`. Set `L` to `LinearMap.toContinuousLinearMap (Matrix.toLin' M)`.

Establish `hfd : ∀ s, HasDerivAt f (L (f s)) s`. Introduce `s`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Establish `h2` using `((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd (b i) s)`.

Use `hf s ⟨a (b i), hW _ (b i).2⟩` as an intermediate fact. Establish `h4 : L (f s) i = ∑ j, b.repr ⟨a (b i), hW _ (b i).2⟩ j * f s j`. Simplify using `only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]`. Both sides reduce to the same expression. Rewrite using `[h4, ← this]`.

Conclude with `h2`. Establish `hf0 : f 0 = 0`. Use extensionality with `i`. Simplify using `only [f, h0]`. Conclude with `Submodule.inner_left_of_mem_orthogonal (K := W.map ι) ⟨b i, (b i).2, rfl⟩ hy`.

Establish `hz : f = fun _ => 0`. Use `ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0) (fun _ => L.lipschitz.lipschitzOnWith) (fun s => ⟨hfd s, trivial⟩) (fun s => ⟨?_, trivial⟩) hf0` and prove the remaining obligations. Simplify using `using hasDerivAt_const s (0 : Fin (Module.finrank ℂ W) → ℂ)`. Rewrite using `[hf t ⟨w, hw⟩, hz]`. Simplify using the standard rewrite rules.
-/
theorem flow_mem_map {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : V →ₗ[ℂ] H) (a : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, a w ∈ W)
    (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0) (t : ℝ) :
    ∀ x ∈ W.map ι, U t x ∈ W.map ι := by
  classical
  have hd : ∀ v s, HasDerivAt (fun t : ℝ => U t (ι v)) (U s (ι (a v))) s := by
    intro v s
    have h1 : HasDerivAt (fun t : ℝ => U (t - s) (ι v)) (ι (a v)) s := by
      have := (show HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) (s - s) by
        rw [sub_self]; exact hder v)
      exact this.comp_sub_const s s
    have h2 := ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : (fun t : ℝ => U t (ι v)) = ((U s).restrictScalars ℝ) ∘ fun t : ℝ => U (t - s) (ι v) := by
      ext r
      have := hadd s (r - s)
      rw [add_sub_cancel] at this
      simp [this]
    rw [h3]
    exact h2
  rintro _ ⟨w, hw, rfl⟩
  rw [← (W.map ι).orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro y hy
  let b := Module.finBasis ℂ W
  let f : ℝ → Fin (Module.finrank ℂ W) → ℂ := fun s i => inner ℂ y (U s (ι (b i)))
  have hf : ∀ s (u : W), inner ℂ y (U s (ι u)) = ∑ j, b.repr u j * f s j := by
    intro s u
    have h3 : (u : V) = ∑ j, b.repr u j • (b j : V) := by
      have := congrArg W.subtype (b.sum_repr u)
      rw [map_sum] at this
      exact this.symm
    rw [h3]
    simp only [f, map_sum, map_smul, inner_sum, inner_smul_right]
  let M : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun i j => b.repr ⟨a (b i), hW _ (b i).2⟩ j
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hfd : ∀ s, HasDerivAt f (L (f s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h2 := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd (b i) s)
    have := hf s ⟨a (b i), hW _ (b i).2⟩
    have h4 : L (f s) i = ∑ j, b.repr ⟨a (b i), hW _ (b i).2⟩ j * f s j := by
      simp only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
      rfl
    rw [h4, ← this]
    exact h2
  have hf0 : f 0 = 0 := by
    ext i
    simp only [f, h0]
    exact Submodule.inner_left_of_mem_orthogonal (K := W.map ι) ⟨b i, (b i).2, rfl⟩ hy
  have hz : f = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun s => ⟨hfd s, trivial⟩) (fun s => ⟨?_, trivial⟩) hf0
    simpa using hasDerivAt_const s (0 : Fin (Module.finrank ℂ W) → ℂ)
  rw [hf t ⟨w, hw⟩, hz]
  simp

/- English proof (translation)
Introduce `p q n e ε T R σ hb hF W hfin hK k hk`. Take `⟨Y, hY, hexp, -⟩` from `Formalism.REAL.compact_exists_log_bounded ε k hk`. Take `⟨X, rfl⟩` from `(Matrix.reindex e e).surjective Y`. Establish `hX : X ∈ upq p q`. Establish `h1` using `hY.1`.

Unfold `Formalism.REAL.inG at h1`. Rewrite `h1` using `[← hb.reindex_Jm, Matrix.conjTranspose_reindex]`. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1`. Simplify using `only [Matrix.reindex_apply]`.

Rewrite using `[Matrix.submatrix_add]`. Conclude with `h1`. Establish `hKC : IsKC X`. Introduce `a b hab`. Rewrite `hab` using `[hb.sameBlock_iff]`.

Establish `h2` using `congrFun (congrFun hY.2 (e a)) (e b)`. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at h2`. Apply the tactic sequence `cases h3 : ε (e a) <;> cases h4 : ε (e b) <;> rw [h3, h4] at hab h2`. Conclude with `(hab rfl).elim`. Simplify using `only [if_true, Bool.false_eq_true, if_false] at h2`.

Take the linear combination `(1/2 : ℂ) * h2`. Simplify using `only [if_true, Bool.false_eq_true, if_false] at h2`. Take the linear combination `(-1/2 : ℂ) * h2`. Conclude with `(hab rfl).elim`. Establish `hk' : σ k = R.U.π (T.expt ((1 : ℝ) • X))`.

Rewrite using `[hF, one_smul, T.expt_cov X hX, ← hexp]`. Use `congr 1`. Use `open scoped Matrix.Norms.Operator in`. Conclude with `(NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by`. Conclude with `LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm`.

Rewrite using `[hk']`. Conclude with `flow_mem_map R.ι (R.HK.act X) W (hK X hKC) (fun t => R.U.π (T.expt (t • X))) (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (R.der X hX) 1`.
-/
theorem isKStableOn_of_kStable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → KStable R.HK.act W → IsKStableOn ε σ (W.map R.ι) := by
  intro p q n e ε T R σ hb hF W hfin hK k hk
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective Y
  have hX : X ∈ upq p q := by
    have h1 := hY.1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hKC : IsKC X := by
    intro a b hab
    rw [hb.sameBlock_iff] at hab
    have h2 := congrFun (congrFun hY.2 (e a)) (e b)
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at h2
    cases h3 : ε (e a) <;> cases h4 : ε (e b) <;> rw [h3, h4] at hab h2
    · exact (hab rfl).elim
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (1/2 : ℂ) * h2
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (-1/2 : ℂ) * h2
    · exact (hab rfl).elim
  have hk' : σ k = R.U.π (T.expt ((1 : ℝ) • X)) := by
    rw [hF, one_smul, T.expt_cov X hX, ← hexp]
    congr 1
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm
  rw [hk']
  exact flow_mem_map R.ι (R.HK.act X) W (hK X hKC) (fun t => R.U.π (T.expt (t • X)))
    (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (R.der X hX) 1

end GlobalTheory.RealPar
