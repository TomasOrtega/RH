import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalG

open Matrix Filter Topology

noncomputable section

namespace QnYLeibnizW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E) (NormedSpace.exp ((s : ℂ) • X) * X * E) s`. Introduce `s`. Establish `h` using `hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (s : ℂ)`. Establish `h2` using `h.scomp (x := s) Complex.ofRealCLM.hasDerivAt`. Establish `h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X)) (NormedSpace.exp ((s : ℂ) • X) * X) s`.

Establish `hcomm : X * NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * X` using `(((Commute.refl X).smul_right (s : ℂ)).exp_right).eq`. Conclude with `h2.congr_deriv (by simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; exact hcomm)`. Conclude with `h3.mul_const E`. Establish `hc` using `is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E) (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, Matrix.mul_assoc, hXE, Matrix.mul_zero])`. Use `hc t 0` as an intermediate fact.

Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this`. Conclude with `this`.
-/
lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
      (NormedSpace.exp ((s : ℂ) • X) * X * E) s := by
    intro s
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (s : ℂ)
    have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
    have h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X))
        (NormedSpace.exp ((s : ℂ) • X) * X) s := by
      have hcomm : X * NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * X :=
        (((Commute.refl X).smul_right (s : ℂ)).exp_right).eq
      exact h2.congr_deriv (by simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; exact hcomm)
    exact h3.mul_const E
  have hc := is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
    (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, Matrix.mul_assoc, hXE, Matrix.mul_zero])
  have := hc t 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
  exact this

end Linfty

/- English proof (translation)
Set `E : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun j _ => v j`. Establish `hXE : X * E = 0`. Use extensionality with `j l`. Use `congrFun hXv j` as an intermediate fact. Simplify `this` using `[E, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Establish `h` using `exp_mul_fix X E hXE t`. Use function extensionality and compare the values at `j`. Use `congrFun (congrFun h j) j` as an intermediate fact. Simplify `this` using `[E, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j _ => v j
  have hXE : X * E = 0 := by
    ext j l
    have := congrFun hXv j
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h := exp_mul_fix X E hXE t
  funext j
  have := congrFun (congrFun h j) j
  simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/- English proof (translation)
Establish `hU : IsUnit H` using `IsUnit.of_mul_eq_one _ hH`. Establish `hinv : H⁻¹ = H` using `Matrix.inv_eq_left_inv hH`. Establish `h1 : Yᴴ * H = -(H * Y)` using `eq_neg_of_add_eq_zero_left hY`. Establish `hYh : Yᴴ = H * (-Y) * H⁻¹`. Rewrite using `[hinv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H`. Rewrite using `[← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]`. Establish `hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]`.

Use `show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H`. Rewrite using `[hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]`.
-/
lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  have hU : IsUnit H := IsUnit.of_mul_eq_one _ hH
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hH
  have h1 : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [hinv]
    calc Yᴴ = Yᴴ * H * H := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = H * (-Y) * H := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

/- English proof (translation)
Take `⟨hgU, hgF⟩` from `hg`. Take `⟨hhU, hhF⟩` from `hh`. Use `⟨?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Establish `e1 : gᴴ * Hpk k r * g = Hpk k r` using `hgU`.

Establish `e2 : hᴴ * Hpk k r * h = Hpk k r` using `hhU`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [e1, e2]`. Take `⟨g1, g2⟩` from `hgF a ha`.

Take `⟨h1, h2⟩` from `hhF a ha`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, h1, g1]`. Rewrite using `[← Matrix.mulVec_mulVec, h2, g2]`.
-/
lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hgU
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hhU
    calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · obtain ⟨g1, g2⟩ := hgF a ha
    obtain ⟨h1, h2⟩ := hhF a ha
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1, g1]
    · rw [← Matrix.mulVec_mulVec, h2, g2]

/- English proof (translation)
Establish `e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩ ⋂ a : Fin r, ⋂ (_ : a.val < i.val), ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})`. Use extensionality with `g`. Simplify using `only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]`. Rewrite using `[e]`. Use `IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)` and prove the remaining obligations.

Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Conclude with `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`. Conclude with `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`.
-/
lemma glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ⋂ a : Fin r, ⋂ (_ : a.val < i.val),
        ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by
    ext g
    simp only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

/- English proof (translation)
Take `⟨hL, hF⟩` from `hX`. Establish `hH : Hpk k r * Hpk k r = 1` using `(hpkFacts k r).2.1`. Use `⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hL, smul_zero]`. Take `⟨h1, h2⟩` from `hF a ha`.

Conclude with `⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩`.
-/
lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

end QnYLeibnizW
