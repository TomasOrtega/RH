import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyTransport

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hm, hF, he⟩` from `hf (A * g₀ * B) (hAB g₀ hg₀)`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun g => A * g * B map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c x => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }`. Set `L'` to `LinearMap.toContinuousLinearMap L`. Use `⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hF.comp L'.contDiff.contDiffOn (fun x hx => hx)`. Introduce `g hg hgJ`. Conclude with `he (A * g * B) hg (hAB g hgJ)`.
-/
theorem smoothOn_comp {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H J A B : Matrix (Fin n) (Fin n) ℂ} (hAB : ∀ g, gᴴ * J * g = J → (A * g * B)ᴴ * H * (A * g * B) = H)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : PI.UpqRep.SmoothOnH H f) :
    PI.PhMeasCore.SmoothOnH J (fun g => f (A * g * B)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, he⟩ := hf (A * g₀ * B) (hAB g₀ hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => A * g * B
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let L' := LinearMap.toContinuousLinearMap L
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, ?_, ?_⟩
  · exact hF.comp L'.contDiff.contDiffOn (fun x hx => hx)
  · intro g hg hgJ
    exact he (A * g * B) hg (hAB g hgJ)

end Smooth

/- English proof (translation)
Unfold `PI.PhMeasCore.dsig PI.UpqRep.dsig`. Use `congr 1`. Use function extensionality and compare the values at `t`. Establish `: (t : ℂ) • (Q⁻¹ * X * Q) = Q⁻¹ * ((t : ℂ) • X) * Q`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul]`.

Rewrite using `[this, Matrix.exp_conj' Q _ hQ]`.
-/
theorem dsig_conj {k r : ℕ} (R : Rep k r) {Q : Mx k r} (hQ : IsUnit Q) (X : Mx k r) (v : R.H) :
    PI.PhMeasCore.dsig (fun g => R.σ (Q⁻¹ * g * Q)) X v =
      PI.UpqRep.dsig (k := k) (r := r) R.σ (Q⁻¹ * X * Q) v := by
  unfold PI.PhMeasCore.dsig PI.UpqRep.dsig
  congr 1
  funext t
  have : (t : ℂ) • (Q⁻¹ * X * Q) = Q⁻¹ * ((t : ℂ) • X) * Q := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_conj' Q _ hQ]

/- English proof (translation)
Introduce `k r ε R Q ⟨⟨hunit, hcay⟩, hU⟩`. Establish `h1 : Q * Qᴴ = 1` using `(Matrix.mem_unitaryGroup_iff).mp hU`. Establish `h2 : Qᴴ * Q = 1` using `(Matrix.mem_unitaryGroup_iff').mp hU`. Establish `hinv : Q⁻¹ = Qᴴ` using `Matrix.inv_eq_left_inv h2`. Establish `hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * Formalism.REAL.Jm ε * Q` using `hcay.symm`.

Establish `hc : ∀ Z : Mx k r, Q * (Qᴴ * Z) = Z` using `fun Z => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Use `smoothOn_comp (H := PI.UpqRep.Hpk k r) (f := fun g => R.σ g v) ?_ hv` and prove the remaining obligations. Introduce `g hg`.

Rewrite using `[← hcay, hinv]`. Establish `hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε` using `hg`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc]`. Simplify using `only [Matrix.mul_assoc] at hg'`. Rewrite using `[← Matrix.mul_assoc (PI.UpqRep.Jm ε) g Q, ← Matrix.mul_assoc gᴴ _ Q, hg']`.

Introduce `Y v`. Establish `ht : Q⁻¹ * PI.DSInfCharCap.thetaJ ε Y * Q = -(Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * Y * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r)`. Rewrite using `[hH, hinv, PI.DSInfCharCap.thetaJ]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc, Matrix.mul_neg, Matrix.neg_mul]`. Unfold `PI.DSInfCharCap.dsigC Rep.dC`.

Rewrite using `[dsig_conj R hunit, dsig_conj R hunit, ← ht]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]`.
-/
theorem smooth_and_dsigC_transport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  intro k r ε R Q ⟨⟨hunit, hcay⟩, hU⟩
  have h1 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  have h2 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h2
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * Formalism.REAL.Jm ε * Q := hcay.symm
  have hc : ∀ Z : Mx k r, Q * (Qᴴ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  constructor
  · intro v hv
    refine smoothOn_comp (H := PI.UpqRep.Hpk k r) (f := fun g => R.σ g v) ?_ hv
    intro g hg
    rw [← hcay, hinv]
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_assoc] at hg'
    rw [← Matrix.mul_assoc (PI.UpqRep.Jm ε) g Q, ← Matrix.mul_assoc gᴴ _ Q, hg']
  · intro Y v
    have ht : Q⁻¹ * PI.DSInfCharCap.thetaJ ε Y * Q =
        -(Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * Y * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r) := by
      rw [hH, hinv, PI.DSInfCharCap.thetaJ]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc,
        Matrix.mul_neg, Matrix.neg_mul]
    unfold PI.DSInfCharCap.dsigC Rep.dC
    rw [dsig_conj R hunit, dsig_conj R hunit, ← ht]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

end GlobalTheory.CayleyTransport
