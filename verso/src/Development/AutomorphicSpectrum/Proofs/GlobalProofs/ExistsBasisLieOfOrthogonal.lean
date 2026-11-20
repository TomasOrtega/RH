import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[vecOf, Complex.inner]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

/- English proof (translation)
Establish `h1 : kᴴ * k = 1` using `(Matrix.mem_unitaryGroup_iff').1 hk`. Establish `h2 : k * kᴴ = 1` using `(Matrix.mem_unitaryGroup_iff).1 hk`. Establish `hinv : k⁻¹ = kᴴ` using `Matrix.inv_eq_right_inv h2`. Rewrite using `[inner_vecOf, inner_vecOf, hinv]`. Establish `: (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]`. Rewrite using `[this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
Set `B` to `stdOrthonormalBasis ℝ W`. Use `⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ`. Introduce `x hx`. Use `congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)` as an intermediate fact.

Simplify `this.symm` using `[Submodule.coe_sum]`.
-/
theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]`. Establish `h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ` using `by conv_lhs => rw [hexp j]`. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]`. Rewrite using `[← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]`.
-/
theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in

/- English proof (translation)
Introduce `n G hG`. Take `⟨hadd, hsmul, -, hAd⟩` from `lieOf_isLieSubalgebra hG`. Set `L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)` to `{ carrier := HCSS.lieOf G add_mem' := fun {X Y} hX hY => hadd X Y hX hY zero_mem' := fun t => by simpa using hG.one_mem smul_mem' := fun r X hX => hsmul r X hX }`. Set `W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n))` to `L.map (vecOf (n := n)).toLinearMap`. Establish `: FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n))` using `FiniteDimensional.complexToReal _`.

Take `⟨d, e, heW, hon, hexp⟩` from `exists_orthonormal W`. Establish `hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W` using `fun X hX => ⟨X, hX, rfl⟩`. Establish `hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G`. Introduce `i`. Take `⟨X, hX, hXe⟩` from `heW i`.

Establish `: vecOf.symm (e i) = X`. Rewrite using `[← hXe]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hX`.

Establish `hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i)`. Introduce `X hX`. Establish `h` using `hexp _ (hmemW X hX)`. Establish `h2` using `congrArg (vecOf (n := n)).symm h`. Rewrite `h2` using `[map_sum]`.

Simplify using `using h2`. Use `⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)`. Introduce `X hX`. Conclude with `⟨_, hexpM X hX⟩`.

Introduce `k hk`. Establish `hkG : k ∈ G` using `hk.1`. Establish `hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ` using `hk.2`. Set `f : Fin d → EuclideanSpace ℂ (Fin n × Fin n)` to `fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)`. Establish `hfW : ∀ i, f i ∈ W` using `fun i => hmemW _ (hAd k hkG _ (hbL i))`.

Establish `hO` using `orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by`. Use `inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))` as an intermediate fact. Simplify `this)` using `[f]`. Use `⟨_, hO, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `hexp _ (hfW i)`.

Establish `h2` using `congrArg (vecOf (n := n)).symm h`. Rewrite `h2` using `[map_sum]`. Simplify `h2` using `[f]`.
-/
theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  intro n G hG
  obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
  let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := HCSS.lieOf G
      add_mem' := fun {X Y} hX hY => hadd X Y hX hY
      zero_mem' := fun t => by simpa using hG.one_mem
      smul_mem' := fun r X hX => hsmul r X hX }
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
    FiniteDimensional.complexToReal _
  obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
  have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
  have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
    intro i
    obtain ⟨X, hX, hXe⟩ := heW i
    have : vecOf.symm (e i) = X := by
      rw [← hXe]; simp
    rw [this]; exact hX
  have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
    intro X hX
    have h := hexp _ (hmemW X hX)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa using h2
  refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
  · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
      (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
  · intro X hX
    exact ⟨_, hexpM X hX⟩
  · intro k hk
    have hkG : k ∈ G := hk.1
    have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
    let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
    have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
    have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
      have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
      simpa [f] using this)
    refine ⟨_, hO, fun i => ?_⟩
    have h := hexp _ (hfW i)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa [f] using h2

end
