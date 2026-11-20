import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilradicalAdjointExpStableStatement
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

/- English proof (translation)
Establish `h1 : Xᴴ = J * (-X) * J⁻¹`. Rewrite using `[mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]`. Unfold `IsUni`. Rewrite using `[← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ), nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
theorem isUni_exp {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  unfold IsUni
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

/- English proof (translation)
Unfold `IsSkew at *`. Rewrite using `[conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]`.
-/
theorem isSkew_real_smul {J Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

/- English proof (translation)
Establish `h1 : IsUni J 1` using `by simp [IsUni]`. Use `hs 1 1 h1 h1` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `mul_eq_left.mp this.symm`.
-/
theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) :
    s 1 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [one_mul] at this
  exact mul_eq_left.mp this.symm

/- English proof (translation)
Simplify using `[lineOf, map_one_of_isMulOn hs]`.
-/
theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

/- English proof (translation)
Establish `h` using `hρ Z hZ f g 0`. Rewrite `h` using `[lineOf_zero hs, mul_one]`. Conclude with `h.deriv.symm`.
-/
theorem rho_apply_eq_deriv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) (g : G) :
    (ρ Z f).1 g = deriv (fun τ : ℝ => f.1 (g * lineOf s Z τ)) 0 := by
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

/- English proof (translation)
Establish `hA : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hJh, mul_assoc, mul_assoc, nonsing_inv_mul _ hJ, mul_one]`. Establish `hB : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hJ, one_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsSkew`. Rewrite using `[conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_sub, sub_mul, mul_sub, hA, hB]`. Establish `: star (1/2 : ℂ) = 1/2` using `by simp`. Rewrite using `[this]`. Use `module`.

Unfold `IsSkew`. Rewrite using `[conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_add, add_mul, mul_add, hA, hB]`. Establish `: star (-Complex.I/2 : ℂ) = Complex.I/2` using `by simp`. Rewrite using `[this]`. Use `module`.

Rewrite using `[smul_smul, show Complex.I * (-Complex.I/2) = 1/2 by linear_combination (-1/2 : ℂ) * Complex.I_sq] module`.
-/
theorem decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsSkew J ((1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J)) ∧ IsSkew J ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) ∧
      Y = (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) + Complex.I • ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) := by
  have hA : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hJh,
      mul_assoc, mul_assoc, nonsing_inv_mul _ hJ, mul_one]
  have hB : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hJ, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_sub, sub_mul, mul_sub, hA, hB]
    have : star (1/2 : ℂ) = 1/2 := by simp
    rw [this]
    module
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_add, add_mul, mul_add, hA, hB]
    have : star (-Complex.I/2 : ℂ) = Complex.I/2 := by simp
    rw [this]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I/2) = 1/2 by linear_combination (-1/2 : ℂ) * Complex.I_sq]
    module

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

def IsLeftInv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (N : Subgroup G) (f : smLoc J s) : Prop :=
  ∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g

/- English proof (translation)
Introduce `ν hν g`. Rewrite using `[rho_apply_eq_deriv hs hρ hZ, rho_apply_eq_deriv hs hρ hZ]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[mul_assoc, hf ν hν]`.
-/
theorem isLeftInv_rho_skew {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Z f) := by
  intro ν hν g
  rw [rho_apply_eq_deriv hs hρ hZ, rho_apply_eq_deriv hs hρ hZ]
  congr 1
  funext τ
  rw [mul_assoc, hf ν hν]

/- English proof (translation)
Substitute `hY` using the available equality. Rewrite using `[map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.
-/
theorem rho_apply_add_I {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) {Y : Matrix (Fin n) (Fin n) ℂ}
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) ℂ) (hY : Y = Z₁ + Complex.I • Z₂) (f : smLoc J s) (g : G) :
    (ρ Y f).1 g = (ρ Z₁ f).1 g + Complex.I * (ρ Z₂ f).1 g := by
  subst hY
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨h1, h2, hY⟩` from `decomp hJh hJ Y`. Establish `e1` using `isLeftInv_rho_skew hs hρ h1 hf`. Establish `e2` using `isLeftInv_rho_skew hs hρ h2 hf`. Introduce `ν hν g`. Rewrite using `[rho_apply_add_I ρ _ _ hY, rho_apply_add_I ρ _ _ hY, e1 ν hν, e2 ν hν]`.
-/
theorem isLeftInv_rho {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    (Y : Matrix (Fin n) (Fin n) ℂ) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Y f) := by
  obtain ⟨h1, h2, hY⟩ := decomp hJh hJ Y
  have e1 := isLeftInv_rho_skew hs hρ h1 hf
  have e2 := isLeftInv_rho_skew hs hρ h2 hf
  intro ν hν g
  rw [rho_apply_add_I ρ _ _ hY, rho_apply_add_I ρ _ _ hY, e1 ν hν, e2 ν hν]

/- English proof (translation)
Proceed by induction on `hw using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨Y, rfl⟩` from `hx`. Conclude with `fun f hf => isLeftInv_rho hJh hJ hs hρ Y hf`. Consider the case `algebraMap r`.

Introduce `f hf ν hν g`. Simplify using `only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]`. Rewrite using `[hf ν hν]`. Consider the case `add a b _ _ ha hb`. Introduce `f hf ν hν g`.

Simplify using `only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]`. Rewrite using `[ha f hf ν hν, hb f hf ν hν]`. Consider the case `mul a b _ _ ha hb`. Introduce `f hf`. Conclude with `ha _ (hb f hf)`.
-/
theorem isLeftInv_adjoin {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {w : Module.End ℂ (smLoc J s)} (hw : w ∈ Algebra.adjoin ℂ (Set.range ρ)) :
    ∀ f : smLoc J s, IsLeftInv N f → IsLeftInv N (w f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    exact fun f hf => isLeftInv_rho hJh hJ hs hρ Y hf
  | algebraMap r =>
    intro f hf ν hν g
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hf ν hν]
  | add a b _ _ ha hb =>
    intro f hf ν hν g
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [ha f hf ν hν, hb f hf ν hν]
  | mul a b _ _ ha hb =>
    intro f hf
    exact ha _ (hb f hf)

/- English proof (translation)
Rewrite using `[rho_apply_eq_deriv hs hρ hZ]`. Establish `hc : (fun τ : ℝ => f.1 (1 * lineOf s Z τ)) = fun _ => f.1 1`. Use function extensionality and compare the values at `τ`. Establish `hmem : lineOf s Z τ ∈ N`. Use `hN _ (isUni_exp hJ (isSkew_real_smul hZ τ)) ?_` and prove the remaining obligations.

Conclude with `(GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x _ (Submodule.smul_of_tower_mem _ τ hZn)).2`. Rewrite using `[one_mul, ← mul_one (lineOf s Z τ), hf _ hmem]`. Rewrite using `[hc, deriv_const]`.
-/
theorem rho_kill_skew {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {x : Fin n → ℂ}
    {N : Subgroup G} (hN : ∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (hZn : Z ∈ nilRad J x) {f : smLoc J s} (hf : IsLeftInv N f) :
    (ρ Z f).1 1 = 0 := by
  rw [rho_apply_eq_deriv hs hρ hZ]
  have hc : (fun τ : ℝ => f.1 (1 * lineOf s Z τ)) = fun _ => f.1 1 := by
    funext τ
    have hmem : lineOf s Z τ ∈ N := by
      refine hN _ (isUni_exp hJ (isSkew_real_smul hZ τ)) ?_
      exact (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x _ (Submodule.smul_of_tower_mem _ τ hZn)).2
    rw [one_mul, ← mul_one (lineOf s Z τ), hf _ hmem]
  rw [hc, deriv_const]

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFin

/- English proof (translation)
Introduce `n G _ J s hJh hJ hs ρ hρ x N hN f hf T hT`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨Y, hY, w, hw, rfl⟩` from `ha`. Establish `hwf : GlobalTheory.TorFinKill.IsLeftInv N (w f)` using `GlobalTheory.TorFinKill.isLeftInv_adjoin hJh hJ hs hρ hw f hf`.

Take `⟨h1, h2, hYe⟩` from `GlobalTheory.TorFinKill.decomp hJh hJ Y`. Establish `hs'` using `(GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x Y hY).1`. Establish `m1 : (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) ∈ nilRad J x` using `Submodule.smul_mem _ _ (Submodule.sub_mem _ hY hs')`. Establish `m2 : (-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J) ∈ nilRad J x` using `Submodule.smul_mem _ _ (Submodule.add_mem _ hY hs')`. Rewrite using `[Module.End.mul_apply, GlobalTheory.TorFinKill.rho_apply_add_I ρ _ _ hYe, GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h1 m1 hwf, GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h2 m2 hwf, mul_zero, add_zero]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`.
-/
theorem leftIdl_apply_one_eq_zero : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  intro n G _ J s hJh hJ hs ρ hρ x N hN f hf T hT
  induction hT using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    have hwf : GlobalTheory.TorFinKill.IsLeftInv N (w f) := GlobalTheory.TorFinKill.isLeftInv_adjoin hJh hJ hs hρ hw f hf
    obtain ⟨h1, h2, hYe⟩ := GlobalTheory.TorFinKill.decomp hJh hJ Y
    have hs' := (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x Y hY).1
    have m1 : (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.sub_mem _ hY hs')
    have m2 : (-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.add_mem _ hY hs')
    rw [Module.End.mul_apply, GlobalTheory.TorFinKill.rho_apply_add_I ρ _ _ hYe,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h1 m1 hwf,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h2 m2 hwf, mul_zero, add_zero]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

end GlobalTheory.TorFin
