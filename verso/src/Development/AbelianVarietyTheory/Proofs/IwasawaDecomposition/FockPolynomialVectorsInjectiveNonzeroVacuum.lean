import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIndep

section Mat

variable {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {H t B' : Matrix (Fin m) (Fin m) ℂ} {δ : Fin m → ℂ}

/- English proof (translation)
Establish `hu : IsUnit B.det` using `Matrix.isUnit_det_of_left_inverse hB`. Establish `hG : G⁻¹ = B * Bᴴ`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])`.

Establish `h1 : Bᴴ * (B⁻¹)ᴴ = 1` using `by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]`. Establish `e : G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b = B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * B') * Matrix.single a b (1 : ℂ) * B⁻¹)`. Simplify using `only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, hB', Matrix.one_mul, Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, Matrix.diagonal_apply]`. Distinguish the cases in `h : c = a`.

Substitute `h` using the available equality. Distinguish the cases in `h' : d = b`. Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.trace_single_eq_of_ne _ _ _ h', Ne.symm h']`.

Simplify using `[h, Ne.symm h]`.
-/
theorem trace_unitMap (hB : Bᴴ * G * B = 1) (hB' : B'ᴴ * H * B' = diagonal δ) (a c : Fin m) (b d : Fin n) :
    (G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b).trace = if (a, b) = (c, d) then δ a else 0 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hG : G⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]
  have e : G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b =
      B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * B') * Matrix.single a b (1 : ℂ) * B⁻¹) := by
    simp only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, hB', Matrix.one_mul,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, Matrix.diagonal_apply]
  by_cases h : c = a
  · subst h
    by_cases h' : d = b
    · subst h'; simp
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h', Ne.symm h']
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `e : diagonal δ * Matrix.single a b (1 : ℂ) = δ a • Matrix.single a b (1 : ℂ)`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]`. Use `split_ifs with h`. Rewrite using `[h.1, smul_eq_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[cplxO, unitMap, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ht, Matrix.mul_assoc B', e, Matrix.mul_smul, Matrix.smul_mul, smul_smul]`.
-/
theorem cplxO_unitMap (ht : t * B' = B' * diagonal δ) (a : Fin m) (b : Fin n) :
    cplxO 1 t (unitMap B B' a b) = (Complex.I * δ a) • unitMap B B' a b := by
  have e : diagonal δ * Matrix.single a b (1 : ℂ) = δ a • Matrix.single a b (1 : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    split_ifs with h
    · rw [h.1, smul_eq_mul]
    · simp
  rw [cplxO, unitMap, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ht, Matrix.mul_assoc B', e,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]

end Mat

/- English proof (translation)
Introduce `D ψ θ S T S' M BS f hψ hθ hS hBS hf f0 hv`. Establish `hT` using `GlobalTheory.Chain.VacVec.cart_isCartanInv M`. Establish `hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1` using `fun τ => by`. Take `⟨ε, h1, h2, -⟩` from `hBS τ`. Rewrite using `[h2, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `h1 a with h | h` into its components or cases. Rewrite using `[h.1, Complex.ofReal_one]`. Conclude with `absurd a.2 (not_lt.2 h.2)`.

Establish `hu` using `fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `hB' : ∀ τ, (onb M τ)ᴴ * gramAt D T τ * onb M τ = diagonal fun a => if M.ε τ a then (1 : ℂ) else -1` using `fun τ => by`. Rewrite using `[← M.fr_gram τ, onb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ (hu τ), conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]`. Both sides reduce to the same expression. Establish `ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1` using `fun τ => by`.

Rewrite using `[cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]`. Both sides reduce to the same expression. Unfold `pureTensorO aPlusAll`. Use `pure_injective (P := IsThetaFunO ψ S T) (B := fun k => annih (heisO ψ S T) θ k.1 (cplxO 1 (cart M k.1)) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2)) (c := fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * π * Complex.I) * (Complex.I * (-2 * (tauE D k.1 D.host.xi0).im : ℝ)))) (fun _ _ => G …` and prove the remaining obligations. Conclude with `fun _ _ h => aPlus_theta hψ hθ _ _ _ h`.

Conclude with `fun _ _ h => annih_theta hψ hθ _ _ _ h`. Conclude with `fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h`. Conclude with `fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'`. Conclude with `fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h`. Conclude with `fun _ _ _ h h' => annih_add hψ hθ _ _ _ h h'`.

Conclude with `fun _ a _ h => annih_smul hψ hθ _ _ _ a h`. Introduce and unpack `⟨τ, a, b⟩ ⟨τ', c, d⟩ g hg`. Use `(annih_aPlus (sS := fun _ => 1) hψ hθ τ _ hS hT τ' _ hg).trans ?_` and prove the remaining obligations. Use `congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)` and prove the remaining obligations. Unfold `omDir`.

Distinguish the cases in `h : τ = τ'`. Substitute `h` using the available equality. Simplify using `only [if_true, cplxO_unitMap (ht τ), Matrix.mul_smul, Matrix.trace_smul, trace_unitMap (hB τ) (hB' τ), Prod.mk.injEq, true_and]`. Establish `hre` using `GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ`. Apply the tactic sequence `split_ifs <;> simp [Complex.mul_re, hre]`.

Simplify using `[h]`. Introduce `i`. Establish `him` using `xi_zero_im_pos D i.1`. Establish `hn : 0 < ‖tauE D i.1 D.host.xi0‖` using `norm_pos_iff.2 fun h => by simp [h] at him`. Establish `hfs : 0 < fockScale D i.1`.

Unfold `fockScale`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression. Simplify using `[hfs.ne', him.ne', Real.pi_ne_zero]`. Conclude with `fun i => hv i.1 _`.
-/
theorem pureTensorO_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  intro D ψ θ S T S' M BS f hψ hθ hS hBS hf f0 hv
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hB' : ∀ τ, (onb M τ)ᴴ * gramAt D T τ * onb M τ = diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [← M.fr_gram τ, onb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hu τ), conjTranspose_one, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  unfold pureTensorO aPlusAll
  refine pure_injective (P := IsThetaFunO ψ S T)
    (B := fun k => annih (heisO ψ S T) θ k.1 (cplxO 1 (cart M k.1)) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2))
    (c := fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * π * Complex.I) *
      (Complex.I * (-2 * (tauE D k.1 D.host.xi0).im : ℝ))))
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf f0 ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun _ _ h => annih_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · exact fun _ _ _ h h' => annih_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => annih_smul hψ hθ _ _ _ a h
  · rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩ g hg
    refine (annih_aPlus (sS := fun _ => 1) hψ hθ τ _ hS hT τ' _ hg).trans ?_
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    unfold omDir
    by_cases h : τ = τ'
    · subst h
      simp only [if_true, cplxO_unitMap (ht τ), Matrix.mul_smul, Matrix.trace_smul, trace_unitMap (hB τ) (hB' τ),
        Prod.mk.injEq, true_and]
      have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
      split_ifs <;> simp [Complex.mul_re, hre]
    · simp [h]
  · intro i
    have him := xi_zero_im_pos D i.1
    have hn : 0 < ‖tauE D i.1 D.host.xi0‖ := norm_pos_iff.2 fun h => by simp [h] at him
    have hfs : 0 < fockScale D i.1 := by
      unfold fockScale
      have := Real.pi_pos
      positivity
    simp [hfs.ne', him.ne', Real.pi_ne_zero]
  · exact fun i => hv i.1 _

end GlobalTheory.FockIndep
