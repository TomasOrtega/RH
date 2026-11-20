import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ZReAddZImStar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

/- English proof (translation)
Establish `e1 : star ((1 : ℂ) / 2) = 1 / 2` using `by simp`. Use extensionality with `i j`. Simplify using `only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]`. Apply the tactic sequence `by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>`. Apply the tactic sequence `simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>`.

Apply the tactic sequence `(try subst_vars) <;> unfold sgn <;> split_ifs <;>`. Apply the tactic sequence `first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)`.
-/
theorem isUe_zRe (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zRe ε a b) := by
  have e1 : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)

/- English proof (translation)
Establish `e2 : star (-(Complex.I / 2)) = Complex.I / 2`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`. Use extensionality with `i j`. Simplify using `only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]`. Apply the tactic sequence `by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>`.

Apply the tactic sequence `simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>`. Apply the tactic sequence `(try subst_vars) <;> unfold sgn <;> split_ifs <;>`. Apply the tactic sequence `first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)`.
-/
theorem isUe_zIm (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zIm ε a b) := by
  have e2 : star (-(Complex.I / 2)) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)

/- English proof (translation)
Establish `h : theta ω Φ g = theta ω (ω g Φ) 1`. Use function extensionality and compare the values at `h`. Simplify using `only [theta, map_one, Module.End.one_apply]`. Simplify using `only [thetaInt, h]`.
-/
theorem thetaInt_at {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν Φ g = thetaInt ω ν (ω g Φ) 1 := by
  have h : theta ω Φ g = theta ω (ω g Φ) 1 := by
    funext h
    simp only [theta, map_one, Module.End.one_apply]
  simp only [thetaInt, h]

/- English proof (translation)
Establish `h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h`. Use function extensionality and compare the values at `h`. Simplify using `only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `tsum_mul_left`. Simplify using `only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]`.

Conclude with `(mul_smul_comm _ _ _).symm`.
-/
theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (r : ℂ) (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν (r • Φ) g = r * thetaInt ω ν Φ g := by
  have h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h := by
    funext h
    simp only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  simp only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

/- English proof (translation)
Unfold `phiS`. Rewrite using `[dif_pos h]`.
-/
theorem phiS_of_mem {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS; rw [dif_pos h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [tens, fP, evX, map_add, MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tens_add_smul {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (A B : PX m n) (r : ℂ) :
    tens θ τ fr (fP c (A + r • B)) Ψ = tens θ τ fr (fP c A) Ψ + r • tens θ τ fr (fP c B) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add, MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH

namespace PositivityTheory.Rg.Sw.Glob

open IInvH in
/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P`. Establish `hmem` using `fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q`. Establish `hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ` using `fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩`. Establish `h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0`. Introduce `X hX Q`.

Unfold `thF`. Rewrite using `[thetaInt_at]`. Conclude with `hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q)) (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)`. Rewrite using `[hOp_eq]`. Use `set A := vfX (cLoc l τ) (zRe ε a b) P`.

Use `set B := vfX (cLoc l τ) (zIm ε a b) P`. Establish `hA` using `phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1`. Establish `hB` using `phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1`. Establish `hAB` using `phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1`. Establish `hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) = phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B`.

Rewrite using `[hA, hB, hAB]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_add, Submodule.coe_smul]`. Conclude with `tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I`. Establish `hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s` using `by rw [hA]; exact (hmem A).2`.

Establish `hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s`. Rewrite using `[hB, Submodule.coe_smul]`. Conclude with `(fockA θ V n l s).smul_mem _ (hmem B).2`. Unfold `thF`. Rewrite using `[hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]`.

Establish `e1` using `h0 _ (isUe_zRe ε a b) P`. Establish `e2` using `h0 _ (isUe_zIm ε a b) P`. Unfold `thF at e1 e2`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gIinv_of (hT : TensMem) (hL : ThLin) (hC : LieComm) (hO : DerivOne) : GIinv := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P
  have hmem := fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q
  have hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ :=
    fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩

  have h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0 := by
    intro X hX Q
    unfold thF
    rw [thetaInt_at]
    exact hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q))
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)
  rw [hOp_eq]
  set A := vfX (cLoc l τ) (zRe ε a b) P
  set B := vfX (cLoc l τ) (zIm ε a b) P
  have hA := phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1
  have hB := phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1
  have hAB := phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1
  have hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) =
      phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B := by
    rw [hA, hB, hAB]
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I
  have hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s := by rw [hA]; exact (hmem A).2
  have hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s := by
    rw [hB, Submodule.coe_smul]; exact (fockA θ V n l s).smul_mem _ (hmem B).2
  unfold thF
  rw [hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]
  have e1 := h0 _ (isUe_zRe ε a b) P
  have e2 := h0 _ (isUe_zIm ε a b) P
  unfold thF at e1 e2
  rw [e1, e2]
  ring

end PositivityTheory.Rg.Sw.Glob
