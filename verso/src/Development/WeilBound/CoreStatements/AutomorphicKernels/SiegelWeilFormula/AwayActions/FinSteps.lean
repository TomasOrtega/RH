import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SDf

variable (d : SD σ)

/- English proof (translation)
Establish `hβf : finOne F • β = β`. Establish `h` using `smul_split (F := F) β`. Rewrite `h` using `[hβ, zero_add]`. Conclude with `h`. Establish `hq : ∀ X Z : Mx F E d.m d.n, finOne F • Z = 0 → β * d.gram (X + Z) (X + Z) = β * d.gram X X`.

Introduce `X Z hZ`. Establish `hZe : eInf F • Z = Z`. Establish `h` using `smul_split (F := F) Z`. Rewrite `h` using `[hZ, add_zero]`. Conclude with `h`.

Establish `h1 : β * d.gram X Z = 0`. Rewrite using `[← hZe, gram_smul_right, ← hβf, Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_mul_eInf, zero_smul]`. Establish `h2 : β * d.gram Z X = 0`. Rewrite using `[← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne, zero_smul]`. Establish `h3 : β * d.gram Z Z = 0`.

Rewrite using `[← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne, zero_smul]`. Simplify using `only [gram_add_left, gram_add_right, Matrix.mul_add, h1, h2, h3, add_zero]`. Use `⟨fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `X Z hZ show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) = d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X`. Rewrite using `[hq X Z hZ, hG X Z hZ]`.

Introduce `f hf Φ hΦ hTΦ`. Use function extensionality and compare the values at `X`. Rewrite using `[(hT.2.1 F E σ d Φ hΦ).1 x β hx X, hTΦ]`. Simplify using `only [id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepN (hT : TAll) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    StepF d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβf : finOne F • β = β := by
    have h := smul_split (F := F) β
    rw [hβ, zero_add] at h
    exact h
  have hq : ∀ X Z : Mx F E d.m d.n, finOne F • Z = 0 → β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
    intro X Z hZ
    have hZe : eInf F • Z = Z := by
      have h := smul_split (F := F) Z
      rw [hZ, add_zero] at h
      exact h
    have h1 : β * d.gram X Z = 0 := by
      rw [← hZe, gram_smul_right, ← hβf, Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_mul_eInf,
        zero_smul]
    have h2 : β * d.gram Z X = 0 := by
      rw [← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne,
        zero_smul]
    have h3 : β * d.gram Z Z = 0 := by
      rw [← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne,
        zero_smul]
    simp only [gram_add_left, gram_add_right, Matrix.mul_add, h1, h2, h3, add_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hq X Z hZ, hG X Z hZ]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [(hT.2.1 F E σ d Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring

/- English proof (translation)
Establish `hinv : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ = eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))`. Establish `h1 : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mul, Matrix.one_mul]`. Use `_ = (eInf F • a'.1) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by`.

Rewrite using `[ha]`. Use `_ = eInf F • (a'.1 * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))) := by`. Rewrite using `[Matrix.smul_mul]`. Use `_ = eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Rewrite using `[← Matrix.transpose_smul, h1, Matrix.transpose_smul, Matrix.transpose_one]`. Take `⟨c, hc⟩ : ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, d.T (d.om x Φ) X = c * d.T Φ (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ)` from `⟨_, fun Φ hΦ X => (hT.2.1 F E σ d Φ hΦ).2.1 x a a' hx X⟩`. Use `⟨fun G X => c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ), fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `X Z hZ show c * G ((X + Z) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) = c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ)`. Rewrite using `[Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]`.

Introduce `f hf Φ hΦ hTΦ`. Use function extensionality and compare the values at `X`. Establish `hfX : f (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) = f X`. Establish `e1 : X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X = X * (((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - 1)`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`.

Establish `h0 : eInf F • (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X) = 0`. Rewrite using `[e1, ← Matrix.mul_smul, smul_sub, hinv, sub_self, Matrix.mul_zero]`. Use `hf X _ ((cw_zero_iff d _).2 h0)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[hc Φ hΦ X, hTΦ]`.

Simplify using `only [id]`. Rewrite using `[hfX]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepM (hT : TAll) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, StepF d x id B := by
  have hinv : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ =
      eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    have h1 : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) =
        eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      calc eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))
          = (eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))) *
              ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
        _ = (eInf F • a'.1) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [ha]
        _ = eInf F • (a'.1 * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
            rw [Matrix.smul_mul]
        _ = eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← Matrix.transpose_smul, h1, Matrix.transpose_smul, Matrix.transpose_one]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, d.T (d.om x Φ) X =
      c * d.T Φ (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) :=
    ⟨_, fun Φ hΦ X => (hT.2.1 F E σ d Φ hΦ).2.1 x a a' hx X⟩
  refine ⟨fun G X => c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ),
    fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩
  · intro X Z hZ
    show c * G ((X + Z) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) =
      c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · intro f hf Φ hΦ hTΦ
    funext X
    have hfX : f (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) = f X := by
      have e1 : X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X =
          X * (((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - 1) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
      have h0 : eInf F • (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X) = 0 := by
        rw [e1, ← Matrix.mul_smul, smul_sub, hinv, sub_self, Matrix.mul_zero]
      have := hf X _ ((cw_zero_iff d _).2 h0)
      rwa [add_sub_cancel] at this
    rw [hc Φ hΦ X, hTΦ]
    simp only [id]
    rw [hfX]
    ring

end SDf

end PositivityTheory.SiegelWeilFormula.KAway

end
