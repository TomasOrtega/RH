import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOddParity

/- English proof (translation)
Take `⟨-, -, hnorm, -⟩` from `h`. Establish `hn` using `hnorm (idF D a)`. Rewrite `hn` using `[Formalism.L2.Theta.norm_idF, map_pow]`. Conclude with `hn`.
-/
theorem isEta_sq (D : D7) (η : (AF D.host.F)ˣ →* Circle) (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  obtain ⟨-, -, hnorm, -⟩ := h
  have hn := hnorm (idF D a)
  rw [Formalism.L2.Theta.norm_idF, map_pow] at hn
  exact hn

/- English proof (translation)
Unfold `Formalism.L2.Host.HChar.HasInfQ`. Use `⟨fun _ => 1, fun _ => by norm_num, ?_⟩` and prove the remaining obligations. Introduce `k`. Rewrite using `[h.inf k]`. Use `symm`.

Conclude with `Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)`.
-/
private theorem hasInfQ_half_of_isEtaT (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (h : Formalism.L2.Host.IsEtaT D.host χ) :
    χ.HasInfQ (tauE D) (fun _ => 1 / 2) := by
  unfold Formalism.L2.Host.HChar.HasInfQ
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
  intro k
  rw [h.inf k]
  symm
  exact Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)

/- English proof (translation)
Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Rewrite using `[Set.mem_setOf_eq]`. Use `⟨1, ?_, 1, ?_⟩` and prove the remaining obligations. Introduce `v first`. Consider the case `exact one_mem _`.

Consider the case `(rw [map_one]; exact one_mem _)`. Consider the case `simp [evalV]`. Apply the tactic sequence `rw [Algebra.TensorProduct.one_def] all_goals simp`.
-/
private theorem one_mem_intAE_twisted_operators (D : D7) : 1 ∈ intAE D := by
  apply AddSubgroup.subset_closure
  rw [Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_⟩
  · intro v
    first
      | exact one_mem _
      | (rw [map_one]; exact one_mem _)
      | simp [evalV]
  · rw [Algebra.TensorProduct.one_def]
    all_goals simp

/- English proof (translation)
Introduce `D c χ hc hχ μ n m hμ hμc hodd`. Unfold `IsEtaTilde`. Use `⟨hc.1, ?_, ?_, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D c χ (fun _ => 1 / 2) hc (hasInfQ_half_of_isEtaT D χ hχ) τ⟩` and prove the remaining obligations. Introduce `x h1 h2 h3`. Use `GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ hc (fun P => ?_) 1 (fun P _ => hχ.unr P) x ⟨h1, h2, h3⟩ ⟨finPart D (x : AE D) - 1, sub_mem h2 (one_mem_intAE_twisted_operators D), by rw [one_smul]⟩` and prove the remaining obligations.

Introduce `y hy _`. Conclude with `hχ.unr P y hy`. Unfold `ResEta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome at hμ hμc ⊢`. Use `⟨hμ.1, fun η hη a => ?_⟩` and prove the remaining obligations. Establish `e1 : μ (idF D a) = η a ^ n` using `hμ.2 η hη a`.

Establish `e2 : (μ * c⁻¹) (idF D a) = η a ^ m` using `hμc.2 η hη a`. Rewrite `e2` using `[MonoidHom.mul_apply, MonoidHom.inv_apply, e1]`. Establish `hs : η a ^ 2 = 1` using `isEta_sq D η hη a`. Establish `hi : (η a ^ m)⁻¹ = η a ^ m`. Rewrite using `[inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, hs, one_pow]`.

Establish `hc' : c (idF D a) = η a ^ n * (η a ^ m)⁻¹`. Rewrite using `[← e2, mul_inv_rev, inv_inv, mul_comm (c _), mul_inv_cancel_left]`. Take `⟨k, hk⟩` from `hodd`. Use `show c (idF D a) = η a ^ 1`. Rewrite using `[pow_one, hc', hi, ← pow_add, hk, pow_succ, pow_mul, hs, one_pow, one_mul]`.
-/
theorem isEtaTilde_of_odd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  intro D c χ hc hχ μ n m hμ hμc hodd
  unfold IsEtaTilde
  refine ⟨hc.1, ?_, ?_, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D c χ (fun _ => 1 / 2) hc
    (hasInfQ_half_of_isEtaT D χ hχ) τ⟩
  ·
    intro x h1 h2 h3
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ hc (fun P => ?_) 1 (fun P _ => hχ.unr P) x ⟨h1, h2, h3⟩
      ⟨finPart D (x : AE D) - 1, sub_mem h2 (one_mem_intAE_twisted_operators D), by rw [one_smul]⟩
    intro y hy _
    exact hχ.unr P y hy
  ·
    unfold ResEta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome at hμ hμc ⊢
    refine ⟨hμ.1, fun η hη a => ?_⟩
    have e1 : μ (idF D a) = η a ^ n := hμ.2 η hη a
    have e2 : (μ * c⁻¹) (idF D a) = η a ^ m := hμc.2 η hη a
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1] at e2
    have hs : η a ^ 2 = 1 := isEta_sq D η hη a
    have hi : (η a ^ m)⁻¹ = η a ^ m := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, hs, one_pow]
    have hc' : c (idF D a) = η a ^ n * (η a ^ m)⁻¹ := by
      rw [← e2, mul_inv_rev, inv_inv, mul_comm (c _), mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hodd
    show c (idF D a) = η a ^ 1
    rw [pow_one, hc', hi, ← pow_add, hk, pow_succ, pow_mul, hs, one_pow, one_mul]

end GlobalTheory.EtaTildeOddParity
