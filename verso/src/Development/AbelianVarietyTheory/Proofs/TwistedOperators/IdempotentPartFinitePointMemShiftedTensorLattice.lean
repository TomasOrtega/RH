import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

/- English proof (translation)
Introduce `D S T C Pg Q e he Lv hLv y hy`. Establish `hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤` using `Ideal.isCoprime_iff_sup_eq.1 Lv.cop`. Establish `h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪` using `by rw [hm]; exact Submodule.mem_top`. Take `⟨t, ht, c, hc, htc⟩` from `Submodule.mem_sup.1 h1`. Establish `hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal`.

Introduce `PP hPP x hx`. Establish `h2` using `mem_of_mem_conjI hx`. Rewrite `h2` using `[hLv, liftI]`. Establish `h3 : stO x ∈ conjI PP.asIdeal` using `Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal) hPP (Ideal.prod_le_inf h2)`. Establish `h4` using `mem_of_mem_conjI h3`.

Establish `h5 : stO (stO x) = x` using `RingOfIntegers.ext (star_star _)`. Rewrite `h4` using `[h5]`. Then use the resulting hypothesis. Establish `htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal`. Introduce `PP hPP htm`. Establish `h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal` using `htc ▸ add_mem htm (hcP PP hPP hc)`.

Conclude with `PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)`. Establish `hPQ : (Pg ∪ Q).Nonempty`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Apply `Lv.proper` to reduce the goal to its premises.

Rewrite using `[hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]`. Establish `ht0 : (t : D.host.E) ≠ 0`. Take `⟨PP, hPP⟩` from `hPQ`. Introduce `h`. Apply `htP PP hPP` to reduce the goal to its premises.

Establish `: t = 0` using `RingOfIntegers.ext (h.trans rfl)`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ` using `Submodule.smul_le_right`. Establish `htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ`.

Introduce `v hv s hs`. Establish `hv' : t • v ∈ Lv.𝔪 • C.X.Λ` using `Submodule.smul_mem_smul ht (hsub hv)`. Conclude with `Submodule.smul_mem _ s hv'`. Establish `hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)` using `smul_mem_tens t htL hy`. Establish `h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))`.

Rewrite using `[GlobalTheory.Ker.SignVac.finW_eq]`. Conclude with `GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty`. Establish `hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D` using `GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP`. Establish `hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ), (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)` using `fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz`. Establish `e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y)`.

Establish `e2 : finW S T ((t : D.host.E) • y) = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y`. Rewrite using `[GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, Matrix.transpose_smul]`. Establish `e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y`. Rewrite using `[GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]`. Rewrite using `[e2, smul_smul, mul_assoc]`.

Establish `e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)`. Express the relevant statement in the definitionally equal form `((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]`. Rewrite using `[e4, mul_smul, ← e3, partAt_eq_smul]`. Rewrite using `[e1]`.

Conclude with `smul_mem_hatA_of_int hA' hz1 h0`.
-/
theorem partAt_finW_mem_hatA_sh : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  intro D S T C Pg Q e he Lv hLv y hy

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hPQ : (Pg ∪ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Lv.proper
    rw [hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPQ
    intro h
    apply htP PP hPP
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _

  have hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ := by
    intro v hv s hs
    have hv' : t • v ∈ Lv.𝔪 • C.X.Λ := Submodule.smul_mem_smul ht (hsub hv)
    exact Submodule.smul_mem _ s hv'
  have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) := smul_mem_tens t htL hy
  have h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]
    exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty

  have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
    GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
  have hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ),
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) :=
    fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
    have e2 : finW S T ((t : D.host.E) • y) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
        Matrix.transpose_smul]
    have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
    rw [e2, smul_smul, mul_assoc]
    have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
    rw [e4, mul_smul, ← e3, partAt_eq_smul]
  rw [e1]
  exact smul_mem_hatA_of_int hA' hz1 h0

end GlobalTheory.LiftLevel

end
