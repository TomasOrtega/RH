import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Introduce `x`. Establish `hc` using `GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))`. Use `set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα`. Establish `hαv : α v = x` using `GlobalTheory.AdelicU.evalV_singleFin_self v x`. Establish `hαw : ∀ w, w ≠ v → α w = 0` using `fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x`.

Establish `h` using `GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α`. Establish `key : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1`. Prove the components needed by the constructor for the conclusion. Introduce `H β hβ`. Establish `e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v)`.

Apply `GlobalTheory.AdelicU.af_ext` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]`.

Express the relevant statement in the definitionally equal form `β u * x = x * β u`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]`. Rewrite using `[e]`. Conclude with `H _ (hβ v)`.

Introduce `H y hy`. Establish `e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y)`. Rewrite using `[hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]`. Use `H (GlobalTheory.AdelicU.singleFin v y) (fun w => by` as an intermediate fact. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self]`. Conclude with `hy`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _`.

Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne hw]`. Conclude with `zero_mem _)`. Rewrite `this` using `[e]`. Conclude with `this`. Rewrite using `[key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `H v` as an intermediate fact. Rewrite `this` using `[hc, neg_zero, exp_zero, hαv]`. Then use the resulting hypothesis. Introduce `H w`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hc, neg_zero, exp_zero, hαv]`. Conclude with `H`. Rewrite using `[hαw w hw, map_zero]`.

Conclude with `zero_le`.
-/
theorem psiUnr_of_not_le {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end PositivityTheory.Mix
