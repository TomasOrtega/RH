import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.DiffCoprimeP

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h` using `GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)`. Establish `key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F))`. Introduce `x`. Use `set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα`. Establish `hαv : α v = x` using `GlobalTheory.AdelicU.evalV_singleFin_self v x`.

Establish `hαw : ∀ w, w ≠ v → α w = 0` using `fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x`. Establish `k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1`. Prove the components needed by the constructor for the conclusion. Introduce `H β hβ`. Establish `e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v)`.

Apply `GlobalTheory.AdelicU.af_ext` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]`.

Express the relevant statement in the definitionally equal form `β u * x = x * β u`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]`. Rewrite using `[e]`. Conclude with `H _ (hβ v)`.

Introduce `H y hy`. Establish `e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y)`. Rewrite using `[hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]`. Use `H (GlobalTheory.AdelicU.singleFin v y) (fun w => by` as an intermediate fact. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self]`. Conclude with `hy`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _`.

Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne hw]`. Conclude with `zero_mem _)`. Rewrite `this` using `[e]`. Conclude with `this`. Rewrite using `[k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `H v` as an intermediate fact. Rewrite `this` using `[hαv]`. Then use the resulting hypothesis. Introduce `H w`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hαv]`. Conclude with `H`. Rewrite using `[hαw w hw, map_zero]`.

Conclude with `zero_le`. Use `set c := FractionalIdeal.count F v (codiff F) with hc`. Establish `hc0 : c ≤ 0`. Use `FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) (one_le_codiff (F := F))` as an intermediate fact. Rewrite `this` using `[FractionalIdeal.count_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hc1 : 0 ≤ c`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F v`.

Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `exp_ne_zero hπ.symm`. Use `set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx`.

Establish `hvx : Valued.v x = exp 1`. Rewrite using `[hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]`. Establish `h1 : Valued.v x ≤ exp (-c)`. Rewrite using `[hvx, exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `h2` using `(hu x).1 ((key x).2 h1)`. Rewrite `h2` using `[HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hc2 : c = 0` using `le_antisymm hc0 hc1`. Introduce `hle`.

Establish `hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹` using `coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)`. Establish `h0 : differentIdeal ℤ (𝓞 F) ≠ 0` using `differentIdeal_ne_bot`. Establish `h1` using `FractionalIdeal.count_coe F v h0`. Rewrite `h1` using `[hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero]`. Establish `h2` using `(Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)`.

Conclude with `h2 (by exact_mod_cast h1.symm)`.
-/
theorem not_le_differentIdeal_of_psiUnr {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl F) (hu : PsiUnr ψ v) : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  classical
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)

  have key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
    intro x
    set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
    have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
    have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
    have k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
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
    rw [k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]
    constructor
    · intro H
      have := H v
      rwa [hαv] at this
    · intro H w
      by_cases hw : w = v
      · subst hw
        rw [hαv]
        exact H
      · rw [hαw w hw, map_zero]
        exact zero_le
  set c := FractionalIdeal.count F v (codiff F) with hc

  have hc0 : c ≤ 0 := by
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    omega

  have hc1 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx
    have hvx : Valued.v x = exp 1 := by
      rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]
    have h1 : Valued.v x ≤ exp (-c) := by
      rw [hvx, exp_le_exp]
      omega
    have h2 := (hu x).1 ((key x).2 h1)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp] at h2
    omega
  have hc2 : c = 0 := le_antisymm hc0 hc1
  intro hle
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero] at h1
  have h2 := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)
  exact h2 (by exact_mod_cast h1.symm)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v hv w hw`. Establish `hnF` using `not_le_differentIdeal_of_psiUnr hB.std v (hB.psiP v hv)`. Use `haveI := hB.unram`. Establish `hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)` using `inferInstance`. Establish `hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E))`.

Rewrite using `[differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E), (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]`. Establish `h0 : differentIdeal ℤ (𝓞 E) ≠ 0` using `differentIdeal_ne_bot`. Unfold `diffE`. Rewrite using `[FractionalIdeal.count_coe E w h0]`. Establish `hnd : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 E)`.

Introduce `hd`. Apply `hnF` to reduce the goal to its premises. Rewrite `hd` using `[hEq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]`. Rewrite using `[← hw]`. Conclude with `hd`.

Rewrite using `[not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hnd)]`. Both sides reduce to the same expression.
-/
theorem count_diffE_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 F) = v → FractionalIdeal.count E w (diffE E) = 0 := by
  intro F E _ _ _ _ _ σ B hB v hv w hw
  have hnF := not_le_differentIdeal_of_psiUnr hB.std v (hB.psiP v hv)
  haveI := hB.unram
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have h0 : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  unfold diffE
  rw [FractionalIdeal.count_coe E w h0]
  have hnd : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
    intro hd
    apply hnF
    rw [hEq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at hd
    rw [← hw]
    exact hd
  rw [not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hnd)]
  rfl

end GlobalTheory.DiffCoprimeP
