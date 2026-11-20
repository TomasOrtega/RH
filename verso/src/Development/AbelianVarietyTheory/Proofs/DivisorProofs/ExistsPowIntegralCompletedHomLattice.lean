import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CosetOrth.LatInt

/- English proof (translation)
Establish `hb` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D`. Establish `h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `J ⟨hJ, hp⟩`. Establish `hne : J ≠ ⊥` using `fun e => hb (le_bot_iff.1 (e ▸ hJ))`.

Conclude with `GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)`. Take `⟨k, hk⟩` from `h`. Conclude with `⟨k, by rw [Nat.cast_pow]; exact hk⟩`.
-/
theorem exists_pow_mem (D : D7) : ∃ k : ℕ, (((D.host.QS * D.host.q) ^ k : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟 := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hb (le_bot_iff.1 (e ▸ hJ))
    exact GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [Nat.cast_pow]; exact hk⟩

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`. Establish `h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`. Introduce `l _`. Distinguish the cases in `h : l = j`.

Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.

Establish `h2` using `hA _ h1 i trivial`. Rewrite `h2` using `[Matrix.mulVec_single_one]`. Conclude with `h2`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `smul c x _ hx => exact Submodule.smul_mem _ c hx`.
-/
theorem homL_entry {D : D7} {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro l _
      by_cases h : l = j
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h2 := hA _ h1 i trivial
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `hB using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨a, ha, A, hA, rfl⟩` from `hB`. Apply the tactic sequence `obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)`. Establish `: (a • A) i j = c • a`.

Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c ha`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `smul c x _ hx => exact Submodule.smul_mem _ c hx`.
-/
theorem YYl_entry {D : D7} {N N' : ℕ} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    B i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)
    have : (a • A) i j = c • a := by
      rw [Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c ha
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/- English proof (translation)
Establish `hb` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D`. Establish `h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈ (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx`. Rewrite `h1` using `[Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)]`. Conclude with `(FractionalIdeal.mem_one_iff _).1 h1`.
-/
theorem mul_int {D : D7} {n : 𝓞 D.host.E} (hn : n ∈ D.host.𝔟) {x : D.host.E}
    (hx : x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = algebraMap (𝓞 D.host.E) D.host.E n * x := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈
      (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx
  rw [Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

/- English proof (translation)
Establish `e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x` using `rfl`. Rewrite using `[e, mul_left_comm, ← map_mul, ← hb]`. Use `InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w`. Express the relevant statement in the definitionally equal form `Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1`.

Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `w.valuation_le_one b`.
-/
theorem inHat_tmul {D : D7} {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (c x : D.host.E) (b : 𝓞 D.host.E)
    (hb : algebraMap (𝓞 D.host.E) D.host.E b = c * x) :
    InHat 1 (algebraMap D.host.E (FA D) c * fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) := by
  have e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x := rfl
  rw [e, mul_left_comm, ← map_mul, ← hb]
  refine InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)
  · exact GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w
  · change Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_le_one b

/- English proof (translation)
Introduce `D S T r LB hr hz`. Take `⟨k, hk⟩` from `exists_pow_mem D`. Use `⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩` and prove the remaining obligations. Use `GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1 (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce `α hα M hM`.

Establish `h1` using `GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM`. Establish `e : finPt (S` using `S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by`. Establish `: (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M`. Use extensionality with `i j`. Simplify using `[hr]`.

Unfold `finPt`. Rewrite using `[this]`. Both sides reduce to the same expression. Apply the tactic sequence `obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)`. Use `inHat_tmul hα _ _ (-b) ?_` and prove the remaining obligations.

Rewrite using `[map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.zero_apply, map_zero, mul_zero]`. Conclude with `inHat_zero _`. Introduce `x y hx hy`.

Rewrite using `[Matrix.add_apply, map_add, mul_add]`. Conclude with `hx.add hy`. Introduce `x hx`. Rewrite using `[Matrix.neg_apply, map_neg, mul_neg]`. Conclude with `hx.neg`.
-/
theorem exists_hatPt_of_mem_latO : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  intro D S T r LB hr hz
  obtain ⟨k, hk⟩ := exists_pow_mem D
  refine ⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩
  refine GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1
    (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM
    have e : finPt (S := S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by
      have : (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M := by
        ext i j
        simp [hr]
      unfold finPt
      rw [this]
      rfl
    obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)
    refine inHat_tmul hα _ _ (-b) ?_
    rw [map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.zero_apply, map_zero, mul_zero]
    exact inHat_zero _
  · intro x y hx hy
    rw [Matrix.add_apply, map_add, mul_add]
    exact hx.add hy
  · intro x hx
    rw [Matrix.neg_apply, map_neg, mul_neg]
    exact hx.neg

end GlobalTheory.CosetOrth.LatInt
