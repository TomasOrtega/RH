import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `hns` using `Formalism.IndefR.Fin.idemAt_split he`. Set `c : 𝓞 D.host.E ≃+* 𝓞 D.host.E` to `Formalism.DivisionValues.cO D.host.E`. Establish `hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)` using `fun x => rfl`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => RingOfIntegers.ext (by rw [hc, hc, star_star])`. Establish `hcF : ∀ a : 𝓞 D.host.F, c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a` using `fun a => RingOfIntegers.ext (by`.

Rewrite using `[hc]`. Conclude with `Formalism.IndefR.Eqv.star_algebraMapF D (a : D.host.F))`. Set `Q : Ideal (𝓞 D.host.E)` to `P.asIdeal.comap (c : 𝓞 D.host.E →+* 𝓞 D.host.E)`. Establish `hQp : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hQv : Q.under (𝓞 D.host.F) = P.asIdeal.under (𝓞 D.host.F)`.

Use extensionality with `a`. Use `show c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P.asIdeal`. Rewrite using `[hcF]`. Establish `hne : Q ≠ P.asIdeal`. Introduce `h`.

Apply `hns` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : c x ∈ Q` using `by show c (c x) ∈ P.asIdeal`. Rewrite using `[hcc]`. Conclude with `hx`.

Rewrite `hx'` using `[h]`. Conclude with `⟨c x, hx', hc x⟩`. Use `set p := P.asIdeal.under (𝓞 D.host.F) with hp`. Establish `hp0 : p ≠ ⊥`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`.

Conclude with `Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)`. Establish `hpP : p.IsPrime` using `Ideal.IsPrime.comap _`. Establish `hpM : p.IsMaximal` using `hpP.isMaximal hp0`. Use `haveI hl1 : P.asIdeal.LiesOver p := ⟨rfl⟩`. Use `haveI hl2 : Q.LiesOver p := ⟨hQv.symm⟩`.

Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank p (𝓞 D.host.E)`. Rewrite `hsum` using `[← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2]`. Set `P1 : p.primesOver (𝓞 D.host.E)` to `⟨P.asIdeal, P.isPrime, hl1⟩`. Set `Q1 : p.primesOver (𝓞 D.host.E)` to `⟨Q, hQp, hl2⟩`. Establish `h12 : P1 ≠ Q1` using `fun h => hne (congrArg Subtype.val h).symm`.

Establish `hpos : ∀ R : p.primesOver (𝓞 D.host.E), 1 ≤ R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)` using `fun R => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)`. Establish `hle : P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) + Q1.1.ramificationIdx (𝓞 D.host.F) * Q1.1.inertiaDeg (𝓞 D.host.F) ≤ 2`. Rewrite using `[← hsum, ← Finset.sum_pair (f := fun R : p.primesOver (𝓞 D.host.E) => R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)) h12]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Establish `h1` using `hpos P1`.

Establish `h2` using `hpos Q1`. Establish `hef : P.asIdeal.ramificationIdx (𝓞 D.host.F) * P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1`. Express the relevant statement in the definitionally equal form `P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) = 1`. Use linear arithmetic over natural numbers and integers. Establish `hf : P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1` using `Nat.eq_one_of_mul_eq_one_left hef`.

Rewrite using `[← Ideal.absNorm_pow_inertiaDeg p P.asIdeal, hf, pow_one]`.
-/
theorem absNorm_eq_under_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under (𝓞 D.host.F)) := by
  classical
  have hns := Formalism.IndefR.Fin.idemAt_split he
  let c : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.DivisionValues.cO D.host.E
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => rfl
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hc, hc, star_star])
  have hcF : ∀ a : 𝓞 D.host.F, c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a :=
    fun a => RingOfIntegers.ext (by
      rw [hc]
      exact Formalism.IndefR.Eqv.star_algebraMapF D (a : D.host.F))
  let Q : Ideal (𝓞 D.host.E) := P.asIdeal.comap (c : 𝓞 D.host.E →+* 𝓞 D.host.E)
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQv : Q.under (𝓞 D.host.F) = P.asIdeal.under (𝓞 D.host.F) := by
    ext a
    show c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P.asIdeal
    rw [hcF]
  have hne : Q ≠ P.asIdeal := by
    intro h
    apply hns
    intro x hx
    have hx' : c x ∈ Q := by
      show c (c x) ∈ P.asIdeal
      rw [hcc]; exact hx
    rw [h] at hx'
    exact ⟨c x, hx', hc x⟩
  set p := P.asIdeal.under (𝓞 D.host.F) with hp
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  have hpP : p.IsPrime := Ideal.IsPrime.comap _
  have hpM : p.IsMaximal := hpP.isMaximal hp0
  haveI hl1 : P.asIdeal.LiesOver p := ⟨rfl⟩
  haveI hl2 : Q.LiesOver p := ⟨hQv.symm⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 D.host.E)
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2] at hsum
  let P1 : p.primesOver (𝓞 D.host.E) := ⟨P.asIdeal, P.isPrime, hl1⟩
  let Q1 : p.primesOver (𝓞 D.host.E) := ⟨Q, hQp, hl2⟩
  have h12 : P1 ≠ Q1 := fun h => hne (congrArg Subtype.val h).symm
  have hpos : ∀ R : p.primesOver (𝓞 D.host.E),
      1 ≤ R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F) := fun R =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) +
      Q1.1.ramificationIdx (𝓞 D.host.F) * Q1.1.inertiaDeg (𝓞 D.host.F) ≤ 2 := by
    rw [← hsum, ← Finset.sum_pair (f := fun R : p.primesOver (𝓞 D.host.E) =>
      R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)) h12]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h1 := hpos P1
  have h2 := hpos Q1
  have hef : P.asIdeal.ramificationIdx (𝓞 D.host.F) * P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := by
    change P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) = 1
    omega
  have hf : P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := Nat.eq_one_of_mul_eq_one_left hef
  rw [← Ideal.absNorm_pow_inertiaDeg p P.asIdeal, hf, pow_one]

variable {T : Type} {L : LevCh D T}

open Classical in

/- English proof (translation)
Establish `hv' : v ∈ insert P.v0 (S1 D)`. Break down `P.mem_S0_of_sum_eq.1 hv with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `Finset.mem_insert_self _ _`. Conclude with `Finset.mem_insert_of_mem h`.

Take `⟨e, he⟩` from `P.w_split v hv'`. Establish `hu : (P.w v).asIdeal.under (𝓞 D.host.F) = v.asIdeal`. Rewrite using `[← HeightOneSpectrum.under_asIdeal, P.under_w hv]`. Rewrite using `[absNorm_eq_under_of_idemAt he, hu]`.
-/
theorem absNorm_w (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    Ideal.absNorm (P.w v).asIdeal = Ideal.absNorm v.asIdeal := by
  have hv' : v ∈ insert P.v0 (S1 D) := by
    rcases P.mem_S0_of_sum_eq.1 hv with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  obtain ⟨e, he⟩ := P.w_split v hv'
  have hu : (P.w v).asIdeal.under (𝓞 D.host.F) = v.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, P.under_w hv]
  rw [absNorm_eq_under_of_idemAt he, hu]

/- English proof (translation)
Introduce `D T L P`. Unfold `GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[map_pow, absNorm_w P hv]`.
-/
theorem absNorm_condE : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  intro D T L P
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [map_pow, absNorm_w P hv]

end GlobalTheory.FunObj.NormLevel

end
