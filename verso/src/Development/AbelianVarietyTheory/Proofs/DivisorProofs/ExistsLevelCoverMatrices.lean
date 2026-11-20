import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObject
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegLevCalc
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SiegLevCover

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `g n ℓ j F hg hn hodd hℓ hℓn hj`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `hd0 : (ℓ ^ j) ^ 2 ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)`. Establish `hN0 : n * (ℓ ^ j) ^ 2 ≠ 0` using `Nat.mul_ne_zero hn0 hd0`. Establish `hnN : n ∣ n * (ℓ ^ j) ^ 2` using `dvd_mul_right n _`.

Establish `hNn : n * (ℓ ^ j) ^ 2 / n = (ℓ ^ j) ^ 2` using `Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)`. Establish `hℓodd : Odd ℓ` using `Odd.of_dvd_nat hodd hℓn`. Establish `hNodd : Odd (n * (ℓ ^ j) ^ 2)` using `hodd.mul (hℓodd.pow.pow)`. Establish `hN3 : 3 ≤ n * (ℓ ^ j) ^ 2` using `le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0))`. Establish `hpow : ∃ a, n * (ℓ ^ j) ^ 2 ∣ n ^ a` using `⟨2 * j + 1, by`.

Rewrite using `[pow_succ' n (2 * j)]`. Use `mul_dvd_mul_left n ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm j 2]`. Conclude with `pow_dvd_pow_of_dvd hℓn _⟩`. Take `⟨κ, hinj, hζ, hfes⟩` from `GlobalTheory.SiegelTor.exists_inclusion_cycAway n (n * (ℓ ^ j) ^ 2) hN0 hnN`.

Take `⟨hfin, het, hsurj⟩` from `hfes hpow`. Take `⟨F'⟩` from `GlobalTheory.SiegelTor.exists_sFam_cycAway g (n * (ℓ ^ j) ^ 2) hg hN3 hNodd`. Take `⟨Q⟩` from `GlobalTheory.SiegLev.nonempty_sQuot g n _ F' κ hn hNodd hnN hζ hfin het`. Set `Fq : SFam g n (zetaAway n)` to `{ X := Q.X s := Q.s smooth := Q.smooth qproj := Q.qproj univ := Q.univ princ := Q.princ rep := fun S s' c hred hdense hpr => GlobalTheory.quotFam_represents g n _ F' κ Q hn hNodd hnN hinj hζ hfin het hsurj S s' c hred hdense hpr inj := fun R _ _ x y s' c hs h₁ h₂ => GlobalTheory. …`. Take `⟨e, he, hpb⟩` from `SFam.exists_iso Fq F`.

Take `⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hbase, hrel, hfree, htrans⟩` from `GlobalTheory.SiegAct.siegel_group_action g n _ F' κ hn hNodd hnN hζ`. Rewrite `hζ`, `hrel`, `htrans` using `[hNn]`. Establish `hlow : SRel F'.univ Q.univ ((ℓ ^ j) ^ 2) 1 Q.π`. Use `Q.low` as an intermediate fact. Rewrite `this` using `[hNn]`. Then use the resulting hypothesis.

Set `q : F'.X ⟶ F.X` to `Q.π ≫ e.hom`. Establish `hqs : q ≫ F.s = F'.s ≫ spMap κ` using `by show (Q.π ≫ e.hom) ≫ F.s = _`. Rewrite using `[Category.assoc, he]`. Conclude with `Q.base`. Establish `hq : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q` using `sRel_comp ((sRel_one_one_iff Q.univ F.univ e.hom).2 hpb) hlow`.

Use `haveI := Q.fin`. Use `haveI := Q.etale`. Use `haveI := Q.onto`. Establish `hinv : ∀ a, ρ a ≫ q = q`. Introduce `a`.

Take `⟨c, hc⟩` from `(GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X F'.X F.s (q ≫ F.s) q F.univ rfl).1`. Establish `m1 : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) (𝟙 F'.X)` using `SiegLevCalc.sRel_cancel (f' := 𝟙 F'.X) hq (by rw [Category.id_comp]; exact (sRel_one_one_iff _ _ _).2 hc)`. Establish `m2 : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 (ρ a ≫ q)` using `sRel_comp hq ⟨ν a, hrel a⟩`. Establish `m3` using `sRel_comp m2 m1`. Rewrite `m3` using `[Category.id_comp, sRel_one_one_iff]`.

Use `SFam.hom_ext F c _ _ ?_ m3 hc` and prove the remaining obligations. Rewrite using `[Category.assoc, hqs]`. Conclude with `hbase a`. Use `⟨κ, F', q, ⟨hinj, hζ, hfin, het, hsurj⟩, ⟨hqs, inferInstance, inferInstance, inferInstance, hq⟩, Ga, inferInstance, inferInstance, ρ, ν, h1, hmul, hν1, hνmul, hrel, hinv, ?_⟩` and prove the remaining obligations. Introduce `K _ _ x y hxy`.

Take `⟨c, hc⟩` from `(GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp K) F.s ((x ≫ q) ≫ F.s) (x ≫ q) F.univ rfl).1`. Establish `mx : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) x` using `SiegLevCalc.sRel_cancel hq ((sRel_one_one_iff _ _ _).2 hc)`. Establish `my : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) y` using `SiegLevCalc.sRel_cancel hq (by rw [← hxy]; exact (sRel_one_one_iff _ _ _).2 hc)`. Establish `hs : x ≫ F'.s ≫ spMap κ = y ≫ F'.s ≫ spMap κ`. Rewrite using `[← hqs, ← Category.assoc, hxy, Category.assoc]`.

Take `⟨a, ha⟩` from `htrans K x y _ c hs mx my`. Use `⟨a, ha, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hy : y ≫ ρ (a⁻¹ * b) = y`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(inv_mul_eq_one.1 (hfree K y _ hy)).symm`.
-/
theorem exists_levelCover : ∀ (g n ℓ j : ℕ) (F : SFam g n (zetaAway n)), 1 ≤ g → 3 ≤ n → Odd n → ℓ.Prime → ℓ ∣ n →
    1 ≤ j →
    ∃ (κ : cycAway n →+* cycAway (n * (ℓ ^ j) ^ 2)) (F' : SFam g (n * (ℓ ^ j) ^ 2) (zetaAway (n * (ℓ ^ j) ^ 2)))
      (q : F'.X ⟶ F.X),
      (Function.Injective κ ∧ κ (zetaAway n) = zetaAway (n * (ℓ ^ j) ^ 2) ^ ((ℓ ^ j) ^ 2) ∧ IsFinite (spMap κ) ∧
        Etale (spMap κ) ∧ Surjective (spMap κ)) ∧
      (q ≫ F.s = F'.s ≫ spMap κ ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧ SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q) ∧
      ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ → (F'.X ⟶ F'.X)) (ν : Γ → (F'.univ.A.left ⟶ F'.univ.A.left)),
        ρ 1 = 𝟙 _ ∧ (∀ a b, ρ (a * b) = ρ a ≫ ρ b) ∧ ν 1 = 𝟙 _ ∧ (∀ a b, ν (a * b) = ν a ≫ ν b) ∧
        (∀ a, SRelBy F'.univ F'.univ ((ℓ ^ j) ^ 2) ((ℓ ^ j) ^ 2) (ρ a) (ν a)) ∧ (∀ a, ρ a ≫ q = q) ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ F'.X), x ≫ q = y ≫ q → ∃! a, x ≫ ρ a = y := by
  intro g n ℓ j F hg hn hodd hℓ hℓn hj
  have hn0 : n ≠ 0 := by omega
  have hd0 : (ℓ ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have hN0 : n * (ℓ ^ j) ^ 2 ≠ 0 := Nat.mul_ne_zero hn0 hd0
  have hnN : n ∣ n * (ℓ ^ j) ^ 2 := dvd_mul_right n _
  have hNn : n * (ℓ ^ j) ^ 2 / n = (ℓ ^ j) ^ 2 := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hodd hℓn
  have hNodd : Odd (n * (ℓ ^ j) ^ 2) := hodd.mul (hℓodd.pow.pow)
  have hN3 : 3 ≤ n * (ℓ ^ j) ^ 2 := le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0))
  have hpow : ∃ a, n * (ℓ ^ j) ^ 2 ∣ n ^ a := ⟨2 * j + 1, by
    rw [pow_succ' n (2 * j)]
    refine mul_dvd_mul_left n ?_
    rw [← pow_mul, mul_comm j 2]
    exact pow_dvd_pow_of_dvd hℓn _⟩
  obtain ⟨κ, hinj, hζ, hfes⟩ := GlobalTheory.SiegelTor.exists_inclusion_cycAway n (n * (ℓ ^ j) ^ 2) hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨F'⟩ := GlobalTheory.SiegelTor.exists_sFam_cycAway g (n * (ℓ ^ j) ^ 2) hg hN3 hNodd
  obtain ⟨Q⟩ := GlobalTheory.SiegLev.nonempty_sQuot g n _ F' κ hn hNodd hnN hζ hfin het
  let Fq : SFam g n (zetaAway n) :=
    { X := Q.X
      s := Q.s
      smooth := Q.smooth
      qproj := Q.qproj
      univ := Q.univ
      princ := Q.princ
      rep := fun S s' c hred hdense hpr =>
        GlobalTheory.quotFam_represents g n _ F' κ Q hn hNodd hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
      inj := fun R _ _ x y s' c hs h₁ h₂ =>
        GlobalTheory.SiegLev.SQuot.eq_of_siegPB g n _ _ _ (zetaAway n) (zetaAway _) F' κ Q R x y s' c hs h₁ h₂ }
  obtain ⟨e, he, hpb⟩ := SFam.exists_iso Fq F
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hbase, hrel, hfree, htrans⟩ :=
    GlobalTheory.SiegAct.siegel_group_action g n _ F' κ hn hNodd hnN hζ
  rw [hNn] at hζ hrel htrans
  have hlow : SRel F'.univ Q.univ ((ℓ ^ j) ^ 2) 1 Q.π := by
    have := Q.low
    rwa [hNn] at this
  let q : F'.X ⟶ F.X := Q.π ≫ e.hom
  have hqs : q ≫ F.s = F'.s ≫ spMap κ := by
    show (Q.π ≫ e.hom) ≫ F.s = _
    rw [Category.assoc, he]
    exact Q.base
  have hq : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q :=
    sRel_comp ((sRel_one_one_iff Q.univ F.univ e.hom).2 hpb) hlow
  haveI := Q.fin
  haveI := Q.etale
  haveI := Q.onto
  have hinv : ∀ a, ρ a ≫ q = q := by
    intro a
    obtain ⟨c, hc⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X F'.X F.s (q ≫ F.s) q F.univ rfl).1
    have m1 : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) (𝟙 F'.X) :=
      SiegLevCalc.sRel_cancel (f' := 𝟙 F'.X) hq (by rw [Category.id_comp]; exact (sRel_one_one_iff _ _ _).2 hc)
    have m2 : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 (ρ a ≫ q) := sRel_comp hq ⟨ν a, hrel a⟩
    have m3 := sRel_comp m2 m1
    rw [Category.id_comp, sRel_one_one_iff] at m3
    refine SFam.hom_ext F c _ _ ?_ m3 hc
    rw [Category.assoc, hqs]
    exact hbase a
  refine ⟨κ, F', q, ⟨hinj, hζ, hfin, het, hsurj⟩, ⟨hqs, inferInstance, inferInstance, inferInstance, hq⟩,
    Ga, inferInstance, inferInstance, ρ, ν, h1, hmul, hν1, hνmul, hrel, hinv, ?_⟩
  intro K _ _ x y hxy
  obtain ⟨c, hc⟩ :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp K) F.s ((x ≫ q) ≫ F.s) (x ≫ q) F.univ rfl).1
  have mx : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) x := SiegLevCalc.sRel_cancel hq ((sRel_one_one_iff _ _ _).2 hc)
  have my : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) y := SiegLevCalc.sRel_cancel hq (by rw [← hxy]; exact (sRel_one_one_iff _ _ _).2 hc)
  have hs : x ≫ F'.s ≫ spMap κ = y ≫ F'.s ≫ spMap κ := by
    rw [← hqs, ← Category.assoc, hxy, Category.assoc]
  obtain ⟨a, ha⟩ := htrans K x y _ c hs mx my
  refine ⟨a, ha, fun b hb => ?_⟩
  have hy : y ≫ ρ (a⁻¹ * b) = y := by
    calc y ≫ ρ (a⁻¹ * b) = x ≫ ρ (a * (a⁻¹ * b)) := by rw [hmul a, ← ha, Category.assoc]
      _ = y := by rw [mul_inv_cancel_left, hb]
  exact (inv_mul_eq_one.1 (hfree K y _ hy)).symm

end GlobalTheory.SiegLevCover
