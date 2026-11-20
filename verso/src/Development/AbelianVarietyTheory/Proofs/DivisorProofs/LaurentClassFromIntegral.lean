import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.LiftWitness

/- English proof (translation)
Simplify using `[laurentMap]`.
-/
theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_id (L : Type) [CommRing L] : spMap (RingHom.id L) = 𝟙 _ := by
  simp [spMap]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `p p' h`. Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`. Simplify using `only [RingHom.prod_apply] at h1 h2`.

Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `n`. Simplify `congrArg (fun r => r.coeff n) h1` using `[laurentMap_coeff]`. Simplify `congrArg (fun r => r.coeff n) h2` using `[laurentMap_coeff]`. Introduce and unpack `⟨f, g⟩`.

Use `⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.prod_apply, Prod.mk.injEq]`. Apply the tactic sequence `constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])`.
-/
theorem laurentProd_bijective (B C : Type) [CommRing B] [CommRing C] : Function.Bijective
    ((laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.coeff_injective
    ext n
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h1
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h2
  · rintro ⟨f, g⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])

open GlobalTheory.EtC.GmPhiNat in

/- English proof (translation)
Set `e` to `(laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))`. Set `E` to `RingEquiv.ofBijective e (laurentProd_bijective B C)`. Establish `hinv : E.symm.toRingHom.comp e = RingHom.id _` using `RingHom.ext fun x => E.symm_apply_apply x`. Establish `hw : pull _ (spMap e) _ n z = 0`. Apply `(GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1` to reduce the goal to its premises.

Simplify using `only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]`. Conclude with `Prod.ext h1 h2`. Use `pull_spMap_comp q e E.symm.toRingHom n i z` as an intermediate fact. Rewrite `this` using `[hinv, spMap_id, pull_id, hw, map_zero]`. Conclude with `this`.
-/
theorem eq_zero_of_pull_laurent_fst_snd (q : ℕ) (B C : Type) [CommRing B] [CommRing C] (n i : ℤ)
    (z : Ht q (sp (LaurentPolynomial (B × C))) n i)
    (h1 : pull _ (spMap (laurentMap (RingHom.fst B C))) _ n z = 0)
    (h2 : pull _ (spMap (laurentMap (RingHom.snd B C))) _ n z = 0) : z = 0 := by
  let e := (laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))
  let E := RingEquiv.ofBijective e (laurentProd_bijective B C)
  have hinv : E.symm.toRingHom.comp e = RingHom.id _ :=
    RingHom.ext fun x => E.symm_apply_apply x
  have hw : pull _ (spMap e) _ n z = 0 := by
    apply (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1
    simp only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]
    exact Prod.ext h1 h2
  have := pull_spMap_comp q e E.symm.toRingHom n i z
  rw [hinv, spMap_id, pull_id, hw, map_zero] at this
  exact this

/- English proof (translation)
Introduce `y`. Take `⟨b, hb⟩` from `hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)`. Take `⟨c, hc⟩` from `hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)`. Take `⟨a, ha⟩` from `(GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)`. Simplify using `only [Prod.mk.injEq] at ha`.

Use `⟨a, (sub_eq_zero.mp ?_).symm⟩` and prove the remaining obligations. Apply `eq_zero_of_pull_laurent_fst_snd q B C 1 i` to reduce the goal to its premises. Rewrite using `[map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]`. Rewrite using `[map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]`.
-/
theorem surj_prod (q : ℕ) [NeZero q] (B C : Type) [CommRing B] [CommRing C] (hq : IsUnit (q : B × C)) (i : ℤ)
    (hB : Function.Surjective (gmPhi q B i)) (hC : Function.Surjective (gmPhi q C i)) :
    Function.Surjective (gmPhi q (B × C) i) := by
  intro y
  obtain ⟨b, hb⟩ := hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)
  obtain ⟨c, hc⟩ := hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)
  obtain ⟨a, ha⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)
  simp only [Prod.mk.injEq] at ha
  refine ⟨a, (sub_eq_zero.mp ?_).symm⟩
  apply eq_zero_of_pull_laurent_fst_snd q B C 1 i
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]

/- English proof (translation)
Set `D` to `A ⧸ p`. Set `Ω` to `AlgebraicClosure (FractionRing D)`. Set `T` to `integralClosure D Ω`. Use `letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra`. Establish `hint : Algebra.IsIntegral A T`.

Establish `h1 : (Ideal.Quotient.mk p).IsIntegral` using `RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h2 : (algebraMap D T).IsIntegral` using `fun x => Algebra.IsIntegral.isIntegral (R := D) x`. Conclude with `⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩`. Establish `hloc : IsLocalRing T` using `GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T`. Establish `hqT : IsUnit (q : T)` using `by simpa using hq.map (algebraMap A T)`.

Use `⟨T, inferInstance, inferInstance, hint, fun a ha => ?_, (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩` and prove the remaining obligations. Establish `hinjΩ : Function.Injective (algebraMap D Ω)`. Rewrite using `[IsScalarTower.algebraMap_eq D (FractionRing D) Ω]`. Conclude with `(algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))`. Establish `hinj : Function.Injective (algebraMap D T)`.

Introduce `x y h`. Conclude with `hinjΩ (congrArg Subtype.val h)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `ha`.
-/
theorem exists_factor (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  let D := A ⧸ p
  let Ω := AlgebraicClosure (FractionRing D)
  let T := integralClosure D Ω
  letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra
  have hint : Algebra.IsIntegral A T := by
    have h1 : (Ideal.Quotient.mk p).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : (algebraMap D T).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := D) x
    exact ⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩
  have hloc : IsLocalRing T := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T
  have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
  refine ⟨T, inferInstance, inferInstance, hint, fun a ha => ?_,
    (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩
  have hinjΩ : Function.Injective (algebraMap D Ω) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) Ω]
    exact (algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))
  have hinj : Function.Injective (algebraMap D T) := by
    intro x y h
    exact hinjΩ (congrArg Subtype.val h)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact ha

/- English proof (translation)
Proceed by induction on `hne using Finset.Nonempty.cons_induction with`. Consider the case `singleton p`. Use `hS p (Finset.mem_singleton_self p)` as an intermediate fact. Take `⟨B, _, _, hint, hker, hsurj⟩` from `exists_factor q A hq i p`. Conclude with `⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by`.

Rewrite `hr` using `[Finset.mem_singleton]`. Substitute `hr` using the available equality. Conclude with `hker a ha, hsurj⟩`. Consider the case `cons p S hp hSne ih`. Use `hS p (Finset.mem_cons_self p S)` as an intermediate fact.

Take `⟨B, _, _, hintB, hkerB, hsurjB⟩` from `ih fun r hr => hS r (Finset.mem_cons_of_mem hr)`. Take `⟨C, _, _, hintC, hkerC, hsurjC⟩` from `exists_factor q A hq i p`. Establish `hqBC : IsUnit (q : B × C)` using `by simpa using hq.map (algebraMap A (B × C))`. Use `⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_, surj_prod q B C hqBC i hsurjB hsurjC⟩` and prove the remaining obligations. Rewrite `ha` using `[Prod.algebraMap_apply, Prod.mk_eq_zero]`.

Break down `Finset.mem_cons.1 hr with rfl | hr` into its components or cases. Conclude with `hkerC a ha.2`. Conclude with `hkerB a ha.1 r hr`.
-/
theorem exists_witness (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (S : Finset (Ideal A)) (hS : ∀ p ∈ S, p.IsPrime) (hne : S.Nonempty) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → ∀ p ∈ S, a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton p =>
    have := hS p (Finset.mem_singleton_self p)
    obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_factor q A hq i p
    exact ⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by
      rw [Finset.mem_singleton] at hr; subst hr; exact hker a ha, hsurj⟩
  | cons p S hp hSne ih =>
    have := hS p (Finset.mem_cons_self p S)
    obtain ⟨B, _, _, hintB, hkerB, hsurjB⟩ := ih fun r hr => hS r (Finset.mem_cons_of_mem hr)
    obtain ⟨C, _, _, hintC, hkerC, hsurjC⟩ := exists_factor q A hq i p
    have hqBC : IsUnit (q : B × C) := by simpa using hq.map (algebraMap A (B × C))
    refine ⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_,
      surj_prod q B C hqBC i hsurjB hsurjC⟩
    rw [Prod.algebraMap_apply, Prod.mk_eq_zero] at ha
    rcases Finset.mem_cons.1 hr with rfl | hr
    · exact hkerC a ha.2
    · exact hkerB a ha.1 r hr

/- English proof (translation)
Introduce `q _ A _ _ hSH hq i x`. Take `⟨hH, -⟩` from `hSH`. Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing A`. Establish `hne : hfin.toFinset.Nonempty`. Take `⟨p, hp, -⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le`.

Conclude with `⟨p, hfin.mem_toFinset.2 hp⟩`. Take `⟨B, _, _, hint, hker, hsurj⟩` from `exists_witness q A hq i hfin.toFinset (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne`. Take `⟨a', ha'⟩` from `hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)`. Use `⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩` and prove the remaining obligations. Rewrite `ha` using `[RingHom.mem_ker]`.

Establish `: a ∈ (⊥ : Ideal A).radical`. Rewrite using `[← Ideal.sInf_minimalPrimes]`. Conclude with `Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)`. Conclude with `this`.
-/
theorem lift_witness : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
      ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  intro q _ A _ _ hSH hq i x
  obtain ⟨hH, -⟩ := hSH
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
    exact ⟨p, hfin.mem_toFinset.2 hp⟩
  obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_witness q A hq i hfin.toFinset
    (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne
  obtain ⟨a', ha'⟩ := hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)
  refine ⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩
  rw [RingHom.mem_ker] at ha
  have : a ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)
  exact this
end GlobalTheory.EtC.LiftWitness
