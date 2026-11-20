import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace EFG

/- English proof (translation)
Conclude with `(Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two`.
-/
theorem two_isPrime : (span {(2 : ℤ)}).IsPrime := by
  exact (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two

/- English proof (translation)
Rewrite using `[← Group.card_H e]`. Conclude with `Nat.card_congr { toFun := fun g => g.1.2 invFun := fun h => ⟨(1, h), rfl⟩ left_inv := fun g => by`. Take `⟨⟨g1, g2⟩, hg⟩` from `g`. Simplify using `only at hg`. Substitute `hg` using the available equality.

Both sides reduce to the same expression. Use `right_inv := fun _ => rfl }`.
-/
theorem card_trivial_first_component (e : ℕ) : Nat.card {g : GG e // g.1 = 1} = 2 ^ e := by
  rw [← Group.card_H e]
  exact Nat.card_congr
    { toFun := fun g => g.1.2
      invFun := fun h => ⟨(1, h), rfl⟩
      left_inv := fun g => by
        obtain ⟨⟨g1, g2⟩, hg⟩ := g
        simp only at hg
        subst hg
        rfl
      right_inv := fun _ => rfl }

/- English proof (translation)
Establish `hmem : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1` using `fun g => by`. Simplify using `[Psi, chD, MonoidHom.mem_ker]`. Establish `: Nat.card (Psi e) = Nat.card (ℤˣ × HGrp e)` using `Nat.card_congr { toFun := fun g => (g.1.1.1, g.1.2) invFun := fun x => ⟨((x.1, 1), x.2), (hmem _).2 rfl⟩ left_inv := fun g => by`. Take `⟨⟨⟨g1, g2⟩, g3⟩, hg⟩` from `g`. Establish `h2 : g2 = 1` using `(hmem _).1 hg`.

Substitute `h2` using the available equality. Both sides reduce to the same expression. Use `right_inv := fun _ => rfl }`. Rewrite using `[this, Nat.card_prod, Group.card_H, Nat.card_eq_fintype_card, Fintype.card_units_int]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_Psi (e : ℕ) : Nat.card (Psi e) = 2 ^ (e + 1) := by
  have hmem : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1 := fun g => by
    simp [Psi, chD, MonoidHom.mem_ker]
  have : Nat.card (Psi e) = Nat.card (ℤˣ × HGrp e) :=
    Nat.card_congr
      { toFun := fun g => (g.1.1.1, g.1.2)
        invFun := fun x => ⟨((x.1, 1), x.2), (hmem _).2 rfl⟩
        left_inv := fun g => by
          obtain ⟨⟨⟨g1, g2⟩, g3⟩, hg⟩ := g
          have h2 : g2 = 1 := (hmem _).1 hg
          subst h2
          rfl
        right_inv := fun _ => rfl }
  rw [this, Nat.card_prod, Group.card_H, Nat.card_eq_fintype_card, Fintype.card_units_int]
  ring

/- English proof (translation)
The claim follows from `Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)`.
-/
theorem coprime_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Nat.Coprime p (2 ^ (e + 2)) :=
  Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

end EFG

open EFG

/- English proof (translation)
Introduce `e q d hh L _ _ ζ a b h`. Establish `hqd` using `hh.toHypOdd`. Take `⟨hEgal, hfin, hmulE, hbijE⟩` from `hostGalois e q d hqd L ζ a b h`. Use `hEgal` as an intermediate fact. Establish `: IsGaloisGroup Gal(hostE ζ a b/ℚ) ℤ (𝓞 (hostE ζ a b))` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)`.

Use `Formalism.FrobeniusOrbits.EFG.two_isPrime` as an intermediate fact. Take `⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(2 : ℤ)}).primesOver (𝓞 (hostE ζ a b)))` from `inferInstance`. Establish `hcardG : Nat.card Gal(hostE ζ a b/ℚ) = 2 ^ (e + 2)`. Rewrite using `[IsGalois.card_aut_eq_finrank, hfin]`. Establish `hIn : Nat.card (P.inertia Gal(hostE ζ a b/ℚ)) = 2 ^ e`.

Rewrite using `[← card_trivial_first_component e]`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => ?_))` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_inertia]`. Conclude with `(hI e q d hh L ζ a b h σ).1 P`. Establish `heE : (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e`.

Rewrite using `[← card_inertia_eq_ramificationIdxIn (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P, hIn]`. Establish `hq2 : q ≠ 2` using `by have := hh.2.2.1; omega`. Establish `hd2 : d ≠ 2` using `by have := hh.2.2.2.1; omega`. Establish `hDec` using `fun σ => hD e q d hh L ζ a b h (ZMod.unitOfCoprime q (coprime_two_pow hh.1 hq2 e)) (ZMod.unitOfCoprime d (coprime_two_pow hh.2.1 hd2 e)) (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) σ`. Establish `hStab : Nat.card (MulAction.stabilizer Gal(hostE ζ a b/ℚ) P) = 2 ^ (e + 1)`.

Rewrite using `[← card_Psi e]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => (hDec σ).1 P))`. Establish `hfE : (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2`. Use `card_stabilizer_eq (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P` as an intermediate fact. Rewrite `this` using `[hStab, heE, pow_succ]`.

Conclude with `(Nat.eq_of_mul_eq_mul_left (by positivity) this).symm`. Establish `hgE : (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2`. Use `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)}) (𝓞 (hostE ζ a b)) Gal(hostE ζ a b/ℚ)` as an intermediate fact. Rewrite `this` using `[heE, hfE, hcardG, show 2 ^ (e + 2) = 2 * (2 ^ e * 2) by ring]`. Conclude with `Nat.eq_of_mul_eq_mul_right (by positivity) this`.

Establish `hcomm : IsMulCommutative Gal(hostE ζ a b/ℚ)` using `⟨⟨fun σ τ => hbijE.1 (by rw [hmulE, hmulE, mul_comm])⟩⟩`. Establish `hAb : IsAbelianGalois ℚ (hostE ζ a b)` using `{}`. Establish `hFab : IsAbelianGalois ℚ (hostF ζ a b)` using `IsAbelianGalois.tower_bot ℚ (hostF ζ a b) (hostE ζ a b)`. Establish `: IsGaloisGroup Gal(hostF ζ a b/ℚ) ℤ (𝓞 (hostF ζ a b))` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostF ζ a b)`. Take `⟨hFfin, hFmem⟩` from `hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h`.

Establish `hcardF : Nat.card Gal(hostF ζ a b/ℚ) = 2 ^ (e + 1)`. Rewrite using `[IsGalois.card_aut_eq_finrank, hFfin]`. Take `⟨-, σc, -, -, hσc, -⟩` from `ConjReal.conj_main hostGalois hostGalSpec hqd h`. Establish `hσcP : σc • P ≠ P`. Introduce `heq`.

Establish `hmem : σc ∈ MulAction.stabilizer Gal(hostE ζ a b/ℚ) P` using `heq`. Rewrite `hmem` using `[(hDec σc).1 P, hσc]`. Conclude with `(hostGroup e).2.2.1 hmem`. Establish `hfixF : ∀ x : 𝓞 (hostF ζ a b), σc • (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x) = algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x`. Introduce `x`.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `hx : (((x : hostF ζ a b) : hostE ζ a b)) ∈ hostF ζ a b` using `(x : hostF ζ a b).2`. Conclude with `((hFmem _).1.1 hx) σc hσc`. Set `PF` to `P.under (𝓞 (hostF ζ a b))`. Establish `hσcPl : (σc • P).LiesOver PF`.

Prove the components needed by the constructor for the conclusion. Use extensionality with `x`. Use `show x ∈ P.under (𝓞 (hostF ζ a b)) ↔ _`. Rewrite using `[Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_eq_iff.mpr (hfixF x).symm]`. Establish `hgF : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1`.

Establish `ht` using `ncard_primesOver_mul_ncard_primesOver (A := ℤ) (p := span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ) (𝓞 (hostE ζ a b)) Gal(hostE ζ a b/ℚ)`. Rewrite `ht` using `[hgE]`. Establish `hne : (PF.primesOver (𝓞 (hostE ζ a b))).ncard ≠ 0`. Introduce `h0; rw [h0, mul_zero] at ht; exact absurd ht (by norm_num)`. Establish `h2le : 2 ≤ (PF.primesOver (𝓞 (hostE ζ a b))).ncard`.

Establish `hsub : ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))) ⊆ PF.primesOver (𝓞 (hostE ζ a b))`. Introduce `I hI`. Break down `hI with rfl | rfl` into its components or cases. Conclude with `⟨hPp, inferInstance⟩`. Conclude with `⟨inferInstance, hσcPl⟩`.

Combine the equalities or inequalities in the displayed calculation. Establish `hF0 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≠ 0`. Introduce `h0; rw [h0, zero_mul] at ht; exact absurd ht (by norm_num)`. Establish `hF1 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≤ 1`. Assume the negation of the conclusion as `hc`.

Establish `hc'` using `not_le.mp hc`. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers. Establish `hte` using `Ideal.ramificationIdx_tower (R := ℤ) PF P`. Establish `htf` using `Ideal.inertiaDeg_tower (R := ℤ) PF P`.

Establish `heF0` using `ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)`. Establish `hfF0` using `inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)`. Establish `heE0` using `ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)`. Establish `hfE0` using `inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)`. Establish `hfundF` using `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)}) (𝓞 (hostF ζ a b)) Gal(hostF ζ a b/ℚ)`.

Rewrite `hfundF` using `[hgF, hcardF, one_mul, heF0, hfF0]`. Rewrite `hte` using `[← heE0, heE]`. Rewrite `htf` using `[← hfE0, hfE]`. Establish `hpos : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ ≠ 0`. Rewrite using `[hfundF]`.

Check the signs of the components of the expression. Establish `hprod : P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b)) = 1`. Establish `: PF.ramificationIdx ℤ * PF.inertiaDeg ℤ * 1 = PF.ramificationIdx ℤ * PF.inertiaDeg ℤ * (P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b)))`. Rewrite using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this).symm`. Establish `he1` using `Nat.eq_one_of_mul_eq_one_right hprod`. Establish `hf1` using `Nat.eq_one_of_mul_eq_one_left hprod`. Rewrite `hte` using `[he1, mul_one]`. Rewrite `htf` using `[hf1, mul_one]`.

Conclude with `⟨heE, hfE, hgE, hgF, heF0.trans hte.symm, hfF0.trans htf.symm⟩`.
-/
theorem hostEFGTwo_of (hI : HostInertia) (hD : HostDecomp) : HostEFGTwo := by
  intro e q d hh L _ _ ζ a b h
  have hqd := hh.toHypOdd
  obtain ⟨hEgal, hfin, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  have : IsGaloisGroup Gal(hostE ζ a b/ℚ) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  have := Formalism.FrobeniusOrbits.EFG.two_isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(2 : ℤ)}).primesOver (𝓞 (hostE ζ a b))) :=
    inferInstance
  have hcardG : Nat.card Gal(hostE ζ a b/ℚ) = 2 ^ (e + 2) := by
    rw [IsGalois.card_aut_eq_finrank, hfin]

  have hIn : Nat.card (P.inertia Gal(hostE ζ a b/ℚ)) = 2 ^ e := by
    rw [← card_trivial_first_component e]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => ?_))
    rw [AddSubgroup.mem_inertia]
    exact (hI e q d hh L ζ a b h σ).1 P
  have heE : (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e := by
    rw [← card_inertia_eq_ramificationIdxIn (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P, hIn]

  have hq2 : q ≠ 2 := by have := hh.2.2.1; omega
  have hd2 : d ≠ 2 := by have := hh.2.2.2.1; omega
  have hDec := fun σ => hD e q d hh L ζ a b h
    (ZMod.unitOfCoprime q (coprime_two_pow hh.1 hq2 e))
    (ZMod.unitOfCoprime d (coprime_two_pow hh.2.1 hd2 e))
    (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) σ
  have hStab : Nat.card (MulAction.stabilizer Gal(hostE ζ a b/ℚ) P) = 2 ^ (e + 1) := by
    rw [← card_Psi e]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => (hDec σ).1 P))
  have hfE : (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2 := by
    have := card_stabilizer_eq (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P
    rw [hStab, heE, pow_succ] at this
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
  have hgE : (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2 := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
      (𝓞 (hostE ζ a b)) Gal(hostE ζ a b/ℚ)
    rw [heE, hfE, hcardG, show 2 ^ (e + 2) = 2 * (2 ^ e * 2) by ring] at this
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this

  have hcomm : IsMulCommutative Gal(hostE ζ a b/ℚ) :=
    ⟨⟨fun σ τ => hbijE.1 (by rw [hmulE, hmulE, mul_comm])⟩⟩
  have hAb : IsAbelianGalois ℚ (hostE ζ a b) := {}
  have hFab : IsAbelianGalois ℚ (hostF ζ a b) :=
    IsAbelianGalois.tower_bot ℚ (hostF ζ a b) (hostE ζ a b)
  have : IsGaloisGroup Gal(hostF ζ a b/ℚ) ℤ (𝓞 (hostF ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostF ζ a b)
  obtain ⟨hFfin, hFmem⟩ :=
    hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h
  have hcardF : Nat.card Gal(hostF ζ a b/ℚ) = 2 ^ (e + 1) := by
    rw [IsGalois.card_aut_eq_finrank, hFfin]
  obtain ⟨-, σc, -, -, hσc, -⟩ := ConjReal.conj_main hostGalois hostGalSpec hqd h
  have hσcP : σc • P ≠ P := by
    intro heq
    have hmem : σc ∈ MulAction.stabilizer Gal(hostE ζ a b/ℚ) P := heq
    rw [(hDec σc).1 P, hσc] at hmem
    exact (hostGroup e).2.2.1 hmem
  have hfixF : ∀ x : 𝓞 (hostF ζ a b),
      σc • (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x) =
        algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x := by
    intro x
    apply RingOfIntegers.coe_injective
    have hx : (((x : hostF ζ a b) : hostE ζ a b)) ∈ hostF ζ a b := (x : hostF ζ a b).2
    exact ((hFmem _).1.1 hx) σc hσc
  let PF := P.under (𝓞 (hostF ζ a b))
  have hσcPl : (σc • P).LiesOver PF := by
    constructor
    ext x
    show x ∈ P.under (𝓞 (hostF ζ a b)) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_eq_iff.mpr (hfixF x).symm]
  have hgF : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1 := by
    have ht := ncard_primesOver_mul_ncard_primesOver (A := ℤ) (p := span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ) (𝓞 (hostE ζ a b))
      Gal(hostE ζ a b/ℚ)
    rw [hgE] at ht
    have hne : (PF.primesOver (𝓞 (hostE ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht; exact absurd ht (by norm_num)
    have h2le : 2 ≤ (PF.primesOver (𝓞 (hostE ζ a b))).ncard := by
      have hsub : ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))) ⊆
          PF.primesOver (𝓞 (hostE ζ a b)) := by
        intro I hI
        rcases hI with rfl | rfl
        · exact ⟨hPp, inferInstance⟩
        · exact ⟨inferInstance, hσcPl⟩
      calc 2 = ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))).ncard :=
            (Set.ncard_pair hσcP.symm).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero hne)
    have hF0 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ht; exact absurd ht (by norm_num)
    have hF1 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≤ 1 := by
      by_contra hc
      have hc' := not_le.mp hc
      nlinarith
    omega

  have hte := Ideal.ramificationIdx_tower (R := ℤ) PF P
  have htf := Ideal.inertiaDeg_tower (R := ℤ) PF P
  have heF0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have hfF0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have heE0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfE0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfundF := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
    (𝓞 (hostF ζ a b)) Gal(hostF ζ a b/ℚ)
  rw [hgF, hcardF, one_mul, heF0, hfF0] at hfundF
  rw [← heE0, heE] at hte
  rw [← hfE0, hfE] at htf
  have hpos : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ ≠ 0 := by
    rw [hfundF]; positivity
  have hprod : P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b)) = 1 := by
    have : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ * 1 = PF.ramificationIdx ℤ * PF.inertiaDeg ℤ *
        (P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b))) := by
      rw [mul_one]
      calc PF.ramificationIdx ℤ * PF.inertiaDeg ℤ = 2 ^ e * 2 := by rw [hfundF, pow_succ]
        _ = (PF.ramificationIdx ℤ * P.ramificationIdx (𝓞 (hostF ζ a b))) *
            (PF.inertiaDeg ℤ * P.inertiaDeg (𝓞 (hostF ζ a b))) := by rw [← hte, ← htf]
        _ = _ := by ring
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this).symm
  have he1 := Nat.eq_one_of_mul_eq_one_right hprod
  have hf1 := Nat.eq_one_of_mul_eq_one_left hprod
  rw [he1, mul_one] at hte
  rw [hf1, mul_one] at htf
  exact ⟨heE, hfE, hgE, hgF, heF0.trans hte.symm, hfF0.trans htf.symm⟩

end Formalism.FrobeniusOrbits
