import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallAevalLineVanishingIdealIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

set_option autoImplicit false

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ChowHt

section Mult

variable {R : Type} [CommRing R]

def localLength (J Q : Ideal R) [Q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))

/- English proof (translation)
Establish `hrad` using `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime Q) Q J h`. Rewrite `hrad` using `[Localization.AtPrime.map_eq_maximalIdeal]`. Establish `hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈ (J.map (algebraMap R (Localization.AtPrime Q))).minimalPrimes`. Rewrite using `[← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]`. Both sides reduce to the same expression.

Use `haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin`. Rewrite using `[localLength, Module.length_eq_of_surjective (R := Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q))) Ideal.Quotient.mk_surjective]`. Conclude with `Module.length_ne_top`.
-/
theorem localLength_ne_top [IsNoetherianRing R] {J Q : Ideal R} [Q.IsPrime]
    (h : Q ∈ J.minimalPrimes) : localLength J Q ≠ ⊤ := by
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime Q) Q J h
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (J.map (algebraMap R (Localization.AtPrime Q))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  rw [localLength, Module.length_eq_of_surjective
    (R := Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

/- English proof (translation)
Rewrite using `[localLength, Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]`. Use `ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top ?_` and prove the remaining obligations. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.map_mono h`.
-/
theorem localLength_ne_zero {J Q : Ideal R} [Q.IsPrime] (h : J ≤ Q) : localLength J Q ≠ 0 := by
  rw [localLength, Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono h

/- English proof (translation)
Rewrite using `[localLength, Localization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal _`.
-/
theorem localLength_self (Q : Ideal R) [Q.IsPrime] : localLength Q Q = 1 := by
  rw [localLength, Localization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _

end Mult

variable {k : Type} [Field k] {N : ℕ}

open Classical in

def projCycle (J : Ideal (MvPolynomial (Fin N) k)) : Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun Q => if h : Q ∈ projComponents J then
      (haveI : Q.IsPrime := h.1.1.1; localLength J Q).toNat else 0)
    ((finite_projComponents J).subset fun Q hQ => by
      by_contra h
      exact hQ (dif_neg h))

/- English proof (translation)
Rewrite using `[projCycle, Finsupp.ofSupportFinite_coe]`. Simplify using `only [dif_pos h]`. Conclude with `ENat.coe_toNat (localLength_ne_top h.1)`.
-/
theorem cast_projCycle_apply {J Q : Ideal (MvPolynomial (Fin N) k)} [Q.IsPrime]
    (h : Q ∈ projComponents J) : (projCycle J Q : ℕ∞) = localLength J Q := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  simp only [dif_pos h]
  exact ENat.coe_toNat (localLength_ne_top h.1)

/- English proof (translation)
Rewrite using `[projCycle, Finsupp.ofSupportFinite_coe]`. Conclude with `dif_neg h`.
-/
theorem projCycle_apply_of_notMem {J Q : Ideal (MvPolynomial (Fin N) k)}
    (h : Q ∉ projComponents J) : projCycle J Q = 0 := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  exact dif_neg h

/- English proof (translation)
Rewrite using `[Finsupp.mem_support_iff]`. Use `⟨fun h => by_contra fun h' => h (projCycle_apply_of_notMem h'), fun h h0 => ?_⟩` and prove the remaining obligations. Use `haveI : Q.IsPrime := h.1.1.1`. Use `localLength_ne_zero h.1.1.2 ?_` and prove the remaining obligations. Rewrite using `[← cast_projCycle_apply h, h0, Nat.cast_zero]`.
-/
theorem mem_support_projCycle {J Q : Ideal (MvPolynomial (Fin N) k)} :
    Q ∈ (projCycle J).support ↔ Q ∈ projComponents J := by
  rw [Finsupp.mem_support_iff]
  refine ⟨fun h => by_contra fun h' => h (projCycle_apply_of_notMem h'), fun h h0 => ?_⟩
  haveI : Q.IsPrime := h.1.1.1
  refine localLength_ne_zero h.1.1.2 ?_
  rw [← cast_projCycle_apply h, h0, Nat.cast_zero]

def hyperplaneForm (u : Fin N → k) : MvPolynomial (Fin N) k := ∑ j, C (u j) * X j

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _`.
-/
theorem isHomogeneous_hyperplaneForm (u : Fin N → k) : (hyperplaneForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _

def hyperplaneSection (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) :
    Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  projCycle (P ⊔ Ideal.span {hyperplaneForm u})

def fixFirstBlock {B : ℕ} (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k) :
    MvPolynomial (Fin B × Fin N) k :=
  aeval (fun p : Fin (B + 1) × Fin N =>
    (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
      Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) f

end GlobalTheory.ChowHt

namespace GlobalTheory.Published

open GlobalTheory.ChowHt

def ChowFormExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
    I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
    (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
      MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f ∧
      ∀ g : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormIntExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f ∧
      ∀ g : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormHyperplaneSection : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 + 1 : ℕ) →
    ∀ u : Fin N → k, hyperplaneForm u ∉ P →
    ∀ (dl : ℕ) (f : MvPolynomial (Fin (e + 1 + 1) × Fin N) k), IsChowFormInt P (e + 1) dl f →
    ∀ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
      (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
      (∀ Q ∈ (hyperplaneSection P u).support, IsChowFormInt Q e (d Q) (g Q)) →
      ∃ c : k, c ≠ 0 ∧
        fixFirstBlock u f = C c * (hyperplaneSection P u).prod (fun Q m => g Q ^ m)

/- English proof (translation)
Use `⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left, fun h k _ _ N D I h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `h k N D I h1 h2 h3`. Conclude with `⟨f, hf, fun g hg => (hf.isChowFormInt.unique hg.isChowFormInt).2⟩`.
-/
theorem chowFormExists_iff : ChowFormExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
      I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
      (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.isChowFormInt.unique hg.isChowFormInt).2⟩

/- English proof (translation)
Use `⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left, fun h k _ _ N D I h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `h k N D I h1 h2 h3`. Conclude with `⟨f, hf, fun g hg => (hf.unique hg).2⟩`.
-/
theorem chowFormIntExists_iff : ChowFormIntExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.unique hg).2⟩

end GlobalTheory.Published
