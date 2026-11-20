import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVarietyStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

/- English proof (translation)
Use `⟨⟨MonObj.one_comp _, one_pow _⟩, ?_⟩` and prove the remaining obligations. Introduce `R _ _ x _ hx`. Rewrite `hx` using `[pow_one]`. Substitute `hx` using the available equality. Use `⟨Algebra.ofId k R, ?_, fun ψ _ => Subsingleton.elim _ _⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(spOver (Algebra.ofId k R) ≫ (1 : ptOver k k ⟶ A.X)).left = (1 : ptOver k R ⟶ A.X).left`. Rewrite using `[MonObj.comp_one]`.
-/
theorem kerPow_one {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) :
    KerPow f 1 k (1 : ptOver k k ⟶ A.X) := by
  refine ⟨⟨MonObj.one_comp _, one_pow _⟩, ?_⟩
  intro R _ _ x _ hx
  rw [pow_one] at hx
  subst hx
  refine ⟨Algebra.ofId k R, ?_, fun ψ _ => Subsingleton.elim _ _⟩
  change (spOver (Algebra.ofId k R) ≫ (1 : ptOver k k ⟶ A.X)).left = (1 : ptOver k R ⟶ A.X).left
  rw [MonObj.comp_one]

/- English proof (translation)
Use `haveI : Fact q.Prime := ⟨hq⟩`. Take `⟨G, -, ⟨tA⟩⟩` from `GlobalTheory.AVTower.exists_tower q k A`. Take `⟨G', -, ⟨tB⟩⟩` from `GlobalTheory.AVTower.exists_tower q k B`. Use `⟨_, inferInstance, inferInstance, kerPt tA tB f e, kerPow_kerPt tA tB f e, ?_⟩` and prove the remaining obligations. Conclude with `(Nat.dvd_prime_pow hq).1 (finrank_quot_kerIdeal_dvd (tA.map tB f.hom) e) |>.imp fun _ h => h.2`.
-/
theorem exists_kerPow_primePow {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) (q e : ℕ) (hq : q.Prime) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f (q ^ e) H i ∧ ∃ j : ℕ, Module.finrank k H = q ^ j := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨G, -, ⟨tA⟩⟩ := GlobalTheory.AVTower.exists_tower q k A
  obtain ⟨G', -, ⟨tB⟩⟩ := GlobalTheory.AVTower.exists_tower q k B
  refine ⟨_, inferInstance, inferInstance, kerPt tA tB f e, kerPow_kerPt tA tB f e, ?_⟩
  exact (Nat.dvd_prime_pow hq).1 (finrank_quot_kerIdeal_dvd (tA.map tB f.hom) e) |>.imp fun _ h => h.2

/- English proof (translation)
Introduce `p hp k _ A B f m`. Establish `hpp : p.Prime` using `hp.out`. Proceed by induction on `m using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow q n hq hn`. Introduce `_ hdvd`.

Establish `hqp : q ≠ p`. Introduce and unpack `rfl`. Conclude with `hdvd (dvd_pow_self q hn.ne')`. Take `⟨H, _, _, i, hi, j, hj⟩` from `exists_kerPow_primePow f q n hq`. Use `⟨H, inferInstance, inferInstance, i, hi, ?_⟩` and prove the remaining obligations.

Rewrite using `[hj]`. Introduce `h`. Conclude with `hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h)).symm`. Consider the case `zero => intro h`. Conclude with `absurd h (lt_irrefl 0)`.

Consider the case `one`. Introduce `_ _`. Use `⟨k, inferInstance, inferInstance, 1, kerPow_one f, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_self]`. Conclude with `hpp.not_dvd_one`.

Consider the case `coprime a b ha hb hab iha ihb`. Introduce `_ hdvd`. Establish `hpa : ¬ p ∣ a` using `fun h => hdvd (h.mul_right b)`. Establish `hpb : ¬ p ∣ b` using `fun h => hdvd (h.mul_left a)`. Take `⟨H₁, _, _, i₁, hi₁, h₁⟩` from `iha (by omega) hpa`.

Take `⟨H₂, _, _, i₂, hi₂, h₂⟩` from `ihb (by omega) hpb`. Take `⟨H, _, _, i, hi, hH⟩` from `GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f a b hab H₁ i₁ H₂ i₂ hi₁ hi₂`. Use `⟨H, inferInstance, inferInstance, i, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[hH]`. Introduce `h`.

Break down `(Nat.Prime.dvd_mul hpp).1 h with h | h` into its components or cases. Conclude with `h₁ h`. Conclude with `h₂ h`.
-/
theorem exists_kerPow_not_dvd : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B)
    (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  intro p hp k _ A B f m
  have hpp : p.Prime := hp.out
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ hdvd
    have hqp : q ≠ p := by
      rintro rfl
      exact hdvd (dvd_pow_self q hn.ne')
    obtain ⟨H, _, _, i, hi, j, hj⟩ := exists_kerPow_primePow f q n hq
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hj]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h)).symm
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    refine ⟨k, inferInstance, inferInstance, 1, kerPow_one f, ?_⟩
    rw [Module.finrank_self]
    exact hpp.not_dvd_one
  | coprime a b ha hb hab iha ihb =>
    intro _ hdvd
    have hpa : ¬ p ∣ a := fun h => hdvd (h.mul_right b)
    have hpb : ¬ p ∣ b := fun h => hdvd (h.mul_left a)
    obtain ⟨H₁, _, _, i₁, hi₁, h₁⟩ := iha (by omega) hpa
    obtain ⟨H₂, _, _, i₂, hi₂, h₂⟩ := ihb (by omega) hpb
    obtain ⟨H, _, _, i, hi, hH⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f a b hab H₁ i₁ H₂ i₂ hi₁ hi₂
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hH]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
    · exact h₁ h
    · exact h₂ h

end GlobalTheory.AV.KerPart
