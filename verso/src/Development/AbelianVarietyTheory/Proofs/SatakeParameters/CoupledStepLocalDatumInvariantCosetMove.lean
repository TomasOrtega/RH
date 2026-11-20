import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

variable {E K : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hboth : Psi w₁ = 0 ∧ Psi w = 0`. Rewrite using `[hboth.1, hboth.2]`. Use `set u := k.symm w₁ with hu`. Establish `hqpow : ∀ m : ℕ, IntAt P (q ^ m)` using `fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)`. Establish `hU : ∀ i, IntAt P (q ^ e' * u i)`.

Distinguish the cases in `hw : Psi w = 0`. Establish `hw₁ : Psi w₁ ≠ 0` using `fun h => hboth ⟨h, hw⟩`. Establish `h1` using `hSupp w₁ hw₁`. Establish `h2 : ∀ i, IntAt P (k (q ^ e' • u) i)`. Introduce `i`.

Rewrite using `[map_smul, hu, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `h1 i`. Introduce `i`. Use `hkint _ h2 i` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis.

Establish `h1` using `hSupp w hw`. Introduce `i`. Establish `e1 : q ^ e' * u i = q ^ e' * w i + q ^ (e + e') * ((q ^ e)⁻¹ * (u - w) i)`. Rewrite using `[Pi.sub_apply, pow_add]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `mem_intS.1 ((intS P).add_mem (mem_intS.2 (h1 i)) ((intS P).mul_mem (mem_intS.2 (hqpow _)) (mem_intS.2 (hc i))))`. Establish `hz : ∀ l, IntAt P ((q ^ e)⁻¹ * (w₁ - w) l)`. Introduce `l`.

Establish `hsum : u = ∑ s, u s • (Pi.single s 1 : Sp E n)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hw₁ : w₁ = k u` using `by rw [hu, LinearEquiv.apply_symm_apply]`. Take `⟨t, ht⟩ : ∃ t, D = e + e' + t` from `⟨D - (e + e'), by omega⟩`.

Establish `e2 : (q ^ e)⁻¹ * (w₁ - w) l = (∑ s, (q ^ e' * u s) * ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) * q ^ t) + (q ^ e)⁻¹ * (u - w) l`. Establish `e3 : (w₁ - w) l = (∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) + (u - w) l`. Establish `e4 : (k u - u) l = ∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)` using `by conv_lhs => rw [hsum]`. Rewrite using `[map_sum, ← Finset.sum_sub_distrib, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← smul_sub, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]`. Rewrite using `[← e4, hw₁]`. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, mul_add, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[ht, pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`.

Use `mem_intS.1 ((intS P).add_mem ((intS P).sum_mem fun s _ => ?_) (mem_intS.2 (hc l)))` and prove the remaining obligations. Conclude with `(intS P).mul_mem ((intS P).mul_mem (mem_intS.2 (hU s)) (mem_intS.2 (hk s l))) (mem_intS.2 (hqpow t))`. Use `hInv w (w₁ - w) hz` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem core (Psi : Sp E n → K) [Zero K] (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (e e' D : ℕ) (hD : e + e' ≤ D)
    (hInv : ∀ y z : Sp E n, (∀ i, IntAt P ((q ^ e)⁻¹ * z i)) → Psi (y + z) = Psi y)
    (hSupp : ∀ y : Sp E n, Psi y ≠ 0 → ∀ i, IntAt P (q ^ e' * y i))
    (k : Sp E n ≃ₗ[E] Sp E n)
    (hkint : ∀ x : Sp E n, (∀ i, IntAt P (k x i)) → ∀ i, IntAt P (x i))
    (hk : ∀ s l, IntAt P ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)))
    (w w₁ : Sp E n) (hc : ∀ l, IntAt P ((q ^ e)⁻¹ * (k.symm w₁ - w) l)) :
    Psi w₁ = Psi w := by
  by_cases hboth : Psi w₁ = 0 ∧ Psi w = 0
  · rw [hboth.1, hboth.2]
  set u := k.symm w₁ with hu
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)

  have hU : ∀ i, IntAt P (q ^ e' * u i) := by
    by_cases hw : Psi w = 0
    · have hw₁ : Psi w₁ ≠ 0 := fun h => hboth ⟨h, hw⟩
      have h1 := hSupp w₁ hw₁
      have h2 : ∀ i, IntAt P (k (q ^ e' • u) i) := by
        intro i
        rw [map_smul, hu, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
        exact h1 i
      intro i
      have := hkint _ h2 i
      rwa [Pi.smul_apply, smul_eq_mul] at this
    · have h1 := hSupp w hw
      intro i
      have e1 : q ^ e' * u i = q ^ e' * w i + q ^ (e + e') * ((q ^ e)⁻¹ * (u - w) i) := by
        rw [Pi.sub_apply, pow_add]
        field_simp
        ring
      rw [e1]
      exact mem_intS.1 ((intS P).add_mem (mem_intS.2 (h1 i))
        ((intS P).mul_mem (mem_intS.2 (hqpow _)) (mem_intS.2 (hc i))))

  have hz : ∀ l, IntAt P ((q ^ e)⁻¹ * (w₁ - w) l) := by
    intro l
    have hsum : u = ∑ s, u s • (Pi.single s 1 : Sp E n) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hw₁ : w₁ = k u := by rw [hu, LinearEquiv.apply_symm_apply]
    obtain ⟨t, ht⟩ : ∃ t, D = e + e' + t := ⟨D - (e + e'), by omega⟩
    have e2 : (q ^ e)⁻¹ * (w₁ - w) l =
        (∑ s, (q ^ e' * u s) * ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) * q ^ t) +
          (q ^ e)⁻¹ * (u - w) l := by
      have e3 : (w₁ - w) l = (∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) + (u - w) l := by
        have e4 : (k u - u) l = ∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l) := by
          conv_lhs => rw [hsum]
          rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_apply]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smul, ← smul_sub, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        rw [← e4, hw₁]
        simp only [Pi.sub_apply]
        ring
      rw [e3, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ht, pow_add, pow_add]
      field_simp
    rw [e2]
    refine mem_intS.1 ((intS P).add_mem ((intS P).sum_mem fun s _ => ?_) (mem_intS.2 (hc l)))
    exact (intS P).mul_mem ((intS P).mul_mem (mem_intS.2 (hU s)) (mem_intS.2 (hk s l))) (mem_intS.2 (hqpow t))
  have := hInv w (w₁ - w) hz
  rwa [add_sub_cancel] at this

end GlobalTheory.PsiCosetInv

namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hL al P x₀ k w w₁ hk hc`. Establish `hInv` using `hL.psiInv al P x₀`. Establish `hSupp` using `hL.psiSupp al P x₀`. Unfold `SameCoset at hc`. Establish `hkint : ∀ x : Sp X.E (R.N (m2 + 1)), (∀ i, IntAt P.1 (k.1 x i)) → ∀ i, IntAt P.1 (x i)`.

Introduce `x hx`. Establish `h1 : k.1 x ∈ stdAt X.E (R.N (m2 + 1)) P.1` using `(mem_localization_standardLattice P.1 _).2 hx`. Conclude with `(mem_localization_standardLattice P.1 _).1 ((k.2 x).1 h1)`. Establish `hq` using `qOf_ne (E := X.E) P.1`. Establish `hqi : IntAt P.1 ((qOf P.1 : ℕ) : X.E)` using `intAt_nat (P := P.1) _`.

Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Simplify using `only [if_pos hP] at hInv hSupp hc`. Conclude with `core _ _ hq hqi 0 1 (cst.D P) (by rw [hL.depthG P hP]) hInv hSupp k.1 hkint hk w w₁ hc`. Simplify using `only [if_neg hP] at hInv hSupp hc`. Conclude with `core _ _ hq hqi cst.M cst.M (cst.D P) (by have := hL.depthQ P hP; omega) hInv hSupp k.1 hkint hk w w₁ hc`.
-/
theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := by
  intro X Pr R Ch sel S mu cst L G m2 hL al P x₀ k w w₁ hk hc
  have hInv := hL.psiInv al P x₀
  have hSupp := hL.psiSupp al P x₀
  unfold SameCoset at hc
  have hkint : ∀ x : Sp X.E (R.N (m2 + 1)), (∀ i, IntAt P.1 (k.1 x i)) → ∀ i, IntAt P.1 (x i) := by
    intro x hx
    have h1 : k.1 x ∈ stdAt X.E (R.N (m2 + 1)) P.1 := (mem_localization_standardLattice P.1 _).2 hx
    exact (mem_localization_standardLattice P.1 _).1 ((k.2 x).1 h1)
  have hq := qOf_ne (E := X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := intAt_nat (P := P.1) _
  by_cases hP : P.1 ∈ Pr.vGs
  · simp only [if_pos hP] at hInv hSupp hc
    exact core _ _ hq hqi 0 1 (cst.D P) (by rw [hL.depthG P hP]) hInv hSupp k.1 hkint hk w w₁ hc
  · simp only [if_neg hP] at hInv hSupp hc
    exact core _ _ hq hqi cst.M cst.M (cst.D P) (by have := hL.depthQ P hP; omega) hInv hSupp k.1 hkint hk w w₁ hc

end GlobalTheory.PsiCosetInv
