import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalSubfieldMissingElemExpOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqOneOfPowMemStatement
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp k _ _ hk K _ _ f hf`. Assume the negation of the conclusion as `hne`. Establish `hK : (p : K) = 0`. Use `congrArg (algebraMap k K) hk` as an intermediate fact. Simplify using `using this`.

Use `haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 hK`. Set `F : Subfield K` to `(frobenius K p).fieldRange`. Establish `hF : ∀ y : K, y ^ p ∈ F` using `fun y => ⟨y, by simp [frobenius_def]⟩`. Establish `hfF : f ∉ F`. Introduce and unpack `⟨h, hh⟩`.

Conclude with `hne ⟨h, by simpa [frobenius_def] using hh⟩`. Take `⟨L, hFL, hfL, htop⟩` from `GlobalTheory.T.exists_maximal_subfield_missing_elem_expOne p K F hF f hfF`. Take `⟨D, hD⟩` from `GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' p K L f hfL (hFL (hF f)) htop`. Establish `hkL : ∀ a : k, algebraMap k K a ∈ L`. Introduce `a`.

Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq a hp.out.pos`. Rewrite using `[← hb, map_pow]`. Conclude with `hFL (hF _)`. Establish `hD0 : ∀ a : k, D (algebraMap k K a) = 0` using `fun a => D.map_algebraMap (⟨_, hkL a⟩ : L)`. Set `D' : Derivation k K K` to `Derivation.mk' { toFun := D map_add' := fun x y => map_add D x y map_smul' := fun a x => by`.

Simplify using `only [Algebra.smul_def, RingHom.id_apply, Derivation.leibniz, hD0, smul_eq_mul]`. Simplify using `}`. Use the proof step `(fun a b => D.leibniz a b)`. Establish `h1 : D' f = 1` using `hD`. Establish `h2` using `D'.liftKaehlerDifferential_comp_D f`.

Rewrite `h2` using `[hf, map_zero, h1]`. Conclude with `zero_ne_one h2`.
-/
theorem exists_pow_eq_of_kaehler_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  intro p hp k _ _ hk K _ _ f hf
  by_contra hne
  have hK : (p : K) = 0 := by
    have := congrArg (algebraMap k K) hk
    simpa using this
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 hK
  let F : Subfield K := (frobenius K p).fieldRange
  have hF : ∀ y : K, y ^ p ∈ F := fun y => ⟨y, by simp [frobenius_def]⟩
  have hfF : f ∉ F := by
    rintro ⟨h, hh⟩
    exact hne ⟨h, by simpa [frobenius_def] using hh⟩
  obtain ⟨L, hFL, hfL, htop⟩ := GlobalTheory.T.exists_maximal_subfield_missing_elem_expOne p K F hF f hfF
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' p K L f hfL (hFL (hF f)) htop
  have hkL : ∀ a : k, algebraMap k K a ∈ L := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    rw [← hb, map_pow]
    exact hFL (hF _)
  have hD0 : ∀ a : k, D (algebraMap k K a) = 0 := fun a =>
    D.map_algebraMap (⟨_, hkL a⟩ : L)
  let D' : Derivation k K K := Derivation.mk'
    { toFun := D
      map_add' := fun x y => map_add D x y
      map_smul' := fun a x => by
        simp only [Algebra.smul_def, RingHom.id_apply, Derivation.leibniz, hD0, smul_eq_mul]
        simp }
    (fun a b => D.leibniz a b)
  have h1 : D' f = 1 := hD
  have h2 := D'.liftKaehlerDifferential_comp_D f
  rw [hf, map_zero, h1] at h2
  exact zero_ne_one h2

end GlobalTheory
