import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GenFibMap

variable {A A' A'' X X' X'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [CommRing X]
  [CommRing X'] [CommRing X''] [Algebra A X] [Algebra A' X'] [Algebra A'' X'']

/- English proof (translation)
Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `⟨φ a, hφ a ha, ?_⟩` and prove the remaining obligations. Simplify using `only [IsScalarTower.algebraMap_apply A X (Localization.AtPrime P), IsScalarTower.algebraMap_apply A' X' (Localization.AtPrime P'), Localization.localRingHom_to_map, hc]`.
-/
theorem submonoid_le (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P') (nonZeroDivisors A')).comap
        (Localization.localRingHom P P' χ hP) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨φ a, hφ a ha, ?_⟩
  simp only [IsScalarTower.algebraMap_apply A X (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply A' X' (Localization.AtPrime P'),
    Localization.localRingHom_to_map, hc]

def genFibMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P') :=
  IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
    (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P')) (Localization.localRingHom P P' χ hP)
    (submonoid_le φ χ hc hφ P P' hP)

/- English proof (translation)
The claim follows from `IsLocalization.map_comp _`.
-/
theorem genFibMap_comp_algebraMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    (genFibMap φ χ hc hφ P P' hP).comp
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))) =
      (algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))).comp
        (Localization.localRingHom P P' χ hP) :=
  IsLocalization.map_comp _

/- English proof (translation)
Rewrite using `[genFibMap, IsLocalization.map_eq, Localization.localRingHom_to_map]`.
-/
theorem genFibMap_apply (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) (y : X) :
    genFibMap φ χ hc hφ P P' hP
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
          (algebraMap X (Localization.AtPrime P) y)) =
      algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))
          (algebraMap X' (Localization.AtPrime P') (χ y)) := by
  rw [genFibMap, IsLocalization.map_eq, Localization.localRingHom_to_map]

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A))` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext P.primeCompl` to reduce the goal to its premises. Conclude with `RingHom.ext h`.
-/
theorem ext {C : Type} [CommRing C] (P : Ideal X) [P.IsPrime]
    {u v : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* C}
    (h : ∀ y : X, u (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y)) =
      v (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y))) : u = v := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A))
  apply IsLocalization.ringHom_ext P.primeCompl
  exact RingHom.ext h

/- English proof (translation)
Use `ext P (fun y => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, genFibMap_apply, hχ]`.
-/
theorem genFibMap_comp (φ₁ : A →+* A') (χ₁ : X →+* X')
    (hc₁ : ∀ a, χ₁ (algebraMap A X a) = algebraMap A' X' (φ₁ a))
    (hφ₁ : ∀ a ∈ nonZeroDivisors A, φ₁ a ∈ nonZeroDivisors A')
    (φ₂ : A' →+* A'') (χ₂ : X' →+* X'')
    (hc₂ : ∀ a, χ₂ (algebraMap A' X' a) = algebraMap A'' X'' (φ₂ a))
    (hφ₂ : ∀ a ∈ nonZeroDivisors A', φ₂ a ∈ nonZeroDivisors A'')
    (φ₃ : A →+* A'') (χ₃ : X →+* X'')
    (hc₃ : ∀ a, χ₃ (algebraMap A X a) = algebraMap A'' X'' (φ₃ a))
    (hφ₃ : ∀ a ∈ nonZeroDivisors A, φ₃ a ∈ nonZeroDivisors A'')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (P'' : Ideal X'') [P''.IsPrime]
    (h₁ : P = P'.comap χ₁) (h₂ : P' = P''.comap χ₂) (h₃ : P = P''.comap χ₃)
    (hχ : ∀ y, χ₃ y = χ₂ (χ₁ y)) :
    (genFibMap φ₂ χ₂ hc₂ hφ₂ P' P'' h₂).comp (genFibMap φ₁ χ₁ hc₁ hφ₁ P P' h₁) =
      genFibMap φ₃ χ₃ hc₃ hφ₃ P P'' h₃ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.comp_apply, genFibMap_apply, hχ]

/- English proof (translation)
Use `ext P (fun y => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, genFibMap_apply, hχ]`.
-/
theorem genFibMap_id (φ : A →+* A) (χ : X →+* X)
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A X (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A)
    (P : Ideal X) [P.IsPrime] (hP : P = P.comap χ) (hχ : ∀ y, χ y = y) :
    genFibMap φ χ hc hφ P P hP = RingHom.id _ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.id_apply, genFibMap_apply, hχ]

end GlobalTheory.GenFibMap
