import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Introduce `Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩`. Use `set φ := cutHom G hM s`. Set `ψ` to `Abelian.factorThruImage φ`. Establish `hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ` using `Abelian.image.fac φ`. Establish `: Epi ψ` using `inferInstanceAs (Epi (Abelian.factorThruImage φ))`.

Establish `hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_kernel _ }`. Establish `hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_kernel _ }`. Set `eK : kernel ψ ≅ kernel φ` to `(kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ`. Establish `arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m → (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n)`. Introduce `a n j m h₁ h₂`.

Take `⟨j', rfl⟩` from `Nat.exists_eq_add_of_le h₁`. Take `⟨m', rfl⟩` from `Nat.exists_eq_add_of_le h₂`. Simplify using `only [Nat.add_sub_cancel_left]`. Use `module`. Use `set J := max j₁ (max jK jC) with hJ`.

Establish `hJ₁ : j₁ ≤ J` using `le_max_left _ _`. Establish `hJK : jK ≤ J` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hJC : jC ≤ J` using `(le_max_right _ _).trans (le_max_right _ _)`. Establish `key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)`. Introduce `m`.

Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `j hmj hJj p hp`. Distinguish the cases in `hm : m < 2 * r`. Conclude with `h₁ j m (by omega) hm p hp`.

Use `push_neg at hm`. Establish `hT : (tens (lbPow A j) (lbPow N m)).IsLB` using `isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)`. Establish `e₁` using `Twist.shortExact_map hT hS₁`. Establish `e₂` using `Twist.shortExact_map hT hS₂`. Choose the witnesses or unpack the hypotheses as in `⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅ twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by`.

Use `nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_` and prove the remaining obligations. Rewrite using `[cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]`. Conclude with `arith _ _ j m (by omega) hm`. Establish `hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) (tens (lbPow A j) (lbPow N m))) ⊤ p)`. Use `ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp` as an intermediate fact.

Conclude with `(cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton`. Establish `hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1))`. Use `hK j m (by omega) hmj (p + 1) (by omega)` as an intermediate fact. Conclude with `@Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this`. Establish `himg` using `cohOn.subsingleton₃ e₁ ⊤ p hmid hker`.

Conclude with `cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)`. Conclude with `⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩`.
-/
theorem twistConeVanishing_of_cut : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  intro Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩
  set φ := cutHom G hM s
  let ψ := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  let eK : kernel ψ ≅ kernel φ := (kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ
  have arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m →
      (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n) := by
    intro a n j m h₁ h₂
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h₁
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h₂
    simp only [Nat.add_sub_cancel_left]
    module
  set J := max j₁ (max jK jC) with hJ
  have hJ₁ : j₁ ≤ J := le_max_left _ _
  have hJK : jK ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : jC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p →
      Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hmj hJj p hp
      by_cases hm : m < 2 * r
      · exact h₁ j m (by omega) hm p hp
      · push_neg at hm
        have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
        have e₁ := Twist.shortExact_map hT hS₁
        have e₂ := Twist.shortExact_map hT hS₂
        obtain ⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅
            twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by
          refine nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT
            (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_
          rw [cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _),
            cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]
          exact arith _ _ j m (by omega) hm
        have hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1))
            (tens (lbPow A j) (lbPow N m))) ⊤ p) := by
          have := ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp
          exact (cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton
        have hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1)) := by
          have := hK j m (by omega) hmj (p + 1) (by omega)
          exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this
        have himg := cohOn.subsingleton₃ e₁ ⊤ p hmid hker
        exact cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)
  exact ⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩

end GlobalTheory
