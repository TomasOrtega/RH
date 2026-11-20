import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftIdempotentAdicComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

/- English proof (translation)
Take `⟨hsurj, hker⟩` from `sharp_map_surjective_ker A`. Use `haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by`. Rewrite using `[pow_one]`. Conclude with `A.compl`. Use `haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl`.

Use `haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete A`. Establish `hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y → Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y`. Introduce `x y h`. Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Rewrite using `[pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]`.

Establish `hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x)` using `fun x hx => hx.map A.sharp`. Establish `hU` using `GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))`. Take `⟨a, ha⟩` from `hsurj (Ideal.Quotient.mk _ e)`. Establish `haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a)`. Establish `: A.aToU1 (a * a) = A.aToU1 a`.

Rewrite using `[map_mul, ha]`. Conclude with `congrArg _ he |>.trans rfl`. Establish `h2` using `hmemker _ _ this`. Rewrite `h2` using `[map_mul]`. Conclude with `h2`.

Take `⟨e₀, ⟨he₀, hmk⟩, huniq⟩` from `GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero (Ideal.Quotient.mk _ a) haid`. Establish `hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y → A.aToU1 x = A.aToU1 y`. Introduce `x y h`. Establish `h3` using `Ideal.Quotient.eq.1 h`. Rewrite `h3` using `[pow_one, ← hker, RingHom.mem_ker, map_sub]`.

Conclude with `sub_eq_zero.1 h3`. Use `⟨e₀, ⟨he₀, ?_⟩, ?_⟩` and prove the remaining obligations. Use `hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩` and prove the remaining obligations. Rewrite using `[← A.sharpMap_eq, hcong _ _ hmk, ha]`. Introduce and unpack `e₁ ⟨he₁, hs₁⟩`.

Use `huniq e₁ ⟨he₁, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmk]`. Apply `hmemker` to reduce the goal to its premises. Establish `hs₀ : A.sharp e₀ = e` using `hU.unique ⟨hsharp_idem _ he₀, by`. Rewrite using `[← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩`.

Rewrite using `[A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]`.
-/
theorem existsUnique_idempotent_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U)
    (he : IsIdempotentElem e) : ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by
    rw [pow_one]; exact A.compl
  haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete A
  have hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y →
      Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y := by
    intro x y h
    apply Ideal.Quotient.eq.2
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  have hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x) := fun x hx =>
    hx.map A.sharp
  have hU := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero
    (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ e)
  have haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a) := by
    have : A.aToU1 (a * a) = A.aToU1 a := by
      rw [map_mul, ha]
      exact congrArg _ he |>.trans rfl
    have h2 := hmemker _ _ this
    rw [map_mul] at h2
    exact h2
  obtain ⟨e₀, ⟨he₀, hmk⟩, huniq⟩ := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero
    (Ideal.Quotient.mk _ a) haid
  have hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y →
      A.aToU1 x = A.aToU1 y := by
    intro x y h
    have h3 := Ideal.Quotient.eq.1 h
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub] at h3
    exact sub_eq_zero.1 h3
  refine ⟨e₀, ⟨he₀, ?_⟩, ?_⟩
  · refine hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩
    rw [← A.sharpMap_eq, hcong _ _ hmk, ha]
  · rintro e₁ ⟨he₁, hs₁⟩
    refine huniq e₁ ⟨he₁, ?_⟩
    rw [← hmk]
    apply hmemker
    have hs₀ : A.sharp e₀ = e := hU.unique ⟨hsharp_idem _ he₀, by
      rw [← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩
    rw [A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]

end GlobalTheory.CompanionTheory.Untilt
