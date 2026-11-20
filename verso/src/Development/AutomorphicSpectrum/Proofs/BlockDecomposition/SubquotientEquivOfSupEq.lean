import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepSecondIso

/- English proof (translation)
Introduce `G V _ _ _ ρ A B E hEA hsup`. Establish `hEA' : E.toSubmodule ≤ A.toSubmodule` using `fun x hx => hEA hx`. Set `PE` to `Submodule.comap E.toSubmodule.subtype B.toSubmodule`. Set `PA` to `Submodule.comap A.toSubmodule.subtype B.toSubmodule`. Set `f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA` to `PA.mkQ ∘ₗ Submodule.inclusion hEA'`.

Establish `hf : PE ≤ LinearMap.ker f`. Introduce `x hx`. Rewrite using `[LinearMap.mem_ker]`. Use `show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `hx`. Set `φ` to `PE.liftQ f hf`. Establish `hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x)` using `fun _ => rfl`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `q hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective PE q`. Rewrite `hq` using `[LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `hq`.

Establish `hsurj : Function.Surjective φ`. Introduce `q`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective PA q`. Establish `ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule`. Rewrite using `[← Subrepresentation.toSubmodule_sup, hsup]`.

Conclude with `a.2`. Take `⟨e, he, b, hb, hab⟩` from `Submodule.mem_sup.mp ha`. Use `⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, Submodule.Quotient.eq]`. Use `show e - (a : V) ∈ B.toSubmodule`.

Establish `hdiff : e - (a : V) = -b`. Rewrite using `[← hab]`. Normalize the expressions using the abelian group laws. Rewrite using `[hdiff]`. Conclude with `B.toSubmodule.neg_mem hb`.

Set `ψ` to `LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩`. Use `⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x) (fun y => ψ.apply_symm_apply y)⟩` and prove the remaining obligations. Conclude with `Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)`.
-/
theorem subQuot_equiv_of_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A →
    Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  intro G V _ _ _ ρ A B E hEA hsup
  have hEA' : E.toSubmodule ≤ A.toSubmodule := fun x hx => hEA hx
  let PE := Submodule.comap E.toSubmodule.subtype B.toSubmodule
  let PA := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA := PA.mkQ ∘ₗ Submodule.inclusion hEA'
  have hf : PE ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  let φ := PE.liftQ f hf
  have hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective PE q
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective PA q
    have ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, hsup]
      exact a.2
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp ha
    refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
    rw [hφ, Submodule.Quotient.eq]
    show e - (a : V) ∈ B.toSubmodule
    have hdiff : e - (a : V) = -b := by
      rw [← hab]
      abel
    rw [hdiff]
    exact B.toSubmodule.neg_mem hb
  let ψ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x)
    (fun y => ψ.apply_symm_apply y)⟩
  exact Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)

end GlobalTheory.CompanionTheory.RepSecondIso
