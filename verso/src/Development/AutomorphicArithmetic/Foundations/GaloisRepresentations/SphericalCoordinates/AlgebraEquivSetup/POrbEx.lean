import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ p _ Kq u τ₁ h₁`. Set `S` to `{τ : E →+* PadicAlgCl p // LiesOver Kq u τ}`. Set `R : Setoid S` to `{ r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]), b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1 iseqv := ⟨fun a => ⟨1, by ext x; simp⟩, fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩, fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by …`. Use `haveI : Finite (E →+* PadicAlgCl p) := inferInstance`. Use `haveI : Finite S := Subtype.finite`.

Use `haveI : Finite (Quotient R) := Quotient.finite _`. Set `s₁ : S` to `⟨τ₁, h₁⟩`. Set `rep : Quotient R → S` to `fun q => if q = Quotient.mk R s₁ then s₁ else q.out`. Establish `hrep : ∀ q, Quotient.mk R (rep q) = q`. Introduce `q`.

Distinguish the cases in `hq : q = Quotient.mk R s₁`. Simplify using `only [rep, if_pos hq]`. Conclude with `hq.symm`. Simplify using `only [rep, if_neg hq]`. Conclude with `Quotient.out_eq q`.

Set `eq` to `Finite.equivFin (Quotient R)`. Use `⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[rep, s₁]`. Introduce `i`. Conclude with `(rep _).2`.

Introduce `i j σ hij`. Apply `eq.symm.injective` to reduce the goal to its premises. Rewrite using `[← hrep (eq.symm i), ← hrep (eq.symm j)]`. Conclude with `Quotient.sound ⟨σ, hij.symm⟩`. Introduce `τ hτ`.

Take `⟨σ, hσ⟩` from `Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))`. Conclude with `⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
