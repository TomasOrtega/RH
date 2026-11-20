import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem sum_up {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∑ᶠ a ∈ s, (ULift.up.{1} (f a)) = ULift.up.{1} (∑ᶠ a ∈ s, f a) :=
  ((AddEquiv.ulift (α := ℤ)).symm.map_finsum_mem f hs).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtPush_of :
    SumComp → FibFin → WtPush := by
  intro hS hF Z Z' S h p _ _ w hw A φ hφ
  let B : Sq (h ≫ p) :=
    ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
      IsPullback.paste_vert (IsPullback.of_hasPullback h A.v) A.pb⟩
  haveI : IsFinite A.r := Sq.finite A
  have hφ' : IsLocallyConstant (φ ∘ (pullback.snd h A.v)) :=
    hφ.comp_continuous (Scheme.Hom.continuous _)
  obtain ⟨ψ, hψ, hψeq⟩ := hw B (φ ∘ (pullback.snd h A.v)) hφ'
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [hψeq Ω x]
  apply (ULift.up_injective : Function.Injective (ULift.up.{1, 0} : ℤ → ULift.{1} ℤ))
  have step1 : ∀ q : gp Ω ⟶ pullback h A.v,
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)
        = w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v)) := by
    intro q
    simp only [Function.comp_apply, pt_comp]
    rfl
  change ULift.up (∑ᶠ (q : gp Ω ⟶ pullback h A.v) (_ : q ∈ fib (pullback.snd h A.v ≫ A.r) x),
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)) = _
  simp only [step1]
  rw [← sum_up (hF _ Ω x)]
  rw [hS (pullback.snd h A.v) A.r Ω x (ULift.{1} ℤ)
    (fun q => ULift.up (w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v))))]
  rw [← sum_up (hF A.r Ω x)]
  apply finsum_mem_congr rfl
  intro y hy
  rw [sum_up (hF _ Ω y)]
  congr 1
  unfold Wt.push
  rw [finsum_mem_mul]
  apply finsum_mem_eq_of_bijOn (fun q => q ≫ pullback.fst h A.v)
    (fib_bijOn (IsPullback.of_hasPullback h A.v) y)
  intro q hq
  simp only [fib, Set.mem_setOf_eq] at hq
  rw [hq]
