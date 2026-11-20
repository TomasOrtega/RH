import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `((AddEquiv.ulift (α := ℤ)).symm.map_finsum_mem f hs).symm`.
-/
private theorem sum_up {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∑ᶠ a ∈ s, (ULift.up.{1} (f a)) = ULift.up.{1} (∑ᶠ a ∈ s, f a) :=
  ((AddEquiv.ulift (α := ℤ)).symm.map_finsum_mem f hs).symm

/- English proof (translation)
Introduce `hS hF Z Z' S h p _ _ w hw A φ hφ`. Set `B : Sq (h ≫ p)` to `⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r, IsPullback.paste_vert (IsPullback.of_hasPullback h A.v) A.pb⟩`. Use `haveI : IsFinite A.r := Sq.finite A`. Establish `hφ' : IsLocallyConstant (φ ∘ (pullback.snd h A.v))` using `hφ.comp_continuous (Scheme.Hom.continuous _)`. Take `⟨ψ, hψ, hψeq⟩` from `hw B (φ ∘ (pullback.snd h A.v)) hφ'`.

Use `⟨ψ, hψ, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ x`. Rewrite using `[hψeq Ω x]`. Apply `(ULift.up_injective : Function.Injective (ULift.up.{1, 0} : ℤ → ULift.{1} ℤ))` to reduce the goal to its premises. Establish `step1 : ∀ q : gp Ω ⟶ pullback h A.v, w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q) = w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v))`.

Introduce `q`. Simplify using `only [Function.comp_apply, pt_comp]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `ULift.up (∑ᶠ (q : gp Ω ⟶ pullback h A.v) (_ : q ∈ fib (pullback.snd h A.v ≫ A.r) x), w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)) = _`. Simplify using `only [step1]`.

Rewrite using `[← sum_up (hF _ Ω x)]`. Rewrite using `[hS (pullback.snd h A.v) A.r Ω x (ULift.{1} ℤ) (fun q => ULift.up (w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v))))]`. Rewrite using `[← sum_up (hF A.r Ω x)]`. Apply `finsum_mem_congr rfl` to reduce the goal to its premises. Introduce `y hy`.

Rewrite using `[sum_up (hF _ Ω y)]`. Use `congr 1`. Unfold `Wt.push`. Rewrite using `[finsum_mem_mul]`. Apply `finsum_mem_eq_of_bijOn (fun q => q ≫ pullback.fst h A.v) (fib_bijOn (IsPullback.of_hasPullback h A.v) y)` to reduce the goal to its premises.

Introduce `q hq`. Simplify using `only [fib, Set.mem_setOf_eq] at hq`. Rewrite using `[hq]`.
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
