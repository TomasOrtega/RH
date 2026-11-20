import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hsum hfin W Z S r p _ _ w' w hr hp A φ hφ`. Take `⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u, m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r` from `⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Establish `hsq : IsPullback A.v m r (pullback.fst p A.u)`. Use `IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)` and prove the remaining obligations. Rewrite using `[hm2]`.

Conclude with `A.pb`. Set `C : Sq r` to `⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩`. Use `haveI : IsFinite m := C.finite`. Use `haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite`. Take `⟨ψ1, hψ1, hψ1s⟩` from `hr C φ hφ`.

Take `⟨ψ2, hψ2, hψ2s⟩` from `hp (Sq.of p A.u) ψ1 hψ1`. Use `⟨ψ2, hψ2, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ x`. Establish `hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z = ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z`. Introduce `c`.

Establish `h` using `congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ) (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))`. Simplify using `only [AddEquiv.map_finsum] at h`. Conclude with `h`. Use `(hψ2s Ω x).trans ?_` and prove the remaining obligations. Rewrite using `[← hm2, hsc]`.

Use `finsum_mem_congr rfl ?_` and prove the remaining obligations. Introduce `y _`. Use `(congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_` and prove the remaining obligations. Rewrite using `[mul_finsum_mem]`. Use `finsum_mem_congr rfl ?_` and prove the remaining obligations.

Introduce `z hz`. Establish `hz' : z ≫ m = y` using `hz`. Use `show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) = w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)`. Rewrite using `[Category.assoc, ← hm1, ← Category.assoc, hz']`. Conclude with `(mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtComp_of :
    SumComp → FibFin → WtComp := by
  intro hsum hfin W Z S r p _ _ w' w hr hp A φ hφ
  obtain ⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u,
      m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r :=
    ⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback A.v m r (pullback.fst p A.u) := by
    refine IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)
    rw [hm2]
    exact A.pb
  let C : Sq r := ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩
  haveI : IsFinite m := C.finite
  haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite
  obtain ⟨ψ1, hψ1, hψ1s⟩ := hr C φ hφ
  obtain ⟨ψ2, hψ2, hψ2s⟩ := hp (Sq.of p A.u) ψ1 hψ1
  refine ⟨ψ2, hψ2, ?_⟩
  intro Ω _ _ x
  have hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z =
      ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z := by
    intro c
    have h := congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ)
      (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))
    simp only [AddEquiv.map_finsum] at h
    exact h
  refine (hψ2s Ω x).trans ?_
  rw [← hm2, hsc]
  refine finsum_mem_congr rfl ?_
  intro y _
  refine (congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl ?_
  intro z hz
  have hz' : z ≫ m = y := hz
  show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) =
    w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)
  rw [Category.assoc, ← hm1, ← Category.assoc, hz']
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
