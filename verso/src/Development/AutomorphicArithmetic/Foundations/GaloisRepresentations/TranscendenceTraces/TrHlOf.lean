import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hR l _ n i Z S p _ w hw hl x k`. Establish `hne : ∀ k : ℕ, NeZero (l ^ k)` using `fun k => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hu : ∀ k : ℕ, IsUnit ((l ^ k : ℕ) : Γ(S, ⊤))` using `fun k => by`. Rewrite using `[Nat.cast_pow]`. Conclude with `hl.pow _`.

Establish `hT : ∃ T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i, ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)`. Use `⟨{ toFun := fun x => ⟨fun k => tr p w (l ^ k) n i (x.1 k), fun k => ?_⟩ map_add' := fun x y => Subtype.ext (funext fun k => map_add (tr p w (l ^ k) n i) (x.1 k) (y.1 k)) map_smul' := fun r x => Subtype.ext (funext fun k => ?_) }, fun _ _ => rfl⟩` and prove the remaining obligations. Use `haveI := hne (k + 1) haveI := hne k`. Conclude with `(hR (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) n i p w hw (hu (k + 1)) (x.1 (k + 1))).trans (congrArg _ (x.2 k))`. Set `f : HtL l k (sch.obj Z) n i →+ HtL l k (sch.obj S) n i` to `tr p w (l ^ k) n i`.

Express the relevant statement in the definitionally equal form `f (r • x.1 k) = r • f (x.1 k)`. Rewrite using `[HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]`. Conclude with `map_nsmul f _ _`. Conclude with `pick_spec (P := fun T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i => ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)) hT x k`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trHl_of :
    TrRed → TrHl := by
  intro hR l _ n i Z S p _ w hw hl x k
  have hne : ∀ k : ℕ, NeZero (l ^ k) := fun k => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ k : ℕ, IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := fun k => by
    rw [Nat.cast_pow]
    exact hl.pow _
  have hT : ∃ T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i,
      ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k) := by
    refine ⟨{ toFun := fun x => ⟨fun k => tr p w (l ^ k) n i (x.1 k), fun k => ?_⟩
              map_add' := fun x y => Subtype.ext (funext fun k => map_add (tr p w (l ^ k) n i) (x.1 k) (y.1 k))
              map_smul' := fun r x => Subtype.ext (funext fun k => ?_) }, fun _ _ => rfl⟩
    · haveI := hne (k + 1)
      haveI := hne k
      exact (hR (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) n i p w hw (hu (k + 1)) (x.1 (k + 1))).trans
        (congrArg _ (x.2 k))
    · let f : HtL l k (sch.obj Z) n i →+ HtL l k (sch.obj S) n i := tr p w (l ^ k) n i
      change f (r • x.1 k) = r • f (x.1 k)
      rw [HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
      exact map_nsmul f _ _
  exact pick_spec (P := fun T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i =>
    ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)) hT x k
