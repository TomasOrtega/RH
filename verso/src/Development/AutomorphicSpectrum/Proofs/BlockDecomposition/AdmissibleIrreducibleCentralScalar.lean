import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π hs hirr hadm t`. Use `haveI := hirr`. Establish `hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t = Matrix.GeneralLinearGroup.scalar (Fin N) t * g`. Introduce `g`. Use extensionality with `i j`.

Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]`. Use `set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef`. Establish `hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w)`. Introduce `g w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `(bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(⊥ : Submodule ℂ V) = ⊤`. Use extensionality with `u`. Simplify using `[h u]`. Set `S : Subgroup (GL (Fin N) k)` to `{ carrier := {g | π g v = v} mul_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Set `K : Subgroup (GL (Fin N) k)` to `GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S`.

Establish `hKo : IsOpen (K : Set (GL (Fin N) k))` using `(GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)`. Establish `hKc : IsCompact (K : Set (GL (Fin N) k))` using `(GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)`. Use `haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc`. Establish `hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w`. Introduce `w`.

Use `show (∀ h : K, _ = _) ↔ _`. Simplify using the standard rewrite rules. Establish `hvK : v ∈ fixed π K` using `(hmem v).2 fun h => h.2.2`. Use `haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩`. Establish `hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K`.

Introduce `w hw`. Use `(hmem _).2 fun h => ?_` and prove the remaining obligations. Rewrite using `[hcomm, (hmem w).1 hw h]`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue ((π z).restrict hst)`. Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`.

Establish `hw0 : (w : V) ≠ 0` using `fun h => hw.2 (Subtype.ext h)`. Establish `hwc : π z (w : V) = c • (w : V)`. Use `congrArg Subtype.val hw.apply_eq_smul` as an intermediate fact. Simplify using `using this`. Set `f : Representation.IntertwiningMap π π` to `{ toLinearMap := π z - c • LinearMap.id isIntertwining' := by`.

Introduce `g`. Use extensionality with `u`. Simplify using `[hcomm] }`. Use `⟨c, fun u => ?_⟩` and prove the remaining obligations. Break down `Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0` into its components or cases.

It suffices to derive a contradiction. Apply `hw0` to reduce the goal to its premises. Apply `hb.1` to reduce the goal to its premises. Use `show π z (w : V) - c • (w : V) = f 0`. Rewrite using `[hwc, sub_self, map_zero]`.

Use `congrArg (fun F : Representation.IntertwiningMap π π => F u) h0` as an intermediate fact. Establish `h1 : π z u - c • u = 0` using `this`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
