import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π hs y`. Take `⟨v, rfl⟩` from `Submodule.mkQ_surjective _ y`. Set `U : Subgroup (GL (Fin n) k)` to `{ carrier := {g | π g v = v} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Use `⟨U, hs v, fun K hK => ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map_of_mem (p := fixed π K) ?_` and prove the remaining obligations.

Introduce `h`. Establish `hv : π (h : GL (Fin n) k) v = v` using `hK h.2`. Simplify using `using hv`.
-/
theorem UpperTheory.Gal.Join.expLev :
    UpperTheory.Gal.Join.ExpLev := by
  intro k _ _ _ _ n V _ _ π hs y
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  let U : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  refine ⟨U, hs v, fun K hK => ?_⟩
  refine Submodule.mem_map_of_mem (p := fixed π K) ?_
  intro h
  have hv : π (h : GL (Fin n) k) v = v := hK h.2
  simpa using hv
