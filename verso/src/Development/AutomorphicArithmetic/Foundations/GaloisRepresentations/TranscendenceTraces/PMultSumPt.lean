import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hS hM hL hO hF V Ω _ _ r _`. Establish `hI : IsIntegralHom r` using `inferInstance`. Establish `hbij : Set.BijOn (fun z : gp Ω ⟶ V => pt z) (fib r (𝟙 (gp Ω))) Set.univ`. Use `⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz z' hz' h`.

Conclude with `hO Ω r Ω (𝟙 (gp Ω)) z z' hz hz' h`. Introduce `v _`. Establish `hv : r v = pt (𝟙 (gp Ω))`. Establish `h1` using `pt_eq (𝟙 (gp Ω)) (r v)`. Simplify using `using h1`.

Take `⟨z, hz, hzv⟩` from `hL r Ω (𝟙 (gp Ω)) v hv`. Conclude with `⟨z, hz, hzv⟩`. Establish `hfin : Finite V`. Establish `hu : (Set.univ : Set V).Finite`. Rewrite using `[← hbij.image_eq]`.

Conclude with `(hF r Ω (𝟙 (gp Ω))).image _`. Conclude with `Set.finite_univ_iff.mp hu`. Use `show (∑ᶠ (z : gp Ω ⟶ V) (_ : z ∈ fib r (𝟙 (gp Ω))), mult r Ω z) = _`. Rewrite using `[finsum_mem_eq_of_bijOn (fun z : gp Ω ⟶ V => pt z) hbij (g := fun v : V => ((Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat : ℤ)) (fun z hz => hM Ω r z hz), finsum_mem_univ, ← Nat.cast_finsum, hS Ω r]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.multSumPt_of :
    StalkSum → MultSec → PtLift → PtOne → FibFin → MultSumPt := by
  intro hS hM hL hO hF V Ω _ _ r _
  have hI : IsIntegralHom r := inferInstance
  have hbij : Set.BijOn (fun z : gp Ω ⟶ V => pt z) (fib r (𝟙 (gp Ω))) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro z hz z' hz' h
      exact hO Ω r Ω (𝟙 (gp Ω)) z z' hz hz' h
    · intro v _
      have hv : r v = pt (𝟙 (gp Ω)) := by
        have h1 := pt_eq (𝟙 (gp Ω)) (r v)
        simpa using h1
      obtain ⟨z, hz, hzv⟩ := hL r Ω (𝟙 (gp Ω)) v hv
      exact ⟨z, hz, hzv⟩
  have hfin : Finite V := by
    have hu : (Set.univ : Set V).Finite := by
      rw [← hbij.image_eq]
      exact (hF r Ω (𝟙 (gp Ω))).image _
    exact Set.finite_univ_iff.mp hu
  show (∑ᶠ (z : gp Ω ⟶ V) (_ : z ∈ fib r (𝟙 (gp Ω))), mult r Ω z) = _
  rw [finsum_mem_eq_of_bijOn (fun z : gp Ω ⟶ V => pt z) hbij
    (g := fun v : V => ((Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat : ℤ))
    (fun z hz => hM Ω r z hz), finsum_mem_univ, ← Nat.cast_finsum, hS Ω r]
