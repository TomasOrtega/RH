import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalRingPointedEtaleNeighbourhoodStatement

open IsLocalRing GlobalTheory.Henselisation

noncomputable section

namespace GlobalTheory.Henselisation

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
The claim follows from `Ring.DirectLimit.of_f h y`.
-/
theorem Hens.of_trans {i j : EtNbhd R} (h : i ≤ j) (y : i.B) :
    Hens.of j (EtNbhd.trans h y) = Hens.of i y :=
  Ring.DirectLimit.of_f h y

/- English proof (translation)
The claim follows from `haveI : IsDirectedOrder (EtNbhd R) := hdir Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) z`.
-/
theorem Hens.exists_of (hdir : IsDirected (EtNbhd R) (· ≤ ·)) (z : Hens R) :
    ∃ (i : EtNbhd R) (y : i.B), Hens.of i y = z :=
  haveI : IsDirectedOrder (EtNbhd R) := hdir
  Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B)
    (f := fun _ _ h => ⇑(EtNbhd.trans h)) z

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩`. Consider the case `succ l ih`. Introduce `x`.

Take `⟨i, y, hy⟩` from `ih (fun k => x k.castSucc)`. Take `⟨j, z, hz⟩` from `Hens.exists_of hdir (x (Fin.last l))`. Take `⟨m, him, hjm⟩` from `directed_of (· ≤ ·) i j`. Use `⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩` and prove the remaining obligations. Introduce `k`.

Proceed by induction on `k using Fin.lastCases with`. Consider the case `last => dsimp only`. Rewrite using `[Fin.lastCases_last, Hens.of_trans, hz]`. Consider the case `cast k => dsimp only`. Rewrite using `[Fin.lastCases_castSucc, Hens.of_trans, hy]`.
-/
theorem Hens.exists_of_fin (hdir : IsDirected (EtNbhd R) (· ≤ ·)) :
    ∀ (l : ℕ) (x : Fin l → Hens R), ∃ (i : EtNbhd R) (y : Fin l → i.B), ∀ k, Hens.of i (y k) = x k := by
  intro l
  induction l with
  | zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩
  | succ l ih =>
    intro x
    obtain ⟨i, y, hy⟩ := ih (fun k => x k.castSucc)
    obtain ⟨j, z, hz⟩ := Hens.exists_of hdir (x (Fin.last l))
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    refine ⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩
    intro k
    induction k using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last, Hens.of_trans, hz]
    | cast k => dsimp only; rw [Fin.lastCases_castSucc, Hens.of_trans, hy]

/- English proof (translation)
Establish `hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y`. Introduce `i r y`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, halg]`. Use `Module.Flat.iff_forall_isTrivialRelation.mpr ?_` and prove the remaining obligations. Introduce `l f x hfx`.

Take `⟨i, y, hy⟩` from `Hens.exists_of_fin hdir l x`. Establish `h0 : ∑ k, f k • y k = 0`. Apply `hinj i` to reduce the goal to its premises. Rewrite using `[map_zero, map_sum]`. Simplify using `only [hsmul, hy]`.

Conclude with `hfx`. Take `⟨k, a, z, hya, haf⟩` from `Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0`. Use `⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩` and prove the remaining obligations. Rewrite using `[← hy m, hya m, map_sum]`. Simplify using `only [hsmul]`.
-/
theorem flat_hens_of_stages (hdir : IsDirected (EtNbhd R) (· ≤ ·))
    (hinj : ∀ i : EtNbhd R, Function.Injective (Hens.of i))
    (halg : ∀ (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r)
    (hflat : ∀ i : EtNbhd R, Module.Flat R i.B) : Module.Flat R (Hens R) := by
  have hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y := by
    intro i r y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr ?_
  intro l f x hfx
  obtain ⟨i, y, hy⟩ := Hens.exists_of_fin hdir l x
  have h0 : ∑ k, f k • y k = 0 := by
    apply hinj i
    rw [map_zero, map_sum]
    simp only [hsmul, hy]
    exact hfx
  obtain ⟨k, a, z, hya, haf⟩ := Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0
  refine ⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩
  rw [← hy m, hya m, map_sum]
  simp only [hsmul]

/- English proof (translation)
Introduce `R _ _` and use `flat_hens_of_stages (GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R) (GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood R)`.
-/
theorem flat_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) :=
  fun R _ _ => flat_hens_of_stages (GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R) (GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood R)

end GlobalTheory.Henselisation
