import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingOpenLevel

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

/- English proof (translation)
Use `⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : q = p`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `FractionalIdeal.one_mem_one _`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `FractionalIdeal.zero_mem _`. Use function extensionality and compare the values at `i`. Simplify using `[mulVec_single]`.
-/
theorem col_mem (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (p : Fin c) :
    (fun i => d.a i p) ∈ d.lat Λ (fun _ => 1) := by
  refine ⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rw [Pi.single_eq_same]; exact FractionalIdeal.one_mem_one _
    · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
  · funext i; simp [mulVec_single]

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩`.
-/
theorem map_mem (d : HermitianOrthogonalExtensionData A B c ε) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {y : Fin A.rank → D.host.E}
    (hy : y ∈ Λ) : frameMat B A d.ι *ᵥ y ∈ d.lat Λ (fun _ => 1) :=
  ⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩

/- English proof (translation)
Use `le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, u, hu, rfl⟩`. Use `Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_` and prove the remaining obligations. Use `choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)`. Establish `e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p`.

Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `map_mem d hy`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `col_mem d Λ p`.
-/
theorem lat_eq (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) :
    d.lat Λ (fun _ => 1) = Λ.map ((frameMat B A d.ι).mulVecLin.restrictScalars (𝓞 D.host.E)) ⊔
      Submodule.span (𝓞 D.host.E) (Set.range fun p i => d.a i p) := by
  refine le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_
    choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)
    have e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p := by
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩; exact map_mem d hy
  · rintro _ ⟨p, rfl⟩; exact col_mem d Λ p

/- English proof (translation)
Use `⟨?_, eq_top_iff.2 fun z _ => ?_⟩` and prove the remaining obligations. Rewrite using `[lat_eq]`. Conclude with `(hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))`. Use `set S := Submodule.span D.host.E ((d.lat Λ fun _ => 1 : Submodule (𝓞 D.host.E) _) : Set (Fin B.rank → D.host.E))`. Establish `h1 : ∀ w, frameMat B A d.ι *ᵥ w ∈ S`.

Establish `: Submodule.span D.host.E (Λ : Set (Fin A.rank → D.host.E)) ≤ S.comap (frameMat B A d.ι).mulVecLin` using `Submodule.span_le.2 fun y hy => Submodule.subset_span (map_mem d hy)`. Introduce `w`. Conclude with `this (by rw [hΛ.span_eq_top]; trivial)`. Establish `h2 : ∀ u, d.a *ᵥ u ∈ S`. Introduce `u`.

Establish `e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p`. Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (col_mem d Λ p))`.

Establish `e : z = frameMat B A d.ι *ᵥ (GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ z) + d.a *ᵥ (GlobalTheory.UnitaryEmbeddingGroup.rM d *ᵥ z)`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, ← add_mulVec, GlobalTheory.UnitaryEmbeddingGroup.decomp d hε, one_mulVec]`. Rewrite using `[e]`. Conclude with `add_mem (h1 _) (h2 _)`.
-/
theorem isLattice_lat (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := by
  refine ⟨?_, eq_top_iff.2 fun z _ => ?_⟩
  · rw [lat_eq]
    exact (hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · set S := Submodule.span D.host.E ((d.lat Λ fun _ => 1 : Submodule (𝓞 D.host.E) _) : Set (Fin B.rank → D.host.E))
    have h1 : ∀ w, frameMat B A d.ι *ᵥ w ∈ S := by
      have : Submodule.span D.host.E (Λ : Set (Fin A.rank → D.host.E)) ≤ S.comap (frameMat B A d.ι).mulVecLin :=
        Submodule.span_le.2 fun y hy => Submodule.subset_span (map_mem d hy)
      intro w
      exact this (by rw [hΛ.span_eq_top]; trivial)
    have h2 : ∀ u, d.a *ᵥ u ∈ S := by
      intro u
      have e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p := by
        funext i
        simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (col_mem d Λ p))
    have e : z = frameMat B A d.ι *ᵥ (GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ z) + d.a *ᵥ (GlobalTheory.UnitaryEmbeddingGroup.rM d *ᵥ z) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, GlobalTheory.UnitaryEmbeddingGroup.decomp d hε, one_mulVec]
    rw [e]
    exact add_mem (h1 _) (h2 _)

end GlobalTheory.UnitaryEmbeddingOpenLevel

open GlobalTheory.UnitaryEmbeddingOpenLevel in

/- English proof (translation)
Introduce `D Y V d Λ 𝔪 hΛ h𝔪`. Conclude with `(congLev_open_compact V (isLattice_lat d one_ne_zero hΛ.1) h𝔪).1`.
-/
theorem GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  intro D Y V d Λ 𝔪 hΛ h𝔪
  exact (congLev_open_compact V (isLattice_lat d one_ne_zero hΛ.1) h𝔪).1

end
