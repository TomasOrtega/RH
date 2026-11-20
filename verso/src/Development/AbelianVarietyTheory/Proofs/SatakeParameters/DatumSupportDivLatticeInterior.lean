import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.Proof.datum_support_div_lattice_interior

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h` and prove the remaining obligations. Simplify using `using IntAt.coe P 0`.
-/
theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h
  simpa using IntAt.coe P 0

/- English proof (translation)
Introduce `y hy`. Take `⟨z, rfl⟩` from `f.surjective y`. Establish `hz : ∀ i, IntAt P (z i)` using `(mem_localization_standardLattice P z).1 ((hf z).1 hy)`. Establish `e : c • x (f z) = f' (c • inFr f f' x z)` using `by simp [inFr]`. Rewrite using `[e, hf']`.

Use `(mem_localization_standardLattice P _).2 fun l => ?_` and prove the remaining obligations. Establish `hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l)` using `by conv_lhs => rw [hz']`.

Simplify using `only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => by ring`. Rewrite using `[e2]`. Conclude with `intAt_sum _ _ fun s _ => (hz s).mul (h s l)`.
-/
theorem smul_mem_of_frames {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E a))
    (M' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ x, f x ∈ M ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) (c : E) (h : ∀ s l, IntAt P (c * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ M, c • x y ∈ M' := by
  classical
  intro y hy
  obtain ⟨z, rfl⟩ := f.surjective y
  have hz : ∀ i, IntAt P (z i) := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
  have e : c • x (f z) = f' (c • inFr f f' x z) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l) := by
    conv_lhs => rw [hz']
    simp only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2]
  exact intAt_sum _ _ fun s _ => (hz s).mul (h s l)

end General

end GlobalTheory.Proof.datum_support_div_lattice_interior
