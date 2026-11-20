import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

open IsLocalRing Polynomial in
/- English proof (translation)
Rewrite using `[eval_map, hom_eval₂, eval₂_map]`. Use `congr 1`.
-/
private lemma residue_eval_map_eq {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    residue R ((P.map φ).eval x) =
      (P.map (residue A)).eval₂ (ResidueField.map φ) (residue R x) := by
  rw [eval_map, hom_eval₂, eval₂_map]
  congr 1

open IsLocalRing Polynomial in

/- English proof (translation)
Introduce `A R _ _ _ _ _ φ _ hfin hunr`. Establish `hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A)` using `RingHom.ext fun a => (ResidueField.map_residue φ a).symm`. Rewrite `hfin`, `hunr` using `[hcomp]`. Use `letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra`. Use `haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite`.

Use `haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp`. Use `haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) := Algebra.FormallyUnramified.isSeparable _ _`. Use `set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)`. Use `set f := minpoly (ResidueField A) pb.gen with hf`. Establish `hfmonic : f.Monic` using `minpoly.monic pb.isIntegral_gen`.

Establish `hfroot : aeval pb.gen f = 0` using `minpoly.aeval _ _`. Establish `hfder : aeval pb.gen (derivative f) ≠ 0` using `(Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot`. Take `⟨q, hqf, hqdeg, hqmonic⟩` from `lifts_and_natDegree_eq_and_monic ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic`. Take `⟨θ₀, hθ₀⟩` from `residue_surjective pb.gen`. Establish `key : ∀ (P : A[X]) (x : R), residue R x = pb.gen → residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A))`.

Introduce `P x hx`. Rewrite using `[residue_eval_map_eq, hx]`. Both sides reduce to the same expression. Take `⟨θ, hroot, hθ⟩` from `HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ) (hqmonic.map φ) θ₀ (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot]) (by`. Rewrite using `[derivative_map]`.

Express the relevant statement in the definitionally equal form `IsUnit (residue R _)`. Rewrite using `[key _ _ hθ₀, ← derivative_map, hqf]`. Conclude with `isUnit_iff_ne_zero.2 hfder)`. Establish `hθres : residue R θ = pb.gen`. Rewrite using `[← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`.

Conclude with `hθ`. Use `⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]`. Conclude with `hfder`. Introduce `r`.

Take `⟨g, hg⟩` from `pb.exists_eq_aeval' (residue R r)`. Take `⟨P, hP⟩` from `map_surjective (residue A) residue_surjective g`. Use `⟨P, ?_⟩` and prove the remaining obligations. Rewrite using `[← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]`. Introduce `P hdeg hmem i`.

Rewrite `hmem` using `[← residue_eq_zero_iff, key _ _ hθres]`. Establish `hzero : P.map (residue A) = 0`. Assume the negation of the conclusion as `hne`. Establish `h1` using `minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem`. Establish `h2` using `natDegree_le_natDegree h1`.

Establish `h3 : (P.map (residue A)).natDegree ≤ P.natDegree` using `natDegree_map_le`. Rewrite `h2` using `[← hf, ← hqdeg]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]`.
-/
theorem _root_.GlobalTheory.exists_hensel_generator_of_residue_finite_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hunr
  have hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A) :=
    RingHom.ext fun a => (ResidueField.map_residue φ a).symm
  rw [hcomp] at hfin hunr
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite
  haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)
  set f := minpoly (ResidueField A) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfroot : aeval pb.gen f = 0 := minpoly.aeval _ _
  have hfder : aeval pb.gen (derivative f) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot
  obtain ⟨q, hqf, hqdeg, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective pb.gen
  have key : ∀ (P : A[X]) (x : R), residue R x = pb.gen →
      residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A)) := by
    intro P x hx
    rw [residue_eval_map_eq, hx]
    rfl
  obtain ⟨θ, hroot, hθ⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ)
    (hqmonic.map φ) θ₀
    (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot])
    (by
      rw [derivative_map]
      change IsUnit (residue R _)
      rw [key _ _ hθ₀, ← derivative_map, hqf]
      exact isUnit_iff_ne_zero.2 hfder)
  have hθres : residue R θ = pb.gen := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hθ
  refine ⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]
    exact hfder
  · intro r
    obtain ⟨g, hg⟩ := pb.exists_eq_aeval' (residue R r)
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective g
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, key _ _ hθres] at hmem
    have hzero : P.map (residue A) = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem
      have h2 := natDegree_le_natDegree h1
      have h3 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hf, ← hqdeg] at h2
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]

end GlobalTheory
