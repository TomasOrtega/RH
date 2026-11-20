import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreIdeal

variable {n : ℕ}

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := by rcases p with ⟨⟨⟩, i⟩; rfl

def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv

/- English proof (translation)
Rewrite using `[Ideal.map_symm]`. Conclude with `Ideal.ext fun _ => Iff.rfl`.
-/
theorem finIdeal_eq_map (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.map (blkRingEquiv n).symm := by
  rw [Ideal.map_symm]
  exact Ideal.ext fun _ => Iff.rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Use `show MvPolynomial.map (algebraMap ℤ ℚ) = _`. Rewrite using `[RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]`.
-/
theorem algebraMap_eq :
    algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
  show MvPolynomial.map (algebraMap ℤ ℚ) = _
  rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]

abbrev intUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

instance : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) :=
  MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ

/- English proof (translation)
Take `⟨-, ⟨hprime, -, -⟩, hhor, -⟩` from `hP`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hprime` as an intermediate fact. Conclude with `Ideal.comap_isPrime _ _`. Use `Set.disjoint_left.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, rfl⟩ hx`. Establish `h1 : (C a : MRing (PBlk n)) ∈ P`. Simplify `hx` using `[IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap]`. Establish `h2 : a ∈ P.comap (C : ℤ →+* MRing (PBlk n))` using `h1`. Rewrite `h2` using `[hhor, Ideal.mem_bot]`.

Conclude with `nonZeroDivisors.ne_zero ha h2`.
-/
theorem finIdeal_isPrime_disjoint (n d : ℕ) (P : Ideal (MRing (PBlk n))) (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime ∧
      Disjoint ((intUnits n : Set (MvPolynomial (Fin n) ℤ))) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  refine ⟨?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hx
    have h1 : (C a : MRing (PBlk n)) ∈ P := by
      simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hx
    have h2 : a ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
    rw [hhor, Ideal.mem_bot] at h2
    exact nonZeroDivisors.ne_zero ha h2

section Homog

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Take `⟨S, hS, hPS⟩` from `hP`. Establish `hH : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ)`. Rewrite using `[genericIdeal, finIdeal_eq_map, hPS, Ideal.map_span, Ideal.map_span]`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨s, hs, rfl⟩, rfl⟩`.

Take `⟨a, ha⟩` from `hS s hs`. Use `⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩` and prove the remaining obligations. Establish `hs' : s.IsHomogeneous (a ())`. Introduce `m hm`. Express the relevant statement in the definitionally equal form `Finsupp.weight (fun _ => 1) m = a ()`.

Rewrite using `[← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]`. Simplify using `using ha m (mem_support_iff.mpr hm) ()`. Conclude with `(IsHomogeneous.rename_isHomogeneous hs').map _`. Introduce `f hf k`. Conclude with `homogeneousComponent_mem_of_mem hH hf k`.
-/
theorem genericIdeal_isHomogIdeal (P : Ideal (MRing (PBlk n)))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P) : IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, hPS⟩ := hP
  have hH : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [genericIdeal, finIdeal_eq_map, hPS, Ideal.map_span, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    refine ⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩
    have hs' : s.IsHomogeneous (a ()) := by
      intro m hm
      change Finsupp.weight (fun _ => 1) m = a ()
      rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
      simpa using ha m (mem_support_iff.mpr hm) ()
    exact (IsHomogeneous.rename_isHomogeneous hs').map _
  intro f hf k
  exact homogeneousComponent_mem_of_mem hH hf k

end Homog

/- English proof (translation)
Introduce `n d P hP`. Take `⟨hQprime, hdisj⟩` from `finIdeal_isPrime_disjoint n d P hP`. Establish `hgen : genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ))`. Rewrite using `[algebraMap_eq]`. Both sides reduce to the same expression.

Establish `hsat : (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = IndefiniteRowSideFullHecke.ArithBezout.finIdeal P`. Rewrite using `[hgen, ← algebraMap_eq]`. Conclude with `IsLocalization.under_map_of_isPrime_disjoint (intUnits n) _ hQprime hdisj`. Take `⟨-, ⟨-, ⟨S, hS, hPS⟩, hrel⟩, -, -⟩` from `hP`. Use `⟨⟨?_, ?_, ?_⟩, hsat⟩` and prove the remaining obligations.

Rewrite using `[hgen]`. Conclude with `IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ _ hQprime hdisj`. Conclude with `genericIdeal_isHomogIdeal P ⟨S, hS, hPS⟩`. Take `⟨i, hi⟩` from `hrel ()`. Use `⟨i, fun hX => hi ?_⟩` and prove the remaining obligations.

Establish `hmem : (X i : MvPolynomial (Fin n) ℤ) ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P`. Rewrite using `[← hsat, Ideal.mem_comap, map_X]`. Conclude with `hX`. Simplify `hmem` using `[IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap]`.
-/
theorem proof : GenericFibreIdeal.Statement := by
  intro n d P hP
  obtain ⟨hQprime, hdisj⟩ := finIdeal_isPrime_disjoint n d P hP
  have hgen : genericIdeal P =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
        (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
    rw [algebraMap_eq]; rfl
  have hsat : (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) =
      IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [hgen, ← algebraMap_eq]
    exact IsLocalization.under_map_of_isPrime_disjoint (intUnits n) _ hQprime hdisj
  obtain ⟨-, ⟨-, ⟨S, hS, hPS⟩, hrel⟩, -, -⟩ := hP
  refine ⟨⟨?_, ?_, ?_⟩, hsat⟩
  · rw [hgen]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ _ hQprime hdisj
  · exact genericIdeal_isHomogIdeal P ⟨S, hS, hPS⟩
  ·
    obtain ⟨i, hi⟩ := hrel ()
    refine ⟨i, fun hX => hi ?_⟩
    have hmem : (X i : MvPolynomial (Fin n) ℤ) ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
      rw [← hsat, Ideal.mem_comap, map_X]
      exact hX
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hmem

end GenericFibreIdeal

end ObjectsChow

end GroundTheory.Heights₂.Heights
