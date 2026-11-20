import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial DirectSum

noncomputable section

universe u

section QuotDecomposition

variable {ι R A : Type*} [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [Decomposition 𝒜] (I : Ideal A)

def quotPieces (n : ι) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [DecidableEq ι] [Decomposition 𝒜] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨a, ha, rfl⟩`.
-/
theorem mk_mem_quotPieces {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotPieces 𝒜 I n :=
  ⟨a, ha, rfl⟩

def quotPieceMap (n : ι) : 𝒜 n →+ quotPieces 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotPieces 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def quotientDecomposition : A →+ ⨁ n, quotPieces 𝒜 I n :=
  (DirectSum.map (quotPieceMap 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable {𝒜 I}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotientDecomposition_apply (a : A) : quotientDecomposition 𝒜 I a =
    DirectSum.map (quotPieceMap 𝒜 I) (DirectSum.decompose 𝒜 a) := rfl

/- English proof (translation)
Use extensionality with `n`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hI n a ha`.
-/
theorem quotientDecomposition_of_mem_ideal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) {a : A}
    (ha : a ∈ I) : quotientDecomposition 𝒜 I a = 0 := by
  ext n
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI n a ha

omit [Decomposition 𝒜] in
/- English proof (translation)
Use extensionality with `n x`. Simplify using `[DirectSum.map_of, quotPieceMap]`.
-/
theorem coe_comp_map_quotPieceMap :
    (DirectSum.coeAddMonoidHom (quotPieces 𝒜 I)).comp (DirectSum.map (quotPieceMap 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  ext n x
  simp [DirectSum.map_of, quotPieceMap]

/- English proof (translation)
Rewrite using `[quotientDecomposition_apply]`. Use `congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotPieceMap (𝒜 := 𝒜) (I := I))` as an intermediate fact. Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply] at this`. Rewrite using `[this]`. Conclude with `congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)`.
-/
theorem coe_quotientDecomposition (a : A) :
    DirectSum.coeAddMonoidHom (quotPieces 𝒜 I) (quotientDecomposition 𝒜 I a) = Ideal.Quotient.mk I a := by
  rw [quotientDecomposition_apply]
  have := congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotPieceMap (𝒜 := 𝒜) (I := I))
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

/- English proof (translation)
Rewrite using `[quotientDecomposition_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]`. Both sides reduce to the same expression.
-/
theorem quotientDecomposition_of_mem_piece {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    quotientDecomposition 𝒜 I a = DirectSum.of (fun n => quotPieces 𝒜 I n) n
      ⟨Ideal.Quotient.mk I a, mk_mem_quotPieces 𝒜 I ha⟩ := by
  rw [quotientDecomposition_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

def quotDecomp (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    A ⧸ I →+ ⨁ n, quotPieces 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (quotientDecomposition 𝒜 I)
    (fun _ ha => AddMonoidHom.mem_ker.mpr (quotientDecomposition_of_mem_ideal hI ha))

@[instance_reducible]
def quotDecomposition (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    Decomposition (quotPieces 𝒜 I) where
  decompose' := quotDecomp hI
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact coe_quotientDecomposition a
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n q =>
      obtain ⟨q, a, ha, rfl⟩ := q
      rw [DirectSum.coeAddMonoidHom_of]
      exact quotientDecomposition_of_mem_piece ha
    | add d e hd he => rw [map_add, map_add, hd, he]

/- English proof (translation)
The claim follows from `letI := quotDecomposition hI Decomposition.isInternal _`.
-/
theorem quotPieces_isInternal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    IsInternal (quotPieces 𝒜 I) :=
  letI := quotDecomposition hI
  Decomposition.isInternal _

end QuotDecomposition

section PolyQuot

variable {S : Type u} [CommRing S] {N : ℕ}

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Simplify using `only [Finsupp.sum, nsmul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `_ = ((∑ i ∈ d.support, d i : ℕ) : ℤ)`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem weight_one_int (d : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = (d.degree : ℤ) := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, nsmul_eq_mul, mul_one]
  change _ = ((∑ i ∈ d.support, d i : ℕ) : ℤ)
  push_cast
  rfl

/- English proof (translation)
Introduce `d hd`. Establish `h1` using `hf hd`. Rewrite `h1` using `[weight_one_int]`. Establish `h2 : Finsupp.weight (1 : Fin (N + 1) → ℕ) d = d.degree`. Rewrite using `[Finsupp.degree_eq_weight_one]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `h1` after adjusting the coercions.
-/
theorem isHomogeneous_of_isWeightedHomogeneous_one {f : Poly S N} {n : ℕ}
    (hf : IsWeightedHomogeneous (fun _ => (1 : ℤ)) f (n : ℤ)) : f.IsHomogeneous n := by
  intro d hd
  have h1 := hf hd
  rw [weight_one_int] at h1
  have h2 : Finsupp.weight (1 : Fin (N + 1) → ℕ) d = d.degree := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [h2]
  exact_mod_cast h1

/- English proof (translation)
Distinguish the cases in `hc : 0 ≤ c`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hc`. Establish `: weightedHomogeneousComponent (fun _ => (1 : ℤ)) (k : ℤ) f = homogeneousComponent k f`. Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_one_int]`.

Simplify using `only [Nat.cast_inj]`. Rewrite using `[this]`. Conclude with `hp f hf k`. Establish `: weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f = 0`. Use extensionality with `d`.

Rewrite using `[coeff_weightedHomogeneousComponent, weight_one_int, coeff_zero]`. Use `split_ifs with h`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `p.zero_mem`.
-/
theorem weightedHomogeneousComponent_one_mem {p : Ideal (Poly S N)}
    (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) (c : ℤ) {f : Poly S N} (hf : f ∈ p) :
    weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f ∈ p := by
  by_cases hc : 0 ≤ c
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) (k : ℤ) f = homogeneousComponent k f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_one_int]
      simp only [Nat.cast_inj]
    rw [this]
    exact hp f hf k
  · have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f = 0 := by
      ext d
      rw [coeff_weightedHomogeneousComponent, weight_one_int, coeff_zero]
      split_ifs with h
      · omega
      · rfl
    rw [this]
    exact p.zero_mem

def quotGraded (p : Ideal (Poly S N)) (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) :
    GradedPMod S N (Poly S N ⧸ p) where
  piece := quotPieces (weightedHomogeneousSubmodule S (fun _ : Fin (N + 1) => (1 : ℤ))) p
  isInternal := by
    classical
    let _ := weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))
    refine quotPieces_isInternal fun n a ha => ?_
    have h := weightedDecomposition.decompose'_apply S (fun _ : Fin (N + 1) => (1 : ℤ)) a n
    change ((weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))).decompose' a n :
      Poly S N) ∈ p
    rw [h]
    exact weightedHomogeneousComponent_one_mem hp n ha
  smul_mem d c q m hq hm := by
    obtain ⟨f, hf, rfl⟩ := hm
    refine ⟨q * f, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule, add_comm c (d : ℤ)]
      exact (isWeightedHomogeneous_int_of_isHomogeneous hq).mul hf
    · change Ideal.Quotient.mk p (q * f) = q • Ideal.Quotient.mk p f
      rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, hf, rfl⟩`. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, hf, rfl⟩`.
-/
theorem mem_quotGraded_piece {p : Ideal (Poly S N)} {hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p}
    {c : ℤ} {m : Poly S N ⧸ p} :
    m ∈ (quotGraded p hp).piece c ↔ ∃ f : Poly S N,
      IsWeightedHomogeneous (fun _ => (1 : ℤ)) f c ∧ Ideal.Quotient.mk p f = m := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

/- English proof (translation)
The claim follows from `Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Poly S N) p).toLinearMap Ideal.Quotient.mk_surjective`.
-/
theorem finite_quot (p : Ideal (Poly S N)) : Module.Finite (Poly S N) (Poly S N ⧸ p) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Poly S N) p).toLinearMap
    Ideal.Quotient.mk_surjective

end PolyQuot

end

end GroundTheory.Heights₂.Heights.Kleiman
