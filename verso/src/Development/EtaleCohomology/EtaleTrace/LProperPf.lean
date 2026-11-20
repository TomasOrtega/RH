import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LProperPf

open LateralTheory.EtaleTrace

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨p, hp⟩`.

Use `⟨p.coeff 0, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hp2` using `hp`. Rewrite `hp2` using `[MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous, MvPolynomial.totalDegree_eq_zero_iff_eq_C]`. Express the relevant statement in the definitionally equal form `_ = p`. Use `conv_rhs => rw [hp2]`.

Both sides reduce to the same expression.
-/
theorem bij (k : Type) [Field k] (N : ℕ) :
    Function.Bijective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    simpa using this
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    have hp2 := hp
    rw [MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp2
    change _ = p
    conv_rhs => rw [hp2]
    rfl

instance tower (k : Type) [Field k] (N : ℕ) :
    IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance ft (k : Type) [Field k] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

/- English proof (translation)
Introduce `k _ N`. Establish `hi : IsIso (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))` using `(ConcreteCategory.isIso_iff_bijective _).mpr (bij k N)`. Unfold `PNto`. Use `infer_instance`.
-/
theorem LProper_of : LPdCut.LProper := by
  intro k _ N
  have hi : IsIso (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bij k N)
  unfold PNto
  infer_instance

end LateralTheory.EtaleTrace.LProperPf
