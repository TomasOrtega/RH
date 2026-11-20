import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.Henselisation

namespace StageHensel

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Establish `h1 : EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (hij.choose a)` using `Localization.localRingHom_to_map _ _ _ _ _`. Rewrite using `[h1]`. Establish `key : (IsScalarTower.toAlgHom R j.A j.B).comp hij.choose = (IsScalarTower.toAlgHom R j.A j.B).comp φ`. Apply `GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq` to reduce the goal to its premises. Introduce `x`.

Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]`. Use `show _ ∈ RingHom.ker j.pt`. Rewrite using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `(congr($(hij.choose_spec) x)).trans (congr($hφ x)).symm`.

Conclude with `congr($key a)`.
-/
theorem trans_algebraMap_eq_of_comp {i j : EtNbhd R} (hij : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  have h1 : EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (hij.choose a) :=
    Localization.localRingHom_to_map _ _ _ _ _
  rw [h1]
  have key : (IsScalarTower.toAlgHom R j.A j.B).comp hij.choose =
      (IsScalarTower.toAlgHom R j.A j.B).comp φ := by
    apply GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq
    intro x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub,
      IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($(hij.choose_spec) x)).trans (congr($hφ x)).symm
  exact congr($key a)

end StageHensel

open StageHensel in

/- English proof (translation)
Set `P : StandardEtalePair i.A` to `⟨h, hm, derivative h, ⟨1, 0, 1, by simp⟩⟩`. Use `letI : Algebra R P.Ring := ((algebraMap i.A P.Ring).comp (algebraMap R i.A)).toAlgebra`. Use `haveI : IsScalarTower R i.A P.Ring := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.Etale R P.Ring := Algebra.Etale.comp R i.A P.Ring`. Use `letI : Algebra i.A (ResidueField R) := (i.pt : i.A →+* ResidueField R).toAlgebra`.

Use `haveI : IsScalarTower R i.A (ResidueField R) := IsScalarTower.of_algebraMap_eq' (i.pt.comp_algebraMap).symm`. Establish `hmap : P.HasMap (i.pt a₀)`. Prove the components needed by the constructor for the conclusion. Use `show eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) h = 0`. Rewrite using `[eval₂_at_apply]`.

Conclude with `h0`. Use `show IsUnit (eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) (derivative h))`. Rewrite using `[eval₂_at_apply]`. Conclude with `isUnit_iff_ne_zero.2 h1`. Set `x : P.Ring →ₐ[R] ResidueField R` to `(P.lift _ hmap).restrictScalars R`.

Establish `hxA : ∀ a : i.A, x (algebraMap i.A P.Ring a) = i.pt a` using `fun a => (P.lift _ hmap).commutes a`. Establish `hxX : x P.X = i.pt a₀` using `P.lift_X _ hmap`. Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R P.Ring)`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hf`. Set `j : EtNbhd R` to `⟨n, RingHom.ker f, Algebra.Etale.of_equiv e.symm, x.comp (e : _ →ₐ[R] P.Ring)⟩`.

Establish `hjpt : ∀ y : P.Ring, j.pt (e.symm y) = x y` using `fun y => by show x (e (e.symm y)) = x y`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Set `φ : i.A →ₐ[R] j.A` to `(e.symm : P.Ring →ₐ[R] j.A).comp (IsScalarTower.toAlgHom R i.A P.Ring)`. Establish `hφa : ∀ a, φ a = e.symm (algebraMap i.A P.Ring a)` using `fun a => rfl`. Establish `hφ : j.pt.comp φ = i.pt` using `AlgHom.ext fun a => by`.

Rewrite using `[AlgHom.comp_apply, hφa, hjpt, hxA]`. Use `⟨j, ⟨φ, hφ⟩, algebraMap j.A j.B (e.symm P.X), ?_, ?_⟩` and prove the remaining obligations. Establish `hc : (EtNbhd.trans (⟨φ, hφ⟩ : i ≤ j)).comp (algebraMap i.A i.B) = ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring)` using `RingHom.ext fun a => by`. Rewrite using `[RingHom.comp_apply, trans_algebraMap_eq_of_comp _ φ hφ, hφa]`. Both sides reduce to the same expression.

Rewrite using `[hc, IsRoot, eval_map]`. Establish `hX` using `(StandardEtalePair.hasMap_X (P := P)).1`. Rewrite `hX` using `[aeval_def]`. Establish `: eval₂ (((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring)) (algebraMap j.A j.B (e.symm P.X)) h = ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)) (eval₂ (algebraMap i.A P.Ring) P.X h)`. Rewrite using `[hom_eval₂]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `_ = (0 : j.B)`. Rewrite using `[show eval₂ (algebraMap i.A P.Ring) P.X h = 0 from hX, map_zero]`. Use `haveI : j.q.IsPrime := RingHom.ker_isPrime _`.

Rewrite using `[trans_algebraMap_eq_of_comp _ φ hφ, ← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]`. Use `show _ ∈ RingHom.ker j.pt`. Rewrite using `[RingHom.mem_ker, map_sub, hjpt, hxX, sub_eq_zero]`. Conclude with `(congr($hφ a₀)).symm`.
-/
theorem exists_le_isRoot_of_simple_root (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R)
    (h : Polynomial i.A) (a₀ : i.A) (hm : h.Monic) (h0 : i.pt (h.eval a₀) = 0)
    (h1 : i.pt (h.derivative.eval a₀) ≠ 0) :
    ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B),
      (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧
      c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  let P : StandardEtalePair i.A := ⟨h, hm, derivative h, ⟨1, 0, 1, by simp⟩⟩
  letI : Algebra R P.Ring := ((algebraMap i.A P.Ring).comp (algebraMap R i.A)).toAlgebra
  haveI : IsScalarTower R i.A P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale R P.Ring := Algebra.Etale.comp R i.A P.Ring
  letI : Algebra i.A (ResidueField R) := (i.pt : i.A →+* ResidueField R).toAlgebra
  haveI : IsScalarTower R i.A (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' (i.pt.comp_algebraMap).symm
  have hmap : P.HasMap (i.pt a₀) := by
    constructor
    · show eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) h = 0
      rw [eval₂_at_apply]
      exact h0
    · show IsUnit (eval₂ (i.pt : i.A →+* ResidueField R)
        ((i.pt : i.A →+* ResidueField R) a₀) (derivative h))
      rw [eval₂_at_apply]
      exact isUnit_iff_ne_zero.2 h1
  let x : P.Ring →ₐ[R] ResidueField R := (P.lift _ hmap).restrictScalars R
  have hxA : ∀ a : i.A, x (algebraMap i.A P.Ring a) = i.pt a := fun a => (P.lift _ hmap).commutes a
  have hxX : x P.X = i.pt a₀ := P.lift_X _ hmap
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R P.Ring)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let j : EtNbhd R := ⟨n, RingHom.ker f, Algebra.Etale.of_equiv e.symm, x.comp (e : _ →ₐ[R] P.Ring)⟩
  have hjpt : ∀ y : P.Ring, j.pt (e.symm y) = x y := fun y => by
    show x (e (e.symm y)) = x y
    rw [AlgEquiv.apply_symm_apply]
  let φ : i.A →ₐ[R] j.A := (e.symm : P.Ring →ₐ[R] j.A).comp (IsScalarTower.toAlgHom R i.A P.Ring)
  have hφa : ∀ a, φ a = e.symm (algebraMap i.A P.Ring a) := fun a => rfl
  have hφ : j.pt.comp φ = i.pt := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hφa, hjpt, hxA]
  refine ⟨j, ⟨φ, hφ⟩, algebraMap j.A j.B (e.symm P.X), ?_, ?_⟩
  · have hc : (EtNbhd.trans (⟨φ, hφ⟩ : i ≤ j)).comp (algebraMap i.A i.B) =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring) :=
      RingHom.ext fun a => by
        rw [RingHom.comp_apply, trans_algebraMap_eq_of_comp _ φ hφ, hφa]
        rfl
    rw [hc, IsRoot, eval_map]
    have hX := (StandardEtalePair.hasMap_X (P := P)).1
    rw [aeval_def] at hX
    have : eval₂ (((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp
        (algebraMap i.A P.Ring)) (algebraMap j.A j.B (e.symm P.X)) h =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)) (eval₂ (algebraMap i.A P.Ring) P.X h) := by
      rw [hom_eval₂]
      rfl
    rw [this]
    change _ = (0 : j.B)
    rw [show eval₂ (algebraMap i.A P.Ring) P.X h = 0 from hX, map_zero]
  · haveI : j.q.IsPrime := RingHom.ker_isPrime _
    rw [trans_algebraMap_eq_of_comp _ φ hφ, ← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, hjpt, hxX, sub_eq_zero]
    exact (congr($hφ a₀)).symm

end GlobalTheory.Henselisation

end
