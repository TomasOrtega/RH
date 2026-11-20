import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceNormOneCompactSupportStatement

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.TwoQ

section Gen

variable {F : Type} [Field F] {d β : F} {R T : Type} [CommRing R] [Algebra F R] [CommRing T]
  (ι : R →+* T) (h : T)

def th (x : Q d β R) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * h, ι (algebraMap F R β) * (ι x.imJ + ι x.imK * h);
     ι x.imJ - ι x.imK * h, ι x.re - ι x.imI * h]

variable {ι h}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[th, Matrix.mul_apply, Fin.sum_univ_two, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]`. Take the linear combination `(-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh`. Take the linear combination `(-ι (algebraMap F R β)) * (ι x.imI * ι y.imK - ι x.imK * ι y.imI) * hh`.

Take the linear combination `(-(ι x.imI * ι y.imK - ι x.imK * ι y.imI)) * hh`. Take the linear combination `(-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh`.
-/
theorem th_mul (hh : h * h = ι (algebraMap F R d)) (x y : Q d β R) :
    th ι h (x * y) = th ι h x * th ι h y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Matrix.mul_apply, Fin.sum_univ_two, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh
  · linear_combination (-ι (algebraMap F R β)) * (ι x.imI * ι y.imK - ι x.imK * ι y.imI) * hh
  · linear_combination (-(ι x.imI * ι y.imK - ι x.imK * ι y.imI)) * hh
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [th]`.
-/
theorem th_one : th ι h (1 : Q d β R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

/- English proof (translation)
Simplify using `only [th, Matrix.det_fin_two_of, qn, map_add, map_sub, map_mul, map_pow]`. Take the linear combination `(-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh`.
-/
theorem th_det (hh : h * h = ι (algebraMap F R d)) (x : Q d β R) : (th ι h x).det = ι (qn x) := by
  simp only [th, Matrix.det_fin_two_of, qn, map_add, map_sub, map_mul, map_pow]
  linear_combination (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh

/- English proof (translation)
Rewrite using `[← th_mul hh, mul_star_eq, hx, map_one, th_one]`.
-/
theorem th_mul_star (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h x * th ι h (star x) = 1 := by
  rw [← th_mul hh, mul_star_eq, hx, map_one, th_one]

/- English proof (translation)
Rewrite using `[← th_mul hh, star_mul_eq, hx, map_one, th_one]`.
-/
theorem th_star_mul (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h (star x) * th ι h x = 1 := by
  rw [← th_mul hh, star_mul_eq, hx, map_one, th_one]

/- English proof (translation)
Establish `hq : ι x.re ^ 2 - ι (algebraMap F R d) * ι x.imI ^ 2 - ι (algebraMap F R β) * ι x.imJ ^ 2 + ι (algebraMap F R d) * ι (algebraMap F R β) * ι x.imK ^ 2 = 1`. Use `congrArg ι hx` as an intermediate fact. Simplify `this` using `[qn]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Simplify using `[th, Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hc, hch]`. Take the linear combination `hq + (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(-ι (algebraMap F R β)) * hq + (-ι (algebraMap F R β)) * (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh`.
-/
theorem th_unitary (hh : h * h = ι (algebraMap F R d)) (c : T →+* T) (hc : ∀ a, c (ι a) = ι a) (hch : c h = -h)
    {x : Q d β R} (hx : qn x = 1) :
    Formalism.UG.cT c (th ι h x) * !![1, 0; 0, -ι (algebraMap F R β)] * th ι h x =
      !![1, 0; 0, -ι (algebraMap F R β)] := by
  have hq : ι x.re ^ 2 - ι (algebraMap F R d) * ι x.imI ^ 2 - ι (algebraMap F R β) * ι x.imJ ^ 2 +
      ι (algebraMap F R d) * ι (algebraMap F R β) * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simpa [qn] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hc, hch]
  · linear_combination hq + (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh
  · ring
  · ring
  · linear_combination (-ι (algebraMap F R β)) * hq +
      (-ι (algebraMap F R β)) * (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh

end Gen

section Coef

variable {T : Type} [CommRing T]

/- English proof (translation)
Establish `hA : M * M.adjugate = 1` using `by rw [Matrix.mul_adjugate, hdet, one_smul]`. Establish `key : Formalism.UG.cT c M * !![1, 0; 0, -B] = !![1, 0; 0, -B] * M.adjugate`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA, Matrix.mul_one]`. Use `_ = !![1, 0; 0, -B] * M.adjugate := by rw [← Matrix.mul_assoc, hM]`.

Establish `e00` using `congrFun (congrFun key 0) 0`. Establish `e01` using `congrFun (congrFun key 0) 1`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] at e00 e01`. Conclude with `⟨e00.symm, by linear_combination -e01⟩`.
-/
theorem entries_of_unitary (c : T →+* T) {B : T} {M : Matrix (Fin 2) (Fin 2) T} (hdet : M.det = 1)
    (hM : Formalism.UG.cT c M * !![1, 0; 0, -B] * M = !![1, 0; 0, -B]) :
    M 1 1 = c (M 0 0) ∧ M 0 1 = B * c (M 1 0) := by
  have hA : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have key : Formalism.UG.cT c M * !![1, 0; 0, -B] = !![1, 0; 0, -B] * M.adjugate := by
    calc Formalism.UG.cT c M * !![1, 0; 0, -B] = Formalism.UG.cT c M * !![1, 0; 0, -B] * (M * M.adjugate) := by
          rw [hA, Matrix.mul_one]
      _ = !![1, 0; 0, -B] * M.adjugate := by rw [← Matrix.mul_assoc, hM]
  have e00 := congrFun (congrFun key 0) 0
  have e01 := congrFun (congrFun key 0) 1
  simp [Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] at e00 e01
  exact ⟨e00.symm, by linear_combination -e01⟩

end Coef

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d β : F} {R : Type} [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `only [inclR]`. Rewrite using `[← IsScalarTower.algebraMap_apply F R (R ⊗[F] E) t]`. Conclude with `Algebra.TensorProduct.includeRight.commutes t`.
-/
theorem incl_alg (t : F) :
    inclR R (algebraMap F E t) = algebraMap R (R ⊗[F] E) (algebraMap F R t) := by
  simp only [inclR]
  rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E) t]
  exact Algebra.TensorProduct.includeRight.commutes t

/- English proof (translation)
Rewrite using `[← map_mul, ← pow_two, hξ, incl_alg]`.
-/
theorem xh_sq {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) :
    inclR (F := F) R ξ * inclR (F := F) R ξ = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  rw [← map_mul, ← pow_two, hξ, incl_alg]

/- English proof (translation)
Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sig_alg (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Simplify using `[sigR, inclR, hσ, TensorProduct.tmul_neg]`.
-/
theorem sig_xh {σ : E →ₐ[F] E} {ξ : E} (hσ : σ ξ = -ξ) :
    sigR R σ (inclR (F := F) R ξ) = -inclR (F := F) R ξ := by
  simp [sigR, inclR, hσ, TensorProduct.tmul_neg]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [JR, J2, incl_alg]`.
-/
theorem hermitian_plane_matrix :
    JR R (J2 E β) = !![1, 0; 0, -algebraMap R (R ⊗[F] E) (algebraMap F R β)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [JR, J2, incl_alg]

abbrev thR (R : Type) [CommRing R] [Algebra F R] (E : Type) [Field E] [Algebra F E] (ξ : E) (x : Q d β R) :
    Matrix (Fin 2) (Fin 2) (R ⊗[F] E) :=
  th (algebraMap R (R ⊗[F] E)) (inclR (F := F) R ξ) x

def toHA (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) (x : Q d β R) (hx : qn x = 1) :
    HA R σ (J2 E β) :=
  (⟨⟨thR R E ξ x, thR R E ξ (star x), th_mul_star (xh_sq hξ) hx, th_star_mul (xh_sq hξ) hx⟩, by
    change Formalism.UG.cT (sigR R σ) (thR R E ξ x) * JR R (J2 E β) * thR R E ξ x = JR R (J2 E β)
    rw [hermitian_plane_matrix]
    exact th_unitary (xh_sq hξ) _ (sig_alg σ) (sig_xh hσ) hx⟩ : HR R σ (J2 E β))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toHA_mat (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) (x : Q d β R)
    (hx : qn x = 1) :
    ((HA.mat R σ (J2 E β) (toHA σ hξ hσ x hx)).1 : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) = thR R E ξ x := rfl

section Basis

variable (b : Module.Basis (Fin 2) F E) {ξ : E}

def co (R : Type) [CommRing R] [Algebra F R] (i : Fin 2) (t : R ⊗[F] E) : R :=
  (Algebra.TensorProduct.basis R b).repr t i

variable {b}

/- English proof (translation)
Establish `h` using `(Algebra.TensorProduct.basis R b).sum_repr t`. Rewrite `h` using `[Fin.sum_univ_two]`. Use `conv_lhs => rw [← h]`. Simplify using `only [Algebra.TensorProduct.basis_apply, hb0, hb1, co, inclR, Algebra.smul_def]`. Simplify using `[Algebra.TensorProduct.one_def]`.
-/
theorem decomp (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (t : R ⊗[F] E) :
    t = algebraMap R (R ⊗[F] E) (co b R 0 t) + algebraMap R (R ⊗[F] E) (co b R 1 t) * inclR (F := F) R ξ := by
  have h := (Algebra.TensorProduct.basis R b).sum_repr t
  rw [Fin.sum_univ_two] at h
  conv_lhs => rw [← h]
  simp only [Algebra.TensorProduct.basis_apply, hb0, hb1, co, inclR, Algebra.smul_def]
  simp [Algebra.TensorProduct.one_def]

/- English proof (translation)
Establish `h : algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F` using `F) R ξ = x • Algebra.TensorProduct.basis R b 0 + y • Algebra.TensorProduct.basis R b 1 := by`. Simplify using `only [Algebra.TensorProduct.basis_apply, hb0, hb1, inclR, Algebra.smul_def]`. Simplify using `[Algebra.TensorProduct.one_def]`. Simplify using `only [co, h, map_add, map_smul, Module.Basis.repr_self]`. Simplify using the standard rewrite rules.
-/
theorem co_emb (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (x y : R) :
    co b R 0 (algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ) = x ∧
    co b R 1 (algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ) = y := by
  have h : algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ =
      x • Algebra.TensorProduct.basis R b 0 + y • Algebra.TensorProduct.basis R b 1 := by
    simp only [Algebra.TensorProduct.basis_apply, hb0, hb1, inclR, Algebra.smul_def]
    simp [Algebra.TensorProduct.one_def]
  simp only [co, h, map_add, map_smul, Module.Basis.repr_self]
  simp

/- English proof (translation)
Establish `h1` using `(co_emb (R := R) hb0 hb1 x 0).1`. Establish `h2` using `(co_emb (R := R) hb0 hb1 y 0).1`. Simplify using `only [map_zero, zero_mul, add_zero] at h1 h2`. Rewrite using `[← h1, ← h2, h]`.
-/
theorem alg_inj (hb0 : b 0 = 1) (hb1 : b 1 = ξ) {x y : R}
    (h : algebraMap R (R ⊗[F] E) x = algebraMap R (R ⊗[F] E) y) : x = y := by
  have h1 := (co_emb (R := R) hb0 hb1 x 0).1
  have h2 := (co_emb (R := R) hb0 hb1 y 0).1
  simp only [map_zero, zero_mul, add_zero] at h1 h2
  rw [← h1, ← h2, h]

/- English proof (translation)
Use `set M : Matrix (Fin 2) (Fin 2) (R ⊗[F] E) := (HA.mat R σ (J2 E β) g).1 with hMdef`. Establish `hU : Formalism.UG.cT (sigR R σ) M * JR R (J2 E β) * M = JR R (J2 E β)` using `(show (g : HR R σ (J2 E β)).1 ∈ HR R σ (J2 E β) from g.2)`. Rewrite `hU` using `[hermitian_plane_matrix]`. Take `⟨h11, h01⟩` from `entries_of_unitary _ hdet hU`. Use `set ι := algebraMap R (R ⊗[F] E) with hι`.

Use `set h := inclR (F := F) R ξ with hh`. Establish `hA` using `decomp (R := R) hb0 hb1 (M 0 0)`. Establish `hC` using `decomp (R := R) hb0 hb1 (M 1 0)`. Establish `hsa : ∀ u v : R, sigR R σ (ι u + ι v * h) = ι u - ι v * h`. Introduce `u v`.

Rewrite using `[map_add, map_mul, sig_alg, sig_alg, sig_xh hσ]`. Expand and normalize the polynomial expressions, which then agree. Set `x : Q d β R` to `⟨co b R 0 (M 0 0), co b R 1 (M 0 0), co b R 0 (M 1 0), -co b R 1 (M 1 0)⟩`. Establish `hthx : thR R E ξ x = M`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `hA.symm` using `[th, x]`. Use `show ι (algebraMap F R β) * (ι (co b R 0 (M 1 0)) + ι (-co b R 1 (M 1 0)) * h) = M 0 1`. Rewrite using `[h01]`. Use `conv_rhs => rw [hC, hsa]`.

Rewrite using `[map_neg]`. Expand and normalize the polynomial expressions, which then agree. Use `show ι (co b R 0 (M 1 0)) - ι (-co b R 1 (M 1 0)) * h = M 1 0 conv_rhs => rw [hC]`. Rewrite using `[map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Use `show ι (co b R 0 (M 0 0)) - ι (co b R 1 (M 0 0)) * h = M 1 1`. Rewrite using `[h11]`. Use `conv_rhs => rw [hA, hsa]`. Establish `hq : qn x = 1`. Apply `alg_inj (E := E) hb0 hb1` to reduce the goal to its premises.

Rewrite using `[map_one, ← th_det (xh_sq hξ), show th _ _ x = M from hthx, hdet]`. Use `⟨x, hq, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hthx.symm`.
-/
theorem exists_of_mem (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E) (hξ : ξ ^ 2 = algebraMap F E d)
    (hσ : σ ξ = -ξ) (g : HA R σ (J2 E β))
    (hdet : ((HA.mat R σ (J2 E β) g).1 : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)).det = 1) :
    ∃ (x : Q d β R) (hx : qn x = 1), g = toHA σ hξ hσ x hx := by
  set M : Matrix (Fin 2) (Fin 2) (R ⊗[F] E) := (HA.mat R σ (J2 E β) g).1 with hMdef
  have hU : Formalism.UG.cT (sigR R σ) M * JR R (J2 E β) * M = JR R (J2 E β) := (show (g : HR R σ (J2 E β)).1 ∈ HR R σ (J2 E β) from g.2)
  rw [hermitian_plane_matrix] at hU
  obtain ⟨h11, h01⟩ := entries_of_unitary _ hdet hU
  set ι := algebraMap R (R ⊗[F] E) with hι
  set h := inclR (F := F) R ξ with hh
  have hA := decomp (R := R) hb0 hb1 (M 0 0)
  have hC := decomp (R := R) hb0 hb1 (M 1 0)
  have hsa : ∀ u v : R, sigR R σ (ι u + ι v * h) = ι u - ι v * h := by
    intro u v
    rw [map_add, map_mul, sig_alg, sig_alg, sig_xh hσ]; ring
  let x : Q d β R := ⟨co b R 0 (M 0 0), co b R 1 (M 0 0), co b R 0 (M 1 0), -co b R 1 (M 1 0)⟩
  have hthx : thR R E ξ x = M := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [th, x] using hA.symm
    · show ι (algebraMap F R β) * (ι (co b R 0 (M 1 0)) + ι (-co b R 1 (M 1 0)) * h) = M 0 1
      rw [h01]
      conv_rhs => rw [hC, hsa]
      rw [map_neg]; ring
    · show ι (co b R 0 (M 1 0)) - ι (-co b R 1 (M 1 0)) * h = M 1 0
      conv_rhs => rw [hC]
      rw [map_neg]; ring
    · show ι (co b R 0 (M 0 0)) - ι (co b R 1 (M 0 0)) * h = M 1 1
      rw [h11]
      conv_rhs => rw [hA, hsa]
  have hq : qn x = 1 := by
    apply alg_inj (E := E) hb0 hb1
    rw [map_one, ← th_det (xh_sq hξ), show th _ _ x = M from hthx, hdet]
  refine ⟨x, hq, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hthx.symm

end Basis

end Tens

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d β : F}

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))`. Establish `a0 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.re` using `hι.comp continuous_re`. Establish `a1 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imI` using `hι.comp continuous_imI`.

Establish `a2 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imJ` using `hι.comp continuous_imJ`. Establish `a3 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imK` using `hι.comp continuous_imK`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `a0.add (a1.mul continuous_const)`.

Conclude with `continuous_const.mul (a2.add (a3.mul continuous_const))`. Conclude with `a2.sub (a3.mul continuous_const)`. Conclude with `a0.sub (a1.mul continuous_const)`.
-/
theorem cont_th (ξ : E) : Continuous fun x : Q d β (AF F) => thR (AF F) E ξ x := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have a0 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.re := hι.comp continuous_re
  have a1 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imI := hι.comp continuous_imI
  have a2 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imJ := hι.comp continuous_imJ
  have a3 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imK := hι.comp continuous_imK
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact a0.add (a1.mul continuous_const)
  · exact continuous_const.mul (a2.add (a3.mul continuous_const))
  · exact a2.sub (a3.mul continuous_const)
  · exact a0.sub (a1.mul continuous_const)

/- English proof (translation)
Rewrite using `[continuous_q_iff]`. Simplify using `only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, zero_mul, add_zero]`. Conclude with `⟨continuous_re, continuous_imI.neg, continuous_imJ.neg, continuous_imK.neg⟩`.
-/
theorem cont_star : Continuous fun x : Q d β (AF F) => star x := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star, zero_mul, add_zero]
  exact ⟨continuous_re, continuous_imI.neg, continuous_imJ.neg, continuous_imK.neg⟩

/- English proof (translation)
Establish `h : Continuous fun x : {x : Q d β (AF F) // qn x = 1} => HA.mat (AF F) σ (J2 E β) (toHA σ hξ hσ x.1 x.2)`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(cont_th ξ).comp continuous_subtype_val`. Conclude with `(cont_th ξ).comp (cont_star.comp continuous_subtype_val)`. Conclude with `Continuous.subtype_mk (p := fun g => g ∈ HR (AF F) σ (J2 E β)) h (fun x => (toHA σ hξ hσ x.1 x.2).2)`.
-/
theorem cont_toHA (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) :
    Continuous fun x : {x : Q d β (AF F) // qn x = 1} => toHA σ hξ hσ x.1 x.2 := by
  have h : Continuous fun x : {x : Q d β (AF F) // qn x = 1} =>
      HA.mat (AF F) σ (J2 E β) (toHA σ hξ hσ x.1 x.2) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (cont_th ξ).comp continuous_subtype_val
    · exact (cont_th ξ).comp (cont_star.comp continuous_subtype_val)
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF F) σ (J2 E β)) h (fun x => (toHA σ hξ hσ x.1 x.2).2)

/- English proof (translation)
Substitute `e` using the available equality. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `th_mul (xh_sq hξ) x y`.
-/
theorem toHA_mul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d)
    (hσ : σ ξ = -ξ) {x y z : Q d β R} (hx : qn x = 1) (hy : qn y = 1) (hz : qn z = 1) (e : z = x * y) :
    toHA σ hξ hσ z hz = toHA σ hξ hσ x hx * toHA σ hξ hσ y hy := by
  subst e
  apply Subtype.ext
  apply Units.ext
  exact th_mul (xh_sq hξ) x y

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Consider the cases of `u with`. Consider the case `inl w`. Simplify using `only [Finset.inl_mem_disjSum]`. Conclude with `⟨h1 w, h2 w⟩`.

Consider the case `inr v`. Simplify using `only [Finset.inr_mem_disjSum]`. Conclude with `⟨h3 v, h4 v⟩`.
-/
theorem idem_proj {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) (u : Pl F) :
    (u ∈ S₁.disjSum S₂ → proj u ε = 1) ∧ (u ∉ S₁.disjSum S₂ → proj u ε = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases u with
  | inl w =>
    simp only [Finset.inl_mem_disjSum]
    exact ⟨h1 w, h2 w⟩
  | inr v =>
    simp only [Finset.inr_mem_disjSum]
    exact ⟨h3 v, h4 v⟩

/- English proof (translation)
Use `adele_ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ T`. Rewrite using `[map_mul, hε u hu, one_mul]`. Rewrite using `[map_mul, ha u hu, mul_zero]`.
-/
theorem mul_idem {T : Set (Pl F)} {ε a : AF F} (hε : ∀ u ∈ T, proj u ε = 1) (ha : ∀ u, u ∉ T → proj u a = 0) :
    ε * a = a := by
  refine adele_ext fun u => ?_
  by_cases hu : u ∈ T
  · rw [map_mul, hε u hu, one_mul]
  · rw [map_mul, ha u hu, mul_zero]

/- English proof (translation)
Use `StrongApprox.mem_SUAdelic.2 ?_` and prove the remaining obligations. Rewrite using `[toHA_mat, th_det (xh_sq hξ), hx, map_one]`.
-/
theorem toHA_mem_SUAdelic (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    (x : Q d β (AF F)) (hx : qn x = 1) : toHA σ hξ hσ x hx ∈ SUAdelic σ (J2 E β) := by
  refine StrongApprox.mem_SUAdelic.2 ?_
  rw [toHA_mat, th_det (xh_sq hξ), hx, map_one]

/- English proof (translation)
Use `⟨toHA_mem_SUAdelic σ hξ hσ x hx, ?_⟩` and prove the remaining obligations. Establish `c0 : ∀ u, u ∉ T → proj u (x.re - 1) = 0` using `fun u hu => by`. Use `congrArg QuaternionAlgebra.re (hT.2 u hu)` as an intermediate fact. Rewrite using `[map_sub, map_one, sub_eq_zero]`. Simplify `this` using `[qmap]`.

Establish `c1 : ∀ u, u ∉ T → proj u x.imI = 0` using `fun u hu => by`. Use `congrArg QuaternionAlgebra.imI (hT.2 u hu)` as an intermediate fact. Simplify `this` using `[qmap]`. Establish `c2 : ∀ u, u ∉ T → proj u x.imJ = 0` using `fun u hu => by`. Use `congrArg QuaternionAlgebra.imJ (hT.2 u hu)` as an intermediate fact.

Simplify `this` using `[qmap]`. Establish `c3 : ∀ u, u ∉ T → proj u x.imK = 0` using `fun u hu => by`. Use `congrArg QuaternionAlgebra.imK (hT.2 u hu)` as an intermediate fact. Simplify `this` using `[qmap]`. Use `set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι`.

Establish `e0 : ι ε * (ι x.re - 1) = ι x.re - 1`. Use `congrArg ι (mul_idem hε c0)` as an intermediate fact. Simplify using `using this`. Establish `e1 : ι ε * ι x.imI = ι x.imI`. Use `congrArg ι (mul_idem hε c1)` as an intermediate fact.

Simplify using `using this`. Establish `e2 : ι ε * ι x.imJ = ι x.imJ`. Use `congrArg ι (mul_idem hε c2)` as an intermediate fact. Simplify using `using this`. Establish `e3 : ι ε * ι x.imK = ι x.imK`.

Use `congrArg ι (mul_idem hε c3)` as an intermediate fact. Simplify using `using this`. Introduce `i j`. Rewrite using `[toHA_mat]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [th, ← hι]`.

Take the linear combination `e0 + inclR (F := F) (AF F) ξ * e1`. Take the linear combination `ι (algebraMap F (AF F) β) * e2 + ι (algebraMap F (AF F) β) * inclR (F := F) (AF F) ξ * e3`. Take the linear combination `e2 - inclR (F := F) (AF F) ξ * e3`. Take the linear combination `e0 - inclR (F := F) (AF F) ξ * e1`.
-/
theorem toHA_mem_supp (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {ε : AF F} (hε : ∀ u ∈ T, proj u ε = 1) {x : Q d β (AF F)} (hT : x ∈ SuppAt d β T)
    (hx : qn x = 1) : toHA σ hξ hσ x hx ∈ SUSupp σ (J2 E β) ε := by
  refine ⟨toHA_mem_SUAdelic σ hξ hσ x hx, ?_⟩
  have c0 : ∀ u, u ∉ T → proj u (x.re - 1) = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.re (hT.2 u hu)
    rw [map_sub, map_one, sub_eq_zero]; simpa [qmap] using this
  have c1 : ∀ u, u ∉ T → proj u x.imI = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imI (hT.2 u hu); simpa [qmap] using this
  have c2 : ∀ u, u ∉ T → proj u x.imJ = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imJ (hT.2 u hu); simpa [qmap] using this
  have c3 : ∀ u, u ∉ T → proj u x.imK = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imK (hT.2 u hu); simpa [qmap] using this
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have e0 : ι ε * (ι x.re - 1) = ι x.re - 1 := by
    have := congrArg ι (mul_idem hε c0); simpa using this
  have e1 : ι ε * ι x.imI = ι x.imI := by
    have := congrArg ι (mul_idem hε c1); simpa using this
  have e2 : ι ε * ι x.imJ = ι x.imJ := by
    have := congrArg ι (mul_idem hε c2); simpa using this
  have e3 : ι ε * ι x.imK = ι x.imK := by
    have := congrArg ι (mul_idem hε c3); simpa using this
  intro i j
  rw [toHA_mat]
  fin_cases i <;> fin_cases j <;> simp [th, ← hι]
  · linear_combination e0 + inclR (F := F) (AF F) ξ * e1
  · linear_combination ι (algebraMap F (AF F) β) * e2 + ι (algebraMap F (AF F) β) * inclR (F := F) (AF F) ξ * e3
  · linear_combination e2 - inclR (F := F) (AF F) ξ * e3
  · linear_combination e0 - inclR (F := F) (AF F) ξ * e1

/- English proof (translation)
Use `⟨hx, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hm2` using `hm.2`. Simplify using `only [toHA_mat] at hm2`. Use `set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι`. Use `set h := inclR (F := F) (AF F) ξ with hh`.

Establish `h00 : ι (δ * (x.re - 1)) + ι (δ * x.imI) * h = ι (x.re - 1) + ι x.imI * h`. Use `hm2 0 0` as an intermediate fact. Simplify using `[th, ← hι, ← hh] at this`. Simplify using `only [map_mul, map_sub, map_one]`. Take the linear combination `this`.

Establish `h10 : ι (δ * x.imJ) + ι (δ * -x.imK) * h = ι x.imJ + ι (-x.imK) * h`. Use `hm2 1 0` as an intermediate fact. Simplify using `[th, ← hι, ← hh] at this`. Simplify using `only [map_mul, map_neg]`. Take the linear combination `this`.

Establish `p0 : δ * (x.re - 1) = x.re - 1`. Use `congrArg (co b (AF F) 0) h00` as an intermediate fact. Rewrite `this` using `[(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1]`. Then use the resulting hypothesis. Establish `p1 : δ * x.imI = x.imI`. Use `congrArg (co b (AF F) 1) h00` as an intermediate fact.

Rewrite `this` using `[(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2]`. Then use the resulting hypothesis. Establish `p2 : δ * x.imJ = x.imJ`. Use `congrArg (co b (AF F) 0) h10` as an intermediate fact. Rewrite `this` using `[(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1]`. Then use the resulting hypothesis. Establish `p3 : δ * -x.imK = -x.imK`.

Use `congrArg (co b (AF F) 1) h10` as an intermediate fact. Rewrite `this` using `[(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2]`. Then use the resulting hypothesis. Establish `q : ∀ a : AF F, δ * a = a → proj u a = 0` using `fun a ha => by`. Rewrite using `[← ha, map_mul, hδ u hu, zero_mul]`. Establish `q0` using `q _ p0`.

Establish `q1` using `q _ p1`. Establish `q2` using `q _ p2`. Establish `q3` using `q _ p3`. Rewrite `q0` using `[map_sub, map_one, sub_eq_zero]`. Rewrite `q3` using `[map_neg, neg_eq_zero]`.

Use `ext`. Simplify `q0` using `[qmap]`. Simplify `q1` using `[qmap]`. Simplify `q2` using `[qmap]`. Simplify `q3` using `[qmap]`.
-/
theorem supp_of_toHA {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {δ : AF F} (hδ : ∀ u, u ∉ T → proj u δ = 0) {x : Q d β (AF F)} (hx : qn x = 1)
    (hm : toHA σ hξ hσ x hx ∈ SUSupp σ (J2 E β) δ) : x ∈ SuppAt d β T := by
  refine ⟨hx, fun u hu => ?_⟩
  have hm2 := hm.2
  simp only [toHA_mat] at hm2
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  set h := inclR (F := F) (AF F) ξ with hh
  have h00 : ι (δ * (x.re - 1)) + ι (δ * x.imI) * h = ι (x.re - 1) + ι x.imI * h := by
    have := hm2 0 0
    simp [th, ← hι, ← hh] at this
    simp only [map_mul, map_sub, map_one]
    linear_combination this
  have h10 : ι (δ * x.imJ) + ι (δ * -x.imK) * h = ι x.imJ + ι (-x.imK) * h := by
    have := hm2 1 0
    simp [th, ← hι, ← hh] at this
    simp only [map_mul, map_neg]
    linear_combination this
  have p0 : δ * (x.re - 1) = x.re - 1 := by
    have := congrArg (co b (AF F) 0) h00
    rwa [(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1] at this
  have p1 : δ * x.imI = x.imI := by
    have := congrArg (co b (AF F) 1) h00
    rwa [(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2] at this
  have p2 : δ * x.imJ = x.imJ := by
    have := congrArg (co b (AF F) 0) h10
    rwa [(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1] at this
  have p3 : δ * -x.imK = -x.imK := by
    have := congrArg (co b (AF F) 1) h10
    rwa [(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2] at this
  have q : ∀ a : AF F, δ * a = a → proj u a = 0 := fun a ha => by
    rw [← ha, map_mul, hδ u hu, zero_mul]
  have q0 := q _ p0
  have q1 := q _ p1
  have q2 := q _ p2
  have q3 := q _ p3
  rw [map_sub, map_one, sub_eq_zero] at q0
  rw [map_neg, neg_eq_zero] at q3
  ext
  · simpa [qmap] using q0
  · simpa [qmap] using q1
  · simpa [qmap] using q2
  · simpa [qmap] using q3

/- English proof (translation)
Establish `hh : ξ * ξ = algebraMap F E (algebraMap F F d)` using `by rw [← pow_two, hξ]; rfl`. Use `⟨toHA_mem_SUAdelic σ hξ hσ _ hq, ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_subgroupOf.2 ?_` and prove the remaining obligations. Use `⟨⟨th (algebraMap F E) ξ γ, th (algebraMap F E) ξ (star γ), th_mul_star hh hγ, th_star_mul hh hγ⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `th_unitary hh (σ : E →+* E) (fun a => σ.commutes a) hσ hγ`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Formalism.UG.bc, toHA, th, rat, qmap, Algebra.ofId_apply, incl_alg]`.
-/
theorem toHA_rat (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) {γ : Q d β F}
    (hγ : qn γ = 1) (hq : qn (rat γ : Q d β (AF F)) = 1) :
    toHA σ hξ hσ (rat γ) hq ∈ SURat σ (J2 E β) := by
  have hh : ξ * ξ = algebraMap F E (algebraMap F F d) := by rw [← pow_two, hξ]; rfl
  refine ⟨toHA_mem_SUAdelic σ hξ hσ _ hq, ?_⟩
  refine Subgroup.mem_subgroupOf.2 ?_
  refine ⟨⟨th (algebraMap F E) ξ γ, th (algebraMap F E) ξ (star γ), th_mul_star hh hγ, th_star_mul hh hγ⟩, ?_, ?_⟩
  · exact th_unitary hh (σ : E →+* E) (fun a => σ.commutes a) hσ hγ
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.UG.bc, toHA, th, rat, qmap, Algebra.ofId_apply, incl_alg]

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `exists_of_mem hb0 hb1 σ hξ hσ g (StrongApprox.mem_SUAdelic.1 hg.1)`. Conclude with `⟨x, hx, supp_of_toHA hb0 hb1 σ hξ hσ hδ hx hg, rfl⟩`.
-/
theorem exists_supp {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {δ : AF F} (hδ : ∀ u, u ∉ T → proj u δ = 0) {g : HA (AF F) σ (J2 E β)}
    (hg : g ∈ SUSupp σ (J2 E β) δ) :
    ∃ (x : Q d β (AF F)) (hx : qn x = 1), x ∈ SuppAt d β T ∧ g = toHA σ hξ hσ x hx := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem hb0 hb1 σ hξ hσ g (StrongApprox.mem_SUAdelic.1 hg.1)
  exact ⟨x, hx, supp_of_toHA hb0 hb1 σ hξ hσ hδ hx hg, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `hz`. Introduce `hy`.

Conclude with `⟨⟨y, h y hy⟩, hy, rfl⟩`.
-/
theorem image_val_eq {A : Set (Q d β (AF F))} (h : ∀ y ∈ A, qn y = 1) :
    Subtype.val '' (Subtype.val ⁻¹' A : Set {x : Q d β (AF F) // qn x = 1}) = A := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, h y hy⟩, hy, rfl⟩

/- English proof (translation)
Establish `hK : IsCompact (Subtype.val ⁻¹' SuppAt d β T : Set {x : Q d β (AF F) // qn x = 1})`. Use `Subtype.isCompact_iff.2 ?_` and prove the remaining obligations. Rewrite using `[image_val_eq fun y hy => hy.1]`. Conclude with `hC`. Use `hK.image (cont_toHA σ hξ hσ) using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨x, hx, hT, rfl⟩` from `exists_supp hb0 hb1 σ hξ hσ hε0 hg`. Conclude with `⟨⟨x, hx⟩, hT, rfl⟩`.

Introduce and unpack `⟨⟨x, hx⟩, hT, rfl⟩`. Conclude with `toHA_mem_supp σ hξ hσ hε1 hT hx`.
-/
theorem compact_SUSupp {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {ε : AF F} (hε1 : ∀ u ∈ T, proj u ε = 1) (hε0 : ∀ u, u ∉ T → proj u ε = 0)
    (hC : IsCompact (SuppAt d β T)) : IsCompact (SUSupp σ (J2 E β) ε) := by
  have hK : IsCompact (Subtype.val ⁻¹' SuppAt d β T : Set {x : Q d β (AF F) // qn x = 1}) := by
    refine Subtype.isCompact_iff.2 ?_
    rw [image_val_eq fun y hy => hy.1]
    exact hC
  convert hK.image (cont_toHA σ hξ hσ) using 1
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hT, rfl⟩ := exists_supp hb0 hb1 σ hξ hσ hε0 hg
    exact ⟨⟨x, hx⟩, hT, rfl⟩
  · rintro ⟨⟨x, hx⟩, hT, rfl⟩
    exact toHA_mem_supp σ hξ hσ hε1 hT hx

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), ξ]`. Use `LinearIndependent.pair_iff.2 fun s t hst => ?_` and prove the remaining obligations. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst`.

Conclude with `⟨hst, rfl⟩`. It suffices to derive a contradiction. Establish `hx : ξ = algebraMap F E (-s / t)`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `ht' : algebraMap F E t ≠ 0` using `by simpa using ht`.

Rewrite using `[map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hst`. Apply `hd (-s / t)` to reduce the goal to its premises. Apply `(algebraMap F E).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, ← hx, hξ]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfin])`. Conclude with `⟨b, by simp [b], by simp [b]⟩`.
-/
theorem exists_basis {d : F} {ξ : E} (hfin : Module.finrank F E = 2) (hd : ∀ r : F, r ^ 2 ≠ d)
    (hξ : ξ ^ 2 = algebraMap F E d) : ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = ξ := by
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      have hx : ξ = algebraMap F E (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hst
      apply hd (-s / t)
      apply (algebraMap F E).injective
      rw [map_pow, ← hx, hξ]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfin])
  exact ⟨b, by simp [b], by simp [b]⟩

/- English proof (translation)
Establish `hε1 : ∀ u ∈ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)), proj u ε = 1` using `fun u hu => (idem_proj hε u).1 (Finset.mem_coe.1 hu)`. Establish `hε0 : ∀ u, u ∉ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)) → proj u ε = 0` using `fun u hu => (idem_proj hε u).2 (fun h => hu (Finset.mem_coe.2 h))`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Use `hnc (compact_SUSupp hb0 hb1 σ hξ hσ hε1 hε0 (GlobalTheory.T.finite_place_norm_one_compact_support d β _ fun s hs => ?_))` and prove the remaining obligations.

Conclude with `GlobalTheory.T.anisotropic_quaternion_norm_one_compact d β s fun x hx => by_contra fun h => hno s hs x h hx`.
-/
theorem exists_split_place {ξ : E} {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    (hnc : ¬ IsCompact (SUSupp σ (J2 E β) ε)) :
    ∃ s ∈ (S₁.disjSum S₂ : Finset (Pl F)), ∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0 := by
  have hε1 : ∀ u ∈ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)), proj u ε = 1 := fun u hu =>
    (idem_proj hε u).1 (Finset.mem_coe.1 hu)
  have hε0 : ∀ u, u ∉ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)) → proj u ε = 0 := fun u hu =>
    (idem_proj hε u).2 (fun h => hu (Finset.mem_coe.2 h))
  by_contra hno
  push_neg at hno
  refine hnc (compact_SUSupp hb0 hb1 σ hξ hσ hε1 hε0 (GlobalTheory.T.finite_place_norm_one_compact_support d β _ fun s hs => ?_))
  exact GlobalTheory.T.anisotropic_quaternion_norm_one_compact d β s fun x hx => by_contra fun h => hno s hs x h hx

/- English proof (translation)
The claim follows from `(qn_qmap _ γ).trans (by rw [hγ, map_one])`.
-/
theorem qn_rat {γ : Q d β F} (hγ : qn γ = 1) : qn (rat γ : Q d β (AF F)) = 1 :=
  (qn_qmap _ γ).trans (by rw [hγ, map_one])

/- English proof (translation)
Take `⟨γ, hγ, h, hh, e⟩` from `hyS`. Establish `hq : qn (rat γ : Q d β (AF F)) = 1` using `qn_rat hγ`. Establish `h1` using `toHA_rat σ hξ hσ hγ hq`. Establish `h2 : toHA σ hξ hσ h hh.1 ∈ SUSupp σ (J2 E β) ε` using `toHA_mem_supp σ hξ hσ (T := {s}) (fun u hu => by`. Rewrite using `[Set.mem_singleton_iff.1 hu]`.

Conclude with `(idem_proj hε s).1 hsS) hh hh.1`. Conclude with `⟨_, h1, _, h2, toHA_mul σ hξ hσ hq hh.1 hy e⟩`.
-/
theorem toHA_mem_SASet (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    {s : Pl F} (hsS : s ∈ (S₁.disjSum S₂ : Finset (Pl F))) {y : Q d β (AF F)} (hy : qn y = 1)
    (hyS : y ∈ SAQ d β s) : toHA σ hξ hσ y hy ∈ Sa2.SASet σ (J2 E β) ε := by
  obtain ⟨γ, hγ, h, hh, e⟩ := hyS
  have hq : qn (rat γ : Q d β (AF F)) = 1 := qn_rat hγ
  have h1 := toHA_rat σ hξ hσ hγ hq
  have h2 : toHA σ hξ hσ h hh.1 ∈ SUSupp σ (J2 E β) ε :=
    toHA_mem_supp σ hξ hσ (T := {s}) (fun u hu => by
      rw [Set.mem_singleton_iff.1 hu]; exact (idem_proj hε s).1 hsS) hh hh.1
  exact ⟨_, h1, _, h2, toHA_mul σ hξ hσ hq hh.1 hy e⟩

/- English proof (translation)
Establish `hsub : ∀ y ∈ SAQ d β s, qn y = 1`. Introduce and unpack `_ ⟨γ, hγ, h, hh, rfl⟩`. Rewrite using `[qn_mul, hh.1, mul_one]`. Conclude with `qn_rat hγ`. Use `closure_subtype.2 ?_` and prove the remaining obligations.

Rewrite using `[image_val_eq hsub]`. Conclude with `hcl`.
-/
theorem closure_norm_one_subtype {s : Pl F} {x : Q d β (AF F)} (hx : qn x = 1) (hcl : x ∈ closure (SAQ d β s)) :
    (⟨x, hx⟩ : {x : Q d β (AF F) // qn x = 1}) ∈
      closure (Subtype.val ⁻¹' SAQ d β s : Set {x : Q d β (AF F) // qn x = 1}) := by
  have hsub : ∀ y ∈ SAQ d β s, qn y = 1 := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩
    rw [qn_mul, hh.1, mul_one]
    exact qn_rat hγ
  refine closure_subtype.2 ?_
  rw [image_val_eq hsub]
  exact hcl

/- English proof (translation)
Establish `hm : Set.MapsTo (fun x : {x : Q d β (AF F) // qn x = 1} => toHA σ hξ hσ x.1 x.2) (Subtype.val ⁻¹' SAQ d β s) (Sa2.SASet σ (J2 E β) ε)` using `fun y hy => toHA_mem_SASet σ hξ hσ hε hsS y.2 hy`. Establish `h` using `map_mem_closure (cont_toHA σ hξ hσ) (closure_norm_one_subtype hx hcl) hm`. Conclude with `h`.
-/
theorem toHA_mem_closure (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    {s : Pl F} (hsS : s ∈ (S₁.disjSum S₂ : Finset (Pl F))) {x : Q d β (AF F)} (hx : qn x = 1)
    (hcl : x ∈ closure (SAQ d β s)) :
    toHA σ hξ hσ x hx ∈ closure (Sa2.SASet σ (J2 E β) ε) := by
  have hm : Set.MapsTo (fun x : {x : Q d β (AF F) // qn x = 1} => toHA σ hξ hσ x.1 x.2)
      (Subtype.val ⁻¹' SAQ d β s) (Sa2.SASet σ (J2 E β) ε) :=
    fun y hy => toHA_mem_SASet σ hξ hσ hε hsS y.2 hy
  have h := map_mem_closure (cont_toHA σ hξ hσ) (closure_norm_one_subtype hx hcl) hm
  exact h

end Adelic

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm β _ d hd ξ hξ hσ hQ S₁ S₂ ε hε hnc T₁ T₂ δ hδ g hg`. Take `⟨b, hb0, hb1⟩` from `exists_basis hcm.2.2.1 hd hξ`. Establish `hδ0 : ∀ u, u ∉ ((T₁.disjSum T₂ : Finset (Pl F)) : Set (Pl F)) → proj u δ = 0` using `fun u hu => (idem_proj hδ u).2 (fun h => hu (Finset.mem_coe.2 h))`. Take `⟨s, hsS, hiso⟩` from `exists_split_place hb0 hb1 σ hξ hσ hε hnc`. Take `⟨x, hx, hT, rfl⟩` from `exists_supp hb0 hb1 σ hξ hσ hδ0 hg`.

Conclude with `toHA_mem_closure σ hξ hσ hε hsS hx (hQ s hiso (T₁.disjSum T₂) hT)`.
-/
theorem plane_strong_approx_of_quaternion : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → ∀ d : F, (∀ r : F, r ^ 2 ≠ d) → ∀ ξ : E, ξ ^ 2 = algebraMap F E d → σ ξ = -ξ →
    (∀ s : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → QSA d β s) → HermitianPlaneStrongApprox σ β := by
  intro F E _ _ _ _ _ σ hcm β _ d hd ξ hξ hσ hQ S₁ S₂ ε hε hnc T₁ T₂ δ hδ g hg
  obtain ⟨b, hb0, hb1⟩ := exists_basis hcm.2.2.1 hd hξ
  have hδ0 : ∀ u, u ∉ ((T₁.disjSum T₂ : Finset (Pl F)) : Set (Pl F)) → proj u δ = 0 := fun u hu =>
    (idem_proj hδ u).2 (fun h => hu (Finset.mem_coe.2 h))
  obtain ⟨s, hsS, hiso⟩ := exists_split_place hb0 hb1 σ hξ hσ hε hnc
  obtain ⟨x, hx, hT, rfl⟩ := exists_supp hb0 hb1 σ hξ hσ hδ0 hg
  exact toHA_mem_closure σ hξ hσ hε hsS hx (hQ s hiso (T₁.disjSum T₂) hT)

end GlobalTheory.CompanionTheory.PlaneSA.TwoQ
