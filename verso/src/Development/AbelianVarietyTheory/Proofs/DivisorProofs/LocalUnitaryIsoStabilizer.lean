import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLineLoc

open GlobalTheory.InertLagParam GlobalTheory.UnitaryInjAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Support

variable {v : Pl F} {m k : Type} [Fintype m] [Fintype k]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_sub, hA u hu, hB u hu, sub_zero]`.
-/
theorem at_sub {A B : Matrix m k (AE F E)} (hA : At (evFin F v) A) (hB : At (evFin F v) B) :
    At (evFin F v) (A - B) := fun u hu => by rw [smul_sub, hA u hu, hB u hu, sub_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_add, hA u hu, hB u hu, add_zero]`.
-/
theorem at_add {A B : Matrix m k (AE F E)} (hA : At (evFin F v) A) (hB : At (evFin F v) B) :
    At (evFin F v) (A + B) := fun u hu => by rw [smul_add, hA u hu, hB u hu, add_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.mul_smul, hA u hu, Matrix.mul_zero]`.
-/
theorem at_mul_left {l : Type} [Fintype l] (C : Matrix l m (AE F E)) {A : Matrix m k (AE F E)}
    (hA : At (evFin F v) A) : At (evFin F v) (C * A) := fun u hu => by
  rw [← Matrix.mul_smul, hA u hu, Matrix.mul_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.smul_mul, hA u hu, Matrix.zero_mul]`.
-/
theorem at_mul_right {l : Type} [Fintype l] {A : Matrix m k (AE F E)} (hA : At (evFin F v) A)
    (C : Matrix k l (AE F E)) : At (evFin F v) (A * C) := fun u hu => by
  rw [← Matrix.smul_mul, hA u hu, Matrix.zero_mul]

/- English proof (translation)
Introduce `u hu` and use `by rw [← Matrix.transpose_smul, hA u hu, Matrix.transpose_zero]`.
-/
theorem at_transpose {A : Matrix m k (AE F E)} (hA : At (evFin F v) A) : At (evFin F v) Aᵀ := fun u hu => by
  rw [← Matrix.transpose_smul, hA u hu, Matrix.transpose_zero]

/- English proof (translation)
Introduce `u hu` and use `by have : u • A.map (cA σ) = (u • A).map (cA σ) := by ext i j; simp [Matrix.smul_apply, map_smul] rw [this, hA u hu]; ext i j; simp`.
-/
theorem at_map_cA (σ : E →ₐ[F] E) {A : Matrix m k (AE F E)} (hA : At (evFin F v) A) :
    At (evFin F v) (A.map (cA σ)) := fun u hu => by
  have : u • A.map (cA σ) = (u • A).map (cA σ) := by
    ext i j; simp [Matrix.smul_apply, map_smul]
  rw [this, hA u hu]; ext i j; simp

end Support

/- English proof (translation)
Establish `hz : At (evFin F v) (A - B)`. Establish `e : A - B = (A - 1) - (B - 1)` using `by abel`. Rewrite using `[e]`. Conclude with `at_sub hA hB`. Establish `h0 : (A - B).map (compFin F E v) = 0`.

Rewrite using `[Matrix.map_sub _ (fun x y => map_sub _ x y), h, sub_self]`. Conclude with `sub_eq_zero.1 (mat_eq_zero_of_at v _ hz h0)`.
-/
theorem eq_of_compFin {n : ℕ} {v : Pl F} {A B : Matrix (Fin n) (Fin n) (AE F E)}
    (hA : At (evFin F v) (A - 1)) (hB : At (evFin F v) (B - 1))
    (h : A.map (compFin F E v) = B.map (compFin F E v)) : A = B := by
  have hz : At (evFin F v) (A - B) := by
    have e : A - B = (A - 1) - (B - 1) := by abel
    rw [e]; exact at_sub hA hB
  have h0 : (A - B).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), h, sub_self]
  exact sub_eq_zero.1 (mat_eq_zero_of_at v _ hz h0)

section Fwd

variable (σ : E →ₐ[F] E) {n : ℕ}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id F R) σ ((1 : R) ⊗ₜ[F] e) = (1 : R) ⊗ₜ[F] σ e`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (e : E) : sigR R σ (inclR (F := F) R e) = inclR (F := F) R (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F R) σ ((1 : R) ⊗ₜ[F] e) = (1 : R) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[JR, Matrix.smul_apply, map_mul]`.
-/
theorem JR_smul (R : Type) [CommRing R] [Algebra F R] (δ : E) (X : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (δ • X) = inclR (F := F) R δ • JR (F := F) R X := by
  ext i j; simp [JR, Matrix.smul_apply, map_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[JR, sigR_inclR]`.
-/
theorem JR_map_sigR (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin n) (Fin n) E) :
    (JR (F := F) R X).map (sigR R σ) = JR (F := F) R (X.map σ) := by
  ext i j; simp [JR, sigR_inclR]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, JR, compFin_inclR]`.
-/
theorem compFin_incM (v : Pl F) (X : Matrix (Fin n) (Fin n) E) :
    (incM F X).map (compFin F E v) = JR (Fv F v) X := by
  ext i j; simp [incM, JR, compFin_inclR]

/- English proof (translation)
Use `set M := (mat g).map (compFin F E v) with hM`. Establish `hm : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J` using `g.2`. Establish `h1` using `congrArg (RingHom.mapMatrix (compFin F E v)) hm`. Simplify using `only [map_mul, RingHom.mapMatrix_apply] at h1`. Establish `e1 : ((mat g).map (cA σ)).map (compFin F E v) = M.map (sigR (Fv F v) σ)`.

Use extensionality with `i j`. Simplify using `[hM, compFin_cA]`. Rewrite `h1` using `[e1, compFin_incM, Matrix.transpose_map]`. Establish `h2` using `congrArg (RingHom.mapMatrix (sigR (Fv F v) σ)) h1`. Simplify using `only [map_mul, RingHom.mapMatrix_apply] at h2`.

Establish `e2 : (M.map (sigR (Fv F v) σ)).map (sigR (Fv F v) σ) = M`. Use extensionality with `i j`. Simplify using `[sigR_sigR σ hσ]`. Rewrite `h2` using `[e2, JR_map_sigR, Matrix.transpose_map]`. Rewrite using `[JR_smul, Matrix.mul_smul, Matrix.smul_mul]`.

Use `congr 1`.
-/
theorem unitary_compFin (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) (δ : E) (v : Pl F) (g : UA σ J) :
    Formalism.UG.cT (sigR (Fv F v) σ) ((mat g).map (compFin F E v)) * JR (Fv F v) (δ • J.map σ) * (mat g).map (compFin F E v) =
      JR (Fv F v) (δ • J.map σ) := by
  set M := (mat g).map (compFin F E v) with hM
  have hm : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have h1 := congrArg (RingHom.mapMatrix (compFin F E v)) hm
  simp only [map_mul, RingHom.mapMatrix_apply] at h1
  have e1 : ((mat g).map (cA σ)).map (compFin F E v) = M.map (sigR (Fv F v) σ) := by
    ext i j; simp [hM, compFin_cA]
  rw [e1, compFin_incM, Matrix.transpose_map] at h1
  have h2 := congrArg (RingHom.mapMatrix (sigR (Fv F v) σ)) h1
  simp only [map_mul, RingHom.mapMatrix_apply] at h2
  have e2 : (M.map (sigR (Fv F v) σ)).map (sigR (Fv F v) σ) = M := by
    ext i j; simp [sigR_sigR σ hσ]
  rw [e2, JR_map_sigR, Matrix.transpose_map] at h2
  rw [JR_smul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1

end Fwd

section Up

variable {n : ℕ} (v : Pl F)

def up (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + (H - 1).map (lift v)

/- English proof (translation)
Rewrite using `[up, add_sub_cancel_left]`.
-/
theorem up_sub_one (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : up v H - 1 = (H - 1).map (lift v) := by
  rw [up, add_sub_cancel_left]

/- English proof (translation)
Rewrite using `[up_sub_one]`. Conclude with `at_map_lift v _`.
-/
theorem at_up (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : At (evFin F v) (up v H - 1) := by
  rw [up_sub_one]; exact at_map_lift v _

/- English proof (translation)
Establish `e : (up v H).map (compFin F E v) = (compFin F E v).mapMatrix (up v H)` using `rfl`. Rewrite using `[e, up, map_add, map_one, RingHom.mapMatrix_apply, map_lift_compFin, add_sub_cancel]`.
-/
theorem compFin_up (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : (up v H).map (compFin F E v) = H := by
  have e : (up v H).map (compFin F E v) = (compFin F E v).mapMatrix (up v H) := rfl
  rw [e, up, map_add, map_one, RingHom.mapMatrix_apply, map_lift_compFin, add_sub_cancel]

/- English proof (translation)
The claim follows from `eq_of_compFin (at_up v _) hA (compFin_up v _)`.
-/
theorem up_compFin {A : Matrix (Fin n) (Fin n) (AE F E)} (hA : At (evFin F v) (A - 1)) :
    up v (A.map (compFin F E v)) = A :=
  eq_of_compFin (at_up v _) hA (compFin_up v _)

/- English proof (translation)
Establish `e : A * B - 1 = (A - 1) * B + (B - 1)`. Rewrite using `[sub_mul, one_mul, sub_add_sub_cancel]`. Rewrite using `[e]`. Conclude with `at_add (at_mul_right hA B) hB`.
-/
theorem at_mul_sub_one {A B : Matrix (Fin n) (Fin n) (AE F E)} (hA : At (evFin F v) (A - 1))
    (hB : At (evFin F v) (B - 1)) : At (evFin F v) (A * B - 1) := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by
    rw [sub_mul, one_mul, sub_add_sub_cancel]
  rw [e]; exact at_add (at_mul_right hA B) hB

/- English proof (translation)
Use `eq_of_compFin (at_up v _) (at_mul_sub_one v (at_up v H) (at_up v K)) ?_` and prove the remaining obligations. Rewrite using `[compFin_up, Matrix.map_mul, compFin_up, compFin_up]`.
-/
theorem up_mul (H K : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : up v (H * K) = up v H * up v K := by
  refine eq_of_compFin (at_up v _) (at_mul_sub_one v (at_up v H) (at_up v K)) ?_
  rw [compFin_up, Matrix.map_mul, compFin_up, compFin_up]

/- English proof (translation)
Rewrite using `[up, sub_self]`. Establish `: (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).map (lift v) = 0` using `by ext i j; simp`. Rewrite using `[this, add_zero]`.
-/
theorem up_one : up v (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
  rw [up, sub_self]
  have : (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).map (lift v) = 0 := by ext i j; simp
  rw [this, add_zero]

end Up

section Bwd

variable (σ : E →ₐ[F] E) {n : ℕ}

/- English proof (translation)
Establish `h2` using `congrArg (RingHom.mapMatrix (sigR (Fv F v) σ)) hH`. Simplify using `only [map_mul, RingHom.mapMatrix_apply] at h2`. Establish `e1 : (Formalism.UG.cT (sigR (Fv F v) σ) H).map (sigR (Fv F v) σ) = Hᵀ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, sigR_sigR σ hσ]`.

Establish `e2 : (δ • J.map σ).map σ = σ δ • J`. Use extensionality with `i j`. Simplify using `[Matrix.smul_apply, hσ]`. Rewrite `h2` using `[e1, JR_map_sigR, e2, JR_smul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hu : IsUnit (inclR (F` using `F) (Fv F v) (σ δ)) := (isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 hδ)).map _`.

Take `⟨u, hu⟩` from `hu`. Establish `h3` using `congrArg (fun X => (↑u⁻¹ : Fv F v ⊗[F] E) • X) h2`. Simplify using `only [← hu, smul_smul, Units.inv_mul, one_smul] at h3`. Conclude with `h3`.
-/
theorem unitary_of_loc (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) (v : Pl F)
    (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hH : Formalism.UG.cT (sigR (Fv F v) σ) H * JR (Fv F v) (δ • J.map σ) * H = JR (Fv F v) (δ • J.map σ)) :
    Hᵀ * JR (Fv F v) J * H.map (sigR (Fv F v) σ) = JR (Fv F v) J := by
  have h2 := congrArg (RingHom.mapMatrix (sigR (Fv F v) σ)) hH
  simp only [map_mul, RingHom.mapMatrix_apply] at h2
  have e1 : (Formalism.UG.cT (sigR (Fv F v) σ) H).map (sigR (Fv F v) σ) = Hᵀ := by
    ext i j; simp [Formalism.UG.cT, sigR_sigR σ hσ]
  have e2 : (δ • J.map σ).map σ = σ δ • J := by
    ext i j; simp [Matrix.smul_apply, hσ]
  rw [e1, JR_map_sigR, e2, JR_smul, Matrix.mul_smul, Matrix.smul_mul] at h2
  have hu : IsUnit (inclR (F := F) (Fv F v) (σ δ)) :=
    (isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 hδ)).map _
  obtain ⟨u, hu⟩ := hu
  have h3 := congrArg (fun X => (↑u⁻¹ : Fv F v ⊗[F] E) • X) h2
  simp only [← hu, smul_smul, Units.inv_mul, one_smul] at h3
  exact h3

/- English proof (translation)
Use `set X := up v H - 1 with hX`. Establish `hXa : At (evFin F v) X` using `at_up v H`. Establish `hU : up v H = 1 + X` using `by rw [hX, add_sub_cancel]`. Establish `hcA : (1 + X).map (cA σ) = 1 + X.map (cA σ)`. Establish `e : (1 + X).map (cA σ) = (cA σ : AE F E →+* AE F E).mapMatrix (1 + X)` using `rfl`.

Rewrite using `[e, map_add, map_one]`. Both sides reduce to the same expression. Establish `hD : At (evFin F v) ((up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J)`. Establish `e : (up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J = Xᵀ * incM F J * (1 + X.map (cA σ)) + incM F J * X.map (cA σ)`. Rewrite using `[hU, hcA, Matrix.transpose_add, Matrix.transpose_one]`.

Use `noncomm_ring`. Rewrite using `[e]`. Conclude with `at_add (at_mul_right (at_mul_right (at_transpose hXa) _) _) (at_mul_left _ (at_map_cA σ hXa))`. Establish `h0 : ((up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J).map (compFin F E v) = 0`. Establish `e : ((up v H).map (cA σ)).map (compFin F E v) = ((up v H).map (compFin F E v)).map (sigR (Fv F v) σ)`.

Use extensionality with `i j`. Simplify using `[compFin_cA]`. Rewrite using `[Matrix.map_sub _ (fun x y => map_sub _ x y), Matrix.map_mul, Matrix.map_mul, e, compFin_incM, Matrix.transpose_map, compFin_up, hH, sub_self]`. Conclude with `sub_eq_zero.1 (mat_eq_zero_of_at v _ hD h0)`.
-/
theorem unitary_up (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (H : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hH : Hᵀ * JR (Fv F v) J * H.map (sigR (Fv F v) σ) = JR (Fv F v) J) :
    (up v H)ᵀ * incM F J * (up v H).map (cA σ) = incM F J := by
  set X := up v H - 1 with hX
  have hXa : At (evFin F v) X := at_up v H
  have hU : up v H = 1 + X := by rw [hX, add_sub_cancel]
  have hcA : (1 + X).map (cA σ) = 1 + X.map (cA σ) := by
    have e : (1 + X).map (cA σ) = (cA σ : AE F E →+* AE F E).mapMatrix (1 + X) := rfl
    rw [e, map_add, map_one]; rfl
  have hD : At (evFin F v) ((up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J) := by
    have e : (up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J =
        Xᵀ * incM F J * (1 + X.map (cA σ)) + incM F J * X.map (cA σ) := by
      rw [hU, hcA, Matrix.transpose_add, Matrix.transpose_one]
      noncomm_ring
    rw [e]
    exact at_add (at_mul_right (at_mul_right (at_transpose hXa) _) _) (at_mul_left _ (at_map_cA σ hXa))
  have h0 : ((up v H)ᵀ * incM F J * (up v H).map (cA σ) - incM F J).map (compFin F E v) = 0 := by
    have e : ((up v H).map (cA σ)).map (compFin F E v) = ((up v H).map (compFin F E v)).map (sigR (Fv F v) σ) := by
      ext i j; simp [compFin_cA]
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), Matrix.map_mul, Matrix.map_mul, e, compFin_incM,
      Matrix.transpose_map, compFin_up, hH, sub_self]
  exact sub_eq_zero.1 (mat_eq_zero_of_at v _ hD h0)

end Bwd

section Lat

open GlobalTheory.KBridge

variable {n : ℕ}

/- English proof (translation)
The claim follows from `evalV_singleFin_ne h a`.
-/
theorem evFin_liftV_ne {v u : Pl F} (h : u ≠ v) (a : Fv F v) : evFin F u (GlobalTheory.LatVac.liftV v a) = 0 :=
  evalV_singleFin_ne h a

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, infT_tmul]`. Establish `: (GlobalTheory.LatVac.liftV v 1 * a).1 = 0` using `zero_mul _`.

Rewrite using `[this, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]`.
-/
theorem infT_liftV_smul (v : Pl F) (x : AE F E) : infT F E (GlobalTheory.LatVac.liftV v 1 • x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, infT_tmul]
    have : (GlobalTheory.LatVac.liftV v 1 * a).1 = 0 := zero_mul _
    rw [this, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

/- English proof (translation)
Rewrite using `[compFin_smul, evFin_liftV_ne h, zero_smul]`.
-/
theorem compFin_liftV_smul {v u : Pl F} (h : u ≠ v) (x : AE F E) :
    compFin F E u (GlobalTheory.LatVac.liftV v 1 • x) = 0 := by
  rw [compFin_smul, evFin_liftV_ne h, zero_smul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finT F E (z i)) = compFin F E u (z i)`. Generalize the expression as in `z i = x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`.
-/
theorem vecLoc_finT (u : Pl F) (z : Fin n → AE F E) :
    vecLoc u (fun i => finT F E (z i)) = fun i => compFin F E u (z i) := by
  funext i
  show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finT F E (z i)) = compFin F E u (z i)
  generalize z i = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/- English proof (translation)
Rewrite using `[GlobalTheory.KBridge.mem_latHat_iff, GlobalTheory.AdelicU.mem_latHat_iff hL]`. Simplify using `only [vecLoc_finT]`.
-/
theorem mem_latHat_iff_comp {W : Spc F E n} (hL : W.L.FG) (z : Fin n → AE F E) :
    z ∈ latHat W ↔ (∀ i, infT F E (z i) = 0) ∧ ∀ u, (fun i => compFin F E u (z i)) ∈ latLoc F W.L u := by
  rw [GlobalTheory.KBridge.mem_latHat_iff, GlobalTheory.AdelicU.mem_latHat_iff hL]
  simp only [vecLoc_finT]

/- English proof (translation)
Use `⟨fun i => ?_, fun u hu => funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `infT_liftV_smul v (y i)`. Rewrite using `[← hy]`. Conclude with `compFin_liftV_smul hu (y i)`.
-/
theorem comp_of_idem {v : Pl F} {y : Fin n → AE F E} (hy : GlobalTheory.LatVac.liftV v 1 • y = y) :
    (∀ i, infT F E (y i) = 0) ∧ ∀ u, u ≠ v → (fun i => compFin F E u (y i)) = 0 := by
  refine ⟨fun i => ?_, fun u hu => funext fun i => ?_⟩
  · rw [← hy]; exact infT_liftV_smul v (y i)
  · rw [← hy]; exact compFin_liftV_smul hu (y i)

/- English proof (translation)
Use `set y := (A - 1) *ᵥ z with hy`. Establish `hAz : A *ᵥ z = z + y` using `by rw [hy, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]`. Establish `hat : At (evFin F v) y` using `fun u hu => by rw [hy, ← Matrix.smul_mulVec, hA u hu, Matrix.zero_mulVec]`. Establish `hidem : GlobalTheory.LatVac.liftV v 1 • y = y` using `GlobalTheory.InertLagUniq.liftV_one_smul v y hat`. Take `⟨h1, h2⟩` from `comp_of_idem hidem`.

Use `⟨fun i => ?_, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hAz, Pi.add_apply, map_add, h1 i, add_zero]`. Use function extensionality and compare the values at `i`. Use `congrFun (h2 u hu) i` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`.

Rewrite using `[hAz, Pi.add_apply, map_add, this, add_zero]`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (compFin F E v) A z i`.
-/
theorem comp_mulVec {v : Pl F} {A : Matrix (Fin n) (Fin n) (AE F E)} (hA : At (evFin F v) (A - 1))
    (z : Fin n → AE F E) :
    (∀ i, infT F E ((A *ᵥ z) i) = infT F E (z i)) ∧
      (∀ u, u ≠ v → (fun i => compFin F E u ((A *ᵥ z) i)) = fun i => compFin F E u (z i)) ∧
      (fun i => compFin F E v ((A *ᵥ z) i)) = A.map (compFin F E v) *ᵥ fun i => compFin F E v (z i) := by
  set y := (A - 1) *ᵥ z with hy
  have hAz : A *ᵥ z = z + y := by rw [hy, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  have hat : At (evFin F v) y := fun u hu => by rw [hy, ← Matrix.smul_mulVec, hA u hu, Matrix.zero_mulVec]
  have hidem : GlobalTheory.LatVac.liftV v 1 • y = y := GlobalTheory.InertLagUniq.liftV_one_smul v y hat
  obtain ⟨h1, h2⟩ := comp_of_idem hidem
  refine ⟨fun i => ?_, fun u hu => ?_, ?_⟩
  · rw [hAz, Pi.add_apply, map_add, h1 i, add_zero]
  · funext i
    have := congrFun (h2 u hu) i
    simp only [Pi.zero_apply] at this
    rw [hAz, Pi.add_apply, map_add, this, add_zero]
  · funext i
    exact RingHom.map_mulVec (compFin F E v) A z i

def liftVec (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) : Fin n → AE F E := fun i => lift v (y i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [liftVec, Pi.smul_apply]`. Rewrite using `[liftV_one_smul_eq, compFin_lift]`.
-/
theorem liftVec_idem (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) :
    GlobalTheory.LatVac.liftV v 1 • liftVec v y = liftVec v y := by
  funext i
  simp only [liftVec, Pi.smul_apply]
  rw [liftV_one_smul_eq, compFin_lift]

/- English proof (translation)
The claim follows from `funext fun i => compFin_lift v (y i)`.
-/
theorem compFin_liftVec (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) :
    (fun i => compFin F E v (liftVec v y i)) = y := funext fun i => compFin_lift v (y i)

/- English proof (translation)
Take `⟨h1, h2⟩` from `comp_of_idem (liftVec_idem v y)`. Rewrite using `[mem_latHat_iff_comp hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Use `h v` as an intermediate fact.

Rewrite `this` using `[compFin_liftVec]`. Then use the resulting hypothesis. Introduce `hy`. Use `⟨h1, fun u => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Rewrite using `[compFin_liftVec]`. Conclude with `hy`. Rewrite using `[h2 u hu]`. Conclude with `zero_mem _`.
-/
theorem liftVec_mem_iff {W : Spc F E n} (hL : W.L.FG) (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) :
    liftVec v y ∈ latHat W ↔ y ∈ latLoc F W.L v := by
  obtain ⟨h1, h2⟩ := comp_of_idem (liftVec_idem v y)
  rw [mem_latHat_iff_comp hL]
  constructor
  · rintro ⟨-, h⟩; have := h v; rwa [compFin_liftVec] at this
  · intro hy
    refine ⟨h1, fun u => ?_⟩
    by_cases hu : u = v
    · subst hu; rw [compFin_liftVec]; exact hy
    · rw [h2 u hu]; exact zero_mem _

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `comp_mulVec hA z`. Rewrite using `[mem_latHat_iff_comp hL]`. Simplify using `only [h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hi, h⟩`.

Use `⟨hi, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Use `h u` as an intermediate fact. Rewrite `this` using `[h2 u hu]`. Then use the resulting hypothesis. Use `h v` as an intermediate fact. Rewrite `this` using `[h3]`. Then use the resulting hypothesis.

Introduce and unpack `⟨hi, hu, hv⟩`. Use `⟨hi, fun u => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Rewrite using `[h3]`.

Conclude with `hv`. Rewrite using `[h2 u e]`. Conclude with `hu u e`.
-/
theorem mulVec_mem_iff {W : Spc F E n} (hL : W.L.FG) {v : Pl F} {A : Matrix (Fin n) (Fin n) (AE F E)}
    (hA : At (evFin F v) (A - 1)) (z : Fin n → AE F E) :
    A *ᵥ z ∈ latHat W ↔ (∀ i, infT F E (z i) = 0) ∧
      (∀ u, u ≠ v → (fun i => compFin F E u (z i)) ∈ latLoc F W.L u) ∧
      A.map (compFin F E v) *ᵥ (fun i => compFin F E v (z i)) ∈ latLoc F W.L v := by
  obtain ⟨h1, h2, h3⟩ := comp_mulVec hA z
  rw [mem_latHat_iff_comp hL]
  simp only [h1]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun u hu => ?_, ?_⟩
    · have := h u; rwa [h2 u hu] at this
    · have := h v; rwa [h3] at this
  · rintro ⟨hi, hu, hv⟩
    refine ⟨hi, fun u => ?_⟩
    by_cases e : u = v
    · subst e; rw [h3]; exact hv
    · rw [h2 u e]; exact hu u e

end Lat

section Main

variable (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} (W : Spc F E d) (v : Pl F)

def toLoc (δ : E) (g : GlobalTheory.SphLine.locU σ W v) : GLoc σ (δ • W.J.map σ) v :=
  ⟨Formalism.UG.bc (compFin F E v) g.1.1, unitary_compFin σ hσ W.J δ v g.1⟩

def ofLoc {δ : E} (hδ : δ ≠ 0) (h : GLoc σ (δ • W.J.map σ) v) : GlobalTheory.SphLine.locU σ W v :=
  ⟨⟨⟨up v (HA.mat _ σ _ h).1, up v (HA.mat _ σ _ h)⁻¹.1,
      by rw [← up_mul, Units.mul_inv, up_one], by rw [← up_mul, Units.inv_mul, up_one]⟩,
    unitary_up σ W.J v _ (unitary_of_loc σ hσ W.J hδ v _ h.2)⟩, at_up v _⟩

def locEquiv {δ : E} (hδ : δ ≠ 0) : GlobalTheory.SphLine.locU σ W v ≃* GLoc σ (δ • W.J.map σ) v where
  toFun := toLoc σ hσ W v δ
  invFun := ofLoc σ hσ W v hδ
  left_inv g := Subtype.ext (Subtype.ext (Units.ext (up_compFin v g.2)))
  right_inv h := GlobalTheory.AutFunCompare.HA_ext σ _ fun r s => congrFun (congrFun (compFin_up v _) r) s
  map_mul' g h := GlobalTheory.AutFunCompare.HA_ext σ _ fun r s =>
    congrArg (fun x : GL (Fin d) (Fv F v ⊗[F] E) => x.1 r s) (map_mul (Formalism.UG.bc (compFin F E v)) g.1.1 h.1.1)

/- English proof (translation)
Establish `hg : At (evFin F v) (mat g.1 - 1)` using `g.2`. Establish `hgi : At (evFin F v) (mat g.1⁻¹ - 1)` using `(g⁻¹).2`. Establish `hiH : (mat g.1⁻¹).map (compFin F E v) * (mat g.1).map (compFin F E v) = 1`. Rewrite using `[← Matrix.map_mul, GlobalTheory.SphLine.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hHi : (mat g.1).map (compFin F E v) * (mat g.1⁻¹).map (compFin F E v) = 1`.

Rewrite using `[← Matrix.map_mul, ← GlobalTheory.SphLine.mat_mul, mul_inv_cancel, GlobalTheory.SphLine.mat_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[GlobalTheory.SphLine.mem_locK, mem_stabLoc]`. Express the relevant statement in the definitionally equal form `(g.1 ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latHat W, mat g.1 *ᵥ z ∈ latHat W ∧ mat g.1⁻¹ *ᵥ z ∈ latHat W) ↔ ∀ y, y ∈ latLoc F W.L v ↔ (mat g.1).map (compFin F E v) *ᵥ y ∈ latLoc F W.L v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hK⟩ y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `(hK _ ((liftVec_mem_iff hL v y).2 hy)).1` as an intermediate fact. Rewrite `this` using `[mulVec_mem_iff hL hg, compFin_liftVec]`. Conclude with `this.2.2`.

Introduce `hy`. Use `(hK _ ((liftVec_mem_iff hL v _).2 hy)).2` as an intermediate fact. Rewrite `this` using `[mulVec_mem_iff hL hgi, compFin_liftVec, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]`. Conclude with `this.2.2`. Introduce `hS`.

Use `⟨g.2, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨hi, hu⟩` from `(mem_latHat_iff_comp hL z).1 hz`. Use `⟨(mulVec_mem_iff hL hg z).2 ⟨hi, fun u _ => hu u, (hS _).1 (hu v)⟩, (mulVec_mem_iff hL hgi z).2 ⟨hi, fun u _ => hu u, ?_⟩⟩` and prove the remaining obligations. Use `(hS _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]`.

Conclude with `hu v`.
-/
theorem locEquiv_mem_iff {δ : E} (hδ : δ ≠ 0) (hL : W.L.FG) (g : GlobalTheory.SphLine.locU σ W v) :
    g.1 ∈ GlobalTheory.SphLine.locK σ W v ↔ locEquiv σ hσ W v hδ g ∈ stabLoc σ (δ • W.J.map σ) W.L v := by
  have hg : At (evFin F v) (mat g.1 - 1) := g.2
  have hgi : At (evFin F v) (mat g.1⁻¹ - 1) := (g⁻¹).2
  have hiH : (mat g.1⁻¹).map (compFin F E v) * (mat g.1).map (compFin F E v) = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.SphLine.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hHi : (mat g.1).map (compFin F E v) * (mat g.1⁻¹).map (compFin F E v) = 1 := by
    rw [← Matrix.map_mul, ← GlobalTheory.SphLine.mat_mul, mul_inv_cancel, GlobalTheory.SphLine.mat_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [GlobalTheory.SphLine.mem_locK, mem_stabLoc]
  change (g.1 ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latHat W, mat g.1 *ᵥ z ∈ latHat W ∧ mat g.1⁻¹ *ᵥ z ∈ latHat W) ↔
    ∀ y, y ∈ latLoc F W.L v ↔ (mat g.1).map (compFin F E v) *ᵥ y ∈ latLoc F W.L v
  constructor
  · rintro ⟨-, hK⟩ y
    constructor
    · intro hy
      have := (hK _ ((liftVec_mem_iff hL v y).2 hy)).1
      rw [mulVec_mem_iff hL hg, compFin_liftVec] at this
      exact this.2.2
    · intro hy
      have := (hK _ ((liftVec_mem_iff hL v _).2 hy)).2
      rw [mulVec_mem_iff hL hgi, compFin_liftVec, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec] at this
      exact this.2.2
  · intro hS
    refine ⟨g.2, fun z hz => ?_⟩
    obtain ⟨hi, hu⟩ := (mem_latHat_iff_comp hL z).1 hz
    refine ⟨(mulVec_mem_iff hL hg z).2 ⟨hi, fun u _ => hu u, (hS _).1 (hu v)⟩,
      (mulVec_mem_iff hL hgi z).2 ⟨hi, fun u _ => hu u, ?_⟩⟩
    refine (hS _).2 ?_
    rw [Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    exact hu v

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d W v δ hδ hL`. Conclude with `⟨locEquiv σ hσ W v hδ, locEquiv_mem_iff σ hσ W v hδ hL⟩`.
-/
theorem exists_locEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (δ : E), δ ≠ 0 → W.L.FG →
    ∃ e : GlobalTheory.SphLine.locU σ W v ≃* GLoc σ (δ • W.J.map σ) v,
      ∀ g, g.1 ∈ GlobalTheory.SphLine.locK σ W v ↔ e g ∈ stabLoc σ (δ • W.J.map σ) W.L v := by
  intro F E _ _ _ _ _ σ hσ d W v δ hδ hL
  exact ⟨locEquiv σ hσ W v hδ, locEquiv_mem_iff σ hσ W v hδ hL⟩

end GlobalTheory.SphLineLoc
