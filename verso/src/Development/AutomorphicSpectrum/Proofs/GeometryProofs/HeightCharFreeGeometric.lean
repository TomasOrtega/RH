import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelRankBoundNormValuationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteKernelNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientOfPowerFnsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFnsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinearStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LemFGeo

section Lin

variable {k : Type} [Field k]

def Tm {d : ℕ} (ρ ρb A : Matrix (Fin d) (Fin d) k) : Module.End k ((Fin d → k) × (Fin d → k)) :=
  LinearMap.prod (Matrix.toLin' ρ ∘ₗ LinearMap.fst k _ _)
    (Matrix.toLin' ρb.transpose ∘ₗ LinearMap.snd k _ _ - Matrix.toLin' A.transpose ∘ₗ LinearMap.fst k _ _)

/- English proof (translation)
Simplify using `[Tm]`.
-/
theorem Tm_apply {d : ℕ} (ρ ρb A : Matrix (Fin d) (Fin d) k) (y : (Fin d → k) × (Fin d → k)) :
    Tm ρ ρb A y = (ρ.mulVec y.1, ρb.transpose.mulVec y.2 - A.transpose.mulVec y.1) := by
  simp [Tm]

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (f.domRestrict K)`. Rewrite `h` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict]`. Establish `h2 : Module.finrank k ((LinearMap.ker f).comap K.subtype) = Module.finrank k (K ⊓ LinearMap.ker f : Submodule k W)`. Rewrite using `[← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_map_add {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k W] (K : Submodule k W) (f : W →ₗ[k] V) :
    Module.finrank k K ≤ Module.finrank k (K.map f) + Module.finrank k (K ⊓ LinearMap.ker f : Submodule k W) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict K)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have h2 : Module.finrank k ((LinearMap.ker f).comap K.subtype) =
      Module.finrank k (K ⊓ LinearMap.ker f : Submodule k W) := by
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  omega

/- English proof (translation)
Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap S)`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker S`. Establish `h3 : Module.finrank k (LinearMap.range (LinearMap.dualMap S)) = Module.finrank k (LinearMap.range S)` using `LinearMap.finrank_range_dualMap_eq_finrank_range S`. Establish `h4 : Module.finrank k (Module.Dual k L) = Module.finrank k L` using `Subspace.dual_finrank_eq`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_ker_dualMap {L : Type} [AddCommGroup L] [Module k L] [FiniteDimensional k L] (S : Module.End k L) :
    Module.finrank k (LinearMap.ker (LinearMap.dualMap S)) = Module.finrank k (LinearMap.ker S) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap S)
  have h2 := LinearMap.finrank_range_add_finrank_ker S
  have h3 : Module.finrank k (LinearMap.range (LinearMap.dualMap S)) = Module.finrank k (LinearMap.range S) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range S
  have h4 : Module.finrank k (Module.Dual k L) = Module.finrank k L := Subspace.dual_finrank_eq
  omega

/- English proof (translation)
Establish `e : LinearMap.ker f = (LinearMap.ker g).map (T : W →ₗ[k] W)`. Use extensionality with `y`. Establish `hy : ∀ z, f (T z) = T (g z)` using `fun z => LinearMap.congr_fun h z`. Simplify using `only [LinearMap.mem_ker, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `hf`. Use `⟨T.symm y, ?_, by simp⟩` and prove the remaining obligations. Use `hy (T.symm y)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, hf]`. Simplify using `using this.symm`.

Introduce and unpack `⟨z, hz, rfl⟩`. Use `hy z` as an intermediate fact. Simplify using `only [LinearEquiv.coe_coe] at *`. Rewrite using `[this, hz, map_zero]`. Rewrite using `[e]`.

Conclude with `LinearEquiv.finrank_map_eq T _`.
-/
theorem finrank_ker_conj {W : Type} [AddCommGroup W] [Module k W] (T : W ≃ₗ[k] W) (f g : Module.End k W)
    (h : f ∘ₗ (T : W →ₗ[k] W) = (T : W →ₗ[k] W) ∘ₗ g) :
    Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker g) := by
  have e : LinearMap.ker f = (LinearMap.ker g).map (T : W →ₗ[k] W) := by
    ext y
    have hy : ∀ z, f (T z) = T (g z) := fun z => LinearMap.congr_fun h z
    simp only [LinearMap.mem_ker, Submodule.mem_map]
    constructor
    · intro hf
      refine ⟨T.symm y, ?_, by simp⟩
      have := hy (T.symm y)
      rw [LinearEquiv.apply_symm_apply, hf] at this
      simpa using this.symm
    · rintro ⟨z, hz, rfl⟩
      have := hy z
      simp only [LinearEquiv.coe_coe] at *
      rw [this, hz, map_zero]
  rw [e]
  exact LinearEquiv.finrank_map_eq T _

/- English proof (translation)
Apply the tactic sequence `let T : ((Fin d → k) × (Fin d → k)) ≃ₗ[k] ((Fin d → k) × (Fin d → k)) := LinearEquiv.ofLinear (LinearMap.prod (LinearMap.fst k _ _) (LinearMap.snd k _ _ + Matrix.toLin' Z.transpose ∘ₗ LinearMap.fst k _ _)) (LinearMap.prod (LinearMap.fst k _ _) (LinearMap.snd k _ _ - Matrix.toLin' …`. Establish `hT : ∀ y, T y = (y.1, y.2 + Z.transpose.mulVec y.1)` using `fun y => by`. Simplify using `[T, LinearEquiv.ofLinear_apply]`. Use `finrank_ker_conj T _ _ (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, Tm_apply]`.

Use `Prod.ext rfl ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]`. Normalize the expressions using the abelian group laws.
-/
theorem finrank_ker_gauge {d : ℕ} (ρ ρb A Z : Matrix (Fin d) (Fin d) k) :
    Module.finrank k (LinearMap.ker (Tm ρ ρb A)) =
      Module.finrank k (LinearMap.ker (Tm ρ ρb (A + ρ.transpose * Z - Z * ρb))) := by
  let T : ((Fin d → k) × (Fin d → k)) ≃ₗ[k] ((Fin d → k) × (Fin d → k)) :=
    LinearEquiv.ofLinear
      (LinearMap.prod (LinearMap.fst k _ _)
        (LinearMap.snd k _ _ + Matrix.toLin' Z.transpose ∘ₗ LinearMap.fst k _ _))
      (LinearMap.prod (LinearMap.fst k _ _)
        (LinearMap.snd k _ _ - Matrix.toLin' Z.transpose ∘ₗ LinearMap.fst k _ _))
      (by ext <;> simp) (by ext <;> simp)
  have hT : ∀ y, T y = (y.1, y.2 + Z.transpose.mulVec y.1) := fun y => by
    simp [T, LinearEquiv.ofLinear_apply]
  refine finrank_ker_conj T _ _ (LinearMap.ext fun y => ?_)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, Tm_apply]
  refine Prod.ext rfl ?_
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
  abel

/- English proof (translation)
Take `⟨Q, hQ⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs`. Establish `hQt : Q.transpose * P.transpose = 1` using `by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]`. Establish `hPj : ∀ v, P.mulVec (j v) = 0` using `fun v => (hk _).2 ⟨v, rfl⟩`. Establish `hAj : ∀ v, A.mulVec (j v) = 0` using `fun v => by`. Rewrite using `[hA, ← Matrix.mulVec_mulVec, hPj, Matrix.mulVec_zero]`.

Set `c : ((Fin d → k) × (Fin d → k)) →ₗ[k] Module.Dual k L` to `LinearMap.dualMap j ∘ₗ (dotProductBilin k k) ∘ₗ LinearMap.snd k _ _`. Establish `hc : ∀ y v, c y v = y.2 ⬝ᵥ j v` using `fun y v => rfl`. Set `m : ((Fin d → k) × (Fin d → k)) →ₗ[k] ((Fin d' → k) × (Fin d' → k))` to `LinearMap.prodMap (Matrix.toLin' P) (Matrix.toLin' Q.transpose)`. Establish `hm : ∀ y, m y = (P.mulVec y.1, Q.transpose.mulVec y.2)` using `fun y => by simp [m]`. Use `set K := LinearMap.ker (Tm ρ ρb A) with hK`.

Establish `hKy : ∀ y ∈ K, ρ.mulVec y.1 = 0 ∧ ρb.transpose.mulVec y.2 - A.transpose.mulVec y.1 = 0`. Introduce `y hy`. Establish `: Tm ρ ρb A y = 0` using `hy`. Rewrite `this` using `[Tm_apply]`. Conclude with `⟨congrArg Prod.fst this, congrArg Prod.snd this⟩`.

Establish `s1 : K.map c ≤ LinearMap.ker (LinearMap.dualMap Sb)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨-, e2⟩` from `hKy y hy`. Use `LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Use `show c y (Sb v) = 0`.

Rewrite using `[hc, hjb, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]`. Use `congrArg (fun w => w ⬝ᵥ j v) e2` as an intermediate fact. Simplify using `only [sub_dotProduct, zero_dotProduct] at this`. Establish `e3 : A.transpose.mulVec y.1 ⬝ᵥ j v = 0`. Rewrite using `[Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAj, dotProduct_zero]`.

Rewrite `this` using `[e3, sub_zero]`. Conclude with `this`. Establish `hφ : ∀ y, c y = 0 → P.transpose.mulVec (Q.transpose.mulVec y.2) = y.2`. Introduce `y hy`. Use `dotProduct_eq _ _ fun w => ?_` and prove the remaining obligations.

Establish `e1 : P.mulVec (w - (Q * P).mulVec w) = 0`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]`. Take `⟨v, hv⟩` from `(hk _).1 e1`. Establish `e2 : y.2 ⬝ᵥ (w - (Q * P).mulVec w) = 0`. Rewrite using `[← hv, ← hc, hy]`.

Both sides reduce to the same expression. Rewrite `e2` using `[dotProduct_sub, sub_eq_zero]`. Establish `hT : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) k) (v : Fin a → k) (w : Fin b → k), M.transpose.mulVec v ⬝ᵥ w = v ⬝ᵥ M.mulVec w` using `fun M v w => by`. Rewrite using `[Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]`. Rewrite using `[hT, hT, Matrix.mulVec_mulVec]`.

Conclude with `e2.symm`. Establish `s2 : (K ⊓ LinearMap.ker c).map m ≤ LinearMap.ker (Tm ρB ρbB AB)`. Introduce and unpack `_ ⟨y, ⟨hy, hcy⟩, rfl⟩`. Take `⟨e1, e2⟩` from `hKy y hy`. Establish `hcy' : c y = 0` using `hcy`.

Establish `e3` using `hφ y hcy'`. Use `LinearMap.mem_ker.2 ?_` and prove the remaining obligations. Rewrite using `[Tm_apply, hm]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show ρB.mulVec (P.mulVec y.1) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_zero]`. Use `show ρbB.transpose.mulVec (Q.transpose.mulVec y.2) - AB.transpose.mulVec (P.mulVec y.1) = 0`. Establish `e4 : Q.transpose.mulVec (ρb.transpose.mulVec y.2 - A.transpose.mulVec y.1) = 0`. Rewrite using `[e2, Matrix.mulVec_zero]`. Establish `e5 : ρb.transpose.mulVec y.2 = P.transpose.mulVec (ρbB.transpose.mulVec (Q.transpose.mulVec y.2))` using `by conv_lhs => rw [← e3]`.

Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h2, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]`. Establish `e6 : A.transpose.mulVec y.1 = P.transpose.mulVec (AB.transpose.mulVec (P.mulVec y.1))`. Rewrite using `[hA]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `e7 : ∀ v, Q.transpose.mulVec (P.transpose.mulVec v) = v` using `fun v => by`.

Rewrite using `[Matrix.mulVec_mulVec, hQt, Matrix.one_mulVec]`. Rewrite `e4` using `[e5, e6, Matrix.mulVec_sub, e7, e7]`. Conclude with `e4`. Establish `s3 : (K ⊓ LinearMap.ker c) ⊓ LinearMap.ker m ≤ (LinearMap.ker Sa).map (LinearMap.inl k (Fin d → k) (Fin d → k) ∘ₗ j)`. Introduce and unpack `y ⟨⟨hy, hcy⟩, hmy⟩`.

Establish `hcy' : c y = 0` using `hcy`. Establish `hmy' : m y = 0` using `hmy`. Rewrite `hmy'` using `[hm]`. Establish `m1 : P.mulVec y.1 = 0` using `congrArg Prod.fst hmy'`. Establish `m2 : Q.transpose.mulVec y.2 = 0` using `congrArg Prod.snd hmy'`.

Establish `e3` using `hφ y hcy'`. Rewrite `e3` using `[m2, Matrix.mulVec_zero]`. Take `⟨v, hv⟩` from `(hk _).1 m1`. Take `⟨e1, -⟩` from `hKy y hy`. Use `⟨v, ?_, Prod.ext (by simpa using hv) (by simpa using e3)⟩` and prove the remaining obligations.

Use `LinearMap.mem_ker.2 (hi ?_)` and prove the remaining obligations. Rewrite using `[hja, hv, e1, map_zero]`. Establish `f1` using `finrank_le_map_add K c`. Establish `f2` using `finrank_le_map_add (K ⊓ LinearMap.ker c) m`. Establish `g1` using `Submodule.finrank_mono s1`.

Establish `g2` using `Submodule.finrank_mono s2`. Establish `g3` using `Submodule.finrank_mono s3`. Establish `g4` using `Submodule.finrank_map_le (LinearMap.inl k (Fin d → k) (Fin d → k) ∘ₗ j) (LinearMap.ker Sa)`. Rewrite `g1` using `[finrank_ker_dualMap]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ker_bound {d d' : ℕ} {L : Type} [AddCommGroup L] [Module k L] [FiniteDimensional k L]
    (P : Matrix (Fin d') (Fin d) k) (ρ ρb A : Matrix (Fin d) (Fin d) k) (ρB ρbB AB : Matrix (Fin d') (Fin d') k)
    (Sa Sb : Module.End k L) (j : L →ₗ[k] (Fin d → k)) (hs : Function.Surjective P.mulVec)
    (hi : Function.Injective j) (hk : ∀ u, P.mulVec u = 0 ↔ u ∈ LinearMap.range j)
    (h1 : P * ρ = ρB * P) (h2 : P * ρb = ρbB * P) (hA : A = P.transpose * AB * P)
    (hja : ∀ v, j (Sa v) = ρ.mulVec (j v)) (hjb : ∀ v, j (Sb v) = ρb.mulVec (j v)) :
    Module.finrank k (LinearMap.ker (Tm ρ ρb A)) ≤
      Module.finrank k (LinearMap.ker Sb) + Module.finrank k (LinearMap.ker (Tm ρB ρbB AB)) +
        Module.finrank k (LinearMap.ker Sa) := by
  obtain ⟨Q, hQ⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs
  have hQt : Q.transpose * P.transpose = 1 := by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  have hPj : ∀ v, P.mulVec (j v) = 0 := fun v => (hk _).2 ⟨v, rfl⟩
  have hAj : ∀ v, A.mulVec (j v) = 0 := fun v => by
    rw [hA, ← Matrix.mulVec_mulVec, hPj, Matrix.mulVec_zero]

  let c : ((Fin d → k) × (Fin d → k)) →ₗ[k] Module.Dual k L :=
    LinearMap.dualMap j ∘ₗ (dotProductBilin k k) ∘ₗ LinearMap.snd k _ _
  have hc : ∀ y v, c y v = y.2 ⬝ᵥ j v := fun y v => rfl
  let m : ((Fin d → k) × (Fin d → k)) →ₗ[k] ((Fin d' → k) × (Fin d' → k)) :=
    LinearMap.prodMap (Matrix.toLin' P) (Matrix.toLin' Q.transpose)
  have hm : ∀ y, m y = (P.mulVec y.1, Q.transpose.mulVec y.2) := fun y => by simp [m]
  set K := LinearMap.ker (Tm ρ ρb A) with hK
  have hKy : ∀ y ∈ K, ρ.mulVec y.1 = 0 ∧ ρb.transpose.mulVec y.2 - A.transpose.mulVec y.1 = 0 := by
    intro y hy
    have : Tm ρ ρb A y = 0 := hy
    rw [Tm_apply] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

  have s1 : K.map c ≤ LinearMap.ker (LinearMap.dualMap Sb) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨-, e2⟩ := hKy y hy
    refine LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)
    show c y (Sb v) = 0
    rw [hc, hjb, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have := congrArg (fun w => w ⬝ᵥ j v) e2
    simp only [sub_dotProduct, zero_dotProduct] at this
    have e3 : A.transpose.mulVec y.1 ⬝ᵥ j v = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAj, dotProduct_zero]
    rw [e3, sub_zero] at this
    exact this

  have hφ : ∀ y, c y = 0 → P.transpose.mulVec (Q.transpose.mulVec y.2) = y.2 := by
    intro y hy
    refine dotProduct_eq _ _ fun w => ?_
    have e1 : P.mulVec (w - (Q * P).mulVec w) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]
    obtain ⟨v, hv⟩ := (hk _).1 e1
    have e2 : y.2 ⬝ᵥ (w - (Q * P).mulVec w) = 0 := by
      rw [← hv, ← hc, hy]; rfl
    rw [dotProduct_sub, sub_eq_zero] at e2
    have hT : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) k) (v : Fin a → k) (w : Fin b → k),
        M.transpose.mulVec v ⬝ᵥ w = v ⬝ᵥ M.mulVec w := fun M v w => by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    rw [hT, hT, Matrix.mulVec_mulVec]
    exact e2.symm
  have s2 : (K ⊓ LinearMap.ker c).map m ≤ LinearMap.ker (Tm ρB ρbB AB) := by
    rintro _ ⟨y, ⟨hy, hcy⟩, rfl⟩
    obtain ⟨e1, e2⟩ := hKy y hy
    have hcy' : c y = 0 := hcy
    have e3 := hφ y hcy'
    refine LinearMap.mem_ker.2 ?_
    rw [Tm_apply, hm]
    refine Prod.ext ?_ ?_
    · show ρB.mulVec (P.mulVec y.1) = 0
      rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_zero]
    · show ρbB.transpose.mulVec (Q.transpose.mulVec y.2) - AB.transpose.mulVec (P.mulVec y.1) = 0
      have e4 : Q.transpose.mulVec (ρb.transpose.mulVec y.2 - A.transpose.mulVec y.1) = 0 := by
        rw [e2, Matrix.mulVec_zero]
      have e5 : ρb.transpose.mulVec y.2 = P.transpose.mulVec (ρbB.transpose.mulVec (Q.transpose.mulVec y.2)) := by
        conv_lhs => rw [← e3]
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h2, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
      have e6 : A.transpose.mulVec y.1 = P.transpose.mulVec (AB.transpose.mulVec (P.mulVec y.1)) := by
        rw [hA]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have e7 : ∀ v, Q.transpose.mulVec (P.transpose.mulVec v) = v := fun v => by
        rw [Matrix.mulVec_mulVec, hQt, Matrix.one_mulVec]
      rw [e5, e6, Matrix.mulVec_sub, e7, e7] at e4
      exact e4
  have s3 : (K ⊓ LinearMap.ker c) ⊓ LinearMap.ker m ≤
      (LinearMap.ker Sa).map (LinearMap.inl k (Fin d → k) (Fin d → k) ∘ₗ j) := by
    rintro y ⟨⟨hy, hcy⟩, hmy⟩
    have hcy' : c y = 0 := hcy
    have hmy' : m y = 0 := hmy
    rw [hm] at hmy'
    have m1 : P.mulVec y.1 = 0 := congrArg Prod.fst hmy'
    have m2 : Q.transpose.mulVec y.2 = 0 := congrArg Prod.snd hmy'
    have e3 := hφ y hcy'
    rw [m2, Matrix.mulVec_zero] at e3
    obtain ⟨v, hv⟩ := (hk _).1 m1
    obtain ⟨e1, -⟩ := hKy y hy
    refine ⟨v, ?_, Prod.ext (by simpa using hv) (by simpa using e3)⟩
    refine LinearMap.mem_ker.2 (hi ?_)
    rw [hja, hv, e1, map_zero]
  have f1 := finrank_le_map_add K c
  have f2 := finrank_le_map_add (K ⊓ LinearMap.ker c) m
  have g1 := Submodule.finrank_mono s1
  have g2 := Submodule.finrank_mono s2
  have g3 := Submodule.finrank_mono s3
  have g4 := Submodule.finrank_map_le (LinearMap.inl k (Fin d → k) (Fin d → k) ∘ₗ j) (LinearMap.ker Sa)
  rw [finrank_ker_dualMap] at g1
  omega

end Lin

/- English proof (translation)
Establish `hA0 : A ≠ 0`. Introduce and unpack `rfl`. Rewrite `hA` using `[zero_pow hn.ne']`. Conclude with `pow_ne_zero _ hM hA.symm`. Establish `h3 : n * padicValNat p A = 2 * d' * padicValNat p M`.

Rewrite using `[← padicValNat.pow, hA, padicValNat.pow]`. Establish `h4 : D ≤ padicValNat p A` using `(padicValNat_dvd_iff_le hA0).1 hD`. Establish `h5 : n * (ρ₀ * padicValNat p M + D + ρ₀ * padicValNat p M) ≤ n * (r * padicValNat p M)`. Establish `e : n * r = 2 * d' + 2 * (n * ρ₀)` using `by rw [← h2, hdd, hN]; ring`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Nat.le_of_mul_le_mul_left h5 hn`.
-/
theorem numeric {p : ℕ} [Fact p.Prime] {n N ρ₀ r d d' D A M : ℕ} (hn : 0 < n) (hN : N = n * ρ₀)
    (hdd : d = d' + N) (h2 : 2 * d = n * r) (hA : A ^ n = M ^ (2 * d')) (hM : M ≠ 0) (hD : p ^ D ∣ A) :
    ρ₀ * padicValNat p M + D + ρ₀ * padicValNat p M ≤ r * padicValNat p M := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hA
    exact pow_ne_zero _ hM hA.symm
  have h3 : n * padicValNat p A = 2 * d' * padicValNat p M := by
    rw [← padicValNat.pow, hA, padicValNat.pow]
  have h4 : D ≤ padicValNat p A := (padicValNat_dvd_iff_le hA0).1 hD
  have h5 : n * (ρ₀ * padicValNat p M + D + ρ₀ * padicValNat p M) ≤ n * (r * padicValNat p M) := by
    have e : n * r = 2 * d' + 2 * (n * ρ₀) := by rw [← h2, hdd, hN]; ring
    calc n * (ρ₀ * padicValNat p M + D + ρ₀ * padicValNat p M)
        = 2 * (n * ρ₀) * padicValNat p M + n * D := by ring
      _ ≤ 2 * (n * ρ₀) * padicValNat p M + n * padicValNat p A := by gcongr
      _ = (2 * d' + 2 * (n * ρ₀)) * padicValNat p M := by rw [h3]; ring
      _ = n * (r * padicValNat p M) := by rw [← e]; ring
  exact Nat.le_of_mul_le_mul_left h5 hn

/- English proof (translation)
Establish `hm : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.Monic` using `LinearMap.charpoly_monic _`. Rewrite using `[(hm.map _).natDegree_pow, hm.natDegree_map, LinearMap.charpoly_natDegree, RingOfIntegers.rank, mul_comm]`.
-/
theorem natDegree_charpoly_pow (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (a : 𝓞 E) (r : ℕ) :
    (((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r).natDegree =
      Module.finrank ℚ E * r := by
  have hm : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.Monic := LinearMap.charpoly_monic _
  rw [(hm.map _).natDegree_pow, hm.natDegree_map, LinearMap.charpoly_natDegree, RingOfIntegers.rank, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Flat.LemFGeo

namespace GlobalTheory.CompanionTheory.Ar.Flat

open LemFGeo in

/- English proof (translation)
Introduce `E _ _ _ H _ hbar X t hP k _ _ p _ _ x hG d r g hc`. Take `⟨Q⟩` from `GlobalTheory.T.abelian_quotient_of_power_fns E H X t hP k p x hG`. Take `⟨d', ⟨gB⟩⟩` from `GlobalTheory.T.exists_formal_germ_local E H hbar (Sp k) Q.tB (GlobalTheory.T.proper_has_power_fns E H k Q.tB Q.proper) k (𝟙 (Sp k))`. Take `⟨Λ, _, _, _, _, P, j, hD, hs, hi, hk, hρ, hj⟩` from `GlobalTheory.T.abelian_quotient_lattice E H hbar X t k p x Q d d' g gB`. Take `⟨Z, hZ⟩` from `GlobalTheory.T.abelian_quotient_bilinear E H hbar X t k p x Q d d' g gB P hD`.

Take `⟨⟨ρH, hρH⟩, -, -⟩` from `GlobalTheory.T.formal_hermitian_action_pairing k d (𝓞 E) g.B`. Set `S : 𝓞 E → Module.End k (TensorProduct ℤ k Λ)` to `fun a => LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)`. Establish `hn : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Establish `hN : Module.finrank k (TensorProduct ℤ k Λ) = Module.finrank ℚ E * Module.finrank (𝓞 E) Λ`. Establish `h` using `(GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ (1 : 𝓞 E) one_ne_zero).2`.

Establish `h'` using `congrArg Polynomial.natDegree h`. Rewrite `h'` using `[LinearMap.charpoly_natDegree, natDegree_charpoly_pow]`. Then use the resulting hypothesis. Establish `h2d : 2 * d = Module.finrank ℚ E * r`. Establish `h'` using `congrArg Polynomial.natDegree (hc 1)`. Rewrite `h'` using `[LinearMap.charpoly_natDegree, natDegree_charpoly_pow]`.

Rewrite using `[← h']`. Simplify using `[two_mul]`. Establish `hdd : d = d' + Module.finrank k (TensorProduct ℤ k Λ)`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)`. Establish `h2 : LinearMap.range (Matrix.toLin' P) = ⊤` using `LinearMap.range_eq_top.2 (fun v => by`.

Take `⟨u, hu⟩` from `hs v`. Conclude with `⟨u, by simpa using hu⟩)`. Establish `h3 : LinearMap.ker (Matrix.toLin' P) = LinearMap.range j`. Use extensionality with `u`. Simplify using `[hk]`.

Rewrite `h1` using `[h2, h3, finrank_top, LinearMap.finrank_range_of_inj hi]`. Simplify using `using h1.symm`. Establish `hb : ∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (rhoH g.B a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs`. Introduce `a ha`. Establish `hM : (Algebra.norm ℤ a).natAbs ≠ 0`.

Rewrite using `[Int.natAbs_ne_zero]`. Conclude with `Algebra.norm_ne_zero_iff.2 ha`. Establish `hba : star a ≠ 0` using `star_ne_zero.2 ha`. Establish `hnorm : (Algebra.norm ℤ (star a)).natAbs = (Algebra.norm ℤ a).natAbs`. Rewrite using `[hbar]`.

Conclude with `congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv (H.bar.toIntAlgEquiv) a)`. Establish `e1 : Module.finrank k (LinearMap.ker (rhoH g.B a)) = _` using `finrank_ker_gauge (rho g.B a) (rho g.B (star a)) (bil (g.B.ad a) 1 1) Z`. Rewrite `e1` using `[hZ a]`. Establish `e2` using `ker_bound P (rho g.B a) (rho g.B (star a)) (P.transpose * bil (gB.B.ad a) 1 1 * P) (rho gB.B a) (rho gB.B (star a)) (bil (gB.B.ad a) 1 1) (S a) (S (star a)) j hs hi hk (hρ a) (hρ _) rfl (hj a) (hj _)`. Take `⟨⟨A, _, _, _, i, hpb⟩, hdeg⟩` from `GlobalTheory.T.exists_finite_kernel_nonzero E H hbar k Q.tB Q.proper d' gB a ha`.

Establish `e3` using `GlobalTheory.T.proper_multiplication_kernel E H hbar k p Q.tB Q.proper Q.ktriv d' gB a A i hpb`. Establish `e5` using `numeric (p := p) hn hN hdd h2d (hdeg A i hpb) hM e3`. Establish `e6` using `(GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ a ha).1`. Establish `e7` using `(GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ (star a) hba).1`. Rewrite `e7` using `[hnorm]`.

Establish `e8 : Module.finrank k (LinearMap.ker (Tm (rho gB.B a) (rho gB.B (star a)) (bil (gB.B.ad a) 1 1))) = Module.finrank k (LinearMap.ker (rhoH gB.B a))` using `rfl`. Rewrite `e2` using `[e8]`. Establish `e9 : Module.finrank k (LinearMap.ker (S a)) ≤ _` using `e6`. Establish `e10 : Module.finrank k (LinearMap.ker (S (star a))) ≤ _` using `e7`. Rewrite using `[e1]`.

Conclude with `e2.trans ((add_le_add (add_le_add e10 le_rfl) e9).trans e5)`. Take `⟨y, hy1, hy2⟩` from `GlobalTheory.T.exists_free_basis_of_kernel_rank_le_norm_valuation E k ((Fin d → k) × (Fin d → k)) p r ρH (fun a => by rw [hρH]; exact hc a) (fun a ha => by rw [hρH]; exact hb a ha)`. Simplify using `only [hρH] at hy1 hy2`. Conclude with `⟨y, hy1, hy2⟩`.
-/
theorem hfree_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X), PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X), GeomPF t x → ∀ (d r : ℕ) (g : GermAt t x d), HChar g.B r → HFree g.B r := by
  intro E _ _ _ H _ hbar X t hP k _ _ p _ _ x hG d r g hc
  obtain ⟨Q⟩ := GlobalTheory.T.abelian_quotient_of_power_fns E H X t hP k p x hG
  obtain ⟨d', ⟨gB⟩⟩ := GlobalTheory.T.exists_formal_germ_local E H hbar (Sp k) Q.tB (GlobalTheory.T.proper_has_power_fns E H k Q.tB Q.proper) k (𝟙 (Sp k))
  obtain ⟨Λ, _, _, _, _, P, j, hD, hs, hi, hk, hρ, hj⟩ := GlobalTheory.T.abelian_quotient_lattice E H hbar X t k p x Q d d' g gB
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.abelian_quotient_bilinear E H hbar X t k p x Q d d' g gB P hD
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing k d (𝓞 E) g.B
  let S : 𝓞 E → Module.End k (TensorProduct ℤ k Λ) := fun a =>
    LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN : Module.finrank k (TensorProduct ℤ k Λ) = Module.finrank ℚ E * Module.finrank (𝓞 E) Λ := by
    have h := (GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ (1 : 𝓞 E) one_ne_zero).2
    have h' := congrArg Polynomial.natDegree h
    rwa [LinearMap.charpoly_natDegree, natDegree_charpoly_pow] at h'
  have h2d : 2 * d = Module.finrank ℚ E * r := by
    have h' := congrArg Polynomial.natDegree (hc 1)
    rw [LinearMap.charpoly_natDegree, natDegree_charpoly_pow] at h'
    rw [← h']
    simp [two_mul]
  have hdd : d = d' + Module.finrank k (TensorProduct ℤ k Λ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
    have h2 : LinearMap.range (Matrix.toLin' P) = ⊤ := LinearMap.range_eq_top.2 (fun v => by
      obtain ⟨u, hu⟩ := hs v
      exact ⟨u, by simpa using hu⟩)
    have h3 : LinearMap.ker (Matrix.toLin' P) = LinearMap.range j := by
      ext u
      simp [hk]
    rw [h2, h3, finrank_top, LinearMap.finrank_range_of_inj hi] at h1
    simpa using h1.symm
  have hb : ∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (rhoH g.B a)) ≤
      r * padicValNat p (Algebra.norm ℤ a).natAbs := by
    intro a ha
    have hM : (Algebra.norm ℤ a).natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero]
      exact Algebra.norm_ne_zero_iff.2 ha
    have hba : star a ≠ 0 := star_ne_zero.2 ha
    have hnorm : (Algebra.norm ℤ (star a)).natAbs = (Algebra.norm ℤ a).natAbs := by
      rw [hbar]
      exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv (H.bar.toIntAlgEquiv) a)
    have e1 : Module.finrank k (LinearMap.ker (rhoH g.B a)) = _ :=
      finrank_ker_gauge (rho g.B a) (rho g.B (star a)) (bil (g.B.ad a) 1 1) Z
    rw [hZ a] at e1
    have e2 := ker_bound P (rho g.B a) (rho g.B (star a)) (P.transpose * bil (gB.B.ad a) 1 1 * P) (rho gB.B a)
      (rho gB.B (star a)) (bil (gB.B.ad a) 1 1) (S a) (S (star a)) j hs hi hk (hρ a) (hρ _) rfl (hj a) (hj _)
    obtain ⟨⟨A, _, _, _, i, hpb⟩, hdeg⟩ := GlobalTheory.T.exists_finite_kernel_nonzero E H hbar k Q.tB Q.proper d' gB a ha
    have e3 := GlobalTheory.T.proper_multiplication_kernel E H hbar k p Q.tB Q.proper Q.ktriv d' gB a A i hpb
    have e5 := numeric (p := p) hn hN hdd h2d (hdeg A i hpb) hM e3
    have e6 := (GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ a ha).1
    have e7 := (GlobalTheory.T.lattice_kernel_rank_bound_norm E k p Λ (star a) hba).1
    rw [hnorm] at e7
    have e8 : Module.finrank k (LinearMap.ker (Tm (rho gB.B a) (rho gB.B (star a)) (bil (gB.B.ad a) 1 1))) =
      Module.finrank k (LinearMap.ker (rhoH gB.B a)) := rfl
    rw [e8] at e2
    have e9 : Module.finrank k (LinearMap.ker (S a)) ≤ _ := e6
    have e10 : Module.finrank k (LinearMap.ker (S (star a))) ≤ _ := e7
    rw [e1]
    exact e2.trans ((add_le_add (add_le_add e10 le_rfl) e9).trans e5)
  obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.exists_free_basis_of_kernel_rank_le_norm_valuation E k ((Fin d → k) × (Fin d → k)) p r ρH
    (fun a => by rw [hρH]; exact hc a) (fun a ha => by rw [hρH]; exact hb a ha)
  simp only [hρH] at hy1 hy2
  exact ⟨y, hy1, hy2⟩

end GlobalTheory.CompanionTheory.Ar.Flat
