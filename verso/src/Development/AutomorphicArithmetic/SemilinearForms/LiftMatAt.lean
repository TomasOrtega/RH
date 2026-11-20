import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open GlobalTheory.Mem.R3.DefLatBC

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

/- English proof (translation)
Set `v : Fin B.S.dim → B'.S.Forms` to `fun k => L (B.S.basis k)`. Set `bv : Basis (Fin B.S.dim) K' B'.S.Forms` to `Basis.mk hli hsp`. Establish `hbv : ∀ k, bv k = L (B.S.basis k)` using `fun k => Basis.mk_apply hli hsp k`. Set `C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'` to `B'.S.basis.toMatrix v`. Establish `hCe : ∀ a i, C a i = B'.S.basis.equivFun (L (B.S.basis i)) a`.

Introduce `a i`. Simplify using `[C, v, Basis.toMatrix_apply]`. Establish `hC : ∀ x, C *ᵥ x = B'.S.basis.equivFun (bv.equivFun.symm x)`. Introduce `x`. Use extensionality with `i`.

Simplify using `only [Matrix.mulVec, dotProduct, hCe, Basis.equivFun_symm_apply, hbv, map_sum, map_smul, Basis.equivFun_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]`. Establish `hL : ∀ f, L f = bv.equivFun.symm (fun k => φ (B.S.basis.equivFun f k))`. Introduce `f`. Use `conv_lhs => rw [← B.S.basis.sum_equivFun f]`. Rewrite using `[map_sum, Basis.equivFun_symm_apply]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, hbv]`. Establish `hψ : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x))`. Introduce `x`. Simplify using `only [hL, LinearEquiv.apply_symm_apply, hC]`.

Establish `hbc : ∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f`. Introduce `f`. Simplify using `only [GlobalTheory.Mem.R3.LiftLatBC.bcF]`. Rewrite using `[hC, LinearEquiv.symm_apply_apply, hL]`. Establish `hbij : Function.Bijective C.mulVec`.

Establish `he : C.mulVec = ⇑(bv.equivFun.symm.trans B'.S.basis.equivFun)` using `funext fun x => by`. Rewrite using `[hC]`. Both sides reduce to the same expression. Rewrite using `[he]`. Conclude with `LinearEquiv.bijective _`.

Establish `hH : Cᴴ * B'.S.H * C = B.S.H.map φ`. Use extensionality with `i j`. Establish `h1` using `csum_coords B'.S (B'.S.basis.equivFun (L (B.S.basis i))) (B'.S.basis.equivFun (L (B.S.basis j)))`. Simplify using `only [LinearEquiv.symm_apply_apply, hcs] at h1`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.L2.DIV.CSD.H, Matrix.of_apply, hCe]`.

Rewrite using `[h1]`. Simplify using `only [Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Establish `hrep : ∀ (T : Module.End K B.S.Forms) (f : B.S.Forms), LinearMap.toMatrix B.S.basis B.S.basis T *ᵥ B.S.basis.equivFun f = B.S.basis.equivFun (T f)` using `fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _`. Establish `hrep' : ∀ (T : Module.End K' B'.S.Forms) (f : B'.S.Forms), LinearMap.toMatrix B'.S.basis B'.S.basis T *ᵥ B'.S.basis.equivFun f = B'.S.basis.equivFun (T f)` using `fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _`.

Establish `hact' : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ`. Introduce `g`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `k`. Establish `hs : (Pi.single k 1 : Fin B.S.dim → K') = fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j)`.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : j = k <;> simp [Pi.single_apply, h]`. Establish `hk : (Pi.single k 1 : Fin B.S.dim → K) = B.S.basis.equivFun (B.S.basis k)`. Use function extensionality and compare the values at `j`. Rewrite using `[Basis.equivFun_self, Pi.single_apply]`.

Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs]`.

Establish `hm : (B.S.actMat B.r g).map φ *ᵥ (fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j)) = fun i => φ (((B.S.actMat B.r g) *ᵥ Pi.single k 1) i)`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec φ _ _ i).symm`. Rewrite using `[hm, hψ, hψ, hk]`. Simplify using `only [Formalism.L2.DIV.CSD.actMat, hrep, hrep', LinearEquiv.symm_apply_apply, hact]`.

Establish `hnab' : B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)))`. Establish `hset : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) = (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨B.S.basis.equivFun.symm x, (mem_nabLat_iff B.S x).mp hx, (hψ x).symm⟩`. Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨B.S.basis.equivFun f, (mem_nabLat_iff B.S _).mpr (by simpa using hf), ?_⟩` and prove the remaining obligations. Simplify using `only [hψ, LinearEquiv.symm_apply_apply]`. Rewrite using `[hset]`.

Use extensionality with `y`. Rewrite using `[mem_nabLat_iff, hnab (B'.S.basis.equivFun.symm y)]`. Set `E` to `B'.S.basis.equivFun.restrictScalars (𝓞 K')`. Establish `hE : (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} = (E : B'.S.Forms →ₗ[𝓞 K'] (Fin B'.S.dim → K')) '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})`. Rewrite using `[Set.image_image]`.

Both sides reduce to the same expression. Rewrite using `[hE, ← Submodule.map_span, Submodule.mem_map_equiv]`. Conclude with `Iff.rfl`. Establish `hcoord : B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))`. Rewrite using `[hZ]`.

Simplify using `only [Formalism.L2.DIV.BlockDat.coord, Submodule.map_span, Submodule.map_coe, LinearEquiv.coe_coe]`. Use `congr 1`. Rewrite using `[Set.image_image, Set.image_image]`. Use `Set.image_congr fun f _ => ?_` and prove the remaining obligations. Rewrite using `[hψ, LinearEquiv.symm_apply_apply]`.

Conclude with `⟨C, hbc, hbij, hH, hact', hnab', hcoord⟩`.
-/
theorem forms_of_semilinear_at (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', (∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f) ∧ Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  let v : Fin B.S.dim → B'.S.Forms := fun k => L (B.S.basis k)
  let bv : Basis (Fin B.S.dim) K' B'.S.Forms := Basis.mk hli hsp
  have hbv : ∀ k, bv k = L (B.S.basis k) := fun k => Basis.mk_apply hli hsp k
  let C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := B'.S.basis.toMatrix v
  have hCe : ∀ a i, C a i = B'.S.basis.equivFun (L (B.S.basis i)) a := by
    intro a i
    simp [C, v, Basis.toMatrix_apply]
  have hC : ∀ x, C *ᵥ x = B'.S.basis.equivFun (bv.equivFun.symm x) := by
    intro x
    ext i
    simp only [Matrix.mulVec, dotProduct, hCe, Basis.equivFun_symm_apply, hbv, map_sum, map_smul,
      Basis.equivFun_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hL : ∀ f, L f = bv.equivFun.symm (fun k => φ (B.S.basis.equivFun f k)) := by
    intro f
    conv_lhs => rw [← B.S.basis.sum_equivFun f]
    rw [map_sum, Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsm, hbv]
  have hψ : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) =
      B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    simp only [hL, LinearEquiv.apply_symm_apply, hC]
  have hbc : ∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f := by
    intro f
    simp only [GlobalTheory.Mem.R3.LiftLatBC.bcF]
    rw [hC, LinearEquiv.symm_apply_apply, hL]
  have hbij : Function.Bijective C.mulVec := by
    have he : C.mulVec = ⇑(bv.equivFun.symm.trans B'.S.basis.equivFun) := funext fun x => by
      rw [hC]
      rfl
    rw [he]
    exact LinearEquiv.bijective _
  have hH : Cᴴ * B'.S.H * C = B.S.H.map φ := by
    ext i j
    have h1 := csum_coords B'.S (B'.S.basis.equivFun (L (B.S.basis i)))
      (B'.S.basis.equivFun (L (B.S.basis j)))
    simp only [LinearEquiv.symm_apply_apply, hcs] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.L2.DIV.CSD.H,
      Matrix.of_apply, hCe]
    rw [h1]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hrep : ∀ (T : Module.End K B.S.Forms) (f : B.S.Forms),
      LinearMap.toMatrix B.S.basis B.S.basis T *ᵥ B.S.basis.equivFun f = B.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hrep' : ∀ (T : Module.End K' B'.S.Forms) (f : B'.S.Forms),
      LinearMap.toMatrix B'.S.basis B'.S.basis T *ᵥ B'.S.basis.equivFun f = B'.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hact' : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro k
    have hs : (Pi.single k 1 : Fin B.S.dim → K') = fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j) := by
      funext j
      by_cases h : j = k <;> simp [Pi.single_apply, h]
    have hk : (Pi.single k 1 : Fin B.S.dim → K) = B.S.basis.equivFun (B.S.basis k) := by
      funext j
      rw [Basis.equivFun_self, Pi.single_apply]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs]
    have hm : (B.S.actMat B.r g).map φ *ᵥ (fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j)) =
        fun i => φ (((B.S.actMat B.r g) *ᵥ Pi.single k 1) i) := by
      funext i
      exact (RingHom.map_mulVec φ _ _ i).symm
    rw [hm, hψ, hψ, hk]
    simp only [Formalism.L2.DIV.CSD.actMat, hrep, hrep', LinearEquiv.symm_apply_apply, hact]
  have hnab' : B'.S.nabLat = Submodule.span (𝓞 K')
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) := by
    have hset : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨B.S.basis.equivFun.symm x, (mem_nabLat_iff B.S x).mp hx, (hψ x).symm⟩
      · rintro ⟨f, hf, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff B.S _).mpr (by simpa using hf), ?_⟩
        simp only [hψ, LinearEquiv.symm_apply_apply]
    rw [hset]
    ext y
    rw [mem_nabLat_iff, hnab (B'.S.basis.equivFun.symm y)]
    let E := B'.S.basis.equivFun.restrictScalars (𝓞 K')
    have hE : (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} =
        (E : B'.S.Forms →ₗ[𝓞 K'] (Fin B'.S.dim → K')) '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      rw [Set.image_image]
      rfl
    rw [hE, ← Submodule.map_span, Submodule.mem_map_equiv]
    exact Iff.rfl
  have hcoord : B'.coord Z' = Submodule.span K'
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
    rw [hZ]
    simp only [Formalism.L2.DIV.BlockDat.coord, Submodule.map_span, Submodule.map_coe, LinearEquiv.coe_coe]
    congr 1
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun f _ => ?_
    rw [hψ, LinearEquiv.symm_apply_apply]
  exact ⟨C, hbc, hbij, hH, hact', hnab', hcoord⟩

end GlobalTheory.Mem.R3.LiftLatBC

end
