import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

section Csd

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

/- English proof (translation)
Simplify using `only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, CSD.csum, CSD.H, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `arg 2`. Use extensionality with `j`. Rewrite using `[Finset.sum_comm]`.

Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem csum_coords (u v : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm u : S.Cl → S.V) (S.basis.equivFun.symm v : S.Cl → S.V) =
      ∑ i, ∑ j, star (u i) * S.H i j * v j := by
  simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, CSD.csum, CSD.H,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [starRingEnd_apply]
  ring

/- English proof (translation)
Simplify using `[CSD.nabLat, valLatF, Submodule.mem_pi, CSD.I]`.
-/
theorem mem_nabLat_iff (x : Fin S.dim → K) :
    x ∈ S.nabLat ↔ ∀ c, (S.basis.equivFun.symm x : S.Cl → S.V) c ∈ S.Nab c := by
  simp [CSD.nabLat, valLatF, Submodule.mem_pi, CSD.I]

end Csd

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

/- English proof (translation)
Use `set C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := Matrix.of fun i k => B'.S.basis.repr (L (B.S.basis k)) i with hCdef`. Establish `hcol : ∀ k, B'.S.basis.equivFun.symm (fun i => C i k) = L (B.S.basis k)`. Introduce `k`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use extensionality with `i`.

Simplify using `[hCdef]`. Establish `hC : ∀ y, C *ᵥ y = B'.S.basis.equivFun (∑ k, y k • L (B.S.basis k))`. Introduce `y`. Use extensionality with `i`. Simplify using `[hCdef, Matrix.mulVec, dotProduct, mul_comm]`.

Establish `hLsum : ∀ x : Fin B.S.dim → K, L (B.S.basis.equivFun.symm x) = ∑ k, φ (x k) • L (B.S.basis k)`. Introduce `x`. Rewrite using `[Basis.equivFun_symm_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => hsm _ _`. Establish `hT : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x))`.

Introduce `x`. Rewrite using `[hC, hLsum]`. Establish `hTf : ∀ f : B.S.Forms, C *ᵥ (fun k => φ (B.S.basis.repr f k)) = ⇑(B'.S.basis.repr (L f))`. Introduce `f`. Use `hT (B.S.basis.equivFun f)` as an intermediate fact.

Simplify using `using this`. Use `⟨C, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y₁ y₂ h`. Establish `h0 : ∑ k, (y₁ - y₂) k • L (B.S.basis k) = 0`. Establish `: C *ᵥ (y₁ - y₂) = 0` using `by rw [Matrix.mulVec_sub, h, sub_self]`.

Rewrite `this` using `[hC]`. Conclude with `(LinearEquiv.map_eq_zero_iff _).mp this`. Use `Fintype.linearIndependent_iff.mp hli _ h0` as an intermediate fact. Use function extensionality and compare the values at `k`. Conclude with `sub_eq_zero.mp (this k)`.

Introduce `y`. Establish `hmem : B'.S.basis.equivFun.symm y ∈ Submodule.span K' (Set.range fun k => L (B.S.basis k))` using `hsp trivial`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun K').mp hmem`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hC, hc, LinearEquiv.apply_symm_apply]`.

Use extensionality with `a b`. Establish `h1` using `hcs (B.S.basis a) (B.S.basis b)`. Rewrite `h1` using `[← hcol a, ← hcol b, csum_coords]`. Simplify using `only [Matrix.map_apply, CSD.H, Matrix.of_apply] at h1 ⊢`. Rewrite using `[← h1, Matrix.mul_apply]`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Matrix.of_apply]`. Introduce `g`. Establish `hv : ∀ f : B.S.Forms, (B'.S.actMat B'.r (e g) * C) *ᵥ (fun k => φ (B.S.basis.repr f k)) = (C * (B.S.actMat B.r g).map φ) *ᵥ (fun k => φ (B.S.basis.repr f k))`.

Introduce `f`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTf]`. Establish `h2 : (B.S.actMat B.r g).map φ *ᵥ (fun k => φ (B.S.basis.repr f k)) = fun k => φ (B.S.basis.repr (B.r g f) k)`. Use function extensionality and compare the values at `k`. Rewrite using `[show (fun k => φ (B.S.basis.repr f k)) = φ ∘ (B.S.basis.repr f) from rfl, ← RingHom.map_mulVec φ]`.

Simplify using `only [CSD.actMat, LinearMap.toMatrix_mulVec_repr]`. Rewrite using `[h2, hTf]`. Simplify using `only [CSD.actMat, LinearMap.toMatrix_mulVec_repr, hact]`. Use extensionality with `i k`. Establish `hs : (fun j => φ (B.S.basis.repr (B.S.basis k) j)) = Pi.single k 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]`.

Use `congrFun (hv (B.S.basis k)) i` as an intermediate fact. Rewrite `this` using `[hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one]`. Conclude with `this`. Set `eO` to `(B'.S.basis.equivFun).restrictScalars (𝓞 K')`. Establish `himg : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) = eO '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨L (B.S.basis.equivFun.symm x), ⟨_, (mem_nabLat_iff _ _).mp hx, rfl⟩, (hT x).symm⟩`. Introduce and unpack `⟨_, ⟨f, hf, rfl⟩, rfl⟩`.

Use `⟨B.S.basis.equivFun f, (mem_nabLat_iff _ _).mpr (by simpa using hf), ?_⟩` and prove the remaining obligations. Use `show C *ᵥ (fun k => φ (B.S.basis.equivFun f k)) = _`. Rewrite using `[hT, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Use extensionality with `y`.

Rewrite using `[himg, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv, ← hnab, mem_nabLat_iff]`. Both sides reduce to the same expression. Rewrite using `[hZ, BlockDat.coord, BlockDat.coord, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`. Use `Set.image_congr fun f _ => ?_` and prove the remaining obligations.

Rewrite using `[hT]`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.
-/
theorem forms_of_semilinear (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  set C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := Matrix.of fun i k => B'.S.basis.repr (L (B.S.basis k)) i with hCdef

  have hcol : ∀ k, B'.S.basis.equivFun.symm (fun i => C i k) = L (B.S.basis k) := by
    intro k
    rw [LinearEquiv.symm_apply_eq]
    ext i
    simp [hCdef]
  have hC : ∀ y, C *ᵥ y = B'.S.basis.equivFun (∑ k, y k • L (B.S.basis k)) := by
    intro y
    ext i
    simp [hCdef, Matrix.mulVec, dotProduct, mul_comm]
  have hLsum : ∀ x : Fin B.S.dim → K, L (B.S.basis.equivFun.symm x) = ∑ k, φ (x k) • L (B.S.basis k) := by
    intro x
    rw [Basis.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _
  have hT : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    rw [hC, hLsum]
  have hTf : ∀ f : B.S.Forms, C *ᵥ (fun k => φ (B.S.basis.repr f k)) = ⇑(B'.S.basis.repr (L f)) := by
    intro f
    have := hT (B.S.basis.equivFun f)
    simpa using this
  refine ⟨C, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    have h0 : ∑ k, (y₁ - y₂) k • L (B.S.basis k) = 0 := by
      have : C *ᵥ (y₁ - y₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
      rw [hC] at this
      exact (LinearEquiv.map_eq_zero_iff _).mp this
    have := Fintype.linearIndependent_iff.mp hli _ h0
    funext k
    exact sub_eq_zero.mp (this k)
  ·
    intro y
    have hmem : B'.S.basis.equivFun.symm y ∈ Submodule.span K' (Set.range fun k => L (B.S.basis k)) := hsp trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K').mp hmem
    refine ⟨c, ?_⟩
    rw [hC, hc, LinearEquiv.apply_symm_apply]
  ·
    ext a b
    have h1 := hcs (B.S.basis a) (B.S.basis b)
    rw [← hcol a, ← hcol b, csum_coords] at h1
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply] at h1 ⊢
    rw [← h1, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Matrix.of_apply]
  ·
    intro g
    have hv : ∀ f : B.S.Forms, (B'.S.actMat B'.r (e g) * C) *ᵥ (fun k => φ (B.S.basis.repr f k)) =
        (C * (B.S.actMat B.r g).map φ) *ᵥ (fun k => φ (B.S.basis.repr f k)) := by
      intro f
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTf]
      have h2 : (B.S.actMat B.r g).map φ *ᵥ (fun k => φ (B.S.basis.repr f k)) =
          fun k => φ (B.S.basis.repr (B.r g f) k) := by
        funext k
        rw [show (fun k => φ (B.S.basis.repr f k)) = φ ∘ (B.S.basis.repr f) from rfl, ← RingHom.map_mulVec φ]
        simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr]
      rw [h2, hTf]
      simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr, hact]
    ext i k
    have hs : (fun j => φ (B.S.basis.repr (B.S.basis k) j)) = Pi.single k 1 := by
      funext j
      by_cases h : j = k
      · subst h; simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    have := congrFun (hv (B.S.basis k)) i
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  ·
    let eO := (B'.S.basis.equivFun).restrictScalars (𝓞 K')
    have himg : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        eO '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨L (B.S.basis.equivFun.symm x), ⟨_, (mem_nabLat_iff _ _).mp hx, rfl⟩, (hT x).symm⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff _ _).mpr (by simpa using hf), ?_⟩
        show C *ᵥ (fun k => φ (B.S.basis.equivFun f k)) = _
        rw [hT, LinearEquiv.symm_apply_apply]
        rfl
    ext y
    rw [himg, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv, ← hnab, mem_nabLat_iff]
    rfl
  ·
    rw [hZ, BlockDat.coord, BlockDat.coord, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    refine Set.image_congr fun f _ => ?_
    rw [hT]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.DefLatBC
