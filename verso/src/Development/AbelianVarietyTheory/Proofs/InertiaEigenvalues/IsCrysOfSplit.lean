import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules

noncomputable section

namespace GlobalTheory.SplitCrys

open Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.BlockCrys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {n : ℕ}

/- English proof (translation)
Use `GlobalTheory.Survey.CrystallineCyclotomic.nontrivial_B PD` as an intermediate fact. Establish `hact : ∀ g (y : Fin n → B), coordAct PD A g (W.mulVec y) = W.mulVec fun i => PD.actB g (y i)`. Introduce `g y`. Establish `h1 : (fun i => PD.actB g (W.mulVec y i)) = (W.map (PD.actB g)).mulVec fun i => PD.actB g (y i)`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Express the relevant statement in the definitionally equal form `((A g).map (algebraMap Qp B)).mulVec _ = _`. Rewrite using `[h1, Matrix.mulVec_mulVec, hW]`. Establish `hinj : Function.Injective W.mulVec` using `Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det W).2 hu)`. Set `f : (Fin n → K₀) →ₗ[K₀] (Fin n → B)` to `(W.mulVecLin.restrictScalars K₀).comp ((Algebra.linearMap K₀ B).compLeft (Fin n))`.

Establish `hf : ∀ c, f c = W.mulVec fun i => algebraMap K₀ B (c i)` using `fun c => rfl`. Establish `hfi : Function.Injective f`. Introduce `c d h`. Rewrite `h` using `[hf, hf]`. Use function extensionality and compare the values at `i`.

Conclude with `(algebraMap K₀ B).injective (congrFun (hinj h) i)`. Establish `hr : LinearMap.range f = coordInv PD A`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ g`.

Rewrite using `[hf, hact]`. Simplify using `only [AlgEquiv.commutes]`. Introduce `hx`. Establish `hxy : W.mulVec (W⁻¹.mulVec x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`.

Establish `hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = W⁻¹.mulVec x i` using `fun i => PD.invB _ fun g => by`. Establish `h2` using `hact g (W⁻¹.mulVec x)`. Rewrite `h2` using `[hxy, hx g]`. Conclude with `congrFun (hinj (h2.symm.trans hxy.symm)) i`. Use `choose c hc using hc`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, funext hc, hxy]`. Rewrite using `[← hr, LinearMap.finrank_range_of_inj hfi, Module.finrank_fin_fun]`.
-/
theorem finrank_coordInv_of_split (A : G → Matrix (Fin n) (Fin n) Qp) (W : Matrix (Fin n) (Fin n) B)
    (hu : IsUnit W.det) (hW : ∀ g, (A g).map (algebraMap Qp B) * W.map (PD.actB g) = W) :
    finrank K₀ (coordInv PD A) = n := by
  have := GlobalTheory.Survey.CrystallineCyclotomic.nontrivial_B PD
  have hact : ∀ g (y : Fin n → B),
      coordAct PD A g (W.mulVec y) = W.mulVec fun i => PD.actB g (y i) := by
    intro g y
    have h1 : (fun i => PD.actB g (W.mulVec y i)) =
        (W.map (PD.actB g)).mulVec fun i => PD.actB g (y i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum]
    change ((A g).map (algebraMap Qp B)).mulVec _ = _
    rw [h1, Matrix.mulVec_mulVec, hW]
  have hinj : Function.Injective W.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det W).2 hu)
  let f : (Fin n → K₀) →ₗ[K₀] (Fin n → B) :=
    (W.mulVecLin.restrictScalars K₀).comp ((Algebra.linearMap K₀ B).compLeft (Fin n))
  have hf : ∀ c, f c = W.mulVec fun i => algebraMap K₀ B (c i) := fun c => rfl
  have hfi : Function.Injective f := by
    intro c d h
    rw [hf, hf] at h
    funext i
    exact (algebraMap K₀ B).injective (congrFun (hinj h) i)
  have hr : LinearMap.range f = coordInv PD A := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩ g
      rw [hf, hact]
      simp only [AlgEquiv.commutes]
    · intro hx
      have hxy : W.mulVec (W⁻¹.mulVec x) = x := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = W⁻¹.mulVec x i := fun i =>
        PD.invB _ fun g => by
          have h2 := hact g (W⁻¹.mulVec x)
          rw [hxy, hx g] at h2
          exact congrFun (hinj (h2.symm.trans hxy.symm)) i
      choose c hc using hc
      refine ⟨c, ?_⟩
      rw [hf, funext hc, hxy]
  rw [← hr, LinearMap.finrank_range_of_inj hfi, Module.finrank_fin_fun]

/- English proof (translation)
Set `A : G → Matrix (Fin n) (Fin n) Qp` to `fun g => Matrix.of fun i j => e.repr (ρ g (e j)) i`. Establish `h1` using `finrank_coordInv PD ρ e A fun g i j => rfl`. Establish `h2` using `finrank_coordInv_of_split PD A W hu hW`. Establish `hL : 0 < finrank Qp LL` using `Module.finrank_pos`. Establish `hV : finrank Qp LL * finrank LL V = n`.

Rewrite using `[Module.finrank_mul_finrank Qp LL V, finrank_eq_card_basis e, Fintype.card_fin]`. Rewrite `h1` using `[h2, ← hV, mul_left_comm]`. Conclude with `Nat.eq_of_mul_eq_mul_left hL h1`.
-/
theorem isCrys_of_split {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
    [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B) (hu : IsUnit W.det)
    (hW : ∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) :
    IsCrys PD ρ := by
  let A : G → Matrix (Fin n) (Fin n) Qp := fun g => Matrix.of fun i j => e.repr (ρ g (e j)) i
  have h1 := finrank_coordInv PD ρ e A fun g i j => rfl
  have h2 := finrank_coordInv_of_split PD A W hu hW
  have hL : 0 < finrank Qp LL := Module.finrank_pos
  have hV : finrank Qp LL * finrank LL V = n := by
    rw [Module.finrank_mul_finrank Qp LL V, finrank_eq_card_basis e, Fintype.card_fin]
  rw [h2, ← hV, mul_left_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hL h1

end GlobalTheory.SplitCrys
