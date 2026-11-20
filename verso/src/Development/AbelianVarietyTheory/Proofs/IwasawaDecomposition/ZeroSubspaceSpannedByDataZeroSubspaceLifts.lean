import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DivisionRationalLift

section Core

variable {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {M W : Type} [NormedAddCommGroup M]
  [InnerProductSpace ℂ M] [AddCommGroup W] [Module ℂ W]

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Take `⟨g, hg⟩` from `Θ.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΘ)`. Establish `hL : LinearMap.toMatrix' g * Θ = 1`. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis. Establish `hL' : (LinearMap.toMatrix' g).map σ * Θ.map σ = 1`.

Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Introduce `x y hxy`. Use `congrArg (fun v => (LinearMap.toMatrix' g).map σ *ᵥ v) hxy` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this`. Conclude with `this`.
-/
theorem mulVec_map_injective {a b : ℕ} (Θ : Matrix (Fin a) (Fin b) K) (hΘ : Function.Injective Θ.mulVec) :
    Function.Injective (Θ.map σ).mulVec := by
  obtain ⟨g, hg⟩ := Θ.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΘ)
  have hL : LinearMap.toMatrix' g * Θ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hL' : (LinearMap.toMatrix' g).map σ * Θ.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have := congrArg (fun v => (LinearMap.toMatrix' g).map σ *ᵥ v) hxy
  simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
  exact this

/- English proof (translation)
Use `set S := Submodule.span ℂ (J '' Set.range fun z => Zm *ᵥ z) with hS`. Use `set N := Submodule.span ℂ (J '' {y | Pr *ᵥ y = 0}) with hN`. Establish `hSN : ∀ a ∈ S, ∀ b ∈ N, inner ℂ a b = 0`. Establish `hle : N ≤ Sᗮ`. Rewrite using `[hN, Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal]`. Introduce `u hu`. Establish `hle2 : S ≤ (Submodule.span ℂ {J y})ᗮ`. Rewrite using `[hS, Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨z, rfl⟩, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hin]`. Establish `h0` using `GlobalTheory.Mem.LiftForms.hform_orth hP z y`. Rewrite `h0` using `[show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]`. Rewrite using `[← h0, map_zero]`.

Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle2 hu)`. Introduce `a ha b hb`. Conclude with `(Submodule.mem_orthogonal _ _).1 (hle hb) a ha`. Establish `hker : ∀ x, Pr *ᵥ (x - Zm *ᵥ (Pr *ᵥ x)) = 0`. Introduce `x`.

Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec, sub_self]`. Establish `htop : ∀ v : M, ∃ a ∈ S, ∃ b ∈ N, a + b = v`. Introduce `v`. Establish `hv : v ∈ S ⊔ N`. Establish `: (⊤ : Submodule ℂ M) ≤ S ⊔ N`.

Rewrite using `[← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hd : J (Pi.single k 1) = J (Zm *ᵥ (Pr *ᵥ Pi.single k 1)) + J (Pi.single k 1 - Zm *ᵥ (Pr *ᵥ Pi.single k 1))`. Rewrite using `[← map_add, add_sub_cancel]`. Use `show J (Pi.single k 1) ∈ S ⊔ N`.

Rewrite using `[hd]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩) (Submodule.subset_span ⟨_, hker _, rfl⟩)`. Conclude with `this Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 hv`. Conclude with `⟨a, ha, b, hb, hab⟩`.

Establish `hNk : N ≤ LinearMap.ker θ'`. Rewrite using `[hN, Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, hθ, show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]`. Establish `hexp : ∀ y : Fin e → K, jW y = ∑ l, σ (y l) • jW (Pi.single l 1)`.

Introduce `y`. Establish `hz : y = ∑ l, y l • (Pi.single l 1 : Fin e → K)`. Use extensionality with `i`. Simplify using `[Pi.single_apply]`. Use `conv_lhs => rw [hz]`.

Simplify using `only [map_sum, map_smulₛₗ]`. Establish `hSk : ∀ a ∈ S, θ' a = 0 → a = 0`. Introduce `a ha h0`. Rewrite `ha` using `[hS, GlobalTheory.Mem.LiftForms.span_range_mulVec, ← Fintype.range_linearCombination]`. Take `⟨c, rfl⟩` from `ha`.

Establish `hcomp : θ' (Fintype.linearCombination ℂ (fun k => J (Zm *ᵥ Pi.single k 1)) c) = ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1)`. Simplify using `only [Fintype.linearCombination_apply, map_sum, map_smul, hθ, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec]`. Simplify using `only [hexp (Θ *ᵥ _), Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`. Rewrite `h0` using `[hcomp]`. Establish `hc0 : (Θ.map σ) *ᵥ c = 0` using `funext fun l => Fintype.linearIndependent_iff.1 hW _ h0 l`.

Establish `hc : c = 0` using `mulVec_map_injective Θ hΘ (hc0.trans (Matrix.mulVec_zero _).symm)`. Rewrite using `[hc, map_zero]`. Establish `hSZ : S ≤ LinearMap.range eM`. Rewrite using `[hS, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨z, rfl⟩, rfl⟩`.

Conclude with `⟨J (Zm *ᵥ z), by rw [hop, hEZ]⟩`. Establish `hmain : (LinearMap.ker θ')ᗮ = S`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `htop v`.

Establish `h1 : inner ℂ b (a + b) = 0` using `(Submodule.mem_orthogonal _ _).1 hv b (hNk hb)`. Establish `h2 : inner ℂ b a = 0` using `by rw [← inner_conj_symm, hSN a ha b hb, map_zero]`. Rewrite `h1` using `[inner_add_right, h2, zero_add, inner_self_eq_zero]`. Rewrite using `[h1, add_zero]`. Conclude with `ha`.

Introduce `s hs`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `w hw`. Take `⟨a, ha, b, hb, rfl⟩` from `htop w`. Establish `hθa : θ' a = 0`.

Establish `h3` using `LinearMap.mem_ker.1 hw`. Rewrite `h3` using `[map_add, LinearMap.mem_ker.1 (hNk hb), add_zero]`. Then use the resulting hypothesis. Rewrite using `[hSk a ha hθa, zero_add, ← inner_conj_symm, hSN s hs b hb, map_zero]`. Rewrite using `[hmain, inf_eq_left.2 hSZ, hS, GlobalTheory.Mem.LiftForms.span_range_mulVec]`.
-/
theorem orth_ker_inf_range {n d e : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (hsp : Submodule.span ℂ (Set.range fun k => J (Pi.single k 1)) = ⊤)
    (H : Matrix (Fin n) (Fin n) K) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (Formalism.DivisionValues.hform H x y))
    (eM : M →ₗ[ℂ] M) (E : Matrix (Fin n) (Fin n) K) (hop : ∀ x, eM (J x) = J (E *ᵥ x))
    (Zm : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : Formalism.DivisionValues.IsOrthProj H Zm Pr)
    (hEZ : ∀ z, E *ᵥ (Zm *ᵥ z) = Zm *ᵥ z)
    (jW : (Fin e → K) →ₛₗ[σ] W) (hW : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin e) (Fin d) K) (hΘ : Function.Injective Θ.mulVec)
    (θ' : M →ₗ[ℂ] W) (hθ : ∀ x, θ' (J x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ')ᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (Set.range fun k => J (Zm *ᵥ Pi.single k 1)) := by

  classical
  set S := Submodule.span ℂ (J '' Set.range fun z => Zm *ᵥ z) with hS
  set N := Submodule.span ℂ (J '' {y | Pr *ᵥ y = 0}) with hN
  have hSN : ∀ a ∈ S, ∀ b ∈ N, inner ℂ a b = 0 := by
    have hle : N ≤ Sᗮ := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      have hle2 : S ≤ (Submodule.span ℂ {J y})ᗮ := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
        have h0 := GlobalTheory.Mem.LiftForms.hform_orth hP z y
        rw [show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero] at h0
        rw [← h0, map_zero]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle2 hu)
    intro a ha b hb
    exact (Submodule.mem_orthogonal _ _).1 (hle hb) a ha
  have hker : ∀ x, Pr *ᵥ (x - Zm *ᵥ (Pr *ᵥ x)) = 0 := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec, sub_self]
  have htop : ∀ v : M, ∃ a ∈ S, ∃ b ∈ N, a + b = v := by
    intro v
    have hv : v ∈ S ⊔ N := by
      have : (⊤ : Submodule ℂ M) ≤ S ⊔ N := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have hd : J (Pi.single k 1) = J (Zm *ᵥ (Pr *ᵥ Pi.single k 1)) + J (Pi.single k 1 - Zm *ᵥ (Pr *ᵥ Pi.single k 1)) := by
          rw [← map_add, add_sub_cancel]
        show J (Pi.single k 1) ∈ S ⊔ N
        rw [hd]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩) (Submodule.subset_span ⟨_, hker _, rfl⟩)
      exact this Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    exact ⟨a, ha, b, hb, hab⟩
  have hNk : N ≤ LinearMap.ker θ' := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hθ, show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]
  have hexp : ∀ y : Fin e → K, jW y = ∑ l, σ (y l) • jW (Pi.single l 1) := by
    intro y
    have hz : y = ∑ l, y l • (Pi.single l 1 : Fin e → K) := by
      ext i; simp [Pi.single_apply]
    conv_lhs => rw [hz]
    simp only [map_sum, map_smulₛₗ]
  have hSk : ∀ a ∈ S, θ' a = 0 → a = 0 := by
    intro a ha h0
    rw [hS, GlobalTheory.Mem.LiftForms.span_range_mulVec, ← Fintype.range_linearCombination] at ha
    obtain ⟨c, rfl⟩ := ha
    have hcomp : θ' (Fintype.linearCombination ℂ (fun k => J (Zm *ᵥ Pi.single k 1)) c) =
        ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, hθ, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec]
      simp only [hexp (Θ *ᵥ _), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [hcomp] at h0
    have hc0 : (Θ.map σ) *ᵥ c = 0 := funext fun l => Fintype.linearIndependent_iff.1 hW _ h0 l
    have hc : c = 0 := mulVec_map_injective Θ hΘ (hc0.trans (Matrix.mulVec_zero _).symm)
    rw [hc, map_zero]
  have hSZ : S ≤ LinearMap.range eM := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨J (Zm *ᵥ z), by rw [hop, hEZ]⟩
  have hmain : (LinearMap.ker θ')ᗮ = S := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := htop v
      have h1 : inner ℂ b (a + b) = 0 := (Submodule.mem_orthogonal _ _).1 hv b (hNk hb)
      have h2 : inner ℂ b a = 0 := by rw [← inner_conj_symm, hSN a ha b hb, map_zero]
      rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
      rw [h1, add_zero]
      exact ha
    · intro s hs
      rw [Submodule.mem_orthogonal]
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := htop w
      have hθa : θ' a = 0 := by
        have h3 := LinearMap.mem_ker.1 hw
        rwa [map_add, LinearMap.mem_ker.1 (hNk hb), add_zero] at h3
      rw [hSk a ha hθa, zero_add, ← inner_conj_symm, hSN s hs b hb, map_zero]
  rw [hmain, inf_eq_left.2 hSZ, hS, GlobalTheory.Mem.LiftForms.span_range_mulVec]

end Core

section Main

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t`. Establish `hR` using `complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim`. Establish `hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec` using `CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t`. Establish `hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1` using `⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩`. Establish `hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)` using `BlockDat.lf_l_proj hB`.

Establish `he : ∀ z, lE D A3.A F.P0 F.ψ0 i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z` using `fun z => GlobalTheory.Mem.LiftForms.lvlOp_lE hB z`. Take `⟨hTh, hθ⟩` from `GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH`. Establish `hf` using `Y.formsL i t`. Conclude with `orth_ker_inf_range ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap) hf.span (lH D A3.A F.P0 F.ψ0 i t) hf.inner (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (lE D A3.A F.P0 F.ψ0 i t) hf.op_eq _ _ hp he (Z.jW i) (hTh.li i) _ hb.1 (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) …`.
-/
theorem divisionRows_rationalLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  have he : ∀ z, lE D A3.A F.P0 F.ψ0 i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) =
      lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z := fun z => GlobalTheory.Mem.LiftForms.lvlOp_lE hB z
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hf := Y.formsL i t
  exact orth_ker_inf_range ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap) hf.span
    (lH D A3.A F.P0 F.ψ0 i t) hf.inner (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (lE D A3.A F.P0 F.ψ0 i t) hf.op_eq
    _ _ hp he (Z.jW i) (hTh.li i) _ hb.1 (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (hθ i t)

end Main

end GlobalTheory.Mem.R3.DivisionRationalLift

end
