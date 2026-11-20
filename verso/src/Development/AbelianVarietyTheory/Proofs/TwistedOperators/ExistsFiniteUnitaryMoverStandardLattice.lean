import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.MoverGlue

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def glue (σ : R →+* R) (ε : R) (P Q : Matrix n n R) : Matrix n n R :=
  ε • P + σ ε • (Q.map σ)ᵀ + (1 - ε - σ ε) • (1 : Matrix n n R)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [glue, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]`. Distinguish the cases in `h : i = j`. Apply the tactic sequence `subst h; simp <;> ring`. Apply the tactic sequence `simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)] <;> ring`.
-/
theorem glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (P Q : Matrix n n R) :
    ((glue σ ε P Q).map σ)ᵀ = σ ε • (P.map σ)ᵀ + ε • Q + (1 - ε - σ ε) • (1 : Matrix n n R) := by
  ext i j
  simp only [glue, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_sub, map_one, hσ]
  by_cases h : i = j
  · subst h; simp <;> ring
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)] <;> ring

/- English proof (translation)
Establish `hσσ : σ ε * σ ε = σ ε` using `by rw [← map_mul, hε]`. Establish `hσε : σ ε * ε = 0` using `by rw [mul_comm, hεσ]`. Establish `h1 : ε * (1 - ε - σ ε) = 0` using `by linear_combination (-1 : R) * hε - hεσ`. Establish `h2 : σ ε * (1 - ε - σ ε) = 0` using `by linear_combination (-1 : R) * hσσ - hσε`. Use `⟨hσσ, hσε, h1, h2, by rw [mul_comm, h1], by rw [mul_comm, h2], ?_⟩` and prove the remaining obligations.

Take the linear combination `(1 : R) * hε + hσσ + 2 * hεσ`.
-/
theorem scal_facts (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) :
    σ ε * σ ε = σ ε ∧ σ ε * ε = 0 ∧ ε * (1 - ε - σ ε) = 0 ∧ σ ε * (1 - ε - σ ε) = 0 ∧
      (1 - ε - σ ε) * ε = 0 ∧ (1 - ε - σ ε) * σ ε = 0 ∧ (1 - ε - σ ε) * (1 - ε - σ ε) = 1 - ε - σ ε := by
  have hσσ : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have hσε : σ ε * ε = 0 := by rw [mul_comm, hεσ]
  have h1 : ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hε - hεσ
  have h2 : σ ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hσσ - hσε
  refine ⟨hσσ, hσε, h1, h2, by rw [mul_comm, h1], by rw [mul_comm, h2], ?_⟩
  linear_combination (1 : R) * hε + hσσ + 2 * hεσ

/- English proof (translation)
Take `⟨-, -, h1, -⟩` from `scal_facts σ ε hε hεσ`. Simplify using `only [glue, smul_add, smul_smul, hε, hεσ, h1, zero_smul, add_zero]`.
-/
theorem smul_glue (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) (P Q : Matrix n n R) :
    ε • glue σ ε P Q = ε • P := by
  obtain ⟨-, -, h1, -⟩ := scal_facts σ ε hε hεσ
  simp only [glue, smul_add, smul_smul, hε, hεσ, h1, zero_smul, add_zero]

/- English proof (translation)
Take `⟨-, -, -, -, h3, h4, h5⟩` from `scal_facts σ ε hε hεσ`. Rewrite using `[glue_cT σ hσ]`. Simplify using `only [smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]`.
-/
theorem off_smul_glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) :
    (1 - ε - σ ε) • ((glue σ ε P Q).map σ)ᵀ = (1 - ε - σ ε) • (1 : Matrix n n R) := by
  obtain ⟨-, -, -, -, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  rw [glue_cT σ hσ]
  simp only [smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]

/- English proof (translation)
Take `⟨hσσ, hσε, h1, h2, h3, h4, h5⟩` from `scal_facts σ ε hε hεσ`. Establish `hsum : ε • (1 : Matrix n n R) + σ ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1`. Rewrite using `[← add_smul, ← add_smul]`. Simplify using the standard rewrite rules. Establish `hsum' : σ ε • (1 : Matrix n n R) + ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1`.

Rewrite using `[add_comm (σ ε • (1 : Matrix n n R))]`. Conclude with `hsum`. Establish `key : ∀ M N : Matrix n n R, ε • (M * N) = ε • (1 : Matrix n n R) → σ ε • ((N.map σ)ᵀ * (M.map σ)ᵀ) = σ ε • (1 : Matrix n n R)`. Introduce `M N hMN`. Use extensionality with `i j`.

Use `congrArg σ (congrFun (congrFun hMN j) i)` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul] at this`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply, this]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]`. Rewrite using `[glue_cT σ hσ]`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[hPQ, key P Q hPQ]`. Apply the tactic sequence `first | exact hsum | exact hsum'`. Simplify using `only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[hQP, key Q P hQP]`.

Apply the tactic sequence `first | exact hsum | exact hsum'`.
-/
theorem glue_unitary (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) (hPQ : ε • (P * Q) = ε • (1 : Matrix n n R)) (hQP : ε • (Q * P) = ε • (1 : Matrix n n R)) :
    glue σ ε P Q * ((glue σ ε P Q).map σ)ᵀ = 1 ∧ ((glue σ ε P Q).map σ)ᵀ * glue σ ε P Q = 1 := by
  obtain ⟨hσσ, hσε, h1, h2, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  have hsum : ε • (1 : Matrix n n R) + σ ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [← add_smul, ← add_smul]; simp
  have hsum' : σ ε • (1 : Matrix n n R) + ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [add_comm (σ ε • (1 : Matrix n n R))]; exact hsum
  have key : ∀ M N : Matrix n n R, ε • (M * N) = ε • (1 : Matrix n n R) →
      σ ε • ((N.map σ)ᵀ * (M.map σ)ᵀ) = σ ε • (1 : Matrix n n R) := by
    intro M N hMN
    ext i j
    have := congrArg σ (congrFun (congrFun hMN j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at this
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply, this]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [glue_cT σ hσ]
  constructor
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hPQ, key P Q hPQ]
    first | exact hsum | exact hsum'
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hQP, key Q P hQP]
    first | exact hsum | exact hsum'

end Alg

variable {D : D7}

/- English proof (translation)
Establish `hmul : ∀ g h : GA D S, fmtC S (g * h) = fmtC S g * fmtC S h`. Introduce `g h`. Simplify using `only [fmtC, cM, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]`. Establish `hone : fmtC S 1 = 1`. Simplify using `only [fmtC, cM, Formalism.L2.Theta.mt, map_one, Units.val_one]`.

Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`. Set `G : GL (Fin S.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)` to `⟨fmtC S k, fmtC S k⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩`. Establish `hfg : (stdL D.host.E S.rank).FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hsp : Submodule.span D.host.E ((stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))) = ⊤`. Rewrite using `[stdL, Submodule.span_span_of_tower]`.

Establish `: (Set.range fun a : Fin S.rank => (Pi.single a (1 : D.host.E) : Fin S.rank → D.host.E)) = Set.range (Pi.basisFun D.host.E (Fin S.rank))`. Use extensionality with `v`. Simplify using `[Pi.basisFun_apply]`. Rewrite using `[this, (Pi.basisFun D.host.E (Fin S.rank)).span_eq]`. Take `⟨Λ, -, -, -, hΛ⟩` from `GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E S.rank _ G hfg hsp`.

Use `⟨Λ, fun u => ?_⟩` and prove the remaining obligations. Establish `hV : ∀ L : Lt D.host.E S.rank, ((hatV L : AddSubgroup _) : Set (Fin S.rank → AfE D)) = (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin S.rank → D.host.E)) : Set _)` using `fun L => rfl`. Establish `hGi : ∀ z, fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ z) = z`. Introduce `z`. Rewrite using `[Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec]`.

Prove the components needed by the constructor for the conclusion. Introduce `hu`. Use `⟨fmtC S k *ᵥ u, ?_, (hGi u).symm⟩` and prove the remaining obligations. Establish `: fmtC S k *ᵥ u ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D))`. Rewrite using `[hV, hΛ]`.

Conclude with `⟨u, hu, rfl⟩`. Conclude with `this`. Introduce and unpack `⟨u₀, hu₀, rfl⟩`. Establish `: u₀ ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D))` using `hu₀`. Rewrite `this` using `[hV, hΛ]`.

Take `⟨w, hw, rfl⟩` from `this`. Express the relevant statement in the definitionally equal form `fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ w) ∈ hatV (stdL D.host.E S.rank)`. Rewrite using `[hGi]`. Conclude with `hw`.
-/
theorem exists_mov (S : HSp D) (k : GA D S) :
    ∃ Λ' : Lt D.host.E S.rank, IsMov (fmtC S k⁻¹) Λ' (stdL D.host.E S.rank) := by
  have hmul : ∀ g h : GA D S, fmtC S (g * h) = fmtC S g * fmtC S h := by
    intro g h
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]
  have hone : fmtC S 1 = 1 := by
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_one, Units.val_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  let G : GL (Fin S.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    ⟨fmtC S k, fmtC S k⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩
  have hfg : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span D.host.E ((stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower]
    have : (Set.range fun a : Fin S.rank => (Pi.single a (1 : D.host.E) : Fin S.rank → D.host.E)) =
        Set.range (Pi.basisFun D.host.E (Fin S.rank)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
  obtain ⟨Λ, -, -, -, hΛ⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E S.rank _ G hfg hsp
  refine ⟨Λ, fun u => ?_⟩
  have hV : ∀ L : Lt D.host.E S.rank, ((hatV L : AddSubgroup _) : Set (Fin S.rank → AfE D)) =
      (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin S.rank → D.host.E)) : Set _) := fun L => rfl
  have hGi : ∀ z, fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec]
  constructor
  · intro hu
    refine ⟨fmtC S k *ᵥ u, ?_, (hGi u).symm⟩
    have : fmtC S k *ᵥ u ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := by
      rw [hV, hΛ]; exact ⟨u, hu, rfl⟩
    exact this
  · rintro ⟨u₀, hu₀, rfl⟩
    have : u₀ ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := hu₀
    rw [hV, hΛ] at this
    obtain ⟨w, hw, rfl⟩ := this
    change fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ w) ∈ hatV (stdL D.host.E S.rank)
    rw [hGi]; exact hw

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[map_mul]`.
-/
theorem map_smul_ringHom {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {m p : Type} (c : R) (M : Matrix m p R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp [map_mul]

end GlobalTheory.MoverGlue

open GlobalTheory.MoverGlue in

/- English proof (translation)
Introduce `D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a hab`. Take `⟨b, hab⟩` from `hab`. Establish `he2 : e * e = e` using `GlobalTheory.PlaceVec.idemSum_mul_self he`. Establish `hec : e * cA D e = 0` using `he.2`. Set `φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D` to `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom`.

Set `ψ : EAf D →+* (Af D.host.F ⊗[D.host.F] D.host.E)` to `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm.toAlgHom.toRingHom`. Establish `hφψ : ∀ z, φ (ψ z) = z` using `fun z => AlgEquiv.apply_symm_apply _ z`. Establish `htoE : ∀ z : AE D, toEAf D z = φ (finPart D z)` using `fun z => rfl`. Set `σ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* (Af D.host.F ⊗[D.host.F] D.host.E)` to `sigR (Af D.host.F) D.sp.cm.sig`. Establish `hσ : ∀ z, σ (σ z) = z`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) ((Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (x ⊗ₜ y)) = x ⊗ₜ y`. Simplify using `only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`.

Use `congr 1`. Conclude with `star_star y`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hfc : ∀ z : AE D, finPart D (cA D z) = σ (finPart D z)` using `fun z => GlobalTheory.UnitaryGlue.map_sigR (sndA D.host.F) D.sp.cm.sig z`. Use `set ε := finPart D e with hεdef`.

Establish `hεε : ε * ε = ε` using `by rw [← map_mul, he2]`. Establish `hεσ : ε * σ ε = 0` using `by rw [← hfc, ← map_mul, hec, map_zero]`. Set `Bs : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)` to `βS.val.map ψ`. Set `Bi : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)` to `(βS⁻¹).val.map ψ`. Establish `hBB : Bs * Bi = 1`.

Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hBB' : Bi * Bs = 1`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `P` to `finPart D a • Bs`. Set `Qm` to `finPart D b • Bi`.

Establish `hPQ : ε • (P * Qm) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _)`. Rewrite using `[smul_mul_smul_comm, hBB, smul_smul, ← map_mul, ← map_mul, hab, he2]`. Establish `hQP : ε • (Qm * P) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _)`. Rewrite using `[smul_mul_smul_comm, hBB', smul_smul, ← map_mul, ← map_mul, mul_comm b a, hab, he2]`. Take `⟨hu1, hu2⟩` from `glue_unitary σ hσ ε hεε hεσ P Qm hPQ hQP`.

Use `set hf := glue σ ε P Qm with hhf`. Set `gfGL : GL (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)` to `⟨hf, (hf.map σ)ᵀ, hu1, hu2⟩`. Establish `hJ : JR (F` using `D.host.F) (Af D.host.F) (HSpace.gram S) = 1 := by`. Rewrite using `[C.m.gS]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `hmem : gfGL ∈ HR (Af D.host.F) D.sp.cm.sig (HSpace.gram S)` using `by show Formalism.UG.cT σ hf * JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) * hf = JR (F := D.host.F) (Af D.host.F) (HSpace.gram S)`. Rewrite using `[hJ, Matrix.mul_one]`. Conclude with `hu2`. Take `⟨g, hgC, hgf⟩` from `(GlobalTheory.UnitaryGlue.adelic_glue D S).1 gfGL hmem`. Take `⟨Λ', hΛ'⟩` from `exists_mov S g`.

Establish `hmt1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1`. Simplify using `only [Formalism.L2.Theta.mt, map_one, Units.val_one]`. Establish `hact : ∀ x : WO S T, actO S T g 1 x = HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)`. Introduce `x`. Use `show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T 1) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (Formalism.L2.Theta.mt S g⁻¹) = _`.

Rewrite using `[hmt1, Matrix.one_mul]`. Establish `hKf : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = (hf.map σ)ᵀ`. Establish `h1 : ((finHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (finPart D)` using `rfl`. Rewrite using `[← h1, map_inv, hgf]`. Both sides reduce to the same expression.

Establish `hKi : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1`. Establish `h1 : ((infHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (infPart D)` using `rfl`. Establish `hg1 : infHom S g = 1` using `hgC`. Rewrite using `[← h1, map_inv, hg1, inv_one, Units.val_one]`. Use `⟨g, Λ', ⟨hgC, ?_, ?_⟩, hΛ'⟩` and prove the remaining obligations.

Introduce `x hx`. Rewrite using `[hact]`. Establish `hX : (1 - ε - σ ε) • x.map (finPart D) = x.map (finPart D)`. Use extensionality with `i j`. Use `congrArg (finPart D) (hx i j)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_sub, map_sub, map_one, hfc]`. Simplify `this` using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Use extensionality with `i j`. Use `GlobalTheory.SplitScalar.adele_ext ?_ ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (infPart D) = x.map (infPart D) by`.

Rewrite using `[Matrix.map_mul, hKi, Matrix.mul_one]) i) j`. Simplify `h` using `only [Matrix.map_apply]`. Establish `h` using `congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (finPart D) = x.map (finPart D) by`. Rewrite using `[Matrix.map_mul, hKf]`. Use `conv_lhs => rw [← hX]`.

Rewrite using `[Matrix.smul_mul, ← Matrix.mul_smul, off_smul_glue_cT σ hσ ε hεε hεσ, Matrix.mul_smul, Matrix.mul_one, hX]) i) j`. Simplify `h` using `only [Matrix.map_apply]`. Introduce `x hx`. Rewrite using `[hact]`. Establish `hcK : ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ.map (toEAf D) = hf.map φ`.

Use extensionality with `i j`. Establish `hk` using `congrFun (congrFun hKf j) i`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply] at hk ⊢`. Rewrite using `[htoE, hfc, hk, hσ]`. Establish `hεhf : (toEAf D e) • hf.map φ = (toEAf D e * toEAf D a) • βS.val`.

Establish `h1 : ε • hf = ε • P` using `smul_glue σ ε hεε hεσ P Qm`. Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun h1 i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h2 ⊢`. Rewrite using `[htoE, htoE, ← map_mul, h2]`.

Simplify using `only [P, Bs, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hφψ, hεdef, mul_assoc]`. Use `set Z := (HMul.hMul ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) with hZdef`. Establish `hxc : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ`. Use extensionality with `i j`. Use `congrArg (cA D) (hx j i)` as an intermediate fact.

Rewrite `this` using `[map_mul, GlobalTheory.DualPairCheck.cA_cA]`. Simplify `this` using `only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]`. Establish `hZ : toEAf D e • Z = Z`. Rewrite using `[hZdef]`. Use `conv_rhs => rw [← hxc]`.

Rewrite using `[Matrix.smul_mul, GlobalTheory.MoverGlue.map_smul_ringHom]`. Establish `hL2 : (HMul.hMul (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) = HMul.hMul (hf.map φ) Z`. Establish `h3 : (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) = HMul.hMul ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D))`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Rewrite using `[h3, Matrix.mul_assoc, Matrix.map_mul, hcK]`.

Establish `hLHS : HMul.hMul (HMul.hMul (βS⁻¹).val (HMul.hMul (hf.map φ) Z)) βT.val = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val` using `by conv_lhs => rw [← hZ]`. Rewrite using `[Matrix.mul_smul, ← Matrix.smul_mul, hεhf, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `hRHS : toEAf D a • HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val Z) βT.val) = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Use `conv_lhs => rw [← hZ]`.

Rewrite using `[Matrix.smul_mul, smul_smul, mul_comm (toEAf D a)]`. Unfold `GlobalTheory.LiftLevel.adjA frMapAdj`. Establish `hGS : (HSpace.gram S)⁻¹.map (incA D) = 1`. Rewrite using `[C.m.gS]`. Simplify using the standard rewrite rules.

Rewrite using `[hGS]`. Simplify using `only [Matrix.one_mul]`. Rewrite using `[hL2, hLHS, ← hRHS]`.
-/
theorem GlobalTheory.LiftLevel.exists_mover : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a hab
  obtain ⟨b, hab⟩ := hab
  have he2 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
  let ψ : EAf D →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm.toAlgHom.toRingHom
  have hφψ : ∀ z, φ (ψ z) = z := fun z => AlgEquiv.apply_symm_apply _ z
  have htoE : ∀ z : AE D, toEAf D z = φ (finPart D z) := fun z => rfl
  let σ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    sigR (Af D.host.F) D.sp.cm.sig
  have hσ : ∀ z, σ (σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) ((Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (x ⊗ₜ y)) = x ⊗ₜ y
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfc : ∀ z : AE D, finPart D (cA D z) = σ (finPart D z) := fun z =>
    GlobalTheory.UnitaryGlue.map_sigR (sndA D.host.F) D.sp.cm.sig z
  set ε := finPart D e with hεdef
  have hεε : ε * ε = ε := by rw [← map_mul, he2]
  have hεσ : ε * σ ε = 0 := by rw [← hfc, ← map_mul, hec, map_zero]
  let Bs : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := βS.val.map ψ
  let Bi : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (βS⁻¹).val.map ψ
  have hBB : Bs * Bi = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : Bi * Bs = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  let P := finPart D a • Bs
  let Qm := finPart D b • Bi
  have hPQ : ε • (P * Qm) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB, smul_smul, ← map_mul, ← map_mul, hab, he2]
  have hQP : ε • (Qm * P) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB', smul_smul, ← map_mul, ← map_mul, mul_comm b a, hab, he2]
  obtain ⟨hu1, hu2⟩ := glue_unitary σ hσ ε hεε hεσ P Qm hPQ hQP
  set hf := glue σ ε P Qm with hhf
  let gfGL : GL (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨hf, (hf.map σ)ᵀ, hu1, hu2⟩
  have hJ : JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) = 1 := by
    rw [C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmem : gfGL ∈ HR (Af D.host.F) D.sp.cm.sig (HSpace.gram S) := by
    show Formalism.UG.cT σ hf * JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) * hf = JR (F := D.host.F) (Af D.host.F) (HSpace.gram S)
    rw [hJ, Matrix.mul_one]; exact hu2
  obtain ⟨g, hgC, hgf⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D S).1 gfGL hmem
  obtain ⟨Λ', hΛ'⟩ := exists_mov S g

  have hmt1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
  have hact : ∀ x : WO S T, actO S T g 1 x = HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹) := by
    intro x; show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T 1) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (Formalism.L2.Theta.mt S g⁻¹) = _; rw [hmt1, Matrix.one_mul]
  have hKf : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = (hf.map σ)ᵀ := by
    have h1 : ((finHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) := rfl
    rw [← h1, map_inv, hgf]; rfl
  have hKi : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := by
    have h1 : ((infHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) := rfl
    have hg1 : infHom S g = 1 := hgC
    rw [← h1, map_inv, hg1, inv_one, Units.val_one]
  refine ⟨g, Λ', ⟨hgC, ?_, ?_⟩, hΛ'⟩
  · intro x hx
    rw [hact]
    have hX : (1 - ε - σ ε) • x.map (finPart D) = x.map (finPart D) := by
      ext i j
      have := congrArg (finPart D) (hx i j)
      rw [map_mul, map_sub, map_sub, map_one, hfc] at this
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using this
    ext i j
    refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (infPart D) = x.map (infPart D) by
        rw [Matrix.map_mul, hKi, Matrix.mul_one]) i) j
      simpa only [Matrix.map_apply] using h
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (finPart D) = x.map (finPart D) by
        rw [Matrix.map_mul, hKf]
        conv_lhs => rw [← hX]
        rw [Matrix.smul_mul, ← Matrix.mul_smul, off_smul_glue_cT σ hσ ε hεε hεσ, Matrix.mul_smul, Matrix.mul_one, hX]) i) j
      simpa only [Matrix.map_apply] using h
  · intro x hx
    rw [hact]
    have hcK : ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ.map (toEAf D) = hf.map φ := by
      ext i j
      have hk := congrFun (congrFun hKf j) i
      simp only [Matrix.map_apply, Matrix.transpose_apply] at hk ⊢
      rw [htoE, hfc, hk, hσ]
    have hεhf : (toEAf D e) • hf.map φ = (toEAf D e * toEAf D a) • βS.val := by
      have h1 : ε • hf = ε • P := smul_glue σ ε hεε hεσ P Qm
      ext i j
      have h2 := congrFun (congrFun h1 i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h2 ⊢
      rw [htoE, htoE, ← map_mul, h2]
      simp only [P, Bs, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hφψ, hεdef, mul_assoc]
    set Z := (HMul.hMul ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) with hZdef
    have hxc : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
      ext i j
      have := congrArg (cA D) (hx j i)
      rw [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
      simpa only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul] using this
    have hZ : toEAf D e • Z = Z := by
      rw [hZdef]
      conv_rhs => rw [← hxc]
      rw [Matrix.smul_mul, GlobalTheory.MoverGlue.map_smul_ringHom]
    have hL2 : (HMul.hMul (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) =
        HMul.hMul (hf.map φ) Z := by
      have h3 : (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ :
          Matrix (Fin S.rank) (Fin T.rank) (AE D)) = HMul.hMul ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ
          ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) := by
        rw [Matrix.map_mul, Matrix.transpose_mul]
      rw [h3, Matrix.mul_assoc, Matrix.map_mul, hcK]
    have hLHS : HMul.hMul (HMul.hMul (βS⁻¹).val (HMul.hMul (hf.map φ) Z)) βT.val = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      conv_lhs => rw [← hZ]
      rw [Matrix.mul_smul, ← Matrix.smul_mul, hεhf, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hRHS : toEAf D a • HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val Z) βT.val) = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      conv_lhs => rw [← hZ]
      rw [Matrix.smul_mul, smul_smul, mul_comm (toEAf D a)]
    unfold GlobalTheory.LiftLevel.adjA frMapAdj
    have hGS : (HSpace.gram S)⁻¹.map (incA D) = 1 := by
      rw [C.m.gS]; simp
    rw [hGS]
    simp only [Matrix.one_mul]
    rw [hL2, hLHS, ← hRHS]
