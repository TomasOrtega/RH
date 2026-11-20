import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOCStatement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter TensorProduct Matrix

namespace GlobalTheory.Cyc.GradedTorsion

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q`.
-/
theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

/- English proof (translation)
Rewrite using `[zC, algebraMap_eq, ha.1, AlgEquiv.commutes]`.
-/
theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (z : ℤ_[l]) : act g (zC z) = zC z := by
  rw [zC, algebraMap_eq, ha.1, AlgEquiv.commutes]

/- English proof (translation)
Establish `h : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])` using `(map_natCast _ _).symm`. Rewrite using `[h, algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Simplify using `[zC]`.
-/
theorem zC_add (x y : ℤ_[l]) : zC (x + y) = zC x + zC y := by simp [zC]

/- English proof (translation)
Simplify using `[zC]`.
-/
theorem zC_mul (x y : ℤ_[l]) : zC (x * y) = zC x * zC y := by simp [zC]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [zC]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zC_add, ih]`.
-/
theorem zC_sum {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) : zC (∑ j ∈ s, f j) = ∑ j ∈ s, zC (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zC_add, ih]

/- English proof (translation)
Simplify using `[zC]`.
-/
theorem zC_pow_l (k : ℕ) : zC ((l : ℤ_[l]) ^ k) = (l : PadicComplex l) ^ k := by simp [zC]

/- English proof (translation)
Introduce `a`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hA a b) (norm_nonneg _) (hy b)`.
-/
theorem mulVec_mem_ball {d : ℕ} {A : Matrix (Fin d) (Fin d) (PadicComplex l)}
    (hA : ∀ a b, ‖A a b‖ ≤ 1) {y : Fin d → PadicComplex l} (hy : y ∈ ball l d) :
    A *ᵥ y ∈ ball l d := by
  intro a
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA a b) (norm_nonneg _) (hy b)

/- English proof (translation)
Establish `: (fun a => act σ (((n : PadicComplex l) • y) a)) = (n : PadicComplex l) • fun a => act σ (y a)`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Simplify using `only [twAct]`. Rewrite using `[this, Matrix.mulVec_smul, smul_comm]`.
-/
theorem twAct_smul_nat (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (n : ℕ)
    (y : Fin d → PadicComplex l) :
    twAct act χ i U σ ((n : PadicComplex l) • y) = (n : PadicComplex l) • twAct act χ i U σ y := by
  have : (fun a => act σ (((n : PadicComplex l) • y) a)) =
      (n : PadicComplex l) • fun a => act σ (y a) := by
    funext a; simp
  simp only [twAct]
  rw [this, Matrix.mulVec_smul, smul_comm]

/- English proof (translation)
Establish `: (fun a => act σ ((D *ᵥ y) a)) = D.map (act σ) *ᵥ fun a => act σ (y a)`. Use function extensionality and compare the values at `a`. Simplify using `[Matrix.mulVec, dotProduct]`. Simplify using `only [twAct]`. Rewrite using `[this, Matrix.mulVec_mulVec, ← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec]`.
-/
theorem twAct_mulVec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (h : D * U σ = M σ * D.map (act σ))
    (y : Fin d → PadicComplex l) :
    twAct act χ i M σ (D *ᵥ y) = D *ᵥ twAct act χ i U σ y := by
  have : (fun a => act σ ((D *ᵥ y) a)) = D.map (act σ) *ᵥ fun a => act σ (y a) := by
    funext a; simp [Matrix.mulVec, dotProduct]
  simp only [twAct]
  rw [this, Matrix.mulVec_mulVec, ← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/- English proof (translation)
Take `⟨hdet, hint, hinv, -, hcomm⟩` from `hD`. Use `set E : Matrix (Fin d) (Fin d) (PadicComplex l) := (l : PadicComplex l) • D⁻¹ with hE`. Establish `hEint : ∀ a b, ‖E a b‖ ≤ 1` using `fun a b => by simpa [hE] using hinv a b`. Establish `hDE : ∀ y, D *ᵥ (E *ᵥ y) = (l : PadicComplex l) • y` using `fun y => by`. Rewrite using `[Matrix.mulVec_mulVec, hE, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Establish `hinj : Function.Injective D.mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det D).2 hdet)`. Establish `hEt : ∀ σ ∈ Gj K m, ∀ y, twAct act χ i U σ (E *ᵥ y) = E *ᵥ twAct act χ i M σ y`. Introduce `σ hσ y`. Apply `hinj` to reduce the goal to its premises. Use `show D *ᵥ _ = D *ᵥ _`.

Rewrite using `[← twAct_mulVec act χ i M U D σ (hcomm σ hσ), hDE, hDE, twAct_smul_nat]`. Take `⟨x, hx, hxe⟩` from `hU (fun σ => E *ᵥ c σ) k ⟨(continuous_const.matrix_mulVec continuous_id).comp_continuousOn hc.1, fun σ hσ => mulVec_mem_ball hEint (hc.2.1 σ hσ), fun σ hσ τ hτ => by`. Simplify using `only [hc.2.2 σ hσ τ hτ, Matrix.mulVec_add, hEt σ hσ]⟩`. Use the proof step `(by`. Take `⟨x, hx, hxe⟩` from `hk`.

Use `⟨E *ᵥ x, mulVec_mem_ball hEint hx, fun σ hσ => ?_⟩` and prove the remaining obligations. Use `hxe σ hσ` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[hEt σ hσ, ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul])`. Use `⟨D *ᵥ x, mulVec_mem_ball hint hx, fun σ hσ => ?_⟩` and prove the remaining obligations.

Use `hxe σ hσ` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[twAct_mulVec act χ i M U D σ (hcomm σ hσ), ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul, hDE, smul_smul, pow_succ]`.
-/
theorem sandwich {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    {K : FinExt l} {m d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    {D : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l} (hD : IsDec act χ K m M D U g)
    (i : ℤ) (n : ℕ)
    (hU : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ),
      CocOn (Gj K m) (twAct act χ i U) (ball l d) c →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ))
    (c : GQ l → Fin d → PadicComplex l) (k : ℕ)
    (hc : CocOn (Gj K m) (twAct act χ i M) (ball l d) c)
    (hk : CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ)) :
    CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ (n + 1) • c σ) := by
  obtain ⟨hdet, hint, hinv, -, hcomm⟩ := hD
  set E : Matrix (Fin d) (Fin d) (PadicComplex l) := (l : PadicComplex l) • D⁻¹ with hE
  have hEint : ∀ a b, ‖E a b‖ ≤ 1 := fun a b => by simpa [hE] using hinv a b
  have hDE : ∀ y, D *ᵥ (E *ᵥ y) = (l : PadicComplex l) • y := fun y => by
    rw [Matrix.mulVec_mulVec, hE, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinj : Function.Injective D.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det D).2 hdet)
  have hEt : ∀ σ ∈ Gj K m, ∀ y, twAct act χ i U σ (E *ᵥ y) = E *ᵥ twAct act χ i M σ y := by
    intro σ hσ y
    apply hinj
    show D *ᵥ _ = D *ᵥ _
    rw [← twAct_mulVec act χ i M U D σ (hcomm σ hσ), hDE, hDE, twAct_smul_nat]
  obtain ⟨x, hx, hxe⟩ := hU (fun σ => E *ᵥ c σ) k
    ⟨(continuous_const.matrix_mulVec continuous_id).comp_continuousOn hc.1,
      fun σ hσ => mulVec_mem_ball hEint (hc.2.1 σ hσ), fun σ hσ τ hτ => by
        simp only [hc.2.2 σ hσ τ hτ, Matrix.mulVec_add, hEt σ hσ]⟩
    (by
      obtain ⟨x, hx, hxe⟩ := hk
      refine ⟨E *ᵥ x, mulVec_mem_ball hEint hx, fun σ hσ => ?_⟩
      have := hxe σ hσ
      simp only at this ⊢
      rw [hEt σ hσ, ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul])
  refine ⟨D *ᵥ x, mulVec_mem_ball hint hx, fun σ hσ => ?_⟩
  have := hxe σ hσ
  simp only at this ⊢
  rw [twAct_mulVec act χ i M U D σ (hcomm σ hσ), ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul,
    hDE, smul_smul, pow_succ]

/- English proof (translation)
Introduce and unpack `f ⟨hfc, hfm⟩ ⟨k, x, hx⟩`. Rewrite `hfc` using `[continuous_adicModule_iff]`. Establish `hb : ∀ y, Ψ y ∈ ball l d` using `fun y => hr ▸ ⟨y, rfl⟩`. Set `c : GQ l → Fin d → PadicComplex l` to `fun σ => if h : σ ∈ G then Ψ (f ⟨σ, h⟩) else 0`. Establish `hc : ∀ σ (h : σ ∈ G), c σ = Ψ (f ⟨σ, h⟩)` using `fun σ h => dif_pos h`.

Establish `hcont : Continuous fun g : ↥G => Ψ (f g)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`.

Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one hε (norm_l_lt (l := l))`. Use `filter_upwards [hfc g N] with h hh`. Take `⟨y, e⟩` from `hh`. Rewrite using `[dist_eq_norm, ← map_sub, e, hl, norm_smul, norm_pow]`. Use `lt_of_le_of_lt ?_ hN` and prove the remaining obligations.

Conclude with `mul_le_of_le_one_right (by positivity) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (hb y))`. Take `⟨y, hy, hye⟩` from `H c k ⟨by`. Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Use `hcont using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Conclude with `hc g g.2,`. Use `fun σ hσ => by rw [hc σ hσ]; exact hb _,`. Use `fun σ hσ τ hτ => by`. Rewrite using `[hc σ hσ, hc τ hτ, hc _ (G.mul_mem hσ hτ)]`. Use `hfm ⟨σ, hσ⟩ ⟨τ, hτ⟩` as an intermediate fact.

Rewrite using `[← hA ⟨σ, hσ⟩, ← map_add, ← this]`. Use the proof step `rfl⟩`. Use the proof step `⟨Ψ x, hb x, fun σ hσ => by`. Use `hx ⟨σ, hσ⟩` as an intermediate fact. Simplify using `only [Pi.smul_apply] at this`.

Simplify using `only`. Rewrite using `[hc σ hσ, ← hl, this, map_sub, hA]⟩`. Rewrite `hy` using `[← hr]`. Take `⟨z, rfl⟩` from `hy`. Use `⟨z, fun g => hinj ?_⟩` and prove the remaining obligations.

Use `hye g g.2` as an intermediate fact. Simplify using `only at this`. Rewrite using `[Pi.smul_apply, hl, map_sub, hA, ← this, hc g g.2]`.
-/
theorem transfer {G : Subgroup (GQ l)} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] ↥G X) {d : ℕ}
    (A : GQ l → (Fin d → PadicComplex l) → (Fin d → PadicComplex l))
    (Ψ : X →+ (Fin d → PadicComplex l)) (hinj : Function.Injective Ψ)
    (hr : Set.range Ψ = ball l d)
    (hl : ∀ (k : ℕ) x, Ψ ((l : ℤ_[l]) ^ k • x) = (l : PadicComplex l) ^ k • Ψ x)
    (hA : ∀ (g : ↥G) x, Ψ (ρ g x) = A g (Ψ x)) (n : ℕ)
    (H : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ), CocOn G A (ball l d) c →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ)) :
    @TorsKilledBy ℤ_[l] ↥G X _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology X) ρ
      (l : ℤ_[l]) ((l : ℤ_[l]) ^ n) := by
  classical
  rintro f ⟨hfc, hfm⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_iff] at hfc
  have hb : ∀ y, Ψ y ∈ ball l d := fun y => hr ▸ ⟨y, rfl⟩
  let c : GQ l → Fin d → PadicComplex l := fun σ => if h : σ ∈ G then Ψ (f ⟨σ, h⟩) else 0
  have hc : ∀ σ (h : σ ∈ G), c σ = Ψ (f ⟨σ, h⟩) := fun σ h => dif_pos h
  have hcont : Continuous fun g : ↥G => Ψ (f g) := by
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt (l := l))
    filter_upwards [hfc g N] with h hh
    obtain ⟨y, e⟩ := hh
    rw [dist_eq_norm, ← map_sub, e, hl, norm_smul, norm_pow]
    refine lt_of_le_of_lt ?_ hN
    exact mul_le_of_le_one_right (by positivity) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (hb y))
  obtain ⟨y, hy, hye⟩ := H c k
    ⟨by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hcont using 1
      funext g
      exact hc g g.2,
    fun σ hσ => by rw [hc σ hσ]; exact hb _,
    fun σ hσ τ hτ => by
      rw [hc σ hσ, hc τ hτ, hc _ (G.mul_mem hσ hτ)]
      have := hfm ⟨σ, hσ⟩ ⟨τ, hτ⟩
      rw [← hA ⟨σ, hσ⟩, ← map_add, ← this]
      rfl⟩
    ⟨Ψ x, hb x, fun σ hσ => by
      have := hx ⟨σ, hσ⟩
      simp only [Pi.smul_apply] at this
      simp only
      rw [hc σ hσ, ← hl, this, map_sub, hA]⟩
  rw [← hr] at hy
  obtain ⟨z, rfl⟩ := hy
  refine ⟨z, fun g => hinj ?_⟩
  have := hye g g.2
  simp only at this
  rw [Pi.smul_apply, hl, map_sub, hA, ← this, hc g g.2]

/- English proof (translation)
Set `e` to `TensorProduct.equivFinsuppOfBasisLeft (N := Q) b`. Use `⟨⟨⟨fun x a => Φ (e x a), ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Introduce `x y`.

Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Introduce `x y hxy`. Apply `e.injective` to reduce the goal to its premises. Use extensionality with `a`.

Conclude with `hinj (congrFun hxy a)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ a`. Conclude with `(hr ▸ ⟨_, rfl⟩ : Φ (e x a) ∈ {y : PadicComplex l | ‖y‖ ≤ 1})`.

Introduce `hy`. Establish `: ∀ a, ∃ q, Φ q = y a` using `fun a => (hr.symm ▸ hy a : y a ∈ Set.range Φ)`. Use `choose q hq using this`. Use `⟨e.symm (Finsupp.equivFunOnFinite.symm q), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Simplify using `[hq]`. Introduce `z x`. Use function extensionality and compare the values at `a`. Simplify using `[hz]`. Introduce `t q a`.

Simplify using `[e, hz]`.
-/
theorem exists_coord {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (hinj : Function.Injective Φ) (hr : Set.range Φ = {y | ‖y‖ ≤ 1})
    (hz : ∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) :
    ∃ Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l), Function.Injective Ψ ∧
      Set.range Ψ = ball l d ∧ (∀ (z : ℤ_[l]) x, Ψ (z • x) = zC z • Ψ x) ∧
      ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q := by
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := Q) b
  refine ⟨⟨⟨fun x a => Φ (e x a), ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · funext a; simp
  · intro x y; funext a; simp
  · intro x y hxy
    apply e.injective
    ext a
    exact hinj (congrFun hxy a)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩ a
      exact (hr ▸ ⟨_, rfl⟩ : Φ (e x a) ∈ {y : PadicComplex l | ‖y‖ ≤ 1})
    · intro hy
      have : ∀ a, ∃ q, Φ q = y a := fun a =>
        (hr.symm ▸ hy a : y a ∈ Set.range Φ)
      choose q hq using this
      refine ⟨e.symm (Finsupp.equivFunOnFinite.symm q), ?_⟩
      funext a
      simp [hq]
  · intro z x
    funext a
    simp [hz]
  · intro t q a
    simp [e, hz]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => funext a`. Simplify using `[twAct, Matrix.mulVec, dotProduct]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, hx, hy, map_add]`.

Use function extensionality and compare the values at `a`. Simplify using `[twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]`. Consider the case `tmul t q`. Use function extensionality and compare the values at `a`. Establish `h1 : b.repr (r t) a = ∑ j, b.repr (r (b j)) a * b.repr t j` using `by conv_lhs => rw [← b.sum_repr t, map_sum, map_sum, Finsupp.finsetSum_apply]`.

Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]`. Simplify using `only [TensorProduct.map_tmul, hΨ, twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, act_zC ha, hM, hs, h1, zC_sum, zC_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem coord_equivariant {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l))
    (hΨ : ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q)
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (r : T →ₗ[ℤ_[l]] T)
    (s : Q →ₗ[ℤ_[l]] Q) (hM : ∀ a j, M g a j = zC (b.repr (r (b j)) a))
    (hs : ∀ x, Φ (s x) = chiC χ i g * act g (Φ x)) (x : T ⊗[ℤ_[l]] Q) :
    Ψ (TensorProduct.map r s x) = twAct act χ i M g (Ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp [twAct, Matrix.mulVec, dotProduct]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  | tmul t q =>
    funext a
    have h1 : b.repr (r t) a = ∑ j, b.repr (r (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    simp only [TensorProduct.map_tmul, hΨ, twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, map_mul, act_zC ha, hM, hs, h1, zC_sum, zC_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[rI, ← finsum_mem_finset_eq_sum]`. Use `finsum_congr fun u => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h1 : u ∈ J <;> by_cases h2 : u = i <;> simp [h1, h2, vZ]`.
-/
theorem rI_eq (l m : ℕ) (J : Finset ℤ) (i : ℤ) :
    rI l m (J : Set ℤ) i = ∑ u ∈ J.erase i, (m + padicValInt l (u - i)) := by
  rw [rI, ← finsum_mem_finset_eq_sum]
  refine finsum_congr fun u => ?_
  by_cases h1 : u ∈ J <;> by_cases h2 : u = i <;> simp [h1, h2, vZ]

/- English proof (translation)
Establish `ha : IsActC AI.actC` using `⟨AI.actC_ext, AI.actC_norm⟩`. Establish `hχ : IsCyc P.χQ` using `P.χQ_cyc`. Establish `hHT'` using `GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel l _ _ ha hχ K _ d M U Dm g _ hD hHT`. Establish `hJ : J = (hfin.toFinset : Set ℤ)` using `hfin.coe_toFinset.symm`. Establish `hc6` using `GlobalTheory.T.cocycle_twist_coboundary_on_ball l _ _ ha hχ K _ d hlev U g hD.2.2.2.1 hfin.toFinset (hJ ▸ hHT') i`.

Rewrite `hc6` using `[← rI_eq, ← hJ]`. Establish `hs` using `sandwich hD i _ hc6`. Take `⟨Φ, hinj, hr, hz, hact⟩` from `GlobalTheory.T.xiGradedPiece_iso_twistedOC l P AI i`. Take `⟨Ψ, hΨi, hΨr, hΨz, hΨ⟩` from `exists_coord b Φ hinj hr hz`. Establish `hn : 2 + max 1 (rI l m J i) = 1 + max 1 (rI l m J i) + 1` using `by omega`.

Rewrite using `[hn]`. Use `transfer _ (twAct AI.actC P.χQ i M) Ψ hΨi hΨr (fun k x => by rw [hΨz, zC_pow_l]) (fun σ x => ?_) _ hs` and prove the remaining obligations. Establish `hζ : (σ : GQ l) (P.ζQ 1) = P.ζQ 1`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ ?_` and prove the remaining obligations. Use `(le_sup_right : _ ≤ Ks K _) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations.

Use `show P.ζQ 1 ^ (l ^ m) = 1`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hlev.1`. Establish `h1 : P.ζQ 1 ^ l = 1` using `(P.ζQ_succ 0).trans P.ζQ_zero`. Rewrite using `[pow_add, pow_one, pow_mul, h1, one_pow]`. Conclude with `coord_equivariant ha _ i b Φ Ψ hΨ M σ (ρ σ) (actQab (xiOK AI) i (i + 1) σ) (hb σ) (hact σ hζ) x`.
-/
theorem of_basis (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (m : ℕ) (hlev : Lev l m)
    (ρ : ↥(Gj K m) →* (T →ₗ[ℤ_[l]] T)) (i : ℤ)
    (J : Set ℤ) (hfin : J.Finite) {d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    (b : Module.Basis (Fin d) ℤ_[l] T)
    (hb : ∀ (σ : ↥(Gj K m)) a j, M σ a j = zC (b.repr (ρ σ (b j)) a))
    {Dm : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l}
    (hD : IsDec AI.actC P.χQ K m M Dm U g) (hHT : HTBasis AI.actC P.χQ (Gj K m) M J) :
    @TorsKilledBy ℤ_[l] _ _ _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology _)
      (repQ AI (Gj K m) ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l m J i))) := by
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hHT' := GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel l _ _ ha hχ K _ d M U Dm g _ hD hHT
  have hJ : J = (hfin.toFinset : Set ℤ) := hfin.coe_toFinset.symm
  have hc6 := GlobalTheory.T.cocycle_twist_coboundary_on_ball l _ _ ha hχ K _ d hlev U g hD.2.2.2.1 hfin.toFinset (hJ ▸ hHT') i
  rw [← rI_eq, ← hJ] at hc6
  have hs := sandwich hD i _ hc6
  obtain ⟨Φ, hinj, hr, hz, hact⟩ := GlobalTheory.T.xiGradedPiece_iso_twistedOC l P AI i
  obtain ⟨Ψ, hΨi, hΨr, hΨz, hΨ⟩ := exists_coord b Φ hinj hr hz
  have hn : 2 + max 1 (rI l m J i) = 1 + max 1 (rI l m J i) + 1 := by omega
  rw [hn]
  refine transfer _ (twAct AI.actC P.χQ i M) Ψ hΨi hΨr
    (fun k x => by rw [hΨz, zC_pow_l]) (fun σ x => ?_) _ hs
  have hζ : (σ : GQ l) (P.ζQ 1) = P.ζQ 1 := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ ?_
    refine (le_sup_right : _ ≤ Ks K _) (IntermediateField.subset_adjoin _ _ ?_)
    show P.ζQ 1 ^ (l ^ m) = 1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlev.1
    have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
    rw [pow_add, pow_one, pow_mul, h1, one_pow]
  exact coord_equivariant ha _ i b Φ Ψ hΨ M σ (ρ σ)
    (actQab (xiOK AI) i (i + 1) σ) (hb σ) (hact σ hζ) x

/- English proof (translation)
Introduce `D HW F h7 l _ K s LL h S E T M0 h0 i hle hW`. Establish `hsm : s ≤ mN l s (M0 + h0)` using `by unfold mN; omega`. Establish `hlev : Lev l (mN l s (M0 + h0))` using `⟨le_trans h.1 hsm, fun h2 => le_trans (h.2.1 h2) hsm⟩`. Establish `h1` using `(GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1`. Use `h1.elim fun d h1 => h1.elim fun M h1 => h1.elim fun A hM => ?_` and prove the remaining obligations.

Establish `h2` using `GlobalTheory.T.exists_decompletion_frame_of_lattice D HW F l K s LL h T M0 h0 hW d M A hM`. Use `h2.elim fun Dm h2 => h2.elim fun U h2 => h2.elim fun g hD => ?_` and prove the remaining obligations. Establish `h3` using `GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks D HW F h7 l K s LL h T hW.1 d M A hM _ hsm`. Use `Exists.elim hM fun b hb => ?_` and prove the remaining obligations. Conclude with `@of_basis l _ (D.loc l) (D.locA l) K _ _ (zlMod LL T) _ hlev ((actTZ LL T).comp (Subgroup.inclusion hle)) i _ h3.1 d M U b (fun σ => hb.1 (Subgroup.inclusion hle σ)) Dm g hD.1 h3.2`.
-/
theorem torsion_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (i : ℤ) (hle : Gj K (mN l s (M0 + h0)) ≤ GK K), HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) i (i + 1))) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K (mN l s (M0 + h0))) ((actTZ LL T).comp (Subgroup.inclusion hle)) i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) i))) := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 i hle hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hlev : Lev l (mN l s (M0 + h0)) :=
    ⟨le_trans h.1 hsm, fun h2 => le_trans (h.2.1 h2) hsm⟩
  have h1 := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  refine h1.elim fun d h1 => h1.elim fun M h1 => h1.elim fun A hM => ?_
  have h2 := GlobalTheory.T.exists_decompletion_frame_of_lattice D HW F l K s LL h T M0 h0 hW d M A hM
  refine h2.elim fun Dm h2 => h2.elim fun U h2 => h2.elim fun g hD => ?_
  have h3 := GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks D HW F h7 l K s LL h T hW.1 d M A hM _ hsm
  refine Exists.elim hM fun b hb => ?_
  exact @of_basis l _ (D.loc l) (D.locA l) K _ _ (zlMod LL T) _ hlev
    ((actTZ LL T).comp (Subgroup.inclusion hle)) i _ h3.1 d M U b
    (fun σ => hb.1 (Subgroup.inclusion hle σ)) Dm g hD.1 h3.2

end GlobalTheory.Cyc.GradedTorsion
