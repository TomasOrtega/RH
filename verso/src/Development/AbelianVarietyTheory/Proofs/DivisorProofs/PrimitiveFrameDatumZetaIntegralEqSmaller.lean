import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLMulIsPrimitiveFrameDiagonalLatticeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.OneSquareZeta
open ValuativeRel GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite `h₀`, the goal using `[isPrimFrame_iff]`. Establish `hrow : ∀ (M : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) C k) i, (M * Y).row i = M.row i ᵥ* Y` using `fun M Y i => by funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]`. Establish `hgX : g.val * X = (g * g₀⁻¹).val * (g₀.val * X)`. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc g.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`. Establish `hg0X : g₀.val * X = ((g * g₀⁻¹)⁻¹).val * (g.val * X)`.

Rewrite using `[hgX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Rewrite using `[mem_KO_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Conclude with `h₀.2 ((g * g₀⁻¹).val.row i) (by rw [← hrow, ← hgX]; exact h1 i) j`. Conclude with `h2 (((g * g₀⁻¹)⁻¹).val.row i) (by rw [← hrow, ← hg0X]; exact h₀.1 i) j`. Introduce and unpack `⟨hu1, hu2⟩`. Use `⟨fun i => ?_, fun c hc i => ?_⟩` and prove the remaining obligations. Use `show (g.val * X).row i ∈ Λ`.

Rewrite using `[hgX, hrow]`. Conclude with `vecMul_mem_of_int h₀.1 (fun j => hu1 i j)`. Establish `h3` using `h₀.2 (c ᵥ* (g * g₀⁻¹).val) (by rw [vecMul_vecMul, ← hgX]; exact hc)`. Establish `hc' : c = (c ᵥ* (g * g₀⁻¹).val) ᵥ* ((g * g₀⁻¹)⁻¹).val`. Rewrite using `[vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]`.

Rewrite using `[hc']`. Express the relevant statement in the definitionally equal form `(∑ l, (c ᵥ* (g * g₀⁻¹).val) l * ((g * g₀⁻¹)⁻¹).val l i) ∈ 𝒪[k]`. Conclude with `Subring.sum_mem _ fun l _ => mul_mem (h3 l) (hu2 l i)`.
-/
theorem isPrimFrame_mul_iff {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] {Λ : Submodule 𝒪[k] (C → k)}
    {X : Matrix (Fin a) C k} {g₀ : GL (Fin a) k} (h₀ : IsPrimFrame Λ (g₀.val * X)) (g : GL (Fin a) k) :
    IsPrimFrame Λ (g.val * X) ↔ g * g₀⁻¹ ∈ KO k (Fin a) := by
  rw [isPrimFrame_iff] at h₀ ⊢
  have hrow : ∀ (M : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) C k) i, (M * Y).row i = M.row i ᵥ* Y :=
    fun M Y i => by funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  have hgX : g.val * X = (g * g₀⁻¹).val * (g₀.val * X) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc g.val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hg0X : g₀.val * X = ((g * g₀⁻¹)⁻¹).val * (g.val * X) := by
    rw [hgX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [mem_KO_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h₀.2 ((g * g₀⁻¹).val.row i) (by rw [← hrow, ← hgX]; exact h1 i) j
    · exact h2 (((g * g₀⁻¹)⁻¹).val.row i) (by rw [← hrow, ← hg0X]; exact h₀.1 i) j
  · rintro ⟨hu1, hu2⟩
    refine ⟨fun i => ?_, fun c hc i => ?_⟩
    · show (g.val * X).row i ∈ Λ
      rw [hgX, hrow]; exact vecMul_mem_of_int h₀.1 (fun j => hu1 i j)
    · have h3 := h₀.2 (c ᵥ* (g * g₀⁻¹).val) (by rw [vecMul_vecMul, ← hgX]; exact hc)
      have hc' : c = (c ᵥ* (g * g₀⁻¹).val) ᵥ* ((g * g₀⁻¹)⁻¹).val := by
        rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [hc']
      change (∑ l, (c ᵥ* (g * g₀⁻¹).val) l * ((g * g₀⁻¹)⁻¹).val l i) ∈ 𝒪[k]
      exact Subring.sum_mem _ fun l _ => mul_mem (h3 l) (hu2 l i)

/- English proof (translation)
Conclude with `GlobalTheory.T.mirabolic_schwartzFunction_left_GL_equivariance k a A' C μ σ ν Ψ g h`.
-/
theorem fFun_mul_left {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C)
    (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k) :
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  exact GlobalTheory.T.mirabolic_schwartzFunction_left_GL_equivariance k a A' C μ σ ν Ψ g h

/- English proof (translation)
Conclude with `GlobalTheory.T.exists_GL_mul_isPrimitiveFrame_diagonalLattice k a C d X hX`.
-/
theorem exists_primFrame {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] (d : C → kˣ)
    (X : Matrix (Fin a) C k) (hX : X.rank = a) : ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  exact GlobalTheory.T.exists_GL_mul_isPrimitiveFrame_diagonalLattice k a C d X hX

/- English proof (translation)
Take `⟨m, hm, x, hx, y, hy, e⟩` from `GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g`. Establish `ht : ∀ m : Fin a → ℤ, GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i` using `fun m => Units.ext (by rw [GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])`. Use `⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨m', hm'⟩ hmem`. Take `⟨x', hx', y', hy', e'⟩` from `mem_shellSet.1 hmem`.

Establish `E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i`. Establish `h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y'`. Rewrite using `[← ht, ← e]`. Conclude with `e'`. Combine the equalities or inequalities in the displayed calculation.

Establish `E'` using `congrArg Units.val E`. Simplify using `only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'`. Conclude with `Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹) (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm`.
-/
theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `set X := X0 k σ * (invT h).val with hXdef`. Establish `hΛ : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹)`. Rewrite using `[latA, dualLat_diagLat, smul_diagLat]`. Establish `hrank : X.rank = a`. Use `(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 ⟨h, rfl⟩` as an intermediate fact.

Simplify using `using this`. Take `⟨g₀, hg₀⟩` from `exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) X hrank`. Rewrite `hg₀` using `[← hΛ]`. Take `⟨⟨m₀, hm₀⟩, hmem, huniq⟩` from `exists_unique_shell hϖ g₀`. Use `set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef`.

Establish `hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S`. Use `letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace`. Use `haveI : BorelSpace (GL (Fin a) k) := borel_GL`. Conclude with `(isOpen_KO.preimage (continuous_mul_right _)).measurableSet`. Establish `hS1 : (haarVol (KO k (Fin a))).real S = 1`.

Simplify using `[hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]`. Establish `hint : ∀ g : GL (Fin a) k, phiA μ σ ν ϖ n (diagLat c) Ψ (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) = S.indicator (fun _ => fFun μ σ ν Ψ X) g`. Introduce `g`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg, phiA, if_pos ((isPrimFrame_mul_iff hg₀ g).2 hg)]`.

Conclude with `fFun_mul_left μ σ ν Ψ g h`. Rewrite using `[Set.indicator_of_notMem hg, phiA, if_neg (fun h' => hg ((isPrimFrame_mul_iff hg₀ g).1 h')), zero_mul, zero_mul]`. Establish `hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν ((Fintype.card C : ℂ) / 2) (fun M => phiA μ σ ν ϖ n (diagLat c) Ψ (M * X)) m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • fFun μ σ ν Ψ X`. Introduce `m`. Rewrite using `[shell]`.

Repeatedly rewrite using `[hint]`. Establish `e1` using `setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1) (f := fun _ => fFun μ σ ν Ψ X) hSm`. Rewrite using `[e1, setIntegral_const]`. Establish `hsub : S ⊆ shellSet ϖ m₀`. Introduce `g hg`.

Take `⟨x, hx, y, hy, e⟩` from `mem_shellSet.1 hmem`. Use `mem_shellSet.2 ⟨g * g₀⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]`. Rewrite using `[hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]`.

Introduce `m hm`. Rewrite using `[hshell]`. Establish `: shellSet ϖ m.1 ∩ S = ∅`. Use `Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)` and prove the remaining obligations. Take `⟨x, hx, y, hy, e⟩` from `mem_shellSet.1 hg1`.

Use `mem_shellSet.2 ⟨(g * g₀⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `[this]`.
-/
theorem bigF_phiA {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ)
    (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (hϖ : IsUnif ϖ) (h : GL C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (phiA μ σ ν ϖ n (diagLat c) Ψ) (X0 k σ * (invT h).val) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  set X := X0 k σ * (invT h).val with hXdef
  have hΛ : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : X.rank = a := by
    have := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 ⟨h, rfl⟩; simpa using this
  obtain ⟨g₀, hg₀⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) X hrank
  rw [← hΛ] at hg₀
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₀
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, phiA μ σ ν ϖ n (diagLat c) Ψ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card C : ℂ) / 2) = S.indicator (fun _ => fFun μ σ ν Ψ X) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, phiA, if_pos ((isPrimFrame_mul_iff hg₀ g).2 hg)]
      exact fFun_mul_left μ σ ν Ψ g h
    · rw [Set.indicator_of_notMem hg, phiA, if_neg (fun h' => hg ((isPrimFrame_mul_iff hg₀ g).1 h')),
        zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card C : ℂ) / 2) (fun M => phiA μ σ ν ϖ n (diagLat c) Ψ (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • fFun μ σ ν Ψ X := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => fFun μ σ ν Ψ X) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹ * g₀ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀ = (g * g₀⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.OneSquareZeta

open GlobalTheory.OneSquareZeta in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ hϖ`. Use function extensionality and compare the values at `h`. Rewrite using `[bigZetaIntegral_eq, bigF_phiA μ σ ν ϖ n c Ψ hϖ h, splitTheta_fFun_frameFirstBlock_mul, smallP]`. Establish `hC : (Fintype.card C : ℂ) = a + Fintype.card A'`. Rewrite using `[← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) = apow (gdet h) ((Fintype.card A' : ℂ) / 2)`. Rewrite using `[← apow_add, hC]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [MonoidHom.mul_apply, Units.val_mul]`. Take the linear combination `(β (gdet h) * ν (gdet h) * smallF μ ν Ψ (Y0 k σ * h.val) : ℂ) * e`.
-/
theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ), IsUnif ϖ →
    bigP (haarVol (KO k (Fin a))) ϖ σ ν β (phiA μ σ ν ϖ n (diagLat c) Ψ) = smallP μ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ hϖ
  funext h
  rw [bigZetaIntegral_eq, bigF_phiA μ σ ν ϖ n c Ψ hϖ h, splitTheta_fFun_frameFirstBlock_mul, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination (β (gdet h) * ν (gdet h) * smallF μ ν Ψ (Y0 k σ * h.val) : ℂ) * e
