import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceConjTransposeMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.Orb
variable {D : D7}

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `(Formalism.BasicNotions.Examples₂.stdSpace_gram_apply _ 1 (fun _ => false) 1 0 a b).trans ?_` and prove the remaining obligations. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[Matrix.one_apply_eq]`.

Conclude with `(if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])`. Rewrite using `[Matrix.one_apply_ne hab]`. Conclude with `if_neg hab`.
-/
theorem gram_rank_one_one : (V1 D).gram = 1 := by
  refine Matrix.ext fun a b => ?_
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply _ 1 (fun _ => false) 1 0 a b).trans ?_
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
  · rw [Matrix.one_apply_ne hab]
    exact if_neg hab

/- English proof (translation)
Unfold `gramAt`. Rewrite using `[gram_rank_one_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  unfold gramAt
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[gram_at_place_rank_one]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use `open scoped ComplexOrder in`.

Simplify using `using (Matrix.PosDef.one : (1 : Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ).PosDef)`.
-/
theorem cartan_involution_rank_one (τ : D.what₂.Tau) : IsCartanInv (gramAt D (V1 D) τ) (1 : Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) := by
  rw [gram_at_place_rank_one]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · open scoped ComplexOrder in
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ).PosDef)

/- English proof (translation)
Unfold `gauss nrm`. Establish `h : ∀ τ, Matrix.trace ((z τ)ᴴ * (gramAt D (V1 D) τ * 1) * z τ) = ((fro (z τ) : ℝ) : ℂ)`. Introduce `τ`. Rewrite using `[gram_at_place_rank_one, mul_one, Matrix.mul_one, trace_conjTranspose_mul_self]`. Simplify using `only [h]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem gaussian_rank_one_formula {n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin n) ℂ) :
    gauss (V1 D) l (fun _ => 1) z = ((Real.exp (-(2 * Real.pi) * nrm l z) : ℝ) : ℂ) := by
  unfold gauss nrm
  have h : ∀ τ, Matrix.trace ((z τ)ᴴ * (gramAt D (V1 D) τ * 1) * z τ) = ((fro (z τ) : ℝ) : ℂ) := by
    intro τ
    rw [gram_at_place_rank_one, mul_one, Matrix.mul_one, trace_conjTranspose_mul_self]
  simp only [h]
  push_cast
  rfl

abbrev mm {r n : ℕ} (y : Mx D r n) (b : Matrix (Fin n) (Fin n) (AE D)) : Mx D r n := HMul.hMul y b

/- English proof (translation)
Conclude with `Matrix.map_mul (f := (θ τ).comp (infPart D)) (L := x) (M := y)`.
-/
theorem compAt_mm {r n : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D r n) (y : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (mm x y) = compAt θ τ x * compAt θ τ y := by
  exact Matrix.map_mul (f := (θ τ).comp (infPart D)) (L := x) (M := y)

/- English proof (translation)
Establish `h : a.1 * (a⁻¹).1 = 1` using `Units.mul_inv a`. Use `show HMul.hMul (HMul.hMul y a.1) (a⁻¹).1 = y`. Rewrite using `[Matrix.mul_assoc, h, Matrix.mul_one]`.
-/
theorem mm_inv {r n : ℕ} (y : Mx D r n) (a : GL (Fin n) (AE D)) : mm (mm y a.1) (a⁻¹).1 = y := by
  have h : a.1 * (a⁻¹).1 = 1 := Units.mul_inv a
  show HMul.hMul (HMul.hMul y a.1) (a⁻¹).1 = y
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

/- English proof (translation)
Use `haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Conclude with `IsModuleTopology.isTopologicalRing (Af D.host.F) _`.
-/
theorem topRing : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact IsModuleTopology.isTopologicalRing (Af D.host.F) _

/- English proof (translation)
The claim follows from `map_sum f g s`.
-/
theorem hom_sum {R S ι : Type*} [Semiring R] [Semiring S] (f : R →+* S) (s : Finset ι) (g : ι → R) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

/- English proof (translation)
Use `haveI := topRing (D := D)`. Take `⟨U₀, hc, hk, h0⟩` from `GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero D m n`. Take `⟨t, ht⟩` from `hT.elim_finite_subcover (fun x => (fun u => -x + u) ⁻¹' U₀) (fun x => hc.isOpen.preimage (by fun_prop)) (fun x hx => Set.mem_iUnion.2 ⟨x, by simpa using h0⟩)`. Establish `hpre : ∀ x, (fun u => -x + u) ⁻¹' U₀ = (Homeomorph.addLeft (-x)) ⁻¹' U₀` using `fun _ => rfl`. Use `⟨U₀ ∪ ⋃ x ∈ t, (fun u => -x + u) ⁻¹' U₀, ?_, ?_, Or.inl h0, fun y hy => Or.inr (ht hy)⟩` and prove the remaining obligations.

Use `hc.union ?_` and prove the remaining obligations. Establish `: ∀ x ∈ t, IsClopen ((fun u => -x + u) ⁻¹' U₀)` using `fun x _ => hc.preimage (by fun_prop)`. Conclude with `t.finite_toSet.isClopen_biUnion this`. Use `hk.union (t.finite_toSet.isCompact_biUnion fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[hpre]`.

Conclude with `(Homeomorph.addLeft (-x)).isCompact_preimage.2 hk`.
-/
theorem exists_clopen_superset {m n : ℕ} (T : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) (hT : IsCompact T) :
    ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧
      (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U ∧ T ⊆ U := by
  haveI := topRing (D := D)
  obtain ⟨U₀, hc, hk, h0⟩ := GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero D m n
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun x => (fun u => -x + u) ⁻¹' U₀)
    (fun x => hc.isOpen.preimage (by fun_prop)) (fun x hx => Set.mem_iUnion.2 ⟨x, by simpa using h0⟩)
  have hpre : ∀ x, (fun u => -x + u) ⁻¹' U₀ = (Homeomorph.addLeft (-x)) ⁻¹' U₀ := fun _ => rfl
  refine ⟨U₀ ∪ ⋃ x ∈ t, (fun u => -x + u) ⁻¹' U₀, ?_, ?_, Or.inl h0, fun y hy => Or.inr (ht hy)⟩
  · refine hc.union ?_
    have : ∀ x ∈ t, IsClopen ((fun u => -x + u) ⁻¹' U₀) := fun x _ => hc.preimage (by fun_prop)
    exact t.finite_toSet.isClopen_biUnion this
  · refine hk.union (t.finite_toSet.isCompact_biUnion fun x _ => ?_)
    rw [hpre]
    exact (Homeomorph.addLeft (-x)).isCompact_preimage.2 hk

/- English proof (translation)
Use `haveI := topRing (D := D)`. Set `fp : Mx D n n → (Fin n → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `fun b i j => finPart D (b i j)`. Establish `hfp : Continuous fp`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `(GlobalTheory.Member.continuous_finPart D).comp ((continuous_apply j).comp (continuous_apply i))`.

Set `mulF : (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) × (Fin n → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `fun p i j => ∑ k, p.1 i k * p.2 k j`. Establish `hmul : Continuous mulF`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations. Use `fun_prop`.

Establish `hT : IsCompact (mulF '' (tsupport g ×ˢ (fp '' A₂)))` using `(hg.isCompact.prod (hA₂.image hfp)).image hmul`. Take `⟨U, hc, hk, h0, hsub⟩` from `exists_clopen_superset _ hT`. Use `⟨U, hc, hk, h0, fun a ha y hy => hsub ?_⟩` and prove the remaining obligations. Use `⟨(_, fp (a⁻¹).1), ⟨subset_tsupport g hy, ⟨_, ha, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`.

Establish `hy' : y = mm (mm y a.1) (a⁻¹).1` using `(mm_inv y a).symm`. Use `show ∑ k, finPart D ((mm y a.1) i k) * finPart D ((a⁻¹).1 k j) = finPart D (y i j)`. Use `conv_rhs => rw [hy']`. Establish `e : (mm (mm y a.1) (a⁻¹).1) i j = ∑ k, (mm y a.1) i k * (a⁻¹).1 k j` using `Matrix.mul_apply`. Rewrite using `[e, hom_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => (RingHom.map_mul _ _ _).symm`.
-/
theorem exists_supp_clopen {n : ℕ} (g : (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : HasCompactSupport g) (A₂ : Set (Mx D n n)) (hA₂ : IsCompact A₂) :
    ∃ U : Set (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧
      (0 : Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U ∧
      ∀ (a : GL (Fin n) (AE D)), (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
        g (fun i j => finPart D ((mm y a.1) i j)) ≠ 0 → (fun i j => finPart D (y i j)) ∈ U := by
  haveI := topRing (D := D)
  let fp : Mx D n n → (Fin n → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := fun b i j => finPart D (b i j)
  have hfp : Continuous fp := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.Member.continuous_finPart D).comp ((continuous_apply j).comp (continuous_apply i))
  let mulF : (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ×
      (Fin n → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun p i j => ∑ k, p.1 i k * p.2 k j
  have hmul : Continuous mulF := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine continuous_finset_sum _ fun k _ => ?_
    fun_prop
  have hT : IsCompact (mulF '' (tsupport g ×ˢ (fp '' A₂))) :=
    (hg.isCompact.prod (hA₂.image hfp)).image hmul
  obtain ⟨U, hc, hk, h0, hsub⟩ := exists_clopen_superset _ hT
  refine ⟨U, hc, hk, h0, fun a ha y hy => hsub ?_⟩
  refine ⟨(_, fp (a⁻¹).1), ⟨subset_tsupport g hy, ⟨_, ha, rfl⟩⟩, ?_⟩
  funext i j
  have hy' : y = mm (mm y a.1) (a⁻¹).1 := (mm_inv y a).symm
  show ∑ k, finPart D ((mm y a.1) i k) * finPart D ((a⁻¹).1 k j) = finPart D (y i j)
  conv_rhs => rw [hy']
  have e : (mm (mm y a.1) (a⁻¹).1) i j = ∑ k, (mm y a.1) i k * (a⁻¹).1 k j := Matrix.mul_apply
  rw [e, hom_sum]
  exact Finset.sum_congr rfl fun k _ => (RingHom.map_mul _ _ _).symm

/- English proof (translation)
Establish `hc : Continuous fun b : Mx D n n => ∑ τ, fro (compAt θ τ b)` using `continuous_finset_sum _ fun τ _ => continuous_fro.comp (GlobalTheory.RealWeil.continuous_compAt hθ τ n n)`. Take `⟨C, hC⟩` from `hA₂.exists_bound_of_continuousOn hc.continuousOn`. Use `⟨max C 1, by positivity, fun b hb τ => ?_⟩` and prove the remaining obligations. Establish `h1 : fro (compAt θ τ b) ≤ ∑ τ, fro (compAt θ τ b)` using `Finset.single_le_sum (f := fun τ => fro (compAt θ τ b)) (fun _ _ => fro_nonneg _) (Finset.mem_univ τ)`. Conclude with `h1.trans ((le_abs_self _).trans ((hC b hb).trans (le_max_left _ _)))`.
-/
theorem exists_inv_bound (θ : InfFam D) (hθ : IsInfFam θ) {n : ℕ} (A₂ : Set (Mx D n n)) (hA₂ : IsCompact A₂) :
    ∃ S : ℝ, 0 < S ∧ ∀ b ∈ A₂, ∀ τ, fro (compAt θ τ b) ≤ S := by
  have hc : Continuous fun b : Mx D n n => ∑ τ, fro (compAt θ τ b) :=
    continuous_finset_sum _ fun τ _ => continuous_fro.comp (GlobalTheory.RealWeil.continuous_compAt hθ τ n n)
  obtain ⟨C, hC⟩ := hA₂.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, by positivity, fun b hb τ => ?_⟩
  have h1 : fro (compAt θ τ b) ≤ ∑ τ, fro (compAt θ τ b) :=
    Finset.single_le_sum (f := fun τ => fro (compAt θ τ b)) (fun _ _ => fro_nonneg _) (Finset.mem_univ τ)
  exact h1.trans ((le_abs_self _).trans ((hC b hb).trans (le_max_left _ _)))

/- English proof (translation)
Unfold `nrm`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Establish `hy' : y = mm (mm y a.1) (a⁻¹).1` using `(mm_inv y a).symm`. Establish `h1 : fro (compAt θ τ y) ≤ fro (compAt θ τ (mm y a.1)) * S` using `by conv_lhs => rw [hy', compAt_mm]`.

Conclude with `(fro_mul _ _).trans (mul_le_mul_of_nonneg_left (hS τ) (fro_nonneg _))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nrm_le {n : ℕ} (θ : InfFam D) (l : D.what₂.Tau → ℝ) (S : ℝ) (a : GL (Fin n) (AE D))
    (hS : ∀ τ, fro (compAt θ τ (a⁻¹).1) ≤ S) (y : Mx D (V1 D).rank n) :
    nrm l (fun τ => compAt θ τ y) ≤ S * nrm l (fun τ => compAt θ τ (mm y a.1)) := by
  unfold nrm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hy' : y = mm (mm y a.1) (a⁻¹).1 := (mm_inv y a).symm
  have h1 : fro (compAt θ τ y) ≤ fro (compAt θ τ (mm y a.1)) * S := by
    conv_lhs => rw [hy', compAt_mm]
    exact (fro_mul _ _).trans (mul_le_mul_of_nonneg_left (hS τ) (fro_nonneg _))
  calc |l τ| * fro (compAt θ τ y) ≤ |l τ| * (fro (compAt θ τ (mm y a.1)) * S) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = S * (|l τ| * fro (compAt θ τ (mm y a.1))) := by ring

/- English proof (translation)
Unfold `nrm`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[abs_div, abs_of_pos hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nrm_scale {m n : ℕ} (l : D.what₂.Tau → ℝ) (c : ℝ) (hc : 0 < c) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    nrm (fun τ => l τ / c) z = nrm l z / c := by
  unfold nrm
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [abs_div, abs_of_pos hc]
  ring

/- English proof (translation)
Take `⟨S, hS0, hS⟩` from `exists_inv_bound θ hθ A₂ hA₂`. Take `⟨C, hC0, hC⟩` from `evalPoly_bound l hl q Real.pi Real.pi_pos`. Take `⟨G₀, hG₀⟩` from `(hg.1.continuous).bounded_above_of_compact_support hg.2`. Use `set G := max G₀ 0 with hGdef`. Establish `hG0 : 0 ≤ G` using `le_max_right _ _`.

Establish `hG : ∀ x, ‖g x‖ ≤ G` using `fun x => (hG₀ x).trans (le_max_left _ _)`. Take `⟨U, hUc, hUk, hU0, hU⟩` from `exists_supp_clopen g hg.2 A₂ hA₂`. Establish `h2S : 0 < 2 * S` using `by positivity`. Establish `hl' : ∀ τ, l τ / (2 * S) ≠ 0` using `fun τ => div_ne_zero (hl τ) h2S.ne'`. Take `⟨Φ, hΦ, -, -⟩` from `GlobalTheory.StdUnn.Inhab.fock_gauss GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n (V1 D) θ (fun τ => l τ / (2 * S)) hl' (fun _ => 1) cartan_involution_rank_one U hUc hUk hU0`.

Establish `hval : ∀ y, Φ.1 y = ((Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) (fun τ => compAt θ τ y)) * U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j)) : ℝ) : ℂ)`. Introduce `y`. Rewrite using `[hΦ]`. Use `show gauss _ _ _ _ * _ = _`. Rewrite using `[gaussian_rank_one_formula]`.

Distinguish the cases in `h : (fun i j => finPart D (y i j)) ∈ U`. Simplify using `[Set.indicator_of_mem h]`. Simplify using `[Set.indicator_of_notMem h]`. Use `⟨((C * G : ℝ) : ℂ) • Φ.1, Submodule.smul_mem _ _ Φ.2, fun y => ?_, fun a ha y => ?_⟩` and prove the remaining obligations. Establish `: (((C * G : ℝ) : ℂ) • Φ.1) y = ((C * G * (Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) (fun τ => compAt θ τ y)) * U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j))) : ℝ) : ℂ)`.

Rewrite using `[Pi.smul_apply, hval, smul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[this, Complex.ofReal_re, Complex.ofReal_im]`. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Establish `: 0 ≤ U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j))` using `Set.indicator_nonneg (fun _ _ => zero_le_one) _`. Check the signs of the components of the expression. Distinguish the cases in `h0 : g (fun i j => finPart D ((mm y a.1) i j)) = 0`. Rewrite using `[h0, mul_zero, norm_zero]`. Conclude with `norm_nonneg _`.

Establish `hmem` using `hU a ha y h0 set z := fun τ => compAt θ τ (mm y a.1) with hz set Y := fun τ => compAt θ τ y with hY`. Establish `hnr : nrm l Y ≤ S * nrm l z` using `nrm_le θ l S a (fun τ => hS _ ha τ) y`. Establish `hrhs : ‖(((C * G : ℝ) : ℂ) • Φ.1) y‖ = C * G * Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y)`. Establish `e : (((C * G : ℝ) : ℂ) • Φ.1) y = ((C * G * Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y) : ℝ) : ℂ)`. Rewrite using `[Pi.smul_apply, hval, Set.indicator_of_mem hmem, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Rewrite using `[hrhs, norm_mul, norm_mul, gaussian_rank_one_formula, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Establish `hN` using `nrm_nonneg l z`.

Establish `hexp : Real.exp (Real.pi * nrm l z) * Real.exp (-(2 * Real.pi) * nrm l z) ≤ Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y)`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Rewrite using `[nrm_scale l _ h2S]`. Establish `h3 : nrm l Y / (2 * S) ≤ nrm l z / 2`.

Rewrite using `[div_le_div_iff₀ h2S (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Use polynomial arithmetic with `[Real.pi_pos]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hC z`.

Conclude with `hG _`. Use `_ = C * G * (Real.exp (Real.pi * nrm l z) * Real.exp (-(2 * Real.pi) * nrm l z)) := by ring`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hG0)`.
-/
theorem gen_maj (θ : InfFam D) (hθ : IsInfFam θ) {n : ℕ} (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (q : MvPolynomial (D.what₂.Tau × Fin (V1 D).rank × Fin n × Bool) ℂ)
    (g : (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin (V1 D).rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (A₂ : Set (Mx D n n)) (hA₂ : IsCompact A₂) :
    ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
      ∀ a : GL (Fin n) (AE D), (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
        ‖evalPoly q (fun τ => compAt θ τ (mm y a.1)) *
          gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ (mm y a.1)) *
          g (fun i j => finPart D ((mm y a.1) i j))‖ ≤ ‖M y‖ := by
  obtain ⟨S, hS0, hS⟩ := exists_inv_bound θ hθ A₂ hA₂
  obtain ⟨C, hC0, hC⟩ := evalPoly_bound l hl q Real.pi Real.pi_pos
  obtain ⟨G₀, hG₀⟩ := (hg.1.continuous).bounded_above_of_compact_support hg.2
  set G := max G₀ 0 with hGdef
  have hG0 : 0 ≤ G := le_max_right _ _
  have hG : ∀ x, ‖g x‖ ≤ G := fun x => (hG₀ x).trans (le_max_left _ _)
  obtain ⟨U, hUc, hUk, hU0, hU⟩ := exists_supp_clopen g hg.2 A₂ hA₂
  have h2S : 0 < 2 * S := by positivity
  have hl' : ∀ τ, l τ / (2 * S) ≠ 0 := fun τ => div_ne_zero (hl τ) h2S.ne'
  obtain ⟨Φ, hΦ, -, -⟩ := GlobalTheory.StdUnn.Inhab.fock_gauss GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n (V1 D) θ
    (fun τ => l τ / (2 * S)) hl' (fun _ => 1) cartan_involution_rank_one U hUc hUk hU0
  have hval : ∀ y, Φ.1 y = ((Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) (fun τ => compAt θ τ y)) *
      U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j)) : ℝ) : ℂ) := by
    intro y
    rw [hΦ]
    show gauss _ _ _ _ * _ = _
    rw [gaussian_rank_one_formula]
    by_cases h : (fun i j => finPart D (y i j)) ∈ U
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  refine ⟨((C * G : ℝ) : ℂ) • Φ.1, Submodule.smul_mem _ _ Φ.2, fun y => ?_, fun a ha y => ?_⟩
  · have : (((C * G : ℝ) : ℂ) • Φ.1) y = ((C * G * (Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) (fun τ => compAt θ τ y)) *
        U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j))) : ℝ) : ℂ) := by
      rw [Pi.smul_apply, hval, smul_eq_mul]
      push_cast
      rfl
    rw [this, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have : 0 ≤ U.indicator (fun _ => (1 : ℝ)) (fun i j => finPart D (y i j)) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    positivity
  · by_cases h0 : g (fun i j => finPart D ((mm y a.1) i j)) = 0
    · rw [h0, mul_zero, norm_zero]
      exact norm_nonneg _
    · have hmem := hU a ha y h0
      set z := fun τ => compAt θ τ (mm y a.1) with hz
      set Y := fun τ => compAt θ τ y with hY
      have hnr : nrm l Y ≤ S * nrm l z := nrm_le θ l S a (fun τ => hS _ ha τ) y
      have hrhs : ‖(((C * G : ℝ) : ℂ) • Φ.1) y‖ = C * G * Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y) := by
        have e : (((C * G : ℝ) : ℂ) • Φ.1) y = ((C * G * Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y) : ℝ) : ℂ) := by
          rw [Pi.smul_apply, hval, Set.indicator_of_mem hmem, smul_eq_mul]
          push_cast
          ring
        rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hrhs, norm_mul, norm_mul, gaussian_rank_one_formula, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hN := nrm_nonneg l z
      have hexp : Real.exp (Real.pi * nrm l z) * Real.exp (-(2 * Real.pi) * nrm l z) ≤
          Real.exp (-(2 * Real.pi) * nrm (fun τ => l τ / (2 * S)) Y) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        rw [nrm_scale l _ h2S]
        have h3 : nrm l Y / (2 * S) ≤ nrm l z / 2 := by
          rw [div_le_div_iff₀ h2S (by norm_num)]
          nlinarith
        nlinarith [Real.pi_pos]
      calc ‖evalPoly q z‖ * Real.exp (-(2 * Real.pi) * nrm l z) * ‖g _‖
          ≤ (C * Real.exp (Real.pi * nrm l z)) * Real.exp (-(2 * Real.pi) * nrm l z) * G := by
            gcongr
            · exact hC z
            · exact hG _
        _ = C * G * (Real.exp (Real.pi * nrm l z) * Real.exp (-(2 * Real.pi) * nrm l z)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hG0)

/- English proof (translation)
Establish `: w = ((w.re : ℝ) : ℂ)` using `Complex.ext rfl (by simpa using h.2)`. Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using h.1)]`. Simplify using the standard rewrite rules.
-/
theorem nn_norm {w : ℂ} (h : 0 ≤ w.re ∧ w.im = 0) : ‖w‖ = w.re := by
  have : w = ((w.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using h.2)
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using h.1)]
  simp

end GlobalTheory.CompanionTheory.ThTot.Orb

namespace GlobalTheory.CompanionTheory.ThTot

/- English proof (translation)
Introduce `D n θ hθ l hl f hf A₁ A₂ _ hA₂`. Establish `key : ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧ ∀ a : GL (Fin n) (AE D), (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n, ‖f (Orb.mm y a.1)‖ ≤ ‖M y‖`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨q, g, hg, rfl⟩` from `hf`.

Conclude with `Orb.gen_maj θ hθ l hl q g hg A₂ hA₂`. Consider the case `zero`. Use `⟨0, Submodule.zero_mem _, fun y => by simp, fun a _ y => by simp⟩` and prove the remaining obligations. Consider the case `add f₁ f₂ _ _ h₁ h₂`. Take `⟨M₁, hM₁, p₁, b₁⟩` from `h₁`.

Take `⟨M₂, hM₂, p₂, b₂⟩` from `h₂`. Establish `hp : ∀ y, 0 ≤ ((M₁ + M₂) y).re ∧ ((M₁ + M₂) y).im = 0` using `fun y => by`. Simplify using `only [Pi.add_apply, Complex.add_re, Complex.add_im]`. Conclude with `⟨add_nonneg (p₁ y).1 (p₂ y).1, by rw [(p₁ y).2, (p₂ y).2, add_zero]⟩`. Use `⟨M₁ + M₂, Submodule.add_mem _ hM₁ hM₂, hp, fun a ha y => ?_⟩` and prove the remaining obligations.

Rewrite using `[Orb.nn_norm (hp y)]`. Simplify using `only [Pi.add_apply, Complex.add_re]`. Establish `e₁` using `b₁ a ha y`. Establish `e₂` using `b₂ a ha y`. Rewrite `e₁` using `[Orb.nn_norm (p₁ y)]`.

Rewrite `e₂` using `[Orb.nn_norm (p₂ y)]`. Conclude with `(norm_add_le _ _).trans (add_le_add e₁ e₂)`. Consider the case `smul c f _ h`. Take `⟨M, hM, p, b⟩` from `h`. Establish `hp : ∀ y, 0 ≤ ((((‖c‖ : ℝ) : ℂ) • M) y).re ∧ ((((‖c‖ : ℝ) : ℂ) • M) y).im = 0` using `fun y => by`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]`. Conclude with `⟨mul_nonneg (norm_nonneg _) (p y).1, by rw [(p y).2, mul_zero]⟩`. Use `⟨((‖c‖ : ℝ) : ℂ) • M, Submodule.smul_mem _ _ hM, hp, fun a ha y => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, norm_norm]`. Conclude with `mul_le_mul_of_nonneg_left (b a ha y) (norm_nonneg _)`.

Take `⟨M, hM, p, b⟩` from `key`. Conclude with `⟨M, hM, p, fun a _ ha y => b a ha y⟩`.
-/
theorem orbitMaj : OrbitMaj := by
  intro D n θ hθ l hl f hf A₁ A₂ _ hA₂
  have key : ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
      ∀ a : GL (Fin n) (AE D), (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
          ‖f (Orb.mm y a.1)‖ ≤ ‖M y‖ := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨q, g, hg, rfl⟩ := hf
      exact Orb.gen_maj θ hθ l hl q g hg A₂ hA₂
    | zero =>
      refine ⟨0, Submodule.zero_mem _, fun y => by simp, fun a _ y => by simp⟩
    | add f₁ f₂ _ _ h₁ h₂ =>
      obtain ⟨M₁, hM₁, p₁, b₁⟩ := h₁
      obtain ⟨M₂, hM₂, p₂, b₂⟩ := h₂
      have hp : ∀ y, 0 ≤ ((M₁ + M₂) y).re ∧ ((M₁ + M₂) y).im = 0 := fun y => by
        simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
        exact ⟨add_nonneg (p₁ y).1 (p₂ y).1, by rw [(p₁ y).2, (p₂ y).2, add_zero]⟩
      refine ⟨M₁ + M₂, Submodule.add_mem _ hM₁ hM₂, hp, fun a ha y => ?_⟩
      rw [Orb.nn_norm (hp y)]
      simp only [Pi.add_apply, Complex.add_re]
      have e₁ := b₁ a ha y
      have e₂ := b₂ a ha y
      rw [Orb.nn_norm (p₁ y)] at e₁
      rw [Orb.nn_norm (p₂ y)] at e₂
      exact (norm_add_le _ _).trans (add_le_add e₁ e₂)
    | smul c f _ h =>
      obtain ⟨M, hM, p, b⟩ := h
      have hp : ∀ y, 0 ≤ ((((‖c‖ : ℝ) : ℂ) • M) y).re ∧ ((((‖c‖ : ℝ) : ℂ) • M) y).im = 0 := fun y => by
        simp only [Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
        exact ⟨mul_nonneg (norm_nonneg _) (p y).1, by rw [(p y).2, mul_zero]⟩
      refine ⟨((‖c‖ : ℝ) : ℂ) • M, Submodule.smul_mem _ _ hM, hp, fun a ha y => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, norm_norm]
      exact mul_le_mul_of_nonneg_left (b a ha y) (norm_nonneg _)
  obtain ⟨M, hM, p, b⟩ := key
  exact ⟨M, hM, p, fun a _ ha y => b a ha y⟩

end GlobalTheory.CompanionTheory.ThTot

end
