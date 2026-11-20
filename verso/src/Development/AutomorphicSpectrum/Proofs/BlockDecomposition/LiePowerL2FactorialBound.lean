import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewAdjointCasimirSpectralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimStableSubspaceStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.AnalyticBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Restricts (W : Submodule ℂ (Sm E a)) (T' : Module.End ℂ W) (T : Module.End ℂ (Sm E a)) : Prop :=
  ∀ v : W, ((T' v : W) : Sm E a) = T v

namespace Restricts

variable {W : Submodule ℂ (Sm E a)} {A' B' : Module.End ℂ W} {A B : Module.End ℂ (Sm E a)}

/- English proof (translation)
Introduce `v` and use `by simp only [Module.End.mul_apply] rw [hA, hB]`.
-/
theorem mul (hA : Restricts W A' A) (hB : Restricts W B' B) : Restricts W (A' * B') (A * B) := fun v => by
  simp only [Module.End.mul_apply]
  rw [hA, hB]

/- English proof (translation)
Introduce `v` and use `by simp only [LinearMap.sub_apply, Submodule.coe_sub] rw [hA, hB]`.
-/
theorem sub (hA : Restricts W A' A) (hB : Restricts W B' B) : Restricts W (A' - B') (A - B) := fun v => by
  simp only [LinearMap.sub_apply, Submodule.coe_sub]
  rw [hA, hB]

/- English proof (translation)
Introduce `v` and use `by simp only [LinearMap.smul_apply, Submodule.coe_smul] rw [hA]`.
-/
theorem smul (c : ℂ) (hA : Restricts W A' A) : Restricts W (c • A') (c • A) := fun v => by
  simp only [LinearMap.smul_apply, Submodule.coe_smul]
  rw [hA]

/- English proof (translation)
Introduce `_` and use `rfl`.
-/
theorem one : Restricts W (1 : Module.End ℂ W) (1 : Module.End ℂ (Sm E a)) := fun _ => rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using one`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul hA`.
-/
theorem pow (hA : Restricts W A' A) (k : ℕ) : Restricts W (A' ^ k) (A ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hA

/- English proof (translation)
Introduce `v` and use `by simp only [LinearMap.sum_apply, Submodule.coe_sum] exact Finset.sum_congr rfl fun i _ => h i v`.
-/
theorem sum {ι : Type} (s : Finset ι) {f' : ι → Module.End ℂ W} {f : ι → Module.End ℂ (Sm E a)}
    (h : ∀ i, Restricts W (f' i) (f i)) : Restricts W (∑ i ∈ s, f' i) (∑ i ∈ s, f i) := fun v => by
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun i _ => h i v

/- English proof (translation)
The claim follows from `LinearMap.ext fun v => Subtype.ext (by rw [hA, hB, e])`.
-/
theorem ext_of_eq (hA : Restricts W A' A) (hB : Restricts W B' B) (e : A = B) : A' = B' :=
  LinearMap.ext fun v => Subtype.ext (by rw [hA, hB, e])

end Restricts

/- English proof (translation)
Use extensionality with `φ g`. Simplify using `[Complex.real_smul]`.
-/
theorem real_smul_end (r : ℝ) (T : Module.End ℂ (Sm E a)) : r • T = (r : ℂ) • T := by
  ext φ g
  simp [Complex.real_smul]

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [map_smul, real_smul_end]`.
-/
theorem lie_sum {ι : Type} [Fintype ι] (Z : ι → GlobalTheory.CuspRep.Lie E a) (r : ι → ℝ) :
    lie E a (∑ l, r l • Z l) = ∑ l, (r l : ℂ) • lie E a (Z l) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, real_smul_end]

/- English proof (translation)
Use `⟨fun e f => b.repr ⟨T (b e).1, hT _ (b e).2⟩ f, fun e => Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hI]`. Establish `h` using `congrArg (Subtype.val) (b.sum_repr ⟨T (b e).1, hT _ (b e).2⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h ⊢`. Conclude with `h.symm`.
-/
theorem exists_coords {W Y : Submodule ℂ (Sm E a)} (hYW : Y ≤ W) {m : ℕ} (b : Module.Basis (Fin m) ℂ Y)
    {T' : Module.End ℂ W} {T : Module.End ℂ (Sm E a)} (hI : Restricts W T' T) (hT : ∀ u ∈ Y, T u ∈ Y) :
    ∃ d : Fin m → Fin m → ℂ, ∀ e, T' ⟨(b e).1, hYW (b e).2⟩ = ∑ f, d e f • (⟨(b f).1, hYW (b f).2⟩ : W) := by
  refine ⟨fun e f => b.repr ⟨T (b e).1, hT _ (b e).2⟩ f, fun e => Subtype.ext ?_⟩
  rw [hI]
  have h := congrArg (Subtype.val) (b.sum_repr ⟨T (b e).1, hT _ (b e).2⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h ⊢
  exact h.symm

/- English proof (translation)
Establish `h` using `congrArg (Subtype.val) (b.sum_repr ⟨φ, hφ⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Establish `e : (⟨φ, hYW hφ⟩ : W) = ∑ f, b.repr ⟨φ, hφ⟩ f • (⟨(b f).1, hYW (b f).2⟩ : W)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`.

Conclude with `h.symm`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)`.
-/
theorem mem_span_basis {W Y : Submodule ℂ (Sm E a)} (hYW : Y ≤ W) {m : ℕ} (b : Module.Basis (Fin m) ℂ Y)
    {φ : Sm E a} (hφ : φ ∈ Y) :
    (⟨φ, hYW hφ⟩ : W) ∈ Submodule.span ℂ (Set.range fun e => (⟨(b e).1, hYW (b e).2⟩ : W)) := by
  have h := congrArg (Subtype.val) (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  have e : (⟨φ, hYW hφ⟩ : W) = ∑ f, b.repr ⟨φ, hφ⟩ f • (⟨(b f).1, hYW (b f).2⟩ : W) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact h.symm
  rw [e]
  exact Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

/- English proof (translation)
Introduce `E _ _ _ a μ _ _ W hW hA φ hφ X`. Take `⟨ι, _, _, Z, K, hspan, hskewK, hΩ⟩` from `GlobalTheory.T.casimir_signature_mem_center E a`. Establish `hL : ∀ (X : GlobalTheory.CuspRep.Lie E a), ∀ ψ ∈ W, lie E a X ψ ∈ W` using `fun X ψ h => hW (.lie X) ψ h`. Establish `hm : ∀ ψ ∈ W, MemL2Quotient (latticeGL E a) μ ψ.1` using `fun ψ h => (hA ψ h).2`. Establish `hc : ∀ ψ ∈ W, Continuous ψ.1` using `fun ψ h => ContAut.continuous_of_isOpen_stab E a ψ (hA ψ h).1.level`.

Establish `hreal : ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ r : ι → ℝ, ∑ l, r l • Z l = X` using `fun X => by`. Establish `hX : X ∈ Submodule.span ℝ (Set.range Z)` using `by rw [hspan]; trivial`. Conclude with `(Submodule.mem_span_range_iff_exists_fun ℝ).1 hX`. Set `Zop : ι → Module.End ℂ W` to `fun i => (lie E a (Z i)).restrict (hL (Z i))`. Establish `hZ : ∀ i, Restricts W (Zop i) (lie E a (Z i))` using `fun i v => rfl`.

Set `j` to `toL2ₗ μ W hm`. Establish `hskew : ∀ i v w, inner ℂ (j (Zop i v)) (j w) = - inner ℂ (j v) (j (Zop i w))` using `fun i v w => GlobalTheory.T.lie_skew_adjoint_l2 E a μ (Z i) v.1 w.1 (hm _ v.2) (hm _ w.2) (hm _ (hL _ _ v.2)) (hm _ (hL _ _ w.2)) (hc _ v.2) (hc _ w.2) (hc _ (hL _ _ v.2)) (hc _ (hL _ _ w.2))`. Use `choose r hr using fun (p : ι × ι) => hreal (toL (of (Z p.1) * of (Z p.2)) - toL (of (Z p.2) * of (Z p.1)))`. Establish `hcomm : ∀ κ i, Zop κ * Zop i - Zop i * Zop κ = ∑ l, ((r (κ, i) l : ℝ) : ℂ) • Zop l` using `fun κ i => by`. Use `Restricts.ext_of_eq (((hZ κ).mul (hZ i)).sub ((hZ i).mul (hZ κ))) (Restricts.sum _ fun l => (hZ l).smul _) ?_` and prove the remaining obligations.

Rewrite using `[lie_comm, ← map_sub, ← hr (κ, i), lie_sum]`. Use `set Ω₀ : Module.End ℂ (Sm E a) := ∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hΩ₀`. Use `set S₀ : Module.End ℂ (Sm E a) := ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hS₀`. Establish `hSI : Restricts W (∑ κ ∈ K, Zop κ * Zop κ) S₀` using `Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)`. Establish `hΩI : Restricts W (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) Ω₀` using `(Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)).sub hSI`.

Establish `hcentral : ∀ i, (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) * Zop i = Zop i * (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ)` using `fun i => Restricts.ext_of_eq (hΩI.mul (hZ i)) ((hZ i).mul hΩI) (GlobalTheory.T.center_commutes_lie_action E a Ω₀ hΩ (Z i))`. Take `⟨Y, hfd, hYW, hφY, hZY, hKY⟩` from `GlobalTheory.T.finite_dim_stable_subspace E a W hW (fun ψ h => (hA ψ h).1) φ hφ`. Set `b` to `Module.finBasis ℂ Y`. Establish `hSY : ∀ u ∈ Y, S₀ u ∈ Y` using `fun u hu => by`. Rewrite using `[hS₀, LinearMap.sum_apply]`.

Conclude with `Submodule.sum_mem _ fun κ hκ => hKY _ (hskewK κ hκ) _ (hKY _ (hskewK κ hκ) _ hu)`. Establish `hΩY : ∀ u ∈ Y, Ω₀ u ∈ Y` using `fun u hu => hZY _ hΩ _ hu`. Take `⟨d, hd⟩` from `exists_coords hYW b hSI hSY`. Take `⟨o, ho⟩` from `exists_coords hYW b hΩI hΩY`. Take `⟨x, hx⟩` from `hreal X`.

Establish `hT : Restricts W (∑ i, ((x i : ℝ) : ℂ) • Zop i) (lie E a X)`. Rewrite using `[← hx, lie_sum]`. Conclude with `Restricts.sum _ fun l => (hZ l).smul _`. Take `⟨M, C, hMC⟩` from `GlobalTheory.T.skew_adjoint_casimir_spectral W (L2 (latticeGL E a) μ) j ι Zop K _ (fun e => (⟨(b e).1, hYW (b e).2⟩ : W)) d o (fun κ i l => ((r (κ, i) l : ℝ) : ℂ)) hskew hcomm hcentral hd ho (fun i => (x i : ℂ)) ⟨φ, hφ⟩ (mem_span_basis hYW b hφY)`. Use `⟨M, C, fun k h => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ (w : W) (f : Sm E a) (_ : w.1 = f) (h : MemL2Quotient (latticeGL E a) μ f.1), j w = h.toL2`. Introduce and unpack `⟨w, hw⟩ f rfl h`. Both sides reduce to the same expression. Rewrite using `[← key _ _ ((hT.pow k) ⟨φ, hφ⟩) h]`. Conclude with `hMC k`.
-/
theorem factorial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E a)), IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) → ∀ φ ∈ W, ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ M C : ℝ, ∀ (k : ℕ) (h : MemL2Quotient (latticeGL E a) μ (((lie E a X) ^ k) φ).1), ‖h.toL2‖ ≤ M * C ^ k * (k.factorial : ℝ) := by
  intro E _ _ _ a μ _ _ W hW hA φ hφ X
  obtain ⟨ι, _, _, Z, K, hspan, hskewK, hΩ⟩ := GlobalTheory.T.casimir_signature_mem_center E a
  have hL : ∀ (X : GlobalTheory.CuspRep.Lie E a), ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ h => hW (.lie X) ψ h
  have hm : ∀ ψ ∈ W, MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ h => (hA ψ h).2
  have hc : ∀ ψ ∈ W, Continuous ψ.1 := fun ψ h =>
    ContAut.continuous_of_isOpen_stab E a ψ (hA ψ h).1.level
  have hreal : ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ r : ι → ℝ, ∑ l, r l • Z l = X := fun X => by
    have hX : X ∈ Submodule.span ℝ (Set.range Z) := by rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  let Zop : ι → Module.End ℂ W := fun i => (lie E a (Z i)).restrict (hL (Z i))
  have hZ : ∀ i, Restricts W (Zop i) (lie E a (Z i)) := fun i v => rfl
  let j := toL2ₗ μ W hm
  have hskew : ∀ i v w, inner ℂ (j (Zop i v)) (j w) = - inner ℂ (j v) (j (Zop i w)) := fun i v w =>
    GlobalTheory.T.lie_skew_adjoint_l2 E a μ (Z i) v.1 w.1 (hm _ v.2) (hm _ w.2) (hm _ (hL _ _ v.2)) (hm _ (hL _ _ w.2))
      (hc _ v.2) (hc _ w.2) (hc _ (hL _ _ v.2)) (hc _ (hL _ _ w.2))
  choose r hr using fun (p : ι × ι) => hreal (toL (of (Z p.1) * of (Z p.2)) - toL (of (Z p.2) * of (Z p.1)))
  have hcomm : ∀ κ i, Zop κ * Zop i - Zop i * Zop κ = ∑ l, ((r (κ, i) l : ℝ) : ℂ) • Zop l := fun κ i => by
    refine Restricts.ext_of_eq (((hZ κ).mul (hZ i)).sub ((hZ i).mul (hZ κ)))
      (Restricts.sum _ fun l => (hZ l).smul _) ?_
    rw [lie_comm, ← map_sub, ← hr (κ, i), lie_sum]
  set Ω₀ : Module.End ℂ (Sm E a) :=
    ∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hΩ₀
  set S₀ : Module.End ℂ (Sm E a) := ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hS₀
  have hSI : Restricts W (∑ κ ∈ K, Zop κ * Zop κ) S₀ := Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)
  have hΩI : Restricts W (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) Ω₀ :=
    (Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)).sub hSI
  have hcentral : ∀ i, (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) * Zop i
      = Zop i * (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) := fun i =>
    Restricts.ext_of_eq (hΩI.mul (hZ i)) ((hZ i).mul hΩI) (GlobalTheory.T.center_commutes_lie_action E a Ω₀ hΩ (Z i))
  obtain ⟨Y, hfd, hYW, hφY, hZY, hKY⟩ := GlobalTheory.T.finite_dim_stable_subspace E a W hW (fun ψ h => (hA ψ h).1) φ hφ
  let b := Module.finBasis ℂ Y
  have hSY : ∀ u ∈ Y, S₀ u ∈ Y := fun u hu => by
    rw [hS₀, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun κ hκ => hKY _ (hskewK κ hκ) _ (hKY _ (hskewK κ hκ) _ hu)
  have hΩY : ∀ u ∈ Y, Ω₀ u ∈ Y := fun u hu => hZY _ hΩ _ hu
  obtain ⟨d, hd⟩ := exists_coords hYW b hSI hSY
  obtain ⟨o, ho⟩ := exists_coords hYW b hΩI hΩY
  obtain ⟨x, hx⟩ := hreal X
  have hT : Restricts W (∑ i, ((x i : ℝ) : ℂ) • Zop i) (lie E a X) := by
    rw [← hx, lie_sum]
    exact Restricts.sum _ fun l => (hZ l).smul _
  obtain ⟨M, C, hMC⟩ := GlobalTheory.T.skew_adjoint_casimir_spectral W (L2 (latticeGL E a) μ) j ι Zop K _
    (fun e => (⟨(b e).1, hYW (b e).2⟩ : W)) d o (fun κ i l => ((r (κ, i) l : ℝ) : ℂ))
    hskew hcomm hcentral hd ho (fun i => (x i : ℂ)) ⟨φ, hφ⟩ (mem_span_basis hYW b hφY)
  refine ⟨M, C, fun k h => ?_⟩
  have key : ∀ (w : W) (f : Sm E a) (_ : w.1 = f) (h : MemL2Quotient (latticeGL E a) μ f.1), j w = h.toL2 := by
    rintro ⟨w, hw⟩ f rfl h
    rfl
  rw [← key _ _ ((hT.pow k) ⟨φ, hφ⟩) h]
  exact hMC k

end GlobalTheory.CompanionTheory.AnalyticBound
