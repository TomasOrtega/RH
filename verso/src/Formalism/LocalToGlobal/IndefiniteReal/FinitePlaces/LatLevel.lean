import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InvForm
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem

set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Set `U : X → Set X` to `fun y => (fun x => x - y) ⁻¹' (H : Set X)`. Establish `hU : ∀ y, IsOpen (U y)` using `fun y => hH.preimage (continuous_id.sub continuous_const)`. Establish `hcov : K ⊆ ⋃ y ∈ K, U y` using `fun x hx => Set.mem_biUnion hx (by simp [U, H.zero_mem])`. Take `⟨t, -, htf, hcov'⟩` from `hK.elim_finite_subcover_image (fun y _ => hU y) hcov`. Take `⟨t', rfl⟩ : ∃ t' : Finset X, (t' : Set X) = t` from `⟨htf.toFinset, by simp⟩`.

Use `⟨t'.card.factorial, Nat.factorial_pos _, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hmaps : ∀ j ∈ Finset.range (t'.card + 1), ∃ i ∈ t', j • y ∈ U i` using `fun j _ => by`. Use `hcov' (hKs y hy j)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨i, hi, hji⟩` from `this`.

Conclude with `⟨i, by simpa using hi, hji⟩`. Use `choose! f hf using hmaps`. Take `⟨j1, hj1, j2, hj2, hne, heq⟩` from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (t'.card + 1)) (t := t') (by simp) (f := f) (fun j hj => (hf j hj).1)`. Establish `h1` using `(hf j1 hj1).2`. Establish `h2` using `(hf j2 hj2).2`.

Rewrite `h1` using `[heq]`. Establish `hdiff : ((j1 : ℤ) - j2) • y ∈ H`. Use `H.sub_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Use `show _ = (j1 • y - f j2) - (j2 • y - f j2)`. Rewrite using `[sub_zsmul, natCast_zsmul, natCast_zsmul]`.

Normalize the expressions using the abelian group laws. Establish `hj1' : j1 ≤ t'.card` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj1)`. Establish `hj2' : j2 ≤ t'.card` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj2)`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Establish `hk : ((j2 - j1 : ℕ) : ℤ) • y ∈ H`.

Use `H.neg_mem hdiff` as an intermediate fact. Rewrite `this` using `[← neg_zsmul, neg_sub]`. Rewrite using `[Nat.cast_sub hlt.le]` and apply the resulting hypothesis. Rewrite `hk` using `[natCast_zsmul]`. Take `⟨c, hc⟩` from `Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj2')`.

Rewrite using `[hc, mul_comm, ← smul_smul]`. Conclude with `H.nsmul_mem hk c`. Establish `hk : ((j1 - j2 : ℕ) : ℤ) • y ∈ H` using `by rwa [Nat.cast_sub hlt.le]`. Rewrite `hk` using `[natCast_zsmul]`. Take `⟨c, hc⟩` from `Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj1')`.

Rewrite using `[hc, mul_comm, ← smul_smul]`. Conclude with `H.nsmul_mem hk c`.
-/
theorem exists_nsmul_mem_cpt' {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  let U : X → Set X := fun y => (fun x => x - y) ⁻¹' (H : Set X)
  have hU : ∀ y, IsOpen (U y) := fun y => hH.preimage (continuous_id.sub continuous_const)
  have hcov : K ⊆ ⋃ y ∈ K, U y := fun x hx => Set.mem_biUnion hx (by simp [U, H.zero_mem])
  obtain ⟨t, -, htf, hcov'⟩ := hK.elim_finite_subcover_image (fun y _ => hU y) hcov
  obtain ⟨t', rfl⟩ : ∃ t' : Finset X, (t' : Set X) = t := ⟨htf.toFinset, by simp⟩
  refine ⟨t'.card.factorial, Nat.factorial_pos _, fun y hy => ?_⟩
  have hmaps : ∀ j ∈ Finset.range (t'.card + 1), ∃ i ∈ t', j • y ∈ U i := fun j _ => by
    have := hcov' (hKs y hy j)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hji⟩ := this
    exact ⟨i, by simpa using hi, hji⟩
  choose! f hf using hmaps
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t'.card + 1)) (t := t') (by simp) (f := f) (fun j hj => (hf j hj).1)
  have h1 := (hf j1 hj1).2
  have h2 := (hf j2 hj2).2
  rw [heq] at h1
  have hdiff : ((j1 : ℤ) - j2) • y ∈ H := by
    convert H.sub_mem h1 h2 using 1
    show _ = (j1 • y - f j2) - (j2 • y - f j2)
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
    abel
  have hj1' : j1 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj1)
  have hj2' : j2 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj2)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : ((j2 - j1 : ℕ) : ℤ) • y ∈ H := by
      have := H.neg_mem hdiff
      rw [← neg_zsmul, neg_sub] at this
      rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj2')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c
  · have hk : ((j1 - j2 : ℕ) : ℤ) • y ∈ H := by rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj1')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c

def LatLevel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      ∃ k : ℕ, 0 < k ∧ ∀ u ∈ latAll S T ΛS ΛT, heisO ψ S T (k • u) f = f

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨α, -, -, a, -, s, -, t, -, rfl⟩` from `hx`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]`.

Use `show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0`. Rewrite using `[show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]`. Consider the case `zero => ext i j`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Use extensionality with `i j`. Establish `h1 : infPart D (x i j) = 0` using `congrFun (congrFun hx i) j`. Establish `h2 : infPart D (y i j) = 0` using `congrFun (congrFun hy i) j`. Use `show infPart D (x i j + y i j) = 0`. Rewrite using `[(infPart D).map_add, h1, h2, add_zero]`.

Consider the case `neg x _ hx`. Use extensionality with `i j`. Establish `h1 : infPart D (x i j) = 0` using `congrFun (congrFun hx i) j`. Use `show infPart D (-x i j) = 0`. Rewrite using `[(infPart D).map_neg, h1, neg_zero]`.
-/
theorem latAll_inf (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {u : WO S T} (hu : u ∈ latAll S T ΛS ΛT) :
    u.map (infPart D) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hx
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | zero => ext i j; simp
  | add x y _ _ hx hy =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [(infPart D).map_add, h1, h2, add_zero]
  | neg x _ hx =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [(infPart D).map_neg, h1, neg_zero]

/- English proof (translation)
Introduce `ψ hψ S T ΛS ΛT hS hT f hf`. Take `⟨U, hUo, hU⟩` from `hf.level`. Take `⟨hcpt, -, -, -⟩` from `hL ψ hψ S T ΛS ΛT hS hT`. Take `⟨m, hm, hmU⟩` from `exists_nsmul_mem_cpt' _ hcpt (fun y hy n => AddSubgroup.nsmul_mem _ hy n) U hUo`. Use `⟨m, hm, fun u hu => hU _ (hmU u hu) ?_⟩` and prove the remaining obligations.

Establish `h0` using `latAll_inf S T ΛS ΛT hu`. Use extensionality with `i j`. Establish `h1 : infPart D (u i j) = 0` using `congrFun (congrFun h0 i) j`. Use `show infPart D ((m • u) i j) = 0`. Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h1, mul_zero]`.
-/
theorem latLevel_of (hL : LatSelfDual D) : LatLevel D := by
  intro ψ hψ S T ΛS ΛT hS hT f hf
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨hcpt, -, -, -⟩ := hL ψ hψ S T ΛS ΛT hS hT
  obtain ⟨m, hm, hmU⟩ := exists_nsmul_mem_cpt' _ hcpt (fun y hy n => AddSubgroup.nsmul_mem _ hy n) U hUo
  refine ⟨m, hm, fun u hu => hU _ (hmU u hu) ?_⟩
  have h0 := latAll_inf S T ΛS ΛT hu
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun h0 i) j
  show infPart D ((m • u) i j) = 0
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h1, mul_zero]

end Formalism.IndefR.Fin

end
