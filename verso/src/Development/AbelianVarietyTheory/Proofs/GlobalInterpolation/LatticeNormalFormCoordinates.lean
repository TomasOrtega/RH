import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.lattice_normal_form_coordinates

open GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

variable {F : Type} [Field F] {n c : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `l`. Unfold `Loc.eN`. Use `l.2` as an intermediate fact. Rewrite using `[if_neg (by omega)]`. Both sides reduce to the same expression.
-/
theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN F N i = 0 := by
  funext l
  unfold Loc.eN
  have := l.2
  rw [if_neg (by omega)]
  rfl

/- English proof (translation)
Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Loc.eN, smul_eq_mul]`. Use `split_ifs with h`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega), mul_zero]`. Rewrite using `[Finset.sum_eq_single ⟨l.1 - n, by omega⟩]`.

Rewrite using `[if_pos (by simp; omega), mul_one]`. Introduce `b _ hb`. Rewrite using `[if_neg, mul_zero]`. Introduce `hl`. Conclude with `hb (Fin.ext (by simp; omega))`.

Simplify using the standard rewrite rules.
-/
theorem sum_eN_apply (g : Fin c → F) (l : Fin (n + c)) :
    (∑ i : Fin c, g i • Loc.eN F (n + c) (n + i.1)) l = if h : l.1 < n then 0 else g ⟨l.1 - n, by omega⟩ := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Loc.eN, smul_eq_mul]
  split_ifs with h
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega), mul_zero]
  · rw [Finset.sum_eq_single ⟨l.1 - n, by omega⟩]
    · rw [if_pos (by simp; omega), mul_one]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hl
      exact hb (Fin.ext (by simp; omega))
    · simp

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[Pi.add_apply, inX_apply, sum_eN_apply]`. Use `split_ifs with h`. Rewrite using `[add_zero]`. Both sides reduce to the same expression.

Rewrite using `[zero_add]`. Use `congr 1`. Conclude with `Fin.ext (by simp; omega)`.
-/
theorem decomp (v : Fin (n + c) → F) :
    v = Loc.inX F n c (fun a => v (Fin.castAdd c a)) +
      ∑ i : Fin c, v (Fin.natAdd n i) • Loc.eN F (n + c) (n + i.1) := by
  funext l
  rw [Pi.add_apply, inX_apply, sum_eN_apply]
  split_ifs with h
  · rw [add_zero]
    rfl
  · rw [zero_add]
    congr 1
    exact Fin.ext (by simp; omega)

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `congrFun hg (Fin.natAdd n i)` as an intermediate fact. Rewrite `this` using `[sum_eN_apply, dif_neg (by simp)]`.

Simplify using `using this`. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `_ ⟨x, rfl⟩ hv`. Take `⟨g, hg⟩` from `(Submodule.mem_span_range_iff_exists_fun F).1 hv`. Use function extensionality and compare the values at `l`.

Establish `h1` using `congrFun hg l`. Rewrite `h1` using `[sum_eN_apply]`. Distinguish the cases in `h : l.1 < n`. Rewrite `h1` using `[dif_pos h]`. Conclude with `h1.symm`.

Rewrite using `[inX_apply, dif_neg h]`. Both sides reduce to the same expression. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Rewrite using `[decomp v]`.

Conclude with `Submodule.add_mem_sup ⟨_, rfl⟩ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`.
-/
theorem isFrame : IsFrame (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg (Fin.natAdd n i)
    rw [sum_eN_apply, dif_neg (by simp)] at this
    simpa using this
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    funext l
    have h1 := congrFun hg l
    rw [sum_eN_apply] at h1
    by_cases h : l.1 < n
    · rw [dif_pos h] at h1
      exact h1.symm
    · rw [inX_apply, dif_neg h]
      rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [decomp v]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/- English proof (translation)
Use `sup_le ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `inX_mem_Ufl _ x`. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Establish `: l.1 < i.1` using `hl`.

Conclude with `eN_mem_Ufl (by omega)`.
-/
theorem flag_le (i : Fin c) :
    flag (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) i ≤ Loc.Ufl F n c i.1 := by
  refine sup_le ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    exact inX_mem_Ufl _ x
  · rintro _ ⟨l, hl, rfl⟩
    have : l.1 < i.1 := hl
    exact eN_mem_Ufl (by omega)

/- English proof (translation)
Use `⟨fun i v hv => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[decomp v, map_add, map_sum]`. Use `add_mem (Ufl_mono (Nat.zero_le i) (h1 _)) (Submodule.sum_mem _ fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j.1 < i`. Rewrite using `[map_smul]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `add_mem (Ufl_mono hj.le (h3 j)) (eN_mem_Ufl (F := F) (n := n) (c := c) (i := i) (s := n + j.1) (by omega))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite using `[mem_Ufl.1 hv (Fin.natAdd n j) (by simp; omega), zero_smul, map_zero]`. Conclude with `zero_mem _`.

Break down `Nat.eq_zero_or_pos c with hc | hc` into its components or cases. Rewrite using `[eN_eq_zero (by omega), map_zero]`. Conclude with `h2 ⟨0, hc⟩ rfl`. Distinguish the cases in `hi : i < c`. Conclude with `h3 ⟨i, hi⟩`.

Rewrite using `[eN_eq_zero (by omega), map_zero, sub_zero]`. Conclude with `zero_mem _`.
-/
theorem R1cond_of {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ x, r (Loc.inX F n c x) ∈ Loc.Ufl F n c 0)
    (h2 : ∀ i : Fin c, i.1 = 0 → r (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1))
    (h3 : ∀ i : Fin c, r (Loc.eN F (n + c) (n + i.1)) - Loc.eN F (n + c) (n + i.1) ∈ Loc.Ufl F n c i.1) :
    Loc.R1cond F n c r := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [decomp v, map_add, map_sum]
    refine add_mem (Ufl_mono (Nat.zero_le i) (h1 _)) (Submodule.sum_mem _ fun j _ => ?_)
    by_cases hj : j.1 < i
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := add_mem (Ufl_mono hj.le (h3 j)) (eN_mem_Ufl (F := F) (n := n) (c := c) (i := i) (s := n + j.1) (by omega))
      rwa [sub_add_cancel] at this
    · rw [mem_Ufl.1 hv (Fin.natAdd n j) (by simp; omega), zero_smul, map_zero]
      exact zero_mem _
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [eN_eq_zero (by omega), map_zero]
    · exact h2 ⟨0, hc⟩ rfl
  · by_cases hi : i < c
    · exact h3 ⟨i, hi⟩
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

/- English proof (translation)
Establish `key : ∀ i, ∀ v ∈ Loc.Ufl F n c i, r⁻¹ v ∈ Loc.Ufl F n c i`. Introduce `i v hv`. Establish `hle : (Loc.Ufl F n c i).map r.toLinearMap ≤ Loc.Ufl F n c i`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `hr.1 i w hw`.

Establish `heq` using `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)`. Rewrite `hv` using `[← heq]`. Take `⟨w, hw, rfl⟩` from `hv`. Establish `: r⁻¹ (r.toLinearMap w) = w` using `r.symm_apply_apply w`. Rewrite using `[this]` and apply the resulting hypothesis.

Use `⟨key, ?_, fun i => ?_⟩` and prove the remaining obligations. Use `show r.symm _ = _`. Rewrite using `[LinearEquiv.symm_apply_eq, hr.2.1]`. Establish `h` using `neg_mem (key i _ (hr.2.2 i))`. Establish `e : r⁻¹ (r (Loc.eN F (n + c) (n + i))) = Loc.eN F (n + c) (n + i)` using `r.symm_apply_apply _`.

Rewrite `h` using `[map_sub, e, neg_sub]`. Then use the resulting hypothesis.
-/
theorem R1cond_inv {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) :
    Loc.R1cond F n c r⁻¹ := by
  have key : ∀ i, ∀ v ∈ Loc.Ufl F n c i, r⁻¹ v ∈ Loc.Ufl F n c i := by
    intro i v hv
    have hle : (Loc.Ufl F n c i).map r.toLinearMap ≤ Loc.Ufl F n c i := by
      rintro _ ⟨w, hw, rfl⟩
      exact hr.1 i w hw
    have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
    rw [← heq] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have : r⁻¹ (r.toLinearMap w) = w := r.symm_apply_apply w
    rwa [this]
  refine ⟨key, ?_, fun i => ?_⟩
  · show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, hr.2.1]
  · have h := neg_mem (key i _ (hr.2.2 i))
    have e : r⁻¹ (r (Loc.eN F (n + c) (n + i))) = Loc.eN F (n + c) (n + i) := r.symm_apply_apply _
    rwa [map_sub, e, neg_sub] at h

/- English proof (translation)
Take `⟨γ, g, u, hg, hu, rfl⟩` from `hr`. Establish `h1 : Loc.R1cond F n c g`. Use `R1cond_of (fun x => ?_) (fun i _ => hg.2 i) (fun i => ?_)` and prove the remaining obligations. Use `hg.1 ⟨Loc.inX F n c x, x, rfl⟩` as an intermediate fact. Take `⟨y, hy⟩` from `(γ ⟨Loc.inX F n c x, x, rfl⟩).2`.

Rewrite using `[show g (Loc.inX F n c x) = Loc.inX F n c y from this.trans hy.symm]`. Conclude with `inX_mem_Ufl 0 y`. Rewrite using `[show g (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1) from hg.2 i, sub_self]`. Conclude with `zero_mem _`. Establish `h2 : Loc.R1cond F n c u`.

Use `R1cond_of (fun x => ?_) hu.2.1 (fun i => flag_le i (hu.2.2 i))` and prove the remaining obligations. Rewrite using `[hu.1 _ ⟨x, rfl⟩]`. Conclude with `inX_mem_Ufl 0 x`. Conclude with `⟨h1.mul h2, R1cond_inv (h1.mul h2)⟩`.
-/
theorem mem_unipotentRadical_of_isSemidirect {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : IsSemidirect (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) r) :
    r ∈ Loc.R1 F n c := by
  obtain ⟨γ, g, u, hg, hu, rfl⟩ := hr
  have h1 : Loc.R1cond F n c g := by
    refine R1cond_of (fun x => ?_) (fun i _ => hg.2 i) (fun i => ?_)
    · have := hg.1 ⟨Loc.inX F n c x, x, rfl⟩
      obtain ⟨y, hy⟩ := (γ ⟨Loc.inX F n c x, x, rfl⟩).2
      rw [show g (Loc.inX F n c x) = Loc.inX F n c y from this.trans hy.symm]
      exact inX_mem_Ufl 0 y
    · rw [show g (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1) from hg.2 i, sub_self]
      exact zero_mem _
  have h2 : Loc.R1cond F n c u := by
    refine R1cond_of (fun x => ?_) hu.2.1 (fun i => flag_le i (hu.2.2 i))
    rw [hu.1 _ ⟨x, rfl⟩]
    exact inX_mem_Ufl 0 x
  exact ⟨h1.mul h2, R1cond_inv (h1.mul h2)⟩

/- English proof (translation)
Use `⟨hL.fg.map _, ?_⟩` and prove the remaining obligations. Establish `h : ((L.map (φ.toLinearMap.restrictScalars O) : Submodule O W) : Set W) = φ.toLinearMap '' (L : Set V)` using `rfl`. Rewrite using `[h, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem isLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type} [AddCommGroup V] [Module F V] [Module O V]
    [IsScalarTower O F V] [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W] (φ : V ≃ₗ[F] W)
    (L : Submodule O V) (hL : Submodule.IsLattice F L) :
    Submodule.IsLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h : ((L.map (φ.toLinearMap.restrictScalars O) : Submodule O W) : Set W) = φ.toLinearMap '' (L : Set V) := rfl
  rw [h, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Introduce `H O F _ _ _ _ _ _ q hq n c L hL Λ hΛ`. Set `φ` to `LinearEquiv.ofInjective (Loc.inX F n c) inX_injective`. Take `⟨r, e, z, hr, ⟨z', rfl⟩, h⟩` from `H O F (Fin (n + c) → F) q hq c _ _ isFrame _ (isLattice_map φ L hL) Λ hΛ`. Use `⟨r, mem_unipotentRadical_of_isSemidirect hr, e, z', ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Use `congr 1`. Unfold `inY`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem latticeNormalFormCoord_of : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm → GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord := by
  intro H O F _ _ _ _ _ _ q hq n c L hL Λ hΛ
  let φ := LinearEquiv.ofInjective (Loc.inX F n c) inX_injective
  obtain ⟨r, e, z, hr, ⟨z', rfl⟩, h⟩ := H O F (Fin (n + c) → F) q hq c _ _ isFrame _ (isLattice_map φ L hL) Λ hΛ
  refine ⟨r, mem_unipotentRadical_of_isSemidirect hr, e, z', ?_⟩
  rw [h]
  congr 1
  unfold inY
  rw [← Submodule.map_comp]
  rfl

end GlobalTheory.Proof.lattice_normal_form_coordinates
