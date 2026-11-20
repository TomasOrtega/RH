import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.EigenSpanSat

def eigenSub {K : Type} [Field K] {n : ℕ} {O : Type} (r : O → Matrix (Fin n) (Fin n) K)
    (τ : O → K) : Submodule K (Fin n → K) where
  carrier := {c | ∀ a, (r a).mulVec c = τ a • c}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx a, hy a, smul_add]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx a, smul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem map_mulVec {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    (M.map iK).mulVec (fun i => iK (c i)) = fun i => iK (M.mulVec c i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Set `_ : Algebra K L` to `iK.toAlgebra`. Set `S` to `Submodule.span K (Set.range σ)`. Establish `: FiniteDimensional K S` using `FiniteDimensional.span_of_finite K (Set.finite_range σ)`. Set `b` to `Module.finBasis K S`. Establish `hli : LinearIndependent K (fun k => (b k : L))` using `b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)`.

Set `D : Fin (finrank K S) → Fin m → K` to `fun k i => b.repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩ k`. Establish `hσ : ∀ i, σ i = ∑ k, iK (D k i) * (b k : L)`. Introduce `i`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩)`. Use `h.symm.trans ?_` and prove the remaining obligations.

Rewrite using `[Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `hvan : ∀ v : Fin (finrank K S) → (Fin n → K), (∑ k, (b k : L) • fun t => iK (v k t)) = 0 → ∀ k, v k = 0`.

Introduce `v hv k`. Use function extensionality and compare the values at `t`. Establish `h` using `congrFun hv t`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h`. Use `Fintype.linearIndependent_iff.1 hli (fun k => v k t) (by` as an intermediate fact.

Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Use the proof step `rfl)`. Conclude with `this k`.

Set `u : Fin (finrank K S) → (Fin n → K)` to `fun k => ∑ i, D k i • c i`. Establish `hy : (∑ i, σ i • (fun t => iK (c i t))) = ∑ k, (b k : L) • fun t => iK (u k t)`. Use function extensionality and compare the values at `t`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, map_sum, map_mul, hσ, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hu : ∀ k, u k = 0`. Introduce `k`. Apply `hP` to reduce the goal to its premises.

Introduce `a`. Establish `h1` using `hvan (fun k => (r a).mulVec (u k) - τ a • u k) (by`. Establish `h2` using `he a`. Rewrite `h2` using `[hy, Matrix.mulVec_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]`. Rewrite using `[← h2]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, map_mulVec, smul_comm (iK (τ a)), ← smul_sub]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `[map_sub, map_mul])`.

Conclude with `sub_eq_zero.1 (h1 k)`. Rewrite using `[hy]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hu k]`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_eigen {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ} {O : Type}
    (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) {m : ℕ} (σ : Fin m → L)
    (c : Fin m → (Fin n → K))
    (hP : ∀ d : Fin m → K, (∀ a, (r a).mulVec (∑ i, d i • c i) = τ a • ∑ i, d i • c i) →
      ∑ i, d i • c i = 0)
    (he : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (c i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (c i t)) :
    ∑ i, σ i • (fun t => iK (c i t)) = 0 := by
  let _ : Algebra K L := iK.toAlgebra
  let S := Submodule.span K (Set.range σ)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range σ)
  let b := Module.finBasis K S
  have hli : LinearIndependent K (fun k => (b k : L)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let D : Fin (finrank K S) → Fin m → K :=
    fun k i => b.repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩ k
  have hσ : ∀ i, σ i = ∑ k, iK (D k i) * (b k : L) := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩)
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def]
    rfl

  have hvan : ∀ v : Fin (finrank K S) → (Fin n → K),
      (∑ k, (b k : L) • fun t => iK (v k t)) = 0 → ∀ k, v k = 0 := by
    intro v hv k
    funext t
    have h := congrFun hv t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have := Fintype.linearIndependent_iff.1 hli (fun k => v k t) (by
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl)
    exact this k
  let u : Fin (finrank K S) → (Fin n → K) := fun k => ∑ i, D k i • c i
  have hy : (∑ i, σ i • (fun t => iK (c i t))) = ∑ k, (b k : L) • fun t => iK (u k t) := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, map_sum, map_mul, hσ,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hu : ∀ k, u k = 0 := by
    intro k
    apply hP
    intro a
    have h1 := hvan (fun k => (r a).mulVec (u k) - τ a • u k) (by
      have h2 := he a
      rw [hy, Matrix.mulVec_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, map_mulVec, smul_comm (iK (τ a)), ← smul_sub]
      congr 1
      funext t
      simp [map_sub, map_mul])
    exact sub_eq_zero.1 (h1 k)
  rw [hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hu k]
  funext t
  simp

end GlobalTheory.EigenSpanSat

namespace GlobalTheory.EigenSpanSat

/- English proof (translation)
Introduce `K _ _ n Λ O r τ 𝔓 T iK _ hFG x hx he`. Take `⟨C, -, hdec, hCW⟩` from `Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf Λ hFG (eigenSub r τ)`. Take `⟨m, s, g, hg⟩` from `Submodule.mem_span_set'.1 hx`. Use `choose l hl hlg using fun i => (g i).2`. Use `choose p hp q hq hpq using fun i => hdec (l i) (hl i)`.

Set `σ : Fin m → T.Fr` to `fun i => algebraMap T.V T.Fr (s i)`. Establish `hsplit : x = ∑ i, σ i • (fun t => iK (p i t)) + ∑ i, σ i • (fun t => iK (q i t))`. Rewrite using `[← hg, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hlg i, hpq i, ← smul_add, algebraMap_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Establish `hpE : ∀ i a, (r a).mulVec (p i) = τ a • p i` using `fun i => (hp i).2`. Establish `hx1 : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (p i t)) = iK (τ a) • ∑ i, σ i • fun t => iK (p i t)`.

Introduce `a`. Rewrite using `[Matrix.mulVec_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, map_mulVec, hpE i a, smul_comm]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Establish `hx2 : ∑ i, σ i • (fun t => iK (q i t)) = 0`. Use `eq_zero_of_eigen iK r τ σ q (fun d hd => ?_) (fun a => ?_)` and prove the remaining obligations. Use `hCW _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hq i))) hd` and prove the remaining obligations.

Establish `h` using `he a`. Rewrite `h` using `[hsplit, Matrix.mulVec_add, hx1 a, smul_add]`. Conclude with `add_left_cancel h`. Rewrite using `[hsplit, hx2, add_zero]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨p i, ⟨(hp i).1, (hp i).2⟩, rfl⟩)`.
-/
theorem span_eigen_sat : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  intro K _ _ n Λ O r τ 𝔓 T iK _ hFG x hx he
  obtain ⟨C, -, hdec, hCW⟩ :=
    Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf Λ hFG (eigenSub r τ)
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose l hl hlg using fun i => (g i).2
  choose p hp q hq hpq using fun i => hdec (l i) (hl i)
  let σ : Fin m → T.Fr := fun i => algebraMap T.V T.Fr (s i)
  have hsplit : x = ∑ i, σ i • (fun t => iK (p i t)) + ∑ i, σ i • (fun t => iK (q i t)) := by
    rw [← hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hlg i, hpq i, ← smul_add, algebraMap_smul]
    congr 1
    funext t
    simp
  have hpE : ∀ i a, (r a).mulVec (p i) = τ a • p i := fun i => (hp i).2
  have hx1 : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (p i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (p i t) := by
    intro a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, map_mulVec, hpE i a, smul_comm]
    congr 1
    funext t
    simp
  have hx2 : ∑ i, σ i • (fun t => iK (q i t)) = 0 := by
    refine eq_zero_of_eigen iK r τ σ q (fun d hd => ?_) (fun a => ?_)
    · refine hCW _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hq i))) hd
    · have h := he a
      rw [hsplit, Matrix.mulVec_add, hx1 a, smul_add] at h
      exact add_left_cancel h
  rw [hsplit, hx2, add_zero]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p i, ⟨(hp i).1, (hp i).2⟩, rfl⟩)

end GlobalTheory.EigenSpanSat
