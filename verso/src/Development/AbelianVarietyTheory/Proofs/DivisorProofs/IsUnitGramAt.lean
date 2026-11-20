import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

/- English proof (translation)
Rewrite using `[← M.fr_gram τ]`. Establish `hJ : IsUnit (Formalism.REAL.Jm (M.ε τ))`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.isUnit_diagonal, Pi.isUnit_iff]`. Introduce `i`.

Apply the tactic sequence `split_ifs <;> simp`. Conclude with `(((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ).mul (M.fr_unit τ)`.
-/
theorem isUnit_gramAt (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    split_ifs <;> simp
  exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ).mul (M.fr_unit τ)

/- English proof (translation)
Establish `hu : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h` using `(M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) ha) _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hb)`. Establish `e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹)`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Unfold `DSModel.rep`.

Rewrite using `[e, h]`. Both sides reduce to the same expression.
-/
theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) ha) _
    (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hb)
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  unfold DSModel.rep
  rw [e, h]
  rfl

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simp | k + 1, u, v, e => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc, prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]`.
-/
theorem prod_mul_eq {G : Type} [Monoid G] (h : G) : ∀ (k : ℕ) (u v : Fin k → G), (∀ i, u i * h = h * v i) →
    (List.ofFn u).prod * h = h * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | k + 1, u, v, e => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]

/- English proof (translation)
Establish `hG` using `isUnit_gramAt M τ`. Establish `hgu : IsUnit g.det`. Establish `h1 : IsUnit (gᴴ * gramAt D V τ * g)` using `by rw [show gᴴ * gramAt D V τ * g = _ from hg]; exact hG`. Rewrite `h1` using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h1`.

Establish `hab : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hgu`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem w hw`. Use `Submodule.subset_span fun k Xs hX => ?_` and prove the remaining obligations. Establish `hX' : ∀ i, g⁻¹ * Xs i * g ∈ lieAt V τ` using `fun i => GlobalTheory.Mem.RealTranslate.skew_conj hg hab (hX i)`.

Establish `h1` using `((M.rep τ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => g⁻¹ * Xs i * g) hX')`. Establish `hm : ∀ (Y : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Y i ∈ lieAt V τ) → ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)` using `fun Y hY t => GlobalTheory.GardingVec.list_prod_mem _ fun x hx => by`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `GlobalTheory.GardingVec.exp_mem hG (hY i) (t i)`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Use `show _ = M.rep τ g (M.rep τ _ w)`. Rewrite using `[← rep_mul M τ (hm Xs hX t) hg, ← rep_mul M τ hg (hm _ hX' t), prod_mul_eq g k _ _ fun i => GlobalTheory.Mem.RealTranslate.exp_conj_eq hab (Xs i) (t i)]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {v : M.H τ} (hv : v ∈ M.sm τ) : M.rep τ g v ∈ M.sm τ := by
  have hG := isUnit_gramAt M τ
  have hgu : IsUnit g.det := by
    have h1 : IsUnit (gᴴ * gramAt D V τ * g) := by rw [show gᴴ * gramAt D V τ * g = _ from hg]; exact hG
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hab : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  induction hv using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span fun k Xs hX => ?_
    have hX' : ∀ i, g⁻¹ * Xs i * g ∈ lieAt V τ := fun i => GlobalTheory.Mem.RealTranslate.skew_conj hg hab (hX i)
    have h1 := ((M.rep τ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => g⁻¹ * Xs i * g) hX')
    have hm : ∀ (Y : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Y i ∈ lieAt V τ) → ∀ t : Fin k → ℝ,
        (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun Y hY t =>
      GlobalTheory.GardingVec.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.GardingVec.exp_mem hG (hY i) (t i)
    convert h1 using 1
    funext t
    show _ = M.rep τ g (M.rep τ _ w)
    rw [← rep_mul M τ (hm Xs hX t) hg, ← rep_mul M τ hg (hm _ hX' t),
      prod_mul_eq g k _ _ fun i => GlobalTheory.Mem.RealTranslate.exp_conj_eq hab (Xs i) (t i)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

def IsEqv (M : DSModel V S) (T : MMap M) : Prop :=
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) ∧
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ} {M : DSModel V S}

/- English proof (translation)
Use `⟨fun τ g hg v w e => ?_, fun τ v x => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.smul_apply, h.1 τ g hg v w e]`. Both sides reduce to the same expression. Take `⟨ℓ, h1, h2⟩` from `h.2 τ v x`. Conclude with `⟨c • ℓ, GlobalTheory.MultMem.sobCont_smul c h1, fun w => by rw [LinearMap.smul_apply, h2]; rfl⟩`.
-/
theorem IsEqv.smul {T : MMap M} (h : IsEqv θ M T) (c : ℂ) : IsEqv θ M (c • T) := by
  refine ⟨fun τ g hg v w e => ?_, fun τ v x => ?_⟩
  · rw [_root_.smul_apply, h.1 τ g hg v w e]; rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.2 τ v x
    exact ⟨c • ℓ, GlobalTheory.MultMem.sobCont_smul c h1, fun w => by rw [LinearMap.smul_apply, h2]; rfl⟩

/- English proof (translation)
Use `⟨fun τ g hg v w e => ?_, fun τ v x => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.add_apply, h.1 τ g hg v w e, h'.1 τ g hg v w e]`. Both sides reduce to the same expression. Take `⟨ℓ, h1, h2⟩` from `h.2 τ v x`. Take `⟨ℓ', h1', h2'⟩` from `h'.2 τ v x`.

Conclude with `⟨ℓ + ℓ', GlobalTheory.MultMem.sobCont_add h1 h1', fun w => by rw [LinearMap.add_apply, h2, h2']; rfl⟩`.
-/
theorem IsEqv.add {T T' : MMap M} (h : IsEqv θ M T) (h' : IsEqv θ M T') : IsEqv θ M (T + T') := by
  refine ⟨fun τ g hg v w e => ?_, fun τ v x => ?_⟩
  · rw [_root_.add_apply, h.1 τ g hg v w e, h'.1 τ g hg v w e]; rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.2 τ v x
    obtain ⟨ℓ', h1', h2'⟩ := h'.2 τ v x
    exact ⟨ℓ + ℓ', GlobalTheory.MultMem.sobCont_add h1 h1', fun w => by rw [LinearMap.add_apply, h2, h2']; rfl⟩

def trM (M : DSModel V S) (κ : GA D V) : MMap M →ₗ[ℂ] MMap M := postOn M (GlobalTheory.FinTranslate.rTrL V κ)

def CyclicSmooth : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → ∀ v ∈ M.sm τ, v ≠ 0 → (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0

/- English proof (translation)
Establish `key : ∀ (s : Finset D.what₂.Tau) (w : M.Vec), T (s.piecewise w v) = 0`. Introduce `s w`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h0`. Consider the case `insert τ s hτ ih`.

Use function extensionality and compare the values at `x`. Take `⟨ℓ, h1, h2⟩` from `h.2 τ (s.piecewise w v) x`. Establish `h3` using `hc D V S M τ ℓ h1 (v τ) (v τ).2 (hv τ) (fun g hg => by`. Establish `e` using `h.1 τ g hg (s.piecewise w v) ⟨M.rep τ g (v τ), rep_mem_sm M τ hg (v τ).2⟩ (by rw [Finset.piecewise_eq_of_notMem _ _ _ hτ])`. Use `(h2 ⟨M.rep τ g (v τ), rep_mem_sm M τ hg (v τ).2⟩).trans ?_` and prove the remaining obligations.

Rewrite using `[e, ih]`. Use the proof step `rfl) (w τ) (w τ).2`. Rewrite `h3` using `[h2]`. Rewrite using `[Finset.piecewise_insert]`. Conclude with `h3`.

Use extensionality with `w x`. Use `key Finset.univ w` as an intermediate fact. Rewrite `this` using `[Finset.piecewise_univ]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem IsEqv.eq_zero (hc : CyclicSmooth) {T : MMap M} (h : IsEqv θ M T) {v : M.Vec} (hv : ∀ τ, (v τ : M.H τ) ≠ 0)
    (h0 : T v = 0) : T = 0 := by
  classical
  have key : ∀ (s : Finset D.what₂.Tau) (w : M.Vec), T (s.piecewise w v) = 0 := by
    intro s w
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert τ s hτ ih =>
      funext x
      obtain ⟨ℓ, h1, h2⟩ := h.2 τ (s.piecewise w v) x
      have h3 := hc D V S M τ ℓ h1 (v τ) (v τ).2 (hv τ) (fun g hg => by
        have e := h.1 τ g hg (s.piecewise w v) ⟨M.rep τ g (v τ), rep_mem_sm M τ hg (v τ).2⟩
          (by rw [Finset.piecewise_eq_of_notMem _ _ _ hτ])
        refine (h2 ⟨M.rep τ g (v τ), rep_mem_sm M τ hg (v τ).2⟩).trans ?_
        rw [e, ih]
        rfl) (w τ) (w τ).2
      rw [h2] at h3
      rw [Finset.piecewise_insert]
      exact h3
  ext w x
  have := key Finset.univ w
  rw [Finset.piecewise_univ] at this
  rw [this]
  rfl

/- English proof (translation)
Use `(h.add (h'.smul (-1))).eq_zero hc hv (by simp [h0])` as an intermediate fact. Rewrite `this` using `[neg_one_smul, ← sub_eq_add_neg]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem IsEqv.ext (hc : CyclicSmooth) {T T' : MMap M} (h : IsEqv θ M T) (h' : IsEqv θ M T') {v : M.Vec}
    (hv : ∀ τ, (v τ : M.H τ) ≠ 0) (h0 : T v = T' v) : T = T' := by
  have := (h.add (h'.smul (-1))).eq_zero hc hv (by simp [h0])
  rw [neg_one_smul, ← sub_eq_add_neg] at this
  exact sub_eq_zero.1 this

end GlobalTheory.UnifEvery
