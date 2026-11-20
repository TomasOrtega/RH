import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTransport

open PI.UpqRep CompanionTheory.LimBd.SchurHpk

/- English proof (translation)
Rewrite using `[← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem dot_conj {n : ℕ} (P a Q : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ ((P * a * Q) *ᵥ x) = (u ᵥ* P) ⬝ᵥ (a *ᵥ (Q *ᵥ x)) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring`.
-/
theorem dot_expand {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ (a *ᵥ x) = ∑ p : Fin n × Fin n, u p.1 * x p.2 * a p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

/- English proof (translation)
Take `⟨S, h1, h2, h3⟩` from `hv`. Conclude with `⟨S, h1, S.smul_mem c h2, h3⟩`.
-/
theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {v : H} (c : ℂ)
    (hv : IsKFinHpk (k := k) (r := r) σ v) : IsKFinHpk (k := k) (r := r) σ (c • v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, S.smul_mem c h2, h3⟩

/- English proof (translation)
Establish `hk` using `fun v => CompanionTheory.CapEig.kfin_iff k r ε P U.R.H U.R.σ v hP`. Establish `hds : ∀ s : {s // IsHCParam (ν s)}, IsDSHpk k r ε (ν s) (fun x => σs s (P * x * P⁻¹))` using `fun s => ⟨P, hP, by`. Establish `e : (fun g => (fun x => σs s (P * x * P⁻¹)) (P⁻¹ * g * P)) = σs s` using `funext fun g => by`. Simplify using `only [forth_back hP.1]`. Rewrite using `[e]`.

Conclude with `(ds s ((hSm s).2 s.2)).2⟩`. Use `⟨fun s => ⟨⟨Hs s, fun x => σs s (P * x * P⁻¹)⟩, isURepOn_of_ds (hds s)⟩, fun s => ⟨s.2, hds s⟩, fun v w hv hw c d => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨ι, _, sI, vI, wI, hI, hsum⟩` from `toSum v w (P *ᵥ Pi.single d 1) (star (Pi.single c 1 ᵥ* P⁻¹)) ((hk v).1 hv) ((hk w).1 hw)`. Use `⟨ι, inferInstance, fun i => ⟨sI i, (hSm _).1 (hI i).1⟩, vI, wI, fun g hg => ?_⟩` and prove the remaining obligations. Use `hsum _ (forth_mem hP.1 hg)` as an intermediate fact.

Rewrite `this` using `[back_forth hP.1, hq, star_star, dot_conj, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (q g), inv_mul_P hP.1, Matrix.mul_one, Matrix.vecMul_one, single_one_dotProduct, Matrix.mulVec_single_one]`. Conclude with `this`. Establish `hs` using `(hSm s).2 s.2`. Take `⟨S, hS, hSK, -, ⟨y, hyS, hy0, -⟩, -⟩` from `(ds s hs).2.2.2.2.2.2.1`. Establish `hy : IsKFin ε (σs s) y` using `⟨S, hS, hyS, hSK⟩`.

Take `⟨ι, _, vI, wI, xI, yI, hI, hsum⟩` from `ofSum s hs y y hy hy`. Use `⟨y, hy0, ι × Fin (2 * r + k + 1) × Fin (2 * r + k + 1), inferInstance, fun p => ((star (yI p.1) ᵥ* P) p.2.1 * (P⁻¹ *ᵥ xI p.1) p.2.2) • vI p.1, fun p => wI p.1, fun p => p.2.1, fun p => p.2.2, fun p => ⟨kfin_smul _ ((hk _).2 (hI p.1).1), (hk _).2 (hI p.1).2⟩, fun g hg => ?_⟩` and prove the remaining obligations. Use `hsum _ (forth_mem hP.1 hg)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[back_forth hP.1, hq, dot_conj, dot_expand, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem transport (U : URep k r) {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ g, q (P * g * P⁻¹) = P * q g * P⁻¹)
    (ν : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ)
    (Sm : Finset (Fin (2 * r + k + 1))) (Hs : Fin (2 * r + k + 1) → Type)
    [∀ s, NormedAddCommGroup (Hs s)] [∀ s, InnerProductSpace ℂ (Hs s)] [∀ s, CompleteSpace (Hs s)]
    (σs : ∀ s, Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs s →L[ℂ] Hs s))
    (hSm : ∀ s, s ∈ Sm ↔ IsHCParam (ν s))
    (ds : ∀ s ∈ Sm, IsHCParam (ν s) ∧ IsDS ε (ν s) (σs s))
    (toSum : ∀ (v w : U.R.H) (x y : Fin (2 * r + k + 1) → ℂ), IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) v →
      IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) w →
      ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin (2 * r + k + 1)) (vI wI : ∀ i, Hs (sI i)),
        (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, U.R.σ (P⁻¹ * g * P) v⟫_ℂ * (star y ⬝ᵥ (q g *ᵥ x)) =
          ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ)
    (ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
      ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → U.R.H) (xI yI : ι → Fin (2 * r + k + 1) → ℂ),
        (∀ i, IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (vI i) ∧ IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ =
          ∑ i, ⟪wI i, U.R.σ (P⁻¹ * g * P) (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (q g *ᵥ xI i))) :
    ∃ T : {s // IsHCParam (ν s)} → URep k r, (∀ s, (T s).R.IsDS ε (ν s)) ∧
      (∀ v w, U.R.KFin v → U.R.KFin w → ∀ c d, ∃ (I : Type) (_ : Fintype I) (s : I → {s // IsHCParam (ν s)})
        (y y' : ∀ i, (T (s i)).R.H),
        ∀ g ∈ GG k r, ⟪w, U.R.σ g v⟫_ℂ * q g c d = ∑ i, ⟪y' i, (T (s i)).R.σ g (y i)⟫_ℂ) ∧
      ∀ s, ∃ y : (T s).R.H, y ≠ 0 ∧ ∃ (I : Type) (_ : Fintype I) (v w : I → U.R.H)
        (c d : I → Fin (2 * r + k + 1)), (∀ i, U.R.KFin (v i) ∧ U.R.KFin (w i)) ∧
        ∀ g ∈ GG k r, ⟪y, (T s).R.σ g y⟫_ℂ = ∑ i, ⟪w i, U.R.σ g (v i)⟫_ℂ * q g (c i) (d i) := by
  have hk := fun v => CompanionTheory.CapEig.kfin_iff k r ε P U.R.H U.R.σ v hP
  have hds : ∀ s : {s // IsHCParam (ν s)}, IsDSHpk k r ε (ν s) (fun x => σs s (P * x * P⁻¹)) := fun s =>
    ⟨P, hP, by
      have e : (fun g => (fun x => σs s (P * x * P⁻¹)) (P⁻¹ * g * P)) = σs s := funext fun g => by
        simp only [forth_back hP.1]
      rw [e]
      exact (ds s ((hSm s).2 s.2)).2⟩
  refine ⟨fun s => ⟨⟨Hs s, fun x => σs s (P * x * P⁻¹)⟩, isURepOn_of_ds (hds s)⟩, fun s => ⟨s.2, hds s⟩,
    fun v w hv hw c d => ?_, fun s => ?_⟩
  · obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := toSum v w (P *ᵥ Pi.single d 1) (star (Pi.single c 1 ᵥ* P⁻¹))
      ((hk v).1 hv) ((hk w).1 hw)
    refine ⟨ι, inferInstance, fun i => ⟨sI i, (hSm _).1 (hI i).1⟩, vI, wI, fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    rw [back_forth hP.1, hq, star_star, dot_conj, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (q g), inv_mul_P hP.1, Matrix.mul_one, Matrix.vecMul_one, single_one_dotProduct,
      Matrix.mulVec_single_one] at this
    exact this
  · have hs := (hSm s).2 s.2
    obtain ⟨S, hS, hSK, -, ⟨y, hyS, hy0, -⟩, -⟩ := (ds s hs).2.2.2.2.2.2.1
    have hy : IsKFin ε (σs s) y := ⟨S, hS, hyS, hSK⟩
    obtain ⟨ι, _, vI, wI, xI, yI, hI, hsum⟩ := ofSum s hs y y hy hy
    refine ⟨y, hy0, ι × Fin (2 * r + k + 1) × Fin (2 * r + k + 1), inferInstance,
      fun p => ((star (yI p.1) ᵥ* P) p.2.1 * (P⁻¹ *ᵥ xI p.1) p.2.2) • vI p.1, fun p => wI p.1,
      fun p => p.2.1, fun p => p.2.2, fun p => ⟨kfin_smul _ ((hk _).2 (hI p.1).1), (hk _).2 (hI p.1).2⟩,
      fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    refine this.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [back_forth hP.1, hq, dot_conj, dot_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, inner_smul_right]
    ring

/- English proof (translation)
Introduce `t hZ k r ε μ U b h hU hg hlt`. Take `⟨hμ, P, hP, hτ⟩` from `hU`. Take `⟨⟨X, hX⟩, ⟨Y, hY⟩⟩` from `hZ _ ε μ U.R.H _ hμ hτ h hg hlt`. Consider the cases of `b`. Conclude with `transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum`.

Establish `hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹` using `fun g => by`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]`. Take `⟨T, h1, h2, h3⟩` from `transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum`. Use `⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, I, _, v, w, c, d, hk, he⟩` from `h3 s`.

Conclude with `⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩`.
-/
theorem zuckerman_hypothesis_holds : ZuckH := by
  intro t hZ k r ε μ U b h hU hg hlt
  obtain ⟨hμ, P, hP, hτ⟩ := hU
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hZ _ ε μ U.R.H _ hμ hτ h hg hlt
  cases b
  · exact transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum
  · have hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ :=
      fun g => by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
          Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    obtain ⟨T, h1, h2, h3⟩ :=
      transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum
    refine ⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩
    obtain ⟨y, hy, I, _, v, w, c, d, hk, he⟩ := h3 s
    exact ⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩

end GlobalTheory.CompanionTheory.ZuckTransport

end
