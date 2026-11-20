import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cnd_V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n × Fin n)

def cnd_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : cnd_V n := WithLp.toLp 2 fun p => M p.1 p.2

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Use `congr 1`. Unfold `Formalism.REAL.hs`. Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem cnd_norm_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ‖cnd_vec M‖ = Real.sqrt (Formalism.REAL.hs M) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold Formalism.REAL.hs
  rw [Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cnd_vec_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : cnd_vec M - cnd_vec N = cnd_vec (M - N) := rfl

/- English proof (translation)
Establish `e : cnd_V n ≃ₗ[ℝ] (Fin n × Fin n → ℂ)` using `WithLp.linearEquiv 2 ℝ _`. Rewrite using `[e.finrank_eq, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cnd_finrank (n : ℕ) : Module.finrank ℝ (cnd_V n) = 2 * n ^ 2 := by
  have e : cnd_V n ≃ₗ[ℝ] (Fin n × Fin n → ℂ) := WithLp.linearEquiv 2 ℝ _
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring

/- English proof (translation)
Establish `hgU : Formalism.REAL.inUJ ε (umat g)` using `g.2`. Take `⟨k₀, X₀, hk, hX, hg⟩` from `(Formalism.REAL.polar_decomposition_holds n ε).1 _ hgU`. Establish `hset : {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧ umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)} = {Real.sqrt (Formalism.REAL.hs X₀)}`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, X, hk', hX', hg', rfl⟩`. Use `((Formalism.REAL.polar_decomposition_holds n ε).2.1 k k₀ X X₀ hk' hk hX' hX (hg'.symm.trans hg)).2` as an intermediate fact. Rewrite using `[this]`. Both sides reduce to the same expression. Introduce `ht`.

Conclude with `⟨k₀, X₀, hk, hX, hg, ht⟩`. Establish `hd : cartanDistance ε g = Real.sqrt (Formalism.REAL.hs X₀)`. Unfold `cartanDistance`. Rewrite using `[hset, csInf_singleton]`. Establish `h1` using `hilbert_schmidt_polar_bound k₀ X₀ hk.1 (hermitian_of_mem_p ε X₀ hX).1`.

Rewrite using `[hd, hg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]`.
-/
theorem cnd_hs_le_dist {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    Real.sqrt (Formalism.REAL.hs (umat g)) ≤ Real.sqrt (n : ℝ) * Real.exp (cartanDistance ε g) := by
  have hgU : Formalism.REAL.inUJ ε (umat g) := g.2
  obtain ⟨k₀, X₀, hk, hX, hg⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 _ hgU
  have hset : {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)} = {Real.sqrt (Formalism.REAL.hs X₀)} := by
    ext t
    constructor
    · rintro ⟨k, X, hk', hX', hg', rfl⟩
      have := ((Formalism.REAL.polar_decomposition_holds n ε).2.1 k k₀ X X₀ hk' hk hX' hX (hg'.symm.trans hg)).2
      rw [this]
      rfl
    · intro ht
      exact ⟨k₀, X₀, hk, hX, hg, ht⟩
  have hd : cartanDistance ε g = Real.sqrt (Formalism.REAL.hs X₀) := by
    unfold cartanDistance
    rw [hset, csInf_singleton]
  have h1 := hilbert_schmidt_polar_bound k₀ X₀ hk.1 (hermitian_of_mem_p ε X₀ hX).1
  rw [hd, hg]
  calc Real.sqrt (Formalism.REAL.hs (k₀ * NormedSpace.exp X₀))
      ≤ Real.sqrt ((n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

def cnd_pt (X : CData) (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : Matrix (Fin X.I.n) (Fin X.I.n) ℂ :=
  umat ((x⁻¹ * (γ : X.I.GA) * x).1 v)

def CSize.SepStep {X : CData} (S : CSize X) : Prop :=
  ∀ (x : X.I.GA) (γ γ' : X.I.GFset), γ ≠ γ' → X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 → X.φ (x⁻¹ * (γ' : X.I.GA) * x) ≠ 0 →
    S.tau1 x ^ 2 ≤ (∏ v, Real.sqrt (Formalism.REAL.hs (cnd_pt X x γ v - cnd_pt X x γ' v))) ^
      ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ))

/- English proof (translation)
Introduce `x r hr T hT`. Establish `hτ` using `(hst.2.2.2.2.2.1 x).1`. Establish `hτ2 : 0 < S.tau1 x ^ 2` using `by positivity`. Use `set p : X.I.GFset → (∀ _ : InfinitePlace X.I.F, cnd_V X.I.n) := fun γ v => cnd_vec (cnd_pt X x γ v) with hp`. Establish `hsepP : ∀ γ ∈ T, ∀ γ' ∈ T, γ ≠ γ' → S.tau1 x ^ 2 ≤ (∏ v, ‖p γ v - p γ' v‖) ^ ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ))`.

Introduce `γ hγ γ' hγ' hne`. Use `hsep x γ γ' hne (hT γ hγ).1 (hT γ' hγ').1` as an intermediate fact. Simplify `this` using `only [hp, cnd_vec_sub, cnd_norm_vec]`. Establish `hcard : (0 : ℝ) < (Fintype.card (InfinitePlace X.I.F) : ℝ)`. Conclude with `Fintype.card_pos` after adjusting the coercions.

Establish `hinj : Set.InjOn p (T : Set X.I.GFset)`. Introduce `γ hγ γ' hγ' h`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hsepP γ hγ γ' hγ' hne`. Rewrite `h1` using `[h]`.

Establish `hz : (∏ v : InfinitePlace X.I.F, ‖p γ' v - p γ' v‖) = 0`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) (by rw [sub_self, norm_zero])`. Rewrite `h1` using `[hz, Real.zero_rpow (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : 0 < Real.sqrt (X.I.n : ℝ)` using `Real.sqrt_pos.2 (by exact_mod_cast hn)`.

Establish `h` using `Formalism.SA.P.packing_count_geometric_mean (InfinitePlace X.I.F) (fun _ => cnd_V X.I.n) (2 * X.I.n ^ 2) (fun _ => cnd_finrank X.I.n) (T.image p) (S.tau1 x ^ 2) (fun v => Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) hτ2 (fun v => mul_pos hs (Real.exp_pos _)) (by`. Introduce `a ha b hb hab`. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.1 ha`. Take `⟨γ', hγ', rfl⟩` from `Finset.mem_image.1 hb`. Conclude with `hsepP γ hγ γ' hγ' (fun e => hab (by rw [e])))`.

Use the proof step `(by`. Introduce `a ha v`. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.1 ha`. Use `show ‖cnd_vec (cnd_pt X x γ v)‖ ≤ _`. Rewrite using `[cnd_norm_vec]`.

Use `le_trans (cnd_hs_le_dist (X.I.ε v) _) ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((hT γ hγ).2 v)) hs.le)`. Rewrite `h` using `[Finset.card_image_of_injOn hinj]`. Conclude with `h`.
-/
theorem cnd_pack {X : CData} (S : CSize X) (hn : 1 ≤ X.I.n) (hst : S.Strata) (hsep : S.SepStep) : S.PackCount := by
  classical
  intro x r hr T hT
  have hτ := (hst.2.2.2.2.2.1 x).1
  have hτ2 : 0 < S.tau1 x ^ 2 := by positivity
  set p : X.I.GFset → (∀ _ : InfinitePlace X.I.F, cnd_V X.I.n) := fun γ v => cnd_vec (cnd_pt X x γ v) with hp
  have hsepP : ∀ γ ∈ T, ∀ γ' ∈ T, γ ≠ γ' → S.tau1 x ^ 2 ≤
      (∏ v, ‖p γ v - p γ' v‖) ^ ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ)) := by
    intro γ hγ γ' hγ' hne
    have := hsep x γ γ' hne (hT γ hγ).1 (hT γ' hγ').1
    simpa only [hp, cnd_vec_sub, cnd_norm_vec] using this
  have hcard : (0 : ℝ) < (Fintype.card (InfinitePlace X.I.F) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn p (T : Set X.I.GFset) := by
    intro γ hγ γ' hγ' h
    by_contra hne
    have h1 := hsepP γ hγ γ' hγ' hne
    rw [h] at h1
    have hz : (∏ v : InfinitePlace X.I.F, ‖p γ' v - p γ' v‖) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) (by rw [sub_self, norm_zero])
    rw [hz, Real.zero_rpow (by positivity)] at h1
    linarith
  have hs : 0 < Real.sqrt (X.I.n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h := Formalism.SA.P.packing_count_geometric_mean (InfinitePlace X.I.F) (fun _ => cnd_V X.I.n) (2 * X.I.n ^ 2)
    (fun _ => cnd_finrank X.I.n) (T.image p) (S.tau1 x ^ 2) (fun v => Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) hτ2
    (fun v => mul_pos hs (Real.exp_pos _))
    (by
      intro a ha b hb hab
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hb
      exact hsepP γ hγ γ' hγ' (fun e => hab (by rw [e])))
    (by
      intro a ha v
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      show ‖cnd_vec (cnd_pt X x γ v)‖ ≤ _
      rw [cnd_norm_vec]
      refine le_trans (cnd_hs_le_dist (X.I.ε v) _) ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((hT γ hγ).2 v)) hs.le)
  rw [Finset.card_image_of_injOn hinj] at h
  exact h

end Formalism.MainNotions.LeviCoordinates

end
