import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
open scoped BigOperators

namespace GlobalTheory.BaseVacuum.ProductTheta

variable (L : PeriodPair) {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

/- English proof (translation)
Rewrite using `[(stdHBasic L (ι × m)).1, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(stdHBasic L m).1]`.
-/
theorem stdH_prod (x y : ι × m → ℂ) :
    stdH L (ι × m) x y = ∑ k, stdH L m (fun v => x (k, v)) (fun v => y (k, v)) := by
  rw [(stdHBasic L (ι × m)).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(stdHBasic L m).1]

/- English proof (translation)
Unfold `alphaQ qOf`. Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Rewrite using `[stdH_prod, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]`.
-/
theorem alphaQ_prod (c : ℝ) (y : ι × m → ℂ) :
    alphaQ c (stdH L (ι × m)) y = ∏ k, alphaQ c (stdH L m) (fun v => y (k, v)) := by
  unfold alphaQ qOf
  rw [← Complex.exp_sum]
  congr 1
  rw [stdH_prod, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

/- English proof (translation)
Unfold `altE`. Rewrite using `[stdH_prod, Complex.im_sum]`.
-/
theorem altE_prod (x y : ι × m → ℂ) :
    altE (stdH L (ι × m)) x y = ∑ k, altE (stdH L m) (fun v => x (k, v)) (fun v => y (k, v)) := by
  unfold altE
  rw [stdH_prod, Complex.im_sum]

/- English proof (translation)
Simplify using `only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Prod.forall]`.
-/
theorem mem_stdLat_prod (x : ι × m → ℂ) :
    x ∈ stdLat L (ι × m) ↔ ∀ k, (fun v => x (k, v)) ∈ stdLat L m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Prod.forall]

/- English proof (translation)
Unfold `F0`. Rewrite using `[opUStd L (ι × m), Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[opUStd L m]`.
-/
theorem heisenbergOperator_gaussianVacuum_prod_blocks (ω₀ : ℂ) (x z : ι × m → ℂ) :
    opU (stdH L (ι × m)) x (F0 L ω₀ (ι × m)) z
      = ∏ k, opU (stdH L m) (fun v => x (k, v)) (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold F0
  rw [opUStd L (ι × m), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [opUStd L m]

/- English proof (translation)
Unfold `F0 prodFn`. Rewrite using `[Fintype.prod_prod_type]`.
-/
theorem gaussianVacuum_prod_blocks (ω₀ : ℂ) (z : ι × m → ℂ) : F0 L ω₀ (ι × m) z = ∏ k, F0 L ω₀ m (fun v => z (k, v)) := by
  unfold F0 prodFn
  rw [Fintype.prod_prod_type]

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[alphaQ_prod]`. Apply the tactic sequence `exact Finset.prod_induction _ (fun a : ℂ => a = 1 ∨ a = -1) (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp) (Or.inl rfl) (fun k _ => h.1 _ (hx k))`. Rewrite using `[alphaQ_prod, alphaQ_prod, alphaQ_prod, altE_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Conclude with `h.2 _ (hx k) _ (hy k)`.
-/
theorem semiChar_prod (c : ℝ) (Λ : AddSubgroup (m → ℂ)) (h : IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m))) :
    IsSemiChar (stdH L (ι × m)) (blkLat (ι := ι) Λ) (alphaQ c (stdH L (ι × m))) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [alphaQ_prod]
    exact Finset.prod_induction _ (fun a : ℂ => a = 1 ∨ a = -1)
      (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
      (Or.inl rfl) (fun k _ => h.1 _ (hx k))
  · rw [alphaQ_prod, alphaQ_prod, alphaQ_prod, altE_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact h.2 _ (hx k) _ (hy k)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∀ x ∈ stdLat L (ι × m), ∀ z, _ = _`. Introduce `x hx z`. Rewrite using `[alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib, gaussianVacuum_prod_blocks]`. Establish `hx'` using `(mem_stdLat_prod L x).1 hx`. Conclude with `Finset.prod_congr rfl fun k _ => hF _ (hx' k) _`.
-/
theorem fixed_prod (ω₀ : ℂ) (c' : ℝ)
    (hF : F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c' (stdH L m)) (stdLat L m)) :
    F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c' (stdH L (ι × m))) (stdLat L (ι × m)) := by
  change ∀ x ∈ stdLat L (ι × m), ∀ z, _ = _
  intro x hx z
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib, gaussianVacuum_prod_blocks]
  have hx' := (mem_stdLat_prod L x).1 hx
  exact Finset.prod_congr rfl fun k _ => hF _ (hx' k) _

def prodReps (S : Finset (m → ℂ)) : Finset (ι × m → ℂ) :=
  (Fintype.piFinset fun _ : ι => S).map (Equiv.curry ι m ℂ).symm.toEmbedding

/- English proof (translation)
Rewrite using `[prodReps, Finset.card_map, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]`.
-/
theorem card_prodReps (S : Finset (m → ℂ)) : (prodReps (ι := ι) S).card = S.card ^ Fintype.card ι := by
  rw [prodReps, Finset.card_map, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨f, hf, rfl⟩` from `Finset.mem_map.1 hy`. Rewrite `hf` using `[Fintype.mem_piFinset]`. Introduce `k`.

Conclude with `hS.1 _ (hf k)`. Introduce `x hx y hy hd`. Take `⟨f, hf, rfl⟩` from `Finset.mem_map.1 hx`. Take `⟨g, hg, rfl⟩` from `Finset.mem_map.1 hy`. Rewrite `hf`, `hg` using `[Fintype.mem_piFinset]`.

Establish `hd'` using `(mem_stdLat_prod L _).1 hd`. Establish `: f = g` using `funext fun k => hS.2.1 _ (hf k) _ (hg k) (hd' k)`. Rewrite using `[this]`. Introduce `y hy`. Establish `: ∀ k, ∃ x ∈ S, (fun v => y (k, v)) - x ∈ stdLat L m` using `fun k => hS.2.2 _ (hy k)`.

Use `choose f hf hfy using this`. Use `⟨(Equiv.curry ι m ℂ).symm f, Finset.mem_map_of_mem _ (Fintype.mem_piFinset.2 hf), ?_⟩` and prove the remaining obligations. Rewrite using `[mem_stdLat_prod]`. Introduce `k`. Conclude with `hfy k`.
-/
theorem prodReps_isReps {Λ : AddSubgroup (m → ℂ)} {S : Finset (m → ℂ)} (hS : IsReps (stdLat L m) Λ S) :
    IsReps (stdLat L (ι × m)) (blkLat (ι := ι) Λ) (prodReps S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf
    intro k
    exact hS.1 _ (hf k)
  · intro x hx y hy hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf hg
    have hd' := (mem_stdLat_prod L _).1 hd
    have : f = g := funext fun k => hS.2.1 _ (hf k) _ (hg k) (hd' k)
    rw [this]
  · intro y hy
    have : ∀ k, ∃ x ∈ S, (fun v => y (k, v)) - x ∈ stdLat L m := fun k => hS.2.2 _ (hy k)
    choose f hf hfy using this
    refine ⟨(Equiv.curry ι m ℂ).symm f, Finset.mem_map_of_mem _ (Fintype.mem_piFinset.2 hf), ?_⟩
    rw [mem_stdLat_prod]
    intro k
    exact hfy k

/- English proof (translation)
Establish `h1` using `Nat.card_eq_of_bijective _ (repClass_bijective hS)`. Rewrite `h1` using `[Nat.card_eq_fintype_card, Fintype.card_coe]`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem relIdx_eq_card {V : Type} [AddCommGroup V] [Module ℂ V] {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V}
    (hS : IsReps Λ₁ Λ₂ S) : relIdx Λ₁ Λ₂ = S.card := by
  have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  rw [h1]
  rfl

/- English proof (translation)
Unfold `sumU prodReps`. Rewrite using `[Finset.sum_map, Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib]`. Both sides reduce to the same expression.
-/
theorem sumU_prod (c : ℝ) (ω₀ : ℂ) (S : Finset (m → ℂ)) (z : ι × m → ℂ) :
    sumU (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (prodReps S) (F0 L ω₀ (ι × m)) z
      = ∏ k, sumU (stdH L m) (alphaQ c (stdH L m)) S (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold sumU prodReps
  rw [Finset.sum_map, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib]
  rfl

/- English proof (translation)
Rewrite using `[← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg r) n), pow_right_comm, Real.sq_sqrt hr]`.
-/
theorem sqrt_pow' (r : ℝ) (hr : 0 ≤ r) (n : ℕ) : Real.sqrt (r ^ n) = Real.sqrt r ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg r) n), pow_right_comm, Real.sq_sqrt hr]

end GlobalTheory.BaseVacuum.ProductTheta

namespace GlobalTheory.BaseVacuum

open ProductTheta in

/- English proof (translation)
Introduce `L ω₀ c ι m _ _ _ _ Λ hα hF hn`. Establish `hα'` using `semiChar_prod L (ι := ι) c Λ hα`. Establish `hF'` using `fixed_prod L (ι := ι) ω₀ c hF`. Take `⟨⟨S, hS⟩, hcard⟩` from `repsExist _ (stdLat L m) Λ hn`. Establish `hS'` using `prodReps_isReps L (ι := ι) hS`.

Establish `hr : relIdx (stdLat L (ι × m)) (blkLat (ι` using `ι) Λ) = relIdx (stdLat L m) Λ ^ Fintype.card ι := by`. Rewrite using `[relIdx_eq_card hS', card_prodReps, hcard S hS]`. Use `⟨hα', hF', by rw [hr]; exact pow_ne_zero _ hn, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[interReps _ _ (stdHBasic L _).2.1 _ _ _ hα' _ hF' _ hS' w, sumU_prod]`. Rewrite using `[Finset.prod_congr rfl fun k _ => interReps _ _ (stdHBasic L m).2.1 _ _ _ hα _ hF _ hS (fun v => w (k, v))]`.

Rewrite using `[hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.cast_pow, sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]`.
-/
theorem prod_blk_inter : ∀ (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)), IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m)) → F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) → relIdx (stdLat L m) Λ ≠ 0 → IsSemiChar (stdH L (ι × m)) (blkLat Λ) (alphaQ c (stdH L (ι × m))) ∧ F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) ∧ relIdx (stdLat L (ι × m)) (blkLat Λ) ≠ 0 ∧ ∀ w, inter (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) (blkLat Λ) (F0 L ω₀ (ι × m)) w = ∏ k, inter (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) Λ (F0 L ω₀ m) (fun v => w (k, v)) := by
  intro L ω₀ c ι m _ _ _ _ Λ hα hF hn
  have hα' := semiChar_prod L (ι := ι) c Λ hα
  have hF' := fixed_prod L (ι := ι) ω₀ c hF
  obtain ⟨⟨S, hS⟩, hcard⟩ := repsExist _ (stdLat L m) Λ hn
  have hS' := prodReps_isReps L (ι := ι) hS
  have hr : relIdx (stdLat L (ι × m)) (blkLat (ι := ι) Λ) = relIdx (stdLat L m) Λ ^ Fintype.card ι := by
    rw [relIdx_eq_card hS', card_prodReps, hcard S hS]
  refine ⟨hα', hF', by rw [hr]; exact pow_ne_zero _ hn, fun w => ?_⟩
  rw [interReps _ _ (stdHBasic L _).2.1 _ _ _ hα' _ hF' _ hS' w, sumU_prod]
  rw [Finset.prod_congr rfl fun k _ => interReps _ _ (stdHBasic L m).2.1 _ _ _ hα _ hF _ hS (fun v => w (k, v))]
  rw [hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.cast_pow,
    sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]

end GlobalTheory.BaseVacuum
