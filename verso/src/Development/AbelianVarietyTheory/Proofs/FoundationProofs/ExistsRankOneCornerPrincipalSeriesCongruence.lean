import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨g, rfl⟩` from `hg`. Conclude with `(g.val i j).2`.
-/
theorem corner_val_le_one {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) : valuation k (g.val i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hg
  exact (g.val i j).2

/- English proof (translation)
Set `N : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨g.val i j, hM i j⟩`. Establish `e : (algebraMap 𝒪[k] k).mapMatrix N = g.val` using `rfl`. Establish `hu : IsUnit N.det`. Use `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, e, hd]`.

Take `⟨u, hu'⟩` from `(Matrix.isUnit_iff_isUnit_det N).2 hu`. Use `⟨u, Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap 𝒪[k] k).mapMatrix u.val = g.val`. Rewrite using `[hu', e]`.
-/
theorem corner_mem_KO {g : GL (Fin n) k} (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) :
    g ∈ KO k (Fin n) := by
  let N : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix N = g.val := rfl
  have hu : IsUnit N.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

end

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hord x hx a b hab hnt htr`. Establish `hnt'` using `hnt`. Unfold `Triv at hnt'`. Use `push_neg at hnt'`. Take `⟨u, hu, hle, hne⟩` from `hnt'`.

Establish `hx0 : x.val a b ≠ 0` using `fun h0 => hnt (h0 ▸ triv_zero _)`. Use `set s : k := ((u : k) - 1) / x.val a b with hs`. Establish `hsx : s * x.val a b = (u : k) - 1` using `div_mul_cancel₀ _ hx0`. Establish `hs1 : valuation k s ≤ 1`. Rewrite using `[hs, map_div₀]`.

Conclude with `div_le_one_of_le₀ hle zero_le'`. Establish `hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j)` using `fun i j => by`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_left' hs1`. Set `M : Matrix (Fin n) (Fin n) k` to `1 + Matrix.vecMulVec (Pi.single b s) (x.val a)`.

Establish `hdet : M.det = (u : k)`. Simplify using `only [M]`. Rewrite using `[Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]`. Expand and normalize the polynomial expressions, which then agree. Set `j : GL (Fin n) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)`.

Establish `hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)` using `rfl`. Establish `hjK : j ∈ KO k (Fin n)`. Use `corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)` and prove the remaining obligations. Rewrite using `[hj, Matrix.add_apply]`. Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations.

Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Rewrite using `[Matrix.vecMulVec_apply, Pi.single_apply] split_ifs`. Conclude with `(hsm _ _).trans (corner_val_le_one hx _ _)`. Simplify using the standard rewrite rules. Use `⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply] split_ifs with h`. Substitute `h` using the available equality. Conclude with `triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))`. Rewrite using `[zero_mul]`. Conclude with `triv_zero _`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Simplify using `[h]`. Use `theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`.

Use `split_ifs with h`. Rewrite using `[h, hsx]`. Simplify using the standard rewrite rules. Conclude with `mul_mem (mul_mem hx hjK) (inv_mem hx)`. Establish `hxx : x.val * (x⁻¹).val = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Rewrite using `[Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]`. Use `congr 2`. Use extensionality with `i`. Simplify using `[Matrix.mulVec_single, mul_comm]`. Use extensionality with `l`.

Use `congrFun (congrFun hxx a) l` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[Matrix.vecMul, dotProduct]`. Rewrite using `[Pi.single_apply, this, Matrix.one_apply]`. Simplify using `[eq_comm]`.
-/
theorem corner_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  intro k _ _ _ _ n ψ hord x hx a b hab hnt htr
  have hnt' := hnt
  unfold Triv at hnt'
  push_neg at hnt'
  obtain ⟨u, hu, hle, hne⟩ := hnt'
  have hx0 : x.val a b ≠ 0 := fun h0 => hnt (h0 ▸ triv_zero _)
  set s : k := ((u : k) - 1) / x.val a b with hs
  have hsx : s * x.val a b = (u : k) - 1 := div_mul_cancel₀ _ hx0
  have hs1 : valuation k s ≤ 1 := by
    rw [hs, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j) := fun i j => by
    rw [map_mul]
    exact mul_le_of_le_one_left' hs1
  let M : Matrix (Fin n) (Fin n) k := 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)
  have hdet : M.det = (u : k) := by
    simp only [M]
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]
    ring
  let j : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)
  have hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a) := rfl
  have hjK : j ∈ KO k (Fin n) := by
    refine corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)
    rw [hj, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.vecMulVec_apply, Pi.single_apply]
      split_ifs
      · exact (hsm _ _).trans (corner_val_le_one hx _ _)
      · simp
  refine ⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩
  · rw [hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      exact triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))
    · rw [zero_mul]; exact triv_zero _
  · intro h
    apply hne
    simp [h]
  · refine theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h, hsx]
    · simp
  · exact mul_mem (mul_mem hx hjK) (inv_mem hx)
  · have hxx : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
    congr 2
    · ext i
      simp [Matrix.mulVec_single, mul_comm]
    · ext l
      have := congrFun (congrFun hxx a) l
      rw [Matrix.mul_apply] at this
      rw [Matrix.vecMul, dotProduct]
      rw [Pi.single_apply, this, Matrix.one_apply]
      simp [eq_comm]

end GlobalTheory.PsType
