import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.IntegrableOnSimp

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def Stk (U : Set V) : Prop := ∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U →
  ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) → dC' (intS' ω) y = intS' (extDeriv ω) y

def Wf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (eta A φ c j g) (fun l : Fin (j + 1) => A (g (k + 1 - j + l)) o)

def Bf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (Kf A φ (eta A φ c j) g) (fun l : Fin (j + 1) => A (g (k - j + l)) o)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Kf]`. Use `congr 1`. Use function extensionality and compare the values at `γ`. Rewrite using `[hD k c j (cons γ σ) (cons γ σ') (fun n hn => by`.

Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ m => exact h m (by omega))]`.
-/
theorem kf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ)
    (h : ∀ n, n + j + 1 ≤ k + 1 → σ n = σ' n) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ') (fun n hn => by
    cases n with
    | zero => rfl
    | succ m => exact h m (by omega))]

/- English proof (translation)
Establish `h0` using `hC H k c hc (k + 1) le_rfl (cons (τ 0) τ') x hx`. Rewrite `h0` using `[Nat.sub_self]`. Establish `e1 : eta A φ c (k + 1) (skip 0 (cons (τ 0) τ')) = eta A φ c (k + 1) τ'`. Use `congr 1`. Establish `e2 : eta A φ c (k + 1) (skip 1 (cons (τ 0) τ')) = eta A φ c (k + 1) τ` using `hD k c (k + 1) _ _ (fun n hn => by`.

Establish `: n = 0` using `by omega`. Substitute `this` using the available equality. Simplify using `[skip, cons])`. Simplify using `only [delG, Finset.sum_range_succ, Finset.sum_range_zero, e1, e2] at h0`. Simplify using `at h0`.

Rewrite `h0` using `[add_neg_eq_zero]`. Conclude with `h0.symm`.
-/
theorem eta_top (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (τ τ' : ℕ → Γ) (x : V) (hx : x ∈ U) :
    eta A φ c (k + 1) τ x = eta A φ c (k + 1) τ' x := by
  have h0 := hC H k c hc (k + 1) le_rfl (cons (τ 0) τ') x hx
  rw [Nat.sub_self] at h0
  have e1 : eta A φ c (k + 1) (skip 0 (cons (τ 0) τ')) = eta A φ c (k + 1) τ' := by
    congr 1
  have e2 : eta A φ c (k + 1) (skip 1 (cons (τ 0) τ')) = eta A φ c (k + 1) τ :=
    hD k c (k + 1) _ _ (fun n hn => by
      have : n = 0 := by omega
      subst this
      simp [skip, cons])
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, e1, e2] at h0
  simp at h0
  rw [add_neg_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
private theorem neg_one_pow_add_one_add_eq_mul (a : ℕ) (m : ℕ) : (-1 : ℝ) ^ (a + 1 + m) = (-1) ^ a * (-1) ^ (m + 1) := by
  ring

/- English proof (translation)
Substitute `hk` using the available equality. Take `⟨ω, hω⟩ : ∃ ω, ω = Kf A φ (eta A φ c j) g` from `⟨_, rfl⟩`. Take `⟨Y, hY⟩ : ∃ Y : Fin (j + 2) → V, Y = fun l : Fin (j + 2) => A (g (a + (l : ℕ))) o` from `⟨_, rfl⟩`. Take `⟨Z, hZ⟩ : ∃ Z : Fin (j + 1) → V, Z = fun l : Fin (j + 1) => A (g (a + 1 + (l : ℕ))) o` from `⟨_, rfl⟩`. Establish `hYU : ∀ l, Y l ∈ U` using `fun l => by rw [hY]; exact H.mapsTo _ _ ho`.

Establish `hZU : ∀ l, Z l ∈ U` using `fun l => by rw [hZ]; exact H.mapsTo _ _ ho`. Establish `hcont : ∀ σ, ContinuousOn (Kf A φ (eta A φ c j) σ) U` using `fun σ => ((hSm H (a + j) c j σ).2).continuousOn`. Establish `hK : ∀ i, a + 1 ≤ i → Kf A φ (eta A φ c j) (skip i g) = ω`. Introduce `i hi`. Rewrite using `[hω]`.

Conclude with `kf_dep hD c j _ _ (fun n hn => by simp only [skip]; rw [if_pos (by omega)])`. Establish `hF2 : ∀ x ∈ U, (∑ i ∈ Finset.range (a + 2), ((-1 : ℝ) ^ i) • Kf A φ (eta A φ c j) (skip i g)) x = eta A φ c j g x`. Introduce `x hx`. Establish `h1` using `hH H j a (eta A φ c j) g x hx`. Establish `h0 : ∀ γ, psi A φ γ x • delG (a + 1) (eta A φ c j) (cons γ g) x = 0`.

Introduce `γ`. Use `hC H (a + j) c hc j (by omega) (cons γ g) x hx` as an intermediate fact. Rewrite `this` using `[show a + j + 1 - j = a + 1 by omega]`. Rewrite using `[this, smul_zero]`. Establish `h2 : Kf A φ (delG (a + 1) (eta A φ c j)) g x = 0`.

Simplify using `only [Kf, h0, finsum_zero]`. Rewrite `h1` using `[h2, sub_zero]`. Rewrite using `[← h1]`. Simplify using `only [delG, Finset.sum_apply]`. Establish `hWj : Wf A φ c o j g = ∑ i ∈ Finset.range (a + 2), (-1 : ℝ) ^ i * intS' (Kf A φ (eta A φ c j) (skip i g)) Z`.

Rewrite using `[← intS'_sum H.convex _ _ _ (fun i _ => hcont _) hZU]`. Rewrite using `[intS'_congr H.convex hF2 hZU]`. Simplify using `only [Wf, hZ]`. Use `congr 1`. Use function extensionality and compare the values at `l`.

Rewrite using `[show a + j + 1 - j + ↑l = a + 1 + ↑l by omega]`. Establish `hBA : ∀ i, i < a + 1 → Bf A φ c o j (skip i g) = intS' (Kf A φ (eta A φ c j) (skip i g)) Z`. Introduce `i hi`. Simplify using `only [Bf, hZ]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Simplify using `only [skip]`. Rewrite using `[if_neg (by omega), show a + j - j + ↑l + 1 = a + 1 + ↑l by omega]`. Establish `hBB : ∀ m : Fin (j + 1), Bf A φ c o j (skip (a + 1 + ↑m) g) = intS' ω (fun l => Y (m.succ.succAbove l))`. Introduce `m`.

Simplify using `only [Bf, hY]`. Rewrite using `[hK _ (by omega)]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using `only [skip, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]`.

Apply the tactic sequence `split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] <;> first | (exfalso; omega) | (congr 3; omega)`. Establish `hExt : extDeriv ω = eta A φ c (j + 1) g` using `by rw [hω]; rfl`. Establish `hSt` using `hS j ω (by`. Rewrite using `[hω]`. Conclude with `((hSm H (a + j) c j g).2).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) Y hYU`.

Rewrite `hSt` using `[hExt]`. Rewrite `hSt` using `[dC', Fin.sum_univ_succ]`. Establish `hW1 : Wf A φ c o (j + 1) g = intS' (eta A φ c (j + 1) g) Y`. Simplify using `only [Wf, hY]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Rewrite using `[show a + j + 1 - (j + 1) + ↑l = a + ↑l by omega]`. Establish `hY0 : (fun l => Y ((0 : Fin (j + 2)).succAbove l)) = Z`. Use function extensionality and compare the values at `l`. Simplify using `only [hY, hZ, Fin.succAbove_zero, Fin.val_succ]`.

Rewrite using `[show a + (↑l + 1) = a + 1 + ↑l by omega]`. Rewrite `hSt` using `[hY0]`. Rewrite using `[show a + j + 2 = (a + 1) + (j + 1) by omega, Finset.sum_range_add]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => by rw [hBA i (Finset.mem_range.mp hi)])]`. Rewrite using `[Finset.sum_range (fun m => (-1 : ℝ) ^ (a + 1 + m) * Bf A φ c o j (skip (a + 1 + m) g))]`.

Simplify using `only [hBB]`. Rewrite `hWj` using `[Finset.sum_range_succ, hK _ le_rfl]`. Rewrite using `[hWj, hW1, ← hSt]`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, neg_one_pow_add_one_add_eq_mul, mul_assoc]`. Rewrite using `[mul_add, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chain (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) {o : V}
    (ho : o ∈ U) (a j : ℕ) (hk : a + j = k) (g : ℕ → Γ) :
    ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) =
      Wf A φ c o j g + (-1) ^ a * Wf A φ c o (j + 1) g := by
  subst hk
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Kf A φ (eta A φ c j) g := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin (j + 2) → V, Y = fun l : Fin (j + 2) => A (g (a + (l : ℕ))) o := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin (j + 1) → V, Z = fun l : Fin (j + 1) => A (g (a + 1 + (l : ℕ))) o :=
    ⟨_, rfl⟩
  have hYU : ∀ l, Y l ∈ U := fun l => by rw [hY]; exact H.mapsTo _ _ ho
  have hZU : ∀ l, Z l ∈ U := fun l => by rw [hZ]; exact H.mapsTo _ _ ho
  have hcont : ∀ σ, ContinuousOn (Kf A φ (eta A φ c j) σ) U :=
    fun σ => ((hSm H (a + j) c j σ).2).continuousOn
  have hK : ∀ i, a + 1 ≤ i → Kf A φ (eta A φ c j) (skip i g) = ω := by
    intro i hi
    rw [hω]
    exact kf_dep hD c j _ _ (fun n hn => by simp only [skip]; rw [if_pos (by omega)])
  have hF2 : ∀ x ∈ U, (∑ i ∈ Finset.range (a + 2),
      ((-1 : ℝ) ^ i) • Kf A φ (eta A φ c j) (skip i g)) x = eta A φ c j g x := by
    intro x hx
    have h1 := hH H j a (eta A φ c j) g x hx
    have h0 : ∀ γ, psi A φ γ x • delG (a + 1) (eta A φ c j) (cons γ g) x = 0 := by
      intro γ
      have := hC H (a + j) c hc j (by omega) (cons γ g) x hx
      rw [show a + j + 1 - j = a + 1 by omega] at this
      rw [this, smul_zero]
    have h2 : Kf A φ (delG (a + 1) (eta A φ c j)) g x = 0 := by
      simp only [Kf, h0, finsum_zero]
    rw [h2, sub_zero] at h1
    rw [← h1]
    simp only [delG, Finset.sum_apply]
  have hWj : Wf A φ c o j g = ∑ i ∈ Finset.range (a + 2),
      (-1 : ℝ) ^ i * intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    rw [← intS'_sum H.convex _ _ _ (fun i _ => hcont _) hZU]
    rw [intS'_congr H.convex hF2 hZU]
    simp only [Wf, hZ]
    congr 1
    funext l
    rw [show a + j + 1 - j + ↑l = a + 1 + ↑l by omega]
  have hBA : ∀ i, i < a + 1 → Bf A φ c o j (skip i g) = intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    intro i hi
    simp only [Bf, hZ]
    congr 1
    funext l
    simp only [skip]
    rw [if_neg (by omega), show a + j - j + ↑l + 1 = a + 1 + ↑l by omega]
  have hBB : ∀ m : Fin (j + 1), Bf A φ c o j (skip (a + 1 + ↑m) g) =
      intS' ω (fun l => Y (m.succ.succAbove l)) := by
    intro m
    simp only [Bf, hY]
    rw [hK _ (by omega)]
    congr 1
    funext l
    simp only [skip, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] <;>
      first | (exfalso; omega) | (congr 3; omega)
  have hExt : extDeriv ω = eta A φ c (j + 1) g := by rw [hω]; rfl
  have hSt := hS j ω (by
    rw [hω]
    exact ((hSm H (a + j) c j g).2).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) Y hYU
  rw [hExt] at hSt
  rw [dC', Fin.sum_univ_succ] at hSt
  have hW1 : Wf A φ c o (j + 1) g = intS' (eta A φ c (j + 1) g) Y := by
    simp only [Wf, hY]
    congr 1
    funext l
    rw [show a + j + 1 - (j + 1) + ↑l = a + ↑l by omega]
  have hY0 : (fun l => Y ((0 : Fin (j + 2)).succAbove l)) = Z := by
    funext l
    simp only [hY, hZ, Fin.succAbove_zero, Fin.val_succ]
    rw [show a + (↑l + 1) = a + 1 + ↑l by omega]
  rw [hY0] at hSt
  rw [show a + j + 2 = (a + 1) + (j + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hBA i (Finset.mem_range.mp hi)])]
  rw [Finset.sum_range (fun m => (-1 : ℝ) ^ (a + 1 + m) * Bf A φ c o j (skip (a + 1 + m) g))]
  simp only [hBB]
  rw [Finset.sum_range_succ, hK _ le_rfl] at hWj
  rw [hWj, hW1, ← hSt]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, neg_one_pow_add_one_add_eq_mul, mul_assoc]
  rw [mul_add, ← Finset.mul_sum]
  ring

end PositivityTheory.KB.WhittakerCocycle

end
