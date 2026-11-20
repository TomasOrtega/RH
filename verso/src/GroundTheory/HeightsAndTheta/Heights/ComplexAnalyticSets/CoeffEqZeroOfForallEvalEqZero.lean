import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassPolynomialDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

/- English proof (translation)
Use `⟨fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ), fun c t => ?_⟩` and prove the remaining obligations. Establish `hj : ∀ j : Fin N, (t + a) ^ (j : ℕ) = ∑ i : Fin N, t ^ (i : ℕ) * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))`. Introduce `j`. Establish `hr` using `Fin.sum_univ_eq_sum_range (fun i => t ^ i * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))) N`. Rewrite using `[hr, add_pow]`.

Rewrite using `[← Finset.sum_subset (Finset.range_subset_range.2 (show (j : ℕ) + 1 ≤ N by omega))]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Introduce `i _ hi`. Simplify using `only [Finset.mem_range, not_lt] at hi`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`.

Simplify using the standard rewrite rules. Repeatedly rewrite using `[hj, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem exists_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ K : Fin N → Fin N → ℂ, ∀ (c : Fin N → ℂ) (t : ℂ),
      ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        ∑ i : Fin N, (∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  refine ⟨fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ), fun c t => ?_⟩
  have hj : ∀ j : Fin N, (t + a) ^ (j : ℕ) =
      ∑ i : Fin N, t ^ (i : ℕ) * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ)) := by
    intro j
    have hr := Fin.sum_univ_eq_sum_range (fun i => t ^ i * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))) N
    rw [hr, add_pow]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show (j : ℕ) + 1 ≤ N by omega))]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  simp_rw [hj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Take `⟨K, hK⟩` from `exists_shift_coeff N a`. Use `⟨fun i => a ^ (N - (i : ℕ)) * (N.choose i : ℂ), K, fun c t => ?_⟩` and prove the remaining obligations. Establish `hr` using `Fin.sum_univ_eq_sum_range (fun i => a ^ (N - i) * (N.choose i : ℂ) * t ^ i) N`. Rewrite using `[hK, add_pow, Finset.sum_range_succ]`. Simplify using `only [add_mul, Finset.sum_add_distrib, hr, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]`.

Establish `: ∑ x ∈ Finset.range N, t ^ x * a ^ (N - x) * (N.choose x : ℂ) = ∑ x ∈ Finset.range N, a ^ (N - x) * (N.choose x : ℂ) * t ^ x` using `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_monic_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ (K₀ : Fin N → ℂ) (K : Fin N → Fin N → ℂ), ∀ (c : Fin N → ℂ) (t : ℂ),
      (t + a) ^ N + ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        t ^ N + ∑ i : Fin N, (K₀ i + ∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  obtain ⟨K, hK⟩ := exists_shift_coeff N a
  refine ⟨fun i => a ^ (N - (i : ℕ)) * (N.choose i : ℂ), K, fun c t => ?_⟩
  have hr := Fin.sum_univ_eq_sum_range (fun i => a ^ (N - i) * (N.choose i : ℂ) * t ^ i) N
  rw [hK, add_pow, Finset.sum_range_succ]
  simp only [add_mul, Finset.sum_add_distrib, hr, Nat.sub_self, pow_zero, Nat.choose_self,
    Nat.cast_one, mul_one]
  have : ∑ x ∈ Finset.range N, t ^ x * a ^ (N - x) * (N.choose x : ℂ) =
      ∑ x ∈ Finset.range N, a ^ (N - x) * (N.choose x : ℂ) * t ^ x :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

/- English proof (translation)
Establish `hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0` using `Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t`. Use `congrArg (fun p => Polynomial.coeff p i) hp` as an intermediate fact. Simplify `this` using `[Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj]`.
-/
theorem coeff_eq_zero_of_forall_eval_eq_zero {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by
  classical
  have hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0 :=
    Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t
  have := congrArg (fun p => Polynomial.coeff p i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj] using this

/- English proof (translation)
The claim follows from `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt z`.
-/
theorem analyticAt_coord {ι : Type} [Fintype ι] (i : ι) (z : ι → ℂ) :
    AnalyticAt ℂ (fun w : ι → ℂ => w i) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt z

/- English proof (translation)
Take `⟨K₀, K, hK⟩` from `exists_monic_shift_coeff N (u₀ k)`. Take `⟨K', hK'⟩` from `exists_shift_coeff N (-u₀ k)`. Set `ι : σ → Option (Fin d ⊕ {m // m ≠ k})` to `fun m => if hm : m = k then none else some (Sum.inr ⟨m, hm⟩)`. Set `φ : (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) → (Fin d → ℂ) × (σ → ℂ)` to `fun z => (fun i => y₀ i + z (some (Sum.inl i)), fun m => u₀ m + z (ι m))`. Set `ψ' : (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → (Fin d ⊕ {m // m ≠ k} → ℂ)` to `fun x' l => Sum.elim (fun i => x'.1 i - y₀ i) (fun m => x'.2 m - u₀ m) l`.

Set `ψ : (Fin d → ℂ) × (σ → ℂ) → (Option (Fin d ⊕ {m // m ≠ k}) → ℂ)` to `fun x o => Option.elim o (x.2 k - u₀ k) (ψ' (x.1, fun m => x.2 m))`. Set `c : Fin N → (Fin d ⊕ {m // m ≠ k} → ℂ) → ℂ` to `fun i w => K₀ i + ∑ j, b j (fun l => y₀ l + w (Sum.inl l)) * K i j`. Establish `hc_an : ∀ i, AnalyticAt ℂ (c i) 0`. Introduce `i`. Establish `hy : AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => fun l => y₀ l + w (Sum.inl l)) 0` using `AnalyticAt.pi (f := fun l (w : Fin d ⊕ {m // m ≠ k} → ℂ) => y₀ l + w (Sum.inl l)) fun l => analyticAt_const.add (analyticAt_coord (Sum.inl l) 0)`.

Establish `hb' : ∀ j, AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => b j (fun l => y₀ l + w (Sum.inl l))) 0`. Introduce `j`. Use `(hb j).comp_of_eq hy ?_` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules.

Conclude with `analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => (hb' j).fun_mul analyticAt_const)`. Establish `hc0 : ∀ i, c i 0 = 0`. Use `coeff_eq_zero_of_forall_eval_eq_zero (fun i => c i 0) fun t => ?_` and prove the remaining obligations. Establish `h1` using `hK (fun j => b j y₀) t`. Establish `h2` using `hG (t + u₀ k)`.

Establish `hy : (fun l => y₀ l + (0 : Fin d ⊕ {m // m ≠ k} → ℂ) (Sum.inl l)) = y₀` using `by funext l; simp`. Simplify using `only [c, hy]`. Rewrite `h2` using `[add_sub_cancel_right]`. Take the linear combination `h1.symm.trans h2`. Establish `hφ : AnalyticAt ℂ φ 0` using `(AnalyticAt.pi (f := fun i (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => y₀ i + z (some (Sum.inl i))) fun i => analyticAt_const.add (analyticAt_coord _ 0)).prod (AnalyticAt.pi (f := fun m (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => u₀ m + z (ι m)) fun m => analyticAt_const.add (analy …`.

Establish `hφ0 : φ 0 = (y₀, u₀)`. Simplify using `[φ]`. Establish `hφψ : ∀ x, φ (ψ x) = x`. Introduce `x`. Use `Prod.ext (funext fun i => ?_) (funext fun m => ?_)` and prove the remaining obligations.

Simplify using `[φ, ψ, ψ']`. Distinguish the cases in `hm : m = k`. Substitute `hm` using the available equality. Simplify using `[φ, ψ, ι]`. Simplify using `[φ, ψ, ψ', ι, hm]`.

Establish `hψ' : AnalyticAt ℂ ψ' (y₀, fun m => u₀ m)`. Rewrite using `[analyticAt_pi_iff]`. Introduce `l`. Consider the cases of `l with`. Consider the case `inl i => exact ((analyticAt_coord i _).comp analyticAt_fst).sub analyticAt_const`.

Consider the case `inr m => exact ((analyticAt_coord m _).comp analyticAt_snd).sub analyticAt_const`. Establish `hψ'0 : ψ' (y₀, fun m => u₀ m) = 0`. Apply the tactic sequence `funext l; cases l <;> simp [ψ']`. Establish `hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀)` using `analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m) fun m => (analyticAt_coord _ _).comp analyticAt_snd)`. Establish `hψ : AnalyticAt ℂ ψ (y₀, u₀)`.

Rewrite using `[analyticAt_pi_iff]`. Introduce `o`. Consider the cases of `o with`. Consider the case `none => exact ((analyticAt_coord k _).comp analyticAt_snd).sub analyticAt_const`. Consider the case `some l => exact (analyticAt_coord l _).comp (hψ'.comp_of_eq hπ rfl)`.

Establish `hψ0 : ψ (y₀, u₀) = 0`. Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `none => simp [ψ]`. Consider the case `some l => simp only [ψ, Option.elim_some]`.

Conclude with `congrFun hψ'0 l`. Establish `hg : AnalyticAt ℂ (f ∘ φ) 0` using `hf.comp_of_eq hφ hφ0`. Take `⟨q, a, hq, ha, hev⟩` from `h _ N c (f ∘ φ) hc_an hc0 hg`. Use `⟨q ∘ ψ, fun i x' => ∑ j, a j (ψ' x') * K' i j, hq.comp_of_eq hψ hψ0, fun i => ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.analyticAt_fun_sum _ fun j _ => ((ha j).comp_of_eq hψ' hψ'0).fun_mul analyticAt_const`.

Establish `ht : Tendsto ψ (𝓝 (y₀, u₀)) (𝓝 0)` using `hψ0 ▸ hψ.continuousAt.tendsto filter_upwards [ht.eventually hev] with x hx`. Rewrite `hx` using `[Function.comp_apply, hφψ]`. Rewrite using `[hx]`. Establish `hy : (fun l => y₀ l + ψ x (some (Sum.inl l))) = x.1` using `by funext l; simp [ψ, ψ']`. Establish `hc' : ∀ i, c i (fun l => ψ x (some l)) = K₀ i + ∑ j, b j x.1 * K i j`.

Introduce `i`. Simplify using `only [c]`. Rewrite using `[hy]`. Establish `h1` using `hK (fun j => b j x.1) (x.2 k - u₀ k)`. Rewrite `h1` using `[sub_add_cancel]`.

Establish `hn : ψ x none = x.2 k - u₀ k` using `rfl`. Establish `hw : weierstrassPolynomial c (ψ x) = x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)`. Unfold `weierstrassPolynomial`. Simplify using `only [hc', hn]`. Conclude with `h1.symm`.

Establish `hr` using `hK' (fun j => a j (ψ' (x.1, fun m => x.2 m))) (x.2 k)`. Rewrite `hr` using `[← sub_eq_add_neg]`. Rewrite using `[hw, Function.comp_apply, ← hr]`. Both sides reduce to the same expression.
-/
theorem weierstrassDivision_in_coordinate (h : WeierstrassPolynomialDivision.Statement)
    {σ : Type} [Fintype σ] [DecidableEq σ] (k : σ) (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (N : ℕ)
    (b : Fin N → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) y₀)
    (hG : ∀ T : ℂ, T ^ N + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u₀ k) ^ N)
    (hf : AnalyticAt ℂ f (y₀, u₀)) :
    ∃ (q : (Fin d → ℂ) × (σ → ℂ) → ℂ) (e : Fin N → (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → ℂ),
      AnalyticAt ℂ q (y₀, u₀) ∧ (∀ i, AnalyticAt ℂ (e i) (y₀, fun m => u₀ m)) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀), f x = q x * (x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)) +
        ∑ i, e i (x.1, fun m => x.2 m) * x.2 k ^ (i : ℕ) := by
  obtain ⟨K₀, K, hK⟩ := exists_monic_shift_coeff N (u₀ k)
  obtain ⟨K', hK'⟩ := exists_shift_coeff N (-u₀ k)

  let ι : σ → Option (Fin d ⊕ {m // m ≠ k}) := fun m =>
    if hm : m = k then none else some (Sum.inr ⟨m, hm⟩)

  let φ : (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) → (Fin d → ℂ) × (σ → ℂ) := fun z =>
    (fun i => y₀ i + z (some (Sum.inl i)), fun m => u₀ m + z (ι m))

  let ψ' : (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → (Fin d ⊕ {m // m ≠ k} → ℂ) := fun x' l =>
    Sum.elim (fun i => x'.1 i - y₀ i) (fun m => x'.2 m - u₀ m) l
  let ψ : (Fin d → ℂ) × (σ → ℂ) → (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) := fun x o =>
    Option.elim o (x.2 k - u₀ k) (ψ' (x.1, fun m => x.2 m))

  let c : Fin N → (Fin d ⊕ {m // m ≠ k} → ℂ) → ℂ := fun i w =>
    K₀ i + ∑ j, b j (fun l => y₀ l + w (Sum.inl l)) * K i j
  have hc_an : ∀ i, AnalyticAt ℂ (c i) 0 := by
    intro i
    have hy : AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => fun l => y₀ l + w (Sum.inl l)) 0 :=
      AnalyticAt.pi (f := fun l (w : Fin d ⊕ {m // m ≠ k} → ℂ) => y₀ l + w (Sum.inl l)) fun l =>
        analyticAt_const.add (analyticAt_coord (Sum.inl l) 0)
    have hb' : ∀ j, AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => b j (fun l => y₀ l + w (Sum.inl l))) 0 := by
      intro j
      refine (hb j).comp_of_eq hy ?_
      funext l; simp
    exact analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => (hb' j).fun_mul analyticAt_const)
  have hc0 : ∀ i, c i 0 = 0 := by
    refine coeff_eq_zero_of_forall_eval_eq_zero (fun i => c i 0) fun t => ?_
    have h1 := hK (fun j => b j y₀) t
    have h2 := hG (t + u₀ k)
    have hy : (fun l => y₀ l + (0 : Fin d ⊕ {m // m ≠ k} → ℂ) (Sum.inl l)) = y₀ := by funext l; simp
    simp only [c, hy]
    rw [add_sub_cancel_right] at h2
    linear_combination h1.symm.trans h2
  have hφ : AnalyticAt ℂ φ 0 :=
    (AnalyticAt.pi (f := fun i (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => y₀ i + z (some (Sum.inl i))) fun i =>
      analyticAt_const.add (analyticAt_coord _ 0)).prod
    (AnalyticAt.pi (f := fun m (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => u₀ m + z (ι m)) fun m => analyticAt_const.add (analyticAt_coord _ 0))
  have hφ0 : φ 0 = (y₀, u₀) := by
    simp [φ]
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    refine Prod.ext (funext fun i => ?_) (funext fun m => ?_)
    · simp [φ, ψ, ψ']
    · by_cases hm : m = k
      · subst hm; simp [φ, ψ, ι]
      · simp [φ, ψ, ψ', ι, hm]
  have hψ' : AnalyticAt ℂ ψ' (y₀, fun m => u₀ m) := by
    rw [analyticAt_pi_iff]
    intro l
    cases l with
    | inl i => exact ((analyticAt_coord i _).comp analyticAt_fst).sub analyticAt_const
    | inr m => exact ((analyticAt_coord m _).comp analyticAt_snd).sub analyticAt_const
  have hψ'0 : ψ' (y₀, fun m => u₀ m) = 0 := by
    funext l; cases l <;> simp [ψ']
  have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
    analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m) fun m =>
      (analyticAt_coord _ _).comp analyticAt_snd)
  have hψ : AnalyticAt ℂ ψ (y₀, u₀) := by
    rw [analyticAt_pi_iff]
    intro o
    cases o with
    | none => exact ((analyticAt_coord k _).comp analyticAt_snd).sub analyticAt_const
    | some l => exact (analyticAt_coord l _).comp (hψ'.comp_of_eq hπ rfl)
  have hψ0 : ψ (y₀, u₀) = 0 := by
    funext o; cases o with
    | none => simp [ψ]
    | some l => simp only [ψ, Option.elim_some]; exact congrFun hψ'0 l
  have hg : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ hφ0
  obtain ⟨q, a, hq, ha, hev⟩ := h _ N c (f ∘ φ) hc_an hc0 hg
  refine ⟨q ∘ ψ, fun i x' => ∑ j, a j (ψ' x') * K' i j, hq.comp_of_eq hψ hψ0, fun i => ?_, ?_⟩
  · exact Finset.analyticAt_fun_sum _ fun j _ => ((ha j).comp_of_eq hψ' hψ'0).fun_mul analyticAt_const
  · have ht : Tendsto ψ (𝓝 (y₀, u₀)) (𝓝 0) := hψ0 ▸ hψ.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with x hx
    rw [Function.comp_apply, hφψ] at hx
    rw [hx]
    have hy : (fun l => y₀ l + ψ x (some (Sum.inl l))) = x.1 := by funext l; simp [ψ, ψ']
    have hc' : ∀ i, c i (fun l => ψ x (some l)) = K₀ i + ∑ j, b j x.1 * K i j := by
      intro i; simp only [c]; rw [hy]
    have h1 := hK (fun j => b j x.1) (x.2 k - u₀ k)
    rw [sub_add_cancel] at h1
    have hn : ψ x none = x.2 k - u₀ k := rfl
    have hw : weierstrassPolynomial c (ψ x) = x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ) := by
      unfold weierstrassPolynomial
      simp only [hc', hn]
      exact h1.symm
    have hr := hK' (fun j => a j (ψ' (x.1, fun m => x.2 m))) (x.2 k)
    rw [← sub_eq_add_neg] at hr
    rw [hw, Function.comp_apply, ← hr]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
