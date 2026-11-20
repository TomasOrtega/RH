import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal ContDiff

noncomputable section
namespace GlobalTheory.WeakHolFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def SmoothLines (f : GAd σ J → ℂ) : Prop :=
  ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod)

/- English proof (translation)
Introduce `k γ hγ g` and use `(hf k γ hγ g).add (hh k γ hγ g)`.
-/
theorem smoothLines_add {f h : GAd σ J → ℂ} (hf : SmoothLines σ J f) (hh : SmoothLines σ J h) :
    SmoothLines σ J (f + h) := fun k γ hγ g => (hf k γ hγ g).add (hh k γ hγ g)

/- English proof (translation)
Introduce `k γ hγ g` and use `(hf k γ hγ g).const_smul c`.
-/
theorem smoothLines_smul {f : GAd σ J → ℂ} (c : ℂ) (hf : SmoothLines σ J f) :
    SmoothLines σ J (c • f) := fun k γ hγ g => (hf k γ hγ g).const_smul c

/- English proof (translation)
Introduce `_ _ _ _` and use `contDiff_const`.
-/
theorem smoothLines_zero : SmoothLines σ J (0 : GAd σ J → ℂ) := fun _ _ _ _ => contDiff_const

/- English proof (translation)
Establish `h1` using `(hf 1 (fun _ => γ) (fun _ => hγ) g).differentiable (by simp)`. Establish `h2 : Differentiable ℝ fun t : ℝ => (fun _ : Fin 1 => t)` using `differentiable_pi.2 fun _ => differentiable_id`. Use `h1.comp h2` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.
-/
theorem differentiable_line {f : GAd σ J → ℂ} (hf : SmoothLines σ J f) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (g : GAd σ J) : Differentiable ℝ fun t => f (g * γ t) := by
  have h1 := (hf 1 (fun _ => γ) (fun _ => hγ) g).differentiable (by simp)
  have h2 : Differentiable ℝ fun t : ℝ => (fun _ : Fin 1 => t) := differentiable_pi.2 fun _ => differentiable_id
  have := h1.comp h2
  simpa [Function.comp_def] using this

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [lineDer, Pi.add_apply]`. Conclude with `deriv_add (differentiable_line hf hγ g 0) (differentiable_line hh hγ g 0)`.
-/
theorem lineDer_add {f h : GAd σ J → ℂ} (hf : SmoothLines σ J f) (hh : SmoothLines σ J h) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : lineDer γ (f + h) = lineDer γ f + lineDer γ h := by
  funext g
  simp only [lineDer, Pi.add_apply]
  exact deriv_add (differentiable_line hf hγ g 0) (differentiable_line hh hγ g 0)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [lineDer, Pi.smul_apply, smul_eq_mul]`. Conclude with `congrFun (deriv_const_mul_field' (𝕜 := ℝ) (v := fun t => f (g * γ t)) c) 0`.
-/
theorem lineDer_smul (c : ℂ) (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) : lineDer γ (c • f) = c • lineDer γ f := by
  funext g
  simp only [lineDer, Pi.smul_apply, smul_eq_mul]
  exact congrFun (deriv_const_mul_field' (𝕜 := ℝ) (v := fun t => f (g * γ t)) c) 0

/- English proof (translation)
Introduce `k γ hγ g`. Set `γ' : Fin (k + 1) → ℝ → GAd σ J` to `Fin.snoc (α := fun _ => ℝ → GAd σ J) γ γ₀`. Establish `hγ' : ∀ i, IsRealLine σ J (γ' i)` using `fun i => by`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify `hγ₀` using `[γ']`.

Simplify `hγ j` using `[γ']`. Establish `hΦ` using `hf (k + 1) γ' hγ' g`. Establish `hsn : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α` using `fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by`. Use `contDiff_pi.2 fun i => ?_` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using contDiff_snd`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `(contDiff_apply ℝ ℝ j).comp contDiff_fst`. Set `Ψ : (Fin k → ℝ) × ℝ → ℂ` to `fun p => f (g * (List.ofFn fun i => γ i (p.1 i)).prod * γ₀ p.2)`. Establish `hΨe : Ψ = (fun t' : Fin (k + 1) → ℝ => f (g * (List.ofFn fun i => γ' i (t' i)).prod)) ∘ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α` using `fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by`.

Use function extensionality and compare the values at `p`. Simplify using `only [Ψ, Function.comp_apply]`. Rewrite using `[List.ofFn_succ']`. Simplify using `[γ', List.prod_concat, mul_assoc]`. Establish `hΨ : ContDiff ℝ ∞ Ψ` using `hΨe ▸ hΦ.comp hsn`.

Establish `key : ∀ t : Fin k → ℝ, lineDer γ₀ f (g * (List.ofFn fun i => γ i (t i)).prod) = fderiv ℝ Ψ (t, 0) ((0 : Fin k → ℝ), (1 : ℝ))` using `fun t => by`. Establish `hd : HasFDerivAt Ψ (fderiv ℝ Ψ (t, 0)) (t, 0)` using `((hΨ.differentiable (by simp)) _).hasFDerivAt`. Establish `hl : HasDerivAt (fun s : ℝ => (t, s)) ((0 : Fin k → ℝ), (1 : ℝ)) 0` using `(hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id 0)`. Conclude with `(hd.comp_hasDerivAt 0 hl).deriv`. Simplify using `only [key]`.

Establish `h2 : ContDiff ℝ ∞ (fderiv ℝ Ψ)` using `hΨ.fderiv_right (m := ∞) (by simp)`. Conclude with `(h2.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const`.
-/
theorem smoothLines_lineDer {f : GAd σ J → ℂ} (hf : SmoothLines σ J f) {γ₀ : ℝ → GAd σ J}
    (hγ₀ : IsRealLine σ J γ₀) : SmoothLines σ J (lineDer γ₀ f) := by
  intro k γ hγ g
  let γ' : Fin (k + 1) → ℝ → GAd σ J := Fin.snoc (α := fun _ => ℝ → GAd σ J) γ γ₀
  have hγ' : ∀ i, IsRealLine σ J (γ' i) := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [γ'] using hγ₀
    · simpa [γ'] using hγ j
  have hΦ := hf (k + 1) γ' hγ' g
  have hsn : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
  let Ψ : (Fin k → ℝ) × ℝ → ℂ := fun p => f (g * (List.ofFn fun i => γ i (p.1 i)).prod * γ₀ p.2)
  have hΨe : Ψ = (fun t' : Fin (k + 1) → ℝ => f (g * (List.ofFn fun i => γ' i (t' i)).prod)) ∘
      (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    funext p
    simp only [Ψ, Function.comp_apply]
    rw [List.ofFn_succ']
    simp [γ', List.prod_concat, mul_assoc]
  have hΨ : ContDiff ℝ ∞ Ψ := hΨe ▸ hΦ.comp hsn
  have key : ∀ t : Fin k → ℝ, lineDer γ₀ f (g * (List.ofFn fun i => γ i (t i)).prod) =
      fderiv ℝ Ψ (t, 0) ((0 : Fin k → ℝ), (1 : ℝ)) := fun t => by
    have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (t, 0)) (t, 0) :=
      ((hΨ.differentiable (by simp)) _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => (t, s)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id 0)
    exact (hd.comp_hasDerivAt 0 hl).deriv
  simp only [key]
  have h2 : ContDiff ℝ ∞ (fderiv ℝ Ψ) := hΨ.fderiv_right (m := ∞) (by simp)
  exact (h2.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

/- English proof (translation)
The claim follows from `| [], _ => hf | γ :: l, hl => smoothLines_lineDer (smoothLines_foldr hf l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)) (hl γ List.mem_cons_self)`.
-/
theorem smoothLines_foldr {f : GAd σ J → ℂ} (hf : SmoothLines σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → SmoothLines σ J (l.foldr lineDer f)
  | [], _ => hf
  | γ :: l, hl => smoothLines_lineDer (smoothLines_foldr hf l fun γ' h => hl γ' (List.mem_cons_of_mem _ h))
      (hl γ List.mem_cons_self)

/- English proof (translation)
The claim follows from `| [], _ => rfl | γ :: l, hl => by have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h) rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add hf hh l hl'] exact lineDer_add (smoothLines_foldr hf l hl') (smoothLines_foldr hh l hl') (hl γ …`.
-/
theorem foldr_add {f h : GAd σ J → ℂ} (hf : SmoothLines σ J f) (hh : SmoothLines σ J h) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (f + h) = l.foldr lineDer f + l.foldr lineDer h
  | [], _ => rfl
  | γ :: l, hl => by
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add hf hh l hl']
    exact lineDer_add (smoothLines_foldr hf l hl') (smoothLines_foldr hh l hl') (hl γ List.mem_cons_self)

/- English proof (translation)
The claim follows from `| [] => rfl | γ :: l => by rw [List.foldr_cons, List.foldr_cons, foldr_smul c f l, lineDer_smul]`.
-/
theorem foldr_smul (c : ℂ) (f : GAd σ J → ℂ) :
    ∀ l : List (ℝ → GAd σ J), l.foldr lineDer (c • f) = c • l.foldr lineDer f
  | [] => rfl
  | γ :: l => by rw [List.foldr_cons, List.foldr_cons, foldr_smul c f l, lineDer_smul]

/- English proof (translation)
Introduce `l` and use `by simpa using foldr_smul (0 : ℂ) (0 : GAd σ J → ℂ) l`.
-/
theorem foldr_zero : ∀ l : List (ℝ → GAd σ J), l.foldr lineDer (0 : GAd σ J → ℂ) = 0 := fun l => by
  simpa using foldr_smul (0 : ℂ) (0 : GAd σ J → ℂ) l

/- English proof (translation)
Rewrite using `[lp.norm_eq_tsum_rpow (by simp)]; simp`.
-/
theorem norm_lp_one (a : lp (fun _ : ℕ => ℂ) 1) : ‖a‖ = ∑' n, ‖a n‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

/- English proof (translation)
Simplify using `using (lp.memℓp a).summable (by simp)`.
-/
theorem summable_lp_one (a : lp (fun _ : ℕ => ℂ) 1) : Summable fun n => ‖a n‖ := by
  simpa using (lp.memℓp a).summable (by simp)

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded ((summable_lp_one a).mul_right M) fun n => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)`.
-/
theorem summable_pair (a : lp (fun _ : ℕ => ℂ) 1) {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) :
    Summable fun n => a n * y n :=
  Summable.of_norm_bounded ((summable_lp_one a).mul_right M) fun n => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)

/- English proof (translation)
Rewrite using `[norm_lp_one]`. Use `tsum_of_norm_bounded ((summable_lp_one a).hasSum.mul_right M) fun n => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)`.
-/
theorem norm_pair_le (a : lp (fun _ : ℕ => ℂ) 1) {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) :
    ‖∑' n, a n * y n‖ ≤ ‖a‖ * M := by
  rw [norm_lp_one]
  refine tsum_of_norm_bounded ((summable_lp_one a).hasSum.mul_right M) fun n => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)

def pairLin {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) : lp (fun _ : ℕ => ℂ) 1 →ₗ[ℂ] ℂ where
  toFun a := ∑' n, a n * y n
  map_add' a b := by
    have e : ∀ n, (a + b : lp (fun _ : ℕ => ℂ) 1) n * y n = a n * y n + b n * y n := fun n => by
      rw [lp.coeFn_add, Pi.add_apply, add_mul]
    simp only [e]
    exact (summable_pair a hy).tsum_add (summable_pair b hy)
  map_smul' c a := by
    have e : ∀ n, (c • a : lp (fun _ : ℕ => ℂ) 1) n * y n = c * (a n * y n) := fun n => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    simp only [e, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

def pairCLM {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] ℂ :=
  (pairLin hy).mkContinuous M fun a => by rw [mul_comm]; exact norm_pair_le a hy

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairCLM_apply {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) (a : lp (fun _ : ℕ => ℂ) 1) :
    pairCLM hy a = ∑' n, a n * y n := rfl

/- English proof (translation)
Rewrite using `[pairCLM_apply, lp.coeFn_single, tsum_eq_single n (fun m hm => by simp [Pi.single_apply, hm])]`. Simplify using the standard rewrite rules.
-/
theorem pairCLM_single {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) (n : ℕ) :
    pairCLM hy (lp.single 1 n 1) = y n := by
  rw [pairCLM_apply, lp.coeFn_single, tsum_eq_single n (fun m hm => by simp [Pi.single_apply, hm])]
  simp

/- English proof (translation)
Use `choose M hM using hx`. Establish `hT : ∀ a, ∃ K, ∀ i, ‖pairCLM (hM i) a‖ ≤ K` using `fun a => by`. Take `⟨K, hK⟩` from `h a`. Conclude with `⟨K, fun i => by rw [pairCLM_apply]; exact hK i⟩`. Take `⟨C, hC⟩` from `banach_steinhaus hT`.

Use `⟨C, fun i n => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖lp.single (E` using `fun _ : ℕ => ℂ) 1 n 1‖ = 1 := by`. Rewrite using `[lp.norm_single (E := fun _ : ℕ => ℂ) (p := 1) (by norm_num) n (1 : ℂ), norm_one]`. Establish `h2` using `(pairCLM (hM i)).le_opNorm (lp.single (E := fun _ : ℕ => ℂ) 1 n 1)`. Rewrite `h2` using `[pairCLM_single, h1, mul_one]`.

Conclude with `h2.trans (hC i)`.
-/
theorem bdd_of_pair {ι : Type} (x : ι → ℕ → ℂ) (hx : ∀ i, ∃ M, ∀ n, ‖x i n‖ ≤ M)
    (h : ∀ a : lp (fun _ : ℕ => ℂ) 1, ∃ K, ∀ i, ‖∑' n, a n * x i n‖ ≤ K) : ∃ M, ∀ i n, ‖x i n‖ ≤ M := by
  choose M hM using hx
  have hT : ∀ a, ∃ K, ∀ i, ‖pairCLM (hM i) a‖ ≤ K := fun a => by
    obtain ⟨K, hK⟩ := h a
    exact ⟨K, fun i => by rw [pairCLM_apply]; exact hK i⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hT
  refine ⟨C, fun i n => ?_⟩
  have h1 : ‖lp.single (E := fun _ : ℕ => ℂ) 1 n 1‖ = 1 := by
    rw [lp.norm_single (E := fun _ : ℕ => ℂ) (p := 1) (by norm_num) n (1 : ℂ), norm_one]
  have h2 := (pairCLM (hM i)).le_opNorm (lp.single (E := fun _ : ℕ => ℂ) 1 n 1)
  rw [pairCLM_single, h1, mul_one] at h2
  exact h2.trans (hC i)

/- English proof (translation)
Establish `hp : ∀ k m, 1 ≤ h k ^ m` using `fun k m => one_le_pow₀ (h1 k)`. Establish `hB : 0 ≤ B` using `nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hy 0)) (by linarith [hp 0 N])`. Rewrite using `[norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith [hp n n]), ← div_eq_mul_inv, div_le_iff₀ (by linarith [hp n n])]`. Use `(hy n).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Use `mul_le_mul_of_nonneg_left ?_ hB` and prove the remaining obligations. Establish `hs : 0 ≤ ∑ k ∈ Finset.range N, h k ^ N` using `Finset.sum_nonneg fun k _ => by linarith [hp k N]`. Break down `le_or_gt N n with hn | hn` into its components or cases. Establish `: h n ^ N ≤ h n ^ n` using `pow_le_pow_right₀ (h1 n) hn`. Use polynomial arithmetic with `[hp n n]`.

Establish `h3 : h n ^ N ≤ ∑ k ∈ Finset.range N, h k ^ N` using `Finset.single_le_sum (f := fun k => h k ^ N) (fun k _ => by linarith [hp k N]) (Finset.mem_range.2 hn)`. Use polynomial arithmetic with `[hp n n, hp n N]`.
-/
theorem norm_div_pow_le {h : ℕ → ℝ} (h1 : ∀ n, 1 ≤ h n) {y : ℕ → ℂ} {B : ℝ} {N : ℕ}
    (hy : ∀ n, ‖y n‖ ≤ B * h n ^ N) (n : ℕ) :
    ‖y n * ((h n ^ n : ℝ) : ℂ)⁻¹‖ ≤ B * (1 + ∑ k ∈ Finset.range N, h k ^ N) := by
  have hp : ∀ k m, 1 ≤ h k ^ m := fun k m => one_le_pow₀ (h1 k)
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hy 0)) (by linarith [hp 0 N])
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith [hp n n]),
    ← div_eq_mul_inv, div_le_iff₀ (by linarith [hp n n])]
  refine (hy n).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hB
  have hs : 0 ≤ ∑ k ∈ Finset.range N, h k ^ N := Finset.sum_nonneg fun k _ => by linarith [hp k N]
  rcases le_or_gt N n with hn | hn
  · have : h n ^ N ≤ h n ^ n := pow_le_pow_right₀ (h1 n) hn
    nlinarith [hp n n]
  · have h3 : h n ^ N ≤ ∑ k ∈ Finset.range N, h k ^ N :=
      Finset.single_le_sum (f := fun k => h k ^ N) (fun k _ => by linarith [hp k N]) (Finset.mem_range.2 hn)
    nlinarith [hp n n, hp n N]

variable (σ J) in

def smoothSub : Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | SmoothLines σ J f}
  add_mem' hf hh := smoothLines_add hf hh
  zero_mem' := smoothLines_zero
  smul_mem' c _ hf := smoothLines_smul c hf

def wordEval (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : GAd σ J) : smoothSub σ J →ₗ[ℂ] ℂ where
  toFun f := l.foldr lineDer (f : GAd σ J → ℂ) g
  map_add' f h := by
    simp only [Submodule.coe_add, foldr_add f.2 h.2 l hl, Pi.add_apply]
  map_smul' c f := by
    simp only [Submodule.coe_smul, foldr_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/- English proof (translation)
Take `⟨μ, hμ⟩` from `LinearMap.exists_extend (wordEval l hl g)`. Establish `hv : ∀ f, SmoothLines σ J f → μ f = l.foldr lineDer f g` using `fun f hf => LinearMap.congr_fun hμ ⟨f, hf⟩`. Use `⟨μ, fun N => ⟨[l], (height σ J g : ℝ) ^ N, by simpa using hl, fun f hf _ hS => ?_⟩, hv⟩` and prove the remaining obligations. Rewrite using `[hv f hf.smooth]`. Conclude with `hS l (List.mem_singleton_self _) g`.
-/
theorem exists_isModerateForm_word (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : GAd σ J) :
    ∃ μ, IsModerateForm σ J μ ∧ ∀ f, SmoothLines σ J f → μ f = l.foldr lineDer f g := by
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (wordEval l hl g)
  have hv : ∀ f, SmoothLines σ J f → μ f = l.foldr lineDer f g := fun f hf =>
    LinearMap.congr_fun hμ ⟨f, hf⟩
  refine ⟨μ, fun N => ⟨[l], (height σ J g : ℝ) ^ N, by simpa using hl, fun f hf _ hS => ?_⟩, hv⟩
  rw [hv f hf.smooth]
  exact hS l (List.mem_singleton_self _) g

def wseq (l : List (ℝ → GAd σ J)) (f : GAd σ J → ℂ) (g : ℕ → GAd σ J) (k : ℕ) : ℂ :=
  l.foldr lineDer f (g k) * ((((height σ J (g k) : ℝ)) ^ k : ℝ) : ℂ)⁻¹

def seqSub (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : ℕ → GAd σ J) :
    Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | SmoothLines σ J f ∧ ∃ M, ∀ k, ‖wseq l f g k‖ ≤ M}
  add_mem' := by
    rintro f h ⟨hf, M, hM⟩ ⟨hh, M', hM'⟩
    refine ⟨smoothLines_add hf hh, M + M', fun k => ?_⟩
    have e : wseq l (f + h) g k = wseq l f g k + wseq l h g k := by
      simp only [wseq, foldr_add hf hh l hl, Pi.add_apply, add_mul]
    rw [e]; exact (norm_add_le _ _).trans (add_le_add (hM k) (hM' k))
  zero_mem' := ⟨smoothLines_zero, 0, fun k => by simp [wseq, foldr_zero]⟩
  smul_mem' := by
    rintro c f ⟨hf, M, hM⟩
    refine ⟨smoothLines_smul c hf, ‖c‖ * M, fun k => ?_⟩
    have e : wseq l (c • f) g k = c * wseq l f g k := by
      simp only [wseq, foldr_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [e, norm_mul]; exact mul_le_mul_of_nonneg_left (hM k) (norm_nonneg _)

def seqLin (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : ℕ → GAd σ J)
    (a : lp (fun _ : ℕ => ℂ) 1) : seqSub l hl g →ₗ[ℂ] ℂ where
  toFun f := ∑' k, a k * wseq l (f : GAd σ J → ℂ) g k
  map_add' f h := by
    obtain ⟨hf, M, hM⟩ := f.2
    obtain ⟨hh, M', hM'⟩ := h.2
    have e : ∀ k, a k * wseq l ((f + h : seqSub l hl g) : GAd σ J → ℂ) g k =
        a k * wseq l (f : GAd σ J → ℂ) g k + a k * wseq l (h : GAd σ J → ℂ) g k := fun k => by
      simp only [Submodule.coe_add, wseq, foldr_add hf hh l hl, Pi.add_apply, add_mul, mul_add]
    simp only [e]
    exact (summable_pair a hM).tsum_add (summable_pair a hM')
  map_smul' c f := by
    have e : ∀ k, a k * wseq l ((c • f : seqSub l hl g) : GAd σ J → ℂ) g k =
        c * (a k * wseq l (f : GAd σ J → ℂ) g k) := fun k => by
      simp only [Submodule.coe_smul, wseq, foldr_smul, Pi.smul_apply, smul_eq_mul]; ring
    simp only [e, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/- English proof (translation)
Take `⟨μ, hμ⟩` from `LinearMap.exists_extend (seqLin l hl g a)`. Establish `hv : ∀ f ∈ seqSub l hl g, μ f = ∑' k, a k * wseq l f g k` using `fun f hf => LinearMap.congr_fun hμ ⟨f, hf⟩`. Establish `h1 : ∀ k, 1 ≤ (height σ J (g k) : ℝ)` using `fun k => by exact_mod_cast one_le_height σ J (g k)`. Use `⟨μ, fun N => ⟨[l], ‖a‖ * (1 * (1 + ∑ k ∈ Finset.range N, (height σ J (g k) : ℝ) ^ N)), by simpa using hl, fun f hf _ hS => ?_⟩, hv⟩` and prove the remaining obligations. Establish `hb : ∀ k, ‖wseq l f g k‖ ≤ 1 * (1 + ∑ k ∈ Finset.range N, (height σ J (g k) : ℝ) ^ N)` using `norm_div_pow_le h1 (y := fun k => l.foldr lineDer f (g k)) (fun k => by`.

Rewrite using `[one_mul]`. Conclude with `hS l (List.mem_singleton_self _) (g k))`. Rewrite using `[hv f ⟨hf.smooth, _, hb⟩]`. Conclude with `norm_pair_le a hb`.
-/
theorem exists_isModerateForm_seq (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : ℕ → GAd σ J)
    (a : lp (fun _ : ℕ => ℂ) 1) :
    ∃ μ, IsModerateForm σ J μ ∧ ∀ f ∈ seqSub l hl g, μ f = ∑' k, a k * wseq l f g k := by
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (seqLin l hl g a)
  have hv : ∀ f ∈ seqSub l hl g, μ f = ∑' k, a k * wseq l f g k := fun f hf =>
    LinearMap.congr_fun hμ ⟨f, hf⟩
  have h1 : ∀ k, 1 ≤ (height σ J (g k) : ℝ) := fun k => by exact_mod_cast one_le_height σ J (g k)
  refine ⟨μ, fun N => ⟨[l], ‖a‖ * (1 * (1 + ∑ k ∈ Finset.range N, (height σ J (g k) : ℝ) ^ N)),
    by simpa using hl, fun f hf _ hS => ?_⟩, hv⟩
  have hb : ∀ k, ‖wseq l f g k‖ ≤ 1 * (1 + ∑ k ∈ Finset.range N, (height σ J (g k) : ℝ) ^ N) :=
    norm_div_pow_le h1 (y := fun k => l.foldr lineDer f (g k)) (fun k => by
      rw [one_mul]; exact hS l (List.mem_singleton_self _) (g k))
  rw [hv f ⟨hf.smooth, _, hb⟩]
  exact norm_pair_le a hb

end GlobalTheory.WeakHolFamily

namespace GlobalTheory.WeakHolFamily

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J H U D _ hD hDU hH hμ l hl`. Use `⟨fun g => ?_, ?_⟩` and prove the remaining obligations. Take `⟨μ, hμm, hμv⟩` from `exists_isModerateForm_word l hl g`. Conclude with `(hμ μ hμm).congr fun s hs => (hμv _ (hH s hs).smooth).symm`. Assume the negation of the conclusion as `hcon push_neg at hcon choose s hs g hg using fun k : ℕ => hcon k k`.

Establish `h1 : ∀ k, 1 ≤ (height σ J (g k) : ℝ)` using `fun k => by exact_mod_cast one_le_height σ J (g k)`. Set `x : ℕ → ℕ → ℂ` to `fun m k => wseq l (H (s m)) g k`. Establish `hx : ∀ m, ∃ M, ∀ k, ‖x m k‖ ≤ M` using `fun m => by`. Take `⟨N, hN⟩` from `(hH _ (hDU (hs m))).growth`. Take `⟨B, hB⟩` from `hN l hl`.

Conclude with `⟨_, norm_div_pow_le h1 (y := fun k => l.foldr lineDer (H (s m)) (g k)) (fun k => hB (g k))⟩`. Establish `hpair : ∀ a : lp (fun _ : ℕ => ℂ) 1, ∃ K, ∀ m, ‖∑' k, a k * x m k‖ ≤ K` using `fun a => by`. Take `⟨μ, hμm, hμv⟩` from `exists_isModerateForm_seq l hl g a`. Establish `hc : ContinuousOn (fun s => μ (H s)) D` using `((hμ μ hμm).mono hDU).continuousOn`. Take `⟨K, hK⟩` from `hD.exists_bound_of_continuousOn hc`.

Use `⟨K, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[← hμv _ ⟨(hH _ (hDU (hs m))).smooth, hx m⟩]`. Conclude with `hK _ (hs m)`. Take `⟨M, hM⟩` from `bdd_of_pair x hx hpair`. Take `⟨k, hk⟩` from `exists_nat_gt M`.

Establish `hpos : 0 < (height σ J (g k) : ℝ) ^ k` using `pow_pos (by linarith [h1 k]) k`. Establish `hlt : (k : ℝ) < ‖x k k‖`. Simplify using `only [x, wseq]`. Rewrite using `[norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← div_eq_mul_inv, lt_div_iff₀ hpos]`. Conclude with `hg k`.

Combine the linear relations using `[hM k k]`.
-/
theorem word_holomorphic_and_uniform :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
      (J : Matrix (Fin n) (Fin n) E) (H : ℂ → GAd σ J → ℂ) (U D : Set ℂ), IsOpen U → IsCompact D → D ⊆ U →
      (∀ s ∈ U, IsSmoothModerate σ J (H s)) →
      (∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) →
      ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        (∀ g, DifferentiableOn ℂ (fun s => l.foldr lineDer (H s) g) U) ∧
        ∃ (N : ℕ) (C : ℝ), ∀ s ∈ D, ∀ g, ‖l.foldr lineDer (H s) g‖ ≤ C * (height σ J g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ n J H U D _ hD hDU hH hμ l hl
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨μ, hμm, hμv⟩ := exists_isModerateForm_word l hl g
    exact (hμ μ hμm).congr fun s hs => (hμv _ (hH s hs).smooth).symm
  · by_contra hcon
    push_neg at hcon
    choose s hs g hg using fun k : ℕ => hcon k k
    have h1 : ∀ k, 1 ≤ (height σ J (g k) : ℝ) := fun k => by exact_mod_cast one_le_height σ J (g k)
    let x : ℕ → ℕ → ℂ := fun m k => wseq l (H (s m)) g k
    have hx : ∀ m, ∃ M, ∀ k, ‖x m k‖ ≤ M := fun m => by
      obtain ⟨N, hN⟩ := (hH _ (hDU (hs m))).growth
      obtain ⟨B, hB⟩ := hN l hl
      exact ⟨_, norm_div_pow_le h1 (y := fun k => l.foldr lineDer (H (s m)) (g k)) (fun k => hB (g k))⟩
    have hpair : ∀ a : lp (fun _ : ℕ => ℂ) 1, ∃ K, ∀ m, ‖∑' k, a k * x m k‖ ≤ K := fun a => by
      obtain ⟨μ, hμm, hμv⟩ := exists_isModerateForm_seq l hl g a
      have hc : ContinuousOn (fun s => μ (H s)) D := ((hμ μ hμm).mono hDU).continuousOn
      obtain ⟨K, hK⟩ := hD.exists_bound_of_continuousOn hc
      refine ⟨K, fun m => ?_⟩
      rw [← hμv _ ⟨(hH _ (hDU (hs m))).smooth, hx m⟩]
      exact hK _ (hs m)
    obtain ⟨M, hM⟩ := bdd_of_pair x hx hpair
    obtain ⟨k, hk⟩ := exists_nat_gt M
    have hpos : 0 < (height σ J (g k) : ℝ) ^ k := pow_pos (by linarith [h1 k]) k
    have hlt : (k : ℝ) < ‖x k k‖ := by
      simp only [x, wseq]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← div_eq_mul_inv,
        lt_div_iff₀ hpos]
      exact hg k
    linarith [hM k k]

end GlobalTheory.WeakHolFamily
