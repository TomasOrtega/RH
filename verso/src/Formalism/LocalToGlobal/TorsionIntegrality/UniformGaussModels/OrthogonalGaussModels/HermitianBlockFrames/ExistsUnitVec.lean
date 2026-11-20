import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocAbs

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `i`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `ht`. Conclude with `S.O.zero_mem`.
-/
theorem IntV_single (j : ι) {t : K} (ht : t ∈ S.O) : S.IntV (Pi.single j t) := by
  intro i
  rw [Pi.single_apply]
  split_ifs
  · exact ht
  · exact S.O.zero_mem

/- English proof (translation)
Introduce `i` and use `S.O.add_mem (hx i) (hy i)`.
-/
theorem IntV_add {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x + y) := fun i => S.O.add_mem (hx i) (hy i)

/- English proof (translation)
Introduce `i` and use `S.O.sub_mem (hx i) (hy i)`.
-/
theorem IntV_sub {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x - y) := fun i => S.O.sub_mem (hx i) (hy i)

/- English proof (translation)
Introduce `i` and use `S.O.mul_mem hc (hx i)`.
-/
theorem IntV_smul {x : ι → K} {c : K} (hc : c ∈ S.O) (hx : S.IntV x) : S.IntV (c • x) := fun i => S.O.mul_mem hc (hx i)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `show S.σ (x k + y k) = S.σ (x k) + S.σ (y k)`. Conclude with `map_add _ _ _`.
-/
theorem cv_add (x y : ι → K) : S.cv (x + y) = S.cv x + S.cv y := by
  funext k
  show S.σ (x k + y k) = S.σ (x k) + S.σ (y k)
  exact map_add _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `show S.σ (x k - y k) = S.σ (x k) - S.σ (y k)`. Conclude with `map_sub _ _ _`.
-/
theorem cv_sub (x y : ι → K) : S.cv (x - y) = S.cv x - S.cv y := by
  funext k
  show S.σ (x k - y k) = S.σ (x k) - S.σ (y k)
  exact map_sub _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `show S.σ (c * x k) = S.σ c * S.σ (x k)`. Conclude with `map_mul _ _ _`.
-/
theorem cv_smul (c : K) (x : ι → K) : S.cv (c • x) = S.σ c • S.cv x := by
  funext k
  show S.σ (c * x k) = S.σ c * S.σ (x k)
  exact map_mul _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `show S.σ ((Pi.single j t : ι → K) k) = (Pi.single j (S.σ t) : ι → K) k`. Rewrite using `[Pi.single_apply, Pi.single_apply]`. Use `split_ifs`. Both sides reduce to the same expression.

Conclude with `map_zero _`.
-/
theorem cv_single (j : ι) (t : K) : S.cv (Pi.single j t) = Pi.single j (S.σ t) := by
  funext k
  show S.σ ((Pi.single j t : ι → K) k) = (Pi.single j (S.σ t) : ι → K) k
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs
  · rfl
  · exact map_zero _

/- English proof (translation)
Unfold `hf`. Rewrite using `[cv_add, add_dotProduct]`.
-/
theorem hf_add_left (Γ : Matrix ι ι K) (x x' y : ι → K) : S.hf Γ (x + x') y = S.hf Γ x y + S.hf Γ x' y := by
  unfold hf
  rw [cv_add, add_dotProduct]

/- English proof (translation)
Unfold `hf`. Rewrite using `[mulVec_add, dotProduct_add]`.
-/
theorem hf_add_right (Γ : Matrix ι ι K) (x y y' : ι → K) : S.hf Γ x (y + y') = S.hf Γ x y + S.hf Γ x y' := by
  unfold hf
  rw [mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `hf`. Rewrite using `[cv_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem hf_smul_left (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ (c • x) y = S.σ c * S.hf Γ x y := by
  unfold hf
  rw [cv_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `hf`. Rewrite using `[mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hf_smul_right (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ x (c • y) = c * S.hf Γ x y := by
  unfold hf
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use `show ∑ k, Γ i k * (Pi.single j t : ι → K) k = Γ i j * t`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same]`. Introduce `k _ hk`. Rewrite using `[Pi.single_eq_of_ne hk, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
private theorem mulVec_single_apply_hermitian_block_frames (Γ : Matrix ι ι K) (i j : ι) (t : K) :
    (Γ *ᵥ Pi.single j t) i = Γ i j * t := by
  show ∑ k, Γ i k * (Pi.single j t : ι → K) k = Γ i j * t
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Unfold `hf`. Rewrite using `[cv_single, ← mulVec_single_apply_hermitian_block_frames Γ i j t]`. Use `show ∑ k, (Pi.single i (S.σ s) : ι → K) k * (Γ *ᵥ Pi.single j t) k = _`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Pi.single_eq_same]`.

Introduce `k _ hk`. Rewrite using `[Pi.single_eq_of_ne hk, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem hf_single (Γ : Matrix ι ι K) (i j : ι) (s t : K) :
    S.hf Γ (Pi.single i s) (Pi.single j t) = S.σ s * (Γ i j * t) := by
  unfold hf
  rw [cv_single, ← mulVec_single_apply_hermitian_block_frames Γ i j t]
  show ∑ k, (Pi.single i (S.σ s) : ι → K) k * (Γ *ᵥ Pi.single j t) k = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, Γ i j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Apply `h0` to reduce the goal to its premises. Use extensionality with `a b`. Simplify using `[h a b]`. Establish `hdiv : ∀ x : ι → K, S.IntV x → ∀ k, S.NU ((Γ *ᵥ x) k)`. Introduce `x hx k`.

Use `show S.NU (∑ l, Γ k l * x l)`. Apply `S.NU_sum` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[mul_comm]`. Conclude with `S.NU_mul (hx l) (hcon k l)`.

Establish `key : ∀ N : ℕ, ∃ x', S.IntV x' ∧ Γ *ᵥ Pi.single j (1 : K) = S.p ^ N • (Γ *ᵥ x')`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => exact ⟨Pi.single j 1, S.IntV_single j S.O.one_mem, by rw [pow_zero, one_smul]⟩`. Consider the case `succ n ih`.

Take `⟨x', hx', hx'eq⟩` from `ih`. Take `⟨x'', hx'', he⟩` from `hU x' hx' (hdiv x' hx')`. Use `⟨x'', hx'', ?_⟩` and prove the remaining obligations. Rewrite using `[hx'eq, he, smul_smul, pow_succ]`. Take `⟨N, hN⟩` from `S.hsep _ (hΓ i j) hij`.

Take `⟨x', hx', heq⟩` from `key N`. Apply `hN` to reduce the goal to its premises. Use `⟨(Γ *ᵥ x') i, S.IntV_mulVec hΓ hx' i, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun heq i`. Rewrite `h1` using `[Pi.smul_apply, smul_eq_mul, mulVec_single_apply_hermitian_block_frames, mul_one]`.

Conclude with `h1`.
-/
theorem exists_not_NU {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ i j, ¬ S.NU (Γ i j) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, j, hij⟩ : ∃ i j, Γ i j ≠ 0 := by
    by_contra h
    push Not at h
    apply h0
    ext a b
    simp [h a b]
  have hdiv : ∀ x : ι → K, S.IntV x → ∀ k, S.NU ((Γ *ᵥ x) k) := by
    intro x hx k
    show S.NU (∑ l, Γ k l * x l)
    apply S.NU_sum
    intro l _
    rw [mul_comm]
    exact S.NU_mul (hx l) (hcon k l)
  have key : ∀ N : ℕ, ∃ x', S.IntV x' ∧
      Γ *ᵥ Pi.single j (1 : K) = S.p ^ N • (Γ *ᵥ x') := by
    intro N
    induction N with
    | zero => exact ⟨Pi.single j 1, S.IntV_single j S.O.one_mem, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      obtain ⟨x', hx', hx'eq⟩ := ih
      obtain ⟨x'', hx'', he⟩ := hU x' hx' (hdiv x' hx')
      refine ⟨x'', hx'', ?_⟩
      rw [hx'eq, he, smul_smul, pow_succ]
  obtain ⟨N, hN⟩ := S.hsep _ (hΓ i j) hij
  obtain ⟨x', hx', heq⟩ := key N
  apply hN
  refine ⟨(Γ *ᵥ x') i, S.IntV_mulVec hΓ hx' i, ?_⟩
  have h1 := congrFun heq i
  rw [Pi.smul_apply, smul_eq_mul, mulVec_single_apply_hermitian_block_frames, mul_one] at h1
  exact h1

/- English proof (translation)
Establish `key : ∀ (v : ι → K) (k : ι), S.IntV v → v k = 1 → S.hf Γ v v ∈ S.O → S.σ (S.hf Γ v v) = S.hf Γ v v → ¬ S.NU (S.hf Γ v v) → ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1`. Introduce `v k hv hk hO hσ hn`. Establish `hu0 : S.hf Γ v v ≠ 0`. Introduce `hz`. Apply `hn` to reduce the goal to its premises.

Unfold `NU`. Conclude with `⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩`. Establish `hinvO : (S.hf Γ v v)⁻¹ ∈ S.O` using `S.hinv _ hO hn`. Establish `hinvσ : S.σ (S.hf Γ v v)⁻¹ = (S.hf Γ v v)⁻¹`. Rewrite using `[map_inv₀, hσ]`.

Establish `hinvn : ¬ ∃ y ∈ S.O, (S.hf Γ v v)⁻¹ = S.p * y`. Introduce and unpack `⟨y, hy, hyeq⟩`. Apply `S.hone` to reduce the goal to its premises. Use `⟨y * S.hf Γ v v, S.O.mul_mem hy hO, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hyeq, inv_mul_cancel₀ hu0]`.

Take `⟨w, hwO, hw⟩` from `S.hnorm _ hinvO hinvσ hinvn`. Use `⟨w • v, k, S.IntV_smul hwO hv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, hk, smul_eq_mul, mul_one]`. Introduce `hwn`. Unfold `NU at hwn`.

Take `⟨y, hy, hyeq⟩` from `hwn`. Apply `hinvn` to reduce the goal to its premises. Use `⟨S.σ w * y, S.O.mul_mem (S.hσO w hwO) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw, hyeq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[S.hf_smul_left, S.hf_smul_right, ← mul_assoc, hw, inv_mul_cancel₀ hu0]`. Establish `hσ2 : S.σ 2 = 2`. Rewrite using `[← one_add_one_eq_two, map_add, map_one]`. Establish `h2O : (2 : K) ∈ S.O`. Establish `h11` using `S.O.add_mem S.O.one_mem S.O.one_mem`.

Rewrite `h11` using `[one_add_one_eq_two]`. Then use the resulting hypothesis. Establish `diag : ∀ m : ι, ¬ S.NU (Γ m m) → ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1`. Introduce `m hm`. Establish `e : S.hf Γ (Pi.single m 1) (Pi.single m 1) = Γ m m`. Rewrite using `[S.hf_single, map_one, one_mul, mul_one]`.

Use `key (Pi.single m 1) m (S.IntV_single m S.O.one_mem) (Pi.single_eq_same m 1) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `hΓ m m`. Rewrite using `[e]`. Conclude with `hH m m`.

Rewrite using `[e]`. Conclude with `hm`. Take `⟨i, j, hij⟩` from `S.exists_not_NU hΓ hU h0`. Distinguish the cases in `hi : S.NU (Γ i i)`. Use `swap`.

Conclude with `diag i hi`. Distinguish the cases in `hj : S.NU (Γ j j)`. Use `swap`. Conclude with `diag j hj`. Establish `hne : i ≠ j`.

Introduce and unpack `rfl`. Conclude with `hij hi`. Establish `ht0 : Γ i j ≠ 0`. Introduce `hz`. Apply `hij` to reduce the goal to its premises.

Unfold `NU`. Conclude with `⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩`. Establish `hcO : (Γ i j)⁻¹ ∈ S.O` using `S.hinv _ (hΓ i j) hij`. Establish `h1 : Γ i j * (Γ i j)⁻¹ = 1` using `mul_inv_cancel₀ ht0`. Establish `h2 : S.σ (Γ i j)⁻¹ * S.σ (Γ i j) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ ht0, map_one]`. Establish `hval : S.hf Γ (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) = Γ i i + 2 + S.σ (Γ i j)⁻¹ * Γ j j * (Γ i j)⁻¹`. Rewrite using `[S.hf_add_left, S.hf_add_right, S.hf_add_right, S.hf_single, S.hf_single, S.hf_single, S.hf_single, map_one, ← hH i j]`. Take the linear combination `h1 + h2`. Use `key (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) i (S.IntV_add (S.IntV_single i S.O.one_mem) (S.IntV_single j hcO)) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero]`. Rewrite using `[hval]`. Conclude with `S.O.add_mem (S.O.add_mem (hΓ i i) h2O) (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) (hΓ j j)) hcO)`. Rewrite using `[hval]`. Simplify using `only [map_add, map_mul, hH i i, hH j j, S.hσσ (Γ i j)⁻¹ hcO, hσ2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval]`. Introduce `hn`. Unfold `NU at hn hi hj`. Take `⟨y, hy, hyeq⟩` from `hn`.

Take `⟨a, ha, hae⟩` from `hi`. Take `⟨b, hb, hbe⟩` from `hj`. Rewrite `hyeq` using `[hae, hbe]`. Establish `h2inv : (2 : K)⁻¹ * 2 = 1` using `inv_mul_cancel₀ S.h2`. Apply `S.hone` to reduce the goal to its premises.

Use `⟨(y - a - S.σ (Γ i j)⁻¹ * b * (Γ i j)⁻¹) * 2⁻¹, S.O.mul_mem (S.O.sub_mem (S.O.sub_mem hy ha) (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) hb) hcO)) S.htwo, ?_⟩` and prove the remaining obligations. Take the linear combination `(2 : K)⁻¹ * hyeq - h2inv`.
-/
theorem exists_unit_vec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by

  have key : ∀ (v : ι → K) (k : ι), S.IntV v → v k = 1 → S.hf Γ v v ∈ S.O →
      S.σ (S.hf Γ v v) = S.hf Γ v v → ¬ S.NU (S.hf Γ v v) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro v k hv hk hO hσ hn
    have hu0 : S.hf Γ v v ≠ 0 := by
      intro hz
      apply hn
      unfold NU
      exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
    have hinvO : (S.hf Γ v v)⁻¹ ∈ S.O := S.hinv _ hO hn
    have hinvσ : S.σ (S.hf Γ v v)⁻¹ = (S.hf Γ v v)⁻¹ := by
      rw [map_inv₀, hσ]
    have hinvn : ¬ ∃ y ∈ S.O, (S.hf Γ v v)⁻¹ = S.p * y := by
      rintro ⟨y, hy, hyeq⟩
      apply S.hone
      refine ⟨y * S.hf Γ v v, S.O.mul_mem hy hO, ?_⟩
      rw [← mul_assoc, ← hyeq, inv_mul_cancel₀ hu0]
    obtain ⟨w, hwO, hw⟩ := S.hnorm _ hinvO hinvσ hinvn
    refine ⟨w • v, k, S.IntV_smul hwO hv, ?_, ?_⟩
    · rw [Pi.smul_apply, hk, smul_eq_mul, mul_one]
      intro hwn
      unfold NU at hwn
      obtain ⟨y, hy, hyeq⟩ := hwn
      apply hinvn
      refine ⟨S.σ w * y, S.O.mul_mem (S.hσO w hwO) hy, ?_⟩
      rw [← hw, hyeq]
      ring
    · rw [S.hf_smul_left, S.hf_smul_right, ← mul_assoc, hw, inv_mul_cancel₀ hu0]
  have hσ2 : S.σ 2 = 2 := by
    rw [← one_add_one_eq_two, map_add, map_one]
  have h2O : (2 : K) ∈ S.O := by
    have h11 := S.O.add_mem S.O.one_mem S.O.one_mem
    rwa [one_add_one_eq_two] at h11

  have diag : ∀ m : ι, ¬ S.NU (Γ m m) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro m hm
    have e : S.hf Γ (Pi.single m 1) (Pi.single m 1) = Γ m m := by
      rw [S.hf_single, map_one, one_mul, mul_one]
    refine key (Pi.single m 1) m (S.IntV_single m S.O.one_mem) (Pi.single_eq_same m 1) ?_ ?_ ?_
    · rw [e]; exact hΓ m m
    · rw [e]; exact hH m m
    · rw [e]; exact hm
  obtain ⟨i, j, hij⟩ := S.exists_not_NU hΓ hU h0
  by_cases hi : S.NU (Γ i i)
  swap
  · exact diag i hi
  by_cases hj : S.NU (Γ j j)
  swap
  · exact diag j hj

  have hne : i ≠ j := by
    rintro rfl
    exact hij hi
  have ht0 : Γ i j ≠ 0 := by
    intro hz
    apply hij
    unfold NU
    exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
  have hcO : (Γ i j)⁻¹ ∈ S.O := S.hinv _ (hΓ i j) hij
  have h1 : Γ i j * (Γ i j)⁻¹ = 1 := mul_inv_cancel₀ ht0
  have h2 : S.σ (Γ i j)⁻¹ * S.σ (Γ i j) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hval : S.hf Γ (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) =
      Γ i i + 2 + S.σ (Γ i j)⁻¹ * Γ j j * (Γ i j)⁻¹ := by
    rw [S.hf_add_left, S.hf_add_right, S.hf_add_right, S.hf_single, S.hf_single, S.hf_single,
      S.hf_single, map_one, ← hH i j]
    linear_combination h1 + h2
  refine key (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) i
    (S.IntV_add (S.IntV_single i S.O.one_mem) (S.IntV_single j hcO)) ?_ ?_ ?_ ?_
  · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero]
  · rw [hval]
    exact S.O.add_mem (S.O.add_mem (hΓ i i) h2O) (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) (hΓ j j)) hcO)
  · rw [hval]
    simp only [map_add, map_mul, hH i i, hH j j, S.hσσ (Γ i j)⁻¹ hcO, hσ2]
    ring
  · rw [hval]
    intro hn
    unfold NU at hn hi hj
    obtain ⟨y, hy, hyeq⟩ := hn
    obtain ⟨a, ha, hae⟩ := hi
    obtain ⟨b, hb, hbe⟩ := hj
    rw [hae, hbe] at hyeq
    have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ S.h2
    apply S.hone
    refine ⟨(y - a - S.σ (Γ i j)⁻¹ * b * (Γ i j)⁻¹) * 2⁻¹,
      S.O.mul_mem (S.O.sub_mem (S.O.sub_mem hy ha)
        (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) hb) hcO)) S.htwo, ?_⟩
    linear_combination (2 : K)⁻¹ * hyeq - h2inv

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
