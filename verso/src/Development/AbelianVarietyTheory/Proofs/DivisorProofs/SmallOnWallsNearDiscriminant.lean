import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnWallsDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallSetCompactDominantStatement

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly.WallNear

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Conclude with `⟨1, zero_le_one, fun v e _ h => by simpa using h s⟩`. Consider the case `zero => exact ⟨0, le_rfl, fun v e _ _ => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨C, hC, h1⟩` from `hx`. Take `⟨D, hD, h2⟩` from `hy`. Use `⟨C + D, by positivity, fun v e he h => ?_⟩` and prove the remaining obligations. Use `h1 v e he h` as an intermediate fact.

Use `h2 v e he h` as an intermediate fact. Use `abs_add_le (x v) (y v)` as an intermediate fact. Simplify using `only [LinearMap.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `smul a x _ hx`.

Take `⟨C, hC, h1⟩` from `hx`. Use `⟨|a| * C, by positivity, fun v e he h => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (h1 v e he h) (abs_nonneg a)`.
-/
theorem bound_of_mem_span {V S : Type*} [AddCommGroup V] [Module ℝ V] (φ : S → V →ₗ[ℝ] ℝ)
    (f : V →ₗ[ℝ] ℝ) (hf : f ∈ Submodule.span ℝ (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V) (e : ℝ), 0 ≤ e → (∀ s, |φ s v| ≤ e) → |f v| ≤ C * e := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun v e _ h => by simpa using h s⟩
  | zero => exact ⟨0, le_rfl, fun v e _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, by positivity, fun v e he h => ?_⟩
    have := h1 v e he h
    have := h2 v e he h
    have := abs_add_le (x v) (y v)
    simp only [LinearMap.add_apply]
    linarith
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨|a| * C, by positivity, fun v e he h => ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 v e he h) (abs_nonneg a)

/- English proof (translation)
Use `haveI := Fintype.ofFinite M`. Use `set K : Submodule ℝ V := ⨅ s, LinearMap.ker (φ s) with hK`. Take `⟨p, hp⟩` from `K.subtype.exists_leftInverse_of_injective K.ker_subtype`. Establish `hmem : ∀ m, (ψ m) ∘ₗ (LinearMap.id - K.subtype ∘ₗ p) ∈ Submodule.span ℝ (Set.range φ)`. Introduce `m`.

Apply `FiniteDimensional.mem_span_of_iInf_ker_le_ker` to reduce the goal to its premises. Introduce `v hv`. Use `LinearMap.congr_fun hp ⟨v, hv⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this`. Simplify using `[this]`.

Use `choose C hC0 hC using fun m => bound_of_mem_span φ _ (hmem m)`. Establish `hs : 0 ≤ ∑ m, C m` using `Finset.sum_nonneg fun m _ => hC0 m`. Use `⟨∑ m, C m + 1, by linarith, fun v e he h => ⟨p v, fun s => ?_, fun m => ?_⟩⟩` and prove the remaining obligations. Use `(p v).2` as an intermediate fact. Conclude with `(Submodule.mem_iInf _).1 this s`.

Establish `h1` using `hC m v e he h`. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, Submodule.subtype_apply, LinearMap.id_apply] at h1`. Establish `h2 : C m ≤ ∑ m, C m` using `Finset.single_le_sum (fun m _ => hC0 m) (Finset.mem_univ m)`. Use `h1.trans (mul_le_mul_of_nonneg_right (by linarith) he)` and prove the remaining obligations.
-/
theorem near_kernel {V S M : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [Finite M]
    (φ : S → V →ₗ[ℝ] ℝ) (ψ : M → V →ₗ[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : V) (e : ℝ), 0 ≤ e → (∀ s, |φ s v| ≤ e) →
      ∃ u : V, (∀ s, φ s u = 0) ∧ ∀ m, |ψ m (v - u)| ≤ C * e := by
  classical
  haveI := Fintype.ofFinite M
  set K : Submodule ℝ V := ⨅ s, LinearMap.ker (φ s) with hK
  obtain ⟨p, hp⟩ := K.subtype.exists_leftInverse_of_injective K.ker_subtype
  have hmem : ∀ m, (ψ m) ∘ₗ (LinearMap.id - K.subtype ∘ₗ p) ∈ Submodule.span ℝ (Set.range φ) := by
    intro m
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have := LinearMap.congr_fun hp ⟨v, hv⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    simp [this]
  choose C hC0 hC using fun m => bound_of_mem_span φ _ (hmem m)
  have hs : 0 ≤ ∑ m, C m := Finset.sum_nonneg fun m _ => hC0 m
  refine ⟨∑ m, C m + 1, by linarith, fun v e he h => ⟨p v, fun s => ?_, fun m => ?_⟩⟩
  · have := (p v).2
    exact (Submodule.mem_iInf _).1 this s
  · have h1 := hC m v e he h
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Submodule.subtype_apply,
      LinearMap.id_apply] at h1
    have h2 : C m ≤ ∑ m, C m := Finset.single_le_sum (fun m _ => hC0 m) (Finset.mem_univ m)
    refine h1.trans (mul_le_mul_of_nonneg_right (by linarith) he)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def VanNear (P : Pol ι N) (τ : ι) (a b : Fin N) : Prop :=
  ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧ (∃ x ∈ U, x τ a = x τ b) ∧
    ∀ x ∈ U, x τ a = x τ b → ev x P = 0

/- English proof (translation)
Take `⟨U, hU, ⟨x, hx, hxe⟩, hv⟩` from `h`. Set `T : (ι → Fin N → ℝ) → (ι → Fin N → ℝ)` to `fun y t i => y (swapAt τ c d (t, i)).1 (swapAt τ c d (t, i)).2`. Establish `hT : Continuous T`. Use `continuous_pi fun t => continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `(continuous_apply _).comp (continuous_apply _)`.

Establish `hTT : ∀ y, T (T y) = y`. Introduce `y`. Use function extensionality and compare the values at `t i`. Apply the tactic sequence `by_cases ht : t = τ <;> simp [T, swapAt, ht]`. Establish `hTτ : ∀ y i, T y τ i = y τ (Equiv.swap c d i)`.

Introduce `y i`. Simplify using `[T, swapAt]`. Use `⟨T ⁻¹' U, hU.preimage hT, ⟨T x, by simpa [hTT] using hx, ?_⟩, fun y hy hye => ?_⟩` and prove the remaining obligations. Rewrite using `[← hTτ (T x), ← hTτ (T x), hTT]`. Conclude with `hxe`.

Establish `h1` using `hv (T y) hy (by rw [hTτ, hTτ]; exact hye)`. Establish `h2 : ev (T y) P = ev y (rename (swapAt τ c d) P)`. Unfold `ev`. Rewrite using `[eval_rename]`. Both sides reduce to the same expression.

Rewrite `h1` using `[h2, hP]`. Simplify `h1` using `[ev]`.
-/
theorem vanNear_swap {P : Pol ι N} {τ : ι} {a b : Fin N} (c d : Fin N)
    (hP : rename (swapAt τ c d) P = -P) (h : VanNear P τ a b) :
    VanNear P τ (Equiv.swap c d a) (Equiv.swap c d b) := by
  obtain ⟨U, hU, ⟨x, hx, hxe⟩, hv⟩ := h
  let T : (ι → Fin N → ℝ) → (ι → Fin N → ℝ) :=
    fun y t i => y (swapAt τ c d (t, i)).1 (swapAt τ c d (t, i)).2
  have hT : Continuous T := by
    refine continuous_pi fun t => continuous_pi fun i => ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hTT : ∀ y, T (T y) = y := by
    intro y; funext t i
    by_cases ht : t = τ <;> simp [T, swapAt, ht]
  have hTτ : ∀ y i, T y τ i = y τ (Equiv.swap c d i) := by
    intro y i; simp [T, swapAt]
  refine ⟨T ⁻¹' U, hU.preimage hT, ⟨T x, by simpa [hTT] using hx, ?_⟩, fun y hy hye => ?_⟩
  · rw [← hTτ (T x), ← hTτ (T x), hTT]; exact hxe
  · have h1 := hv (T y) hy (by rw [hTτ, hTτ]; exact hye)
    have h2 : ev (T y) P = ev y (rename (swapAt τ c d) P) := by
      unfold ev
      rw [eval_rename]; rfl
    rw [h2, hP] at h1
    simpa [ev] using h1

/- English proof (translation)
Establish `h1 : ∀ k (a : Fin N), (a : ℕ) + k + 1 = j → VanNear P τ a ⟨j, hjN⟩`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a ha`.

Establish `: a = ⟨j - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[this]`. Conclude with `h`. Consider the case `succ k ih`. Introduce `a ha`.

Use `vanNear_swap a ⟨a + 1, by omega⟩ (hP τ _ _ rfl (by simp; omega)) (ih ⟨a + 1, by omega⟩ (by simp; omega))` as an intermediate fact. Rewrite `this` using `[Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)]`. Then use the resulting hypothesis. Establish `h2 : ∀ k (b : Fin N), (b : ℕ) = j + k → VanNear P τ a b`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `b hb`. Establish `: b = ⟨j, hjN⟩` using `Fin.ext (by simpa using hb)`. Rewrite using `[this]; exact h1 (j - 1 - a) a (by omega)`. Consider the case `succ k ih`.

Introduce `b hb`. Establish `hlt` using `b.isLt`. Use `vanNear_swap ⟨j + k, by omega⟩ b (hP τ _ _ (by simp; omega) (by omega)) (ih ⟨j + k, by omega⟩ rfl)` as an intermediate fact. Rewrite `this` using `[Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)]`. Then use the resulting hypothesis. Conclude with `h2 (b - j) b (by omega)`.
-/
theorem vanNear_all {j : ℕ} (hj : 1 ≤ j) (hjN : j < N) {P : Pol ι N} (hP : AntiL j P) (τ : ι)
    (h : VanNear P τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩) (a b : Fin N) (ha : (a : ℕ) < j)
    (hb : j ≤ (b : ℕ)) : VanNear P τ a b := by
  have h1 : ∀ k (a : Fin N), (a : ℕ) + k + 1 = j → VanNear P τ a ⟨j, hjN⟩ := by
    intro k
    induction k with
    | zero =>
      intro a ha
      have : a = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact h
    | succ k ih =>
      intro a ha
      have := vanNear_swap a ⟨a + 1, by omega⟩ (hP τ _ _ rfl (by simp; omega))
        (ih ⟨a + 1, by omega⟩ (by simp; omega))
      rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne
        (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)] at this
  have h2 : ∀ k (b : Fin N), (b : ℕ) = j + k → VanNear P τ a b := by
    intro k
    induction k with
    | zero =>
      intro b hb
      have : b = ⟨j, hjN⟩ := Fin.ext (by simpa using hb)
      rw [this]; exact h1 (j - 1 - a) a (by omega)
    | succ k ih =>
      intro b hb
      have hlt := b.isLt
      have := vanNear_swap ⟨j + k, by omega⟩ b (hP τ _ _ (by simp; omega) (by omega))
        (ih ⟨j + k, by omega⟩ rfl)
      rwa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
        (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)] at this
  exact h2 (b - j) b (by omega)

noncomputable def antiSub (ι : Type) [Fintype ι] [DecidableEq ι] (N j n : ℕ) : Submodule ℝ (Pol ι N) where
  carrier := {P | P.IsHomogeneous n ∧ AntiL j P}
  add_mem' := fun {P Q} hP hQ => ⟨hP.1.add hQ.1, fun τ a b h1 h2 => by
    rw [map_add, hP.2 τ a b h1 h2, hQ.2 τ a b h1 h2, neg_add]⟩
  zero_mem' := ⟨isHomogeneous_zero _ _ _, fun τ a b _ _ => by simp⟩
  smul_mem' := fun c P hP => ⟨(homogeneousSubmodule (ι × Fin N) ℝ n).smul_mem c hP.1,
    fun τ a b h1 h2 => by rw [map_smul, hP.2 τ a b h1 h2, smul_neg]⟩

/- English proof (translation)
The claim follows from `((Finsupp.finite_of_degree_le (σ := ι × Fin N) n).subset (fun m (hm : m.degree = n) => hm.le)).to_subtype`.
-/
theorem finite_deg (n : ℕ) : Finite {m : (ι × Fin N) →₀ ℕ // m.degree = n} :=
  ((Finsupp.finite_of_degree_le (σ := ι × Fin N) n).subset
    (fun m (hm : m.degree = n) => hm.le)).to_subtype

/- English proof (translation)
Use `haveI := finite_deg (ι := ι) (N := N) n`. Set `L : antiSub ι N j n →ₗ[ℝ] ({m : (ι × Fin N) →₀ ℕ // m.degree = n} → ℝ)` to `LinearMap.pi fun m => lcoeff ℝ m.1 ∘ₗ (antiSub ι N j n).subtype`. Use `FiniteDimensional.of_injective L ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `P hP`.

Use extensionality with `m`. Distinguish the cases in `hm : m.degree = n`. Simplify `congrFun hP ⟨m, hm⟩` using `[L]`. Simplify using `using P.2.1.coeff_eq_zero hm`.
-/
theorem finiteDimensional_antiSub (j n : ℕ) : FiniteDimensional ℝ (antiSub ι N j n) := by
  haveI := finite_deg (ι := ι) (N := N) n
  let L : antiSub ι N j n →ₗ[ℝ] ({m : (ι × Fin N) →₀ ℕ // m.degree = n} → ℝ) :=
    LinearMap.pi fun m => lcoeff ℝ m.1 ∘ₗ (antiSub ι N j n).subtype
  refine FiniteDimensional.of_injective L ?_
  rw [injective_iff_map_eq_zero]
  intro P hP
  ext m
  by_cases hm : m.degree = n
  · simpa [L] using congrFun hP ⟨m, hm⟩
  · simpa using P.2.1.coeff_eq_zero hm

/- English proof (translation)
Introduce `ι _ _ N j hj hjN`. Use `set n := dimFl ι N + 1 with hn`. Use `haveI := finite_deg (ι := ι) (N := N) n`. Use `haveI := finiteDimensional_antiSub (ι := ι) (N := N) j n`. Take `⟨C, hC, H⟩` from `near_kernel (V := antiSub ι N j n) (S := Σ τ : ι, wallSet (N := N) j τ (1 / (4 * (N : ℝ)))) (M := {m : (ι × Fin N) →₀ ℕ // m.degree = n}) (fun s => (aeval (R := ℝ) (fun x : ι × Fin N => s.2.1 x.1 x.2)).toLinearMap ∘ₗ (antiSub ι N j n).subtype) (fun m => lcoeff ℝ m.1 ∘ₗ (antiSub ι …`.

Use `⟨C, hC, fun P e he hP hA hs => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hb⟩` from `H ⟨P, hP, hA⟩ e he (fun s => by`. Simplify `hs s.1 s.2.1 s.2.2)` using `[ev, aeval_eq_eval]`. Establish `hu' : ∀ τ, ∀ lam ∈ wallSet (N` using `N) j τ (1 / (4 * (N : ℝ))), ev lam u.1 = 0 := by`. Introduce `τ lam hl`.

Simplify `hu ⟨τ, lam, hl⟩` using `[ev, aeval_eq_eval]`. Take `⟨al, be, hab⟩` from `GlobalTheory.T.vanishing_on_walls_divisible ι N j u.1 u.2.1 u.2.2 (fun τ a b ha hb => by`. Use `vanNear_all hj hjN u.2.2 τ ?_ a b ha hb` and prove the remaining obligations. Take `⟨-, -, U, hU, ⟨x, hx, hg⟩, hw⟩` from `GlobalTheory.T.wall_set_compact_dominant ι N j τ hj hjN`. Use `⟨U, hU, ⟨x, hx, hg _ _ (by simp; omega) rfl⟩, fun y hy hye => hu' τ y (hw y hy ?_)⟩` and prove the remaining obligations.

Introduce `c d h1 h2`. Establish `hc : c = ⟨j - 1, lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩` using `Fin.ext (by simp; omega)`. Establish `hd : d = ⟨j, hjN⟩` using `Fin.ext h2`. Rewrite using `[hc, hd]`. Conclude with `hye)`.

Use `⟨al, be, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[← hab]`. Distinguish the cases in `hm : m.degree = n`. Simplify using `using hb ⟨m, hm⟩`. Rewrite using `[(hP.sub u.2.1).coeff_eq_zero hm, abs_zero]`.

Check the signs of the components of the expression.
-/
theorem near_discriminant_multiple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 < C ∧ ∀ (P : Pol ι N) (e : ℝ), 0 ≤ e → P.IsHomogeneous (dimFl ι N + 1) → AntiL j P → (∀ τ, ∀ lam ∈ wallSet (N := N) j τ (1 / (4 * (N : ℝ))), |ev lam P| ≤ e) → ∃ al be : ι → ℝ, CoefLe (P - delPol ι N * invForm j al be) (C * e) := by
  intro ι _ _ N j hj hjN
  set n := dimFl ι N + 1 with hn
  haveI := finite_deg (ι := ι) (N := N) n
  haveI := finiteDimensional_antiSub (ι := ι) (N := N) j n
  obtain ⟨C, hC, H⟩ := near_kernel (V := antiSub ι N j n)
    (S := Σ τ : ι, wallSet (N := N) j τ (1 / (4 * (N : ℝ))))
    (M := {m : (ι × Fin N) →₀ ℕ // m.degree = n})
    (fun s => (aeval (R := ℝ) (fun x : ι × Fin N => s.2.1 x.1 x.2)).toLinearMap ∘ₗ (antiSub ι N j n).subtype)
    (fun m => lcoeff ℝ m.1 ∘ₗ (antiSub ι N j n).subtype)
  refine ⟨C, hC, fun P e he hP hA hs => ?_⟩
  obtain ⟨u, hu, hb⟩ := H ⟨P, hP, hA⟩ e he (fun s => by
    simpa [ev, aeval_eq_eval] using hs s.1 s.2.1 s.2.2)
  have hu' : ∀ τ, ∀ lam ∈ wallSet (N := N) j τ (1 / (4 * (N : ℝ))), ev lam u.1 = 0 := by
    intro τ lam hl
    simpa [ev, aeval_eq_eval] using hu ⟨τ, lam, hl⟩
  obtain ⟨al, be, hab⟩ := GlobalTheory.T.vanishing_on_walls_divisible ι N j u.1 u.2.1 u.2.2 (fun τ a b ha hb => by
    refine vanNear_all hj hjN u.2.2 τ ?_ a b ha hb
    obtain ⟨-, -, U, hU, ⟨x, hx, hg⟩, hw⟩ := GlobalTheory.T.wall_set_compact_dominant ι N j τ hj hjN
    refine ⟨U, hU, ⟨x, hx, hg _ _ (by simp; omega) rfl⟩, fun y hy hye => hu' τ y (hw y hy ?_)⟩
    intro c d h1 h2
    have hc : c = ⟨j - 1, lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩ := Fin.ext (by simp; omega)
    have hd : d = ⟨j, hjN⟩ := Fin.ext h2
    rw [hc, hd]; exact hye)
  refine ⟨al, be, fun m => ?_⟩
  rw [← hab]
  by_cases hm : m.degree = n
  · simpa using hb ⟨m, hm⟩
  · rw [(hP.sub u.2.1).coeff_eq_zero hm, abs_zero]; positivity

end GlobalTheory.FlagPoly.WallNear
