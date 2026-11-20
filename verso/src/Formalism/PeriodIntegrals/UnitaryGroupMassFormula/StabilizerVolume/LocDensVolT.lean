import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

/- English proof (translation)
Establish `hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1`. Introduce `w hw`. Establish `h1` using `Complex.sq_norm w`. Rewrite `h1` using `[hw, Complex.normSq_apply]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1`. Introduce `w hw`. Use `hsq w hw` as an intermediate fact. Rewrite using `[sq, Complex.mul_re]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1` using `fun k => by rw [norm_pow, hz, one_pow]`. Establish `hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1` using `fun k => (Complex.re_le_norm _).trans (hn k).le`. Establish `key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2` using `by rw [pow_succ, pow_mul]`. Rewrite using `[e, hre _ (hn k)]`. Establish `h1` using `h k`.

Establish `h2` using `hle k`. Rewrite using `[pow_succ]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]`. Establish `hz1 : z.re ≤ 1` using `by simpa using hle 0`. Establish `hre1 : z.re = 1`.

Assume the negation of the conclusion as `hne`. Establish `hε : 0 < 1 - z.re`. Break down `lt_or_eq_of_le hz1 with h' | h'` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h' hne`.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)`. Establish `h1` using `key k`. Establish `h2` using `h k`. Establish `h3 : 1 < (3 : ℝ) ^ k * (1 - z.re)`. Rewrite `hk` using `[div_lt_iff₀ hε]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : z.im = 0`. Use `hsq z hz` as an intermediate fact. Rewrite `this` using `[hre1]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `Complex.ext (by simp [hre1]) (by simp [him])`.
-/
theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    nlinarith
  have hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
    intro w hw
    have := hsq w hw
    rw [sq, Complex.mul_re]
    nlinarith
  have hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hn k).le
  have key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, hre _ (hn k)]
      have h1 := h k
      have h2 := hle k
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]
  have hz1 : z.re ≤ 1 := by simpa using hle 0
  have hre1 : z.re = 1 := by
    by_contra hne
    have hε : 0 < 1 - z.re := by
      rcases lt_or_eq_of_le hz1 with h' | h'
      · linarith
      · exact absurd h' hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := key k
    have h2 := h k
    have h3 : 1 < (3 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have := hsq z hz
    rw [hre1] at this
    nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [zero_smul, pow_zero, psiV]`. Establish `: pairA F 0 (singleV F v 0) = 0`. Establish `h` using `singleV_add (F := F) v 0 0`.

Rewrite `h` using `[add_zero]`. Establish `h0 : singleV F v 0 = 0`. Use `congrArg (fun x => x - singleV F v 0) h` as an intermediate fact. Conclude with `(by simpa using this : (0 : Af F) = singleV F v 0).symm`. Rewrite using `[h0]`.

Both sides reduce to the same expression. Rewrite using `[this, AddChar.map_zero_eq_one]`. Consider the case `succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]`.
-/
theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

/- English proof (translation)
Use `set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef`. Establish `hU : IsOpen U` using `isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)`. Set `Φ : (∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F` to `fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)`. Establish `hΦ : Continuous Φ` using `continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous`. Set `x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` to `fun v => ⟨0, zero_mem _⟩`.

Establish `hx0 : Φ x0 = 0` using `by show pairA F 0 _ = 0`. Establish `: (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `j`. Both sides reduce to the same expression.

Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hx0U : x0 ∈ Φ ⁻¹' U`. Simplify using `only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one, Complex.one_re]`. Evaluate the numerical expressions.

Take `⟨I, u, hu, hsub⟩` from `isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U`. Use `filter_upwards [(I.finite_toSet).eventually_cofinite_notMem] with v hv`. Establish `hbig : ∀ y ∈ v.adicCompletionIntegers F, 1 / 2 < (psiV F ψ v y).re`. Introduce `y hy`. Establish `hmem : Function.update x0 v ⟨y, hy⟩ ∈ (I : Set _).pi u`.

Introduce `w hw`. Establish `hwv : w ≠ v` using `fun h => hv (h ▸ hw)`. Rewrite using `[Function.update_of_ne hwv]`. Conclude with `(hu w hw).2`. Establish `e : Φ (Function.update x0 v ⟨y, hy⟩) = pairA F 0 (singleV F v y)` using `by show pairA F 0 _ = _`.

Use `congr 1`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `j`. Use `show ((Function.update x0 v ⟨y, hy⟩ j : _) : Fv F j) = (Pi.single v y : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) j`. Distinguish the cases in `hj : j = v`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hj, Pi.single_eq_of_ne hj]`. Use `hsub hmem` as an intermediate fact. Simplify using `only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this`.

Conclude with `this`. Introduce `y hy`. Use `eq_one_of_pow (psiV F ψ v y) (hψ.2.1 _) ?_` and prove the remaining obligations. Introduce `k`. Rewrite using `[← psiV_nsmul]`.

Apply `hbig` to reduce the goal to its premises. Rewrite using `[nsmul_eq_mul]`. Conclude with `mul_mem (by exact_mod_cast (natCast_mem (v.adicCompletionIntegers F) (2 ^ k))) hy`.
-/
theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  filter_upwards [(I.finite_toSet).eventually_cofinite_notMem] with v hv
  have hbig : ∀ y ∈ v.adicCompletionIntegers F, 1 / 2 < (psiV F ψ v y).re := by
    intro y hy
    have hmem : Function.update x0 v ⟨y, hy⟩ ∈ (I : Set _).pi u := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hwv]
      exact (hu w hw).2
    have e : Φ (Function.update x0 v ⟨y, hy⟩) = pairA F 0 (singleV F v y) := by
      show pairA F 0 _ = _
      congr 1
      apply RestrictedProduct.ext
      intro j
      show ((Function.update x0 v ⟨y, hy⟩ j : _) : Fv F j) =
        (Pi.single v y : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) j
      by_cases hj : j = v
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have := hsub hmem
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  refine eq_one_of_pow (psiV F ψ v y) (hψ.2.1 _) ?_
  intro k
  rw [← psiV_nsmul]
  apply hbig
  rw [nsmul_eq_mul]
  exact mul_mem (by exact_mod_cast (natCast_mem (v.adicCompletionIntegers F) (2 ^ k))) hy

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

/- English proof (translation)
Introduce `F _ _ ψ hψ`. Use `filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2`. Introduce `t`. Use `⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩` and prove the remaining obligations.
-/
theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabS
