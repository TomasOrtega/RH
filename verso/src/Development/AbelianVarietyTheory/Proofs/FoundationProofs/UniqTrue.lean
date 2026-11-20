import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDiscreteInertiaKummerCoboundaryBoundStatement
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.HTCoUniq

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (π : K) : AddSubgroup K where
  carrier := {z | ‖z‖ ≤ ‖π‖}
  zero_mem' := by simp
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := fun ha => by simpa using ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ball {π z : K} : z ∈ ball π ↔ ‖z‖ ≤ ‖π‖ := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_ball, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) ha).trans hz`.
-/
theorem mul_mem_ball {π a z : K} (ha : ‖a‖ ≤ 1) (hz : z ∈ ball π) : a * z ∈ ball π := by
  rw [mem_ball, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hz

/- English proof (translation)
Use `(mem_ball.1 hz).trans ?_` and prove the remaining obligations. Rewrite using `[norm_pow, norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hp.le h`.
-/
theorem ball_pow_mono {p : K} (hp : ‖p‖ < 1) {i k : ℕ} (h : i ≤ k) {z : K} (hz : z ∈ ball (p ^ k)) : z ∈ ball (p ^ i) := by
  refine (mem_ball.1 hz).trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hp.le h

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_ball]`. Establish `h1 : 0 < ‖p ^ a‖` using `norm_pos_iff.2 (pow_ne_zero _ hp0)`. Establish `e : p ^ k = p ^ a * p ^ (k - a)` using `by rw [← pow_add, Nat.add_sub_cancel' h]`. Rewrite `hz` using `[e, norm_mul, norm_mul]`. Conclude with `le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans hz) h1`.
-/
theorem mem_ball_of_mul {p : K} (hp0 : p ≠ 0) {a k : ℕ} (h : a ≤ k) {u z : K} (hu : ‖p ^ a‖ ≤ ‖u‖)
    (hz : u * z ∈ ball (p ^ k)) : z ∈ ball (p ^ (k - a)) := by
  rw [mem_ball] at hz ⊢
  have h1 : 0 < ‖p ^ a‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  have e : p ^ k = p ^ a * p ^ (k - a) := by rw [← pow_add, Nat.add_sub_cancel' h]
  rw [e, norm_mul, norm_mul] at hz
  exact le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans hz) h1

omit [IsUltrametricDist K] in
/- English proof (translation)
Take `⟨a, ha⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 hu) hp`. Conclude with `⟨a, by rw [norm_pow]; exact ha.le⟩`.
-/
theorem exists_pow_le {p : K} (hp : ‖p‖ < 1) {u : K} (hu : u ≠ 0) : ∃ a : ℕ, ‖p ^ a‖ ≤ ‖u‖ := by
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hu) hp
  exact ⟨a, by rw [norm_pow]; exact ha.le⟩

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ K]

/- English proof (translation)
Rewrite using `[mem_ball, hn]`. Conclude with `hz`.
-/
theorem smul_mem_ball (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (g : Γ) {π z : K} (hz : z ∈ ball π) : g • z ∈ ball π := by
  rw [mem_ball, hn]; exact hz

/- English proof (translation)
Establish `e : lam t * (h • d - d) = h • (d * lam t - (t • x - x)) - (d * lam (h * t) - ((h * t) • x - x)) + (d * lam h - (h • x - x)) + d * (lam (h * t) - lam h - lam t)`. Simplify using `only [smul_sub, smul_mul', hfix, mul_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (add_mem (sub_mem (smul_mem_ball hn h h2) h3) h1) (mul_mem_ball hd hadd)`.
-/
theorem inv_mul (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) {lam : Γ → K} {π d x : K} (hd : ‖d‖ ≤ 1) {h t : Γ}
    (hfix : h • lam t = lam t) (hadd : lam (h * t) - lam h - lam t ∈ ball π)
    (h1 : d * lam h - (h • x - x) ∈ ball π) (h2 : d * lam t - (t • x - x) ∈ ball π)
    (h3 : d * lam (h * t) - ((h * t) • x - x) ∈ ball π) : lam t * (h • d - d) ∈ ball π := by
  have e : lam t * (h • d - d) = h • (d * lam t - (t • x - x)) - (d * lam (h * t) - ((h * t) • x - x)) +
      (d * lam h - (h • x - x)) + d * (lam (h * t) - lam h - lam t) := by
    simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
  rw [e]
  exact add_mem (add_mem (sub_mem (smul_mem_ball hn h h2) h3) h1) (mul_mem_ball hd hadd)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using neg_mem (hadd 1 1)`. Consider the case `succ n ih`. Establish `e : lam (s ^ (n + 1)) - ((n + 1 : ℕ) : K) * lam s = (lam (s ^ n * s) - lam (s ^ n) - lam s) + (lam (s ^ n) - n * lam s)`. Rewrite using `[pow_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (hadd _ _) ih`.
-/
theorem pow_sub_mem {lam : Γ → K} {π : K} (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π) (s : Γ) (n : ℕ) :
    lam (s ^ n) - n * lam s ∈ ball π := by
  induction n with
  | zero => simpa using neg_mem (hadd 1 1)
  | succ n ih =>
    have e : lam (s ^ (n + 1)) - ((n + 1 : ℕ) : K) * lam s =
        (lam (s ^ n * s) - lam (s ^ n) - lam s) + (lam (s ^ n) - n * lam s) := by
      rw [pow_succ]; push_cast; ring
    rw [e]; exact add_mem (hadd _ _) ih

/- English proof (translation)
Use `⟨∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d), ?_, fun s => ?_⟩` and prove the remaining obligations. Establish `: (∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d)) ∈ ball (1 : K)` using `sum_mem fun q _ => sub_mem (smul_mem_ball hn _ (by simpa [mem_ball] using hy)) (mul_mem_ball (hl _) (smul_mem_ball hn _ (by simpa [mem_ball] using hd)))`. Simplify `this` using `[mem_ball]`. Rewrite using `[← Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ H => q.out • d)] conv => enter [2, 2, 2]`. Rewrite using `[← Equiv.sum_comp (MulAction.toPerm s)]`.

Rewrite using `[Finset.smul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `sum_mem fun q _ => ?_` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H (s * q.out)`. Establish `hq : (MulAction.toPerm s q : Γ ⧸ H).out = s * q.out * h`. Rewrite using `[← hh, MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul]`.

Rewrite using `[hq]`. Use `set r := q.out`. Establish `e : (s * r * h) • d * lam s - (s • (r • y - lam r * r • d) - ((s * r * h) • y - lam (s * r * h) * (s * r * h) • d)) = - ((s * r) • (d * lam h - ((h : Γ) • y - y))) - (lam r + lam h) * (s * r) • ((h : Γ) • d - d) - (s * r * h) • d * (lam (s * r * h) - lam (s * r) - lam h) - (s * r …`. Simplify using `only [smul_sub, smul_mul', hfix, mul_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `hd' : ‖(s * r * h) • d‖ ≤ 1` using `by rw [hn]; exact hd`. Use `sub_mem (sub_mem (sub_mem (neg_mem (smul_mem_ball hn _ (h1 h h.2))) (mul_mem_ball ?_ (smul_mem_ball hn _ (h2 h h.2)))) (mul_mem_ball hd' (hadd _ _))) (mul_mem_ball hd' (hadd _ _))` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hl _) (hl _))`.
-/
theorem transfer (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (H : Subgroup Γ) [Fintype (Γ ⧸ H)] {lam : Γ → K} {π d y : K}
    (hd : ‖d‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hl : ∀ s, ‖lam s‖ ≤ 1) (hfix : ∀ g s : Γ, g • lam s = lam s)
    (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π)
    (h1 : ∀ h ∈ H, d * lam h - (h • y - y) ∈ ball π) (h2 : ∀ h ∈ H, h • d - d ∈ ball π) :
    ∃ X : K, ‖X‖ ≤ 1 ∧ ∀ s : Γ, (∑ q : Γ ⧸ H, q.out • d) * lam s - (s • X - X) ∈ ball π := by
  refine ⟨∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d), ?_, fun s => ?_⟩
  · have : (∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d)) ∈ ball (1 : K) :=
      sum_mem fun q _ => sub_mem (smul_mem_ball hn _ (by simpa [mem_ball] using hy))
        (mul_mem_ball (hl _) (smul_mem_ball hn _ (by simpa [mem_ball] using hd)))
    simpa [mem_ball] using this
  · rw [← Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ H => q.out • d)]
    conv => enter [2, 2, 2]; rw [← Equiv.sum_comp (MulAction.toPerm s)]
    rw [Finset.smul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine sum_mem fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (s * q.out)
    have hq : (MulAction.toPerm s q : Γ ⧸ H).out = s * q.out * h := by
      rw [← hh, MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul]
    rw [hq]
    set r := q.out
    have e : (s * r * h) • d * lam s - (s • (r • y - lam r * r • d) - ((s * r * h) • y - lam (s * r * h) * (s * r * h) • d)) =
        - ((s * r) • (d * lam h - ((h : Γ) • y - y))) - (lam r + lam h) * (s * r) • ((h : Γ) • d - d) -
          (s * r * h) • d * (lam (s * r * h) - lam (s * r) - lam h) - (s * r * h) • d * (lam (s * r) - lam s - lam r) := by
      simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
    rw [e]
    have hd' : ‖(s * r * h) • d‖ ≤ 1 := by rw [hn]; exact hd
    refine sub_mem (sub_mem (sub_mem (neg_mem (smul_mem_ball hn _ (h1 h h.2))) (mul_mem_ball ?_ (smul_mem_ball hn _ (h2 h h.2))))
      (mul_mem_ball hd' (hadd _ _))) (mul_mem_ball hd' (hadd _ _))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hl _) (hl _))

/- English proof (translation)
Use `haveI := Fintype.ofFinite (O →ₐ[R] K)`. Establish `hsep : ∀ φ : O →ₐ[R] K, ∃ a : O, φ ≠ O.val → (a : K) - φ a ≠ 0`. Introduce `φ`. Distinguish the cases in `h : φ = O.val`. Conclude with `⟨0, fun h' => absurd h h'⟩`.

Take `⟨a, ha⟩` from `DFunLike.ne_iff.1 h`. Conclude with `⟨a, fun _ => sub_ne_zero.2 (Ne.symm ha)⟩`. Use `choose α hα using hsep`. Use `set S : Finset (O →ₐ[R] K) := Finset.univ.erase O.val with hS`. Establish `hD : (∏ φ ∈ S, ((α φ : K) - φ (α φ))) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun φ h => hα φ (Finset.ne_of_mem_erase h)`.

Take `⟨b, hb⟩` from `exists_pow_le hp hD`. Establish `hN : (((Nat.card (O →ₐ[R] K)).factorial : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)`. Take `⟨a, ha⟩` from `exists_pow_le hp hN`. Use `⟨a + c + b + 1, ?_⟩` and prove the remaining obligations. Introduce `Γ _ _ hn hR lam m k hkm hl hfix hadd s₀ hs₀ U d y hd hy hyp`.

Distinguish the cases in `hk : k ≤ a + c + b + 1`. Rewrite using `[Nat.sub_eq_zero_of_le hk, mem_ball]`. Simplify using `using hd`. Set `H : Subgroup Γ` to `{ carrier := {h | ∀ a ∈ O, h • a = a} one_mem' := fun a _ => one_smul _ _ mul_mem' := fun {g h} hg hh a ha => by rw [mul_smul, hh a ha, hg a ha] inv_mem' := fun {g} hg a ha => by rw [inv_smul_eq_iff, hg a ha] }`. Set `e : Γ → (O →ₐ[R] K)` to `fun g => { toRingHom := (MulSemiringAction.toRingHom Γ K g).comp (O.val : O →+* K) commutes' := fun r => hR g r }`.

Establish `he : ∀ g (a : O), e g a = g • (a : K)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective fun q : Γ ⧸ H => e q.out`. Introduce `q q' hq`. Rewrite using `[← q.out_eq', ← q'.out_eq', QuotientGroup.eq]`. Introduce `a ha`.

Rewrite using `[mul_smul, inv_smul_eq_iff]`. Conclude with `(DFunLike.congr_fun hq ⟨a, ha⟩).symm`. Use `haveI : Finite (Γ ⧸ H) := Finite.of_injective _ hinj`. Use `haveI := Fintype.ofFinite (Γ ⧸ H)`. Establish `hidx : H.index ≤ Nat.card (O →ₐ[R] K)` using `Nat.card_le_card_of_injective _ hinj`.

Establish `ht : s₀ ^ (Nat.card (O →ₐ[R] K)).factorial ∈ H` using `Subgroup.pow_mem_of_index_ne_zero_of_dvd (Nat.card_pos (α := Γ ⧸ H)).ne' s₀ fun n h0 hn => Nat.dvd_factorial h0 (hn.trans hidx)`. Use `set t := s₀ ^ (Nat.card (O →ₐ[R] K)).factorial`. Establish `hlt : ‖p ^ a‖ ≤ ‖lam t‖`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `h1` using `pow_sub_mem hadd s₀ (Nat.card (O →ₐ[R] K)).factorial`. Establish `h2 : ‖p ^ m‖ < ‖p ^ a‖`. Rewrite using `[norm_pow, norm_pow]`. Conclude with `pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.2 hp0) hp (by omega)`. Establish `h3` using `IsUltrametricDist.norm_add_le_max (lam t) (-(lam t - ((Nat.card (O →ₐ[R] K)).factorial : ℕ) * lam s₀))`.

Rewrite `h3` using `[norm_neg, neg_sub, add_sub_cancel, norm_mul, hs₀, mul_one]`. Conclude with `absurd (ha.trans h3) (not_le.2 (max_lt hlt (lt_of_le_of_lt h1 h2)))`. Establish `hinv : ∀ h ∈ H, h • d - d ∈ ball (p ^ (k - a))` using `fun h hh => mem_ball_of_mul hp0 (by omega) hlt (inv_mul hn hd (hfix _ _) (ball_pow_mono hp hkm (hadd _ _)) (hyp h hh) (hyp t ht) (hyp _ (H.mul_mem hh ht)))`. Establish `hT : ∀ β ∈ O, p ^ c * ∑ q : Γ ⧸ H, q.out • (β * d) ∈ ball (p ^ (k - a))`. Introduce `β hβ`.

Establish `hβd : ‖β * d‖ ≤ 1` using `by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hd`. Establish `hβy : ‖β * y‖ ≤ 1` using `by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hy`. Take `⟨X, hX, hXs⟩` from `transfer hn H (π := p ^ (k - a)) hβd hβy hl hfix (fun s t => ball_pow_mono hp (by omega) (hadd s t)) (fun h hh => by`. Use `mul_mem_ball (hO β hβ) (ball_pow_mono hp (Nat.sub_le k a) (hyp h hh))` as an intermediate fact. Rewrite using `[smul_mul', hh β hβ]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Use the proof step `(fun h hh => by`. Use `mul_mem_ball (hO β hβ) (hinv h hh)` as an intermediate fact. Rewrite using `[smul_mul', hh β hβ]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Use `U _ (by omega) _ X ?_ hX hXs` and prove the remaining obligations. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => by rw [hn]; exact hβd`. Establish `hsep : ∀ S' : Finset (O →ₐ[R] K), ∀ β ∈ O, p ^ c * ∑ q : Γ ⧸ H, (∏ φ ∈ S', (q.out • (α φ : K) - φ (α φ))) * q.out • (β * d) ∈ ball (p ^ (k - a))`.

Introduce `S'`. Proceed by induction on `S' using Finset.induction_on with`. Consider the case `empty => simpa using hT`. Consider the case `insert φ S' hφS ih`. Introduce `β hβ`.

Establish `h1` using `sub_mem (ih (α φ * β) (O.mul_mem (α φ).2 hβ)) (mul_mem_ball (hφ φ (α φ)) (ih β hβ))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_insert hφS]`.

Simplify using `only [smul_mul']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hsep S 1 O.one_mem`. Establish `hout : ((1 : Γ) : Γ ⧸ H).out ∈ H`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H (1 : Γ)`.

Rewrite using `[hh, one_mul]`. Conclude with `h.2`. Rewrite `h1` using `[Finset.sum_eq_single ((1 : Γ) : Γ ⧸ H) (fun q _ hq => ?_) (by simp)]`. Establish `h2 : (p ^ c * ∏ φ ∈ S, ((α φ : K) - φ (α φ))) * d ∈ ball (p ^ (k - a))`. Rewrite `h1` using `[Finset.prod_congr rfl (fun φ _ => by rw [hout _ (α φ).2])]`.

Rewrite `h1`, the goal using `[mem_ball]`. Simplify `h1` using `only [norm_mul, hn, one_mul, mul_assoc]`. Establish `h3` using `mem_ball_of_mul hp0 (a := c + b) (by omega) (by rw [pow_add, norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)) h2`. Conclude with `ball_pow_mono hp (by omega) h3`. Establish `hne : e q.out ≠ O.val`.

Introduce `h`. Apply `hq` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Use `show e q.out = e _`. Rewrite using `[h]`.

Use extensionality with `a`. Conclude with `(hout _ a.2).symm`. Rewrite using `[Finset.prod_eq_zero (i := e q.out) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) (by rw [he, sub_self]), zero_mul]`.
-/
theorem core [CharZero K] {R : Type} [CommRing R] [Algebra R K] (O : Subalgebra R K) [Finite (O →ₐ[R] K)]
    (hO : ∀ a ∈ O, ‖a‖ ≤ 1) (hφ : ∀ (φ : O →ₐ[R] K) a, ‖φ a‖ ≤ 1) {p : K} (hp0 : p ≠ 0) (hp : ‖p‖ < 1) (c : ℕ) :
    ∃ c₁ : ℕ, ∀ (Γ : Type) [Group Γ] [MulSemiringAction Γ K] (_ : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖)
      (_ : ∀ (g : Γ) (a : R), g • algebraMap R K a = algebraMap R K a) (lam : Γ → K) (m k : ℕ) (_ : k ≤ m)
      (_ : ∀ s, ‖lam s‖ ≤ 1) (_ : ∀ g s : Γ, g • lam s = lam s)
      (_ : ∀ s t, lam (s * t) - lam s - lam t ∈ ball (p ^ m)) (s₀ : Γ) (_ : ‖lam s₀‖ = 1)
      (_ : ∀ k' ≤ m, ∀ T X : K, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 → (∀ s : Γ, T * lam s - (s • X - X) ∈ ball (p ^ k')) →
        p ^ c * T ∈ ball (p ^ k')) (d y : K) (_ : ‖d‖ ≤ 1) (_ : ‖y‖ ≤ 1)
      (_ : ∀ h : Γ, (∀ a ∈ O, h • a = a) → d * lam h - (h • y - y) ∈ ball (p ^ k)), d ∈ ball (p ^ (k - c₁)) := by
  classical
  haveI := Fintype.ofFinite (O →ₐ[R] K)
  have hsep : ∀ φ : O →ₐ[R] K, ∃ a : O, φ ≠ O.val → (a : K) - φ a ≠ 0 := by
    intro φ
    by_cases h : φ = O.val
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
      exact ⟨a, fun _ => sub_ne_zero.2 (Ne.symm ha)⟩
  choose α hα using hsep
  set S : Finset (O →ₐ[R] K) := Finset.univ.erase O.val with hS
  have hD : (∏ φ ∈ S, ((α φ : K) - φ (α φ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun φ h => hα φ (Finset.ne_of_mem_erase h)
  obtain ⟨b, hb⟩ := exists_pow_le hp hD
  have hN : (((Nat.card (O →ₐ[R] K)).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  obtain ⟨a, ha⟩ := exists_pow_le hp hN
  refine ⟨a + c + b + 1, ?_⟩
  intro Γ _ _ hn hR lam m k hkm hl hfix hadd s₀ hs₀ U d y hd hy hyp
  by_cases hk : k ≤ a + c + b + 1
  · rw [Nat.sub_eq_zero_of_le hk, mem_ball]; simpa using hd
  let H : Subgroup Γ :=
    { carrier := {h | ∀ a ∈ O, h • a = a}
      one_mem' := fun a _ => one_smul _ _
      mul_mem' := fun {g h} hg hh a ha => by rw [mul_smul, hh a ha, hg a ha]
      inv_mem' := fun {g} hg a ha => by rw [inv_smul_eq_iff, hg a ha] }
  let e : Γ → (O →ₐ[R] K) := fun g =>
    { toRingHom := (MulSemiringAction.toRingHom Γ K g).comp (O.val : O →+* K)
      commutes' := fun r => hR g r }
  have he : ∀ g (a : O), e g a = g • (a : K) := fun _ _ => rfl
  have hinj : Function.Injective fun q : Γ ⧸ H => e q.out := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq]
    intro a ha
    rw [mul_smul, inv_smul_eq_iff]
    exact (DFunLike.congr_fun hq ⟨a, ha⟩).symm
  haveI : Finite (Γ ⧸ H) := Finite.of_injective _ hinj
  haveI := Fintype.ofFinite (Γ ⧸ H)
  have hidx : H.index ≤ Nat.card (O →ₐ[R] K) := Nat.card_le_card_of_injective _ hinj
  have ht : s₀ ^ (Nat.card (O →ₐ[R] K)).factorial ∈ H :=
    Subgroup.pow_mem_of_index_ne_zero_of_dvd (Nat.card_pos (α := Γ ⧸ H)).ne' s₀
      fun n h0 hn => Nat.dvd_factorial h0 (hn.trans hidx)
  set t := s₀ ^ (Nat.card (O →ₐ[R] K)).factorial
  have hlt : ‖p ^ a‖ ≤ ‖lam t‖ := by
    by_contra hlt
    push Not at hlt
    have h1 := pow_sub_mem hadd s₀ (Nat.card (O →ₐ[R] K)).factorial
    have h2 : ‖p ^ m‖ < ‖p ^ a‖ := by
      rw [norm_pow, norm_pow]
      exact pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.2 hp0) hp (by omega)
    have h3 := IsUltrametricDist.norm_add_le_max (lam t) (-(lam t - ((Nat.card (O →ₐ[R] K)).factorial : ℕ) * lam s₀))
    rw [norm_neg, neg_sub, add_sub_cancel, norm_mul, hs₀, mul_one] at h3
    exact absurd (ha.trans h3) (not_le.2 (max_lt hlt (lt_of_le_of_lt h1 h2)))
  have hinv : ∀ h ∈ H, h • d - d ∈ ball (p ^ (k - a)) := fun h hh =>
    mem_ball_of_mul hp0 (by omega) hlt (inv_mul hn hd (hfix _ _) (ball_pow_mono hp hkm (hadd _ _))
      (hyp h hh) (hyp t ht) (hyp _ (H.mul_mem hh ht)))
  have hT : ∀ β ∈ O, p ^ c * ∑ q : Γ ⧸ H, q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro β hβ
    have hβd : ‖β * d‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hd
    have hβy : ‖β * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hy
    obtain ⟨X, hX, hXs⟩ := transfer hn H (π := p ^ (k - a)) hβd hβy hl hfix
      (fun s t => ball_pow_mono hp (by omega) (hadd s t))
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (ball_pow_mono hp (Nat.sub_le k a) (hyp h hh))
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (hinv h hh)
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
    refine U _ (by omega) _ X ?_ hX hXs
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => by rw [hn]; exact hβd
  have hsep : ∀ S' : Finset (O →ₐ[R] K), ∀ β ∈ O,
      p ^ c * ∑ q : Γ ⧸ H, (∏ φ ∈ S', (q.out • (α φ : K) - φ (α φ))) * q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty => simpa using hT
    | insert φ S' hφS ih =>
      intro β hβ
      have h1 := sub_mem (ih (α φ * β) (O.mul_mem (α φ).2 hβ)) (mul_mem_ball (hφ φ (α φ)) (ih β hβ))
      convert h1 using 1
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_insert hφS]
      simp only [smul_mul']
      ring
  have h1 := hsep S 1 O.one_mem
  have hout : ((1 : Γ) : Γ ⧸ H).out ∈ H := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : Γ)
    rw [hh, one_mul]; exact h.2
  rw [Finset.sum_eq_single ((1 : Γ) : Γ ⧸ H) (fun q _ hq => ?_) (by simp)] at h1
  · have h2 : (p ^ c * ∏ φ ∈ S, ((α φ : K) - φ (α φ))) * d ∈ ball (p ^ (k - a)) := by
      rw [Finset.prod_congr rfl (fun φ _ => by rw [hout _ (α φ).2])] at h1
      rw [mem_ball] at h1 ⊢
      simpa only [norm_mul, hn, one_mul, mul_assoc] using h1
    have h3 := mem_ball_of_mul hp0 (a := c + b) (by omega)
      (by rw [pow_add, norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)) h2
    exact ball_pow_mono hp (by omega) h3
  · have hne : e q.out ≠ O.val := by
      intro h
      apply hq
      apply hinj
      show e q.out = e _
      rw [h]
      ext a
      exact (hout _ a.2).symm
    rw [Finset.prod_eq_zero (i := e q.out) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) (by rw [he, sub_self]), zero_mul]

end Abstract

open ReciprocityTheory.Neutral.Cmp

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hq : IsIntegral ℚ_[l] a` using `Algebra.IsIntegral.isIntegral a`. Express the relevant statement in the definitionally equal form `spectralValue (minpoly ℚ_[l] a) ≤ 1`. Rewrite using `[spectralValue_le_one_iff (minpoly.monic hq)]`. Introduce `k`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]`.

Conclude with `PadicInt.norm_le_one _`.
-/
theorem norm_le_one_of_isIntegral {a : Qbar l} (hi : IsIntegral ℤ_[l] a) : ‖a‖ ≤ 1 := by
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']`. Both sides reduce to the same expression.
-/
theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in

/- English proof (translation)
Establish `h0 : ((l : Qbar l) ^ n) ≠ 0` using `pow_ne_zero _ natCast_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, e⟩`. Rewrite using `[← map_sub, e, map_mul, map_pow, map_natCast, mul_comm]`. Conclude with `mul_mem_ball ((hj z).1 hz) (mem_ball.2 le_rfl)`.

Introduce `h`. Establish `h1 : ((l : Ω) ^ n) ≠ 0`. Introduce `h'`. Apply `h0` to reduce the goal to its premises. Simplify using `using congrArg j h'`.

Use `⟨(x - y) / (l : Ω) ^ n, (hj _).2 ?_, by field_simp⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_sub, map_pow, map_natCast, norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _)`.
-/
theorem cgA_iff (hj : Compat l A j) (n : ℕ) (x y : Ω) :
    GlobalTheory.Glue.CgA A l n x y ↔ j x - j y ∈ ball ((l : Qbar l) ^ n) := by
  have h0 : ((l : Qbar l) ^ n) ≠ 0 := pow_ne_zero _ natCast_ne_zero
  constructor
  · rintro ⟨z, hz, e⟩
    rw [← map_sub, e, map_mul, map_pow, map_natCast, mul_comm]
    exact mul_mem_ball ((hj z).1 hz) (mem_ball.2 le_rfl)
  · intro h
    have h1 : ((l : Ω) ^ n) ≠ 0 := by
      intro h'
      apply h0
      simpa using congrArg j h'
    refine ⟨(x - y) / (l : Ω) ^ n, (hj _).2 ?_, by field_simp⟩
    rw [map_div₀, map_sub, map_pow, map_natCast, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)

/- English proof (translation)
Take `⟨o, ho⟩` from `Metric.denseRange_iff.1 (denseRange ℚ j) T _ (norm_pos_iff.2 (pow_ne_zero n (natCast_ne_zero (l := l))))`. Rewrite `ho` using `[dist_eq_norm]`. Use `⟨o, (hj o).2 ?_, ho.le⟩` and prove the remaining obligations. Establish `h1 : T - j o ∈ ball ((l : Qbar l) ^ 0)` using `ball_pow_mono norm_natCast_lt_one (Nat.zero_le n) ho.le`. Establish `h2 : T ∈ ball ((l : Qbar l) ^ 0)` using `by simpa [mem_ball] using hT`.

Simplify `sub_mem h2 h1` using `[mem_ball]`.
-/
theorem exists_approx (hj : Compat l A j) (n : ℕ) {T : Qbar l} (hT : ‖T‖ ≤ 1) :
    ∃ o ∈ A, T - j o ∈ ball ((l : Qbar l) ^ n) := by
  obtain ⟨o, ho⟩ := Metric.denseRange_iff.1 (denseRange ℚ j) T _
    (norm_pos_iff.2 (pow_ne_zero n (natCast_ne_zero (l := l))))
  rw [dist_eq_norm] at ho
  refine ⟨o, (hj o).2 ?_, ho.le⟩
  have h1 : T - j o ∈ ball ((l : Qbar l) ^ 0) := ball_pow_mono norm_natCast_lt_one (Nat.zero_le n) ho.le
  have h2 : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
  simpa [mem_ball] using sub_mem h2 h1

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in
/- English proof (translation)
Rewrite using `[hj.valuation_lt_one_iff, map_natCast]`. Conclude with `norm_natCast_lt_one`.
-/
theorem valuation_lt_one (hj : Compat l A j) : A.valuation (l : Ω) < 1 := by
  rw [hj.valuation_lt_one_iff, map_natCast]; exact norm_natCast_lt_one

/- English proof (translation)
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `h` using `lies_over_ratPrime A (valuation_lt_one hj)`. Use `⟨ratPrime l, fun x => by simpa using h x, (h (l : 𝓞 ℚ)).1 ?_⟩` and prove the remaining obligations. Simplify using `using valuation_lt_one hj`.
-/
theorem overL (hj : Compat l A j) : OverL l A := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have h := lies_over_ratPrime A (valuation_lt_one hj)
  refine ⟨ratPrime l, fun x => by simpa using h x, (h (l : 𝓞 ℚ)).1 ?_⟩
  simpa using valuation_lt_one hj

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1)))`. Rewrite using `[ZMod.isUnit_iff_coprime]`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]`.

Introduce `h`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by simpa using h))`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_pow_self l hm.ne')).mp h))`. Take `⟨⟨s, hs⟩, hsu⟩` from `GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA (m + 1) hu.unit`.

Establish `h1 : PadicInt.toZModPow (m + 1) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1)))`. Simplify `congrArg Units.val hsu` using `[cycMod]`. Establish `h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - ((1 + l ^ m : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (m + 1) : ℤ_[l] →+* ZMod (l ^ (m + 1)))`. Rewrite using `[RingHom.mem_ker, map_sub, h1, map_natCast, sub_self]`. Rewrite `h2` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`.

Take `⟨b, hb⟩` from `h2`. Establish `h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * (1 + l * b)`. Move the coercions through the operations in `at hb`. Take the linear combination `hb`. Establish `hm : cycMod ℚ Ω l m s = 1`.

Use `ext`. Use `show PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Rewrite using `[h3, map_add, map_one, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]`. Use `⟨s, hs, hm, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, ha'⟩` from `exists_lamv_eq hm`.

Establish `h4 : a = 1 + l * b` using `mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero)) (add_left_cancel (ha.symm.trans h3))`. Rewrite using `[ha', norm_algebraMap_padicInt, h4]`. Establish `h5 : ‖(l : ℤ_[l]) * b‖ < 1`. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one b)) (PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl)`.

Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h5.ne'), norm_one, max_eq_left h5.le]`.
-/
theorem exists_norm_lamv_eq_one (hl2 : l ≠ 2) (hA : A.valuation (l : Ω) < 1) (m : ℕ) :
    ∃ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 ∧ ‖lamv l m s‖ = 1 := by
  have hl := (Fact.out : l.Prime)
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by simpa using h))
    · exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_pow_self l hm.ne')).mp h))
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA (m + 1) hu.unit
  have h1 : PadicInt.toZModPow (m + 1) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    simpa [cycMod] using congrArg Units.val hsu
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - ((1 + l ^ m : ℕ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + 1) : ℤ_[l] →+* ZMod (l ^ (m + 1))) := by
    rw [RingHom.mem_ker, map_sub, h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * (1 + l * b) := by
    push_cast at hb
    linear_combination hb
  have hm : cycMod ℚ Ω l m s = 1 := by
    ext
    show PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1
    rw [h3, map_add, map_one, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
  refine ⟨s, hs, hm, ?_⟩
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hm
  have h4 : a = 1 + l * b :=
    mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero)) (add_left_cancel (ha.symm.trans h3))
  rw [ha', norm_algebraMap_padicInt, h4]
  have h5 : ‖(l : ℤ_[l]) * b‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one b))
      (PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h5.ne'), norm_one, max_eq_left h5.le]

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `h1 : s ζ' = ζ' ^ (PadicInt.toZModPow (m + m) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ' hζ.pow_eq_one`.

Rewrite `h1` using `[ht, ← pow_mul, ← pow_succ, pow_eq_pow_mod _ hζ.pow_eq_one]`. Establish `: NeZero (l ^ (m + m))` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Use `replace h1 := congrArg (Nat.cast : ℕ → ZMod (l ^ (m + m))) (hζ.pow_inj (Nat.mod_lt _ (pow_pos hl.pos _)) (ZMod.val_lt _) h1)`. Rewrite `h1` using `[ZMod.natCast_mod, ZMod.natCast_zmod_val]`. Take `⟨a, ha, ha'⟩` from `exists_lamv_eq hs`.

Establish `h2 : ((l ^ m * t + 1 : ℕ) : ℤ_[l]) - ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (m + m) : ℤ_[l] →+* ZMod (l ^ (m + m)))`. Rewrite using `[RingHom.mem_ker, map_sub, ← h1, map_natCast, sub_self]`. Rewrite `h2` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Take `⟨b, hb⟩` from `h2`. Establish `h4 : (t : ℤ_[l]) - a = b * (l : ℤ_[l]) ^ m`.

Apply `mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero : (l : ℤ_[l]) ≠ 0))` to reduce the goal to its premises. Rewrite `hb` using `[ha]`. Move the coercions through the operations in `at hb`. Take the linear combination `hb`. Establish `h5` using `congrArg (algebraMap ℤ_[l] (Qbar l)) h4`.

Rewrite `h5` using `[map_sub, map_natCast, map_mul, map_pow, map_natCast]`. Rewrite using `[ha', h5]`. Conclude with `mul_mem_ball (by rw [norm_algebraMap_padicInt]; exact PadicInt.norm_le_one b) (mem_ball.2 le_rfl)`.
-/
theorem kummer_sub_lamv {m : ℕ} {ζ' : Ω} (hζ : IsPrimitiveRoot ζ' (l ^ (m + m))) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1)
    {t : ℕ} (ht : s ζ' = (ζ' ^ l ^ m) ^ t * ζ') : (t : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
  have hl := (Fact.out : l.Prime)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have h1 : s ζ' = ζ' ^ (PadicInt.toZModPow (m + m) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ' hζ.pow_eq_one
  rw [ht, ← pow_mul, ← pow_succ, pow_eq_pow_mod _ hζ.pow_eq_one] at h1
  have : NeZero (l ^ (m + m)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  replace h1 := congrArg (Nat.cast : ℕ → ZMod (l ^ (m + m)))
    (hζ.pow_inj (Nat.mod_lt _ (pow_pos hl.pos _)) (ZMod.val_lt _) h1)
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val] at h1
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hs
  have h2 : ((l ^ m * t + 1 : ℕ) : ℤ_[l]) - ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + m) : ℤ_[l] →+* ZMod (l ^ (m + m))) := by
    rw [RingHom.mem_ker, map_sub, ← h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h4 : (t : ℤ_[l]) - a = b * (l : ℤ_[l]) ^ m := by
    apply mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero : (l : ℤ_[l]) ≠ 0))
    rw [ha] at hb
    push_cast at hb
    linear_combination hb
  have h5 := congrArg (algebraMap ℤ_[l] (Qbar l)) h4
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h5
  rw [ha', h5]
  exact mul_mem_ball (by rw [norm_algebraMap_padicInt]; exact PadicInt.norm_le_one b) (mem_ball.2 le_rfl)

def grp (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (m : ℕ) : Subgroup (GK ℚ j) :=
  (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker).comap (res j)

/- English proof (translation)
Take `⟨σ, rfl⟩` from `exists_res_eq hj (Ine_le_Dec A hs)`. Conclude with `⟨⟨σ, ⟨hs, hm⟩⟩, rfl⟩`.
-/
theorem exists_grp (hj : Compat l A j) {m : ℕ} {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (hm : cycMod ℚ Ω l m s = 1) :
    ∃ σ : grp A j m, res j σ.1 = s := by
  obtain ⟨σ, rfl⟩ := exists_res_eq hj (Ine_le_Dec A hs)
  exact ⟨⟨σ, ⟨hs, hm⟩⟩, rfl⟩

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]`. Conclude with `σ.commutes ⟨_, (Kloc ℚ j).algebraMap_mem _⟩`.
-/
theorem smul_algebraMap (σ : GK ℚ j) (a : ℤ_[l]) : σ (algebraMap ℤ_[l] (Qbar l) a) = algebraMap ℤ_[l] (Qbar l) a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  exact σ.commutes ⟨_, (Kloc ℚ j).algebraMap_mem _⟩

/- English proof (translation)
Establish `e : lamv l m (s * t) - lamv l m s - lamv l m t = lamv l m s * (lamv l m t * (l : Qbar l) ^ m)`. Rewrite using `[lamv_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem_ball (norm_lamv_le_one hs) (mul_mem_ball (norm_lamv_le_one ht) (mem_ball.2 le_rfl))`.
-/
theorem lamv_add_mem {m : ℕ} {s t : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) (ht : cycMod ℚ Ω l m t = 1) :
    lamv l m (s * t) - lamv l m s - lamv l m t ∈ ball ((l : Qbar l) ^ m) := by
  have e : lamv l m (s * t) - lamv l m s - lamv l m t = lamv l m s * (lamv l m t * (l : Qbar l) ^ m) := by
    rw [lamv_mul]; ring
  rw [e]
  exact mul_mem_ball (norm_lamv_le_one hs) (mul_mem_ball (norm_lamv_le_one ht) (mem_ball.2 le_rfl))

/- English proof (translation)
Take `⟨a, -, ha⟩` from `exists_lamv_eq hs`. Rewrite using `[ha, smul_algebraMap]`.
-/
theorem smul_lamv {m : ℕ} (σ : GK ℚ j) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : σ (lamv l m s) = lamv l m s := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, smul_algebraMap]

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound l hl2`. Use `⟨c + 1, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ _ A j hj m k hkm T X hT hX hyp`. Establish `hl` using `(Fact.out : l.Prime)`. Establish `hp1` using `norm_natCast_lt_one (l := l)`.

Establish `hpc : ‖(l : Qbar l) ^ c‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le`. Break down `k with _ | n` into its components or cases. Establish `: T ∈ ball ((l : Qbar l) ^ 0)` using `by simpa [mem_ball] using hT`. Conclude with `mul_mem_ball (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le) this`. Establish `hn : ∀ (g : grp A j m) (x : Qbar l), ‖g • x‖ = ‖x‖` using `fun g x => norm_map_GK j g.1 x`.

Take `⟨s₀, hs₀, hm₀, hu₀⟩` from `exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m`. Take `⟨t, rfl⟩` from `exists_grp hj hs₀ hm₀`. Establish `hinv : ∀ h : grp A j m, h • T - T ∈ ball ((l : Qbar l) ^ (n + 1))`. Introduce `h`. Use `inv_mul hn (lam := fun σ : grp A j m => lamv l m (res j σ.1)) hT (h := h) (t := t) (smul_lamv h.1 hm₀) (by simpa using ball_pow_mono hp1 hkm (lamv_add_mem h.2.2 hm₀)) (hyp _) (hyp _) (hyp _)` as an intermediate fact.

Rewrite `this` using `[mem_ball, norm_mul, hu₀, one_mul]`. Then use the resulting hypothesis. Take `⟨o, ho, hTo⟩` from `exists_approx hj (n + 1) hT`. Take `⟨x, hx, hXx⟩` from `exists_approx hj (n + 1) hX`. Take `⟨y, hy, hyfix, hoy⟩` from `GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A (overL hj) (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker) (fun h hh => Ine_le_Dec A hh.1) n o ho (fun h hh => by`. Take `⟨σ, rfl⟩` from `exists_grp hj hh.1 hh.2`.

Rewrite using `[cgA_iff hj, res_spec]`. Use `add_mem (sub_mem (hinv σ) (smul_mem_ball hn σ hTo)) hTo` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Use `show σ.1 (j o) - j o = σ.1 T - T - (σ.1 T - σ.1 (j o)) + (T - j o)`.

Use the proof step `ring)`. Rewrite `hoy` using `[cgA_iff hj]`. Establish `hTy : T - j y ∈ ball ((l : Qbar l) ^ n)`. Simplify using `using add_mem (ball_pow_mono hp1 (Nat.le_succ n) hTo) hoy`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`.

Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `: NeZero ((l ^ (m + m) : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.ne_zero)⟩`. Take `⟨ζ', hζ'⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (m + m))`. Establish `hζ : IsPrimitiveRoot (ζ' ^ l ^ m) (l ^ m)` using `hζ'.pow (pow_pos hl.pos _) (pow_add l m m)`. Establish `key` using `hc Ω A (overL hj) m n (by omega) _ ζ' hζ rfl y x hy hx (fun s hs hm => hyfix s ⟨hs, hm⟩) (fun s hs hm τ hτ => by`.

Establish `h1` using `kummer_sub_lamv hζ' hm hτ`. Take `⟨σ, rfl⟩` from `exists_grp hj hs hm`. Rewrite using `[cgA_iff hj, map_mul, map_natCast, map_sub, res_spec]`. Establish `h2` using `ball_pow_mono hp1 (Nat.le_succ n) hXx`. Use `sub_mem (add_mem (sub_mem (add_mem (ball_pow_mono hp1 (Nat.le_succ n) (hyp σ)) (mul_mem_ball hT (ball_pow_mono hp1 (by omega : n ≤ m) h1))) (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one (Qbar l) τ.val) hTy)) (smul_mem_ball hn σ h2)) h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Use `show _ = T * _ - (σ.1 X - X) + _ - _ + (σ.1 X - σ.1 (j x)) - _`. Use the proof step `ring)`. Rewrite `key` using `[cgA_iff hj, map_zero, sub_zero, map_mul, map_pow, map_natCast]`.

Establish `h3` using `add_mem key (mul_mem_ball hpc hTy)`. Rewrite `h3`, the goal using `[mem_ball]`. Establish `e : (l : Qbar l) ^ (c + 1) * T = l * ((l : Qbar l) ^ c * j y + (l : Qbar l) ^ c * (T - j y))` using `by ring`. Rewrite using `[e, pow_succ' _ n, norm_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left h3 (norm_nonneg _)`.
-/
theorem uniq_true (hl2 : l ≠ 2) : ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (j : Ω →+* Qbar l), Compat l A j → ∀ m k : ℕ, k ≤ m → ∀ T X : Qbar l, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 →
    (∀ σ : grp A j m, T * lamv l m (res j σ.1) - (σ • X - X) ∈ ball ((l : Qbar l) ^ k)) →
    (l : Qbar l) ^ c * T ∈ ball ((l : Qbar l) ^ k) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound l hl2
  refine ⟨c + 1, ?_⟩
  intro Ω _ _ _ A j hj m k hkm T X hT hX hyp
  have hl := (Fact.out : l.Prime)
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  rcases k with _ | n
  · have : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
    exact mul_mem_ball (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le) this
  have hn : ∀ (g : grp A j m) (x : Qbar l), ‖g • x‖ = ‖x‖ := fun g x => norm_map_GK j g.1 x
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m
  obtain ⟨t, rfl⟩ := exists_grp hj hs₀ hm₀
  have hinv : ∀ h : grp A j m, h • T - T ∈ ball ((l : Qbar l) ^ (n + 1)) := by
    intro h
    have := inv_mul hn (lam := fun σ : grp A j m => lamv l m (res j σ.1)) hT (h := h) (t := t) (smul_lamv h.1 hm₀)
      (by simpa using ball_pow_mono hp1 hkm (lamv_add_mem h.2.2 hm₀)) (hyp _) (hyp _) (hyp _)
    rwa [mem_ball, norm_mul, hu₀, one_mul] at this
  obtain ⟨o, ho, hTo⟩ := exists_approx hj (n + 1) hT
  obtain ⟨x, hx, hXx⟩ := exists_approx hj (n + 1) hX
  obtain ⟨y, hy, hyfix, hoy⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A (overL hj) (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker)
    (fun h hh => Ine_le_Dec A hh.1) n o ho (fun h hh => by
      obtain ⟨σ, rfl⟩ := exists_grp hj hh.1 hh.2
      rw [cgA_iff hj, res_spec]
      have := add_mem (sub_mem (hinv σ) (smul_mem_ball hn σ hTo)) hTo
      convert this using 1
      rw [smul_sub]
      show σ.1 (j o) - j o = σ.1 T - T - (σ.1 T - σ.1 (j o)) + (T - j o)
      ring)
  rw [cgA_iff hj] at hoy
  have hTy : T - j y ∈ ball ((l : Qbar l) ^ n) := by
    simpa using add_mem (ball_pow_mono hp1 (Nat.le_succ n) hTo) hoy
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l ^ (m + m) : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (m + m))
  have hζ : IsPrimitiveRoot (ζ' ^ l ^ m) (l ^ m) := hζ'.pow (pow_pos hl.pos _) (pow_add l m m)
  have key := hc Ω A (overL hj) m n (by omega) _ ζ' hζ rfl y x hy hx (fun s hs hm => hyfix s ⟨hs, hm⟩)
    (fun s hs hm τ hτ => by
      have h1 := kummer_sub_lamv hζ' hm hτ
      obtain ⟨σ, rfl⟩ := exists_grp hj hs hm
      rw [cgA_iff hj, map_mul, map_natCast, map_sub, res_spec]
      have h2 := ball_pow_mono hp1 (Nat.le_succ n) hXx
      have := sub_mem (add_mem (sub_mem (add_mem (ball_pow_mono hp1 (Nat.le_succ n) (hyp σ))
        (mul_mem_ball hT (ball_pow_mono hp1 (by omega : n ≤ m) h1)))
        (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one (Qbar l) τ.val) hTy)) (smul_mem_ball hn σ h2)) h2
      convert this using 1
      rw [smul_sub]
      show _ = T * _ - (σ.1 X - X) + _ - _ + (σ.1 X - σ.1 (j x)) - _
      ring)
  rw [cgA_iff hj, map_zero, sub_zero, map_mul, map_pow, map_natCast] at key
  have h3 := add_mem key (mul_mem_ball hpc hTy)
  rw [mem_ball] at h3 ⊢
  have e : (l : Qbar l) ^ (c + 1) * T = l * ((l : Qbar l) ^ c * j y + (l : Qbar l) ^ c * (T - j y)) := by ring
  rw [e, pow_succ' _ n, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

/- English proof (translation)
Introduce `l _ hl2 c`. Establish `hp1` using `norm_natCast_lt_one (l := l)`. Take `⟨c', hc'⟩` from `uniq_true hl2`. Take `⟨c₁, hc₁⟩` from `core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha) (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ)) natCast_ne_zero hp1 c'`. Use `⟨c₁, ?_⟩` and prove the remaining obligations.

Introduce `Ω _ _ _ A j Z m c₀ y h h' H H'`. Take `⟨hj, f, hf, hyp⟩` from `H.sub H'`. Take `⟨x, hx, hfx⟩` from `exists_eq_sub_of_mem_cob hj (neg_mem hf)`. Establish `hyp' : ∀ s ∈ Ine (F` using `ℚ) A, cycMod ℚ Ω l m s = 1 → (h - h') * lamv l m s + f s ∈ ball ((l : Qbar l) ^ (m - c₀)) := fun s hs hm => by`. Use `hyp s hs hm` as an intermediate fact.

Simplify using `only [Cg, sub_self, zero_sub, norm_neg] at this`. Conclude with `this`. Take `⟨s₀, hs₀, hm₀, hu₀⟩` from `exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m`. Establish `hd : ‖h - h'‖ ≤ 1`. Establish `h1 : f s₀ ∈ ball ((l : Qbar l) ^ 0)`.

Take `⟨q, o, w, how, e⟩` from `mem_cob_iff.1 hf`. Rewrite using `[e]`. Use `sum_mem fun i _ => mul_mem_ball (norm_le_one_of_mem (how i).1) (sub_mem ?_ ?_)` and prove the remaining obligations. Simplify `(hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 (how i).2)` using `[mem_ball]`. Simplify `(hj _).1 (how i).2` using `[mem_ball]`.

Establish `h2` using `sub_mem (ball_pow_mono hp1 (Nat.zero_le _) (hyp' s₀ hs₀ hm₀)) h1`. Simplify `h2` using `[mem_ball, hu₀]`. Take `⟨t, rfl⟩` from `exists_grp hj hs₀ hm₀`. Use `hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a) (fun σ => lamv l m (res j σ.1)) m (m - c₀) (Nat.sub_le _ _) (fun σ => norm_lamv_le_one σ.2.2) (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀ (fun k hk …` and prove the remaining obligations. Establish `h1` using `hfx σ.1.toRingEquiv (res j σ.1) (fun w => res_spec j σ.1 w) hσ`.

Establish `h2` using `hyp' _ σ.2.1 σ.2.2`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite `h1` using `[Pi.neg_apply]`. Use `show _ - (σ.1.toRingEquiv x - x) = _`. Rewrite using `[← h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ c : Coef l, ∃ c₁ : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (j : Ω →+* Qbar l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h h' : Qbar l),
    GlobalTheory.LambdaValuationPowers.HTCoIn c A j Z m c₀ y h → GlobalTheory.LambdaValuationPowers.HTCoIn c A j Z m c₀ y h' → Cg (m - c₀ - c₁) h h' := by
  intro l _ hl2 c
  have hp1 := norm_natCast_lt_one (l := l)
  obtain ⟨c', hc'⟩ := uniq_true hl2
  obtain ⟨c₁, hc₁⟩ := core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha)
    (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ))
    natCast_ne_zero hp1 c'
  refine ⟨c₁, ?_⟩
  intro Ω _ _ _ A j Z m c₀ y h h' H H'
  obtain ⟨hj, f, hf, hyp⟩ := H.sub H'
  obtain ⟨x, hx, hfx⟩ := exists_eq_sub_of_mem_cob hj (neg_mem hf)
  have hyp' : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      (h - h') * lamv l m s + f s ∈ ball ((l : Qbar l) ^ (m - c₀)) := fun s hs hm => by
    have := hyp s hs hm
    simp only [Cg, sub_self, zero_sub, norm_neg] at this
    exact this
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m
  have hd : ‖h - h'‖ ≤ 1 := by
    have h1 : f s₀ ∈ ball ((l : Qbar l) ^ 0) := by
      obtain ⟨q, o, w, how, e⟩ := mem_cob_iff.1 hf
      rw [e]
      refine sum_mem fun i _ => mul_mem_ball (norm_le_one_of_mem (how i).1) (sub_mem ?_ ?_)
      · simpa [mem_ball] using (hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 (how i).2)
      · simpa [mem_ball] using (hj _).1 (how i).2
    have h2 := sub_mem (ball_pow_mono hp1 (Nat.zero_le _) (hyp' s₀ hs₀ hm₀)) h1
    simpa [mem_ball, hu₀] using h2
  obtain ⟨t, rfl⟩ := exists_grp hj hs₀ hm₀
  refine hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a)
    (fun σ => lamv l m (res j σ.1)) m (m - c₀) (Nat.sub_le _ _) (fun σ => norm_lamv_le_one σ.2.2)
    (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀
    (fun k hk T X hT hX hh => hc' Ω A j hj m k hk T X hT hX hh) (h - h') x hd hx fun σ hσ => ?_
  have h1 := hfx σ.1.toRingEquiv (res j σ.1) (fun w => res_spec j σ.1 w) hσ
  have h2 := hyp' _ σ.2.1 σ.2.2
  convert h2 using 1
  rw [Pi.neg_apply] at h1
  show _ - (σ.1.toRingEquiv x - x) = _
  rw [← h1]; ring

end GlobalTheory.LambdaValuationPowers.HTCoUniq
