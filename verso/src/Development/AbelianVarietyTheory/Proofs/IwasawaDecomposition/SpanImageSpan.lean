import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf

open NumberField

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

/- English proof (translation)
Use extensionality with `x'`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨x, hx, funext fun k => (h k k rfl).symm⟩`.

Introduce and unpack `⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩`.
-/
theorem relSet_eq {n : ℕ} (S : Set (Fin n → K)) :
    {x' : Fin n → K' | ∃ x ∈ S, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' S := by
  ext x'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero`. Rewrite using `[SetLike.mem_coe]`. Use `Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Consider the case `add y z _ _ hy hz`. Rewrite `hy`, `hz`, the goal using `[SetLike.mem_coe]`. Use `Submodule.add_mem _ hy hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Consider the case `smul a y _ hy`. Rewrite `hy`, the goal using `[SetLike.mem_coe]`. Use `Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_image_span {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun x k => φ (x k)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [SetLike.mem_coe]
      convert Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1
      funext k; simp
    | add y z _ _ hy hz =>
      rw [SetLike.mem_coe] at hy hz ⊢
      convert Submodule.add_mem _ hy hz using 1; funext k; simp
    | smul a y _ hy =>
      rw [SetLike.mem_coe] at hy ⊢
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1
      funext k
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Use `set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ`. Use `set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef`. Establish `hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K)` using `fun a => rfl`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨hyX, hyV⟩`.

Set `bQ` to `Module.finBasis K ((Fin n → K) ⧸ V)`. Set `ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K` to `fun r => (bQ.coord r).comp V.mkQ`. Establish `hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx r`. Simplify using `[ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]`. Introduce `h`. Establish `: V.mkQ x = 0` using `bQ.ext_elem fun r => by simpa [ℓ] using h r`. Conclude with `(Submodule.Quotient.mk_eq_zero V).1 this`.

Set `q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K` to `fun r k => ℓ r (Pi.single k 1)`. Establish `hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k`. Introduce `r x`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ (ℓ r) x]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, mul_comm]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`. Establish `hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0`.

Introduce `r`. Establish `key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨x, hx, rfl⟩` from `hw`. Establish `h0` using `(hℓV x).1 hx r`. Rewrite `h0` using `[hℓ]`. Use `congrArg φ h0` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`.

Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]`.

Consider the case `smul a b _ hb`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]`. Conclude with `key y hyV`.

Take `⟨m, r0, g, hg⟩` from `Submodule.mem_span_set'.1 hyX`. Use `choose x hxX hx using fun i => (g i).2`. Establish `hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k)`. Introduce `k`. Rewrite using `[← hg, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← hx i]`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))`. Use `choose b hb using hd`. Establish `hd0 : ((d : 𝓞 K) : K) ≠ 0`.

Use `nonZeroDivisors.coe_ne_zero d` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i)` using `fun i r => by`. Use `hb (i, r)` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`.

Conclude with `this`. Use `letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra`. Establish `hinj : Function.Injective ψ` using `fun a a' h => by`. Use `congrArg (fun z : 𝓞 K' => (z : K')) h` as an intermediate fact. Simplify using `only [hψ] at this`.

Conclude with `RingOfIntegers.ext (φ.injective this)`. Use `haveI : Module.Flat (𝓞 K) (𝓞 K') := by`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce and unpack `z ⟨a, ha⟩`. Establish `ha' : ψ a * z = 0` using `ha`.

Break down `mul_eq_zero.1 ha' with h | h` into its components or cases. Conclude with `absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)`. Conclude with `h`. Take `⟨N, a, yv, hr, ha⟩` from `GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Establish `h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K')`. Rewrite using `[show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from map_sum (algebraMap (𝓞 K') K') _ _]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Simplify using `only [hb', map_mul]`.

Establish `h2` using `hyℓ r`. Simplify using `only [hy, Finset.mul_sum] at h2`. Rewrite `h2` using `[Finset.sum_comm]`. Express the relevant statement in the definitionally equal form `_ = (0 : K')`. Rewrite using `[← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hℓ, map_sum]`. Simplify using `only [map_mul, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring)`. Set `u : Fin N → Fin n → K` to `fun l => ∑ i, a i l • x i`.

Establish `huX : ∀ l, u l ∈ X` using `fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)`. Establish `huV : ∀ l, u l ∈ V`. Introduce `l`. Rewrite using `[hℓV]`. Introduce `r`.

Establish `h1` using `congrArg (fun z : 𝓞 K => (z : K)) (ha l r)`. Simplify using `only [map_sum, map_mul, hb', map_zero] at h1`. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Rewrite using `[mul_zero, ← h1, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smul_of_tower, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hyu : y = ∑ l, yv l • Φ (u l)`. Use function extensionality and compare the values at `k`. Rewrite using `[hy, Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]`. Establish `h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K')`. Introduce `i`. Rewrite using `[hr i]`. Rewrite using `[show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from map_sum (algebraMap (𝓞 K') K') _ _]`.

Both sides reduce to the same expression. Simplify using `only [h2, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)`.

Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hyu]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, ⟨hxX, hxV⟩, rfl⟩`. Conclude with `⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩`.
-/
theorem span_image_inf {n : ℕ} (X : Submodule (𝓞 K) (Fin n → K)) (V : Submodule K (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' (X : Set (Fin n → K))) ⊓
      (Submodule.span K' ((fun (x : Fin n → K) k => φ (x k)) '' (V : Set (Fin n → K)))).restrictScalars (𝓞 K') =
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) ''
      ((X ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  classical
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef
  have hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K) := fun a => rfl
  apply le_antisymm
  · rintro y ⟨hyX, hyV⟩

    let bQ := Module.finBasis K ((Fin n → K) ⧸ V)
    let ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K := fun r => (bQ.coord r).comp V.mkQ
    have hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0 := by
      intro x
      constructor
      · intro hx r
        simp [ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]
      · intro h
        have : V.mkQ x = 0 := bQ.ext_elem fun r => by simpa [ℓ] using h r
        exact (Submodule.Quotient.mk_eq_zero V).1 this
    let q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K := fun r k => ℓ r (Pi.single k 1)
    have hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k := by
      intro r x
      rw [LinearMap.pi_apply_eq_sum_univ (ℓ r) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0 := by
      intro r
      have key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, rfl⟩ := hw
          have h0 := (hℓV x).1 hx r
          rw [hℓ] at h0
          have := congrArg φ h0
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a b _ hb =>
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]
      exact key y hyV
    obtain ⟨m, r0, g, hg⟩ := Submodule.mem_span_set'.1 hyX
    choose x hxX hx using fun i => (g i).2
    have hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k) := by
      intro k
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, ← hx i]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
      (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))
    choose b hb using hd
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i) := fun i r => by
      have := hb (i, r)
      rw [Algebra.smul_def] at this
      exact this
    letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra
    have hinj : Function.Injective ψ := fun a a' h => by
      have := congrArg (fun z : 𝓞 K' => (z : K')) h
      simp only [hψ] at this
      exact RingOfIntegers.ext (φ.injective this)
    haveI : Module.Flat (𝓞 K) (𝓞 K') := by
      rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
      rintro z ⟨a, ha⟩
      have ha' : ψ a * z = 0 := ha
      rcases mul_eq_zero.1 ha' with h | h
      · exact absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)
      · exact h
    obtain ⟨N, a, yv, hr, ha⟩ := GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by
      apply RingOfIntegers.ext
      have h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K') := by
        rw [show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      rw [h1]
      simp only [hb', map_mul]
      have h2 := hyℓ r
      simp only [hy, Finset.mul_sum] at h2
      rw [Finset.sum_comm] at h2
      change _ = (0 : K')
      rw [← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hℓ, map_sum]
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring)
    let u : Fin N → Fin n → K := fun l => ∑ i, a i l • x i
    have huX : ∀ l, u l ∈ X := fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
    have huV : ∀ l, u l ∈ V := by
      intro l
      rw [hℓV]
      intro r
      have h1 := congrArg (fun z : 𝓞 K => (z : K)) (ha l r)
      simp only [map_sum, map_mul, hb', map_zero] at h1
      apply mul_left_cancel₀ hd0
      rw [mul_zero, ← h1, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
      ring
    have hyu : y = ∑ l, yv l • Φ (u l) := by
      funext k
      rw [hy, Finset.sum_apply]
      simp only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]
      have h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K') := by
        intro i
        rw [hr i]
        rw [show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      simp only [h2, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      change _ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)
      rw [map_mul]
      change φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))
      ring
    rw [hyu]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxV⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩

end GlobalTheory.Mem.R3.LiftForms

namespace GlobalTheory.Mem.R3.LiftForms
variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

/- English proof (translation)
Substitute `hn hS hV` using the available equality. Establish `e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' (V : Set (Fin n → K))` using `relSet_eq φ (V : Set (Fin n → K))`. Establish `e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K), ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))` using `relSet_eq φ _`. Rewrite using `[relSet_eq, e1, e2, ← span_image_span φ S]`. Conclude with `span_image_inf φ _ V`.
-/
theorem span_rel_inf {n n' : ℕ} (hn : n = n') (S : Set (Fin n → K)) (V : Submodule K (Fin n → K))
    (S' : Set (Fin n' → K')) (V' : Submodule K' (Fin n' → K'))
    (hS : S' = {x' | ∃ x ∈ S, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)})
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    Submodule.span (𝓞 K') S' ⊓ V'.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') {x' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
        ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn hS hV
  have e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' (V : Set (Fin n → K)) := relSet_eq φ (V : Set (Fin n → K))
  have e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
      ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) :
        Set (Fin n → K)) := relSet_eq φ _
  rw [relSet_eq, e1, e2, ← span_image_span φ S]
  exact span_image_inf φ _ V

end GlobalTheory.Mem.R3.LiftForms
