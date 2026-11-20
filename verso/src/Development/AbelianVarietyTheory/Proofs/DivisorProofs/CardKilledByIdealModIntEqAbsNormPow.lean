import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
open scoped NumberField

namespace GlobalTheory.TorsQuotCount

variable {K : Type} [Field K] [NumberField K] {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

/- English proof (translation)
Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce and unpack `x ⟨⟨a, ha⟩, hx⟩`. Establish `hx' : a • x = 0` using `hx`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hI : Ideal.span {a} ≠ ⊥` using `by simpa [Ideal.span_singleton_eq_bot] using ha0`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))`. Establish `hN : Ideal.absNorm (Ideal.span {a}) ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 hI`. Establish `h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0`. Rewrite using `[natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← ht, mul_smul, hx', smul_zero]`. Conclude with `(Submodule.mem_bot _).2 ((smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN))`.
-/
theorem flat_of_free [Module.Free ℤ M] : Module.Flat (𝓞 K) M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : a • x = 0 := hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hI : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  have h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← ht, mul_smul, hx', smul_zero]
  exact (Submodule.mem_bot _).2 ((smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN))

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M`. Use `haveI : Module.Flat (𝓞 K) M := flat_of_free`. Establish `h20 : (2 : 𝓞 K) ≠ 0` using `two_ne_zero`. Establish `hI : Ideal.span {(2 : 𝓞 K)} ≠ ⊥` using `by simpa [Ideal.span_singleton_eq_bot] using h20`. Use `haveI : Finite (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI`.

Establish `e1` using `GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(2 : 𝓞 K)})`. Use `haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) := Nat.finite_of_card_ne_zero (by rw [Int.card_ideal_quot]; norm_num)`. Establish `e2` using `GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := ℤ) (N := M) (Ideal.span {((2 : ℕ) : ℤ)})`. Rewrite `e2` using `[Int.card_ideal_quot]`. Establish `hq : Nat.card (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) = 2 ^ Module.finrank ℚ K`.

Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]`. Establish `h2 : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2` using `by simp`. Rewrite using `[h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]`. Both sides reduce to the same expression. Establish `hPQ : (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M).restrictScalars ℤ = (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M)`.

Use extensionality with `x`. Simplify using `only [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]`. Apply the tactic sequence `constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [two_smul]⟩`. Establish `hsame : Nat.card (M ⧸ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)) = Nat.card (M ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M))`. Rewrite using `[← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)).toEquiv, hPQ]`.

Rewrite `e1` using `[hsame, e2, hq, hr, ← pow_mul]`. Establish `hn : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `h3` using `Nat.pow_right_injective (le_refl 2) e1`. Establish `h4 : Module.finrank ℚ K * r = Module.finrank ℚ K * Module.finrank (𝓞 K) M`. Rewrite `h3` using `[mul_comm]`.

Conclude with `h3`. Conclude with `(Nat.eq_of_mul_eq_mul_left hn h4).symm`.
-/
theorem finrank_eq [Module.Free ℤ M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.finrank ℤ M = r * Module.finrank ℚ K) : Module.finrank (𝓞 K) M = r := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have h20 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have hI : Ideal.span {(2 : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using h20
  haveI : Finite (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have e1 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(2 : 𝓞 K)})
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Nat.finite_of_card_ne_zero (by rw [Int.card_ideal_quot]; norm_num)
  have e2 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := ℤ) (N := M) (Ideal.span {((2 : ℕ) : ℤ)})
  rw [Int.card_ideal_quot] at e2
  have hq : Nat.card (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) = 2 ^ Module.finrank ℚ K := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have h2 : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
    rw [h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hPQ : (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M).restrictScalars ℤ =
      (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [two_smul]⟩
  have hsame : Nat.card (M ⧸ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)) =
      Nat.card (M ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M)) := by
    rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)).toEquiv, hPQ]
  rw [hsame, e2, hq, hr, ← pow_mul] at e1
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h3 := Nat.pow_right_injective (le_refl 2) e1
  have h4 : Module.finrank ℚ K * r = Module.finrank ℚ K * Module.finrank (𝓞 K) M := by
    rw [mul_comm] at h3; exact h3
  exact (Nat.eq_of_mul_eq_mul_left hn h4).symm

/- English proof (translation)
Introduce `K _ _ M _ _ hfree hfin r hr 𝔟 c hc hcb`. Use `haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M`. Use `haveI : Module.Flat (𝓞 K) M := flat_of_free`. Establish `hd` using `finrank_eq (K := K) (M := M) r hr`. Establish `hc0 : (c : 𝓞 K) ≠ 0` using `by exact_mod_cast hc.ne'`.

Establish `hspan : Ideal.span {(c : 𝓞 K)} ≠ ⊥` using `by simpa [Ideal.span_singleton_eq_bot] using hc0`. Establish `hb : 𝔟 ≠ ⊥` using `fun h => hc0 (by rw [h] at hcb; exact (Submodule.mem_bot _).1 hcb)`. Use `haveI : Finite (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hspan`. Use `haveI : Finite (𝓞 K ⧸ 𝔟) := Ideal.finiteQuotientOfFreeOfNeBot _ hb`. Establish `hX` using `GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(c : 𝓞 K)})`.

Establish `hNc : Nat.card (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) ≠ 0` using `Nat.card_pos.ne'`. Use `set P : Submodule (𝓞 K) M := Ideal.span {(c : 𝓞 K)} • ⊤ with hP`. Use `haveI : Finite (M ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hNc)`. Take `⟨b, hbsup⟩` from `IsDedekindDomain.exists_sup_span_eq ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb) hspan`. Establish `hcX : ∀ x : M ⧸ P, (c : 𝓞 K) • x = 0`.

Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H m`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial`.

Set `f : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P)` to `b • LinearMap.id`. Establish `hf : ∀ x, f x = b • x` using `fun x => rfl`. Establish `hmem : ∀ a ∈ 𝔟, ∃ u v : 𝓞 K, a = u * c + v * b`. Introduce `a ha`. Rewrite `ha` using `[← hbsup, Submodule.mem_sup]`.

Take `⟨y, hy, z, hz, rfl⟩` from `ha`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Take `⟨v, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Conclude with `⟨u, v, rfl⟩`. Establish `hbmem : b ∈ 𝔟` using `hbsup ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)`.

Establish `e1 : {x : M ⧸ P // ∀ a ∈ 𝔟, a • x = 0} ≃ LinearMap.ker f` using `{ toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, hf]; exact x.2 b hbmem⟩ invFun := fun x => ⟨x.1, fun a ha => by`. Take `⟨u, v, rfl⟩` from `hmem a ha`. Establish `hx : b • (x.1 : M ⧸ P) = 0` using `by rw [← hf]; exact x.2`. Rewrite using `[add_smul, mul_smul, mul_smul, hcX, hx, smul_zero, smul_zero, add_zero]⟩`. Use `left_inv := fun x => rfl`.

Use `right_inv := fun x => rfl }`. Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)`. Establish `h2` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)`. Establish `h3 : Nat.card ((M ⧸ P) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f)` using `Nat.card_congr f.quotKerEquivRange.toEquiv`. Establish `hpos : 0 < Nat.card (LinearMap.range f)` using `Nat.card_pos`.

Establish `hker : Nat.card (LinearMap.ker f) = Nat.card ((M ⧸ P) ⧸ LinearMap.range f)`. Rewrite `h1` using `[h3]`. Establish `h4` using `h1.symm.trans h2`. Conclude with `Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h4)`. Establish `hPle : P ≤ 𝔟 • ⊤` using `Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb)`.

Establish `hrange : LinearMap.range f = Submodule.map P.mkQ (𝔟 • ⊤)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H m => exact ⟨b • m, Submodule.smul_mem_smul hbmem trivial, by simp [hf]⟩`.

Introduce and unpack `_ ⟨m, hm, rfl⟩`. Use `Submodule.smul_induction_on (p := fun m => P.mkQ m ∈ LinearMap.range f) hm ?_ ?_` and prove the remaining obligations. Introduce `a ha n _`. Take `⟨u, v, rfl⟩` from `hmem a ha`. Use `⟨v • P.mkQ n, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf, map_smul, add_smul, mul_smul, mul_smul, hcX, smul_zero, zero_add]`. Conclude with `smul_comm _ _ _`. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.

Establish `hQ : Nat.card ((M ⧸ P) ⧸ LinearMap.range f) = Nat.card (M ⧸ (𝔟 • ⊤ : Submodule (𝓞 K) M))`. Rewrite using `[hrange]`. Conclude with `Nat.card_congr (Submodule.quotientQuotientEquivQuotient P (𝔟 • ⊤) hPle).toEquiv`. Establish `hM` using `GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) 𝔟`. Rewrite using `[Nat.card_congr e1, hker, hQ, hM, hd, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`.
-/
theorem card_killed_eq : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M],
    Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K →
    ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 →
    Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} =
      Ideal.absNorm 𝔟 ^ r := by
  intro K _ _ M _ _ hfree hfin r hr 𝔟 c hc hcb
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have hd := finrank_eq (K := K) (M := M) r hr
  have hc0 : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc.ne'
  have hspan : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc0
  have hb : 𝔟 ≠ ⊥ := fun h => hc0 (by rw [h] at hcb; exact (Submodule.mem_bot _).1 hcb)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hspan
  haveI : Finite (𝓞 K ⧸ 𝔟) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have hX := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(c : 𝓞 K)})
  have hNc : Nat.card (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) ≠ 0 := Nat.card_pos.ne'
  set P : Submodule (𝓞 K) M := Ideal.span {(c : 𝓞 K)} • ⊤ with hP
  haveI : Finite (M ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hNc)
  obtain ⟨b, hbsup⟩ := IsDedekindDomain.exists_sup_span_eq ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb) hspan
  have hcX : ∀ x : M ⧸ P, (c : 𝓞 K) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  let f : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P) := b • LinearMap.id
  have hf : ∀ x, f x = b • x := fun x => rfl
  have hmem : ∀ a ∈ 𝔟, ∃ u v : 𝓞 K, a = u * c + v * b := by
    intro a ha
    rw [← hbsup, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨u, v, rfl⟩
  have hbmem : b ∈ 𝔟 := hbsup ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  have e1 : {x : M ⧸ P // ∀ a ∈ 𝔟, a • x = 0} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, hf]; exact x.2 b hbmem⟩
      invFun := fun x => ⟨x.1, fun a ha => by
        obtain ⟨u, v, rfl⟩ := hmem a ha
        have hx : b • (x.1 : M ⧸ P) = 0 := by rw [← hf]; exact x.2
        rw [add_smul, mul_smul, mul_smul, hcX, hx, smul_zero, smul_zero, add_zero]⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((M ⧸ P) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hker : Nat.card (LinearMap.ker f) = Nat.card ((M ⧸ P) ⧸ LinearMap.range f) := by
    rw [h3] at h1
    have h4 := h1.symm.trans h2
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h4)
  have hPle : P ≤ 𝔟 • ⊤ := Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb)
  have hrange : LinearMap.range f = Submodule.map P.mkQ (𝔟 • ⊤) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H m => exact ⟨b • m, Submodule.smul_mem_smul hbmem trivial, by simp [hf]⟩
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.smul_induction_on (p := fun m => P.mkQ m ∈ LinearMap.range f) hm ?_ ?_
      · intro a ha n _
        obtain ⟨u, v, rfl⟩ := hmem a ha
        refine ⟨v • P.mkQ n, ?_⟩
        rw [hf, map_smul, add_smul, mul_smul, mul_smul, hcX, smul_zero, zero_add]
        exact smul_comm _ _ _
      · intro x y hx hy
        rw [map_add]
        exact add_mem hx hy
  have hQ : Nat.card ((M ⧸ P) ⧸ LinearMap.range f) = Nat.card (M ⧸ (𝔟 • ⊤ : Submodule (𝓞 K) M)) := by
    rw [hrange]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotient P (𝔟 • ⊤) hPle).toEquiv
  have hM := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) 𝔟
  rw [Nat.card_congr e1, hker, hQ, hM, hd, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

end GlobalTheory.TorsQuotCount
