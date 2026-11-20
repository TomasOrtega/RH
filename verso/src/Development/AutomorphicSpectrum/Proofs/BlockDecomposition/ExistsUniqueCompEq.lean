import Mathlib

namespace GlobalTheory.CompanionTheory.PfCompl

open Ideal

variable {B T T₁ : Type*} [CommRing B] [CommRing T] [CommRing T₁]

/- English proof (translation)
Establish `hIJ : span {π ^ M} ≤ (span {g π ^ M}).comap g`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hxK : span {π ^ M} ≤ ((span {x π}) ^ M).comap x`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]`.

Conclude with `Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M`. Establish `hinj' : Function.Injective (Ideal.quotientMap (span {g π ^ M}) g hIJ)`. Use `Ideal.quotientMap_injective' ?_` and prove the remaining obligations. Introduce `b hb`. Conclude with `hinj b (Ideal.mem_comap.1 hb)`.

Establish `hsurj' : Function.Surjective (Ideal.quotientMap (span {g π ^ M}) g hIJ)`. Introduce `z`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨b, hb⟩` from `hsurj y`. Conclude with `⟨Ideal.Quotient.mk _ b, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hb).symm⟩`.

Set `e` to `RingEquiv.ofBijective _ ⟨hinj', hsurj'⟩`. Use `⟨(Ideal.quotientMap _ x hxK).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk _)), ?_⟩` and prove the remaining obligations. Introduce `y b hy`. Establish `h1 : e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (span {g π ^ M}) y` using `by show Ideal.quotientMap _ g hIJ (Ideal.Quotient.mk _ b) = _`. Rewrite using `[Ideal.quotientMap_mk]`.

Conclude with `(Ideal.Quotient.eq.2 hy).symm`. Establish `h2 : e.symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (span {π ^ M}) b`. Rewrite using `[← h1, RingEquiv.symm_apply_apply]`. Use `show Ideal.quotientMap _ x hxK (e.symm (Ideal.Quotient.mk _ y)) = _`. Rewrite using `[h2, Ideal.quotientMap_mk]`.
-/
theorem exists_level_hom (π : B) (g : B →+* T) (x : B →+* T₁) (M : ℕ)
    (hsurj : ∀ y : T, ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ b, g b ∈ span {g π ^ M} → b ∈ span {π ^ M}) :
    ∃ f : T →+* T₁ ⧸ (span {x π}) ^ M,
      ∀ y b, y - g b ∈ span {g π ^ M} → f y = Ideal.Quotient.mk _ (x b) := by
  have hIJ : span {π ^ M} ≤ (span {g π ^ M}).comap g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hxK : span {π ^ M} ≤ ((span {x π}) ^ M).comap x := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M
  have hinj' : Function.Injective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    refine Ideal.quotientMap_injective' ?_
    intro b hb
    exact hinj b (Ideal.mem_comap.1 hb)
  have hsurj' : Function.Surjective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hb).symm⟩
  let e := RingEquiv.ofBijective _ ⟨hinj', hsurj'⟩
  refine ⟨(Ideal.quotientMap _ x hxK).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk _)), ?_⟩
  intro y b hy
  have h1 : e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (span {g π ^ M}) y := by
    show Ideal.quotientMap _ g hIJ (Ideal.Quotient.mk _ b) = _
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 hy).symm
  have h2 : e.symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (span {π ^ M}) b := by
    rw [← h1, RingEquiv.symm_apply_apply]
  show Ideal.quotientMap _ x hxK (e.symm (Ideal.Quotient.mk _ y)) = _
  rw [h2, Ideal.quotientMap_mk]

/- English proof (translation)
Establish `hb : x b = ψ (g b)` using `(DFunLike.congr_fun hψ b).symm`. Establish `hπ : ψ (g π) = x π` using `DFunLike.congr_fun hψ π`. Rewrite using `[Ideal.Quotient.eq, hb, ← map_sub]`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[← ht, map_mul, map_pow, hπ]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M)`.
-/
theorem mk_eq_of_comp_eq (π : B) (g : B →+* T) (x : B →+* T₁) (ψ : T →+* T₁)
    (hψ : ψ.comp g = x) (M : ℕ) (y : T) (b : B) (hy : y - g b ∈ span {g π ^ M}) :
    Ideal.Quotient.mk ((span {x π}) ^ M) (ψ y) = Ideal.Quotient.mk _ (x b) := by
  have hb : x b = ψ (g b) := (DFunLike.congr_fun hψ b).symm
  have hπ : ψ (g π) = x π := DFunLike.congr_fun hψ π
  rw [Ideal.Quotient.eq, hb, ← map_sub]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy
  rw [← ht, map_mul, map_pow, hπ]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M)

/- English proof (translation)
Establish `key : ∀ a c : T₁, (∀ n : ℕ, Ideal.Quotient.mk (span {x π} ^ n) a = Ideal.Quotient.mk _ c) → a = c`. Introduce `a c h`. Establish `h0` using `IsHausdorff.haus' (I := span {x π}) (a - c) fun n => by`. Rewrite using `[SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `Ideal.Quotient.eq.1 (h n)`.

Conclude with `sub_eq_zero.1 h0`. Use `choose f hf using fun n => exists_level_hom π g x n (hsurj n) (hinj n)`. Establish `hle : ∀ {m n : ℕ}, m ≤ n → ∀ z : T, z ∈ span {g π ^ n} → z ∈ span {g π ^ m}`. Introduce `m n h z hz`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`.

Use `Ideal.mem_span_singleton'.2 ⟨t * g π ^ (n - m), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← pow_add, Nat.sub_add_cancel h]`. Establish `hcompat : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow (span {x π}) h).comp (f n) = f m`. Introduce `m n h`. Use extensionality with `y`.

Take `⟨b, hb⟩` from `hsurj n y`. Rewrite using `[RingHom.comp_apply, hf n y b hb, hf m y b (hle h _ hb)]`. Use `first`. Consider the case `rfl`. Consider the case `exact Ideal.Quotient.factor_mk _ _`.

Consider the case `simp [Ideal.Quotient.factorPow]`. Use `⟨IsAdicComplete.liftRingHom _ f hcompat, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Apply `key` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[RingHom.comp_apply, IsAdicComplete.mk_liftRingHom, hf n (g b) b (by simp)]`. Introduce `ψ hψ`. Use extensionality with `y`. Apply `key` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[IsAdicComplete.mk_liftRingHom]`. Take `⟨b, hb⟩` from `hsurj n y`. Rewrite using `[hf n y b hb]`. Conclude with `mk_eq_of_comp_eq π g x ψ hψ n y b hb`.
-/
theorem existsUnique_comp_eq (π : B) (g : B →+* T)
    (hsurj : ∀ (M : ℕ) (y : T), ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ (M : ℕ) (b : B), g b ∈ span {g π ^ M} → b ∈ span {π ^ M})
    (x : B →+* T₁) (hc : IsAdicComplete (span {x π}) T₁) :
    ∃! ψ : T →+* T₁, ψ.comp g = x := by
  have key : ∀ a c : T₁,
      (∀ n : ℕ, Ideal.Quotient.mk (span {x π} ^ n) a = Ideal.Quotient.mk _ c) → a = c := by
    intro a c h
    have h0 := IsHausdorff.haus' (I := span {x π}) (a - c) fun n => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (h n)
    exact sub_eq_zero.1 h0
  choose f hf using fun n => exists_level_hom π g x n (hsurj n) (hinj n)
  have hle : ∀ {m n : ℕ}, m ≤ n → ∀ z : T, z ∈ span {g π ^ n} → z ∈ span {g π ^ m} := by
    intro m n h z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Ideal.mem_span_singleton'.2 ⟨t * g π ^ (n - m), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow (span {x π}) h).comp (f n) = f m := by
    intro m n h
    ext y
    obtain ⟨b, hb⟩ := hsurj n y
    rw [RingHom.comp_apply, hf n y b hb, hf m y b (hle h _ hb)]
    first
      | rfl
      | exact Ideal.Quotient.factor_mk _ _
      | simp [Ideal.Quotient.factorPow]
  refine ⟨IsAdicComplete.liftRingHom _ f hcompat, ?_, ?_⟩
  · ext b
    apply key
    intro n
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom, hf n (g b) b (by simp)]
  · intro ψ hψ
    ext y
    apply key
    intro n
    rw [IsAdicComplete.mk_liftRingHom]
    obtain ⟨b, hb⟩ := hsurj n y
    rw [hf n y b hb]
    exact mk_eq_of_comp_eq π g x ψ hψ n y b hb

end GlobalTheory.CompanionTheory.PfCompl
