import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob

noncomputable section

namespace UpperTheory.V.Af

/- English proof (translation)
Establish `key : ∀ T : Finset Y, (↑T : Set Y) ⊆ f '' Sig → T.card ≤ N`. Introduce `T hT`. Establish `hpre : ∀ y : T, ∃ a, a ∈ Sig ∧ f a = y.1` using `fun y => hT y.2`. Use `choose g hgS hgf using hpre`. Establish `hinj : Function.Injective g`.

Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hgf x, ← hgf y, hxy]`. Establish `hS` using `hcard (Finset.univ.image g) ?_ ?_`. Rewrite `hS` using `[Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]`. Then use the resulting hypothesis.

Introduce `a ha`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.mp ha`. Conclude with `hgS y`. Introduce `a ha b hb hab`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.mp ha`.

Take `⟨y, -, rfl⟩` from `Finset.mem_image.mp hb`. Establish `hxy` using `hiso _ (hgS x) _ (hgS y) hab`. Rewrite `hxy` using `[hgf x, hgf y]`. Rewrite using `[Subtype.ext hxy]`. Establish `hfin : (f '' Sig).Finite`.

Assume the negation of the conclusion as `hinf`. Take `⟨t, ht, htc⟩` from `Set.Infinite.exists_subset_card_eq hinf (N + 1)`. Use `key t ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨hfin.to_subtype, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]`. Conclude with `key _ (by simp)`.
-/
theorem finite_image_of_card_le {P Y : Type} (Sig : Set P) (Iso : P → P → Prop) (f : P → Y)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → f a = f b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N) :
    Finite ↥(f '' Sig) ∧ Nat.card ↥(f '' Sig) ≤ N := by
  classical
  have key : ∀ T : Finset Y, (↑T : Set Y) ⊆ f '' Sig → T.card ≤ N := by
    intro T hT
    have hpre : ∀ y : T, ∃ a, a ∈ Sig ∧ f a = y.1 := fun y => hT y.2
    choose g hgS hgf using hpre
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← hgf x, ← hgf y, hxy]
    have hS := hcard (Finset.univ.image g) ?_ ?_
    · rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] at hS
    · intro a ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ha
      exact hgS y
    · intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
      have hxy := hiso _ (hgS x) _ (hgS y) hab
      rw [hgf x, hgf y] at hxy
      rw [Subtype.ext hxy]
  have hfin : (f '' Sig).Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := key t ht
    omega
  refine ⟨hfin.to_subtype, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  exact key _ (by simp)

/- English proof (translation)
Take `⟨hfin, hN⟩` from `finite_image_of_card_le Sig Iso sys hiso N hcard`. Use `⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN, fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, a, ha, rfl⟩`. Simplify using `using hn a ha`. Introduce `σ`.

Establish `hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig`. Introduce and unpack `⟨_, a, ha, rfl⟩`. Take `⟨b, hb, h⟩` from `hconj σ a ha`. Conclude with `⟨b, hb, funext h⟩`. Set `F : ↥(sys '' Sig) → ↥(sys '' Sig)` to `fun s => ⟨_, hmem s⟩`.

Establish `hF : Function.Injective F`. Introduce `s s' h`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Conclude with `Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)`. Use `⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩` and prove the remaining obligations.

Simplify using `[F, Multiset.map_map]`. Introduce and unpack `⟨_, a, ha, rfl⟩ b hb`. Take `⟨c, hc, rfl⟩` from `Multiset.mem_map.1 hb`. Rewrite using `[norm_inv, hpure a ha c hc, ← Real.rpow_neg (Nat.cast_nonneg q)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `k hk ⟨_, a, ha, rfl⟩ b hb`. Take `⟨c, hc, rfl⟩` from `Multiset.mem_map.1 hb`. Conclude with `(hint a ha c hc).1 k hk`. Introduce and unpack `k hk ⟨_, a, ha, rfl⟩ b hb`.

Take `⟨c, hc, rfl⟩` from `Multiset.mem_map.1 hb`. Rewrite using `[inv_inv]`. Conclude with `(hint a ha c hc).2 k hk`. Simplify using `[Multiset.map_map]`.
-/
theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hpure : ∀ a ∈ Sig, ∀ b ∈ sys a w, ‖b‖ = (q : ℝ) ^ (-(wt : ℝ) / 2))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_inv, hpure a ha c hc, ← Real.rpow_neg (Nat.cast_nonneg q)]
    congr 1
    ring
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]

open NumberField IsDedekindDomain in

/- English proof (translation)
Introduce `hMw`. Establish `hcop : Nat.Coprime p M` using `(Nat.Prime.coprime_iff_not_dvd hp).mpr hM`. Establish `h` using `Nat.gcd_eq_gcd_ab p M`. Rewrite `h` using `[Nat.Coprime.gcd_eq_one hcop]`. Establish `h1 : (1 : 𝓞 F) = (p : 𝓞 F) * (Nat.gcdA p M : 𝓞 F) + (M : 𝓞 F) * (Nat.gcdB p M : 𝓞 F)`.

Establish `h'` using `congrArg (Int.cast : ℤ → 𝓞 F) h`. Move the coercions through the operations in `at h'`. Conclude with `h'`. Establish `hone : (1 : 𝓞 F) ∈ w.asIdeal`. Rewrite using `[h1]`.

Conclude with `w.asIdeal.add_mem (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_right _ _ hMw)`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)`.
-/
theorem natCast_notMem_of_not_dvd {F : Type} [Field F] [NumberField F] {p M : ℕ} (hp : p.Prime)
    {w : HeightOneSpectrum (𝓞 F)} (hw : (p : 𝓞 F) ∈ w.asIdeal) (hM : ¬ p ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := by
  intro hMw
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hM
  have h := Nat.gcd_eq_gcd_ab p M
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  have h1 : (1 : 𝓞 F) = (p : 𝓞 F) * (Nat.gcdA p M : 𝓞 F) + (M : 𝓞 F) * (Nat.gcdB p M : 𝓞 F) := by
    have h' := congrArg (Int.cast : ℤ → 𝓞 F) h
    push_cast at h'
    exact h'
  have hone : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [h1]
    exact w.asIdeal.add_mem (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_right _ _ hMw)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

open NumberField IsDedekindDomain in

/- English proof (translation)
Rewrite using `[Filter.eventually_cofinite]`. Establish `hM' : (M : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.mpr hM`. Establish `hI : Ideal.span {(M : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hM'`.

Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Set.mem_setOf_eq, not_not] at hw ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hw`.
-/
theorem eventually_natCast_notMem {F : Type} [Field F] [NumberField F] {M : ℕ} (hM : M ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (M : 𝓞 F) ∉ w.asIdeal := by
  rw [Filter.eventually_cofinite]
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hI : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hM'
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

end UpperTheory.V.Af
