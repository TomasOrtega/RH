import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Introduce `Ω _ _ N _ Γ _ π χ k hN`. Use `haveI : Fact (1 < N) := ⟨hN⟩`. Establish `hsum : ∀ f : ZMod N → Ω, (∀ x, ¬ IsUnit x → f x = 0) → ∑ x, f x = ∑ u : (ZMod N)ˣ, f u`. Introduce `f hf`. Use `symm`.

Rewrite using `[show ∑ u : (ZMod N)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨Units.val, Units.val_injective⟩, f x by`. Rewrite using `[Finset.sum_map]`. Use the proof step `rfl]`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `x _ hx`.

Apply `hf` to reduce the goal to its premises. Introduce and unpack `⟨u, rfl⟩`. Conclude with `hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)`. Establish `h1 : ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k a) = ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k (a : ZMod N).val)`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations.

Take `⟨_, h2⟩` from `Finset.mem_Icc.1 ha`. Break down `h2.lt_or_eq with h | rfl` into its components or cases. Rewrite using `[ZMod.val_cast_of_lt h]`. Rewrite using `[ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul]`. Simplify using `only [thetaEl, sumEl, map_neg, map_sum, ev_single, genB, Ek]`.

Rewrite using `[h1, b_sumicc (fun x : ZMod N => dirOf π χ x * algebraMap ℚ Ω (bcoef N k x.val)), hsum _ (fun x hx => by simp [MulChar.map_nonunit _ hx])]`. Simplify using `only [dirOf_unit]`. Rewrite using `[neg_div, Finset.sum_div]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[map_div₀, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (k : ℕ), 2 ≤ N → ev ℚ χ (thetaEl k π) = -genB k (dirOf π χ) / k := by
  intro Ω _ _ N _ Γ _ π χ k hN
  haveI : Fact (1 < N) := ⟨hN⟩
  have hsum : ∀ f : ZMod N → Ω, (∀ x, ¬ IsUnit x → f x = 0) →
      ∑ x, f x = ∑ u : (ZMod N)ˣ, f u := by
    intro f hf
    symm
    rw [show ∑ u : (ZMod N)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨Units.val, Units.val_injective⟩, f x by
      rw [Finset.sum_map]; rfl]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hf
    rintro ⟨u, rfl⟩
    exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)
  have h1 : ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k a) =
      ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k (a : ZMod N).val) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨_, h2⟩ := Finset.mem_Icc.1 ha
    rcases h2.lt_or_eq with h | rfl
    · rw [ZMod.val_cast_of_lt h]
    · rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul]
  simp only [thetaEl, sumEl, map_neg, map_sum, ev_single, genB, Ek]
  rw [h1, b_sumicc (fun x : ZMod N => dirOf π χ x * algebraMap ℚ Ω (bcoef N k x.val)),
    hsum _ (fun x hx => by simp [MulChar.map_nonunit _ hx])]
  simp only [dirOf_unit]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_div₀, map_natCast]
  ring
