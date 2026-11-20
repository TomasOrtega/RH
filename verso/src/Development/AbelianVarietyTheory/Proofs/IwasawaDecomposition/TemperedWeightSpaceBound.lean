import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedFrobeniusEigenvalueSizes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `(hp.2 n).2.2 hv`.

Establish `: u = 0`. Establish `: u ∈ (⊥ : Submodule Complex V)` using `h0 ▸ hu`. Simplify using `using this`. Simplify using `[this]`. Introduce `h0`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `h1 : (N ^ n) v ∈ absSpace f (q ^ ((n : Real) / 2))` using `(hp.2 n).1 hv`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Use `(hp.2 n).2.1 hv (zero_mem _) (by simpa using h1)` as an intermediate fact.

Simplify using `[this]`.
-/
theorem IsPurePair.absSpace_neg_eq_bot_iff {V : Type*} [AddCommGroup V] [Module Complex V]
    {q : Real} {f N : Module.End Complex V} (hp : IsPurePair q f N) (n : Nat) :
    absSpace f (q ^ (-(n : Real) / 2)) = ⊥ ↔ absSpace f (q ^ ((n : Real) / 2)) = ⊥ := by
  constructor
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (hp.2 n).2.2 hv
    have : u = 0 := by
      have : u ∈ (⊥ : Submodule Complex V) := h0 ▸ hu
      simpa using this
    simp [this]
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (N ^ n) v ∈ absSpace f (q ^ ((n : Real) / 2)) := (hp.2 n).1 hv
    rw [h0, Submodule.mem_bot] at h1
    have := (hp.2 n).2.1 hv (zero_mem _) (by simpa using h1)
    simp [this]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h V _ _ _ a ha hV`. Establish `hp` using `ha (frob h) deg_frob`. Use `set q : ℝ := ((normV w : ℕ) : ℝ)`. Establish `hw : ∀ k : ℤ, wtSpace a k = absSpace (a.ρ (frob h)) (q ^ ((k : ℝ) / 2))` using `fun _ => rfl`. Establish `hneg : ∀ n : ℕ, wtSpace a (-(n : ℤ)) = ⊥ ↔ wtSpace a (n : ℤ) = ⊥`.

Introduce `n`. Rewrite using `[hw, hw]`. Use `push_cast`. Conclude with `IsPurePair.absSpace_neg_eq_bot_iff hp n`. Use `set d := Module.finrank ℂ V`.

Establish `hbig : ∀ k : ℤ, (d : ℤ) ≤ |k| → wtSpace a k = ⊥` using `fun k hk => hp.absSpace_eq_bot_of_finrank_le a.nilpotent hk`. Establish `hex : ∃ n : ℕ, wtSpace a (n : ℤ) ≠ ⊥`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hall : ∀ i : ℤ, wtSpace a i = ⊥`.

Introduce `i`. Break down `le_total 0 i with hi | hi` into its components or cases. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hi`. Conclude with `hc n`. Take `⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ)` from `⟨(-i).toNat, by omega⟩`.

Conclude with `(hneg n).2 (hc n)`. Establish `htop` using `hp.1`. Simplify using `only [← hw, hall, iSup_bot] at htop`. Conclude with `bot_ne_top htop`. Set `P : ℕ → Prop` to `fun n => wtSpace a (n : ℤ) ≠ ⊥`.

Take `⟨n₀, hn₀⟩` from `hex`. Establish `hn₀d : n₀ ≤ d`. Assume the negation of the conclusion as `hc`. Conclude with `hn₀ (hbig _ (by rw [abs_of_nonneg (by positivity)]; omega))`. Use `⟨Nat.findGreatest P d, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ne, hneg]`. Conclude with `Nat.findGreatest_spec (P := P) hn₀d hn₀`. Introduce `k hk`. Establish `hk0 : 0 ≤ k` using `le_trans (by positivity) hk.le`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hk0`.

Establish `hn : Nat.findGreatest P d < n` using `by exact_mod_cast hk`. Distinguish the cases in `hnd : n ≤ d`. Use `Nat.findGreatest_is_greatest (P := P) hn hnd` as an intermediate fact. Simplify `this` using `[P]`. Conclude with `hbig _ (by rw [abs_of_nonneg (by positivity)]; omega)`.
-/
theorem exists_top_weight :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), a.Tempered →
      Nontrivial V → ∃ m : ℕ, wtSpace a (-(m : ℤ)) ≠ ⊥ ∧ ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥ := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a ha hV
  have hp := ha (frob h) deg_frob
  set q : ℝ := ((normV w : ℕ) : ℝ)
  have hw : ∀ k : ℤ, wtSpace a k = absSpace (a.ρ (frob h)) (q ^ ((k : ℝ) / 2)) := fun _ => rfl
  have hneg : ∀ n : ℕ, wtSpace a (-(n : ℤ)) = ⊥ ↔ wtSpace a (n : ℤ) = ⊥ := by
    intro n
    rw [hw, hw]
    push_cast
    exact IsPurePair.absSpace_neg_eq_bot_iff hp n
  set d := Module.finrank ℂ V
  have hbig : ∀ k : ℤ, (d : ℤ) ≤ |k| → wtSpace a k = ⊥ := fun k hk =>
    hp.absSpace_eq_bot_of_finrank_le a.nilpotent hk

  have hex : ∃ n : ℕ, wtSpace a (n : ℤ) ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    have hall : ∀ i : ℤ, wtSpace a i = ⊥ := by
      intro i
      rcases le_total 0 i with hi | hi
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        exact hc n
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
        exact (hneg n).2 (hc n)
    have htop := hp.1
    simp only [← hw, hall, iSup_bot] at htop
    exact bot_ne_top htop
  classical
  let P : ℕ → Prop := fun n => wtSpace a (n : ℤ) ≠ ⊥
  obtain ⟨n₀, hn₀⟩ := hex
  have hn₀d : n₀ ≤ d := by
    by_contra hc
    exact hn₀ (hbig _ (by rw [abs_of_nonneg (by positivity)]; omega))
  refine ⟨Nat.findGreatest P d, ?_, ?_⟩
  · rw [Ne, hneg]
    exact Nat.findGreatest_spec (P := P) hn₀d hn₀
  · intro k hk
    have hk0 : 0 ≤ k := le_trans (by positivity) hk.le
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hn : Nat.findGreatest P d < n := by exact_mod_cast hk
    by_cases hnd : n ≤ d
    · have := Nat.findGreatest_is_greatest (P := P) hn hnd
      simpa [P] using this
    · exact hbig _ (by rw [abs_of_nonneg (by positivity)]; omega)

end GlobalTheory.WeilDeligne.PrimDecomp
