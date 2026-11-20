import Development.EtaleCohomology.KummerTheory.PlacePf

noncomputable section

namespace LateralTheory.KummerTheory

def PlaceGood (k K : Type) [Field k] [Field K] [Algebra k K] (A : LocalSubring K) : Prop :=
  (∀ c : k, algebraMap k K c ∈ A.toSubring) ∧
    ∀ a ∈ A.toSubring, ∃ c : k, a = algebraMap k K c ∨ (a - algebraMap k K c)⁻¹ ∉ A.toSubring

def PlaceZorn : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K],
  ∃ A : LocalSubring K, PlaceGood k K A ∧ ∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A

def PlaceStep : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → (∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A) →
    ∀ x : K, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

/- English proof (translation)
Introduce `k K _ _ _ _ _`. Take `⟨A, hA, hmax⟩` from `h1 k K`. Establish `hv` using `h2 k K A hA hmax`. Set `T : ValuationSubring K` to `⟨A.toSubring, hv⟩`. Set `σ : k →+* T` to `(algebraMap k K).codRestrict T (fun c => hA.1 c)`.

Use `⟨T, σ, fun x => rfl, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨c, hc⟩` from `hA.2 a a.2`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply]`. Apply `Ideal.Quotient.eq.mpr` to reduce the goal to its premises. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨w, hw⟩` from `isUnit_iff_exists_inv.mp hu`.

Establish `hK : ((σ c : K) - (a : K)) * (w : K) = 1`. Use `congrArg (fun z : T => (z : K)) hw` as an intermediate fact. Simplify using `using this`. Break down `hc with h | h` into its components or cases. Establish `: (σ c : K) - (a : K) = 0` using `by rw [h]; simp [σ]`.

Rewrite `hK` using `[this, zero_mul]`. Conclude with `zero_ne_one hK`. Apply `h` to reduce the goal to its premises. Establish `hinv : ((σ c : K) - (a : K))⁻¹ = (w : K)` using `inv_eq_of_mul_eq_one_right hK`. Establish `: ((a : K) - algebraMap k K c)⁻¹ = -(w : K)`.

Rewrite using `[← hinv, ← inv_neg, neg_sub]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `T.neg_mem _ w.2`.
-/
theorem PlaceEx_of (h1 : PlaceZorn) (h2 : PlaceStep) : PlaceEx := by
  intro k K _ _ _ _ _
  obtain ⟨A, hA, hmax⟩ := h1 k K
  have hv := h2 k K A hA hmax
  let T : ValuationSubring K := ⟨A.toSubring, hv⟩
  let σ : k →+* T := (algebraMap k K).codRestrict T (fun c => hA.1 c)
  refine ⟨T, σ, fun x => rfl, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hA.2 a a.2
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  have hK : ((σ c : K) - (a : K)) * (w : K) = 1 := by
    have := congrArg (fun z : T => (z : K)) hw
    simpa using this
  rcases hc with h | h
  · have : (σ c : K) - (a : K) = 0 := by rw [h]; simp [σ]
    rw [this, zero_mul] at hK; exact zero_ne_one hK
  · apply h
    have hinv : ((σ c : K) - (a : K))⁻¹ = (w : K) := inv_eq_of_mul_eq_one_right hK
    have : ((a : K) - algebraMap k K c)⁻¹ = -(w : K) := by
      rw [← hinv, ← inv_neg, neg_sub]; rfl
    rw [this]; exact T.neg_mem _ w.2

end LateralTheory.KummerTheory
