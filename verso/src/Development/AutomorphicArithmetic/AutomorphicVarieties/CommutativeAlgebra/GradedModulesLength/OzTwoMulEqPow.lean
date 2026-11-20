import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

/- English proof (translation)
Substitute `hc` using the available equality. Use `Submodule.mul_induction_on hf (fun p hp q hq => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `Submodule.mul_mem_mul hp (SetLike.GradedMul.mul_mem hz hq)`. Rewrite using `[mul_add]`.

Conclude with `add_mem hp hq`.
-/
private theorem absR {w a b c : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + b) :
    z * f ∈ 𝒜 a * 𝒜 c := by
  subst hc
  refine Submodule.mul_induction_on hf (fun p hp q hq => ?_) (fun p q hp hq => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul hp (SetLike.GradedMul.mul_mem hz hq)
  · rw [mul_add]; exact add_mem hp hq

/- English proof (translation)
Substitute `hd` using the available equality. Rewrite `hf` using `[mul_comm (𝒜 a)]`. Rewrite using `[mul_comm (𝒜 c)]`. Conclude with `absR 𝒜 hz hf hc`.
-/
private theorem absL {w a b c d : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + a) (hd : d = b) :
    z * f ∈ 𝒜 c * 𝒜 d := by
  subst hd
  rw [mul_comm (𝒜 a)] at hf
  rw [mul_comm (𝒜 c)]
  exact absR 𝒜 hz hf hc

private def dec (ε j : ℤ) : Submodule O A where
  carrier := {f | f ∈ 𝒜 j ∧ (1 ≤ ε * j → f ∈ 𝒜 ε * 𝒜 (j - ε) ⊔ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε)) ∧
    (2 ≤ ε * j → f ∈ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε))}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun h => add_mem (ha.2.1 h) (hb.2.1 h), fun h => add_mem (ha.2.2 h) (hb.2.2 h)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ ha := ⟨Submodule.smul_mem _ c ha.1, fun h => Submodule.smul_mem _ c (ha.2.1 h),
    fun h => Submodule.smul_mem _ c (ha.2.2 h)⟩

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `hf`. Use `⟨SetLike.GradedMul.mul_mem hz h0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `c2 : w = 2 * ε`. Substitute `c2` using the available equality. Establish `: z * f ∈ 𝒜 (2 * ε) * 𝒜 (2 * ε + j - 2 * ε)`.

Rewrite using `[add_sub_cancel_left]`. Conclude with `Submodule.mul_mem_mul hz h0`. Conclude with `⟨fun _ => Submodule.mem_sup_right this, fun _ => this⟩`. Distinguish the cases in `c1 : w = ε`. Substitute `c1` using the available equality.

Use `⟨fun _ => Submodule.mem_sup_left ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_cancel_left]`. Conclude with `Submodule.mul_mem_mul hz h0`. Apply the tactic sequence `obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))`. Rewrite using `[mul_add]`.

Conclude with `add_mem (absL 𝒜 hz hp (by ring) (by ring)) (absR 𝒜 hz hq (by ring))`. Apply the tactic sequence `refine ⟨fun h => ?_, fun h => absR 𝒜 hz (h2 (by rcases hε with rfl | rfl <;> omega)) (by ring)⟩`. Apply the tactic sequence `obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))`. Rewrite using `[mul_add]`. Conclude with `add_mem (Submodule.mem_sup_left (absR 𝒜 hz hp (by ring))) (Submodule.mem_sup_right (absR 𝒜 hz hq (by ring)))`.
-/
private theorem dec_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w j : ℤ} (hw : -2 ≤ w ∧ w ≤ 2) {z f : A} (hz : z ∈ 𝒜 w)
    (hf : f ∈ dec 𝒜 ε j) : z * f ∈ dec 𝒜 ε (w + j) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨SetLike.GradedMul.mul_mem hz h0, ?_⟩
  by_cases c2 : w = 2 * ε
  · subst c2
    have : z * f ∈ 𝒜 (2 * ε) * 𝒜 (2 * ε + j - 2 * ε) := by
      rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    exact ⟨fun _ => Submodule.mem_sup_right this, fun _ => this⟩
  by_cases c1 : w = ε
  · subst c1
    refine ⟨fun _ => Submodule.mem_sup_left ?_, fun h => ?_⟩
    · rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    · obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
      rw [mul_add]
      exact add_mem (absL 𝒜 hz hp (by ring) (by ring)) (absR 𝒜 hz hq (by ring))
  refine ⟨fun h => ?_, fun h => absR 𝒜 hz (h2 (by rcases hε with rfl | rfl <;> omega)) (by ring)⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
  rw [mul_add]
  exact add_mem (Submodule.mem_sup_left (absR 𝒜 hz hp (by ring))) (Submodule.mem_sup_right (absR 𝒜 hz hq (by ring)))

/- English proof (translation)
Take `⟨s, hs, htop⟩` from `hx.gen`. Establish `gen : ∀ (w : ℤ), (-2 ≤ w ∧ w ≤ 2) → ∀ z ∈ 𝒜 w, ∀ g ∈ ⨆ i, dec 𝒜 ε i, z * g ∈ ⨆ i, dec 𝒜 ε i`. Introduce `w hw z hz g hg`. Use `Submodule.iSup_induction (motive := fun g => z * g ∈ ⨆ i, dec 𝒜 ε i) _ hg (fun i g hg => ?_) (by simp) (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb)` and prove the remaining obligations. Conclude with `Submodule.mem_iSup_of_mem _ (dec_mul 𝒜 hε hw hz hg)`.

Establish `key : ∀ a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ s), ∀ g ∈ ⨆ i, dec 𝒜 ε i, a * g ∈ ⨆ i, dec 𝒜 ε i`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Break down `ha with ha | ha` into its components or cases.

Conclude with `gen 0 (by omega) a ha`. Apply the tactic sequence `rcases hs a ha with h | h | h | h <;> exact gen _ (by omega) a h`. Consider the case `algebraMap c`. Introduce `g hg`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem _ c hg`. Consider the case `add a b _ _ ha hb`. Introduce `g hg`. Rewrite using `[add_mul]`. Conclude with `add_mem (ha g hg) (hb g hg)`.

Consider the case `mul a b _ _ ha hb`. Introduce `g hg`. Rewrite using `[mul_assoc]`. Conclude with `ha _ (hb g hg)`. Establish `h1 : (1 : A) ∈ dec 𝒜 ε 0` using `⟨SetLike.GradedOne.one_mem, fun h => by omega, fun h => by omega⟩`.

Establish `h2` using `key f (htop ▸ Algebra.mem_top) 1 (Submodule.mem_iSup_of_mem _ h1)`. Rewrite `h2` using `[mul_one]`. Establish `h3 : ∀ g ∈ ⨆ i, dec 𝒜 ε i, (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j`. Introduce `g hg`. Use `Submodule.iSup_induction (motive := fun g => (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j) _ hg (fun i g hg => ?_) (by simp) (fun a b ha hb => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Rewrite using `[DirectSum.decompose_of_mem_same 𝒜 hg.1]` and apply the resulting hypothesis. Rewrite using `[DirectSum.decompose_of_mem_ne 𝒜 hg.1 hi]`. Conclude with `zero_mem _`.

Simplify using `only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]`. Conclude with `add_mem ha hb`. Establish `h4` using `h3 f h2`. Rewrite `h4` using `[DirectSum.decompose_of_mem_same 𝒜 hf]`. Then use the resulting hypothesis.
-/
private theorem dec_all [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : f ∈ dec 𝒜 ε j := by
  obtain ⟨s, hs, htop⟩ := hx.gen
  have gen : ∀ (w : ℤ), (-2 ≤ w ∧ w ≤ 2) → ∀ z ∈ 𝒜 w, ∀ g ∈ ⨆ i, dec 𝒜 ε i, z * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro w hw z hz g hg
    refine Submodule.iSup_induction (motive := fun g => z * g ∈ ⨆ i, dec 𝒜 ε i) _ hg (fun i g hg => ?_) (by simp)
      (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb)
    exact Submodule.mem_iSup_of_mem _ (dec_mul 𝒜 hε hw hz hg)
  have key : ∀ a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ s), ∀ g ∈ ⨆ i, dec 𝒜 ε i, a * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact gen 0 (by omega) a ha
      · rcases hs a ha with h | h | h | h <;> exact gen _ (by omega) a h
    | algebraMap c =>
      intro g hg
      rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c hg
    | add a b _ _ ha hb =>
      intro g hg
      rw [add_mul]; exact add_mem (ha g hg) (hb g hg)
    | mul a b _ _ ha hb =>
      intro g hg
      rw [mul_assoc]; exact ha _ (hb g hg)
  have h1 : (1 : A) ∈ dec 𝒜 ε 0 := ⟨SetLike.GradedOne.one_mem, fun h => by omega, fun h => by omega⟩
  have h2 := key f (htop ▸ Algebra.mem_top) 1 (Submodule.mem_iSup_of_mem _ h1)
  rw [mul_one] at h2
  have h3 : ∀ g ∈ ⨆ i, dec 𝒜 ε i, (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j := by
    intro g hg
    refine Submodule.iSup_induction (motive := fun g => (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j) _ hg
      (fun i g hg => ?_) (by simp) (fun a b ha hb => ?_)
    · by_cases hi : i = j
      · subst hi
        rwa [DirectSum.decompose_of_mem_same 𝒜 hg.1]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hg.1 hi]; exact zero_mem _
    · simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem ha hb
  have h4 := h3 f h2
  rwa [DirectSum.decompose_of_mem_same 𝒜 hf] at h4

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use extensionality with `f`. Simplify using `only [Nat.cast_zero, mul_zero, pow_zero, mem_oz, Submodule.mem_one]`. Conclude with `⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩`.

Consider the case `succ n ih`. Rewrite using `[pow_succ, mul_comm (_ ^ n), ← ih]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Apply the tactic sequence `have h := (dec_all 𝒜 hx hε hf).2.2 (by rcases hε with rfl | rfl <;> push_cast <;> omega)`.

Establish `e : 2 * ε * ((n + 1 : ℕ) : ℤ) - 2 * ε = 2 * ε * n` using `by push_cast; ring`. Rewrite `h` using `[e]`. Use `clear hf`. Use `Submodule.mul_induction_on h (fun p hp q hq => ?_) (fun p q hp hq => add_mem hp hq)` and prove the remaining obligations. Conclude with `Submodule.mul_mem_mul hp hq`.

Use `Submodule.mul_le.2 fun p hp q hq => ?_` and prove the remaining obligations. Establish `e : 2 * ε * ((n + 1 : ℕ) : ℤ) = 2 * ε + 2 * ε * n` using `by push_cast; ring`. Rewrite using `[mem_oz, e]`. Conclude with `SetLike.GradedMul.mul_mem (A := 𝒜) hp hq`.
-/
private theorem pow_eps [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (n : ℕ) : oz 𝒜 (2 * ε * n) = oz 𝒜 (2 * ε) ^ n := by
  induction n with
  | zero =>
    ext f
    simp only [Nat.cast_zero, mul_zero, pow_zero, mem_oz, Submodule.mem_one]
    exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  | succ n ih =>
    rw [pow_succ, mul_comm (_ ^ n), ← ih]
    apply le_antisymm
    · intro f hf
      have h := (dec_all 𝒜 hx hε hf).2.2 (by rcases hε with rfl | rfl <;> push_cast <;> omega)
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) - 2 * ε = 2 * ε * n := by push_cast; ring
      rw [e] at h
      clear hf
      refine Submodule.mul_induction_on h (fun p hp q hq => ?_) (fun p q hp hq => add_mem hp hq)
      exact Submodule.mul_mem_mul hp hq
    · refine Submodule.mul_le.2 fun p hp q hq => ?_
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) = 2 * ε + 2 * ε * n := by push_cast; ring
      rw [mem_oz, e]
      exact SetLike.GradedMul.mul_mem (A := 𝒜) hp hq

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O _ _ _ _ _ A _ _ 𝒜 _ _ x hx n`. Establish `h1` using `pow_eps 𝒜 hx (Or.inr rfl) n`. Establish `h2` using `pow_eps 𝒜 hx (Or.inl rfl) n`. Establish `e : (2 * -1 * n : ℤ) = -(2 * n)` using `by ring`. Rewrite `h1` using `[e]`.

Rewrite `h2` using `[mul_one]`. Conclude with `⟨h1, h2⟩`.
-/
theorem UpperTheory.V.Alg.M.oz_two_mul_eq_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx n
  have h1 := pow_eps 𝒜 hx (Or.inr rfl) n
  have h2 := pow_eps 𝒜 hx (Or.inl rfl) n
  have e : (2 * -1 * n : ℤ) = -(2 * n) := by ring
  rw [e] at h1
  rw [mul_one] at h2
  exact ⟨h1, h2⟩
