import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z2

open ReciprocityTheory.ChartRestriction.L3.WA

section Generic

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def IdealLike (S : Subring K) (P : K → Prop) : Prop :=
  (∀ a b, P a → P b → P (a - b)) ∧ (∀ x ∈ S, ∀ a, P a → P (x * a)) ∧ ¬ P 1

/- English proof (translation)
Use `hP.1 a _ ha (hP.2.1 (-1) (S.neg_mem S.one_mem) b hb)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IdealLike.add {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {a b : K} (ha : P a)
    (hb : P b) : P (a + b) := by
  have := hP.1 a _ ha (hP.2.1 (-1) (S.neg_mem S.one_mem) b hb)
  convert this using 1
  ring

/- English proof (translation)
Use `hP.2.1 _ hμ.2.2 _ h` as an intermediate fact. Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ hμ.1, one_mul]`. Then use the resulting hypothesis.
-/
theorem IdealLike.cancel {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {μ a : K}
    (hμ : IsUnitIn S μ) (h : P (μ * a)) : P a := by
  have := hP.2.1 _ hμ.2.2 _ h
  rwa [← mul_assoc, inv_mul_cancel₀ hμ.1, one_mul] at this

/- English proof (translation)
Introduce `h`. Apply `hP.2.2` to reduce the goal to its premises. Use `hP.1 _ _ h (hP.add (hP.2.1 x hx ε hε) (hP.2.1 y hy η hη))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem IdealLike.not_one_add {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {ε η : K}
    (hε : P ε) (hη : P η) {x y : K} (hx : x ∈ S) (hy : y ∈ S) {v : K} (hv : v = 1 + x * ε + y * η) :
    ¬ P v := by
  intro h
  apply hP.2.2
  have := hP.1 _ _ h (hP.add (hP.2.1 x hx ε hε) (hP.2.1 y hy η hη))
  convert this using 1
  rw [hv]
  ring

/- English proof (translation)
Establish `hμS` using `hμ.2.1`. Establish `hγS : γ ∈ S`. Establish `e : γ = 1 - α * ε - β * η` using `by linear_combination hγ`. Rewrite using `[e]`. Conclude with `S.sub_mem (S.sub_mem S.one_mem (S.mul_mem hα hε)) (S.mul_mem hβ hη)`.

Establish `hcμ : c + μ ∈ S` using `S.add_mem hc hμS`. Establish `m5 : γ + ε + c * η ∈ S` using `S.add_mem (S.add_mem hγS hε) (S.mul_mem hc hη)`. Establish `m6 : γ + ε + (c + μ) * η ∈ S` using `S.add_mem (S.add_mem hγS hε) (S.mul_mem hcμ hη)`. Establish `m7 : γ + c * ε + η ∈ S` using `S.add_mem (S.add_mem hγS (S.mul_mem hc hε)) hη`. Establish `m8 : γ + (c + μ) * ε + η ∈ S` using `S.add_mem (S.add_mem hγS (S.mul_mem hcμ hε)) hη`.

Establish `x1 : 1 - α ∈ S` using `S.sub_mem S.one_mem hα`. Establish `y1 : 1 - β ∈ S` using `S.sub_mem S.one_mem hβ`. Establish `n5 : ∀ {R : K → Prop}, IdealLike S R → R ε → R η → ¬ R (γ + ε + c * η)` using `fun hR h1 h2 => hR.not_one_add h1 h2 x1 (S.sub_mem hc hβ) (by linear_combination hγ)`. Establish `n6 : ¬ P (γ + ε + (c + μ) * η)` using `hP.not_one_add hPε hPη x1 (S.sub_mem hcμ hβ) (by linear_combination hγ)`. Establish `n7 : ¬ P (γ + c * ε + η)` using `hP.not_one_add hPε hPη (S.sub_mem hc hα) y1 (by linear_combination hγ)`.

Establish `n8 : ¬ P (γ + (c + μ) * ε + η)` using `hP.not_one_add hPε hPη (S.sub_mem hcμ hα) y1 (by linear_combination hγ)`. Distinguish the cases in `hQη : Q η`. Distinguish the cases in `hQε : Q ε`. Conclude with `Or.inl (hunit _ m5 (n5 hP hPε hPη) (n5 hQ hQε hQη))`. Distinguish the cases in `h7 : Q (γ + c * ε + η)`.

Distinguish the cases in `h8 : Q (γ + (c + μ) * ε + η)`. It suffices to derive a contradiction. Apply `hQε` to reduce the goal to its premises. Apply `hQ.cancel hμ` to reduce the goal to its premises. Use `hQ.1 _ _ h8 h7 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Or.inr (Or.inr (Or.inr (hunit _ m8 n8 h8)))`. Conclude with `Or.inr (Or.inr (Or.inl (hunit _ m7 n7 h7)))`. Distinguish the cases in `h5 : Q (γ + ε + c * η)`. Distinguish the cases in `h6 : Q (γ + ε + (c + μ) * η)`.

It suffices to derive a contradiction. Apply `hQη` to reduce the goal to its premises. Apply `hQ.cancel hμ` to reduce the goal to its premises. Use `hQ.1 _ _ h6 h5 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Conclude with `Or.inr (Or.inl (hunit _ m6 n6 h6))`. Conclude with `Or.inl (hunit _ m5 (n5 hP hPε hPη) h5)`.
-/
theorem plane_ring_half {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) (hPε : P ε) (hPη : P η) :
    IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
      IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η) := by
  have hμS := hμ.2.1
  have hγS : γ ∈ S := by
    have e : γ = 1 - α * ε - β * η := by linear_combination hγ
    rw [e]
    exact S.sub_mem (S.sub_mem S.one_mem (S.mul_mem hα hε)) (S.mul_mem hβ hη)
  have hcμ : c + μ ∈ S := S.add_mem hc hμS
  have m5 : γ + ε + c * η ∈ S := S.add_mem (S.add_mem hγS hε) (S.mul_mem hc hη)
  have m6 : γ + ε + (c + μ) * η ∈ S := S.add_mem (S.add_mem hγS hε) (S.mul_mem hcμ hη)
  have m7 : γ + c * ε + η ∈ S := S.add_mem (S.add_mem hγS (S.mul_mem hc hε)) hη
  have m8 : γ + (c + μ) * ε + η ∈ S := S.add_mem (S.add_mem hγS (S.mul_mem hcμ hε)) hη
  have x1 : 1 - α ∈ S := S.sub_mem S.one_mem hα
  have y1 : 1 - β ∈ S := S.sub_mem S.one_mem hβ
  have n5 : ∀ {R : K → Prop}, IdealLike S R → R ε → R η → ¬ R (γ + ε + c * η) := fun hR h1 h2 =>
    hR.not_one_add h1 h2 x1 (S.sub_mem hc hβ) (by linear_combination hγ)
  have n6 : ¬ P (γ + ε + (c + μ) * η) :=
    hP.not_one_add hPε hPη x1 (S.sub_mem hcμ hβ) (by linear_combination hγ)
  have n7 : ¬ P (γ + c * ε + η) :=
    hP.not_one_add hPε hPη (S.sub_mem hc hα) y1 (by linear_combination hγ)
  have n8 : ¬ P (γ + (c + μ) * ε + η) :=
    hP.not_one_add hPε hPη (S.sub_mem hcμ hα) y1 (by linear_combination hγ)
  by_cases hQη : Q η
  · by_cases hQε : Q ε
    · exact Or.inl (hunit _ m5 (n5 hP hPε hPη) (n5 hQ hQε hQη))
    · by_cases h7 : Q (γ + c * ε + η)
      · by_cases h8 : Q (γ + (c + μ) * ε + η)
        · exfalso
          apply hQε
          apply hQ.cancel hμ
          convert hQ.1 _ _ h8 h7 using 1
          ring
        · exact Or.inr (Or.inr (Or.inr (hunit _ m8 n8 h8)))
      · exact Or.inr (Or.inr (Or.inl (hunit _ m7 n7 h7)))
  · by_cases h5 : Q (γ + ε + c * η)
    · by_cases h6 : Q (γ + ε + (c + μ) * η)
      · exfalso
        apply hQη
        apply hQ.cancel hμ
        convert hQ.1 _ _ h6 h5 using 1
        ring
      · exact Or.inr (Or.inl (hunit _ m6 n6 h6))
    · exact Or.inl (hunit _ m5 (n5 hP hPε hPη) h5)

/- English proof (translation)
Distinguish the cases in `hUε : IsUnitIn S ε`. Conclude with `Or.inl hUε`. Distinguish the cases in `hUη : IsUnitIn S η`. Conclude with `Or.inr (Or.inl hUη)`. Establish `hε' : P ε ∨ Q ε`.

Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Conclude with `hUε (hunit ε hε hh.1 hh.2)`. Establish `hη' : P η ∨ Q η`. Assume the negation of the conclusion as `hh`.

Use `push Not at hh`. Conclude with `hUη (hunit η hη hh.1 hh.2)`. Distinguish the cases in `hPP : P ε ∧ P η`. Conclude with `Or.inr (Or.inr (Or.inr (plane_ring_half hP hQ hunit hε hη hα hβ hc hμ hγ hPP.1 hPP.2)))`. Distinguish the cases in `hQQ : Q ε ∧ Q η`.

Conclude with `Or.inr (Or.inr (Or.inr (plane_ring_half hQ hP (fun a ha h1 h2 => hunit a ha h2 h1) hε hη hα hβ hc hμ hγ hQQ.1 hQQ.2)))`. Use `Or.inr (Or.inr (Or.inl ?_))` and prove the remaining obligations. Establish `m3 : ε + μ * η ∈ S` using `S.add_mem hε (S.mul_mem hμ.2.1 hη)`. Break down `hε' with hPε | hQε` into its components or cases. Establish `hPη : ¬ P η` using `fun h => hPP ⟨hPε, h⟩`.

Establish `hQη : Q η` using `hη'.resolve_left hPη`. Establish `hQε : ¬ Q ε` using `fun h => hQQ ⟨h, hQη⟩`. Use `hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)` and prove the remaining obligations. Apply `hPη` to reduce the goal to its premises. Apply `hP.cancel hμ` to reduce the goal to its premises.

Use `hP.1 _ _ h3 hPε using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Apply `hQε` to reduce the goal to its premises. Use `hQ.1 _ _ h3 (hQ.2.1 μ hμ.2.1 η hQη) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hQη : ¬ Q η` using `fun h => hQQ ⟨hQε, h⟩`. Establish `hPη : P η` using `hη'.resolve_right hQη`. Establish `hPε : ¬ P ε` using `fun h => hPP ⟨h, hPη⟩`. Use `hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)` and prove the remaining obligations. Apply `hPε` to reduce the goal to its premises.

Use `hP.1 _ _ h3 (hP.2.1 μ hμ.2.1 η hPη) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Apply `hQη` to reduce the goal to its premises. Apply `hQ.cancel hμ` to reduce the goal to its premises. Use `hQ.1 _ _ h3 hQε using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem plane_ring_core {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) :
    IsUnitIn S ε ∨ IsUnitIn S η ∨ IsUnitIn S (ε + μ * η) ∨
      (IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
        IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η)) := by
  by_cases hUε : IsUnitIn S ε
  · exact Or.inl hUε
  by_cases hUη : IsUnitIn S η
  · exact Or.inr (Or.inl hUη)
  have hε' : P ε ∨ Q ε := by
    by_contra hh
    push Not at hh
    exact hUε (hunit ε hε hh.1 hh.2)
  have hη' : P η ∨ Q η := by
    by_contra hh
    push Not at hh
    exact hUη (hunit η hη hh.1 hh.2)
  by_cases hPP : P ε ∧ P η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hP hQ hunit hε hη hα hβ hc hμ hγ hPP.1 hPP.2)))
  by_cases hQQ : Q ε ∧ Q η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hQ hP (fun a ha h1 h2 => hunit a ha h2 h1)
      hε hη hα hβ hc hμ hγ hQQ.1 hQQ.2)))
  refine Or.inr (Or.inr (Or.inl ?_))
  have m3 : ε + μ * η ∈ S := S.add_mem hε (S.mul_mem hμ.2.1 hη)
  rcases hε' with hPε | hQε
  · have hPη : ¬ P η := fun h => hPP ⟨hPε, h⟩
    have hQη : Q η := hη'.resolve_left hPη
    have hQε : ¬ Q ε := fun h => hQQ ⟨h, hQη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPη
      apply hP.cancel hμ
      convert hP.1 _ _ h3 hPε using 1
      ring
    · apply hQε
      convert hQ.1 _ _ h3 (hQ.2.1 μ hμ.2.1 η hQη) using 1
      ring
  · have hQη : ¬ Q η := fun h => hQQ ⟨hQε, h⟩
    have hPη : P η := hη'.resolve_right hQη
    have hPε : ¬ P ε := fun h => hPP ⟨h, hPη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPε
      convert hP.1 _ _ h3 (hP.2.1 μ hμ.2.1 η hPη) using 1
      ring
    · apply hQη
      apply hQ.cancel hμ
      convert hQ.1 _ _ h3 hQε using 1
      ring

/- English proof (translation)
Set `A : AddSubgroup K` to `{ carrier := {a | ∃ m ∈ N, B v m = a} zero_mem' := ⟨0, N.zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩`. Conclude with `⟨m + m', N.add_mem hm hm', by simp⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Conclude with `⟨-m, N.neg_mem hm, by simp⟩ }`. Establish `hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A`. Introduce and unpack `s hs _ ⟨m, hm, rfl⟩`. Conclude with `⟨s • m, hsm s hs m hm, by simp⟩`. Establish `hA0 : ∃ a ∈ A, a ≠ 0` using `⟨B v m0, ⟨m0, hm0, rfl⟩, hne⟩`.

Establish `hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Simplify using `using hint v hv m hm`. Take `⟨β, hβA, hβ0, hdiv⟩` from `hS.principal A hA hA0 hAb`.

Take `⟨m1, hm1, hβ⟩` from `hβA`. Establish `hx : (star β)⁻¹ • v ∈ N`. Apply `hdual` to reduce the goal to its premises. Introduce `m hm`. Establish `h1` using `hdiv (B v m) ⟨m, hm, rfl⟩`.

Establish `e : B m ((star β)⁻¹ • v) = star (B v m * β⁻¹)`. Rewrite using `[map_smul, smul_eq_mul, ← hsym v m, star_mul', star_inv₀]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hS.star_mem _ h1`.

Establish `hc` using `hprim _ hx`. Establish `hβi : β⁻¹ ∈ S`. Use `hS.star_mem _ hc` as an intermediate fact. Rewrite `this` using `[star_inv₀, star_star]`. Then use the resulting hypothesis. Use `⟨β⁻¹ • m1, hsm _ hβi _ hm1, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, hβ, inv_mul_cancel₀ hβ0]`.
-/
theorem plane_partner {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hsym : ∀ x y, star (B x y) = B y x) {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N)
    (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S) (hdual : ∀ x, (∀ m ∈ N, B m x ∈ S) → x ∈ N) {v : V}
    (hv : v ∈ N) (hprim : ∀ c : K, c • v ∈ N → c ∈ S) {m0 : V} (hm0 : m0 ∈ N) (hne : B v m0 ≠ 0) :
    ∃ m ∈ N, B v m = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ N, B v m = a}
      zero_mem' := ⟨0, N.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', N.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, N.neg_mem hm, by simp⟩ }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨s • m, hsm s hs m hm, by simp⟩
  have hA0 : ∃ a ∈ A, a ≠ 0 := ⟨B v m0, ⟨m0, hm0, rfl⟩, hne⟩
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hint v hv m hm
  obtain ⟨β, hβA, hβ0, hdiv⟩ := hS.principal A hA hA0 hAb
  obtain ⟨m1, hm1, hβ⟩ := hβA
  have hx : (star β)⁻¹ • v ∈ N := by
    apply hdual
    intro m hm
    have h1 := hdiv (B v m) ⟨m, hm, rfl⟩
    have e : B m ((star β)⁻¹ • v) = star (B v m * β⁻¹) := by
      rw [map_smul, smul_eq_mul, ← hsym v m, star_mul', star_inv₀]
      ring
    rw [e]
    exact hS.star_mem _ h1
  have hc := hprim _ hx
  have hβi : β⁻¹ ∈ S := by
    have := hS.star_mem _ hc
    rwa [star_inv₀, star_star] at this
  refine ⟨β⁻¹ • m1, hsm _ hβi _ hm1, ?_⟩
  rw [map_smul, smul_eq_mul, hβ, inv_mul_cancel₀ hβ0]

/- English proof (translation)
Set `A : AddSubgroup K` to `{ carrier := {c | c • w ∈ N} zero_mem' := by simp [N.zero_mem] add_mem' := by`. Introduce `a b ha hb`. Use `show (a + b) • w ∈ N`. Rewrite using `[add_smul]`. Conclude with `N.add_mem ha hb`.

Use the proof step `neg_mem' := by`. Introduce `a ha`. Use `show (-a) • w ∈ N`. Rewrite using `[neg_smul]`. Conclude with `N.neg_mem ha }`.

Establish `hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A`. Introduce `s hs a ha`. Use `show (s * a) • w ∈ N`. Rewrite using `[mul_smul]`. Conclude with `hsm s hs _ ha`.

Take `⟨t, ht0, htw⟩` from `hspan`. Establish `hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Use `hint z hz _ ha` as an intermediate fact.

Simplify `this` using `[map_smul, hzw]`. Take `⟨α, hαA, hα0, hdiv⟩` from `hS.principal A hA ⟨t, htw, ht0⟩ hAb`. Use `⟨α, hα0, hαA, fun c hc => ?_⟩` and prove the remaining obligations. Establish `h1 : c * α ∈ A` using `by show (c * α) • w ∈ N`. Rewrite using `[mul_smul]` and apply the resulting hypothesis.

Use `hdiv _ h1` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ hα0, mul_one]`. Then use the resulting hypothesis.
-/
theorem plane_prim {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S)
    {z w : V} (hz : z ∈ N) (hzw : B z w = 1) (hspan : ∃ t : K, t ≠ 0 ∧ t • w ∈ N) :
    ∃ α : K, α ≠ 0 ∧ α • w ∈ N ∧ ∀ c : K, c • (α • w) ∈ N → c ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {c | c • w ∈ N}
      zero_mem' := by simp [N.zero_mem]
      add_mem' := by
        intro a b ha hb
        show (a + b) • w ∈ N
        rw [add_smul]
        exact N.add_mem ha hb
      neg_mem' := by
        intro a ha
        show (-a) • w ∈ N
        rw [neg_smul]
        exact N.neg_mem ha }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    intro s hs a ha
    show (s * a) • w ∈ N
    rw [mul_smul]
    exact hsm s hs _ ha
  obtain ⟨t, ht0, htw⟩ := hspan
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    intro a ha
    have := hint z hz _ ha
    simpa [map_smul, hzw] using this
  obtain ⟨α, hαA, hα0, hdiv⟩ := hS.principal A hA ⟨t, htw, ht0⟩ hAb
  refine ⟨α, hα0, hαA, fun c hc => ?_⟩
  have h1 : c * α ∈ A := by
    show (c * α) • w ∈ N
    rwa [mul_smul]
  have := hdiv _ h1
  rwa [mul_assoc, mul_inv_cancel₀ hα0, mul_one] at this

def planeForm (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) : V →ₗ⋆[K] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y - b * h x z * h z y)
    (by intros; simp only [map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem planeForm_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) (x y : V) :
    planeForm h z b x y = h x y - b * h x z * h z y := rfl

end Generic

section Ring

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def InI (p I : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ I ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ _ ⟨r₁, s₁, hs₁, hr₁, rfl⟩ ⟨r₂, s₂, hs₂, hr₂, rfl⟩`. Establish `h1` using `algebraMap_ne_zero_of_mem_hcompl hp hs₁`. Establish `h2` using `algebraMap_ne_zero_of_mem_hcompl hp hs₂`. Use `⟨r₁ * s₂ - s₁ * r₂, s₁ * s₂, mul_mem hs₁ hs₂, I.sub_mem (I.mul_mem_right _ hr₁) (I.mul_mem_left _ hr₂), ?_⟩` and prove the remaining obligations.

Rewrite using `[div_sub_div _ _ h1 h2, map_sub, map_mul, map_mul, map_mul]`. Introduce `x hx a ha`. Take `⟨r, s, hs, hr, rfl⟩` from `ha`. Take `⟨k, t, ht, rfl⟩` from `(mem_locR_iff hp x).1 ((mem_locRing p x).1 hx)`. Use `⟨k * r, t * s, mul_mem ht hs, I.mul_mem_left k hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[div_mul_div_comm, map_mul, map_mul]`. Introduce and unpack `⟨r, s, hs, hr, h1⟩`. Establish `h0` using `algebraMap_ne_zero_of_mem_hcompl hp hs`. Rewrite `h1` using `[eq_div_iff h0, one_mul]`. Establish `hsr : s = r` using `RingOfIntegers.ext h1`.

Conclude with `hI s hs (hsr ▸ hr)`.
-/
theorem plane_idealLike {p : Ideal (𝓞 K)} (hp : p.IsPrime) (I : Ideal (𝓞 K))
    (hI : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ∉ I) : IdealLike (locRing p) (InI p I) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ ⟨r₁, s₁, hs₁, hr₁, rfl⟩ ⟨r₂, s₂, hs₂, hr₂, rfl⟩
    have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
    have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
    refine ⟨r₁ * s₂ - s₁ * r₂, s₁ * s₂, mul_mem hs₁ hs₂,
      I.sub_mem (I.mul_mem_right _ hr₁) (I.mul_mem_left _ hr₂), ?_⟩
    rw [div_sub_div _ _ h1 h2, map_sub, map_mul, map_mul, map_mul]
  · intro x hx a ha
    obtain ⟨r, s, hs, hr, rfl⟩ := ha
    obtain ⟨k, t, ht, rfl⟩ := (mem_locR_iff hp x).1 ((mem_locRing p x).1 hx)
    refine ⟨k * r, t * s, mul_mem ht hs, I.mul_mem_left k hr, ?_⟩
    rw [div_mul_div_comm, map_mul, map_mul]
  · rintro ⟨r, s, hs, hr, h1⟩
    have h0 := algebraMap_ne_zero_of_mem_hcompl hp hs
    rw [eq_div_iff h0, one_mul] at h1
    have hsr : s = r := RingOfIntegers.ext h1
    exact hI s hs (hsr ▸ hr)

/- English proof (translation)
Take `⟨r, s, hs, rfl⟩` from `(mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)`. Rewrite using `[isUnitIn_div_iff hp r hs, mem_hcompl_iff hp]`. Conclude with `⟨fun hr => h1 ⟨r, s, hs, hr, rfl⟩, fun hr => h2 ⟨r, s, hs, hr, rfl⟩⟩`.
-/
theorem plane_unit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (h1 : ¬ InI p p a) (h2 : ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) : IsUnitIn (locRing p) a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  rw [isUnitIn_div_iff hp r hs, mem_hcompl_iff hp]
  exact ⟨fun hr => h1 ⟨r, s, hs, hr, rfl⟩, fun hr => h2 ⟨r, s, hs, hr, rfl⟩⟩

/- English proof (translation)
Take `⟨r, s, hs, hr, rfl⟩` from `h`. Use `⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_conjIdeal_iff, conjO_conjO]`. Conclude with `hr`. Rewrite using `[algebraMap_conjO, algebraMap_conjO, star_div₀]`.
-/
theorem plane_star₁ {p : Ideal (𝓞 K)} {a : K} (h : InI p p a) :
    InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (star a) := by
  obtain ⟨r, s, hs, hr, rfl⟩ := h
  refine ⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩
  · rw [mem_conjIdeal_iff, conjO_conjO]
    exact hr
  · rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

/- English proof (translation)
Take `⟨r, s, hs, hr, rfl⟩` from `h`. Use `⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(mem_conjIdeal_iff p r).1 hr`. Rewrite using `[algebraMap_conjO, algebraMap_conjO, star_div₀]`.
-/
theorem plane_star₂ {p : Ideal (𝓞 K)} {a : K} (h : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) :
    InI p p (star a) := by
  obtain ⟨r, s, hs, hr, rfl⟩ := h
  refine ⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩
  · exact (mem_conjIdeal_iff p r).1 hr
  · rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

end Ring

/- English proof (translation)
Introduce `K _ _ _ V _ _ _ h hK hs _ p hp N z b hN hz hprim hnu hb hbb hw`. Take `⟨w, hzw, hww⟩` from `hw`. Establish `hS` using `isHermSemilocal_locRing hK hp`. Establish `hpP` using `hp.isPrime`. Establish `hsym : ∀ x y, star (h x y) = h y x` using `fun x y => hs.eq x y`.

Establish `hPl : IdealLike (locRing p) (InI p p)` using `plane_idealLike hpP p (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').1)`. Establish `hQl : IdealLike (locRing p) (InI p (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) p)) := plane_idealLike hpP _ (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').2)`. Establish `hunit : ∀ a ∈ locRing p, ¬ InI p p a → ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) p) a → IsUnitIn (locRing p) a := fun a ha h1 h2 => plane_unit hpP ha h1 h2`. Establish `hζS : h z z ∈ locRing p` using `hN.int z hz z hz`. Establish `hζr : star (h z z) = h z z` using `hsym z z`.

Establish `hJ : InI p p (h z z) ∧ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) p) (h z z) := by`. Distinguish the cases in `h1 : InI p p (h z z)`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `plane_star₁ h1` as an intermediate fact. Rewrite `this` using `[hζr]`. Then use the resulting hypothesis.

Establish `h2 : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) p) (h z z) := by`. Assume the negation of the conclusion as `h2`. Conclude with `hnu (hunit _ hζS h1 h2)`. Use `⟨?_, h2⟩` and prove the remaining obligations. Use `plane_star₂ h2` as an intermediate fact.

Rewrite `this` using `[hζr]`. Then use the resulting hypothesis. Establish `hu : IsUnitIn (locRing p) (1 - b * h z z)`. Establish `hm : 1 - b * h z z ∈ locRing p` using `(locRing p).sub_mem (locRing p).one_mem ((locRing p).mul_mem hb hζS)`. Use `hunit _ hm (fun h1 => hPl.2.2 ?_) (fun h1 => hQl.2.2 ?_)` and prove the remaining obligations. Use `hPl.add h1 (hPl.2.1 b hb _ hJ.1) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `hQl.add h1 (hQl.2.1 b hb _ hJ.2) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨q, hq⟩ : ∃ q : V →ₗ⋆[K] V →ₗ[K] K, ∀ x y, q x y = h x y - b * h x z * h z y` from `⟨planeForm h z b, planeForm_apply h z b⟩`. Establish `hqsym : ∀ x y, star (q x y) = q y x`.

Introduce `x y`. Rewrite using `[hq, hq, star_sub, star_mul', star_mul', hbb, hsym, hsym, hsym]`. Expand and normalize the polynomial expressions, which then agree. Establish `hqint : ∀ x ∈ N, ∀ y ∈ N, q x y ∈ locRing p`. Introduce `x hx y hy`.

Rewrite using `[hq]`. Conclude with `(locRing p).sub_mem (hN.int x hx y hy) ((locRing p).mul_mem ((locRing p).mul_mem hb (hN.int x hx z hz)) (hN.int z hz y hy))`. Establish `hqz : ∀ x, q z x = (1 - b * h z z) * h z x`. Introduce `x`. Rewrite using `[hq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hqdual : ∀ x, (∀ m ∈ N, q m x ∈ locRing p) → x ∈ N`. Introduce `x hx`. Establish `hzx : h z x ∈ locRing p`. Use `(locRing p).mul_mem hu.2.2 (hx z hz)` as an intermediate fact.

Rewrite `this` using `[hqz, ← mul_assoc, inv_mul_cancel₀ hu.1, one_mul]`. Then use the resulting hypothesis. Establish `hx' : x - (b * h z x) • z ∈ N`. Apply `hN.dual` to reduce the goal to its premises. Introduce `m hm`. Use `hx m hm using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hq, map_sub, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `N.add_mem hx' (hN.smul_mem _ ((locRing p).mul_mem hb hzx) z hz)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hwz : h w z = 1` using `by rw [← hsym, hzw, star_one]`.

Establish `hqw : q w w = 0` using `by rw [hq, hwz, hzw, hww]; ring`. Take `⟨α, hα0, heN, heprim⟩` from `plane_prim hS h hN.smul_mem hN.int hz hzw (hN.span w)`. Establish `hze : h z (α • w) = α` using `by rw [map_smul, smul_eq_mul, hzw, mul_one]`. Establish `hqee : q (α • w) (α • w) = 0`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hqw, mul_zero]`.

Establish `hqez : q (α • w) z ≠ 0`. Rewrite using `[← hqsym, hqz, hze, star_mul']`. Conclude with `mul_ne_zero (star_ne_zero.mpr hu.1) (star_ne_zero.mpr hα0)`. Generalize the expression as in `α • w = e at heN heprim hze hqee hqez`. Take `⟨f₀, hf₀N, hef₀⟩` from `plane_partner hS q hqsym hN.smul_mem hqint hqdual heN heprim hz hqez`.

Establish `hf₀e : q f₀ e = 1` using `by rw [← hqsym, hef₀, star_one]`. Take `⟨c₁, hc₁S, hc₁⟩` from `exists_trace_eq hS (s := -q f₀ f₀) ((locRing p).neg_mem (hqint f₀ hf₀N f₀ hf₀N)) (by rw [star_neg, hqsym])`. Establish `hfN : f₀ + c₁ • e ∈ N` using `N.add_mem hf₀N (hN.smul_mem c₁ hc₁S e heN)`. Establish `hqef : q e (f₀ + c₁ • e) = 1`. Rewrite using `[map_add, map_smul, smul_eq_mul, hqee, mul_zero, add_zero, hef₀]`.

Establish `hqff : q (f₀ + c₁ • e) (f₀ + c₁ • e) = 0`. Simplify using `only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hqee, hef₀, hf₀e]`. Take the linear combination `hc₁`. Generalize the expression as in `f₀ + c₁ • e = f at hfN hqef hqff`. Establish `hqfe : q f e = 1` using `by rw [← hqsym, hqef, star_one]`.

Take `⟨t, htN, hzt⟩` from `plane_partner hS h hsym hN.smul_mem hN.int hN.dual hz hprim heN (by rw [hze]; exact hα0)`. Establish `hgN : t - q f t • e - q e t • f ∈ N` using `N.sub_mem (N.sub_mem htN (hN.smul_mem _ (hqint f hfN t htN) e heN)) (hN.smul_mem _ (hqint e heN t htN) f hfN)`. Establish `hqeg : q e (t - q f t • e - q e t • f) = 0`. Simplify using `only [map_sub, map_smul, smul_eq_mul, hqee, hqef]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hqfg : q f (t - q f t • e - q e t • f) = 0`. Simplify using `only [map_sub, map_smul, smul_eq_mul, hqff, hqfe]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzg : q f t * h z e + q e t * h z f + h z (t - q f t • e - q e t • f) = 1`. Simplify using `only [map_sub, map_smul, smul_eq_mul, hzt]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hαS` using `hqint f hfN t htN`. Establish `hβS` using `hqint e heN t htN`. Generalize the expression as in `q f t = α' at hgN hqeg hqfg hzg hαS`. Generalize the expression as in `q e t = β' at hgN hqeg hqfg hzg hβS`.

Generalize the expression as in `t - α' • e - β' • f = g at hgN hqeg hqfg hzg`. Establish `hqge : q g e = 0` using `by rw [← hqsym, hqeg, star_zero]`. Establish `hqgf : q g f = 0` using `by rw [← hqsym, hqfg, star_zero]`. Take `⟨c, hcS, hc⟩` from `exists_trace_eq hS (s := -q g g) ((locRing p).neg_mem (hqint g hgN g hgN)) (by rw [star_neg, hqsym])`. Take `⟨θ, -, hμ⟩` from `hS.unram`.

Establish `hμs : star (θ - star θ) = -(θ - star θ)` using `by rw [star_sub, star_star]; ring`. Generalize the expression as in `θ - star θ = μ at hμ hμs`. Establish `key : ∀ s a d : K, s ∈ locRing p → a ∈ locRing p → d ∈ locRing p → star s * s * q g g + star a * d + star d * a = 0 → IsUnitIn (locRing p) (s * h z g + a * h z e + d * h z f) → ∃ y ∈ N, h z y = 1 ∧ h y y = b`. Introduce `s a d hs' ha hd hn hU`. Establish `hXN : s • g + a • e + d • f ∈ N` using `N.add_mem (N.add_mem (hN.smul_mem s hs' g hgN) (hN.smul_mem a ha e heN)) (hN.smul_mem d hd f hfN)`.

Establish `hzX : h z (s • g + a • e + d • f) = s * h z g + a * h z e + d * h z f`. Simplify using `only [map_add, map_smul, smul_eq_mul]`. Establish `hqX : q (s • g + a • e + d • f) (s • g + a • e + d • f) = 0`. Rewrite using `[← hn]`. Simplify using `only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hqee, hqff, hqef, hqfe, hqeg, hqge, hqfg, hqgf]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f), hN.smul_mem _ hU.2.2 _ hXN, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]`. Establish `h1 : h z ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 1`. Rewrite using `[map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]`.

Establish `h2 : h ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) z = 1`. Rewrite using `[← hsym, h1, star_one]`. Establish `h3` using `hq ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))`. Rewrite `h3` using `[h1, h2]`. Establish `h4 : q ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 0`.

Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hqX, mul_zero]`. Rewrite `h3` using `[h4]`. Take the linear combination `-h3`. Establish `hS0 : (0 : K) ∈ locRing p` using `(locRing p).zero_mem`. Establish `hS1 : (1 : K) ∈ locRing p` using `(locRing p).one_mem`.

Establish `hμS : μ ∈ locRing p` using `hμ.2.1`. Establish `hcμ : c + μ ∈ locRing p` using `(locRing p).add_mem hcS hμS`. Break down `plane_ring_core hPl hQl hunit (hN.int z hz e heN) (hN.int z hz f hfN) hαS hβS hcS hμ hzg with h1 | h1 | h1 | h1 | h1 | h1 | h1` into its components or cases. Conclude with `key 0 1 0 hS0 hS1 hS0 (by simp) (by convert h1 using 1; ring)`. Conclude with `key 0 0 1 hS0 hS0 hS1 (by simp) (by convert h1 using 1; ring)`.

Conclude with `key 0 1 μ hS0 hS1 hμS (by rw [hμs]; simp) (by convert h1 using 1; ring)`. Conclude with `key 1 1 c hS1 hS1 hcS (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)`. Conclude with `key 1 1 (c + μ) hS1 hS1 hcμ (by rw [star_one, star_add, hμs]; linear_combination hc) (by convert h1 using 1; ring)`. Conclude with `key 1 c 1 hS1 hcS hS1 (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)`. Conclude with `key 1 (c + μ) 1 hS1 hcμ hS1 (by rw [star_one, star_add, hμs]; linear_combination hc) (by convert h1 using 1; ring)`.
-/
theorem primitive_plane_local : Z0.PrimPlaneLoc := by
  intro K _ _ _ V _ _ _ h hK hs _ p hp N z b hN hz hprim hnu hb hbb hw
  obtain ⟨w, hzw, hww⟩ := hw
  have hS := isHermSemilocal_locRing hK hp
  have hpP := hp.isPrime
  have hsym : ∀ x y, star (h x y) = h y x := fun x y => hs.eq x y
  have hPl : IdealLike (locRing p) (InI p p) :=
    plane_idealLike hpP p (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').1)
  have hQl : IdealLike (locRing p) (InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p)) :=
    plane_idealLike hpP _ (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').2)
  have hunit : ∀ a ∈ locRing p, ¬ InI p p a → ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a →
      IsUnitIn (locRing p) a := fun a ha h1 h2 => plane_unit hpP ha h1 h2

  have hζS : h z z ∈ locRing p := hN.int z hz z hz
  have hζr : star (h z z) = h z z := hsym z z
  have hJ : InI p p (h z z) ∧ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
    by_cases h1 : InI p p (h z z)
    · refine ⟨h1, ?_⟩
      have := plane_star₁ h1
      rwa [hζr] at this
    · have h2 : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
        by_contra h2
        exact hnu (hunit _ hζS h1 h2)
      refine ⟨?_, h2⟩
      have := plane_star₂ h2
      rwa [hζr] at this
  have hu : IsUnitIn (locRing p) (1 - b * h z z) := by
    have hm : 1 - b * h z z ∈ locRing p := (locRing p).sub_mem (locRing p).one_mem ((locRing p).mul_mem hb hζS)
    refine hunit _ hm (fun h1 => hPl.2.2 ?_) (fun h1 => hQl.2.2 ?_)
    · convert hPl.add h1 (hPl.2.1 b hb _ hJ.1) using 1
      ring
    · convert hQl.add h1 (hQl.2.1 b hb _ hJ.2) using 1
      ring

  obtain ⟨q, hq⟩ : ∃ q : V →ₗ⋆[K] V →ₗ[K] K, ∀ x y, q x y = h x y - b * h x z * h z y :=
    ⟨planeForm h z b, planeForm_apply h z b⟩
  have hqsym : ∀ x y, star (q x y) = q y x := by
    intro x y
    rw [hq, hq, star_sub, star_mul', star_mul', hbb, hsym, hsym, hsym]
    ring
  have hqint : ∀ x ∈ N, ∀ y ∈ N, q x y ∈ locRing p := by
    intro x hx y hy
    rw [hq]
    exact (locRing p).sub_mem (hN.int x hx y hy)
      ((locRing p).mul_mem ((locRing p).mul_mem hb (hN.int x hx z hz)) (hN.int z hz y hy))
  have hqz : ∀ x, q z x = (1 - b * h z z) * h z x := by
    intro x
    rw [hq]
    ring
  have hqdual : ∀ x, (∀ m ∈ N, q m x ∈ locRing p) → x ∈ N := by
    intro x hx
    have hzx : h z x ∈ locRing p := by
      have := (locRing p).mul_mem hu.2.2 (hx z hz)
      rwa [hqz, ← mul_assoc, inv_mul_cancel₀ hu.1, one_mul] at this
    have hx' : x - (b * h z x) • z ∈ N := by
      apply hN.dual
      intro m hm
      convert hx m hm using 1
      rw [hq, map_sub, map_smul, smul_eq_mul]
      ring
    have := N.add_mem hx' (hN.smul_mem _ ((locRing p).mul_mem hb hzx) z hz)
    rwa [sub_add_cancel] at this

  have hwz : h w z = 1 := by rw [← hsym, hzw, star_one]
  have hqw : q w w = 0 := by rw [hq, hwz, hzw, hww]; ring
  obtain ⟨α, hα0, heN, heprim⟩ := plane_prim hS h hN.smul_mem hN.int hz hzw (hN.span w)
  have hze : h z (α • w) = α := by rw [map_smul, smul_eq_mul, hzw, mul_one]
  have hqee : q (α • w) (α • w) = 0 := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hqw, mul_zero]
  have hqez : q (α • w) z ≠ 0 := by
    rw [← hqsym, hqz, hze, star_mul']
    exact mul_ne_zero (star_ne_zero.mpr hu.1) (star_ne_zero.mpr hα0)
  generalize α • w = e at heN heprim hze hqee hqez

  obtain ⟨f₀, hf₀N, hef₀⟩ := plane_partner hS q hqsym hN.smul_mem hqint hqdual heN heprim hz hqez
  have hf₀e : q f₀ e = 1 := by rw [← hqsym, hef₀, star_one]
  obtain ⟨c₁, hc₁S, hc₁⟩ := exists_trace_eq hS (s := -q f₀ f₀)
    ((locRing p).neg_mem (hqint f₀ hf₀N f₀ hf₀N)) (by rw [star_neg, hqsym])
  have hfN : f₀ + c₁ • e ∈ N := N.add_mem hf₀N (hN.smul_mem c₁ hc₁S e heN)
  have hqef : q e (f₀ + c₁ • e) = 1 := by
    rw [map_add, map_smul, smul_eq_mul, hqee, mul_zero, add_zero, hef₀]
  have hqff : q (f₀ + c₁ • e) (f₀ + c₁ • e) = 0 := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hqee, hef₀, hf₀e]
    linear_combination hc₁
  generalize f₀ + c₁ • e = f at hfN hqef hqff
  have hqfe : q f e = 1 := by rw [← hqsym, hqef, star_one]

  obtain ⟨t, htN, hzt⟩ := plane_partner hS h hsym hN.smul_mem hN.int hN.dual hz hprim heN
    (by rw [hze]; exact hα0)

  have hgN : t - q f t • e - q e t • f ∈ N :=
    N.sub_mem (N.sub_mem htN (hN.smul_mem _ (hqint f hfN t htN) e heN))
      (hN.smul_mem _ (hqint e heN t htN) f hfN)
  have hqeg : q e (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqee, hqef]
    ring
  have hqfg : q f (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqff, hqfe]
    ring
  have hzg : q f t * h z e + q e t * h z f + h z (t - q f t • e - q e t • f) = 1 := by
    simp only [map_sub, map_smul, smul_eq_mul, hzt]
    ring
  have hαS := hqint f hfN t htN
  have hβS := hqint e heN t htN
  generalize q f t = α' at hgN hqeg hqfg hzg hαS
  generalize q e t = β' at hgN hqeg hqfg hzg hβS
  generalize t - α' • e - β' • f = g at hgN hqeg hqfg hzg
  have hqge : q g e = 0 := by rw [← hqsym, hqeg, star_zero]
  have hqgf : q g f = 0 := by rw [← hqsym, hqfg, star_zero]
  obtain ⟨c, hcS, hc⟩ := exists_trace_eq hS (s := -q g g)
    ((locRing p).neg_mem (hqint g hgN g hgN)) (by rw [star_neg, hqsym])
  obtain ⟨θ, -, hμ⟩ := hS.unram
  have hμs : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  generalize θ - star θ = μ at hμ hμs

  have key : ∀ s a d : K, s ∈ locRing p → a ∈ locRing p → d ∈ locRing p →
      star s * s * q g g + star a * d + star d * a = 0 →
      IsUnitIn (locRing p) (s * h z g + a * h z e + d * h z f) → ∃ y ∈ N, h z y = 1 ∧ h y y = b := by
    intro s a d hs' ha hd hn hU
    have hXN : s • g + a • e + d • f ∈ N :=
      N.add_mem (N.add_mem (hN.smul_mem s hs' g hgN) (hN.smul_mem a ha e heN)) (hN.smul_mem d hd f hfN)
    have hzX : h z (s • g + a • e + d • f) = s * h z g + a * h z e + d * h z f := by
      simp only [map_add, map_smul, smul_eq_mul]
    have hqX : q (s • g + a • e + d • f) (s • g + a • e + d • f) = 0 := by
      rw [← hn]
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, RingHom.id_apply, hqee, hqff, hqef, hqfe, hqeg, hqge, hqfg, hqgf]
      ring
    refine ⟨(s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f),
      hN.smul_mem _ hU.2.2 _ hXN, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
    · have h1 : h z ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 1 := by
        rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
      have h2 : h ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) z = 1 := by
        rw [← hsym, h1, star_one]
      have h3 := hq ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
        ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
      rw [h1, h2] at h3
      have h4 : q ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
          ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 0 := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hqX, mul_zero]
      rw [h4] at h3
      linear_combination -h3
  have hS0 : (0 : K) ∈ locRing p := (locRing p).zero_mem
  have hS1 : (1 : K) ∈ locRing p := (locRing p).one_mem
  have hμS : μ ∈ locRing p := hμ.2.1
  have hcμ : c + μ ∈ locRing p := (locRing p).add_mem hcS hμS
  rcases plane_ring_core hPl hQl hunit (hN.int z hz e heN) (hN.int z hz f hfN) hαS hβS hcS hμ hzg with
    h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact key 0 1 0 hS0 hS1 hS0 (by simp) (by convert h1 using 1; ring)
  · exact key 0 0 1 hS0 hS0 hS1 (by simp) (by convert h1 using 1; ring)
  · exact key 0 1 μ hS0 hS1 hμS (by rw [hμs]; simp) (by convert h1 using 1; ring)
  · exact key 1 1 c hS1 hS1 hcS (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 1 (c + μ) hS1 hS1 hcμ (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)
  · exact key 1 c 1 hS1 hcS hS1 (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 (c + μ) 1 hS1 hcμ hS1 (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)

end Formalism.L2.SG.Pf.LatDictZ.Z2
