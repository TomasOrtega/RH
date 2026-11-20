import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.H90
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

/- English proof (translation)
Use `(L.two.map (algebraMap O K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.
-/
theorem IsLoc.two_ne (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have := (L.two.map (algebraMap O K)).ne_zero
  rwa [map_ofNat] at this

/- English proof (translation)
Introduce `t ht x` and use `by rw [Units.val_mul, mul_smul] exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht`.
-/
theorem lcount_inv (L : IsLoc O Δ) {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

/- English proof (translation)
Establish `h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1`. Apply the tactic sequence `ext <;> simp`. Establish `hω : IsUnit (ofE Δ (ω : Etau K τ))`. Use `isUnit_iff_exists_inv.2 ⟨ofE Δ (algebraMap K (Etau K τ) τ - ω), ?_⟩` and prove the remaining obligations. Rewrite using `[← ofE_mul, h1]`.

Apply the tactic sequence `ext <;> simp [ofE]`. Establish `hd : IsUnit d` using `isUnit_of_mul_isUnit_left (h.d_norm ▸ hω)`. Take `⟨u, hu⟩` from `hd`. Establish `hβ : ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀) = 1`. Establish `hn` using `h.d_norm`.

Rewrite `hn` using `[← hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sigL_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * ((u : EL Δ τ) * sigL (u : EL Δ τ)) := by`.

Rewrite using `[h₀, hn]`. Use `_ = (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) := by`. Rewrite using `[sigL_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by simp [sigL_one]`.

Take `⟨y, hy⟩` from `h90 O K Δ τ L h.reg _ hβ`. Establish `key : d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = d₀`. Rewrite using `[hy, ← hu]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.

Use `_ = d₀ := by simp`. Use `⟨m * y * star (sigL (y : EL Δ τ)), ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `hD` using `(datIso O K Δ τ c d m y).2 h`. Rewrite `hD` using `[key]`. Then use the resulting hypothesis. Establish `e` using `(datIso O K Δ τ c d (t • m) y).1`.

Rewrite `e` using `[key, smul_mul_assoc, smul_mul_assoc]`. Conclude with `e`.
-/
theorem dat_move (L : IsLoc O Δ) {c : K} {d m : EL Δ τ} (h : IsDat c d m) {d₀ : EL Δ τ} (h₀ : d₀ * sigL d₀ = ofE Δ (ω : Etau K τ)) :
    ∃ m', IsDat c d₀ m' ∧ ∀ t : K, lcount O c d (t • m) = lcount O c d₀ (t • m') := by
  have h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1 := by
    ext <;> simp
  have hω : IsUnit (ofE Δ (ω : Etau K τ)) := by
    refine isUnit_iff_exists_inv.2 ⟨ofE Δ (algebraMap K (Etau K τ) τ - ω), ?_⟩
    rw [← ofE_mul, h1]
    ext <;> simp [ofE]
  have hd : IsUnit d := isUnit_of_mul_isUnit_left (h.d_norm ▸ hω)
  obtain ⟨u, hu⟩ := hd
  have hβ : ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀) = 1 := by
    have hn := h.d_norm
    rw [← hu] at hn
    calc ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀)
        = ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (d₀ * sigL d₀) := by
          rw [sigL_mul]; ring
      _ = ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * ((u : EL Δ τ) * sigL (u : EL Δ τ)) := by
          rw [h₀, hn]
      _ = (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) * sigL (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * (u : EL Δ τ)) := by
          rw [sigL_mul]; ring
      _ = 1 := by simp [sigL_one]
  obtain ⟨y, hy⟩ := h90 O K Δ τ L h.reg _ hβ
  have key : d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = d₀ := by
    rw [hy, ← hu]
    calc (u : EL Δ τ) * (((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * d₀ * (y : EL Δ τ)) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)
        = ((u : EL Δ τ) * ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) * d₀ * ((y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) := by
          ring
      _ = d₀ := by simp
  refine ⟨m * y * star (sigL (y : EL Δ τ)), ?_, fun t => ?_⟩
  · have hD := (datIso O K Δ τ c d m y).2 h
    rwa [key] at hD
  · have e := (datIso O K Δ τ c d (t • m) y).1
    rw [key, smul_mul_assoc, smul_mul_assoc] at e
    exact e

/- English proof (translation)
Establish `h4 : IsUnit (4 : O)`. Establish `h` using `L.two.mul L.two`. Evaluate the numerical expressions using `at h`. Conclude with `h`. Establish `unit_of : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → IsUnit (4 + x)`.

Introduce `x hx`. Assume the negation of the conclusion as `hn`. Establish `h1 : 4 + x ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hn`. Establish `h2 : (4 : O) ∈ IsLocalRing.maximalIdeal O`. Simplify using `using (IsLocalRing.maximalIdeal O).sub_mem h1 hx`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h2 h4`. Establish `unit_nm : ∀ x : O, x ∉ IsLocalRing.maximalIdeal O → IsUnit x`. Introduce `x hx`. Assume the negation of the conclusion as `hn`. Conclude with `hx ((IsLocalRing.mem_maximalIdeal _).2 hn)`.

Distinguish the cases in `ha : τ₀ - 2 ∈ IsLocalRing.maximalIdeal O`. Use `left`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Establish `h` using `unit_of _ ha`. Use `h using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hb : τ₀ + 2 ∈ IsLocalRing.maximalIdeal O`. Use `right`. Use `left`. Use `⟨hb, ?_⟩` and prove the remaining obligations.

Establish `h` using `unit_of _ ((IsLocalRing.maximalIdeal O).neg_mem hb)`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `right`. Use `right`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `unit_nm _ hb`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `(unit_nm _ ha).neg`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tri (L : IsLoc O Δ) (τ₀ : O) : τ₀ - 2 ∈ IsLocalRing.maximalIdeal O ∧ IsUnit (2 + τ₀) ∨ τ₀ + 2 ∈ IsLocalRing.maximalIdeal O ∧ IsUnit (2 - τ₀) ∨
    IsUnit (2 + τ₀) ∧ IsUnit (2 - τ₀) := by
  have h4 : IsUnit (4 : O) := by
    have h := L.two.mul L.two
    norm_num at h
    exact h
  have unit_of : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → IsUnit (4 + x) := by
    intro x hx
    by_contra hn
    have h1 : 4 + x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 : (4 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using (IsLocalRing.maximalIdeal O).sub_mem h1 hx
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 h4
  have unit_nm : ∀ x : O, x ∉ IsLocalRing.maximalIdeal O → IsUnit x := by
    intro x hx
    by_contra hn
    exact hx ((IsLocalRing.mem_maximalIdeal _).2 hn)
  by_cases ha : τ₀ - 2 ∈ IsLocalRing.maximalIdeal O
  · left
    refine ⟨ha, ?_⟩
    have h := unit_of _ ha
    convert h using 1
    ring
  · by_cases hb : τ₀ + 2 ∈ IsLocalRing.maximalIdeal O
    · right; left
      refine ⟨hb, ?_⟩
      have h := unit_of _ ((IsLocalRing.maximalIdeal O).neg_mem hb)
      convert h using 1
      ring
    · right; right
      refine ⟨?_, ?_⟩
      · have h := unit_nm _ hb
        convert h using 1
        ring
      · have h := (unit_nm _ ha).neg
        convert h using 1
        ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Take `⟨v, rfl⟩` from `hu`. Take `⟨w, s, hs, he⟩` from `h`. Use `⟨w * v⁻¹, s, hs, ?_⟩` and prove the remaining obligations. Establish `hv : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, hv, mul_one]`. Use `_ = _ := by`. Rewrite using `[he, Units.val_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EvenVal.of_mul_unit {c : K} {u : O} (hu : IsUnit u) (h : EvenVal O (c * algebraMap O K u)) : EvenVal O c := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨w, s, hs, he⟩ := h
  refine ⟨w * v⁻¹, s, hs, ?_⟩
  have hv : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc c = c * algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) := by
        rw [mul_assoc, hv, mul_one]
    _ = _ := by
        rw [he, Units.val_mul, map_mul]
        ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Establish `h2 : 2 + τ ≠ 0`. Introduce `h`. Apply `hτ` to reduce the goal to its premises. Establish `e : τ = -2` using `by linear_combination h`. Rewrite using `[e]`.

Evaluate the numerical expressions. Use `⟨⟨1 + ω, ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp <;> field_simp <;> ring`. Apply the tactic sequence `ext <;> simp <;> field_simp <;> ring`.
-/
theorem exists_unit_one_add_generator (hτ : τ ^ 2 - 4 ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω := by
  have h2 : 2 + τ ≠ 0 := by
    intro h
    apply hτ
    have e : τ = -2 := by linear_combination h
    rw [e]
    norm_num
  refine ⟨⟨1 + ω, ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩, ?_, ?_⟩, rfl⟩
  · ext <;> simp <;> field_simp <;> ring
  · ext <;> simp <;> field_simp <;> ring

/- English proof (translation)
Establish `h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1`. Apply the tactic sequence `ext <;> simp`. Conclude with `⟨⟨ω, algebraMap K (Etau K τ) τ - ω, h1, by rw [mul_comm]; exact h1⟩, rfl⟩`.
-/
theorem exists_a : ∃ a : (Etau K τ)ˣ, (a : Etau K τ) = ω := by
  have h1 : (ω : Etau K τ) * (algebraMap K (Etau K τ) τ - ω) = 1 := by
    ext <;> simp
  exact ⟨⟨ω, algebraMap K (Etau K τ) τ - ω, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end UpperTheory.V.Z.Sym.Loc
