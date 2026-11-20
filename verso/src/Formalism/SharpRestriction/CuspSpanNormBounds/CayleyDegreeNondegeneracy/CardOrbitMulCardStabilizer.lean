import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfFibreStructure

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

section Abstract

open MulAction

variable {Γ 𝒳 𝒴 : Type} [Group Γ] [MulAction Γ 𝒳] [MulAction Γ 𝒴]

/- English proof (translation)
Establish `h1 : Nat.card (orbit A x) = Nat.card (A ⧸ stabilizer A x)` using `Nat.card_congr (orbitEquivQuotientStabilizer A x)`. Establish `h2 : stabilizer A x = (stabilizer Γ x).subgroupOf A`. Use extensionality with `a`. Simplify using `[mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]`. Establish `h3 : Nat.card (stabilizer A x) = Nat.card (stabilizer Γ x)`.

Rewrite using `[h2]`. Conclude with `Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv`. Rewrite using `[h1, ← h3, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]`.
-/
theorem card_orbit_mul_card_stabilizer (A : Subgroup Γ) (x : 𝒳) (hle : stabilizer Γ x ≤ A) :
    Nat.card (orbit A x) * Nat.card (stabilizer Γ x) = Nat.card A := by
  have h1 : Nat.card (orbit A x) = Nat.card (A ⧸ stabilizer A x) :=
    Nat.card_congr (orbitEquivQuotientStabilizer A x)
  have h2 : stabilizer A x = (stabilizer Γ x).subgroupOf A := by
    ext a
    simp [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
  have h3 : Nat.card (stabilizer A x) = Nat.card (stabilizer Γ x) := by
    rw [h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, ← h3, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

/- English proof (translation)
The claim follows from `Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel (G := Γ) (a := g • y) (b := y) ⟨g, rfl⟩).toEquiv`.
-/
theorem card_stabilizer_smul_eq (g : Γ) (y : 𝒳) :
    Nat.card (stabilizer Γ (g • y)) = Nat.card (stabilizer Γ y) :=
  Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel (G := Γ) (a := g • y) (b := y) ⟨g, rfl⟩).toEquiv

/- English proof (translation)
Set `O : 𝒳 → Set 𝒳` to `fun y => {x | (x ∈ R ∧ m x = M) ∧ ∃ γ : Γ, γ • y = x}`. Establish `hOfin : ∀ y, (O y).Finite` using `fun y => hfin.subset fun x hx => hx.1`. Establish `hApos : (0 : ℝ) < (Nat.card (stabilizer Γ M) : ℝ)` using `by exact_mod_cast Nat.card_pos`. Establish `hcard : ∀ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), (O y).ncard * Nat.card (stabilizer Γ y) = Nat.card (stabilizer Γ M)`. Introduce `y hy`.

Take `⟨hys, γ0, hγ0⟩` from `Finset.mem_filter.1 hy`. Establish `hmx : m (γ0⁻¹ • y) = M` using `by rw [hm, ← hγ0, inv_smul_smul]`. Establish `hle : stabilizer Γ (γ0⁻¹ • y) ≤ stabilizer Γ M`. Introduce `γ hγ`. Rewrite `hγ`, the goal using `[mem_stabilizer_iff]`.

Rewrite using `[← hmx, ← hm, hγ]`. Establish `hO : O y = orbit (stabilizer Γ M) (γ0⁻¹ • y)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, hxM⟩, γ, rfl⟩`.

Use `⟨⟨γ * γ0, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_stabilizer_iff, mul_smul, hγ0, ← hm, hxM]`. Express the relevant statement in the definitionally equal form `(γ * γ0) • γ0⁻¹ • y = γ • y`. Rewrite using `[mul_smul, smul_inv_smul]`. Introduce and unpack `⟨⟨a, ha⟩, rfl⟩`.

Rewrite `ha` using `[mem_stabilizer_iff]`. Use `⟨⟨hR a _ (hR _ _ (hsR y hys)), ?_⟩, a * γ0⁻¹, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m (a • γ0⁻¹ • y) = M`. Rewrite using `[hm, hmx, ha]`. Express the relevant statement in the definitionally equal form `(a * γ0⁻¹) • y = a • γ0⁻¹ • y`.

Rewrite using `[mul_smul]`. Rewrite using `[hO, ← card_stabilizer_smul_eq γ0⁻¹ y, ← Nat.card_coe_set_eq]`. Conclude with `card_orbit_mul_card_stabilizer _ _ hle`. Establish `hpart : {x | x ∈ R ∧ m x = M}.ncard = ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), (O y).ncard`. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`.

Establish `hU : hfin.toFinset = (s.filter (fun y => ∃ γ : Γ, γ • M = m y)).biUnion fun y => (hOfin y).toFinset`. Use extensionality with `x`. Simplify using `only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨y, ⟨hy, γ, hγ⟩, _⟩` from `hs x hx.1`. Use `⟨y, ⟨hy, γ⁻¹, ?_⟩, hx, γ, hγ⟩` and prove the remaining obligations. Rewrite using `[← hx.2, ← hγ, hm, inv_smul_smul]`. Introduce and unpack `⟨y, _, hx, _⟩`. Conclude with `hx`.

Rewrite using `[hU, Finset.card_biUnion]`. Conclude with `Finset.sum_congr rfl fun y _ => (Set.ncard_eq_toFinset_card _ (hOfin y)).symm`. Introduce `y hy y' hy' hne`. Rewrite using `[Function.onFun, Finset.disjoint_left]`. Rewrite `hy`, `hy'` using `[Finset.mem_coe]`.

Introduce `x hx hx'`. Rewrite `hx`, `hx'` using `[Set.Finite.mem_toFinset]`. Take `⟨y0, _, huniq⟩` from `hs x hx.1.1`. Conclude with `hne ((huniq y ⟨(Finset.mem_filter.1 hy).1, hx.2⟩).trans (huniq y' ⟨(Finset.mem_filter.1 hy').1, hx'.2⟩).symm)`. Rewrite using `[hpart, Nat.cast_sum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `h` using `hcard y hy`. Establish `h' : ((O y).ncard : ℝ) * (Nat.card (stabilizer Γ y) : ℝ) = (Nat.card (stabilizer Γ M) : ℝ)`. Conclude with `h` after adjusting the coercions. Establish `hs0 : (Nat.card (stabilizer Γ y) : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `h'` using `[h0, mul_zero]`. Conclude with `hApos.ne h'`. Rewrite using `[← h']`. Establish `hO0 : ((O y).ncard : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `h'` using `[h0, zero_mul]`. Conclude with `hApos.ne h'`. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_fibre_inv_card_stabilizer (m : 𝒳 → 𝒴) (hm : ∀ (γ : Γ) x, m (γ • x) = γ • m x) (R : Set 𝒳)
    (hR : ∀ (γ : Γ), ∀ x ∈ R, γ • x ∈ R) (s : Finset 𝒳) (hsR : ∀ x ∈ s, x ∈ R)
    (hs : ∀ x ∈ R, ∃! y, y ∈ s ∧ ∃ γ : Γ, γ • y = x) (M : 𝒴) (hA : Finite (stabilizer Γ M))
    (hfin : {x | x ∈ R ∧ m x = M}.Finite) [DecidablePred fun y : 𝒳 => ∃ γ : Γ, γ • M = m y] :
    ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), ((Nat.card (stabilizer Γ y) : ℕ) : ℝ)⁻¹ =
      ({x | x ∈ R ∧ m x = M}.ncard : ℝ) / (Nat.card (stabilizer Γ M) : ℝ) := by
  classical
  let O : 𝒳 → Set 𝒳 := fun y => {x | (x ∈ R ∧ m x = M) ∧ ∃ γ : Γ, γ • y = x}
  have hOfin : ∀ y, (O y).Finite := fun y => hfin.subset fun x hx => hx.1
  have hApos : (0 : ℝ) < (Nat.card (stabilizer Γ M) : ℝ) := by exact_mod_cast Nat.card_pos
  have hcard : ∀ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y),
      (O y).ncard * Nat.card (stabilizer Γ y) = Nat.card (stabilizer Γ M) := by
    intro y hy
    obtain ⟨hys, γ0, hγ0⟩ := Finset.mem_filter.1 hy
    have hmx : m (γ0⁻¹ • y) = M := by rw [hm, ← hγ0, inv_smul_smul]
    have hle : stabilizer Γ (γ0⁻¹ • y) ≤ stabilizer Γ M := by
      intro γ hγ
      rw [mem_stabilizer_iff] at hγ ⊢
      rw [← hmx, ← hm, hγ]
    have hO : O y = orbit (stabilizer Γ M) (γ0⁻¹ • y) := by
      ext x
      constructor
      · rintro ⟨⟨_, hxM⟩, γ, rfl⟩
        refine ⟨⟨γ * γ0, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, hγ0, ← hm, hxM]
        · change (γ * γ0) • γ0⁻¹ • y = γ • y
          rw [mul_smul, smul_inv_smul]
      · rintro ⟨⟨a, ha⟩, rfl⟩
        rw [mem_stabilizer_iff] at ha
        refine ⟨⟨hR a _ (hR _ _ (hsR y hys)), ?_⟩, a * γ0⁻¹, ?_⟩
        · change m (a • γ0⁻¹ • y) = M
          rw [hm, hmx, ha]
        · change (a * γ0⁻¹) • y = a • γ0⁻¹ • y
          rw [mul_smul]
    rw [hO, ← card_stabilizer_smul_eq γ0⁻¹ y, ← Nat.card_coe_set_eq]
    exact card_orbit_mul_card_stabilizer _ _ hle
  have hpart : {x | x ∈ R ∧ m x = M}.ncard = ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), (O y).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have hU : hfin.toFinset = (s.filter (fun y => ∃ γ : Γ, γ • M = m y)).biUnion fun y => (hOfin y).toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨y, ⟨hy, γ, hγ⟩, _⟩ := hs x hx.1
        refine ⟨y, ⟨hy, γ⁻¹, ?_⟩, hx, γ, hγ⟩
        rw [← hx.2, ← hγ, hm, inv_smul_smul]
      · rintro ⟨y, _, hx, _⟩
        exact hx
    rw [hU, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun y _ => (Set.ncard_eq_toFinset_card _ (hOfin y)).symm
    · intro y hy y' hy' hne
      rw [Function.onFun, Finset.disjoint_left]
      rw [Finset.mem_coe] at hy hy'
      intro x hx hx'
      rw [Set.Finite.mem_toFinset] at hx hx'
      obtain ⟨y0, _, huniq⟩ := hs x hx.1.1
      exact hne ((huniq y ⟨(Finset.mem_filter.1 hy).1, hx.2⟩).trans
        (huniq y' ⟨(Finset.mem_filter.1 hy').1, hx'.2⟩).symm)
  rw [hpart, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hcard y hy
  have h' : ((O y).ncard : ℝ) * (Nat.card (stabilizer Γ y) : ℝ) = (Nat.card (stabilizer Γ M) : ℝ) := by
    exact_mod_cast h
  have hs0 : (Nat.card (stabilizer Γ y) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h'
    exact hApos.ne h'
  rw [← h']
  have hO0 : ((O y).ncard : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h'
    exact hApos.ne h'
  field_simp

end Abstract

end Formalism.MainNotions.BridgeLemma₂

end
