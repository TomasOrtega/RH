import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ConjPoint

open PeriodPair Polynomial WeierstrassCurve

def mapPoint (W : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ) :
    W.toAffine.Point →+ (W.map σ).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some _ _ h => .some _ _ <| (W.toAffine.map_nonsingular σ.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right,
        Affine.Point.add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, Affine.map_negY]]
    · simpa only [Affine.Point.add_some hxy, ← Affine.map_addX, ← Affine.map_addY,
        ← Affine.map_slope] using!
        (Affine.Point.add_some fun h ↦ hxy ⟨σ.injective h.1,
          σ.injective (W.toAffine.map_negY σ .. ▸ h).2⟩).symm

/- English proof (translation)
Substitute `hW` using the available equality. Use `⟨AddEquiv.ofBijective (mapPoint W σ) ⟨?_, ?_⟩, fun x y h ↦ ⟨_, rfl⟩⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `(_ | ⟨x, y, h⟩) e`. Both sides reduce to the same expression.

Conclude with `(Affine.Point.some_ne_zero _ e).elim`. Introduce and unpack `(_ | ⟨x, y, h⟩)`. Conclude with `⟨0, rfl⟩`. Take `⟨x, rfl⟩` from `σ.surjective x`. Take `⟨y, rfl⟩` from `σ.surjective y`.

Conclude with `⟨.some x y ((W.toAffine.map_nonsingular (σ : ℂ →+* ℂ).injective ..).mp h), rfl⟩`.
-/
lemma exists_pointHom (W W' : WeierstrassCurve ℂ) (σ : ℂ ≃+* ℂ) (hW : W' = W.map (σ : ℂ →+* ℂ)) :
    ∃ s : W.toAffine.Point ≃+ W'.toAffine.Point,
      ∀ x y h, ∃ h', s (.some x y h) = .some (σ x) (σ y) h' := by
  subst hW
  refine ⟨AddEquiv.ofBijective (mapPoint W σ) ⟨?_, ?_⟩, fun x y h ↦ ⟨_, rfl⟩⟩
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, h⟩) e
    · rfl
    · exact (Affine.Point.some_ne_zero _ e).elim
  · rintro (_ | ⟨x, y, h⟩)
    · exact ⟨0, rfl⟩
    · obtain ⟨x, rfl⟩ := σ.surjective x
      obtain ⟨y, rfl⟩ := σ.surjective y
      exact ⟨.some x y ((W.toAffine.map_nonsingular (σ : ℂ →+* ℂ).injective ..).mp h), rfl⟩

def IsConj (L L' : PeriodPair) (σ : ℂ ≃+* ℂ) (t t' : ℂ) : Prop :=
  (t ∈ L.lattice ∧ t' ∈ L'.lattice) ∨
  (t ∉ L.lattice ∧ t' ∉ L'.lattice ∧ ℘[L'] t' = σ (℘[L] t) ∧ ℘'[L'] t' = σ (℘'[L] t))

variable {L L' : PeriodPair} {σ : ℂ ≃+* ℂ}

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_pointHom (latticeCurve L) (latticeCurve L') σ (by`. Simplify using `[latticeCurve, WeierstrassCurve.map, h₂, h₃, map_ofNat])`. Use `⟨s, hs, fun t t' ↦ ?_⟩` and prove the remaining obligations. Unfold `IsConj`. Distinguish the cases in `ht : t ∈ L.lattice`.

Rewrite using `[latticePoint_of_mem L ht, map_zero, eq_comm (a := 0), latticePoint_eq_zero_iff]`. Simplify using `[ht]`. Rewrite using `[latticePoint_of_notMem L ht]`. Take `⟨h', e⟩` from `hs _ _ (latticeCurve_nonsingular L ht)`. Rewrite using `[e]`.

Distinguish the cases in `ht' : t' ∈ L'.lattice`. Rewrite using `[latticePoint_of_mem L' ht']`. Simplify using `[ht, ht']`. Rewrite using `[latticePoint_of_notMem L' ht', Affine.Point.some.injEq]`. Simplify using `only [ht, ht', map_div₀, map_ofNat, false_and, false_or, not_false_iff, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩`. Rewrite using `[a, b]`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨a, b⟩; exact ⟨a.symm, by linear_combination -2 * b⟩`.
-/
lemma exists_conjEquiv (h₂ : L'.g₂ = σ L.g₂) (h₃ : L'.g₃ = σ L.g₃) :
    ∃ s : (latticeCurve L).toAffine.Point ≃+ (latticeCurve L').toAffine.Point,
      (∀ x y h, ∃ h', s (.some x y h) = .some (σ x) (σ y) h') ∧
      ∀ t t', IsConj L L' σ t t' ↔ s (latticePoint L t) = latticePoint L' t' := by
  obtain ⟨s, hs⟩ := exists_pointHom (latticeCurve L) (latticeCurve L') σ (by
    simp [latticeCurve, WeierstrassCurve.map, h₂, h₃, map_ofNat])
  refine ⟨s, hs, fun t t' ↦ ?_⟩
  unfold IsConj
  by_cases ht : t ∈ L.lattice
  · rw [latticePoint_of_mem L ht, map_zero, eq_comm (a := 0), latticePoint_eq_zero_iff]
    simp [ht]
  · rw [latticePoint_of_notMem L ht]
    obtain ⟨h', e⟩ := hs _ _ (latticeCurve_nonsingular L ht)
    rw [e]
    by_cases ht' : t' ∈ L'.lattice
    · rw [latticePoint_of_mem L' ht']
      simp [ht, ht']
    · rw [latticePoint_of_notMem L' ht', Affine.Point.some.injEq]
      simp only [ht, ht', map_div₀, map_ofNat, false_and, false_or, not_false_iff, true_and]
      constructor
      · rintro ⟨a, b⟩; rw [a, b]; exact ⟨rfl, rfl⟩
      · rintro ⟨a, b⟩; exact ⟨a.symm, by linear_combination -2 * b⟩

/- English proof (translation)
Break down `eq_or_ne α 0 with rfl | hα0` into its components or cases. Use `left`. Simplify using the standard rewrite rules. Take `⟨s, hs, hc⟩` from `exists_conjEquiv h₂ h₃`. Take `⟨A, D, -, -, hD, -, -, -, -, hAD⟩` from `exists_latticeIsogeny_eq_div hα0 hα ⊤ trivial trivial`.

Use `trivial (fun _ _ _ ↦ trivial)`. Set `φ : (latticeCurve L').toAffine.Point →+ (latticeCurve L').toAffine.Point` to `(s.toAddMonoidHom.comp (latticeIsogeny α hα)).comp s.symm.toAddMonoidHom`. Establish `hφs : ∀ P, φ (s P) = s (latticeIsogeny α hα P)` using `fun P ↦ by simp [φ]`. Set `A'` to `A.map (σ : ℂ →+* ℂ)`. Set `D'` to `D.map (σ : ℂ →+* ℂ)`.

Establish `ev : ∀ (Q : ℂ[X]) (x : ℂ), (Q.map (σ : ℂ →+* ℂ)).eval (σ x) = σ (Q.eval x)` using `fun Q x ↦ by`. Rewrite using `[eval_map]`. Conclude with `eval₂_at_apply (σ : ℂ →+* ℂ) x`. Establish `hφ : ∀ (x y : ℂ) (h : (latticeCurve L').toAffine.Nonsingular x y), (D'.eval x = 0 → φ (.some x y h) = 0) ∧ (D'.eval x ≠ 0 → ∃ h', φ (.some x y h) = .some (A'.eval x / D'.eval x) ((σ α)⁻¹ * ((derivative A' * D' - A' * derivative D').eval x / D'.eval x ^ 2) * y) h')`. Introduce `x y h`.

Take `⟨P, hP⟩` from `s.surjective (.some x y h)`. Break down `P with _ | ⟨x₀, y₀, h₀⟩` into its components or cases. Conclude with `(Affine.Point.some_ne_zero _ (hP.symm.trans (map_zero s))).elim`. Take `⟨h₁, e⟩` from `hs _ _ h₀`. Rewrite using `[← hP, hφs]`.

Rewrite `hP` using `[e, Affine.Point.some.injEq]`. Take `⟨rfl, rfl⟩` from `hP`. Establish `e1 : (derivative A' * D' - A' * derivative D') = (derivative A * D - A * derivative D).map (σ : ℂ →+* ℂ)`. Simplify using `[A', D', Polynomial.map_sub, Polynomial.map_mul, derivative_map]`. Rewrite using `[e1]`.

Simplify using `only [A', D', ev, map_eq_zero, ne_eq]`. Use `⟨fun h0 ↦ by rw [(hAD _ _ h₀).1 h0, map_zero], fun h0 ↦ ?_⟩` and prove the remaining obligations. Take `⟨h', e'⟩` from `(hAD _ _ h₀).2 h0`. Take `⟨h'', e''⟩` from `hs _ _ h'`. Rewrite using `[e', e'']`.

Simplify using `only [← map_inv₀, ← map_div₀, ← map_pow, ← map_mul]`. Conclude with `⟨h'', trivial⟩`. Take `⟨β, hβ, hβ0, hφβ⟩` from `exists_eq_latticeIsogeny φ A' 0 D' (hD.map _).ne_zero (by`. Introduce `x y h h0`. Take `⟨h', e⟩` from `(hφ x y h).2 h0`.

Simplify using `only [eval_zero, zero_mul, add_zero]`. Conclude with `⟨_, h', e⟩)`. Establish `key : ∀ z, β * z ∉ L'.lattice → D'.eval (℘[L'] z) ≠ 0 ∧ ℘[L'] (β * z) = A'.eval (℘[L'] z) / D'.eval (℘[L'] z) ∧ ℘'[L'] (β * z) / 2 = (σ α)⁻¹ * ((derivative A' * D' - A' * derivative D').eval (℘[L'] z) / D'.eval (℘[L'] z) ^ 2) * (℘'[L'] z / 2)`. Introduce `z hz`. Establish `hz' : z ∉ L'.lattice` using `fun h ↦ hz (hβ z h)`.

Use `hφ _ _ (latticeCurve_nonsingular L' hz')` as an intermediate fact. Rewrite `this` using `[← latticePoint_of_notMem L' hz', hφβ, latticeIsogeny_latticePoint, latticePoint_eq_zero_iff]`. Establish `h0 : D'.eval (℘[L'] z) ≠ 0` using `fun h ↦ hz (this.1 h)`. Take `⟨h', e⟩` from `this.2 h0`. Rewrite `e` using `[latticePoint_of_notMem L' hz, Affine.Point.some.injEq]`.

Conclude with `⟨h0, e⟩`. Establish `hβα : β = σ α`. Establish `hσ : σ α ≠ 0` using `by simpa using hα0`. Establish `e : β * (L'.ω₁ / 4 / β) = L'.ω₁ / 4` using `by field_simp`. Establish `h2 : L'.ω₁ / 4 + L'.ω₁ / 4 ∉ L'.lattice`.

Rewrite using `[show L'.ω₁ / 4 + L'.ω₁ / 4 = L'.ω₁ / 2 by ring]`. Conclude with `L'.ω₁_div_two_notMem_lattice`. Establish `h1 : β * (L'.ω₁ / 4 / β) ∉ L'.lattice`. Rewrite using `[e]`. Conclude with `fun h ↦ h2 (add_mem h h)`.

Take `⟨k0, -, k2⟩` from `key _ h1`. Establish `k3` using `derivWeierstrassP_mul_eq hβ (fun z hz ↦ (key z hz).2.1) h1 k0`. Establish `k4 : ℘'[L'] (β * (L'.ω₁ / 4 / β)) ≠ 0`. Rewrite using `[Ne, derivWeierstrassP_eq_zero_iff L' h1, e]`. Conclude with `h2`.

Rewrite `k2` using `[mul_assoc, ← mul_div_assoc _ _ (2 : ℂ), ← k3]`. Generalize the expression as in `℘'[L'] (β * (L'.ω₁ / 4 / β)) = c at k2 k4`. Clear denominators, using `at k2` for the nonvanishing conditions. Conclude with `k2.symm`. Rewrite `ht`, the goal using `[hc]`.

Rewrite using `[← latticeIsogeny_latticePoint hα, ← hφs, ht, hφβ, latticeIsogeny_latticePoint, hβα]`.
-/
lemma IsConj.mul (h₂ : L'.g₂ = σ L.g₂) (h₃ : L'.g₃ = σ L.g₃) {α : ℂ}
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) {t t' : ℂ} (ht : IsConj L L' σ t t') :
    IsConj L L' σ (α * t) (σ α * t') := by
  rcases eq_or_ne α 0 with rfl | hα0
  · left; simp
  obtain ⟨s, hs, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨A, D, -, -, hD, -, -, -, -, hAD⟩ := exists_latticeIsogeny_eq_div hα0 hα ⊤ trivial trivial
    trivial (fun _ _ _ ↦ trivial)
  let φ : (latticeCurve L').toAffine.Point →+ (latticeCurve L').toAffine.Point :=
    (s.toAddMonoidHom.comp (latticeIsogeny α hα)).comp s.symm.toAddMonoidHom
  have hφs : ∀ P, φ (s P) = s (latticeIsogeny α hα P) := fun P ↦ by simp [φ]
  let A' := A.map (σ : ℂ →+* ℂ)
  let D' := D.map (σ : ℂ →+* ℂ)
  have ev : ∀ (Q : ℂ[X]) (x : ℂ), (Q.map (σ : ℂ →+* ℂ)).eval (σ x) = σ (Q.eval x) := fun Q x ↦ by
    rw [eval_map]; exact eval₂_at_apply (σ : ℂ →+* ℂ) x
  have hφ : ∀ (x y : ℂ) (h : (latticeCurve L').toAffine.Nonsingular x y),
      (D'.eval x = 0 → φ (.some x y h) = 0) ∧
      (D'.eval x ≠ 0 → ∃ h', φ (.some x y h) = .some (A'.eval x / D'.eval x)
        ((σ α)⁻¹ * ((derivative A' * D' - A' * derivative D').eval x / D'.eval x ^ 2) * y) h') := by
    intro x y h
    obtain ⟨P, hP⟩ := s.surjective (.some x y h)
    rcases P with _ | ⟨x₀, y₀, h₀⟩
    · exact (Affine.Point.some_ne_zero _ (hP.symm.trans (map_zero s))).elim
    obtain ⟨h₁, e⟩ := hs _ _ h₀
    rw [← hP, hφs]
    rw [e, Affine.Point.some.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    have e1 : (derivative A' * D' - A' * derivative D') =
        (derivative A * D - A * derivative D).map (σ : ℂ →+* ℂ) := by
      simp [A', D', Polynomial.map_sub, Polynomial.map_mul, derivative_map]
    rw [e1]
    simp only [A', D', ev, map_eq_zero, ne_eq]
    refine ⟨fun h0 ↦ by rw [(hAD _ _ h₀).1 h0, map_zero], fun h0 ↦ ?_⟩
    obtain ⟨h', e'⟩ := (hAD _ _ h₀).2 h0
    obtain ⟨h'', e''⟩ := hs _ _ h'
    rw [e', e'']
    simp only [← map_inv₀, ← map_div₀, ← map_pow, ← map_mul]
    exact ⟨h'', trivial⟩
  obtain ⟨β, hβ, hβ0, hφβ⟩ := exists_eq_latticeIsogeny φ A' 0 D' (hD.map _).ne_zero (by
    intro x y h h0
    obtain ⟨h', e⟩ := (hφ x y h).2 h0
    simp only [eval_zero, zero_mul, add_zero]
    exact ⟨_, h', e⟩)
  have key : ∀ z, β * z ∉ L'.lattice → D'.eval (℘[L'] z) ≠ 0 ∧
      ℘[L'] (β * z) = A'.eval (℘[L'] z) / D'.eval (℘[L'] z) ∧
      ℘'[L'] (β * z) / 2 = (σ α)⁻¹ * ((derivative A' * D' - A' * derivative D').eval (℘[L'] z) /
        D'.eval (℘[L'] z) ^ 2) * (℘'[L'] z / 2) := by
    intro z hz
    have hz' : z ∉ L'.lattice := fun h ↦ hz (hβ z h)
    have := hφ _ _ (latticeCurve_nonsingular L' hz')
    rw [← latticePoint_of_notMem L' hz', hφβ, latticeIsogeny_latticePoint,
      latticePoint_eq_zero_iff] at this
    have h0 : D'.eval (℘[L'] z) ≠ 0 := fun h ↦ hz (this.1 h)
    obtain ⟨h', e⟩ := this.2 h0
    rw [latticePoint_of_notMem L' hz, Affine.Point.some.injEq] at e
    exact ⟨h0, e⟩
  have hβα : β = σ α := by
    have hσ : σ α ≠ 0 := by simpa using hα0
    have e : β * (L'.ω₁ / 4 / β) = L'.ω₁ / 4 := by field_simp
    have h2 : L'.ω₁ / 4 + L'.ω₁ / 4 ∉ L'.lattice := by
      rw [show L'.ω₁ / 4 + L'.ω₁ / 4 = L'.ω₁ / 2 by ring]
      exact L'.ω₁_div_two_notMem_lattice
    have h1 : β * (L'.ω₁ / 4 / β) ∉ L'.lattice := by
      rw [e]; exact fun h ↦ h2 (add_mem h h)
    obtain ⟨k0, -, k2⟩ := key _ h1
    have k3 := derivWeierstrassP_mul_eq hβ (fun z hz ↦ (key z hz).2.1) h1 k0
    have k4 : ℘'[L'] (β * (L'.ω₁ / 4 / β)) ≠ 0 := by
      rw [Ne, derivWeierstrassP_eq_zero_iff L' h1, e]; exact h2
    rw [mul_assoc, ← mul_div_assoc _ _ (2 : ℂ), ← k3] at k2
    generalize ℘'[L'] (β * (L'.ω₁ / 4 / β)) = c at k2 k4
    field_simp at k2
    exact k2.symm
  rw [hc] at ht ⊢
  rw [← latticeIsogeny_latticePoint hα, ← hφs, ht, hφβ, latticeIsogeny_latticePoint, hβα]

/- English proof (translation)
Set `S' : Set M` to `Subtype.val ⁻¹' S`. Establish `hS' : S'.Countable` using `hS.preimage Subtype.val_injective`. Use `haveI : Countable (Subfield.closure S') := by`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Use `(Subfield.cardinalMk_closure_le_max S').trans (max_le ?_ le_rfl)` and prove the remaining obligations.

Conclude with `Cardinal.mk_le_aleph0_iff.2 hS'`. Take `⟨σ, hσ⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq ((M.val : M →+* ℂ).comp (Subfield.closure S').subtype) ((ρ : M →+* ℂ).comp (Subfield.closure S').subtype)`. Use `⟨σ, fun x hx hM ↦ ?_⟩` and prove the remaining obligations. Use `hσ ⟨⟨x, hM⟩, Subfield.subset_closure hx⟩` as an intermediate fact. Simplify `this` using `[cj, TaylorLogMetric.liftM, hM]`.
-/
lemma exists_ringEquiv_eq_cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {S : Set ℂ}
    (hS : S.Countable) : ∃ σ : ℂ ≃+* ℂ, ∀ x ∈ S, x ∈ M → σ x = cj M ρ x := by
  let S' : Set M := Subtype.val ⁻¹' S
  have hS' : S'.Countable := hS.preimage Subtype.val_injective
  haveI : Countable (Subfield.closure S') := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max S').trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hS'
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq
    ((M.val : M →+* ℂ).comp (Subfield.closure S').subtype)
    ((ρ : M →+* ℂ).comp (Subfield.closure S').subtype)
  refine ⟨σ, fun x hx hM ↦ ?_⟩
  have := hσ ⟨⟨x, hM⟩, Subfield.subset_closure hx⟩
  simpa [cj, TaylorLogMetric.liftM, hM] using this

def IsRat (L : PeriodPair) (M : IntermediateField ℚ ℂ) (t : ℂ) : Prop :=
  t ∈ L.lattice ∨ (℘[L] t ∈ M ∧ ℘'[L] t ∈ M)

variable {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

/- English proof (translation)
Distinguish the cases in `ht : t ∈ L.lattice`. Conclude with `.inl ⟨ht, ht⟩`. Take `⟨a, b⟩` from `h.resolve_left ht`. Conclude with `.inr ⟨ht, ht, (hσ _ a).symm, (hσ _ b).symm⟩`.
-/
lemma IsRat.isConj {t : ℂ} (h : IsRat L M t) (hσ : ∀ x ∈ M, σ x = x) : IsConj L L σ t t := by
  by_cases ht : t ∈ L.lattice
  · exact .inl ⟨ht, ht⟩
  · obtain ⟨a, b⟩ := h.resolve_left ht
    exact .inr ⟨ht, ht, (hσ _ a).symm, (hσ _ b).symm⟩

/- English proof (translation)
Distinguish the cases in `ht : t ∈ L.lattice`. Conclude with `.inl ht`. Establish `key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ x ∈ M, σ x = x) → σ x = x) → x ∈ M` using `fun x hx ↦ by`. Take `⟨y, rfl⟩` from `GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M) x fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩`. Conclude with `y.2`.

Use `.inr ⟨key _ fun σ hσ ↦ ?_, key _ fun σ hσ ↦ ?_⟩` and prove the remaining obligations. Conclude with `((h σ hσ).resolve_left fun h ↦ ht h.1).2.2.1.symm`. Conclude with `((h σ hσ).resolve_left fun h ↦ ht h.1).2.2.2.symm`.
-/
lemma isRat_of_forall_isConj {t : ℂ}
    (h : ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ M, σ x = x) → IsConj L L σ t t) : IsRat L M t := by
  by_cases ht : t ∈ L.lattice
  · exact .inl ht
  have key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ x ∈ M, σ x = x) → σ x = x) → x ∈ M := fun x hx ↦ by
    obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M) x
      fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩
    exact y.2
  refine .inr ⟨key _ fun σ hσ ↦ ?_, key _ fun σ hσ ↦ ?_⟩
  · exact ((h σ hσ).resolve_left fun h ↦ ht h.1).2.2.1.symm
  · exact ((h σ hσ).resolve_left fun h ↦ ht h.1).2.2.2.symm

/- English proof (translation)
Take `⟨s, -, hc⟩` from `exists_conjEquiv h₂ h₃`. Rewrite `ht`, `hu`, the goal using `[hc]`. Rewrite using `[latticePoint_add, latticePoint_add, map_add, ht, hu]`.
-/
lemma IsConj.add (h₂ : L'.g₂ = σ L.g₂) (h₃ : L'.g₃ = σ L.g₃) {t t' u u' : ℂ}
    (ht : IsConj L L' σ t t') (hu : IsConj L L' σ u u') : IsConj L L' σ (t + u) (t' + u') := by
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  rw [hc] at ht hu ⊢
  rw [latticePoint_add, latticePoint_add, map_add, ht, hu]

/- English proof (translation)
Use `IsConj.mul h₂ h₃ (α := n) (fun l hl ↦ by rw [← nsmul_eq_mul]; exact nsmul_mem hl n) ht` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Break down `this with h | h` into its components or cases. Conclude with `iff_of_true h.1 h.2`. Conclude with `iff_of_false h.1 h.2.1`.
-/
lemma IsConj.nsmul_mem_iff (h₂ : L'.g₂ = σ L.g₂) (h₃ : L'.g₃ = σ L.g₃) {t t' : ℂ}
    (ht : IsConj L L' σ t t') (n : ℕ) : (n : ℂ) * t ∈ L.lattice ↔ (n : ℂ) * t' ∈ L'.lattice := by
  have := IsConj.mul h₂ h₃ (α := n)
    (fun l hl ↦ by rw [← nsmul_eq_mul]; exact nsmul_mem hl n) ht
  rw [map_natCast] at this
  rcases this with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false h.1 h.2.1

def IsStar (L L' : PeriodPair) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (t t' : ℂ) : Prop :=
  (t ∈ L.lattice ∧ t' ∈ L'.lattice) ∨
  (t ∉ L.lattice ∧ t' ∉ L'.lattice ∧ ℘[L] t ∈ M ∧ ℘'[L] t ∈ M ∧
    ℘[L'] t' = cj M ρ (℘[L] t) ∧ ℘'[L'] t' = cj M ρ (℘'[L] t))

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_ringEquiv_eq_cj M ρ (S := {L.g₂, L.g₃, α} ∪ (℘[L] '' T ∪ ℘'[L] '' T)) ((Set.toFinite _).countable.union ((hT.image _).union (hT.image _)))`. Use `⟨σ, by rw [hσ _ (by simp) m₂, h₂], by rw [hσ _ (by simp) m₃, h₃], hσ _ (by simp) mα, fun t ht t' ↦ ?_⟩` and prove the remaining obligations. Establish `a` using `hσ (℘[L] t) (.inr (.inl ⟨t, ht, rfl⟩))`. Establish `b` using `hσ (℘'[L] t) (.inr (.inr ⟨t, ht, rfl⟩))`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(h | ⟨h1, h2, h3, h4, h5, h6⟩)`. Conclude with `⟨.inl h.1, .inl h⟩`. Conclude with `⟨.inr ⟨h3, h4⟩, .inr ⟨h1, h2, by rw [a h3, h5], by rw [b h4, h6]⟩⟩`. Introduce and unpack `⟨h0, h | ⟨h1, h2, h5, h6⟩⟩`. Conclude with `.inl h`.

Take `⟨h3, h4⟩` from `h0.resolve_left h1`. Conclude with `.inr ⟨h1, h2, h3, h4, by rw [← a h3, h5], by rw [← b h4, h6]⟩`.
-/
lemma exists_ringEquiv_isStar (m₂ : L.g₂ ∈ M) (m₃ : L.g₃ ∈ M) (h₂ : L'.g₂ = cj M ρ L.g₂)
    (h₃ : L'.g₃ = cj M ρ L.g₃) {α : ℂ} (mα : α ∈ M) {T : Set ℂ} (hT : T.Countable) :
    ∃ σ : ℂ ≃+* ℂ, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ ∧ σ α = cj M ρ α ∧
      ∀ t ∈ T, ∀ t', IsStar L L' M ρ t t' ↔ IsRat L M t ∧ IsConj L L' σ t t' := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_eq_cj M ρ
    (S := {L.g₂, L.g₃, α} ∪ (℘[L] '' T ∪ ℘'[L] '' T))
    ((Set.toFinite _).countable.union ((hT.image _).union (hT.image _)))
  refine ⟨σ, by rw [hσ _ (by simp) m₂, h₂], by rw [hσ _ (by simp) m₃, h₃], hσ _ (by simp) mα,
    fun t ht t' ↦ ?_⟩
  have a := hσ (℘[L] t) (.inr (.inl ⟨t, ht, rfl⟩))
  have b := hσ (℘'[L] t) (.inr (.inr ⟨t, ht, rfl⟩))
  constructor
  · rintro (h | ⟨h1, h2, h3, h4, h5, h6⟩)
    · exact ⟨.inl h.1, .inl h⟩
    · exact ⟨.inr ⟨h3, h4⟩, .inr ⟨h1, h2, by rw [a h3, h5], by rw [b h4, h6]⟩⟩
  · rintro ⟨h0, h | ⟨h1, h2, h5, h6⟩⟩
    · exact .inl h
    · obtain ⟨h3, h4⟩ := h0.resolve_left h1
      exact .inr ⟨h1, h2, h3, h4, by rw [← a h3, h5], by rw [← b h4, h6]⟩

/- English proof (translation)
Use `⟨fun t ht ↦ ?_, fun t t₁ t₂ h ↦ ?_, fun t t' u u' ht hu ↦ ?_, fun α mα hα t t' ht ↦ ?_, fun n t t' ht ↦ ?_, fun n hn hr t' ht' ↦ ?_⟩` and prove the remaining obligations. Take `⟨σ, e₂, e₃, -, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem (Set.countable_singleton t)`. Take `⟨s, -, hc⟩` from `exists_conjEquiv e₂ e₃`. Take `⟨t', ht'⟩` from `latticePoint_surjective L' (s (latticePoint L t))`. Conclude with `⟨t', (hσ t rfl t').2 ⟨ht, (hc _ _).2 ht'.symm⟩⟩`.

Take `⟨σ, e₂, e₃, -, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem (Set.countable_singleton t)`. Take `⟨s, -, hc⟩` from `exists_conjEquiv e₂ e₃`. Rewrite `h` using `[hσ t rfl, hc]`. Rewrite using `[hσ t rfl, hc, h.2, latticePoint_eq_iff, and_iff_right h.1]`. Take `⟨σ, e₂, e₃, -, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem (T := {t, u, t + u}) (Set.toFinite _).countable`.

Rewrite `ht`, `hu`, the goal using `[hσ _ (by simp)]`. Conclude with `⟨isRat_of_forall_isConj fun τ hτ ↦ IsConj.add (hτ _ m₂).symm (hτ _ m₃).symm (ht.1.isConj hτ) (hu.1.isConj hτ), IsConj.add e₂ e₃ ht.2 hu.2⟩`. Take `⟨σ, e₂, e₃, eα, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ mα (T := {t, α * t}) (Set.toFinite _).countable`. Rewrite `ht`, the goal using `[hσ _ (by simp)]`. Use `⟨isRat_of_forall_isConj fun τ hτ ↦ ?_, eα ▸ IsConj.mul e₂ e₃ hα ht.2⟩` and prove the remaining obligations.

Use `IsConj.mul (hτ _ m₂).symm (hτ _ m₃).symm hα (ht.1.isConj hτ)` as an intermediate fact. Rewrite `this` using `[hτ _ mα]`. Then use the resulting hypothesis. Take `⟨σ, e₂, e₃, -, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem (Set.countable_singleton t)`. Conclude with `((hσ t rfl t').1 ht).2.nsmul_mem_iff e₂ e₃ n`. Establish `hL : (L.lattice : Set ℂ).Countable`.

Use `(Set.countable_range fun p : ℤ × ℤ ↦ p.1 * L.ω₁ + p.2 * L.ω₂).mono fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨a, b, h⟩` from `L.mem_lattice.1 hx`. Conclude with `⟨(a, b), h⟩`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Take `⟨σ, e₂, e₃, -, hσ⟩` from `exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem (T := (fun t ↦ (n : ℂ) * t) ⁻¹' (L.lattice : Set ℂ)) (hL.preimage (mul_right_injective₀ hn'))`.

Take `⟨s, -, hc⟩` from `exists_conjEquiv e₂ e₃`. Take `⟨P, hP⟩` from `s.surjective (latticePoint L' t')`. Take `⟨t, rfl⟩` from `latticePoint_surjective L P`. Establish `h` using `(hc _ _).2 hP`. Establish `hnt` using `(h.nsmul_mem_iff e₂ e₃ n).2 ht'`.

Conclude with `⟨t, hnt, (hσ t hnt t').2 ⟨hr t hnt, h⟩⟩`.
-/
theorem isStar_props (m₂ : L.g₂ ∈ M) (m₃ : L.g₃ ∈ M) (h₂ : L'.g₂ = cj M ρ L.g₂)
    (h₃ : L'.g₃ = cj M ρ L.g₃) :
    (∀ t, IsRat L M t → ∃ t', IsStar L L' M ρ t t') ∧
    (∀ t t₁ t₂, IsStar L L' M ρ t t₁ → (IsStar L L' M ρ t t₂ ↔ t₁ - t₂ ∈ L'.lattice)) ∧
    (∀ t t' u u', IsStar L L' M ρ t t' → IsStar L L' M ρ u u' →
      IsStar L L' M ρ (t + u) (t' + u')) ∧
    (∀ α ∈ M, (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ∀ t t', IsStar L L' M ρ t t' →
      IsStar L L' M ρ (α * t) (cj M ρ α * t')) ∧
    (∀ (n : ℕ) t t', IsStar L L' M ρ t t' →
      ((n : ℂ) * t ∈ L.lattice ↔ (n : ℂ) * t' ∈ L'.lattice)) ∧
    (∀ n : ℕ, 0 < n → (∀ t, (n : ℂ) * t ∈ L.lattice → IsRat L M t) →
      ∀ t', (n : ℂ) * t' ∈ L'.lattice → ∃ t, (n : ℂ) * t ∈ L.lattice ∧ IsStar L L' M ρ t t') := by
  refine ⟨fun t ht ↦ ?_, fun t t₁ t₂ h ↦ ?_, fun t t' u u' ht hu ↦ ?_, fun α mα hα t t' ht ↦ ?_,
    fun n t t' ht ↦ ?_, fun n hn hr t' ht' ↦ ?_⟩
  · obtain ⟨σ, e₂, e₃, -, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem
      (Set.countable_singleton t)
    obtain ⟨s, -, hc⟩ := exists_conjEquiv e₂ e₃
    obtain ⟨t', ht'⟩ := latticePoint_surjective L' (s (latticePoint L t))
    exact ⟨t', (hσ t rfl t').2 ⟨ht, (hc _ _).2 ht'.symm⟩⟩
  · obtain ⟨σ, e₂, e₃, -, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem
      (Set.countable_singleton t)
    obtain ⟨s, -, hc⟩ := exists_conjEquiv e₂ e₃
    rw [hσ t rfl, hc] at h
    rw [hσ t rfl, hc, h.2, latticePoint_eq_iff, and_iff_right h.1]
  · obtain ⟨σ, e₂, e₃, -, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem
      (T := {t, u, t + u}) (Set.toFinite _).countable
    rw [hσ _ (by simp)] at ht hu ⊢
    exact ⟨isRat_of_forall_isConj fun τ hτ ↦ IsConj.add (hτ _ m₂).symm (hτ _ m₃).symm
      (ht.1.isConj hτ) (hu.1.isConj hτ), IsConj.add e₂ e₃ ht.2 hu.2⟩
  · obtain ⟨σ, e₂, e₃, eα, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ mα
      (T := {t, α * t}) (Set.toFinite _).countable
    rw [hσ _ (by simp)] at ht ⊢
    refine ⟨isRat_of_forall_isConj fun τ hτ ↦ ?_, eα ▸ IsConj.mul e₂ e₃ hα ht.2⟩
    have := IsConj.mul (hτ _ m₂).symm (hτ _ m₃).symm hα (ht.1.isConj hτ)
    rwa [hτ _ mα] at this
  · obtain ⟨σ, e₂, e₃, -, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem
      (Set.countable_singleton t)
    exact ((hσ t rfl t').1 ht).2.nsmul_mem_iff e₂ e₃ n
  · have hL : (L.lattice : Set ℂ).Countable := by
      refine (Set.countable_range fun p : ℤ × ℤ ↦ p.1 * L.ω₁ + p.2 * L.ω₂).mono fun x hx ↦ ?_
      obtain ⟨a, b, h⟩ := L.mem_lattice.1 hx
      exact ⟨(a, b), h⟩
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨σ, e₂, e₃, -, hσ⟩ := exists_ringEquiv_isStar m₂ m₃ h₂ h₃ M.zero_mem
      (T := (fun t ↦ (n : ℂ) * t) ⁻¹' (L.lattice : Set ℂ))
      (hL.preimage (mul_right_injective₀ hn'))
    obtain ⟨s, -, hc⟩ := exists_conjEquiv e₂ e₃
    obtain ⟨P, hP⟩ := s.surjective (latticePoint L' t')
    obtain ⟨t, rfl⟩ := latticePoint_surjective L P
    have h := (hc _ _).2 hP
    have hnt := (h.nsmul_mem_iff e₂ e₃ n).2 ht'
    exact ⟨t, hnt, (hσ t hnt t').2 ⟨hr t hnt, h⟩⟩

/- English proof (translation)
Introduce `D cc δ hc M ρ hK m₂ m₃`. Take `⟨⟨w₁, w₂, hw, hΛ⟩, -, -, -, hO⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc`. Generalize the expression as in `lamOf D cc δ = Λ at *`. Set `L : PeriodPair` to `⟨w₁, w₂, hw⟩`. Establish `hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice` using `fun z ↦ by`.

Rewrite using `[hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `[L]`. Take `⟨g₂e, g₃e, hd, -, hwp, -, hex⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL`. Take `⟨L', h₂, h₃⟩` from `hex (cj M ρ (g2 Λ)) (cj M ρ (g3 Λ)) (by`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Establish `h' : ρ (⟨g2 Λ, m₂⟩ ^ 3 - 27 * ⟨g3 Λ, m₃⟩ ^ 2) = 0`. Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_ofNat]`. Simplify `h` using `only [cj, TaylorLogMetric.liftM, dif_pos m₂, dif_pos m₃]`. Establish `h''` using `congrArg Subtype.val ((map_eq_zero ρ).1 h')`.

Conclude with `h'')`. Take `⟨g₂e', g₃e', -, -, hwp', huniq, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup fun _ ↦ Iff.rfl`. Establish `hΛ' : lamConj M ρ Λ = L'.lattice.toAddSubgroup`. Use `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨L'.lattice.toAddSubgroup, g₂e'.trans h₂, g₃e'.trans h₃⟩` as an intermediate fact. Conclude with `huniq _ (this.1.trans (g₂e'.trans h₂).symm) (this.2.trans (g₃e'.trans h₃).symm)`.

Establish `hL' : ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice` using `fun z ↦ by rw [hΛ']; rfl`. Establish `hS : ∀ t t', StarPt M ρ Λ t t' ↔ IsStar L L' M ρ t t'` using `fun t t' ↦ by`. Unfold `StarPt IsStar`. Rewrite using `[← hL, ← hL']`. Use `or_congr Iff.rfl (and_congr_right fun ht ↦ and_congr_right fun ht' ↦ ?_)` and prove the remaining obligations.

Rewrite `ht'`, the goal using `[hΛ']`. Rewrite using `[(hwp t ht).1, (hwp t ht).2, (hwp' t' ht').1, (hwp' t' ht').2]`. Establish `hR : ∀ t, (t ∉ Λ → wpF Λ t ∈ M ∧ wpD Λ t ∈ M) → IsRat L M t` using `fun t h ↦ by`. Distinguish the cases in `ht : t ∈ Λ`. Conclude with `.inl ((hL t).1 ht)`.

Conclude with `.inr (by rw [← (hwp t ht).1, ← (hwp t ht).2]; exact h ht)`. Rewrite `m₂`, `h₂` using `[g₂e]`. Rewrite `m₃`, `h₃` using `[g₃e]`. Take `⟨a1, a2, a3, a4, a5, a6⟩` from `isStar_props m₂ m₃ h₂ h₃`. Simplify using `only [hS, hL']`.

Use `⟨fun t _ ht ↦ a1 t (hR t fun h ↦ ht.resolve_left h), a2, fun t t' ω ht hω ↦ ?_, a3, fun a t t' ht ↦ ?_, fun n t t' ht ↦ ?_, fun n hn hr t' ht' ↦ ?_⟩` and prove the remaining obligations. Simplify using `using a3 t t' ω 0 ht (.inl ⟨(hL ω).1 hω, zero_mem _⟩)`. Use `a4 _ (hK (a : D.host.K)).1 (fun l hl ↦ (hL _).1 (hO a l ((hL l).2 hl))) t t' ht` as an intermediate fact. Rewrite `this` using `[(hK (a : D.host.K)).2]`. Then use the resulting hypothesis. Rewrite using `[hL]`.

Conclude with `a5 n t t' ht`. Take `⟨t, h1, h2⟩` from `a6 n hn (fun t ht ↦ hR t (hr t ((hL _).2 ht))) t' ht'`. Conclude with `⟨t, (hL _).2 h1, h2⟩`.
-/
theorem galStar_holds : ∀ D : D7, galStar D := by
  intro D cc δ hc M ρ hK m₂ m₃
  obtain ⟨⟨w₁, w₂, hw, hΛ⟩, -, -, -, hO⟩ := GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc
  generalize lamOf D cc δ = Λ at *
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z ↦ by
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨g₂e, g₃e, hd, -, hwp, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨L', h₂, h₃⟩ := hex (cj M ρ (g2 Λ)) (cj M ρ (g3 Λ)) (by
    intro h
    apply hd
    have h' : ρ (⟨g2 Λ, m₂⟩ ^ 3 - 27 * ⟨g3 Λ, m₃⟩ ^ 2) = 0 := by
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat]
      simpa only [cj, TaylorLogMetric.liftM, dif_pos m₂, dif_pos m₃] using h
    have h'' := congrArg Subtype.val ((map_eq_zero ρ).1 h')
    exact h'')
  obtain ⟨g₂e', g₃e', -, -, hwp', huniq, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup fun _ ↦ Iff.rfl
  have hΛ' : lamConj M ρ Λ = L'.lattice.toAddSubgroup := by
    have := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ)))
      ⟨L'.lattice.toAddSubgroup, g₂e'.trans h₂, g₃e'.trans h₃⟩
    exact huniq _ (this.1.trans (g₂e'.trans h₂).symm) (this.2.trans (g₃e'.trans h₃).symm)
  have hL' : ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice := fun z ↦ by rw [hΛ']; rfl
  have hS : ∀ t t', StarPt M ρ Λ t t' ↔ IsStar L L' M ρ t t' := fun t t' ↦ by
    unfold StarPt IsStar
    rw [← hL, ← hL']
    refine or_congr Iff.rfl (and_congr_right fun ht ↦ and_congr_right fun ht' ↦ ?_)
    rw [hΛ'] at ht' ⊢
    rw [(hwp t ht).1, (hwp t ht).2, (hwp' t' ht').1, (hwp' t' ht').2]
  have hR : ∀ t, (t ∉ Λ → wpF Λ t ∈ M ∧ wpD Λ t ∈ M) → IsRat L M t := fun t h ↦ by
    by_cases ht : t ∈ Λ
    · exact .inl ((hL t).1 ht)
    · exact .inr (by rw [← (hwp t ht).1, ← (hwp t ht).2]; exact h ht)
  rw [g₂e] at m₂ h₂
  rw [g₃e] at m₃ h₃
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := isStar_props m₂ m₃ h₂ h₃
  simp only [hS, hL']
  refine ⟨fun t _ ht ↦ a1 t (hR t fun h ↦ ht.resolve_left h), a2, fun t t' ω ht hω ↦ ?_, a3,
    fun a t t' ht ↦ ?_, fun n t t' ht ↦ ?_, fun n hn hr t' ht' ↦ ?_⟩
  · simpa using a3 t t' ω 0 ht (.inl ⟨(hL ω).1 hω, zero_mem _⟩)
  · have := a4 _ (hK (a : D.host.K)).1 (fun l hl ↦ (hL _).1 (hO a l ((hL l).2 hl))) t t' ht
    rwa [(hK (a : D.host.K)).2] at this
  · rw [hL]; exact a5 n t t' ht
  · obtain ⟨t, h1, h2⟩ := a6 n hn (fun t ht ↦ hR t (hr t ((hL _).2 ht))) t' ht'
    exact ⟨t, (hL _).2 h1, h2⟩

end GlobalTheory.ConjPoint
