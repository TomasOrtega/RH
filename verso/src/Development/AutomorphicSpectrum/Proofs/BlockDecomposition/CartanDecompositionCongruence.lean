import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFractionRingInteger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteCosetsPrincipalCongruence

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Dblock.CartanCover

/- English proof (translation)
Proceed by induction on `n, h using Nat.le_induction with`. Consider the case `base`. Rewrite using `[Finset.sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `j hj`.

Rewrite using `[if_neg]`. Simplify using `using hj`. Consider the case `succ n hn ih`. Rewrite using `[Finset.sum_range_succ, ih, if_pos hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_tel (A : ℕ → ℤ) (i n : ℕ) (h : i ≤ n) :
    ∑ j ∈ Finset.range n, (if i ≤ j then A j - A (j + 1) else 0) = A i - A n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      rw [if_neg]
      simpa using hj
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos hn]
    ring

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Set `A : ℕ → ℤ` to `fun j => a ⟨min j n, by omega⟩`. Establish `hA : ∀ j, A (j + 1) ≤ A j` using `fun j => ha (by simp only [Fin.le_def]; omega)`. Use `⟨fun j => (A j - A (j + 1)).toNat, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `sum_tel A i n (by omega)`.

Rewrite `h1` using `[Finset.sum_range]`. Establish `hi : A i = a i`. Simplify using `only [A]`. Use `congr 1`. Use `ext`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hn : A n = a ⟨n + 1 - 1, by omega⟩`. Simplify using `only [A]`. Use `congr 1`.

Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[← hi, ← hn, ← h1]`. Unfold `Zls.lamOf`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Int.toNat_of_nonneg (by linarith [hA j])`. Both sides reduce to the same expression.
-/
theorem exists_lamOf (N : ℕ) (hN : 1 ≤ N) (a : Fin N → ℤ) (ha : Antitone a) :
    ∃ g : Fin (N - 1) → ℕ, ∀ i, Zls.lamOf g i = a i - a ⟨N - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  let A : ℕ → ℤ := fun j => a ⟨min j n, by omega⟩
  have hA : ∀ j, A (j + 1) ≤ A j := fun j => ha (by simp only [Fin.le_def]; omega)
  refine ⟨fun j => (A j - A (j + 1)).toNat, fun i => ?_⟩
  have h1 := sum_tel A i n (by omega)
  rw [Finset.sum_range] at h1
  have hi : A i = a i := by
    simp only [A]
    congr 1
    ext
    simp only
    omega
  have hn : A n = a ⟨n + 1 - 1, by omega⟩ := by
    simp only [A]
    congr 1
    ext
    simp
  rw [← hi, ← hn, ← h1]
  unfold Zls.lamOf
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact Int.toNat_of_nonneg (by linarith [hA j])
  · rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable abbrev red (N m : ℕ) :
    GL (Fin N) 𝒪[k] →* GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))

noncomputable abbrev incl (N : ℕ) : GL (Fin N) 𝒪[k] →* GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k)

/- English proof (translation)
Use `haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k`. Use `haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) := GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow 𝒪[k] (Zls.unif k) m Zls.irreducible_unif`. Use `infer_instance`.
-/
theorem finite_red (N m : ℕ) : Finite (GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m})) := by
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
    GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow 𝒪[k] (Zls.unif k) m Zls.irreducible_unif
  infer_instance

/- English proof (translation)
Establish `h1 : ((Zls.diagPow k N (Zls.lamOf g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => ((Zls.unifU k ^ Zls.lamOf g i : kˣ) : k)` using `rfl`. Establish `h2 : ((Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun _ => ((Zls.unifU k ^ c : kˣ) : k)` using `rfl`. Rewrite using `[Units.val_mul, h1, h2, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← Units.val_mul, ← zpow_add, hg, sub_add_cancel, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
theorem diag_eq (N : ℕ) (a : Fin N → ℤ) (g : Fin (N - 1) → ℕ) (c : ℤ)
    (hg : ∀ i, Zls.lamOf g i = a i - c) :
    (Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ (a i)) : Matrix (Fin N) (Fin N) k) =
      ((Zls.diagPow k N (Zls.lamOf g) * Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) :
        GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
  have h1 : ((Zls.diagPow k N (Zls.lamOf g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ Zls.lamOf g i : kˣ) : k) := rfl
  have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun _ => ((Zls.unifU k ^ c : kˣ) : k) := rfl
  rw [Units.val_mul, h1, h2, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Units.val_mul, ← zpow_add, hg, sub_add_cancel, Units.val_zpow_eq_zpow_val]
  rfl

/- English proof (translation)
Introduce `k _ _ _ _ N m _ hN`. Use `haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k`. Use `haveI := finite_red k N m`. Establish `hsec : ∀ u : GL (Fin N) 𝒪[k], ∃ w : GL (Fin N) 𝒪[k], red k N m w = red k N m u` using `fun u => ⟨u, rfl⟩`. Set `σ : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) → GL (Fin N) 𝒪[k]` to `fun c => if hc : ∃ w, red k N m w = c then hc.choose else 1`.

Establish `hσ : ∀ u, red k N m (σ (red k N m u)) = red k N m u` using `fun u => by`. Establish `hc : ∃ w, red k N m w = red k N m u` using `hsec u`. Simplify using `only [σ, dif_pos hc]`. Conclude with `hc.choose_spec`. Set `f : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) × GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) → GL (Fin N) k × GL (Fin N) k` to `fun c => (incl k N (σ c.1), incl k N (σ c.2))`.

Use `⟨(Set.finite_range f).toFinset, ?_, fun h => ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨c, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hp`. Conclude with `⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩`. Establish `hh : IsUnit (h : Matrix (Fin N) (Fin N) k).det` using `(Matrix.isUnit_iff_isUnit_det _).1 h.isUnit`.

Take `⟨u, v, a, hu, hv, ha, e⟩` from `GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists 𝒪[k] k N (Zls.unif k) Zls.irreducible_unif (h : Matrix (Fin N) (Fin N) k) hh`. Take `⟨g, hg⟩` from `exists_lamOf N hN a ha`. Set `U : GL (Fin N) 𝒪[k]` to `Matrix.nonsingInvUnit u hu`. Set `V : GL (Fin N) 𝒪[k]` to `Matrix.nonsingInvUnit v hv`. Set `z : GL (Fin N) k` to `Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ a ⟨N - 1, by omega⟩)`.

Establish `hz : z ∈ Subgroup.center (GL (Fin N) k)`. Rewrite using `[Matrix.GeneralLinearGroup.center_eq_range_scalar]`. Conclude with `⟨_, rfl⟩`. Establish `hzc : ∀ w : GL (Fin N) k, z * w = w * z` using `fun w => ((Subgroup.mem_center_iff.1 hz) w).symm`. Establish `hmat : h = incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[e, diag_eq k N a g _ hg]`. Both sides reduce to the same expression. Set `p₁` to `σ (red k N m U)`. Set `p₂` to `σ (red k N m V)`.

Establish `hx : p₁⁻¹ * U ∈ (red k N m).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]`. Establish `hy : V * p₂⁻¹ ∈ (red k N m).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]`. Use `⟨f (red k N m U, red k N m V), (Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩, g, incl k N (p₁⁻¹ * U), ⟨_, hx, rfl⟩, incl k N (V * p₂⁻¹), ⟨_, hy, rfl⟩, z, hz, ?_⟩` and prove the remaining obligations.

Simplify using `only [f, map_mul, map_inv]`. Rewrite using `[hmat]`. Establish `hzV : ∀ w : GL (Fin N) k, w * z = z * w` using `fun w => (hzc w).symm`. Express the relevant statement in the definitionally equal form `incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V = incl k N p₁ * ((incl k N p₁)⁻¹ * incl k N U) * Zls.diagPow k N (Zls.lamOf g) * (incl k N V * (incl k N p₂)⁻¹) * incl k N p₂ * z`. Simplify using `only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]`.

Rewrite using `[hzc (incl k N V), mul_inv_cancel_left]`.
-/
theorem cartan_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m : ℕ), 1 ≤ m → 1 ≤ N → ∃ s : Finset (GL (Fin N) k × GL (Fin N) k), (∀ p ∈ s, p.1 ∈ KO k (Fin N) ∧ p.2 ∈ KO k (Fin N)) ∧ ∀ h : GL (Fin N) k, ∃ p ∈ s, ∃ g : Fin (N - 1) → ℕ, ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, ∃ z ∈ Subgroup.center (GL (Fin N) k), h = p.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.2 * z := by
  intro k _ _ _ _ N m _ hN
  classical
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI := finite_red k N m

  have hsec : ∀ u : GL (Fin N) 𝒪[k], ∃ w : GL (Fin N) 𝒪[k], red k N m w = red k N m u := fun u => ⟨u, rfl⟩
  let σ : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) → GL (Fin N) 𝒪[k] := fun c =>
    if hc : ∃ w, red k N m w = c then hc.choose else 1
  have hσ : ∀ u, red k N m (σ (red k N m u)) = red k N m u := fun u => by
    have hc : ∃ w, red k N m w = red k N m u := hsec u
    simp only [σ, dif_pos hc]
    exact hc.choose_spec
  let f : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) × GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) →
      GL (Fin N) k × GL (Fin N) k := fun c => (incl k N (σ c.1), incl k N (σ c.2))
  refine ⟨(Set.finite_range f).toFinset, ?_, fun h => ?_⟩
  · intro p hp
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hp
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · have hh : IsUnit (h : Matrix (Fin N) (Fin N) k).det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    obtain ⟨u, v, a, hu, hv, ha, e⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists 𝒪[k] k N (Zls.unif k)
      Zls.irreducible_unif (h : Matrix (Fin N) (Fin N) k) hh
    obtain ⟨g, hg⟩ := exists_lamOf N hN a ha
    let U : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit u hu
    let V : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit v hv
    let z : GL (Fin N) k := Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ a ⟨N - 1, by omega⟩)
    have hz : z ∈ Subgroup.center (GL (Fin N) k) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hzc : ∀ w : GL (Fin N) k, z * w = w * z := fun w => ((Subgroup.mem_center_iff.1 hz) w).symm
    have hmat : h = incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V := by
      apply Units.ext
      rw [e, diag_eq k N a g _ hg]
      rfl
    let p₁ := σ (red k N m U)
    let p₂ := σ (red k N m V)
    have hx : p₁⁻¹ * U ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have hy : V * p₂⁻¹ ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    refine ⟨f (red k N m U, red k N m V), (Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩, g,
      incl k N (p₁⁻¹ * U), ⟨_, hx, rfl⟩, incl k N (V * p₂⁻¹), ⟨_, hy, rfl⟩, z, hz, ?_⟩
    simp only [f, map_mul, map_inv]
    rw [hmat]
    have hzV : ∀ w : GL (Fin N) k, w * z = z * w := fun w => (hzc w).symm
    change incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V =
      incl k N p₁ * ((incl k N p₁)⁻¹ * incl k N U) * Zls.diagPow k N (Zls.lamOf g) *
        (incl k N V * (incl k N p₂)⁻¹) * incl k N p₂ * z
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [hzc (incl k N V), mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.Dblock.CartanCover
