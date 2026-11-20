import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SplitM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `t ht x` and use `by rw [Units.val_mul, mul_smul] exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht`.
-/
private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L c d m h hτ hodd`. Take `⟨a, rfl⟩` from `hτ`. Establish `h2` using `L.two`. Establish `hu : IsUnit (2 - a)`. Assume the negation of the conclusion as `hn`.

Apply `hodd` to reduce the goal to its premises. Establish `hp : IsUnit (2 + a)`. Assume the negation of the conclusion as `hp`. Establish `hsum` using `IsLocalRing.nonunits_add hn hp`. Apply `hsum` to reduce the goal to its premises.

Establish `e : (2 - a) + (2 + a) = 2 * 2` using `by ring`. Rewrite using `[e]`. Conclude with `h2.mul h2`. Use `⟨hp.unit, 1, one_ne_zero, ?_⟩` and prove the remaining obligations. Simplify using `[map_add, map_ofNat]`.

Take `⟨v, hv⟩` from `hu`. Establish `hv' : algebraMap O K (v : O) = 2 - algebraMap O K a`. Rewrite using `[hv, map_sub, map_ofNat]`. Establish `hex : ∃ u : Oˣ, algebraMap O K ↑u = 2 - algebraMap O K a` using `⟨v, hv'⟩`. Use `⟨hex, ?_⟩` and prove the remaining obligations.

Establish `hD : ¬ EvenVal O (algebraMap O K a ^ 2 - 4)`. Introduce and unpack `⟨u, s, hs0, hus⟩`. Apply `hodd` to reduce the goal to its premises. Use `⟨-(u * v⁻¹), s, hs0, ?_⟩` and prove the remaining obligations. Establish `hw : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1`.

Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `hw` using `[hv']`. Simplify using `only [Units.val_neg, Units.val_mul, map_neg, map_mul]`. Take the linear combination `(-(algebraMap O K ((v⁻¹ : Oˣ) : O))) * hus + (-(2 + algebraMap O K a)) * hw`. Establish `hreg` using `h.reg`.

Take `⟨ε, hε⟩` from `ramUnit O K Δ L _ hreg hD`. Establish `hinv : ∀ t ∈ NE (algebraMap O K a), ∀ x : Kˣ, lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m)` using `fun t ht x => inv_norm L h t ht x`. Establish `hg : ((Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) = algebraMap O K ε` using `rfl`. Take `⟨_, h2', _⟩` from `sumShift O K Δ _ L hreg (fun y : Kˣ => lcount O c d ((y : K) • m)) hinv (Units.map (algebraMap O K : O →* K) ε)`. Establish `hshift : ∀ x : Kˣ, lcount O c d (((x * Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) • m) = lcount O c d ((x : K) • m)`.

Introduce `x`. Rewrite using `[Units.val_mul, hg, mul_comm, mul_smul]`. Conclude with `splitM O K Δ _ L c d _ (datSmul K Δ _ c d m h x) ⟨a, rfl⟩ hex ε`. Simplify using `only [hshift, hg, hε] at h2'`. Establish `h3 : kapSum O c d m = -1 * kapSum O c d m`.

Unfold `kapSum`. Conclude with `h2'`. Take the linear combination `h3 / 2`.
-/
theorem UpperTheory.V.Z.Sym.Loc.kapRam : UpperTheory.V.Z.Sym.Loc.KapRam := by
  intro O K _ _ _ _ _ Δ τ L c d m h hτ hodd
  obtain ⟨a, rfl⟩ := hτ
  have h2 := L.two
  have hu : IsUnit (2 - a) := by
    by_contra hn
    apply hodd
    have hp : IsUnit (2 + a) := by
      by_contra hp
      have hsum := IsLocalRing.nonunits_add hn hp
      apply hsum
      have e : (2 - a) + (2 + a) = 2 * 2 := by ring
      rw [e]
      exact h2.mul h2
    refine ⟨hp.unit, 1, one_ne_zero, ?_⟩
    simp [map_add, map_ofNat]
  obtain ⟨v, hv⟩ := hu
  have hv' : algebraMap O K (v : O) = 2 - algebraMap O K a := by
    rw [hv, map_sub, map_ofNat]
  have hex : ∃ u : Oˣ, algebraMap O K ↑u = 2 - algebraMap O K a := ⟨v, hv'⟩
  refine ⟨hex, ?_⟩
  have hD : ¬ EvenVal O (algebraMap O K a ^ 2 - 4) := by
    rintro ⟨u, s, hs0, hus⟩
    apply hodd
    refine ⟨-(u * v⁻¹), s, hs0, ?_⟩
    have hw : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv'] at hw
    simp only [Units.val_neg, Units.val_mul, map_neg, map_mul]
    linear_combination (-(algebraMap O K ((v⁻¹ : Oˣ) : O))) * hus + (-(2 + algebraMap O K a)) * hw
  have hreg := h.reg
  obtain ⟨ε, hε⟩ := ramUnit O K Δ L _ hreg hD
  have hinv : ∀ t ∈ NE (algebraMap O K a), ∀ x : Kˣ,
      lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) :=
    fun t ht x => inv_norm L h t ht x
  have hg : ((Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) = algebraMap O K ε := rfl
  obtain ⟨_, h2', _⟩ := sumShift O K Δ _ L hreg (fun y : Kˣ => lcount O c d ((y : K) • m)) hinv
    (Units.map (algebraMap O K : O →* K) ε)
  have hshift : ∀ x : Kˣ, lcount O c d (((x * Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) • m)
      = lcount O c d ((x : K) • m) := by
    intro x
    rw [Units.val_mul, hg, mul_comm, mul_smul]
    exact splitM O K Δ _ L c d _ (datSmul K Δ _ c d m h x) ⟨a, rfl⟩ hex ε
  simp only [hshift, hg, hε] at h2'
  have h3 : kapSum O c d m = -1 * kapSum O c d m := by
    unfold kapSum
    exact h2'
  linear_combination h3 / 2
