import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vcount

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish `key : ∀ X, (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (1 + x) * y ∈ S) ∧ X = cls τ S) ↔ (∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S)`. Introduce `X`. Apply `exists_congr` to reduce the goal to its premises. Introduce `S`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hL, hst, hX⟩`. Use `⟨hL, ?_, hX⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hL.fg`. Introduce `y hy`. Establish `h1` using `hst y hy`.

Rewrite `h1`, `hy`, the goal using `[SetLike.mem_coe]`. Establish `h2` using `(Submodule.span O (s : Set (Etau K τ))).sub_mem h1 hy`. Simplify `h2` using `[add_mul]`. Introduce and unpack `⟨hL, hst, hX⟩`. Use `⟨hL, ?_, hX⟩` and prove the remaining obligations.

Take `⟨s, rfl⟩` from `hL.fg`. Introduce `y hy`. Establish `h1` using `hst y hy`. Rewrite `h1`, `hy`, the goal using `[SetLike.mem_coe]`. Rewrite using `[add_mul, one_mul]`.

Conclude with `(Submodule.span O (s : Set (Etau K τ))).add_mem hy h1`. Unfold `vcount`. Use `congr 1`. Use function extensionality and compare the values at `X`. Use `split_ifs with h1 h2 h2`.

Both sides reduce to the same expression. Conclude with `absurd ((key X).1 h1) h2`. Conclude with `absurd ((key X).2 h2) h1`. Both sides reduce to the same expression.
-/
private theorem vcount_one_add {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (x : Etau K τ) :
    vcount O τ (1 + x) = vcount O τ x := by
  have key : ∀ X, (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (1 + x) * y ∈ S) ∧ X = cls τ S) ↔
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) := by
    intro X
    apply exists_congr
    intro S
    constructor
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      have h2 := (Submodule.span O (s : Set (Etau K τ))).sub_mem h1 hy
      simpa [add_mul] using h2
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      rw [add_mul, one_mul]
      exact (Submodule.span O (s : Set (Etau K τ))).add_mem hy h1
  unfold vcount
  congr 1
  funext X
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((key X).1 h1) h2
  · exact absurd ((key X).2 h2) h1
  · rfl

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ hτO j χ hj hχ a ha z hz`. Take `⟨o, ho⟩` from `hτO`. Establish `hna : QuadraticAlgebra.norm (a : Etau K τ) = 1`. Rewrite using `[ha]`. Simplify using `[QuadraticAlgebra.norm]`.

Establish `hnz : QuadraticAlgebra.norm (z : Etau K τ) = 2 + τ`. Rewrite using `[hz]`. Simplify using `[QuadraticAlgebra.norm]`. Expand and normalize the polynomial expressions, which then agree. Establish `gA : gOrb O j χ a = vcount O τ a`.

Establish `h1` using `gLat O K Δ τ L hτ j χ hj hχ a 1 1 (by rw [hna]; simp)`. Simplify using `using h1`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu⟩`. Establish `gZ` using `gLat O K Δ τ L hτ j χ hj hχ z 1 u (by rw [hnz, hu]; simp)`.

Simplify using `only [map_one, Units.val_one, inv_one, one_mul, one_smul] at gZ`. Rewrite using `[gA, gZ, hz, ← ha, vcount_one_add]`. Introduce and unpack `⟨u, hu⟩`. Rewrite using `[gA, ha]`. Apply `vMax O K Δ τ L hτ` to reduce the goal to its premises.

Conclude with `⟨o, by rw [ho]; simp [trace]⟩`. Conclude with `⟨1, by simp [QuadraticAlgebra.norm]⟩`. Conclude with `⟨u, by rw [hu]; simp⟩`. Introduce and unpack `⟨u, hu⟩ s ε hs`. Establish `gZ` using `gLat O K Δ τ L hτ j χ hj hχ z s ε (by rw [hnz, hs])`.

Use `haveI := L.frac`. Establish `hsO : ∃ c : O, algebraMap O K c = (s : K)`. Establish `hint : IsIntegral O ((s : K) ^ 2)`. Establish `: (s : K) ^ 2 = algebraMap O K (((ε⁻¹ : Oˣ) : O) * (2 + o))`. Establish `hinv : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite using `[map_mul, map_add, map_ofNat, ho]`. Take the linear combination `(-(algebraMap O K ((ε⁻¹ : Oˣ) : O))) * hs - (s : K) ^ 2 * hinv`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos hint)`. Take `⟨c, hc⟩` from `hsO`. Establish `hs0` using `s.ne_zero`. Establish `hv : vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ)) = 1`. Apply `vMax O K Δ τ L hτ` to reduce the goal to its premises.

Use `⟨ε * c, ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Simplify using `[trace]`. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-hs`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Simplify using `[QuadraticAlgebra.norm]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-hs`. Use `⟨-(ε * u), ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[hu]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(2 - τ) * hs`. Rewrite using `[gZ, hv, mul_one]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.gVals : UpperTheory.V.Z.Sym.Loc.GVals := by
  intro O K _ _ _ _ _ Δ τ L hτ hτO j χ hj hχ a ha z hz
  obtain ⟨o, ho⟩ := hτO
  have hna : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha]
    simp [QuadraticAlgebra.norm]
  have hnz : QuadraticAlgebra.norm (z : Etau K τ) = 2 + τ := by
    rw [hz]
    simp [QuadraticAlgebra.norm]
    ring
  have gA : gOrb O j χ a = vcount O τ a := by
    have h1 := gLat O K Δ τ L hτ j χ hj hχ a 1 1 (by rw [hna]; simp)
    simpa using h1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z 1 u (by rw [hnz, hu]; simp)
    simp only [map_one, Units.val_one, inv_one, one_mul, one_smul] at gZ
    rw [gA, gZ, hz, ← ha, vcount_one_add]
  · rintro ⟨u, hu⟩
    rw [gA, ha]
    apply vMax O K Δ τ L hτ
    · exact ⟨o, by rw [ho]; simp [trace]⟩
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · exact ⟨u, by rw [hu]; simp⟩
  · rintro ⟨u, hu⟩ s ε hs
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z s ε (by rw [hnz, hs])
    haveI := L.frac
    have hsO : ∃ c : O, algebraMap O K c = (s : K) := by
      have hint : IsIntegral O ((s : K) ^ 2) := by
        have : (s : K) ^ 2 = algebraMap O K (((ε⁻¹ : Oˣ) : O) * (2 + o)) := by
          have hinv : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [map_mul, map_add, map_ofNat, ho]
          linear_combination (-(algebraMap O K ((ε⁻¹ : Oˣ) : O))) * hs - (s : K) ^ 2 * hinv
        rw [this]
        exact isIntegral_algebraMap
      exact IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos hint)
    obtain ⟨c, hc⟩ := hsO
    have hs0 := s.ne_zero
    have hv : vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ)) = 1 := by
      apply vMax O K Δ τ L hτ
      · refine ⟨ε * c, ?_⟩
        rw [hz]
        simp [trace]
        rw [hc]
        field_simp
        linear_combination -hs
      · refine ⟨ε, ?_⟩
        rw [hz]
        simp [QuadraticAlgebra.norm]
        field_simp
        linear_combination -hs
      · refine ⟨-(ε * u), ?_⟩
        rw [hz]
        simp
        rw [hu]
        field_simp
        linear_combination (2 - τ) * hs
    rw [gZ, hv, mul_one]
