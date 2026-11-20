import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Rewrite using `[← algebraMap_smul (Lsq K Δ) k m]`. Simplify using `only [herm, smul_mul_assoc, map_smul, smul_eq_mul, mul_zero, zero_mul, map_zero, add_zero, zero_add]`.
-/
private theorem splitM_lemma {K : Type} [Field K] {Δ τ : K} (c k : K) (m : EL Δ τ) (x y : Sp Δ τ) :
    herm c (k • m) x y = herm c m (x.1, 0) y + algebraMap K (Lsq K Δ) k * herm c m (0, x.2) y := by
  rw [← algebraMap_smul (Lsq K Δ) k m]
  simp only [herm, smul_mul_assoc, map_smul, smul_eq_mul, mul_zero, zero_mul, map_zero, add_zero, zero_add]

/- English proof (translation)
Simplify using `[herm]`.
-/
private theorem splitM_lemma_3 {K : Type} [Field K] {Δ τ : K} (c : K) (m : EL Δ τ) (y : Sp Δ τ) :
    herm c m (0, 0) y = 0 := by
  simp [herm]

/- English proof (translation)
Take `⟨-, -, h1, h2⟩` from `One.splitS O K Δ τ hl hτ hu c d m hd S hS`. Establish `h2' : ∀ x ∈ S, ((0 : Lsq K Δ), x.2) ∈ S` using `fun x hx => by`. Simplify `h2 x hx 1 (by simp) (by simp)` using `[ofE_one]`. Establish `e : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ε))`. Rewrite using `[← IsScalarTower.algebraMap_apply]`.

Conclude with `isIntegral_algebraMap`. Establish `ei : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ↑ε⁻¹))`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `isIntegral_algebraMap`. Use `⟨hS.fg, fun y => ?_, hS.stab⟩` and prove the remaining obligations.

Rewrite using `[hS.dual y]`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Rewrite using `[splitM_lemma]`. Conclude with `(hy _ (h1 x hx)).add (e.mul (hy _ (h2' x hx)))`.

Introduce `hy x hx`. Establish `a` using `hy _ (h1 x hx)`. Establish `b` using `hy _ (h2' x hx)`. Rewrite `a`, `b` using `[splitM_lemma]`. Simplify using `only [splitM_lemma_3, mul_zero, add_zero, zero_add] at a b`.

Establish `hm'` using `splitM_lemma c 1 m x y`. Rewrite `hm'` using `[one_smul, map_one, one_mul]`. Use `show IsIntegral O (herm c m x y)`. Rewrite using `[hm']`. Use `a.add ?_` and prove the remaining obligations.

Use `ei.mul b` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, one_mul]`. Then use the resulting hypothesis.
-/
private theorem splitM_lemma_2 (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] (Δ τ : K) (hl : IsLoc O Δ) (c : K) (d m : EL Δ τ) (hd : IsDat c d m)
    (hτ : τ ∈ (algebraMap O K).range) (hu : ∃ u : Oˣ, algebraMap O K u = 2 - τ) (ε : Oˣ)
    (S : Set (Sp Δ τ)) (hS : IsFix O c d m S) : IsFix O c d (algebraMap O K ε • m) S := by
  obtain ⟨-, -, h1, h2⟩ := One.splitS O K Δ τ hl hτ hu c d m hd S hS
  have h2' : ∀ x ∈ S, ((0 : Lsq K Δ), x.2) ∈ S := fun x hx => by
    simpa [ofE_one] using h2 x hx 1 (by simp) (by simp)
  have e : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ε)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have ei : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ↑ε⁻¹)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  refine ⟨hS.fg, fun y => ?_, hS.stab⟩
  rw [hS.dual y]
  constructor
  · intro hy x hx
    rw [splitM_lemma]
    exact (hy _ (h1 x hx)).add (e.mul (hy _ (h2' x hx)))
  · intro hy x hx
    have a := hy _ (h1 x hx)
    have b := hy _ (h2' x hx)
    rw [splitM_lemma] at a b
    simp only [splitM_lemma_3, mul_zero, add_zero, zero_add] at a b
    have hm' := splitM_lemma c 1 m x y
    rw [one_smul, map_one, one_mul] at hm'
    show IsIntegral O (herm c m x y)
    rw [hm']
    refine a.add ?_
    have := ei.mul b
    rwa [← mul_assoc, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, one_mul] at this

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hl c d m hd hτ hu ε`. Establish `hd' : IsDat c d (algebraMap O K ε • m)`. Simplify using `using datSmul K Δ τ c d m hd (Units.map (algebraMap O K).toMonoidHom ε)`. Establish `key : ∀ S, IsFix O c d (algebraMap O K ε • m) S ↔ IsFix O c d m S`. Introduce `S`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `splitM_lemma_2 O K Δ τ hl c d _ hd' hτ hu ε⁻¹ S h` as an intermediate fact. Rewrite `this` using `[smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]`. Then use the resulting hypothesis. Conclude with `splitM_lemma_2 O K Δ τ hl c d m hd hτ hu ε S`.

Unfold `lcount`. Use `congr 1`. Use function extensionality and compare the values at `S`. Distinguish the cases in `h : IsFix O c d m S`. Rewrite using `[if_pos ((key S).2 h), if_pos h]`.

Rewrite using `[if_neg (fun h' => h ((key S).1 h')), if_neg h]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.splitM : UpperTheory.V.Z.Sym.Loc.SplitM := by
  intro O K _ _ _ _ _ Δ τ hl c d m hd hτ hu ε
  have hd' : IsDat c d (algebraMap O K ε • m) := by
    simpa using datSmul K Δ τ c d m hd (Units.map (algebraMap O K).toMonoidHom ε)
  have key : ∀ S, IsFix O c d (algebraMap O K ε • m) S ↔ IsFix O c d m S := by
    intro S
    constructor
    · intro h
      have := splitM_lemma_2 O K Δ τ hl c d _ hd' hτ hu ε⁻¹ S h
      rwa [smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul] at this
    · exact splitM_lemma_2 O K Δ τ hl c d m hd hτ hu ε S
  unfold lcount
  congr 1
  funext S
  by_cases h : IsFix O c d m S
  · rw [if_pos ((key S).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((key S).1 h')), if_neg h]
