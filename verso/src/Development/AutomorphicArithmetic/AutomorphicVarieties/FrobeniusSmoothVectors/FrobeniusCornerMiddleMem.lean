import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMiddleTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `haveI : P.IsPrime := hP`. Use `haveI : Nontrivial (B ⧸ P) := inferInstance`. Use `haveI : IsCO O (B ⧸ P) := co_quot O B (B ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)`. Establish `hm : ∀ x ∈ maximalIdeal B, Ideal.Quotient.mk P x ∈ maximalIdeal (B ⧸ P)`. Introduce `x hx`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, hu⟩`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)`. Establish `hxy : x * y - 1 ∈ P`. Rewrite using `[← Ideal.Quotient.eq, map_mul, hy, ← hu]`.

Simplify using the standard rewrite rules. Establish `h2 : x * y - 1 ∈ maximalIdeal B` using `IsLocalRing.le_maximalIdeal hP.ne_top hxy`. Establish `h3 : x * y ∈ maximalIdeal B` using `Ideal.mul_mem_right _ _ hx`. Apply `(IsLocalRing.maximalIdeal.isMaximal B).ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Simplify using `using Ideal.sub_mem _ h3 h2`. Set `χ : F.G0 →* B ⧸ P` to `{ toFun := fun g => Ideal.Quotient.mk P (a g) map_one' := by simp [h1] map_mul' := fun g h => by`. Rewrite using `[← map_mul]`. Conclude with `Ideal.Quotient.eq.mpr (hmul g h) }`. Establish `hχ : ∀ g, χ g = Ideal.Quotient.mk P (a g)` using `fun g => rfl`.

Establish `key` using `frobenius_corner_middle_trivial hF (B ⧸ P) (fun c hc' => by`. Rewrite using `[IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hO c hc')`. Use `χ`. Use the proof step `(fun N => by`.

Establish `hle : ∀ x ∈ maximalIdeal B ^ N, Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N) (Ideal.Quotient.mk P x) = 0`. Introduce `x hx`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmap : Ideal.map (Ideal.Quotient.mk P) (maximalIdeal B) ≤ maximalIdeal (B ⧸ P)` using `Ideal.map_le_iff_le_comap.mpr hm`. Use `Ideal.pow_right_mono hmap N` as an intermediate fact.

Rewrite `this` using `[← Ideal.map_pow]`. Conclude with `this (Ideal.mem_map_of_mem _ hx)`. Set `f` to `Ideal.Quotient.lift (maximalIdeal B ^ N) ((Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N)).comp (Ideal.Quotient.mk P)) hle`. Use `(hc N).comp f using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Use the proof step `rfl)`. Use the proof step `(fun g => by`. Rewrite using `[hχ, ← map_one (Ideal.Quotient.mk P), ← map_sub]`. Conclude with `hm _ (hres g))`. Use the proof step `(fun g => by rw [hχ, hχ, hst g])`.

Use the proof step `(fun v g hg hΨ => by`. Rewrite using `[hχ, ← map_one (Ideal.Quotient.mk P)]`. Conclude with `Ideal.Quotient.eq.mpr (hloc v g hg hΨ))`. Use `g`. Rewrite `key` using `[hχ, ← map_one (Ideal.Quotient.mk P)]`.

Conclude with `Ideal.Quotient.eq.mp key`.
-/
private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (P : Ideal B) (hP : P.IsPrime) (a : F.G0 → B) (hO : ∀ c ∈ maximalIdeal O, algebraMap O B c ∈ P)
    (h1 : a 1 = 1) (hmul : ∀ g h, a (g * h) - a g * a h ∈ P) (hc : AdicCont (maximalIdeal B) a)
    (hres : ∀ g, a g - 1 ∈ maximalIdeal B) (hst : ∀ g, a (F.star g) = a g)
    (hloc : ∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → a (F.loc0 v g) - 1 ∈ P) (g : F.G0) : a g - 1 ∈ P := by
  haveI : P.IsPrime := hP
  haveI : Nontrivial (B ⧸ P) := inferInstance
  haveI : IsCO O (B ⧸ P) :=
    co_quot O B (B ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
  have hm : ∀ x ∈ maximalIdeal B, Ideal.Quotient.mk P x ∈ maximalIdeal (B ⧸ P) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have hxy : x * y - 1 ∈ P := by
      rw [← Ideal.Quotient.eq, map_mul, hy, ← hu]
      simp
    have h2 : x * y - 1 ∈ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top hxy
    have h3 : x * y ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hx
    apply (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Ideal.sub_mem _ h3 h2
  let χ : F.G0 →* B ⧸ P :=
    { toFun := fun g => Ideal.Quotient.mk P (a g)
      map_one' := by simp [h1]
      map_mul' := fun g h => by
        rw [← map_mul]
        exact Ideal.Quotient.eq.mpr (hmul g h) }
  have hχ : ∀ g, χ g = Ideal.Quotient.mk P (a g) := fun g => rfl
  have key := frobenius_corner_middle_trivial hF (B ⧸ P)
    (fun c hc' => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hO c hc')
    χ
    (fun N => by
      have hle : ∀ x ∈ maximalIdeal B ^ N,
          Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N) (Ideal.Quotient.mk P x) = 0 := by
        intro x hx
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have hmap : Ideal.map (Ideal.Quotient.mk P) (maximalIdeal B) ≤ maximalIdeal (B ⧸ P) :=
          Ideal.map_le_iff_le_comap.mpr hm
        have := Ideal.pow_right_mono hmap N
        rw [← Ideal.map_pow] at this
        exact this (Ideal.mem_map_of_mem _ hx)
      let f := Ideal.Quotient.lift (maximalIdeal B ^ N)
        ((Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N)).comp (Ideal.Quotient.mk P)) hle
      convert (hc N).comp f using 1
      funext x
      rfl)
    (fun g => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P), ← map_sub]
      exact hm _ (hres g))
    (fun g => by rw [hχ, hχ, hst g])
    (fun v g hg hΨ => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P)]
      exact Ideal.Quotient.eq.mpr (hloc v g hg hΨ))
    g
  rw [hχ, ← map_one (Ideal.Quotient.mk P)] at key
  exact Ideal.Quotient.eq.mp key

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hF S P hP hlam hmul hloc`. Take `⟨hB, hm⟩` from `UpperTheory.V.Fr.co_B hF (Or.inr rfl) S`. Take `⟨-, hc, -, -⟩` from `UpperTheory.V.Fr.cont_u hF (Or.inr rfl) S`. Take `⟨-, -, -, -, hst⟩` from `UpperTheory.V.Fr.star hF`. Establish `h1 : S.aB 1 1 = 1` using `Subtype.ext (by show S.ρ.r 1 1 1 = 1`.

Rewrite using `[map_one, Matrix.one_apply_eq])`. Use `aux hF S.B P hP (fun g => S.aB g 1) (fun c hc => hlam (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc))) h1 hmul (hm ▸ hc 1) (fun g => ?_) (fun g => Subtype.ext (hst S.ρ g 1 1)) (fun v g hg hΨ => ?_)` and prove the remaining obligations. Rewrite using `[hm] show S.ρ.r g 1 1 - 1 ∈ maximalIdeal S.R`. Rewrite using `[← res_eq_zero_iff O, map_sub, map_one, sub_eq_zero]`. Establish `h` using `S.lift.2.1.1 g 1`.

Establish `hw : w 3 1 = 0` using `rfl`. Rewrite `h` using `[hw, zpow_zero]`. Conclude with `h`. Establish `h2 : S.ψB v 1 g - 1 ∈ P` using `hlam (Ideal.mem_sup_right (Ideal.subset_span ⟨v, 1, g, hg, hΨ, rfl⟩))`. Establish `h3` using `P.add_mem (hloc v g) h2`.

Rewrite `h3` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Fr.frobenius_corner_middle_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (S : Space O F 3) (P : Ideal S.B), P.IsPrime → S.lamId ≤ P → (∀ g h, S.aB (g * h) 1 - S.aB g 1 * S.aB h 1 ∈ P) → (∀ v g, S.aB (F.loc0 v g) 1 - S.ψB v 1 g ∈ P) → ∀ g, S.aB g 1 - 1 ∈ P := by
  intro l _ O _ _ _ _ F C₀ hF S P hP hlam hmul hloc
  obtain ⟨hB, hm⟩ := UpperTheory.V.Fr.co_B hF (Or.inr rfl) S
  obtain ⟨-, hc, -, -⟩ := UpperTheory.V.Fr.cont_u hF (Or.inr rfl) S
  obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
  have h1 : S.aB 1 1 = 1 := Subtype.ext (by
    show S.ρ.r 1 1 1 = 1
    rw [map_one, Matrix.one_apply_eq])
  refine aux hF S.B P hP (fun g => S.aB g 1)
    (fun c hc => hlam (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc))) h1 hmul (hm ▸ hc 1) (fun g => ?_)
    (fun g => Subtype.ext (hst S.ρ g 1 1)) (fun v g hg hΨ => ?_)
  · rw [hm]
    show S.ρ.r g 1 1 - 1 ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O, map_sub, map_one, sub_eq_zero]
    have h := S.lift.2.1.1 g 1
    have hw : w 3 1 = 0 := rfl
    rw [hw, zpow_zero] at h
    exact h
  · have h2 : S.ψB v 1 g - 1 ∈ P :=
      hlam (Ideal.mem_sup_right (Ideal.subset_span ⟨v, 1, g, hg, hΨ, rfl⟩))
    have h3 := P.add_mem (hloc v g) h2
    rwa [sub_add_sub_cancel] at h3
