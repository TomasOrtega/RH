import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

namespace GlobalTheory

open Formalism.MainNotions.BlochKatoReduction Formalism.BasicNotions

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matAct, map_sum, map_smul]`.
-/
theorem matAct_comp_linear {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (f : M →ₗ[R] N)
    (v : Fin n → M) : matAct (M := N) A (fun i => f (v i)) = fun i => f (matAct (M := M) A v i) := by
  funext i
  simp [matAct, map_sum, map_smul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matAct, Matrix.mulVec, dotProduct]`.
-/
theorem matAct_self_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : matAct (M := R) A v = A.mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]`.
-/
private theorem matAct_fractionRing {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (v : Fin n → FractionRing O) :
    matAct (M := FractionRing O) A v = (A.map (algebraMap O (FractionRing O))).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]

/- English proof (translation)
Use `set B := A.map (algebraMap O (FractionRing O)) with hB`. Establish `hd : B.det = algebraMap O (FractionRing O) A.det`. Rewrite using `[hB, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hU : IsUnit B`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h`. Establish `hf : ⇑(matAct (M` using `FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)`. Rewrite using `[hf]`. Conclude with `⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩`.
-/
theorem matAct_fraction_bijective {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Function.Bijective (matAct (M := FractionRing O) A) := by
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = algebraMap O (FractionRing O) A.det := by
    rw [hB, RingHom.map_det]; rfl
  have hU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h
  have hf : ⇑(matAct (M := FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)
  rw [hf]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

/- English proof (translation)
Set `ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O)` to `(Algebra.linearMap O (FractionRing O)).compLeft (Fin n)`. Set `π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O)` to `(LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)`. Set `e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O)` to `LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)`. Establish `he : ∀ x, e x = matAct (M` using `FractionRing O) A x := fun x => rfl`. Establish `hAι : ∀ y, matAct (M` using `FractionRing O) A (ι y) = ι (A.mulVec y) := by`.

Introduce `y`. Establish `key` using `matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y`. Rewrite `key` using `[matAct_self_apply]`. Conclude with `key`. Establish `hAπ : ∀ x, matAct (M` using `KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) := fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x`.

Establish `hπι : ∀ y, π (ι y) = 0`. Introduce `y`. Use function extensionality and compare the values at `i`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩`. Establish `hιinj : Function.Injective ι`.

Introduce `a b hab`. Use function extensionality and compare the values at `i`. Conclude with `IsFractionRing.injective O (FractionRing O) (congrFun hab i)`. Establish `hlift : ∀ x, π x = 0 → ∃ y, ι y = x`. Introduce `x hx`.

Establish `hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i`. Introduce `i`. Take `⟨a, ha⟩` from `(Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)`. Conclude with `⟨a, ha⟩`. Use `choose y hy using hmem`.

Conclude with `⟨y, funext hy⟩`. Set `φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O)` to `π ∘ₗ e.symm.toLinearMap ∘ₗ ι`. Establish `hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M` using `KmodO O) A) := by`. Introduce `y`. Rewrite using `[LinearMap.mem_ker]`.

Use `show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0`. Rewrite using `[hAπ, ← he, e.apply_symm_apply, hπι]`. Set `φ` to `φ0.codRestrict _ hφ0`. Establish `hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y))` using `fun y => rfl`. Establish `hsurj : Function.Surjective φ`.

Introduce and unpack `⟨x, hx⟩`. Establish `hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i` using `fun i => Submodule.Quotient.mk_surjective _ (x i)`. Use `choose k hk using hpre`. Establish `hπk : π k = x` using `funext hk`. Take `⟨y, hy⟩` from `hlift (matAct (M := FractionRing O) A k) (by`.

Rewrite using `[← hAπ, hπk]`. Conclude with `hx)`. Use `⟨y, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, hy, ← he, e.symm_apply_apply, hπk]`. Establish `hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ`.

Use extensionality with `y`. Rewrite using `[LinearMap.mem_range, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]`. Both sides reduce to the same expression. Introduce `hy`. Establish `h0 : π (e.symm (ι y)) = 0`. Rewrite using `[← hφ, hy]`.

Both sides reduce to the same expression. Take `⟨z, hz⟩` from `hlift _ h0`. Use `⟨z, hιinj ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩`.
-/
theorem nonempty_coker_equiv_ker_matAct {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Nonempty (((Fin n → O) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[O]
      LinearMap.ker (matAct (M := KmodO O) A)) := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O) :=
    LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)
  have he : ∀ x, e x = matAct (M := FractionRing O) A x := fun x => rfl
  have hAι : ∀ y, matAct (M := FractionRing O) A (ι y) = ι (A.mulVec y) := by
    intro y
    have key := matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y
    rw [matAct_self_apply] at key
    exact key
  have hAπ : ∀ x, matAct (M := KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) :=
    fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x
  have hπι : ∀ y, π (ι y) = 0 := by
    intro y
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun hab i)
  have hlift : ∀ x, π x = 0 → ∃ y, ι y = x := by
    intro x hx
    have hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i := by
      intro i
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)
      exact ⟨a, ha⟩
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  let φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O) := π ∘ₗ e.symm.toLinearMap ∘ₗ ι
  have hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro y
    rw [LinearMap.mem_ker]
    show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0
    rw [hAπ, ← he, e.apply_symm_apply, hπι]
  let φ := φ0.codRestrict _ hφ0
  have hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y)) := fun y => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i :=
      fun i => Submodule.Quotient.mk_surjective _ (x i)
    choose k hk using hpre
    have hπk : π k = x := funext hk
    obtain ⟨y, hy⟩ := hlift (matAct (M := FractionRing O) A k) (by
      rw [← hAπ, hπk]
      exact hx)
    refine ⟨y, Subtype.ext ?_⟩
    rw [hφ, hy, ← he, e.symm_apply_apply, hπk]
  have hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      rw [hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]
      rfl
    · intro hy
      have h0 : π (e.symm (ι y)) = 0 := by
        rw [← hφ, hy]
        rfl
      obtain ⟨z, hz⟩ := hlift _ h0
      refine ⟨z, hιinj ?_⟩
      rw [Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hfl` using `Module.length_ne_top_iff.mp hne`. Establish `: IsNoetherian O (LinearMap.ker (matAct (M` using `KmodO O) A)) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1`. Use `set B := A.map (algebraMap O (FractionRing O)) with hB`. Establish `hd : B.det = 0`.

Rewrite using `[hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]`. Take `⟨v, hv0, hBv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hd`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by`. Assume the negation of the conclusion as `hh`. Conclude with `hv0 (funext fun i => by`.

Assume the negation of the conclusion as `hi`. Conclude with `hh ⟨i, hi⟩)`. Set `π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O)` to `(LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)`. Set `g0 : FractionRing O →ₗ[O] (Fin n → KmodO O)` to `π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))`. Establish `hg0 : ∀ t, g0 t = π (t • v)` using `fun t => rfl`.

Establish `hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M` using `KmodO O) A) := by`. Introduce `t`. Rewrite using `[LinearMap.mem_ker, hg0]`. Use `(matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_` and prove the remaining obligations. Rewrite using `[matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Set `g` to `g0.codRestrict _ hg0mem`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero`.

Establish `hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g`. Introduce and unpack `_ ⟨t, rfl⟩`. Establish `ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ)`. Rewrite using `[Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[ht, map_smul]`. Conclude with `Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩`. Establish `hbot` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)`. Use `set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht`. Establish `hgt : g t = 0`.

Establish `hm : g t ∈ LinearMap.range g` using `⟨t, rfl⟩`. Rewrite `hm` using `[hbot]`. Conclude with `(Submodule.mem_bot O).mp hm`. Establish `hcomp : π (t • v) i0 = 0`. Rewrite using `[← hg0]`.

Conclude with `congrFun (congrArg Subtype.val hgt) i0`. Take `⟨a, ha⟩` from `(Submodule.Quotient.mk_eq_zero _).1 hcomp`. Establish `ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1`. Establish `h1 : algebraMap O (FractionRing O) a = t * v i0` using `ha`. Rewrite using `[h1, ht]`.

Clear the denominators using the available nonvanishing facts. Rewrite `ha'` using `[← map_mul, ← map_one (algebraMap O (FractionRing O))]`. Establish `hmul : a * ϖ = 1` using `IsFractionRing.injective O (FractionRing O) ha'`. Establish `hunit : IsUnit ϖ` using `⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩`. Conclude with `hϖ.not_isUnit hunit`.
-/
theorem length_ker_matAct_eq_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (h : A.det = 0) :
    Module.length O (LinearMap.ker (matAct (M := KmodO O) A)) = ⊤ := by
  classical
  by_contra hne
  have hfl := Module.length_ne_top_iff.mp hne
  have : IsNoetherian O (LinearMap.ker (matAct (M := KmodO O) A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hh
    exact hv0 (funext fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let g0 : FractionRing O →ₗ[O] (Fin n → KmodO O) :=
    π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))
  have hg0 : ∀ t, g0 t = π (t • v) := fun t => rfl
  have hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro t
    rw [LinearMap.mem_ker, hg0]
    refine (matAct_comp_linear A
      (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_
    rw [matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]
    funext i
    simp
  let g := g0.codRestrict _ hg0mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g := by
    rintro _ ⟨t, rfl⟩
    have ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ) := by
      rw [Algebra.smul_def]
      field_simp
    rw [ht, map_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O)
    (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht
  have hgt : g t = 0 := by
    have hm : g t ∈ LinearMap.range g := ⟨t, rfl⟩
    rw [hbot] at hm
    exact (Submodule.mem_bot O).mp hm
  have hcomp : π (t • v) i0 = 0 := by
    rw [← hg0]
    exact congrFun (congrArg Subtype.val hgt) i0
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hcomp
  have ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1 := by
    have h1 : algebraMap O (FractionRing O) a = t * v i0 := ha
    rw [h1, ht]
    field_simp
  rw [← map_mul, ← map_one (algebraMap O (FractionRing O))] at ha'
  have hmul : a * ϖ = 1 := IsFractionRing.injective O (FractionRing O) ha'
  have hunit : IsUnit ϖ := ⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  exact hϖ.not_isUnit hunit

/- English proof (translation)
Introduce `O _ _ _ a Φ`. Distinguish the cases in `h : Φ.det = 0`. Rewrite using `[length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]`. Take `⟨e⟩` from `nonempty_coker_equiv_ker_matAct Φ h`. Rewrite using `[← e.length_eq]`.

Conclude with `RelativeLengthSpanDet.length_coker Φ`.
-/
theorem length_ker_matAct_kmod_eq_addVal_det :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : ℕ)
      (Φ : Matrix (Fin a) (Fin a) O),
      Module.length O (LinearMap.ker (Formalism.MainNotions.BlochKatoReduction.matAct (M := Formalism.BasicNotions.KmodO O) Φ)) =
        IsDiscreteValuationRing.addVal O Φ.det := by
  intro O _ _ _ a Φ
  by_cases h : Φ.det = 0
  · rw [length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨e⟩ := nonempty_coker_equiv_ker_matAct Φ h
    rw [← e.length_eq]
    exact RelativeLengthSpanDet.length_coker Φ

end GlobalTheory
