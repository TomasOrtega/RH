import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped nonZeroDivisors

namespace GlobalTheory.LatVecPair

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr h)]`. Prove the components needed by the constructor for the conclusion. Introduce `H t ht`. Take `⟨x, hx⟩` from `(FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mp (H _ (FractionalIdeal.mem_coeIdeal_of_mem (S := (𝓞 E)⁰) (P := E) ht))`. Conclude with `RingHom.mem_range.mpr ⟨x, by rw [hx, mul_comm]⟩`.

Introduce `H y hy`. Take `⟨t, ht, rfl⟩` from `(FractionalIdeal.mem_coeIdeal (S := (𝓞 E)⁰)).mp hy`. Take `⟨x, hx⟩` from `RingHom.mem_range.mp (H t ht)`. Conclude with `(FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mpr ⟨x, by rw [hx, mul_comm]⟩`.
-/
theorem mem_inv_coe_iff {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ≠ ⊥) (c : E) :
    c ∈ ((𝔞 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔ ∀ t ∈ 𝔞, (t : E) * c ∈ (algebraMap (𝓞 E) E).range := by
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr h)]
  constructor
  · intro H t ht
    obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mp
      (H _ (FractionalIdeal.mem_coeIdeal_of_mem (S := (𝓞 E)⁰) (P := E) ht))
    exact RingHom.mem_range.mpr ⟨x, by rw [hx, mul_comm]⟩
  · intro H y hy
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (𝓞 E)⁰)).mp hy
    obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H t ht)
    exact (FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mpr ⟨x, by rw [hx, mul_comm]⟩

/- English proof (translation)
Establish `h' : ((𝔞 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ = ((𝔟 : FractionalIdeal (𝓞 E)⁰ E))⁻¹`. Use extensionality with `c`. Rewrite using `[mem_inv_coe_iff ha, mem_inv_coe_iff hb]`. Conclude with `(h c).symm`. Conclude with `FractionalIdeal.coeIdeal_injective (inv_inj.mp h')`.
-/
theorem ideal_eq_of_inv {𝔞 𝔟 : Ideal (𝓞 E)} (ha : 𝔞 ≠ ⊥) (hb : 𝔟 ≠ ⊥)
    (h : ∀ c : E, (∀ t ∈ 𝔟, (t : E) * c ∈ (algebraMap (𝓞 E) E).range) ↔
      ∀ t ∈ 𝔞, (t : E) * c ∈ (algebraMap (𝓞 E) E).range) : 𝔞 = 𝔟 := by
  have h' : ((𝔞 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ = ((𝔟 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    ext c
    rw [mem_inv_coe_iff ha, mem_inv_coe_iff hb]
    exact (h c).symm
  exact FractionalIdeal.coeIdeal_injective (inv_inj.mp h')

/- English proof (translation)
Set `C : FractionalIdeal (𝓞 E)⁰ E` to `⟨𝔠, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hC1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ C`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mp hx`. Use `show algebraMap (𝓞 E) E y ∈ 𝔠`.

Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `𝔠.smul_mem y h1`. Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Introduce `h0`. Establish `h1m : (1 : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)` using `(FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mpr ⟨1, map_one _⟩`.

Rewrite `h1m` using `[h0]`. Conclude with `one_ne_zero ((FractionalIdeal.mem_zero_iff (S := (𝓞 E)⁰)).mp h1m)`. Establish `hC0 : C ≠ 0`. Introduce `h0`. Rewrite `hC1` using `[h0, FractionalIdeal.le_zero_iff]`.

Conclude with `h10 hC1`. Establish `hle : C⁻¹ ≤ 1`. Simplify using `using FractionalIdeal.inv_anti_mono h10 hC0 hC1`. Take `⟨𝔞, h𝔞⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle`. Establish `ha : 𝔞 ≠ ⊥`.

Introduce and unpack `rfl`. Rewrite `h𝔞` using `[FractionalIdeal.coeIdeal_bot]`. Conclude with `hC0 (inv_eq_zero.mp h𝔞.symm)`. Use `⟨𝔞, ha, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_inv_coe_iff ha, h𝔞, inv_inv]`.

Conclude with `Iff.rfl`.
-/
theorem exists_ideal_inv (𝔠 : Submodule (𝓞 E) E) (hfg : 𝔠.FG) (h1 : (1 : E) ∈ 𝔠) :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ ∀ c : E, (∀ t ∈ 𝔞, (t : E) * c ∈ (algebraMap (𝓞 E) E).range) ↔ c ∈ 𝔠 := by
  let C : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔠, FractionalIdeal.isFractional_of_fg hfg⟩
  have hC1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ C := by
    intro x hx
    obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mp hx
    show algebraMap (𝓞 E) E y ∈ 𝔠
    rw [Algebra.algebraMap_eq_smul_one]
    exact 𝔠.smul_mem y h1
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    intro h0
    have h1m : (1 : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
      (FractionalIdeal.mem_one_iff (S := (𝓞 E)⁰)).mpr ⟨1, map_one _⟩
    rw [h0] at h1m
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff (S := (𝓞 E)⁰)).mp h1m)
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, FractionalIdeal.le_zero_iff] at hC1
    exact h10 hC1
  have hle : C⁻¹ ≤ 1 := by
    simpa using FractionalIdeal.inv_anti_mono h10 hC0 hC1
  obtain ⟨𝔞, h𝔞⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have ha : 𝔞 ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot] at h𝔞
    exact hC0 (inv_eq_zero.mp h𝔞.symm)
  refine ⟨𝔞, ha, fun c => ?_⟩
  rw [← mem_inv_coe_iff ha, h𝔞, inv_inv]
  exact Iff.rfl

omit [NumberField E] in
/- English proof (translation)
Use `⟨⟨LinearMap.toMatrix' (e : (Fin n → E) →ₗ[E] (Fin n → E)), LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin n → E)), ?_, ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]`. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]`. Conclude with `LinearMap.toMatrix'_mulVec _ y`.
-/
theorem exists_GL_of_equiv {n : ℕ} (e : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ γ : GL (Fin n) E, ∀ y, (γ : Matrix (Fin n) (Fin n) E) *ᵥ y = e y := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → E) →ₗ[E] (Fin n → E)),
      LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin n → E)), ?_, ?_⟩, fun y => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · exact LinearMap.toMatrix'_mulVec _ y

omit [NumberField E] in
/- English proof (translation)
Establish `h0 : (Pi.single 0 1 : Fin (k + 1) → E) ≠ 0`. Introduce `h`. Use `congrFun h 0` as an intermediate fact. Simplify using `at this`. Set `f : (E ∙ x) ≃ₗ[E] (E ∙ (Pi.single 0 1 : Fin (k + 1) → E))` to `(LinearEquiv.toSpanNonzeroSingleton E _ x hx).symm.trans (LinearEquiv.toSpanNonzeroSingleton E _ _ h0)`.

Take `⟨g, hg⟩` from `Submodule.exists_linearEquiv_restrict_eq f`. Establish `h1 : (LinearEquiv.toSpanNonzeroSingleton E _ x hx).symm ⟨x, Submodule.mem_span_singleton_self x⟩ = 1`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]`. Use `⟨g, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, LinearEquiv.toSpanNonzeroSingleton_one]`.
-/
theorem exists_equiv_single {k : ℕ} (x : Fin (k + 1) → E) (hx : x ≠ 0) :
    ∃ e : (Fin (k + 1) → E) ≃ₗ[E] (Fin (k + 1) → E), e x = Pi.single 0 1 := by
  have h0 : (Pi.single 0 1 : Fin (k + 1) → E) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  let f : (E ∙ x) ≃ₗ[E] (E ∙ (Pi.single 0 1 : Fin (k + 1) → E)) :=
    (LinearEquiv.toSpanNonzeroSingleton E _ x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton E _ _ h0)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : (LinearEquiv.toSpanNonzeroSingleton E _ x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨g, ?_⟩
  calc g x = f ⟨x, Submodule.mem_span_singleton_self x⟩ :=
      (hg ⟨x, Submodule.mem_span_singleton_self x⟩).symm
    _ = Pi.single 0 1 := by
      show ((LinearEquiv.toSpanNonzeroSingleton E _ _ h0)
        ((LinearEquiv.toSpanNonzeroSingleton E _ x hx).symm ⟨x, _⟩) : Fin (k + 1) → E) = _
      rw [h1, LinearEquiv.toSpanNonzeroSingleton_one]

/- English proof (translation)
Take `⟨b, hbL, hbspan, hbli⟩` from `exists_linearIndependent E (L : Set (Fin k → E))`. Establish `hsp : ⊤ ≤ Submodule.span E (Set.range ((↑) : b → Fin k → E))`. Rewrite using `[Subtype.range_coe, hbspan, hL.span_eq_top]`. Use `set B := Module.Basis.mk hbli hsp with hB`. Establish `hBi : ∀ i, B i = (i : Fin k → E)` using `fun i => Module.Basis.mk_apply _ _ _`.

Establish `: Finite b` using `Module.Finite.finite_basis B`. Set `: Fintype b` to `Fintype.ofFinite _`. Use `⟨B.constr E (fun i => l ⟨i.1, hbL i.2⟩), fun z => ?_⟩` and prove the remaining obligations. Take `⟨⟨d, hd⟩, hdint⟩` from `IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ (fun i => B.repr z i)`. Establish `hall : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = d • B.repr z i` using `fun i => RingHom.mem_rangeS.mp (hdint i (Finset.mem_univ i))`.

Use `choose a ha using hall`. Establish `hdz : (d • z : L) = ∑ i, a i • (⟨i.1, hbL i.2⟩ : L)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, ← B.sum_repr z, Finset.smul_sum, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.coe_smul, ← algebraMap_smul E (a i), ha, smul_assoc, hBi]`. Establish `key : d • (B.constr E (fun i => l ⟨i.1, hbL i.2⟩) z) = d • l z`. Rewrite using `[← l.map_smul, hdz, map_sum, Module.Basis.constr_apply_fintype, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[l.map_smul, Module.Basis.equivFun_apply, ← algebraMap_smul E (a i), ha, smul_assoc]`.

Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Conclude with `smul_right_injective E hd0 key`.
-/
theorem exists_extend {k : ℕ} (L : Submodule (𝓞 E) (Fin k → E)) (hL : Submodule.IsLattice E L)
    (l : L →ₗ[𝓞 E] E) : ∃ f : (Fin k → E) →ₗ[E] E, ∀ z : L, f z = l z := by
  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent E (L : Set (Fin k → E))
  have hsp : ⊤ ≤ Submodule.span E (Set.range ((↑) : b → Fin k → E)) := by
    rw [Subtype.range_coe, hbspan, hL.span_eq_top]
  set B := Module.Basis.mk hbli hsp with hB
  have hBi : ∀ i, B i = (i : Fin k → E) := fun i => Module.Basis.mk_apply _ _ _
  have : Finite b := Module.Finite.finite_basis B
  let : Fintype b := Fintype.ofFinite _
  refine ⟨B.constr E (fun i => l ⟨i.1, hbL i.2⟩), fun z => ?_⟩
  obtain ⟨⟨d, hd⟩, hdint⟩ :=
    IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ (fun i => B.repr z i)
  have hall : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = d • B.repr z i := fun i =>
    RingHom.mem_rangeS.mp (hdint i (Finset.mem_univ i))
  choose a ha using hall
  have hdz : (d • z : L) = ∑ i, a i • (⟨i.1, hbL i.2⟩ : L) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, ← B.sum_repr z, Finset.smul_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha, smul_assoc, hBi]
  have key : d • (B.constr E (fun i => l ⟨i.1, hbL i.2⟩) z) = d • l z := by
    rw [← l.map_smul, hdz, map_sum, Module.Basis.constr_apply_fintype, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [l.map_smul, Module.Basis.equivFun_apply, ← algebraMap_smul E (a i), ha, smul_assoc]
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  exact smul_right_injective E hd0 key

/- English proof (translation)
Set `T : Λ →ₗ[𝓞 E] L` to `{ toFun := fun y => ⟨Fin.tail (y : Fin (k + 1) → E), (h _).mpr ⟨y, y.2, rfl⟩⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hT : Function.Surjective T`. Introduce and unpack `⟨z, hz⟩`. Take `⟨y, hy, rfl⟩` from `(h z).mp hz`. Conclude with `⟨⟨y, hy⟩, rfl⟩`.

Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.mpr hL.fg`. Establish `: Module.FinitePresentation (𝓞 E) L` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) L` using `Module.Flat.projective_of_finitePresentation`. Take `⟨s, hs⟩` from `Module.projective_lifting_property T LinearMap.id hT`. Set `l : L →ₗ[𝓞 E] E` to `(LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (k + 1) => E) 0).comp (Λ.subtype.comp s)`.

Take `⟨f, hf⟩` from `exists_extend L hL l`. Use `⟨f, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hsz : T (s ⟨z, hz⟩) = ⟨z, hz⟩` using `LinearMap.congr_fun hs ⟨z, hz⟩`. Establish `e1 : f z = ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E) 0` using `hf ⟨z, hz⟩`. Establish `e2 : Fin.tail ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E) = z` using `congrArg Subtype.val hsz`.

Use `Fin.cons_self_tail ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E)` as an intermediate fact. Rewrite `this` using `[e2, ← e1]`. Rewrite using `[this]`. Conclude with `(s ⟨z, hz⟩).2`.
-/
theorem exists_section {k : ℕ} (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (L : Submodule (𝓞 E) (Fin k → E))
    (hL : Submodule.IsLattice E L) (h : ∀ z, z ∈ L ↔ ∃ y ∈ Λ, Fin.tail y = z) :
    ∃ f : (Fin k → E) →ₗ[E] E, ∀ z ∈ L, (Fin.cons (f z) z : Fin (k + 1) → E) ∈ Λ := by
  let T : Λ →ₗ[𝓞 E] L :=
    { toFun := fun y => ⟨Fin.tail (y : Fin (k + 1) → E), (h _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Surjective T := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := (h z).mp hz
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.fg
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T LinearMap.id hT
  let l : L →ₗ[𝓞 E] E :=
    (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (k + 1) => E) 0).comp (Λ.subtype.comp s)
  obtain ⟨f, hf⟩ := exists_extend L hL l
  refine ⟨f, fun z hz => ?_⟩
  have hsz : T (s ⟨z, hz⟩) = ⟨z, hz⟩ := LinearMap.congr_fun hs ⟨z, hz⟩
  have e1 : f z = ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E) 0 := hf ⟨z, hz⟩
  have e2 : Fin.tail ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E) = z := congrArg Subtype.val hsz
  have := Fin.cons_self_tail ((s ⟨z, hz⟩ : Λ) : Fin (k + 1) → E)
  rw [e2, ← e1] at this
  rw [this]
  exact (s ⟨z, hz⟩).2

/- English proof (translation)
Use `⟨hΛ.fg.map _, ?_⟩` and prove the remaining obligations. Establish `hc : ((Λ.map (f.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin m → E)) : Set (Fin m → E)) = f '' (Λ : Set (Fin n → E))` using `Submodule.map_coe _ _`. Rewrite using `[hc, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hf]`.
-/
theorem isLattice_map {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (f : (Fin n → E) →ₗ[E] (Fin m → E)) (hf : Function.Surjective f) :
    Submodule.IsLattice E (Λ.map (f.restrictScalars (𝓞 E))) := by
  refine ⟨hΛ.fg.map _, ?_⟩
  have hc : ((Λ.map (f.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin m → E)) : Set (Fin m → E)) =
      f '' (Λ : Set (Fin n → E)) := Submodule.map_coe _ _
  rw [hc, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

def consZero (k : ℕ) : (Fin k → E) →ₗ[E] (Fin (k + 1) → E) where
  toFun z := Fin.cons 0 z
  map_add' a b := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c a := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem consZero_apply {k : ℕ} (z : Fin k → E) : consZero k z = Fin.cons 0 z := rfl

omit [NumberField E] in
/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero_apply]`.
-/
theorem cons_eq {k : ℕ} (c : E) (z : Fin k → E) :
    (Fin.cons c z : Fin (k + 1) → E) = Pi.single 0 c + consZero k z := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero_apply]

/- English proof (translation)
Establish `hzero : ∀ z ∈ L, consZero k z ∈ Λ` using `fun z hz => (h _).mpr ⟨fun t _ => RingHom.mem_range.mpr ⟨0, by simp [consZero_apply]⟩, by simpa [consZero_apply] using hz⟩`. Establish `htail0 : ∀ c : E, Fin.tail (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) = 0` using `fun c =>`. Use function extensionality and compare the values at `fun j => by show (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) j.succ = 0`. Conclude with `Pi.single_eq_of_ne (Fin.succ_ne_zero j) c`. Establish `h1 : (Pi.single 0 1 : Fin (k + 1) → E) ∈ Λ` using `(h _).mpr ⟨fun t _ => RingHom.mem_range.mpr ⟨t, by rw [Pi.single_eq_same, mul_one]⟩, by rw [htail0]; exact L.zero_mem⟩`.

Use `⟨⟨?_, ?_⟩, h1⟩` and prove the remaining obligations. Set `C : Submodule (𝓞 E) E` to `(((𝔞 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ : FractionalIdeal (𝓞 E)⁰ E)`. Establish `hCfg : C.FG` using `FractionalIdeal.fg_of_isUnit _ (isUnit_iff_ne_zero.mpr (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr ha)))`. Set `φ : (E × (Fin k → E)) →ₗ[𝓞 E] (Fin (k + 1) → E)` to `((LinearMap.single E (fun _ : Fin (k + 1) => E) 0).coprod (consZero k)).restrictScalars (𝓞 E)`. Establish `hΛeq : Λ = (C.prod L).map φ`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨hy0, hyt⟩` from `(h y).mp hy`. Use `⟨(y 0, Fin.tail y), ⟨(mem_inv_coe_iff ha _).mpr hy0, hyt⟩, ?_⟩` and prove the remaining obligations.

Use `show Pi.single 0 (y 0) + consZero k (Fin.tail y) = y`. Rewrite using `[← cons_eq, Fin.cons_self_tail]`. Introduce and unpack `⟨⟨c, z⟩, ⟨hc, hz⟩, rfl⟩ show Pi.single 0 c + consZero k z ∈ Λ`. Rewrite using `[← cons_eq]`. Conclude with `(h _).mpr ⟨by simpa using (mem_inv_coe_iff ha c).mp hc, by simpa using hz⟩`.

Rewrite using `[hΛeq]`. Conclude with `(hCfg.prod hL.fg).map φ`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Rewrite using `[← Fin.cons_self_tail y, cons_eq]`.

Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `hs : (Pi.single 0 (y 0) : Fin (k + 1) → E) = y 0 • Pi.single 0 1`. Use extensionality with `j`. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hj]`. Rewrite using `[hs]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`. Establish `hy : Fin.tail y ∈ Submodule.span E (L : Set (Fin k → E))`.

Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `hmap : (Submodule.span E (L : Set (Fin k → E))).map (consZero k) ≤ Submodule.span E (Λ : Set (Fin (k + 1) → E))`. Rewrite using `[Submodule.map_span_le]`. Introduce `z hz`.

Conclude with `Submodule.subset_span (hzero z hz)`. Conclude with `hmap ⟨_, hy, rfl⟩`.
-/
theorem isLattice_sum {k : ℕ} (𝔞 : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin k → E))
    (Λ : Submodule (𝓞 E) (Fin (k + 1) → E))
    (h : ∀ y, y ∈ Λ ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ L)
    (ha : 𝔞 ≠ ⊥) (hL : Submodule.IsLattice E L) : Submodule.IsLattice E Λ ∧ Pi.single 0 1 ∈ Λ := by
  have hzero : ∀ z ∈ L, consZero k z ∈ Λ := fun z hz =>
    (h _).mpr ⟨fun t _ => RingHom.mem_range.mpr ⟨0, by simp [consZero_apply]⟩,
      by simpa [consZero_apply] using hz⟩
  have htail0 : ∀ c : E, Fin.tail (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) = 0 := fun c =>
    funext fun j => by
      show (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) j.succ = 0
      exact Pi.single_eq_of_ne (Fin.succ_ne_zero j) c
  have h1 : (Pi.single 0 1 : Fin (k + 1) → E) ∈ Λ :=
    (h _).mpr ⟨fun t _ => RingHom.mem_range.mpr ⟨t, by rw [Pi.single_eq_same, mul_one]⟩,
      by rw [htail0]; exact L.zero_mem⟩
  refine ⟨⟨?_, ?_⟩, h1⟩
  · let C : Submodule (𝓞 E) E :=
      (((𝔞 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ : FractionalIdeal (𝓞 E)⁰ E)
    have hCfg : C.FG := FractionalIdeal.fg_of_isUnit _
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr ha)))
    let φ : (E × (Fin k → E)) →ₗ[𝓞 E] (Fin (k + 1) → E) :=
      ((LinearMap.single E (fun _ : Fin (k + 1) => E) 0).coprod (consZero k)).restrictScalars (𝓞 E)
    have hΛeq : Λ = (C.prod L).map φ := by
      ext y
      constructor
      · intro hy
        obtain ⟨hy0, hyt⟩ := (h y).mp hy
        refine ⟨(y 0, Fin.tail y), ⟨(mem_inv_coe_iff ha _).mpr hy0, hyt⟩, ?_⟩
        show Pi.single 0 (y 0) + consZero k (Fin.tail y) = y
        rw [← cons_eq, Fin.cons_self_tail]
      · rintro ⟨⟨c, z⟩, ⟨hc, hz⟩, rfl⟩
        show Pi.single 0 c + consZero k z ∈ Λ
        rw [← cons_eq]
        exact (h _).mpr ⟨by simpa using (mem_inv_coe_iff ha c).mp hc, by simpa using hz⟩
    rw [hΛeq]
    exact (hCfg.prod hL.fg).map φ
  · rw [eq_top_iff]
    intro y _
    rw [← Fin.cons_self_tail y, cons_eq]
    refine Submodule.add_mem _ ?_ ?_
    · have hs : (Pi.single 0 (y 0) : Fin (k + 1) → E) = y 0 • Pi.single 0 1 := by
        ext j
        by_cases hj : j = 0
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    · have hy : Fin.tail y ∈ Submodule.span E (L : Set (Fin k → E)) := by
        rw [hL.span_eq_top]
        trivial
      have hmap : (Submodule.span E (L : Set (Fin k → E))).map (consZero k) ≤
          Submodule.span E (Λ : Set (Fin (k + 1) → E)) := by
        rw [Submodule.map_span_le]
        intro z hz
        exact Submodule.subset_span (hzero z hz)
      exact hmap ⟨_, hy, rfl⟩

/- English proof (translation)
Set `tl : (Fin (k + 1) → E) →ₗ[E] (Fin k → E)` to `LinearMap.funLeft E E Fin.succ`. Set `L : Submodule (𝓞 E) (Fin k → E)` to `Λ.map (tl.restrictScalars (𝓞 E))`. Establish `hL : Submodule.IsLattice E L` using `isLattice_map Λ hΛ tl (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective k))`. Establish `hLmem : ∀ z, z ∈ L ↔ ∃ y ∈ Λ, Fin.tail y = z` using `fun z => by`. Rewrite using `[Submodule.mem_map]`.

Both sides reduce to the same expression. Take `⟨f, hf⟩` from `exists_section Λ L hL hLmem`. Establish `htail0 : ∀ c : E, Fin.tail (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) = 0` using `fun c =>`. Use function extensionality and compare the values at `fun j => by show (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) j.succ = 0`. Conclude with `Pi.single_eq_of_ne (Fin.succ_ne_zero j) c`.

Set `N : (Fin (k + 1) → E) →ₗ[E] (Fin (k + 1) → E)` to `(LinearMap.single E (fun _ : Fin (k + 1) => E) 0) ∘ₗ f ∘ₗ tl`. Establish `hNapp : ∀ y, N y = Pi.single 0 (f (Fin.tail y))` using `fun y => rfl`. Establish `hNN : ∀ y, N (N y) = 0`. Introduce `y`. Rewrite using `[hNapp, hNapp, htail0, map_zero, Pi.single_zero]`.

Set `e : (Fin (k + 1) → E) ≃ₗ[E] (Fin (k + 1) → E)` to `LinearEquiv.ofLinearMap (LinearMap.id - N) (LinearMap.id + N) (LinearMap.ext fun y => by`. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_add, hNN]`. Use the proof step `abel)`. Use the proof step `(LinearMap.ext fun y => by`. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_sub, hNN]`.

Use the proof step `abel)`. Establish `heapp : ∀ y, e y = y - N y` using `fun y => rfl`. Set `sg : E →ₗ[𝓞 E] (Fin (k + 1) → E)` to `(LinearMap.single E (fun _ : Fin (k + 1) => E) 0).restrictScalars (𝓞 E)`. Set `𝔠 : Submodule (𝓞 E) E` to `Λ.comap sg`. Establish `h𝔠fg : 𝔠.FG` using `Submodule.fg_of_fg_map_injective sg (fun a b hab => Pi.single_injective 0 hab) (Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le sg Λ))`.

Establish `h𝔠1 : (1 : E) ∈ 𝔠` using `h1`. Take `⟨𝔞, ha, h𝔞⟩` from `exists_ideal_inv 𝔠 h𝔠fg h𝔠1`. Use `⟨e, 𝔞, L, ha, hL, ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[heapp, hNapp, htail0, map_zero, Pi.single_zero, sub_zero]`. Establish `he0 : e y 0 = y 0 - f (Fin.tail y)`.

Rewrite using `[heapp, Pi.sub_apply, hNapp, Pi.single_eq_same]`. Establish `het : Fin.tail (e y) = Fin.tail y`. Rewrite using `[heapp, hNapp]`. Use function extensionality and compare the values at `j`. Use `show y j.succ - (Pi.single (0 : Fin (k + 1)) (f (Fin.tail y)) : Fin (k + 1) → E) j.succ = y j.succ`.

Rewrite using `[Pi.single_eq_of_ne (Fin.succ_ne_zero j), sub_zero]`. Rewrite using `[he0, het, h𝔞]`. Establish `hsplit : y = Pi.single 0 (y 0 - f (Fin.tail y)) + Fin.cons (f (Fin.tail y)) (Fin.tail y)`. Rewrite using `[cons_eq, ← add_assoc, ← Pi.single_add, sub_add_cancel, ← cons_eq, Fin.cons_self_tail]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h0, ht⟩`. Rewrite using `[hsplit]`. Conclude with `Λ.add_mem h0 (hf _ ht)`. Introduce `hy`. Establish `ht : Fin.tail y ∈ L` using `(hLmem _).mpr ⟨y, hy, rfl⟩`.

Use `⟨?_, ht⟩` and prove the remaining obligations. Use `show Pi.single 0 (y 0 - f (Fin.tail y)) ∈ Λ`. Rewrite using `[eq_sub_of_add_eq hsplit.symm]`. Conclude with `Λ.sub_mem hy (hf _ ht)`.
-/
theorem exists_normal {k : ℕ} (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (hΛ : Submodule.IsLattice E Λ)
    (h1 : Pi.single 0 1 ∈ Λ) :
    ∃ (e : (Fin (k + 1) → E) ≃ₗ[E] (Fin (k + 1) → E)) (𝔞 : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin k → E)),
      𝔞 ≠ ⊥ ∧ Submodule.IsLattice E L ∧ e (Pi.single 0 1) = Pi.single 0 1 ∧
      ∀ y, ((∀ t ∈ 𝔞, (t : E) * e y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail (e y) ∈ L) ↔ y ∈ Λ := by
  let tl : (Fin (k + 1) → E) →ₗ[E] (Fin k → E) := LinearMap.funLeft E E Fin.succ
  let L : Submodule (𝓞 E) (Fin k → E) := Λ.map (tl.restrictScalars (𝓞 E))
  have hL : Submodule.IsLattice E L := isLattice_map Λ hΛ tl
    (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective k))
  have hLmem : ∀ z, z ∈ L ↔ ∃ y ∈ Λ, Fin.tail y = z := fun z => by
    rw [Submodule.mem_map]
    rfl
  obtain ⟨f, hf⟩ := exists_section Λ L hL hLmem
  have htail0 : ∀ c : E, Fin.tail (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) = 0 := fun c =>
    funext fun j => by
      show (Pi.single (0 : Fin (k + 1)) c : Fin (k + 1) → E) j.succ = 0
      exact Pi.single_eq_of_ne (Fin.succ_ne_zero j) c
  let N : (Fin (k + 1) → E) →ₗ[E] (Fin (k + 1) → E) :=
    (LinearMap.single E (fun _ : Fin (k + 1) => E) 0) ∘ₗ f ∘ₗ tl
  have hNapp : ∀ y, N y = Pi.single 0 (f (Fin.tail y)) := fun y => rfl
  have hNN : ∀ y, N (N y) = 0 := by
    intro y
    rw [hNapp, hNapp, htail0, map_zero, Pi.single_zero]
  let e : (Fin (k + 1) → E) ≃ₗ[E] (Fin (k + 1) → E) :=
    LinearEquiv.ofLinearMap (LinearMap.id - N) (LinearMap.id + N)
      (LinearMap.ext fun y => by
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
          map_add, hNN]
        abel)
      (LinearMap.ext fun y => by
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
          map_sub, hNN]
        abel)
  have heapp : ∀ y, e y = y - N y := fun y => rfl
  let sg : E →ₗ[𝓞 E] (Fin (k + 1) → E) :=
    (LinearMap.single E (fun _ : Fin (k + 1) => E) 0).restrictScalars (𝓞 E)
  let 𝔠 : Submodule (𝓞 E) E := Λ.comap sg
  have h𝔠fg : 𝔠.FG := Submodule.fg_of_fg_map_injective sg (fun a b hab => Pi.single_injective 0 hab)
    (Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le sg Λ))
  have h𝔠1 : (1 : E) ∈ 𝔠 := h1
  obtain ⟨𝔞, ha, h𝔞⟩ := exists_ideal_inv 𝔠 h𝔠fg h𝔠1
  refine ⟨e, 𝔞, L, ha, hL, ?_, fun y => ?_⟩
  · rw [heapp, hNapp, htail0, map_zero, Pi.single_zero, sub_zero]
  · have he0 : e y 0 = y 0 - f (Fin.tail y) := by
      rw [heapp, Pi.sub_apply, hNapp, Pi.single_eq_same]
    have het : Fin.tail (e y) = Fin.tail y := by
      rw [heapp, hNapp]
      funext j
      show y j.succ - (Pi.single (0 : Fin (k + 1)) (f (Fin.tail y)) : Fin (k + 1) → E) j.succ = y j.succ
      rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j), sub_zero]
    rw [he0, het, h𝔞]
    have hsplit : y = Pi.single 0 (y 0 - f (Fin.tail y)) + Fin.cons (f (Fin.tail y)) (Fin.tail y) := by
      rw [cons_eq, ← add_assoc, ← Pi.single_add, sub_add_cancel, ← cons_eq, Fin.cons_self_tail]
    constructor
    · rintro ⟨h0, ht⟩
      rw [hsplit]
      exact Λ.add_mem h0 (hf _ ht)
    · intro hy
      have ht : Fin.tail y ∈ L := (hLmem _).mpr ⟨y, hy, rfl⟩
      refine ⟨?_, ht⟩
      show Pi.single 0 (y 0 - f (Fin.tail y)) ∈ Λ
      rw [eq_sub_of_add_eq hsplit.symm]
      exact Λ.sub_mem hy (hf _ ht)

omit [NumberField E] in
/- English proof (translation)
Establish `h00 : M 0 0 = 1`. Use `congrFun hM 0` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same]`. Then use the resulting hypothesis. Establish `hs0 : ∀ j : Fin k, M j.succ 0 = 0` using `fun j => by`. Use `congrFun hM j.succ` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j)]`. Then use the resulting hypothesis. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Fin.tail]`. Rewrite using `[Fin.sum_univ_succ, h00, one_mul]`. Use function extensionality and compare the values at `i`.

Simplify using `only [Matrix.mulVec, dotProduct, Fin.tail, Matrix.submatrix_apply]`. Rewrite using `[Fin.sum_univ_succ, hs0, zero_mul, zero_add]`.
-/
theorem mulVec_zero_tail {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) (y : Fin (k + 1) → E) :
    (M *ᵥ y) 0 = y 0 + (fun b => M 0 b.succ) ⬝ᵥ Fin.tail y ∧
      Fin.tail (M *ᵥ y) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y := by
  have h00 : M 0 0 = 1 := by
    have := congrFun hM 0
    rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] at this
  have hs0 : ∀ j : Fin k, M j.succ 0 = 0 := fun j => by
    have := congrFun hM j.succ
    rwa [Matrix.mulVec_single_one, Matrix.col_apply,
      Pi.single_eq_of_ne (Fin.succ_ne_zero j)] at this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct, Fin.tail]
    rw [Fin.sum_univ_succ, h00, one_mul]
  · funext i
    simp only [Matrix.mulVec, dotProduct, Fin.tail, Matrix.submatrix_apply]
    rw [Fin.sum_univ_succ, hs0, zero_mul, zero_add]

/- English proof (translation)
Introduce `E _ _ k Lf hLf`. Use `⟨fun 𝔞 Λ' ha hΛ' => isLattice_sum 𝔞 Λ' (Lf 𝔞 Λ') (hLf 𝔞 Λ') ha hΛ', ?_, ?_⟩` and prove the remaining obligations. Introduce `Λ hΛ x hx hx0`. Take `⟨e₁, he₁⟩` from `exists_equiv_single x hx0`. Set `Λ₁` to `Λ.map ((e₁ : (Fin (k + 1) → E) →ₗ[E] (Fin (k + 1) → E)).restrictScalars (𝓞 E))`.

Establish `hΛ₁ : Submodule.IsLattice E Λ₁` using `isLattice_map Λ hΛ _ e₁.surjective`. Establish `hmem₁ : ∀ y, e₁ y ∈ Λ₁ ↔ y ∈ Λ` using `fun y => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', hy', hyy⟩`. Rewrite `hy'` using `[e₁.injective hyy]`. Then use the resulting hypothesis.

Introduce `hy`. Conclude with `⟨y, hy, rfl⟩`. Establish `h1 : Pi.single 0 1 ∈ Λ₁`. Rewrite using `[← he₁]`. Conclude with `(hmem₁ x).mpr hx`.

Take `⟨e₂, 𝔞, Λ', ha, hΛ', he₂, hmem₂⟩` from `exists_normal Λ₁ hΛ₁ h1`. Take `⟨γ, hγ⟩` from `exists_GL_of_equiv (e₁.trans e₂)`. Use `⟨γ, 𝔞, Λ', ha, hΛ', ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hγ, LinearEquiv.trans_apply, he₁, he₂]`. Rewrite using `[hγ, LinearEquiv.trans_apply, hLf, hmem₂, hmem₁]`.

Introduce `𝔞 𝔟 Λ₁ Λ₂ ha hb hΛ₁ hΛ₂ γ hγ`. Establish `hm` using `mulVec_zero_tail (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) hγ`. Use `set r : Fin k → E := fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ with hr`. Use `set γ' := (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ with hγ'`. Set `Cd : Ideal (𝓞 E) → E → Prop` to `fun 𝔡 c => ∀ t ∈ 𝔡, (t : E) * c ∈ (algebraMap (𝓞 E) E).range`.

Establish `hadd : ∀ 𝔡 a b, Cd 𝔡 a → Cd 𝔡 b → Cd 𝔡 (a + b)` using `fun 𝔡 a b ha hb t ht => by`. Rewrite using `[mul_add]`. Conclude with `Subring.add_mem _ (ha t ht) (hb t ht)`. Establish `hneg : ∀ 𝔡 a, Cd 𝔡 a → Cd 𝔡 (-a)` using `fun 𝔡 a ha t ht => by`. Rewrite using `[mul_neg]`.

Conclude with `Subring.neg_mem _ (ha t ht)`. Establish `hzero : ∀ 𝔡, Cd 𝔡 0` using `fun 𝔡 t _ => by`. Rewrite using `[mul_zero]`. Conclude with `Subring.zero_mem _`. Establish `hv : ∀ c z, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z = Fin.cons (c + r ⬝ᵥ z) (γ' *ᵥ z)` using `fun c z => by`.

Take `⟨h1, h2⟩` from `hm (Fin.cons c z)`. Rewrite `h1` using `[Fin.cons_zero, Fin.tail_cons]`. Rewrite `h2` using `[Fin.tail_cons]`. Rewrite using `[← Fin.cons_self_tail ((γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z), h1, h2]`. Establish `hL : ∀ 𝔡 (Λ : Submodule (𝓞 E) (Fin k → E)) c z, Fin.cons c z ∈ Lf 𝔡 Λ ↔ Cd 𝔡 c ∧ z ∈ Λ`.

Introduce `𝔡 Λ c z`. Rewrite using `[hLf, Fin.cons_zero, Fin.tail_cons]`. Establish `hLγ : ∀ c z, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z ∈ Lf 𝔟 Λ₂ ↔ Cd 𝔟 (c + r ⬝ᵥ z) ∧ γ' *ᵥ z ∈ Λ₂` using `fun c z => by`. Rewrite using `[hv, hL]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Establish `H' : ∀ c z, (Cd 𝔟 (c + r ⬝ᵥ z) ∧ γ' *ᵥ z ∈ Λ₂) ↔ (Cd 𝔞 c ∧ z ∈ Λ₁)` using `fun c z => by`. Rewrite using `[← hLγ, ← hL]`. Conclude with `H _`. Establish `hab : 𝔞 = 𝔟` using `ideal_eq_of_inv ha hb (fun c => by`.

Use `H' c 0` as an intermediate fact. Simplify `this)` using `[Cd, Λ₁.zero_mem, Λ₂.zero_mem]`. Substitute `hab` using the available equality. Use `⟨rfl, fun z => ?_, fun z hz t ht => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `hz2`. Use `(H' (-(r ⬝ᵥ z)) z).mp ⟨by rw [neg_add_cancel]; exact hzero 𝔞, hz2⟩` as an intermediate fact. Conclude with `this.2`. Introduce `hz1`. Conclude with `((H' 0 z).mpr ⟨hzero 𝔞, hz1⟩).2`.

Use `((H' 0 z).mpr ⟨hzero 𝔞, hz⟩).1` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `this t ht`. Introduce and unpack `⟨rfl, hΛ, hrow⟩ y`. Rewrite using `[← Fin.cons_self_tail y, hLγ, hL]`.

Distinguish the cases in `hy : Fin.tail y ∈ Λ₁`. Establish `hr' : Cd 𝔞 (r ⬝ᵥ Fin.tail y)` using `hrow _ hy`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, -⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations.

Use `hadd 𝔞 _ _ h1 (hneg 𝔞 _ hr')` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, -⟩`. Conclude with `⟨hadd 𝔞 _ _ h1 hr', (hΛ _).mpr hy⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h2⟩`. Conclude with `absurd ((hΛ _).mp h2) hy`. Introduce and unpack `⟨-, h2⟩`. Conclude with `absurd h2 hy`.
-/
theorem classes : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → (∀ 𝔞 Λ', 𝔞 ≠ ⊥ → Submodule.IsLattice E Λ' → Submodule.IsLattice E (Lf 𝔞 Λ') ∧ Pi.single 0 1 ∈ Lf 𝔞 Λ') ∧ (∀ Λ : Submodule (𝓞 E) (Fin (k + 1) → E), Submodule.IsLattice E Λ → ∀ x ∈ Λ, x ≠ 0 → ∃ (γ : GL (Fin (k + 1)) E) (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ ∧ Submodule.IsLattice E Λ' ∧ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ x = Pi.single 0 1 ∧ ∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔞 Λ' ↔ y ∈ Λ) ∧ ∀ 𝔞 𝔟 Λ₁ Λ₂, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Submodule.IsLattice E Λ₁ → Submodule.IsLattice E Λ₂ → ∀ γ : GL (Fin (k + 1)) E, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1 → ((∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔟 Λ₂ ↔ y ∈ Lf 𝔞 Λ₁) ↔ 𝔞 = 𝔟 ∧ (∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ₂ ↔ y ∈ Λ₁) ∧ ∀ y ∈ Λ₁, ∀ t ∈ 𝔞, (t : E) * ((fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ) ⬝ᵥ y) ∈ (algebraMap (𝓞 E) E).range) := by
  intro E _ _ k Lf hLf
  refine ⟨fun 𝔞 Λ' ha hΛ' => isLattice_sum 𝔞 Λ' (Lf 𝔞 Λ') (hLf 𝔞 Λ') ha hΛ', ?_, ?_⟩
  · intro Λ hΛ x hx hx0
    obtain ⟨e₁, he₁⟩ := exists_equiv_single x hx0
    let Λ₁ := Λ.map ((e₁ : (Fin (k + 1) → E) →ₗ[E] (Fin (k + 1) → E)).restrictScalars (𝓞 E))
    have hΛ₁ : Submodule.IsLattice E Λ₁ := isLattice_map Λ hΛ _ e₁.surjective
    have hmem₁ : ∀ y, e₁ y ∈ Λ₁ ↔ y ∈ Λ := fun y => by
      constructor
      · rintro ⟨y', hy', hyy⟩
        rwa [e₁.injective hyy] at hy'
      · intro hy
        exact ⟨y, hy, rfl⟩
    have h1 : Pi.single 0 1 ∈ Λ₁ := by
      rw [← he₁]
      exact (hmem₁ x).mpr hx
    obtain ⟨e₂, 𝔞, Λ', ha, hΛ', he₂, hmem₂⟩ := exists_normal Λ₁ hΛ₁ h1
    obtain ⟨γ, hγ⟩ := exists_GL_of_equiv (e₁.trans e₂)
    refine ⟨γ, 𝔞, Λ', ha, hΛ', ?_, fun y => ?_⟩
    · rw [hγ, LinearEquiv.trans_apply, he₁, he₂]
    · rw [hγ, LinearEquiv.trans_apply, hLf, hmem₂, hmem₁]
  · intro 𝔞 𝔟 Λ₁ Λ₂ ha hb hΛ₁ hΛ₂ γ hγ
    have hm := mulVec_zero_tail (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) hγ
    set r : Fin k → E := fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ with hr
    set γ' := (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ with hγ'
    let Cd : Ideal (𝓞 E) → E → Prop := fun 𝔡 c => ∀ t ∈ 𝔡, (t : E) * c ∈ (algebraMap (𝓞 E) E).range
    have hadd : ∀ 𝔡 a b, Cd 𝔡 a → Cd 𝔡 b → Cd 𝔡 (a + b) := fun 𝔡 a b ha hb t ht => by
      rw [mul_add]
      exact Subring.add_mem _ (ha t ht) (hb t ht)
    have hneg : ∀ 𝔡 a, Cd 𝔡 a → Cd 𝔡 (-a) := fun 𝔡 a ha t ht => by
      rw [mul_neg]
      exact Subring.neg_mem _ (ha t ht)
    have hzero : ∀ 𝔡, Cd 𝔡 0 := fun 𝔡 t _ => by
      rw [mul_zero]
      exact Subring.zero_mem _
    have hv : ∀ c z, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z =
        Fin.cons (c + r ⬝ᵥ z) (γ' *ᵥ z) := fun c z => by
      obtain ⟨h1, h2⟩ := hm (Fin.cons c z)
      rw [Fin.cons_zero, Fin.tail_cons] at h1
      rw [Fin.tail_cons] at h2
      rw [← Fin.cons_self_tail ((γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z), h1, h2]
    have hL : ∀ 𝔡 (Λ : Submodule (𝓞 E) (Fin k → E)) c z, Fin.cons c z ∈ Lf 𝔡 Λ ↔ Cd 𝔡 c ∧ z ∈ Λ := by
      intro 𝔡 Λ c z
      rw [hLf, Fin.cons_zero, Fin.tail_cons]
    have hLγ : ∀ c z, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Fin.cons c z ∈ Lf 𝔟 Λ₂ ↔
        Cd 𝔟 (c + r ⬝ᵥ z) ∧ γ' *ᵥ z ∈ Λ₂ := fun c z => by
      rw [hv, hL]
    constructor
    · intro H
      have H' : ∀ c z, (Cd 𝔟 (c + r ⬝ᵥ z) ∧ γ' *ᵥ z ∈ Λ₂) ↔ (Cd 𝔞 c ∧ z ∈ Λ₁) := fun c z => by
        rw [← hLγ, ← hL]
        exact H _
      have hab : 𝔞 = 𝔟 := ideal_eq_of_inv ha hb (fun c => by
        have := H' c 0
        simpa [Cd, Λ₁.zero_mem, Λ₂.zero_mem] using this)
      subst hab
      refine ⟨rfl, fun z => ?_, fun z hz t ht => ?_⟩
      · constructor
        · intro hz2
          have := (H' (-(r ⬝ᵥ z)) z).mp ⟨by rw [neg_add_cancel]; exact hzero 𝔞, hz2⟩
          exact this.2
        · intro hz1
          exact ((H' 0 z).mpr ⟨hzero 𝔞, hz1⟩).2
      · have := ((H' 0 z).mpr ⟨hzero 𝔞, hz⟩).1
        rw [zero_add] at this
        exact this t ht
    · rintro ⟨rfl, hΛ, hrow⟩ y
      rw [← Fin.cons_self_tail y, hLγ, hL]
      by_cases hy : Fin.tail y ∈ Λ₁
      · have hr' : Cd 𝔞 (r ⬝ᵥ Fin.tail y) := hrow _ hy
        constructor
        · rintro ⟨h1, -⟩
          refine ⟨?_, hy⟩
          have := hadd 𝔞 _ _ h1 (hneg 𝔞 _ hr')
          rwa [add_neg_cancel_right] at this
        · rintro ⟨h1, -⟩
          exact ⟨hadd 𝔞 _ _ h1 hr', (hΛ _).mpr hy⟩
      · constructor
        · rintro ⟨-, h2⟩
          exact absurd ((hΛ _).mp h2) hy
        · rintro ⟨-, h2⟩
          exact absurd h2 hy

end GlobalTheory.LatVecPair
