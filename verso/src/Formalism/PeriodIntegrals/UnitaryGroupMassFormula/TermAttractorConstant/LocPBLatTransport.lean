import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

abbrev fO (n : S.V ≃ₗ[E] S.V) : S.V →ₗ[𝓞 E] S.V := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fO_apply (n : S.V ≃ₗ[E] S.V) (v : S.V) : fO n v = n v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gmap_eq_map (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n M = M.map (fO n) := rfl

/- English proof (translation)
Rewrite using `[gmap_eq_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify `hw` using `[fO_apply]`. Introduce `hv`.

Conclude with `⟨n.symm v, hv, by simp [fO_apply]⟩`.
-/
theorem mem_gmap_iff (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.gmap n M ↔ n.symm v ∈ M := by
  rw [gmap_eq_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [fO_apply] using hw
  · intro hv
    exact ⟨n.symm v, hv, by simp [fO_apply]⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_localization_iff (P : Ideal (𝓞 E)) [P.IsPrime] (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s ∈ P.primeCompl, s • v ∈ M := Iff.rfl

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_localization_iff, mem_gmap_iff, mem_localization_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsv⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite `hsv` using `[mem_gmap_iff]`. Establish `e : n.symm (s • v) = s • n.symm v` using `(fO n.symm).map_smul s v`. Rewrite `hsv` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨s, hs, hsv⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_gmap_iff]`. Establish `e : n.symm (s • v) = s • n.symm v` using `(fO n.symm).map_smul s v`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem locP_gmap (P : Ideal (𝓞 E)) [P.IsPrime] (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.gmap n M) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P M) := by
  ext v
  rw [mem_localization_iff, mem_gmap_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff] at hsv
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e] at hsv
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e]

/- English proof (translation)
Use extensionality with `v`. Use `SetLike.ext_iff.1 h (n v)` as an intermediate fact. Simplify `this` using `[mem_gmap_iff]`.
-/
theorem gmap_injective (n : S.V ≃ₗ[E] S.V) {A B : Submodule (𝓞 E) S.V}
    (h : Formalism.HermitianLatticesTheory.gmap n A = Formalism.HermitianLatticesTheory.gmap n B) : A = B := by
  ext v
  have := SetLike.ext_iff.1 h (n v)
  simpa [mem_gmap_iff] using this

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le le_sup_left ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Establish `e : a = (a - b) + b` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left h) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))`. Use `sup_le le_sup_left ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Establish `e : b = a - (a - b)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a)) (Submodule.mem_sup_left h)`.
-/
theorem sup_span_swap {M : Submodule (𝓞 E) S.V} {a b : S.V} (h : a - b ∈ M) :
    M ⊔ Submodule.span (𝓞 E) {a} = M ⊔ Submodule.span (𝓞 E) {b} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : a = (a - b) + b := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : b = a - (a - b) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))
      (Submodule.mem_sup_left h)

/- English proof (translation)
Rewrite using `[gmap_eq_map, Submodule.map_span, Set.image_singleton, fO_apply]`.
-/
theorem gmap_span_singleton (n : S.V ≃ₗ[E] S.V) (v : S.V) :
    Formalism.HermitianLatticesTheory.gmap n (Submodule.span (𝓞 E) {v}) = Submodule.span (𝓞 E) {n v} := by
  rw [gmap_eq_map, Submodule.map_span, Set.image_singleton, fO_apply]

/- English proof (translation)
Rewrite using `[gmap_eq_map, gmap_eq_map, gmap_eq_map, Submodule.map_sup]`.
-/
theorem gmap_sup (n : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap n A ⊔ Formalism.HermitianLatticesTheory.gmap n B := by
  rw [gmap_eq_map, gmap_eq_map, gmap_eq_map, Submodule.map_sup]

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Establish `h : n v ∈ Formalism.HermitianLatticesTheory.gmap n Λ` using `(mem_gmap_iff n Λ (n v)).2 (by simpa using hv)`. Rewrite `h` using `[hn.2]`. Then use the resulting hypothesis.
-/
theorem autLam_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) : n v ∈ Λ := by
  have h : n v ∈ Formalism.HermitianLatticesTheory.gmap n Λ := (mem_gmap_iff n Λ (n v)).2 (by simpa using hv)
  rwa [hn.2] at h

/- English proof (translation)
Rewrite `hv` using `[← hn.2]`. Conclude with `(mem_gmap_iff n Λ v).1 hv`.
-/
theorem autLam_symm_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) :
    n.symm v ∈ Λ := by
  rw [← hn.2] at hv
  exact (mem_gmap_iff n Λ v).1 hv

/- English proof (translation)
Unfold `XLam`. Rewrite using `[Submodule.mem_inf, Submodule.restrictScalars_mem]`.
-/
theorem mem_XLam {F : LFlag S r T} {v : S.V} : v ∈ XLam Λ F ↔ v ∈ Λ ∧ v ∈ Xsp F := by
  unfold XLam
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem]

/- English proof (translation)
Establish `hni : n.symm ∈ NLam Λ F` using `nlam_inv hn`. Use extensionality with `v`. Rewrite using `[mem_gmap_iff, mem_XLam, mem_XLam]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Establish `a1` using `autLam_maps hn.1 h1`. Establish `a2` using `nlam_maps_X hn _ h2`. Simplify using `only [LinearEquiv.apply_symm_apply] at a1 a2`. Conclude with `⟨a1, a2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨autLam_symm_maps hn.1 h1, nlam_maps_X hni _ h2⟩`.
-/
theorem gmap_XLam_self {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n (XLam Λ F) = XLam Λ F := by
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  ext v
  rw [mem_gmap_iff, mem_XLam, mem_XLam]
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := autLam_maps hn.1 h1
    have a2 := nlam_maps_X hn _ h2
    simp only [LinearEquiv.apply_symm_apply] at a1 a2
    exact ⟨a1, a2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, nlam_maps_X hni _ h2⟩

/- English proof (translation)
The claim follows from `mem_XLam.2 ⟨Submodule.sub_mem _ (autLam_maps hn.1 hz) hz, hn.2.2 _ (z_mem_orth F)⟩`.
-/
theorem nlam_z_sub {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hz : F.fl.z ∈ Λ) :
    n F.fl.z - F.fl.z ∈ XLam Λ F :=
  mem_XLam.2 ⟨Submodule.sub_mem _ (autLam_maps hn.1 hz) hz, hn.2.2 _ (z_mem_orth F)⟩

/- English proof (translation)
Set `g : S.V ≃ₗ[E] S.V` to `m.trans n`. Establish `hfr' : ∀ a, frame F₂ a = g (frame F₁ a)` using `fun a => hfr a`. Establish `hg : IsAutLam S Λ g` using `autLam_mul hn.1 hm.1`. Establish `h1 : XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap g (XLam Λ F₁)`. Use extensionality with `v`.

Rewrite using `[mem_gmap_iff, mem_XLam, mem_XLam, Xsp_mem_transport hfr' v]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨autLam_symm_maps hg h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Use `autLam_maps hg h1` as an intermediate fact. Simplify using `using this`. Rewrite using `[h1]`. Use `show Formalism.HermitianLatticesTheory.gmap (n * m) (XLam Λ F₁) = _`.

Rewrite using `[gmap_mul', gmap_XLam_self hm]`.
-/
theorem XLam_transport {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} {T₀ : E} {F : LFlag S r T₀}
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap n (XLam Λ F₁) := by
  let g : S.V ≃ₗ[E] S.V := m.trans n
  have hfr' : ∀ a, frame F₂ a = g (frame F₁ a) := fun a => hfr a
  have hg : IsAutLam S Λ g := autLam_mul hn.1 hm.1
  have h1 : XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap g (XLam Λ F₁) := by
    ext v
    rw [mem_gmap_iff, mem_XLam, mem_XLam, Xsp_mem_transport hfr' v]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨autLam_symm_maps hg h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := autLam_maps hg h1
      simpa using this
  rw [h1]
  show Formalism.HermitianLatticesTheory.gmap (n * m) (XLam Λ F₁) = _
  rw [gmap_mul', gmap_XLam_self hm]

/- English proof (translation)
Unfold `UU`. Rewrite using `[gmap_sup, gmap_sup, gmap_sup, gmap_span_singleton, gmap_span_singleton, gmap_XLam_self hn, ← XLam_transport hn hm hfr, sup_assoc, sup_assoc (XLam Λ F ⊔ _)]`. Establish `e1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} = XLam Λ F ⊔ Submodule.span (𝓞 E) {n F.zt}`. Use `sup_span_swap ?_` and prove the remaining obligations. Rewrite using `[hF.2]`.

Use `Submodule.neg_mem _ (nlam_z_sub hn hF.1)` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Establish `e2 : XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {F₂.zt} = XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {n F₁.zt}`. Use `sup_span_swap ?_` and prove the remaining obligations. Rewrite using `[hzt, ← map_sub, XLam_transport hn hm hfr, mem_gmap_iff, LinearEquiv.symm_apply_apply, h₁.2]`.

Conclude with `nlam_z_sub hm h₁.1`. Rewrite using `[e1, e2]`.
-/
theorem UU_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    UU Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (UU Λ F F₁) := by
  unfold UU
  rw [gmap_sup, gmap_sup, gmap_sup, gmap_span_singleton, gmap_span_singleton, gmap_XLam_self hn,
    ← XLam_transport hn hm hfr, sup_assoc, sup_assoc (XLam Λ F ⊔ _)]
  have e1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} = XLam Λ F ⊔ Submodule.span (𝓞 E) {n F.zt} := by
    refine sup_span_swap ?_
    rw [hF.2]
    have := Submodule.neg_mem _ (nlam_z_sub hn hF.1)
    rwa [neg_sub] at this
  have e2 : XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {F₂.zt} = XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {n F₁.zt} := by
    refine sup_span_swap ?_
    rw [hzt, ← map_sub, XLam_transport hn hm hfr, mem_gmap_iff, LinearEquiv.symm_apply_apply, h₁.2]
    exact nlam_z_sub hm h₁.1
  rw [e1, e2]

/- English proof (translation)
Unfold `spanE`. Rewrite using `[gmap_eq_map, Submodule.map_coe]`. Establish `e : ⇑(fO n) = ⇑(n : S.V →ₗ[E] S.V)` using `rfl`. Rewrite using `[e, Submodule.span_image]`.
-/
theorem spanE_gmap (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap n M) = (spanE S M).map (n : S.V →ₗ[E] S.V) := by
  unfold spanE
  rw [gmap_eq_map, Submodule.map_coe]
  have e : ⇑(fO n) = ⇑(n : S.V →ₗ[E] S.V) := rfl
  rw [e, Submodule.span_image]

/- English proof (translation)
Unfold `BLat UUE`. Rewrite using `[UU_transport hF h₁ hn hm hfr hzt, spanE_gmap]`. Use extensionality with `v`. Rewrite using `[mem_gmap_iff, Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, Submodule.mem_map_equiv]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨autLam_symm_maps hn.1 h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Use `autLam_maps hn.1 h1` as an intermediate fact.

Simplify using `using this`.
-/
theorem BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    BLat Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (BLat Λ F F₁) := by
  unfold BLat UUE
  rw [UU_transport hF h₁ hn hm hfr hzt, spanE_gmap]
  ext v
  rw [mem_gmap_iff, Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, Submodule.mem_map_equiv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := autLam_maps hn.1 h1
    simpa using this

/- English proof (translation)
Rewrite using `[BLat_transport hF h₁ hn hm hfr hzt, locP_gmap]`.
-/
theorem locP_BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt))
    (P : Ideal (𝓞 E)) [P.IsPrime] :
    Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₂) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₁)) := by
  rw [BLat_transport hF h₁ hn hm hfr hzt, locP_gmap]

/- English proof (translation)
Rewrite using `[locP_BLat_transport hF h₁ hn hm hfr hzt, UU_transport hF h₁ hn hm hfr hzt, locP_gmap]`. Conclude with `⟨gmap_injective n, fun h => by rw [h]⟩`.
-/
theorem offg_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt))
    (P : Ideal (𝓞 E)) [P.IsPrime] :
    Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₂) = Formalism.HermitianLatticesTheory.localization₂ P (UU Λ F F₂) ↔
      Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₁) = Formalism.HermitianLatticesTheory.localization₂ P (UU Λ F F₁) := by
  rw [locP_BLat_transport hF h₁ hn hm hfr hzt, UU_transport hF h₁ hn hm hfr hzt, locP_gmap]
  exact ⟨gmap_injective n, fun h => by rw [h]⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
