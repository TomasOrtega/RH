import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

set_option autoImplicit false

noncomputable section

open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit

namespace GlobalTheory.HTLat

section Eigen

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)

def eigSubLat (χ : Λ →+* C) (X : Submodule O V) : Submodule O V :=
  X ⊓ (eigenSub ρ χ).restrictScalars O

variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ)

def eigQuotLat (i : ι) (X : Submodule O V) : Submodule O V :=
  X.map ((proj h ρ i).restrictScalars O)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_eigSubLat {χ : Λ →+* C} {X : Submodule O V} {x : V} :
    x ∈ eigSubLat ρ χ X ↔ x ∈ X ∧ x ∈ eigenSub ρ χ := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_eigQuotLat {i : ι} {X : Submodule O V} {x : V} :
    x ∈ eigQuotLat ρ h i X ↔ ∃ y ∈ X, proj h ρ i y = x := Iff.rfl

/- English proof (translation)
Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `proj_mem h ρ i y`.
-/
theorem eigQuotLat_le (i : ι) (X : Submodule O V) :
    eigQuotLat ρ h i X ≤ (eigenSub ρ (σ i)).restrictScalars O := by
  rintro _ ⟨y, -, rfl⟩
  exact proj_mem h ρ i y

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V) in
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : _root_.GlobalTheory.EigenSplit.IsSplitting σ) in

/- English proof (translation)
Introduce `x hx`. Conclude with `⟨x, hx.1, _root_.GlobalTheory.EigenSplit.proj_of_mem h hx.2⟩`.
-/
theorem _root_.GlobalTheory.HTLat.eigSubLat_le_eigQuotLat (i : ι) (X : Submodule O V) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ (σ i) X ≤ _root_.GlobalTheory.HTLat.eigQuotLat ρ h i X := by
  intro x hx
  exact ⟨x, hx.1, _root_.GlobalTheory.EigenSplit.proj_of_mem h hx.2⟩

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V) in
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : _root_.GlobalTheory.EigenSplit.IsSplitting σ) in
/- English proof (translation)
The claim follows from `inf_le_inf_right _ hXY`.
-/
theorem _root_.GlobalTheory.HTLat.eigSubLat_mono (χ : Λ →+* C) {X Y : Submodule O V} (hXY : X ≤ Y) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ χ X ≤ _root_.GlobalTheory.HTLat.eigSubLat ρ χ Y :=
  inf_le_inf_right _ hXY

/- English proof (translation)
The claim follows from `Submodule.map_mono hXY`.
-/
theorem eigQuotLat_mono (i : ι) {X Y : Submodule O V} (hXY : X ≤ Y) :
    eigQuotLat ρ h i X ≤ eigQuotLat ρ h i Y := Submodule.map_mono hXY

/- English proof (translation)
Rewrite using `[eigQuotLat, eigQuotLat, ← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Use extensionality with `x`. Conclude with `hf.proj h i x`.
-/
theorem map_eigQuotLat {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V'] [IsScalarTower O C V']
    {ρ' : Λ →+* Module.End C V'} {f : V →ₗ[C] V'} (hf : IsEquivariant ρ ρ' f) (i : ι)
    (X : Submodule O V) :
    (eigQuotLat ρ h i X).map (f.restrictScalars O) =
      eigQuotLat ρ' h i (X.map (f.restrictScalars O)) := by
  rw [eigQuotLat, eigQuotLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact hf.proj h i x

end Eigen

section Embeddings

variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]

def embO (φ : E →+* C) : 𝓞 E →+* O :=
  let e : O ≃+* (algebraMap O C).range := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  e.symm.toRingHom.comp ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ fun a =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe a)).tower_top)))

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E] in
omit [NumberField E] in
/- English proof (translation)
Establish `hb : Function.Bijective (algebraMap O C).rangeRestrict` using `⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩`. Establish `hm : ∀ x, (φ.comp (algebraMap (𝓞 E) E)) x ∈ (algebraMap O C).range` using `fun x => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe x)).tower_top))`. Conclude with `congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap O C).rangeRestrict hb).apply_symm_apply ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ hm a))`.
-/
theorem _root_.GlobalTheory.HTLat.algebraMap_embO (φ : E →+* C) (a : 𝓞 E) :
    algebraMap O C (_root_.GlobalTheory.HTLat.embO hv φ a) = φ a := by
  have hb : Function.Bijective (algebraMap O C).rangeRestrict :=
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  have hm : ∀ x, (φ.comp (algebraMap (𝓞 E) E)) x ∈ (algebraMap O C).range := fun x =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe x)).tower_top))
  exact congrArg Subtype.val
    ((RingEquiv.ofBijective (algebraMap O C).rangeRestrict hb).apply_symm_apply
      ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ hm a))

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E] in

/- English proof (translation)
Establish `hfun : (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) = fun φ => (RingHom.id C).comp (φ.comp (algebraMap (𝓞 E) E))`. Use function extensionality and compare the values at `φ`. Use extensionality with `a`. Simplify using `[_root_.GlobalTheory.HTLat.algebraMap_embO]`. Rewrite using `[hfun]`.

Use `_root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (E := E) ?_ (NumberField.Embeddings.card E C) _ ?_` and prove the remaining obligations. Introduce `φ ψ h`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h`. Conclude with `isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))`.
-/
theorem _root_.GlobalTheory.HTLat.isSplitting_embO [IsAlgClosed C] [CharZero C] :
    _root_.GlobalTheory.EigenSplit.IsSplitting
      (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) := by
  classical
  have hfun : (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) =
      fun φ => (RingHom.id C).comp (φ.comp (algebraMap (𝓞 E) E)) := by
    funext φ
    ext a
    simp [_root_.GlobalTheory.HTLat.algebraMap_embO]
  rw [hfun]
  refine _root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (E := E) ?_
    (NumberField.Embeddings.card E C) _ ?_
  · intro φ ψ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · exact isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))

/- English proof (translation)
Rewrite using `[isSplitting_iff_isUnit_det _ (Module.Basis.singleton Unit ℤ)]`. Simplify using the standard rewrite rules.
-/
theorem isSplitting_int (R : Type) [CommRing R] :
    IsSplitting (fun _ : Unit => Int.castRingHom R) := by
  rw [isSplitting_iff_isUnit_det _ (Module.Basis.singleton Unit ℤ)]
  simp

end Embeddings

section Graded

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

def grLat (La : Submodule O U) (F' F : Submodule C U) : Submodule O (U ⧸ F') :=
  (La ⊓ F.restrictScalars O).map (F'.mkQ.restrictScalars O)

/- English proof (translation)
The claim follows from `Submodule.map_mono (inf_le_inf_right _ h)`.
-/
theorem grLat_mono {La La' : Submodule O U} (h : La ≤ La') (F' F : Submodule C U) :
    grLat La F' F ≤ grLat La' F' F := Submodule.map_mono (inf_le_inf_right _ h)

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hx.2, rfl⟩`.
-/
theorem grLat_le (La : Submodule O U) (F' F : Submodule C U) :
    grLat La F' F ≤ (F.map F'.mkQ).restrictScalars O := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.2, rfl⟩

/- English proof (translation)
Use `le_antisymm (le_inf (Submodule.map_mono inf_le_left) (grLat_le La F' F)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩`. Use `⟨x, ⟨hx, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `h1 : y - x ∈ F'` using `(Submodule.Quotient.eq F').1 hxy`. Establish `h2` using `F.sub_mem hy (h h1)`.

Simplify using `using h2`.
-/
theorem grLat_eq_inf (La : Submodule O U) {F' F : Submodule C U} (h : F' ≤ F) :
    grLat La F' F = La.map (F'.mkQ.restrictScalars O) ⊓ (F.map F'.mkQ).restrictScalars O := by
  refine le_antisymm (le_inf (Submodule.map_mono inf_le_left) (grLat_le La F' F)) ?_
  rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  have h1 : y - x ∈ F' := (Submodule.Quotient.eq F').1 hxy
  have h2 := F.sub_mem hy (h h1)
  simpa using h2

def scaleLat (a : C) (La : Submodule O U) : Submodule O U :=
  La.map ((a • LinearMap.id : U →ₗ[C] U).restrictScalars O)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scaleLat {a : C} {La : Submodule O U} {x : U} :
    x ∈ scaleLat a La ↔ ∃ y ∈ La, a • y = x := Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[mem_scaleLat]`.
-/
theorem scaleLat_one (La : Submodule O U) : scaleLat (1 : C) La = La := by
  ext x; simp [mem_scaleLat]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨⟨y, hy, rfl⟩, hF⟩, rfl⟩`. Conclude with `⟨F'.mkQ y, ⟨y, ⟨hy, (F.smul_mem_iff ha).1 hF⟩, rfl⟩, (map_smul F'.mkQ a y).symm⟩`. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`.

Conclude with `⟨a • y, ⟨⟨y, hy.1, rfl⟩, F.smul_mem a hy.2⟩, map_smul F'.mkQ a y⟩`.
-/
theorem grLat_scaleLat {a : C} (ha : a ≠ 0) (La : Submodule O U) (F' F : Submodule C U) :
    grLat (scaleLat a La) F' F = scaleLat a (grLat La F' F) := by
  ext z
  constructor
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hF⟩, rfl⟩
    exact ⟨F'.mkQ y, ⟨y, ⟨hy, (F.smul_mem_iff ha).1 hF⟩, rfl⟩, (map_smul F'.mkQ a y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, ⟨⟨y, hy.1, rfl⟩, F.smul_mem a hy.2⟩, map_smul F'.mkQ a y⟩

variable (v : Valuation C ℝ≥0)

def latNorm (La : Submodule O U) (x : U) : ℝ≥0 := sInf {r | ∃ a : C, x ∈ scaleLat a La ∧ v a = r}

variable {v}

/- English proof (translation)
Use `IsLeast.csInf_eq ⟨⟨c, ⟨g, Submodule.mem_span_singleton_self g, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ⟨y, hy, hay⟩, rfl⟩`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `h1 : (a * algebraMap O C b) • g = c • g`. Rewrite using `[mul_smul, algebraMap_smul]`.

Conclude with `hay`. Rewrite using `[← smul_left_injective C hg h1, map_mul]`. Conclude with `mul_le_of_le_one_right' (hv.map_le_one b)`.
-/
theorem latNorm_span_singleton (hv : v.Integers O) {g : U} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  refine IsLeast.csInf_eq ⟨⟨c, ⟨g, Submodule.mem_span_singleton_self g, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨a, ⟨y, hy, hay⟩, rfl⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h1 : (a * algebraMap O C b) • g = c • g := by
    rw [mul_smul, algebraMap_smul]; exact hay
  rw [← smul_left_injective C hg h1, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one b)

/- English proof (translation)
Take `⟨s, rfl⟩` from `hfg`. Establish `h3 : ∀ y ∈ s, ∃ c : C, c • x = y` using `fun y hy => Submodule.mem_span_singleton.1 (h₁ (Submodule.subset_span hy))`. Use `choose! c hc using h3`. Establish `hs : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Introduce and unpack `rfl`. Simplify using `at h₂`. Take `⟨y, hy, hmax⟩` from `s.exists_max_image (fun y => v (c y)) hs`. Establish `hle : Submodule.span O (s : Set U) ≤ Submodule.span O {c y • x}`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Distinguish the cases in `h0 : c y = 0`. Establish `: c z = 0` using `by simpa [h0] using hmax z hz`. Rewrite using `[← hc z hz, this, zero_smul]`. Conclude with `Submodule.zero_mem _`.

Take `⟨b, hb⟩` from `hv.exists_of_le_one (r := c z / c y) (by`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ (hmax z hz) zero_le)`. Use `Submodule.mem_span_singleton.2 ⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C b, hb, smul_smul, div_mul_cancel₀ _ h0, hc z hz]`.

Use `⟨c y, fun h0 => h₂ ?_, le_antisymm hle ?_⟩` and prove the remaining obligations. Rewrite `hle` using `[h0, zero_smul, Submodule.span_zero_singleton]`. Conclude with `le_bot_iff.1 hle`. Rewrite using `[hc y hy]`. Conclude with `Submodule.span_mono (by simpa using hy)`.
-/
theorem exists_generator (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) {x : U}
    (h₁ : La ≤ (Submodule.span C {x}).restrictScalars O) (h₂ : La ≠ ⊥) :
    ∃ c : C, c ≠ 0 ∧ La = Submodule.span O {c • x} := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have h3 : ∀ y ∈ s, ∃ c : C, c • x = y := fun y hy =>
    Submodule.mem_span_singleton.1 (h₁ (Submodule.subset_span hy))
  choose! c hc using h3
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h₂
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image (fun y => v (c y)) hs
  have hle : Submodule.span O (s : Set U) ≤ Submodule.span O {c y • x} := by
    rw [Submodule.span_le]
    intro z hz
    by_cases h0 : c y = 0
    · have : c z = 0 := by simpa [h0] using hmax z hz
      rw [← hc z hz, this, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨b, hb⟩ := hv.exists_of_le_one (r := c z / c y) (by
        rw [map_div₀]; exact div_le_one_of_le₀ (hmax z hz) zero_le)
      refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
      rw [← algebraMap_smul C b, hb, smul_smul, div_mul_cancel₀ _ h0, hc z hz]
  refine ⟨c y, fun h0 => h₂ ?_, le_antisymm hle ?_⟩
  · rw [h0, zero_smul, Submodule.span_zero_singleton] at hle
    exact le_bot_iff.1 hle
  · rw [hc y hy]
    exact Submodule.span_mono (by simpa using hy)

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] in
variable (v : Valuation C ℝ≥0) in
variable {v} in

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O C)` using `hv.hom_inj`. Use `haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hinj`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : Module.Finite O La := Module.Finite.iff_fg.mpr hfg`. Establish `key : ∀ (o : O) (u : U), o ≠ 0 → o • u ∈ F → u ∈ F`.

Introduce `o u ho hu`. Establish `h0 : algebraMap O C o ≠ 0`. Introduce `h`. Conclude with `ho (hinj (by rw [h, map_zero]))`. Rewrite `hu` using `[← algebraMap_smul C o u]`.

Use `F.smul_mem (algebraMap O C o)⁻¹ hu` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ h0, one_smul]`. Then use the resulting hypothesis. Set `g : La →ₗ[O] U ⧸ F.restrictScalars O` to `(F.restrictScalars O).mkQ ∘ₗ La.subtype`. Establish `htf : Submodule.torsion O (LinearMap.range g) = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Take `⟨⟨o, ho⟩, hox⟩` from `(Submodule.mem_torsion_iff x).1 hx`. Take `⟨q, hq⟩` from `x`. Take `⟨u, rfl⟩` from `Submodule.mkQ_surjective _ q`. Establish `hox' : o • (F.restrictScalars O).mkQ u = 0` using `congrArg Subtype.val hox`.

Rewrite `hox'` using `[← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `hu : u ∈ F` using `key o u (nonZeroDivisors.ne_zero ho) hox'`. Rewrite using `[Submodule.mem_bot]`. Use `ext`. Simplify using `using hu`.

Use `haveI : Module.Flat O (LinearMap.range g) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htf`. Use `haveI : Module.Free O (LinearMap.range g) := Module.free_of_flat_of_isLocalRing`. Use `haveI : Module.FinitePresentation O (LinearMap.range g) := Module.finitePresentation_of_projective _ _`. Establish `hker` using `Module.FinitePresentation.fg_ker g.rangeRestrict (LinearMap.surjective_rangeRestrict g)`. Rewrite `hker` using `[LinearMap.ker_rangeRestrict]`.

Establish `heq : La ⊓ F.restrictScalars O = (LinearMap.ker g).map La.subtype`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx1, hx2⟩`. Conclude with `⟨⟨x, hx1⟩, by simpa [g] using hx2, rfl⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, by simpa [g] using hy⟩`. Rewrite using `[heq]`. Conclude with `hker.map _`.
-/
theorem _root_.GlobalTheory.HTLat.fg_inf (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG)
    (F : Submodule C U) : (La ⊓ F.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hinj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O La := Module.Finite.iff_fg.mpr hfg
  have key : ∀ (o : O) (u : U), o ≠ 0 → o • u ∈ F → u ∈ F := by
    intro o u ho hu
    have h0 : algebraMap O C o ≠ 0 := by
      intro h
      exact ho (hinj (by rw [h, map_zero]))
    rw [← algebraMap_smul C o u] at hu
    have := F.smul_mem (algebraMap O C o)⁻¹ hu
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  let g : La →ₗ[O] U ⧸ F.restrictScalars O := (F.restrictScalars O).mkQ ∘ₗ La.subtype
  have htf : Submodule.torsion O (LinearMap.range g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨o, ho⟩, hox⟩ := (Submodule.mem_torsion_iff x).1 hx
    obtain ⟨q, hq⟩ := x
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ q
    have hox' : o • (F.restrictScalars O).mkQ u = 0 := congrArg Subtype.val hox
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hox'
    have hu : u ∈ F := key o u (nonZeroDivisors.ne_zero ho) hox'
    rw [Submodule.mem_bot]
    ext
    simpa using hu
  haveI : Module.Flat O (LinearMap.range g) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htf
  haveI : Module.Free O (LinearMap.range g) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation O (LinearMap.range g) :=
    Module.finitePresentation_of_projective _ _
  have hker := Module.FinitePresentation.fg_ker g.rangeRestrict
    (LinearMap.surjective_rangeRestrict g)
  rw [LinearMap.ker_rangeRestrict] at hker
  have heq : La ⊓ F.restrictScalars O = (LinearMap.ker g).map La.subtype := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, by simpa [g] using hx2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [g] using hy⟩
  rw [heq]
  exact hker.map _

/- English proof (translation)
The claim follows from `(fg_inf hv hfg F).map _`.
-/
theorem fg_grLat (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) (F' F : Submodule C U) :
    (grLat La F' F).FG := (fg_inf hv hfg F).map _

end Graded

section Frames

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}

variable (C) in

def step (f : Fin N → U) (i : ℕ) : Submodule C U := Submodule.span C (f '' {k | (k : ℕ) < i})

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.HTLat.step]`.
-/
theorem _root_.GlobalTheory.HTLat.step_zero (f : Fin N → U) :
    _root_.GlobalTheory.HTLat.step C f 0 = ⊥ := by
  simp [_root_.GlobalTheory.HTLat.step]

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
/- English proof (translation)
Introduce `i j hij`. Use `Submodule.span_mono (Set.image_mono ?_)` and prove the remaining obligations. Introduce `k hk`. Conclude with `lt_of_lt_of_le hk hij`.
-/
theorem _root_.GlobalTheory.HTLat.step_mono (f : Fin N → U) :
    Monotone (_root_.GlobalTheory.HTLat.step C f) := by
  intro i j hij
  refine Submodule.span_mono (Set.image_mono ?_)
  intro k hk
  exact lt_of_lt_of_le hk hij

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩`.
-/
theorem _root_.GlobalTheory.HTLat.mem_step_succ (f : Fin N → U) (i : Fin N) :
    f i ∈ _root_.GlobalTheory.HTLat.step C f (i + 1) :=
  Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

/- English proof (translation)
Rewrite using `[step, step, ← Submodule.span_union, ← Set.image_singleton, ← Set.image_union]`. Use `congr 2`. Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem step_succ (f : Fin N → U) (i : Fin N) :
    step C f (i + 1) = step C f i ⊔ Submodule.span C {f i} := by
  rw [step, step, ← Submodule.span_union, ← Set.image_singleton, ← Set.image_union]
  congr 2
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

/- English proof (translation)
Rewrite using `[step, step, Submodule.map_span, Set.image_comp]`.
-/
theorem map_step {U' : Type} [AddCommGroup U'] [Module C U'] (g : U →ₗ[C] U') (f : Fin N → U) (i : ℕ) :
    (step C f i).map g = step C (g ∘ f) i := by
  rw [step, step, Submodule.map_span, Set.image_comp]

/- English proof (translation)
Rewrite using `[step_succ, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, Set.image_singleton]`.
-/
theorem map_mkQ_step_succ (f : Fin N → U) (i : Fin N) :
    (step C f (i + 1)).map (step C f i).mkQ = Submodule.span C {(step C f i).mkQ (f i)} := by
  rw [step_succ, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
    Set.image_singleton]

variable (C) in

def grAt (La : Submodule O U) (f : Fin N → U) (i : Fin N) : Submodule O (U ⧸ step C f i) :=
  grLat La (step C f i) (step C f (i + 1))

def grNorm (v : Valuation C ℝ≥0) (La : Submodule O U) (f : Fin N → U) (i : Fin N) : ℝ≥0 :=
  latNorm v (grAt C La f i) ((step C f i).mkQ (f i))

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in

/- English proof (translation)
Use `set S := _root_.GlobalTheory.HTLat.step C f i with hS`. Use `set S' := _root_.GlobalTheory.HTLat.step C f (i + 1) with hS'`. Use `set xb := S.mkQ (f i) with hxb`. Establish `hxb0 : xb ≠ 0`. Rewrite using `[hxb, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hf`. Establish `hSS' : S ≤ S'` using `_root_.GlobalTheory.HTLat.step_mono f (Nat.le_succ _)`. Establish `hfi : f i ∈ S'` using `_root_.GlobalTheory.HTLat.mem_step_succ f i`. Establish `hS'le : S' ≤ S ⊔ C ∙ f i`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk` into its components or cases. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨k, hk, rfl⟩)`. Rewrite using `[Fin.ext hk]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.

Establish `hG : ∀ q ∈ _root_.GlobalTheory.HTLat.grAt C La f i, ∃ b : C, q = b • xb`. Introduce `q hq`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.1 hq`. Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.1 (hS'le hw.2)`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 ht`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show S.mkQ w = b • S.mkQ (f i)`. Rewrite using `[← hst, map_add, map_smul, Submodule.mkQ_apply S s, (Submodule.Quotient.mk_eq_zero S).2 hs, zero_add]`. Establish `hmem : a • xb ∈ _root_.GlobalTheory.HTLat.grAt C La f i`. Use `Submodule.mem_map.2 ⟨a • f i + y, ⟨hLa, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `S'.add_mem (S'.smul_mem a hfi) (hSS' hy)`. Use `show S.mkQ (a • f i + y) = a • S.mkQ (f i)`. Rewrite using `[map_add, map_smul, Submodule.mkQ_apply S y, (Submodule.Quotient.mk_eq_zero S).2 hy, add_zero]`. Establish `hGfg : (_root_.GlobalTheory.HTLat.grAt C La f i).FG` using `(_root_.GlobalTheory.HTLat.fg_inf hv hfg S').map _`. Take `⟨s, hs⟩` from `hGfg`.

Use `choose! coef hcoef using hG`. Establish `hsG : ∀ q ∈ s, q ∈ _root_.GlobalTheory.HTLat.grAt C La f i` using `fun q hq => hs ▸ Submodule.subset_span hq`. Establish `hsne : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`.

Rewrite `hs` using `[Finset.coe_empty, Submodule.span_empty]`. Rewrite `hmem` using `[← hs, Submodule.mem_bot]`. Conclude with `smul_ne_zero ha hxb0 hmem`. Take `⟨q₀, hq₀, hmax⟩` from `s.exists_max_image (fun q => v (coef q)) hsne`. Establish `hc : coef q₀ ≠ 0`.

Introduce `hc0`. Establish `hzero : ∀ q ∈ (s : Set (U ⧸ S)), q = 0`. Introduce `q hq`. Establish `h1` using `hmax q hq`. Rewrite `h1` using `[hc0, map_zero, nonpos_iff_eq_zero, Valuation.zero_iff]`.

Rewrite using `[hcoef q (hsG q hq), h1, zero_smul]`. Establish `hbot : _root_.GlobalTheory.HTLat.grAt C La f i = ⊥`. Rewrite using `[← hs, Submodule.span_eq_bot]`. Conclude with `hzero`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`.

Conclude with `smul_ne_zero ha hxb0 hmem`. Establish `hspan : _root_.GlobalTheory.HTLat.grAt C La f i = Submodule.span O {coef q₀ • xb}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hs, Submodule.span_le]`. Introduce `q hq`.

Establish `hle : v (coef q / coef q₀) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ (hmax q hq) (by positivity)`. Take `⟨o, ho⟩` from `hv.exists_of_le_one hle`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`.

Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hc, ← hcoef q (hsG q hq)]`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← hcoef q₀ (hsG q₀ hq₀)]`. Conclude with `hsG q₀ hq₀`. Use `⟨coef q₀, hc, hspan, ?_⟩` and prove the remaining obligations.

Use `show _root_.GlobalTheory.HTLat.latNorm v (_root_.GlobalTheory.HTLat.grAt C La f i) xb = _`. Rewrite using `[hspan]`. Unfold `_root_.GlobalTheory.HTLat.latNorm _root_.GlobalTheory.HTLat.scaleLat`. Use `IsLeast.csInf_eq ⟨⟨(coef q₀)⁻¹, ?_, map_inv₀ v _⟩, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map.2 ⟨coef q₀ • xb, Submodule.mem_span_singleton_self _, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Introduce and unpack `r ⟨b, hb, rfl⟩`. Take `⟨z, hz, hbz⟩` from `Submodule.mem_map.1 hb`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 hz`.

Establish `h1 : (b * algebraMap O C o * coef q₀) • xb = xb`. Establish `e1 : (b • LinearMap.id : (U ⧸ S) →ₗ[C] (U ⧸ S)) (o • coef q₀ • xb) = xb` using `hbz`. Rewrite `e1` using `[LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul C o, smul_smul, smul_smul]`. Conclude with `e1`. Establish `h2 : b * algebraMap O C o * coef q₀ = 1`.

Establish `h3 : (b * algebraMap O C o * coef q₀ - 1) • xb = 0`. Rewrite using `[sub_smul, h1, one_smul, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hxb0)`. Establish `h4 : b * algebraMap O C o = (coef q₀)⁻¹` using `eq_inv_of_mul_eq_one_left h2`. Use `show (v (coef q₀))⁻¹ ≤ v b`.

Rewrite using `[← map_inv₀, ← h4, map_mul]`. Conclude with `mul_le_of_le_one_right (by positivity) (hv.map_le_one o)`.
-/
theorem _root_.GlobalTheory.HTLat.exists_grAt_eq {v : Valuation C ℝ≥0} (hv : v.Integers O)
    {La : Submodule O U} (hfg : La.FG)
    (f : Fin N → U) (i : Fin N) (hf : f i ∉ _root_.GlobalTheory.HTLat.step C f i) {a : C}
    (ha : a ≠ 0) {y : U} (hy : y ∈ _root_.GlobalTheory.HTLat.step C f i)
    (hLa : a • f i + y ∈ La) :
    ∃ c : C, c ≠ 0 ∧ _root_.GlobalTheory.HTLat.grAt C La f i =
        Submodule.span O {c • (_root_.GlobalTheory.HTLat.step C f i).mkQ (f i)} ∧
      _root_.GlobalTheory.HTLat.grNorm v La f i = (v c)⁻¹ := by
  classical
  set S := _root_.GlobalTheory.HTLat.step C f i with hS
  set S' := _root_.GlobalTheory.HTLat.step C f (i + 1) with hS'
  set xb := S.mkQ (f i) with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hf
  have hSS' : S ≤ S' := _root_.GlobalTheory.HTLat.step_mono f (Nat.le_succ _)
  have hfi : f i ∈ S' := _root_.GlobalTheory.HTLat.mem_step_succ f i
  have hS'le : S' ≤ S ⊔ C ∙ f i := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [Fin.ext hk]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hG : ∀ q ∈ _root_.GlobalTheory.HTLat.grAt C La f i, ∃ b : C, q = b • xb := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hS'le hw.2)
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 ht
    refine ⟨b, ?_⟩
    show S.mkQ w = b • S.mkQ (f i)
    rw [← hst, map_add, map_smul, Submodule.mkQ_apply S s,
      (Submodule.Quotient.mk_eq_zero S).2 hs, zero_add]
  have hmem : a • xb ∈ _root_.GlobalTheory.HTLat.grAt C La f i := by
    refine Submodule.mem_map.2 ⟨a • f i + y, ⟨hLa, ?_⟩, ?_⟩
    · exact S'.add_mem (S'.smul_mem a hfi) (hSS' hy)
    · show S.mkQ (a • f i + y) = a • S.mkQ (f i)
      rw [map_add, map_smul, Submodule.mkQ_apply S y, (Submodule.Quotient.mk_eq_zero S).2 hy,
        add_zero]
  have hGfg : (_root_.GlobalTheory.HTLat.grAt C La f i).FG :=
    (_root_.GlobalTheory.HTLat.fg_inf hv hfg S').map _
  obtain ⟨s, hs⟩ := hGfg
  choose! coef hcoef using hG
  have hsG : ∀ q ∈ s, q ∈ _root_.GlobalTheory.HTLat.grAt C La f i := fun q hq =>
    hs ▸ Submodule.subset_span hq
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    rw [← hs, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  obtain ⟨q₀, hq₀, hmax⟩ := s.exists_max_image (fun q => v (coef q)) hsne
  have hc : coef q₀ ≠ 0 := by
    intro hc0
    have hzero : ∀ q ∈ (s : Set (U ⧸ S)), q = 0 := by
      intro q hq
      have h1 := hmax q hq
      rw [hc0, map_zero, nonpos_iff_eq_zero, Valuation.zero_iff] at h1
      rw [hcoef q (hsG q hq), h1, zero_smul]
    have hbot : _root_.GlobalTheory.HTLat.grAt C La f i = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      exact hzero
    rw [hbot, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  have hspan : _root_.GlobalTheory.HTLat.grAt C La f i = Submodule.span O {coef q₀ • xb} := by
    apply le_antisymm
    · rw [← hs, Submodule.span_le]
      intro q hq
      have hle : v (coef q / coef q₀) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax q hq) (by positivity)
      obtain ⟨o, ho⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨o, ?_⟩
      rw [← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hc, ← hcoef q (hsG q hq)]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        ← hcoef q₀ (hsG q₀ hq₀)]
      exact hsG q₀ hq₀
  refine ⟨coef q₀, hc, hspan, ?_⟩
  show _root_.GlobalTheory.HTLat.latNorm v (_root_.GlobalTheory.HTLat.grAt C La f i) xb = _
  rw [hspan]
  unfold _root_.GlobalTheory.HTLat.latNorm _root_.GlobalTheory.HTLat.scaleLat
  refine IsLeast.csInf_eq ⟨⟨(coef q₀)⁻¹, ?_, map_inv₀ v _⟩, ?_⟩
  · refine Submodule.mem_map.2 ⟨coef q₀ • xb, Submodule.mem_span_singleton_self _, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro r ⟨b, hb, rfl⟩
    obtain ⟨z, hz, hbz⟩ := Submodule.mem_map.1 hb
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h1 : (b * algebraMap O C o * coef q₀) • xb = xb := by
      have e1 : (b • LinearMap.id : (U ⧸ S) →ₗ[C] (U ⧸ S)) (o • coef q₀ • xb) = xb := hbz
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul C o, smul_smul,
        smul_smul] at e1
      exact e1
    have h2 : b * algebraMap O C o * coef q₀ = 1 := by
      have h3 : (b * algebraMap O C o * coef q₀ - 1) • xb = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hxb0)
    have h4 : b * algebraMap O C o = (coef q₀)⁻¹ := eq_inv_of_mul_eq_one_left h2
    show (v (coef q₀))⁻¹ ≤ v b
    rw [← map_inv₀, ← h4, map_mul]
    exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)

structure AdaptedFrame (W U₁ : Submodule C U) (N j : ℕ) where

  f : Fin N → U
  indep : LinearIndependent C f
  le : j ≤ N
  step_j : step C f j = W
  step_N : step C f N = U₁

/- English proof (translation)
The claim follows from `F.indep.notMem_span_image (by simp)`.
-/
theorem AdaptedFrame.notMem_step {W U₁ : Submodule C U} {j : ℕ} (F : AdaptedFrame W U₁ N j)
    (i : Fin N) : F.f i ∉ step C F.f i :=
  F.indep.notMem_span_image (by simp)

/- English proof (translation)
Establish `h1 : F.f '' {k | (k : ℕ) < i} = Set.range (F.f ∘ Fin.castLE hi)`. Rewrite using `[Set.range_comp, Fin.range_castLE]`. Rewrite using `[step, h1, finrank_span_eq_card (F.indep.comp _ (Fin.castLE_injective hi)), Fintype.card_fin]`.
-/
theorem AdaptedFrame.finrank_step {W U₁ : Submodule C U} {j : ℕ} (F : AdaptedFrame W U₁ N j)
    {i : ℕ} (hi : i ≤ N) : Module.finrank C (step C F.f i) = i := by
  have h1 : F.f '' {k | (k : ℕ) < i} = Set.range (F.f ∘ Fin.castLE hi) := by
    rw [Set.range_comp, Fin.range_castLE]
  rw [step, h1, finrank_span_eq_card (F.indep.comp _ (Fin.castLE_injective hi)), Fintype.card_fin]

def stdFrame (C : Type) [Field C] (N j : ℕ) (hj : j ≤ N) :
    AdaptedFrame (step C (Pi.basisFun C (Fin N)) j) ⊤ N j where
  f := Pi.basisFun C (Fin N)
  indep := (Pi.basisFun C (Fin N)).linearIndependent
  le := hj
  step_j := rfl
  step_N := by
    have : {k : Fin N | (k : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun k => k.2
    rw [step, this, Set.image_univ, Module.Basis.span_eq]

/- English proof (translation)
Establish `: FiniteDimensional C W` using `Submodule.finiteDimensional_of_le h`. Take `⟨Q, hQ⟩` from `(W.comap U₁.subtype).exists_isCompl`. Establish `hj : Module.finrank C (W.comap U₁.subtype) = Module.finrank C W` using `(Submodule.comapSubtypeEquivOfLe h).finrank_eq`. Establish `hN : Module.finrank C W + Module.finrank C Q = Module.finrank C U₁`. Rewrite using `[← hj]`.

Conclude with `Submodule.finrank_add_eq_of_isCompl hQ`. Set `b₁` to `Module.finBasisOfFinrankEq C _ hj`. Set `b₂` to `Module.finBasis C Q`. Set `b` to `((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ hQ)).reindex (finSumFinEquiv.trans (finCongr hN))`. Establish `hb : ∀ k, (U₁.subtype ∘ b) ((finSumFinEquiv.trans (finCongr hN)) (Sum.inl k)) = (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) (b₁ k)` using `fun k => by simp [b]`.

Use `⟨⟨U₁.subtype ∘ b, b.linearIndependent.map' _ U₁.ker_subtype, by omega, ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (U₁.subtype ∘ b) '' {k | (k : ℕ) < Module.finrank C W} = (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) '' Set.range b₁`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`.

Use `⟨_, ⟨⟨k, hk⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hb ⟨k, hk⟩).symm.trans (congrArg (U₁.subtype ∘ b) (Fin.ext rfl))`. Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨(finSumFinEquiv.trans (finCongr hN)) (Sum.inl k), k.2, hb k⟩`. Rewrite using `[step, h1, ← Submodule.map_span, b₁.span_eq, Submodule.map_comp, Submodule.map_subtype_top, Submodule.map_comap_subtype, inf_eq_right.2 h]`.

Establish `: {k : Fin (Module.finrank C U₁) | (k : ℕ) < Module.finrank C U₁} = Set.univ` using `Set.eq_univ_of_forall fun k => k.2`. Rewrite using `[← map_step, step, this, Set.image_univ, b.span_eq, Submodule.map_subtype_top]`.
-/
theorem nonempty_adaptedFrame {W U₁ : Submodule C U} (h : W ≤ U₁) [FiniteDimensional C U₁] :
    Nonempty (AdaptedFrame W U₁ (Module.finrank C U₁) (Module.finrank C W)) := by
  have : FiniteDimensional C W := Submodule.finiteDimensional_of_le h
  obtain ⟨Q, hQ⟩ := (W.comap U₁.subtype).exists_isCompl
  have hj : Module.finrank C (W.comap U₁.subtype) = Module.finrank C W :=
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  have hN : Module.finrank C W + Module.finrank C Q = Module.finrank C U₁ := by
    rw [← hj]; exact Submodule.finrank_add_eq_of_isCompl hQ
  let b₁ := Module.finBasisOfFinrankEq C _ hj
  let b₂ := Module.finBasis C Q
  let b := ((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ hQ)).reindex
    (finSumFinEquiv.trans (finCongr hN))
  have hb : ∀ k, (U₁.subtype ∘ b) ((finSumFinEquiv.trans (finCongr hN)) (Sum.inl k)) =
      (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) (b₁ k) := fun k => by simp [b]
  refine ⟨⟨U₁.subtype ∘ b, b.linearIndependent.map' _ U₁.ker_subtype, by omega, ?_, ?_⟩⟩
  · have h1 : (U₁.subtype ∘ b) '' {k | (k : ℕ) < Module.finrank C W} =
        (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) '' Set.range b₁ := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨_, ⟨⟨k, hk⟩, rfl⟩, ?_⟩
        exact (hb ⟨k, hk⟩).symm.trans (congrArg (U₁.subtype ∘ b) (Fin.ext rfl))
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨(finSumFinEquiv.trans (finCongr hN)) (Sum.inl k), k.2, hb k⟩
    rw [step, h1, ← Submodule.map_span, b₁.span_eq, Submodule.map_comp, Submodule.map_subtype_top,
      Submodule.map_comap_subtype, inf_eq_right.2 h]
  · have : {k : Fin (Module.finrank C U₁) | (k : ℕ) < Module.finrank C U₁} = Set.univ :=
      Set.eq_univ_of_forall fun k => k.2
    rw [← map_step, step, this, Set.image_univ, b.span_eq, Submodule.map_subtype_top]

def logAbs_vp (p : ℕ) (v : Valuation C ℝ≥0) (r : ℝ≥0) : ℝ :=
  -(Real.log p * (Real.log r / Real.log (v (p : C))))

/- English proof (translation)
Rewrite using `[logAbs_vp, logAbs_vp, logAbs_vp, NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 hr) (NNReal.coe_ne_zero.2 hs)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logAbs_vp_mul (p : ℕ) (v : Valuation C ℝ≥0) {r s : ℝ≥0} (hr : r ≠ 0) (hs : s ≠ 0) :
    logAbs_vp p v (r * s) = logAbs_vp p v r + logAbs_vp p v s := by
  rw [logAbs_vp, logAbs_vp, logAbs_vp, NNReal.coe_mul,
    Real.log_mul (NNReal.coe_ne_zero.2 hr) (NNReal.coe_ne_zero.2 hs)]
  ring

/- English proof (translation)
Establish `: Real.log (v (p : C)) ≠ 0` using `(Real.log_neg (NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)) (by exact_mod_cast h1)).ne`. Rewrite using `[logAbs_vp, div_self this, mul_one]`.
-/
theorem logAbs_vp_self (p : ℕ) (v : Valuation C ℝ≥0) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1) :
    logAbs_vp p v (v (p : C)) = -Real.log p := by
  have : Real.log (v (p : C)) ≠ 0 :=
    (Real.log_neg (NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)) (by exact_mod_cast h1)).ne
  rw [logAbs_vp, div_self this, mul_one]

/- English proof (translation)
Establish `: Real.log p ≠ 0` using `(Real.log_pos (by exact_mod_cast hp)).ne'`. Rewrite using `[logAbs_vp, h, NNReal.coe_inv, NNReal.coe_natCast, Real.log_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem logAbs_vp_of_normalised {p : ℕ} (hp : 1 < p) (v : Valuation C ℝ≥0)
    (h : v (p : C) = (p : ℝ≥0)⁻¹) (r : ℝ≥0) : logAbs_vp p v r = Real.log r := by
  have : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [logAbs_vp, h, NNReal.coe_inv, NNReal.coe_natCast, Real.log_inv]
  field_simp

variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']

def phiAt_vp (p : ℕ) (v : Valuation C ℝ≥0) (al : U →ₗ[C] U') (LW : Submodule O U)
    (Lom : Submodule O U') (f : Fin N → U) (j : ℕ) (lam : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, lam i * logAbs_vp p v
    (if (i : ℕ) < j then grNorm v LW f i else grNorm v Lom (al ∘ f) i)

/- English proof (translation)
Rewrite using `[← map_step]`. Introduce and unpack `⟨y, hy, e⟩`. Establish `hU : ∀ k, k ≤ N → step C F.f k ≤ U₁` using `fun k hk => (step_mono F.f hk).trans F.step_N.le`. Establish `h1 : F.f i - y ∈ step C F.f j`. Rewrite using `[F.step_j]`.

Use `⟨?_, U₁.sub_mem (hU _ i.2 (mem_step_succ F.f i)) (hU _ i.2.le hy)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `al (F.f i - y) = 0`. Rewrite using `[map_sub, e]`. Conclude with `sub_self _`. Conclude with `F.notMem_step i (by simpa using Submodule.add_mem _ (step_mono F.f hi h1) hy)`.
-/
theorem AdaptedFrame.map_notMem_step (al : U →ₗ[C] U') {U₁ : Submodule C U} {j : ℕ}
    (F : AdaptedFrame (LinearMap.ker al ⊓ U₁) U₁ N j) (i : Fin N) (hi : j ≤ i) :
    (al ∘ F.f) i ∉ step C (al ∘ F.f) i := by
  rw [← map_step]
  rintro ⟨y, hy, e⟩
  have hU : ∀ k, k ≤ N → step C F.f k ≤ U₁ := fun k hk => (step_mono F.f hk).trans F.step_N.le
  have h1 : F.f i - y ∈ step C F.f j := by
    rw [F.step_j]
    refine ⟨?_, U₁.sub_mem (hU _ i.2 (mem_step_succ F.f i)) (hU _ i.2.le hy)⟩
    change al (F.f i - y) = 0
    rw [map_sub, e]
    exact sub_self _
  exact F.notMem_step i (by simpa using Submodule.add_mem _ (step_mono F.f hi h1) hy)

/- English proof (translation)
Establish `hp : (p : C) ≠ 0` using `fun h => h0 (by rw [h, map_zero])`. Establish `h2` using `latNorm_span_singleton hv (smul_ne_zero (inv_ne_zero hp) hx) (p : C)`. Rewrite `h2` using `[smul_smul, mul_inv_cancel₀ hp, one_smul]`. Rewrite using `[h2, one_mul, logAbs_vp_self p v h0 h1]`.
-/
example (p : ℕ) (v : Valuation C ℝ≥0) (hv : v.Integers O) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1)
    (x : U) (hx : x ≠ 0) :
    1 * logAbs_vp p v (latNorm v (Submodule.span O {(p : C)⁻¹ • x}) x) = -Real.log p := by
  have hp : (p : C) ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have h2 := latNorm_span_singleton hv (smul_ne_zero (inv_ne_zero hp) hx) (p : C)
  rw [smul_smul, mul_inv_cancel₀ hp, one_smul] at h2
  rw [h2, one_mul, logAbs_vp_self p v h0 h1]

end Frames

end GlobalTheory.HTLat
