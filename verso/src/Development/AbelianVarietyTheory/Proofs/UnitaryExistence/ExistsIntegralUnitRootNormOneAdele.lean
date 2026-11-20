import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdLat.UnitRoot

section quad
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2`. Rewrite using `[← h2]`. Conclude with `AlgEquiv.card_le`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `: 2 < Fintype.card (E ≃ₐ[F] E)` using `Fintype.two_lt_card_iff.2 ⟨f, 1, c, h.1, h.2, hc.symm⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_or (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (f : E ≃ₐ[F] E) : f = 1 ∨ f = c := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← h2]; exact AlgEquiv.card_le
  by_contra h
  push Not at h
  have : 2 < Fintype.card (E ≃ₐ[F] E) :=
    Fintype.two_lt_card_iff.2 ⟨f, 1, c, h.1, h.2, hc.symm⟩
  omega

/- English proof (translation)
Break down `eq_one_or c h2 hc (c * c) with h | h` into its components or cases. Conclude with `congrArg (fun g : E ≃ₐ[F] E => g x) h`. Conclude with `absurd (mul_left_cancel (a := c) (h.trans (mul_one c).symm)) hc`.
-/
theorem invol (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  rcases eq_one_or c h2 hc (c * c) with h | h
  · exact congrArg (fun g : E ≃ₐ[F] E => g x) h
  · exact absurd (mul_left_cancel (a := c) (h.trans (mul_one c).symm)) hc

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Use `haveI : IsGalois F E := inferInstance`. Take `⟨y, rfl⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).2 (fun f => by`. Break down `eq_one_or c h2 hc f with rfl | rfl` into its components or cases.

Both sides reduce to the same expression. Conclude with `hfix)`. Conclude with `⟨y, ⟨⟨y, (isIntegral_algebraMap_iff (algebraMap F E).injective).1 hx⟩, rfl⟩, rfl⟩`.
-/
theorem fixed_integral (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E)
    (hx : IsIntegral ℤ x) (hfix : c x = x) :
    ∃ y ∈ (algebraMap (𝓞 F) F).range, algebraMap F E y = x := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := inferInstance
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).2 (fun f => by
    rcases eq_one_or c h2 hc f with rfl | rfl
    · rfl
    · exact hfix)
  exact ⟨y, ⟨⟨y, (isIntegral_algebraMap_iff (algebraMap F E).injective).1 hx⟩, rfl⟩, rfl⟩

end quad

section inst
variable (F : Type) [Field F] [NumberField F]

abbrev IntAd : Type := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F

noncomputable def incl : IntAd F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := ⟨fun v => a v, Filter.Eventually.of_forall fun v => (a v).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_apply (a : IntAd F) (v) : incl F a v = a v := rfl

/- English proof (translation)
Introduce `a b h` and use `funext fun v => Subtype.ext (by rw [← incl_apply, ← incl_apply, h])`.
-/
theorem incl_injective : Function.Injective (incl F) := fun a b h =>
  funext fun v => Subtype.ext (by rw [← incl_apply, ← incl_apply, h])

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v => ⟨a v, ha v⟩, rfl⟩`.
-/
theorem exists_incl {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ b, incl F b = a := ⟨fun v => ⟨a v, ha v⟩, rfl⟩

noncomputable def primeAt (v : HeightOneSpectrum (𝓞 F)) : Ideal (IntAd F) :=
  (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).comap
    (Pi.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) v)

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' hx hy := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩) hx hy

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem _root_.GlobalTheory.AdLat.UnitRoot.mem_hatRing (z : _root_.GlobalTheory.AdLat.RA F E) :
    z ∈ _root_.GlobalTheory.AdLat.UnitRoot.hatRing F E ↔
      z ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := Iff.rfl

variable {F E}

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
variable {F E} in
/- English proof (translation)
Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨⟨c (a : E), a.2.map c.toAlgHom.toRingHom.toIntAlgHom⟩, rfl⟩`.
-/
theorem _root_.GlobalTheory.AdLat.UnitRoot.conj_mem (c : E ≃ₐ[F] E) :
    ∀ x ∈ Set.range (algebraMap (𝓞 E) E), c x ∈ Set.range (algebraMap (𝓞 E) E) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨c (a : E), a.2.map c.toAlgHom.toRingHom.toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Take `⟨x, rfl⟩` from `hx`. Take `⟨y, hy, hyx⟩` from `fixed_integral c h2 hc _ (RingOfIntegers.isIntegral_coe x) hfix`. Take `⟨b, hb⟩` from `exists_incl F (a := algebraMap F _ y * a) (fun v => adele_mul_integral F ((mem_range_iff_adele_integral F y).1 hy v) (ha v))`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hyx]`.
-/
theorem tmul_fixed (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E}
    (hx : x ∈ Set.range (algebraMap (𝓞 E) E)) (hfix : c x = x) :
    ∃ b, (a ⊗ₜ[F] x : RA F E) = incl F b ⊗ₜ[F] 1 := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, hy, hyx⟩ := fixed_integral c h2 hc _ (RingOfIntegers.isIntegral_coe x) hfix
  obtain ⟨b, hb⟩ := exists_incl F (a := algebraMap F _ y * a)
    (fun v => adele_mul_integral F ((mem_range_iff_adele_integral F y).1 hy v) (ha v))
  refine ⟨b, ?_⟩
  rw [hb, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hyx]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [sg_tmul, sg_tmul, invol c h2 hc]`. Consider the case `add y z h1 h2 => rw [map_add, map_add, h1, h2]`.
-/
theorem sg_sg (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [sg_tmul, sg_tmul, invol c h2 hc]
  | add y z h1 h2 => rw [map_add, map_add, h1, h2]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, x, hx, rfl⟩` from `hx`. Rewrite using `[sg_tmul, ← TensorProduct.tmul_add]`. Use `tmul_fixed c h2 hc ha ?_ (by rw [map_add, invol c h2 hc, add_comm])` and prove the remaining obligations.

Take `⟨s, hs⟩` from `conj_mem c x hx`. Take `⟨t, rfl⟩` from `hx`. Conclude with `⟨t + s, by rw [map_add, hs]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ h1 h2`.

Take `⟨a, ha⟩` from `h1`. Take `⟨b, hb⟩` from `h2`. Conclude with `⟨a + b, by rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hb]; ring⟩`. Consider the case `neg y _ h1`. Take `⟨a, ha⟩` from `h1`.

Conclude with `⟨-a, by rw [map_neg, map_neg, TensorProduct.neg_tmul, ← ha]; ring⟩`.
-/
theorem trace_mem (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z + sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, ← TensorProduct.tmul_add]
    refine tmul_fixed c h2 hc ha ?_ (by rw [map_add, invol c h2 hc, add_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t + s, by rw [map_add, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a + b, by rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hb]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨-a, by rw [map_neg, map_neg, TensorProduct.neg_tmul, ← ha]; ring⟩

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, x, hx, rfl⟩` from `hx`. Rewrite using `[sg_tmul, Algebra.TensorProduct.tmul_mul_tmul]`. Use `tmul_fixed c h2 hc (fun v => adele_mul_integral F (ha v) (ha v)) ?_ (by rw [map_mul, invol c h2 hc, mul_comm])` and prove the remaining obligations.

Take `⟨s, hs⟩` from `conj_mem c x hx`. Take `⟨t, rfl⟩` from `hx`. Conclude with `⟨t * s, by rw [map_mul, hs]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z hy hz h1 h3`.

Take `⟨a, ha⟩` from `h1`. Take `⟨b, hb⟩` from `h3`. Take `⟨d, hd⟩` from `trace_mem c h2 hc ((hatRing F E).mul_mem hy (galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) hz))`. Rewrite `hd` using `[map_mul, sg_sg c h2 hc]`. Conclude with `⟨a + b + d, by`.

Rewrite using `[map_add, map_add, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul, ← ha, ← hb, ← hd]`. Use the proof step `ring⟩`. Consider the case `neg y _ h1`. Take `⟨a, ha⟩` from `h1`. Conclude with `⟨a, by rw [map_neg, ← ha]; ring⟩`.
-/
theorem norm_mem (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z * sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    refine tmul_fixed c h2 hc (fun v => adele_mul_integral F (ha v) (ha v)) ?_
      (by rw [map_mul, invol c h2 hc, mul_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t * s, by rw [map_mul, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz h1 h3 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h3
    obtain ⟨d, hd⟩ := trace_mem c h2 hc ((hatRing F E).mul_mem hy
      (galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) hz))
    rw [map_mul, sg_sg c h2 hc] at hd
    exact ⟨a + b + d, by
      rw [map_add, map_add, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul,
        ← ha, ← hb, ← hd]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by rw [map_neg, ← ha]; ring⟩

variable (F E) in

noncomputable def adIn : IntAd F →+* hatRing F E :=
  ((Algebra.TensorProduct.includeLeftRingHom :
    FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict (hatRing F E)
    fun a => (mem_hatRing F E _).2 (tmul_mem_adelicCompletion_of_integral F (a := incl F a) (x := 1)
      (fun v => (a v).2) ⟨1, map_one _⟩)

noncomputable def conjHat (c : E ≃ₐ[F] E) : hatRing F E →+* hatRing F E :=
  ((sg (FiniteAdeleRing (𝓞 F) F) c : RA F E →+* RA F E).comp (hatRing F E).subtype).codRestrict _
    fun z => galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) z.2

variable (F E) in

noncomputable def intIn : 𝓞 E →+* hatRing F E :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) :
    E →+* RA F E).comp (algebraMap (𝓞 E) E)).codRestrict _
    fun a => one_tmul_mem_adelicCompletionOfElementSet F ⟨a, rfl⟩

end inst

end GlobalTheory.AdLat.UnitRoot

namespace GlobalTheory.AdLat
open UnitRoot

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hle` using `card_algHom_le_finrank (K := F) (M := E) (L := E)`. Rewrite `hle` using `[h2]`. Set `f : Fin 3 → (E →ₐ[F] E)` to `![AlgHom.id F E, (c : E →ₐ[F] E), ((c * c : E ≃ₐ[F] E) : E →ₐ[F] E)]`. Establish `hf : Function.Injective f`.

Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢`. Apply the tactic sequence `all_goals have hx := fun x => DFunLike.congr_fun hij x`. Apply the tactic sequence `all_goals simp only [AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom, AlgEquiv.mul_apply] at hx`. Apply the tactic sequence `all_goals first`.

Consider the case `exact hc (AlgEquiv.ext fun x => (hx x).symm)`. Consider the case `exact hc (AlgEquiv.ext fun x => hx x)`. Consider the case `exact h (AlgEquiv.ext fun x => (hx x).symm)`. Consider the case `exact h (AlgEquiv.ext fun x => hx x)`. Consider the case `exact hc (AlgEquiv.ext fun x => c.injective (hx x).symm)`.

Consider the case `exact hc (AlgEquiv.ext fun x => c.injective (hx x))`. Use `Nat.card_le_card_of_injective f hf` as an intermediate fact. Rewrite `this` using `[Nat.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma mul_self_eq_one_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) : c * c = 1 := by
  by_contra h
  have hle := card_algHom_le_finrank (K := F) (M := E) (L := E)
  rw [h2] at hle
  let f : Fin 3 → (E →ₐ[F] E) :=
    ![AlgHom.id F E, (c : E →ₐ[F] E), ((c * c : E ≃ₐ[F] E) : E →ₐ[F] E)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals have hx := fun x => DFunLike.congr_fun hij x
    all_goals simp only [AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom, AlgEquiv.mul_apply] at hx
    all_goals first
      | exact hc (AlgEquiv.ext fun x => (hx x).symm)
      | exact hc (AlgEquiv.ext fun x => hx x)
      | exact h (AlgEquiv.ext fun x => (hx x).symm)
      | exact h (AlgEquiv.ext fun x => hx x)
      | exact hc (AlgEquiv.ext fun x => c.injective (hx x).symm)
      | exact hc (AlgEquiv.ext fun x => c.injective (hx x))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at this
  omega

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Establish `hcc` using `mul_self_eq_one_of_quadratic c h2 hc`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Simplify using `only [_root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_algHom]`.

Rewrite using `[← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
private lemma sg_sg_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (z : _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
      (_root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  have hcc := mul_self_eq_one_of_quadratic c h2 hc
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [_root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.coe_algHom]
    rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Set `S : Set (𝓞 E)` to `{d | ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ d = t - s}`. Establish `htop : Ideal.span S = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ h`. Take `⟨t, s, hs, hts⟩` from `hP M hM`.

Conclude with `hts (hle (Ideal.subset_span ⟨t, s, hs, rfl⟩))`. Establish `h1 : (1 : 𝓞 E) ∈ Ideal.span S` using `htop ▸ Submodule.mem_top`. Take `⟨n, f, g, hfg⟩` from `Submodule.mem_span_set'.1 h1`. Use `choose t s hs ht using fun k => (g k).2`. Use `⟨n, f, t, s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfg]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, ht k]`.
-/
private lemma exists_sum_mul_sub_conj_eq_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    ∃ (n : ℕ) (r t s : Fin n → 𝓞 E), (∀ k, (s k : E) = c (t k : E)) ∧
      ∑ k, r k * (t k - s k) = 1 := by
  let S : Set (𝓞 E) := {d | ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ d = t - s}
  have htop : Ideal.span S = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨t, s, hs, hts⟩ := hP M hM
    exact hts (hle (Ideal.subset_span ⟨t, s, hs, rfl⟩))
  have h1 : (1 : 𝓞 E) ∈ Ideal.span S := htop ▸ Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 h1
  choose t s hs ht using fun k => (g k).2
  refine ⟨n, f, t, s, hs, ?_⟩
  rw [← hfg]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, ht k]

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Assume the negation of the conclusion as `hxb`. Establish `htop : IntermediateField.adjoin F {x} = ⊤`. Establish `hd : Module.finrank F (IntermediateField.adjoin F {x}) ∣ 2`. Rewrite using `[← h2]; exact IntermediateField.finrank_dvd_of_le_right le_top |>.trans (by simp)`. Break down `(Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1` into its components or cases.

Conclude with `absurd (IntermediateField.adjoin_simple_eq_bot_iff.1 (IntermediateField.finrank_eq_one_iff.1 h1)) hxb`. Apply `IntermediateField.eq_of_le_of_finrank_eq le_top` to reduce the goal to its premises. Rewrite using `[h1, IntermediateField.finrank_top', h2]`. Apply `hc` to reduce the goal to its premises. Establish `hx' : Algebra.adjoin F {x} = ⊤`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic x), htop]`. Both sides reduce to the same expression. Use `AlgHom.ext_of_adjoin_eq_top (φ₁ := (c : E →ₐ[F] E)) (φ₂ := AlgHom.id F E) hx' (by simpa using hx)` as an intermediate fact. Use extensionality with `y`. Conclude with `DFunLike.congr_fun this y`.
-/
private lemma mem_bot_of_fixed_of_quadratic {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (x : E) (hx : c x = x) : x ∈ (⊥ : IntermediateField F E) := by
  by_contra hxb
  have htop : IntermediateField.adjoin F {x} = ⊤ := by
    have hd : Module.finrank F (IntermediateField.adjoin F {x}) ∣ 2 := by
      rw [← h2]; exact IntermediateField.finrank_dvd_of_le_right le_top |>.trans (by simp)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact absurd (IntermediateField.adjoin_simple_eq_bot_iff.1
        (IntermediateField.finrank_eq_one_iff.1 h1)) hxb
    · apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [h1, IntermediateField.finrank_top', h2]
  apply hc
  have hx' : Algebra.adjoin F {x} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), htop]
    rfl
  have := AlgHom.ext_of_adjoin_eq_top (φ₁ := (c : E →ₐ[F] E)) (φ₂ := AlgHom.id F E) hx'
    (by simpa using hx)
  ext y
  exact DFunLike.congr_fun this y

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Take `⟨f, rfl⟩` from `IntermediateField.mem_bot.1 (mem_bot_of_fixed_of_quadratic c h2 hc x hx)`. Take `⟨y, hy⟩` from `hint`. Use `⟨⟨f, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `: IsIntegral ℤ (algebraMap F E f)` using `hy ▸ y.2`. Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1 this`.
-/
private lemma exists_integer_of_fixed_integral {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (x : E) (hx : c x = x) (hint : x ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∃ f : 𝓞 F, algebraMap F E f = x := by
  obtain ⟨f, rfl⟩ := IntermediateField.mem_bot.1 (mem_bot_of_fixed_of_quadratic c h2 hc x hx)
  obtain ⟨y, hy⟩ := hint
  refine ⟨⟨f, ?_⟩, rfl⟩
  have : IsIntegral ℤ (algebraMap F E f) := hy ▸ y.2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1 this

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Establish `hcc` using `mul_self_eq_one_of_quadratic c h2 hc`. Establish `hfix : c (x + c x) = x + c x`.

Rewrite using `[map_add, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply, add_comm]`. Take `⟨y, rfl⟩` from `hx`. Take `⟨w, hw⟩` from `_root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨y, rfl⟩`. Take `⟨f, hf⟩` from `exists_integer_of_fixed_integral c h2 hc _ hfix ⟨y + w, by simp [hw]⟩`. Use `⟨algebraMap F _ (f : F) * a, hsm f a ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[show _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] algebraMap (𝓞 E) E y) = a ⊗ₜ[F] c (algebraMap (𝓞 E) E y) by`. Simplify using `[_root_.GlobalTheory.AdLat.sg], ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one,`. Use the proof step `TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]`. Consider the case `zero => exact ⟨0, h0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨n, hn, e⟩` from `hx`. Take `⟨m, hm, e'⟩` from `hy`. Conclude with `⟨n + m, hadd _ _ hn hm, by rw [map_add, TensorProduct.add_tmul, ← e, ← e']; abel⟩`. Consider the case `neg x _ hx`. Take `⟨n, hn, e⟩` from `hx`.

Conclude with `⟨-n, hneg _ hn, by rw [map_neg, TensorProduct.neg_tmul, ← e]; abel⟩`.
-/
private lemma exists_add_sg_eq_tmul_one_of_mem_closure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (P : FiniteAdeleRing (𝓞 F) F → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hneg : ∀ a, P a → P (-a)) (hsm : ∀ (f : 𝓞 F) a, P a → P (algebraMap F _ (f : F) * a))
    (z : _root_.GlobalTheory.AdLat.RA F E)
    (hz : z ∈ AddSubgroup.closure
      {z | ∃ a, P a ∧ ∃ x ∈ Set.range (algebraMap (𝓞 E) E), z = a ⊗ₜ[F] x}) :
    ∃ n, P n ∧ z + _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c z = n ⊗ₜ[F] (1 : E) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have hcc := mul_self_eq_one_of_quadratic c h2 hc
    have hfix : c (x + c x) = x + c x := by
      rw [map_add, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply, add_comm]
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨w, hw⟩ := _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨y, rfl⟩
    obtain ⟨f, hf⟩ := exists_integer_of_fixed_integral c h2 hc _ hfix ⟨y + w, by simp [hw]⟩
    refine ⟨algebraMap F _ (f : F) * a, hsm f a ha, ?_⟩
    rw [show _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
        (a ⊗ₜ[F] algebraMap (𝓞 E) E y) = a ⊗ₜ[F] c (algebraMap (𝓞 E) E y) by
      simp [_root_.GlobalTheory.AdLat.sg], ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
  | zero => exact ⟨0, h0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, e⟩ := hx
    obtain ⟨m, hm, e'⟩ := hy
    exact ⟨n + m, hadd _ _ hn hm, by rw [map_add, TensorProduct.add_tmul, ← e, ← e']; abel⟩
  | neg x _ hx =>
    obtain ⟨n, hn, e⟩ := hx
    exact ⟨-n, hneg _ hn, by rw [map_neg, TensorProduct.neg_tmul, ← e]; abel⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, h0, by simp⟩`. Consider the case `insert k s hk ih`. Take `⟨n, hn, e⟩` from `ih`. Establish `hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (b ⊗ₜ[F] x) = b ⊗ₜ[F] c x` using `fun b x => by`.

Simplify using `[_root_.GlobalTheory.AdLat.sg]`. Take `⟨cw, hcw⟩` from `_root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨w k, rfl⟩`. Establish `hfix : c ((w k : E) * c (w k : E)) = (w k : E) * c (w k : E)`. Rewrite using `[map_mul, ← AlgEquiv.mul_apply, mul_self_eq_one_of_quadratic c h2 hc, AlgEquiv.one_apply, mul_comm]`. Take `⟨f, hf⟩` from `exists_integer_of_fixed_integral c h2 hc _ hfix ⟨w k * cw, by simp [hcw]⟩`.

Establish `hmem : (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a k ⊗ₜ[F] (w k : E)) ∈ AddSubgroup.closure {z | ∃ a, P a ∧ ∃ x ∈ Set.range (algebraMap (𝓞 E) E), z = a ⊗ₜ[F] x}`. Rewrite using `[hσ, ← hcw, Finset.sum_mul]`. Use `AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Conclude with `⟨a j * a k, hmul _ _ (ha j) (ha k), _, ⟨w j * cw, rfl⟩, by`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, map_mul]⟩`.

Take `⟨m, hm, e'⟩` from `exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc P h0 hadd hneg hsm _ hmem`. Use `⟨n + m + algebraMap F _ (f : F) * (a k * a k), hadd _ _ (hadd _ _ hn hm) (hsm f _ (hmul _ _ (ha k) (ha k))), ?_⟩` and prove the remaining obligations. Establish `hN : (a k ⊗ₜ[F] (w k : E)) * (a k ⊗ₜ[F] c (w k : E)) = (algebraMap F _ (f : F) * (a k * a k)) ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]`. Rewrite using `[Finset.sum_insert hk, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul, ← e, ← e', map_mul, sg_sg_of_quadratic c h2 hc, hσ]`.

Take the linear combination `hN`.
-/
private lemma exists_norm_sum_tmul_eq_tmul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (P : FiniteAdeleRing (𝓞 F) F → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hneg : ∀ a, P a → P (-a)) (hsm : ∀ (f : 𝓞 F) a, P a → P (algebraMap F _ (f : F) * a))
    (hmul : ∀ a b, P a → P b → P (a * b)) {ι : Type} (s : Finset ι)
    (a : ι → FiniteAdeleRing (𝓞 F) F) (w : ι → 𝓞 E) (ha : ∀ k, P (a k)) :
    ∃ n, P n ∧ (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) *
      _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) =
        n ⊗ₜ[F] (1 : E) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | insert k s hk ih =>
    obtain ⟨n, hn, e⟩ := ih
    have hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
        (b ⊗ₜ[F] x) = b ⊗ₜ[F] c x := fun b x => by
      simp [_root_.GlobalTheory.AdLat.sg]
    obtain ⟨cw, hcw⟩ := _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨w k, rfl⟩
    have hfix : c ((w k : E) * c (w k : E)) = (w k : E) * c (w k : E) := by
      rw [map_mul, ← AlgEquiv.mul_apply, mul_self_eq_one_of_quadratic c h2 hc, AlgEquiv.one_apply, mul_comm]
    obtain ⟨f, hf⟩ := exists_integer_of_fixed_integral c h2 hc _ hfix ⟨w k * cw, by simp [hcw]⟩
    have hmem : (∑ k ∈ s, a k ⊗ₜ[F] (w k : E)) *
        _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a k ⊗ₜ[F] (w k : E)) ∈ AddSubgroup.closure
        {z | ∃ a, P a ∧ ∃ x ∈ Set.range (algebraMap (𝓞 E) E), z = a ⊗ₜ[F] x} := by
      rw [hσ, ← hcw, Finset.sum_mul]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ?_
      exact ⟨a j * a k, hmul _ _ (ha j) (ha k), _, ⟨w j * cw, rfl⟩, by
        rw [Algebra.TensorProduct.tmul_mul_tmul, map_mul]⟩
    obtain ⟨m, hm, e'⟩ := exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc P h0 hadd hneg hsm _ hmem
    refine ⟨n + m + algebraMap F _ (f : F) * (a k * a k),
      hadd _ _ (hadd _ _ hn hm) (hsm f _ (hmul _ _ (ha k) (ha k))), ?_⟩
    have hN : (a k ⊗ₜ[F] (w k : E)) * (a k ⊗ₜ[F] c (w k : E)) =
        (algebraMap F _ (f : F) * (a k * a k)) ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    rw [Finset.sum_insert hk, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul, ← e, ← e',
      map_mul, sg_sg_of_quadratic c h2 hc, hσ]
    linear_combination hN

open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc hP u hu hnorm`. Establish `hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (b ⊗ₜ[F] x) = b ⊗ₜ[F] c x` using `fun b x => by simp [_root_.GlobalTheory.AdLat.sg]`. Use `set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c with hσdef`. Establish `hcc` using `mul_self_eq_one_of_quadratic c h2 hc`. Establish `hσσ : ∀ z, σ (σ z) = z` using `sg_sg_of_quadratic c h2 hc`.

Take `⟨n, r, t, s, hs, hrts⟩` from `exists_sum_mul_sub_conj_eq_one c hP`. Set `X : Option (Fin n) → 𝓞 E` to `fun i => i.elim 1 t`. Set `CX : Option (Fin n) → 𝓞 E` to `fun i => i.elim 1 s`. Set `Y : Option (Fin n) → 𝓞 E` to `fun i => i.elim (-∑ k, r k * s k) r`. Apply the tactic sequence `have hCX : ∀ i, (CX i : E) = c (X i : E) := by rintro (_ | k) <;> simp [X, CX, hs]`.

Establish `hXY : ∑ i, Y i * X i = 1`. Rewrite using `[Fintype.sum_option, ← hrts]`. Simplify using `only [X, Y, Option.elim_none, Option.elim_some, mul_one, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hCXY : ∑ i, Y i * CX i = 0`.

Rewrite using `[Fintype.sum_option]`. Simplify using `only [CX, Y, Option.elim_none, Option.elim_some, mul_one]`. Rewrite using `[← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun k _ => by ring`. Set `ρ : 𝓞 E →+* _root_.GlobalTheory.AdLat.RA F E` to `(Algebra.TensorProduct.includeRight : E →ₐ[F] _root_.GlobalTheory.AdLat.RA F E).toRingHom.comp (algebraMap (𝓞 E) E)`.

Establish `hρ : ∀ x, ρ x = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E)` using `fun x => rfl`. Establish `hσX : ∀ i, σ (ρ (X i)) = ρ (CX i)` using `fun i => by rw [hρ, hσ, hρ, hCX]`. Establish `hσCX : ∀ i, σ (ρ (CX i)) = ρ (X i)` using `fun i => by`. Rewrite using `[hρ, hσ, hρ, hCX, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]`. Set `m : Option (Fin n) → _root_.GlobalTheory.AdLat.RA F E` to `fun i => ρ (X i) + u * ρ (CX i)`.

Establish `hum : ∀ i, u * σ (m i) = m i` using `fun i => by`. Simplify using `only [m, map_add, map_mul, hσX, hσCX]`. Take the linear combination `ρ (X i) * hnorm`. Set `H` to `_root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))`. Establish `hρmem : ∀ x, ρ x ∈ H` using `fun x => _root_.GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩`.

Establish `hmul : ∀ a b, a ∈ H → b ∈ H → a * b ∈ H` using `fun a b ha hb => _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by`. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`. Conclude with `⟨a * b, map_mul _ _ _⟩) ha hb`. Establish `hσmem : ∀ z ∈ H, σ z ∈ H` using `fun z hz => _root_.GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet F c (_root_.GlobalTheory.AdLat.UnitRoot.conj_mem c) hz`. Establish `hmmem : ∀ i, m i ∈ H` using `fun i => add_mem (hρmem _) (hmul _ _ hu (hρmem _))`.

Set `Pint : FiniteAdeleRing (𝓞 F) F → Prop` to `fun a => ∀ v, a v ∈ v.adicCompletionIntegers F`. Establish `hsmI : ∀ (f : 𝓞 F) a, Pint a → Pint (algebraMap F _ (f : F) * a)` using `fun f a ha v => _root_.GlobalTheory.AdLat.adele_mul_integral F ((_root_.GlobalTheory.AdLat.mem_range_iff_adele_integral F (f : F)).1 ⟨f, rfl⟩ v) (ha v)`. Establish `h0I : Pint 0` using `fun v => zero_mem _`. Establish `haddI : ∀ a b, Pint a → Pint b → Pint (a + b)` using `fun a b ha hb v => _root_.GlobalTheory.AdLat.adele_add_integral F (ha v) (hb v)`. Establish `hnegI : ∀ a, Pint a → Pint (-a)` using `fun a ha v => neg_mem (ha v)`.

Establish `hmulI : ∀ a b, Pint a → Pint b → Pint (a * b)` using `fun a b ha hb v => _root_.GlobalTheory.AdLat.adele_mul_integral F (ha v) (hb v)`. Establish `hp : ∀ i j, ∃ q, Pint q ∧ m i * σ (m j) = q ⊗ₜ[F] (1 : E)`. Introduce `i j`. Take `⟨q, hq, e⟩` from `exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc Pint h0I haddI hnegI hsmI (ρ (X i) * σ (m j)) (hmul _ _ (hρmem _) (hσmem _ (hmmem j)))`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e, map_mul, hσσ, hσX]`. Use `hum j` as an intermediate fact. Simplify using `only [m] at this ⊢`. Take the linear combination `ρ (CX i) * this`. Use `choose p hpint hpe using hp`.

Set `Pv : HeightOneSpectrum (𝓞 F) → FiniteAdeleRing (𝓞 F) F → Prop` to `fun v a => Pint a ∧ Valued.v (a v) < 1`. Establish `hkey : ∀ v, ∃ ij : Option (Fin n) × Option (Fin n), ¬ Valued.v (p ij.1 ij.2 v) < 1`. Introduce `v`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Use `choose cy hcy using fun j => _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨Y j, rfl⟩`. Establish `h1 : ∑ i, ρ (Y i) * m i = 1`. Simplify using `only [m, mul_add, Finset.sum_add_distrib, mul_left_comm _ u, ← Finset.mul_sum, ← map_mul, ← map_sum, hXY, hCXY, map_one, map_zero, mul_zero, add_zero]`. Establish `h1' : ∑ j, ρ (cy j) * σ (m j) = 1`. Use `congrArg σ h1` as an intermediate fact.

Rewrite `this` using `[map_sum, map_one]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hρ (Y j), hσ, ← hcy]`. Both sides reduce to the same expression.

Establish `hZ : ∑ ij : Option (Fin n) × Option (Fin n), p ij.1 ij.2 ⊗ₜ[F] ((Y ij.1 * cy ij.2 : 𝓞 E) : E) = 1`. Rewrite using `[← mul_one (1 : _root_.GlobalTheory.AdLat.RA F E)]`. Use `nth_rewrite 1 [← h1]`. Rewrite using `[← h1', Finset.sum_mul_sum, ← Finset.sum_product']`. Use `Finset.sum_congr rfl fun ij _ => ?_` and prove the remaining obligations.

Rewrite using `[show ρ (Y ij.1) * m ij.1 * (ρ (cy ij.2) * σ (m ij.2)) = ρ (Y ij.1 * cy ij.2) * (m ij.1 * σ (m ij.2)) by rw [map_mul]; ring, hpe, hρ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Establish `h0v : Pv v 0` using `⟨h0I, by show Valued.v (0 : v.adicCompletion F) < 1`. Rewrite using `[map_zero]`. Conclude with `zero_lt_one⟩`. Establish `haddv : ∀ a b, Pv v a → Pv v b → Pv v (a + b)` using `fun a b ha hb => ⟨haddI a b ha.1 hb.1, by show Valued.v (a v + b v) < 1`.

Conclude with `Valuation.map_add_lt _ ha.2 hb.2⟩`. Establish `hnegv : ∀ a, Pv v a → Pv v (-a)` using `fun a ha => ⟨hnegI a ha.1, by show Valued.v (-(a v)) < 1`. Rewrite using `[Valuation.map_neg]`. Conclude with `ha.2⟩`. Establish `hmulv : ∀ a b, Pint a → Pv v b → Pv v (a * b)` using `fun a b ha hb => ⟨hmulI a b ha hb.1, by show Valued.v (a v * b v) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (ha v))) hb.2⟩`. Establish `hPv : ∀ ij : Option (Fin n) × Option (Fin n), Pv v (p ij.1 ij.2)` using `fun ij => ⟨hpint ij.1 ij.2, hcon ij⟩`. Use `clear_value m ρ H X CX Y`. Take `⟨N, hN, eN⟩` from `exists_norm_sum_tmul_eq_tmul_one c h2 hc (Pv v) h0v haddv hnegv (fun f a ha => by`.

Use `hmulv _ a (hsmI f 1 (_root_.GlobalTheory.AdLat.adele_one_integral F)) ha` as an intermediate fact. Rewrite using `[mul_one] at this)` and apply the resulting hypothesis. Use the proof step `(fun a b ha hb => hmulv a b ha.1 hb) Finset.univ`. Use the proof step `(fun ij : Option (Fin n) × Option (Fin n) => p ij.1 ij.2)`. Use the proof step `(fun ij : Option (Fin n) × Option (Fin n) => Y ij.1 * cy ij.2) hPv`.

Use `beta_reduce at eN`. Rewrite `eN` using `[hZ, map_one, mul_one, Algebra.TensorProduct.one_def]`. Establish `hN1 : N = 1` using `(Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) (algebraMap F E).injective eN).symm`. Use `hN.2` as an intermediate fact. Rewrite `this` using `[hN1]`.

Conclude with `absurd this (by show ¬ Valued.v (1 : v.adicCompletion F) < 1`. Rewrite using `[map_one]`. Conclude with `lt_irrefl 1)`. Use `choose ij hij using hkey`. Establish `hval1 : ∀ v, Valued.v (p (ij v).1 (ij v).2 v) = 1` using `fun v => le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hpint _ _ v)) (not_lt.1 (hij v))`.

Establish `hne : ∀ v, p (ij v).1 (ij v).2 v ≠ 0` using `fun v h => by`. Use `hval1 v` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Establish `hE0 : ∀ (q : Option (Fin n) × Option (Fin n)) (v : HeightOneSpectrum (𝓞 F)), (if ij v = q then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F`.

Introduce `q v`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `hD0 : ∀ v : HeightOneSpectrum (𝓞 F), (p (ij v).1 (ij v).2 v)⁻¹ ∈ v.adicCompletionIntegers F` using `fun v => by`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval1, inv_one]`. Set `e : Option (Fin n) × Option (Fin n) → FiniteAdeleRing (𝓞 F) F` to `fun q => ⟨fun v => if ij v = q then 1 else 0, Filter.Eventually.of_forall fun v => hE0 q v⟩`. Set `d : FiniteAdeleRing (𝓞 F) F` to `⟨fun v => (p (ij v).1 (ij v).2 v)⁻¹, Filter.Eventually.of_forall hD0⟩`. Establish `heI : ∀ q, Pint (e q)` using `fun q v => hE0 q v`. Establish `hdI : Pint d` using `hD0`.

Set `ev : ∀ v : HeightOneSpectrum (𝓞 F), FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F` to `fun v => { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Establish `hsum1 : d * ∑ q : Option (Fin n) × Option (Fin n), ∑ q' : Option (Fin n) × Option (Fin n), e q * e q' * p q.1 q'.2 = 1`. Apply `FiniteAdeleRing.ext F` to reduce the goal to its premises. Introduce `v`. Use `map_sum (ev v) (fun q => ∑ q' : Option (Fin n) × Option (Fin n), e q * e q' * p q.1 q'.2) Finset.univ` as an intermediate fact.

Use `show d v * (ev v) _ = 1`. Rewrite using `[this]`. Establish `hevv : ∀ a : FiniteAdeleRing (𝓞 F) F, ev v a = a v` using `fun _ => rfl`. Establish `hev : ∀ q, e q v = if ij v = q then 1 else 0` using `fun _ => rfl`. Establish `hdv : d v = (p (ij v).1 (ij v).2 v)⁻¹` using `rfl`.

Simplify using `only [map_sum, map_mul]`. Simplify using `only [hevv, hev, hdv, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `inv_mul_cancel₀ (hne v)`. Use `⟨∑ q, (e q ⊗ₜ[F] (1 : E)) * m q.1, ?_, ⟨(d ⊗ₜ[F] (1 : E)) * ∑ q, (e q ⊗ₜ[F] (1 : E)) * σ (m q.2), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.sum_mem _ fun q _ => hmul _ _ (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hmmem _)`.

Conclude with `hmul _ _ (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F hdI ⟨1, map_one _⟩) (AddSubgroup.sum_mem _ fun q _ => hmul _ _ (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hσmem _ (hmmem _)))`. Rewrite using `[mul_left_comm, Finset.sum_mul_sum]`. Establish `hterm : ∀ q q' : Option (Fin n) × Option (Fin n), (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) = (e q * e q' * p q.1 q'.2) ⊗ₜ[F] (1 : E)` using `fun q q' => by`. Rewrite using `[show (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) = (e q ⊗ₜ[F] (1 : E)) * (e q' ⊗ₜ[F] (1 : E)) * (m q.1 * σ (m q'.2)) by ring, hpe, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]`. Simplify using `only [hterm, ← TensorProduct.sum_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsum1]`.

Both sides reduce to the same expression. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hσ, map_one, mul_left_comm, hum]`.
-/
theorem _root_.GlobalTheory.AdLat.exists_integral_unit_root : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP u hu hnorm
  classical
  have hσ : ∀ b (x : E), _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (b ⊗ₜ[F] x) =
      b ⊗ₜ[F] c x := fun b x => by simp [_root_.GlobalTheory.AdLat.sg]
  set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c with hσdef
  have hcc := mul_self_eq_one_of_quadratic c h2 hc
  have hσσ : ∀ z, σ (σ z) = z := sg_sg_of_quadratic c h2 hc
  obtain ⟨n, r, t, s, hs, hrts⟩ := exists_sum_mul_sub_conj_eq_one c hP
  let X : Option (Fin n) → 𝓞 E := fun i => i.elim 1 t
  let CX : Option (Fin n) → 𝓞 E := fun i => i.elim 1 s
  let Y : Option (Fin n) → 𝓞 E := fun i => i.elim (-∑ k, r k * s k) r
  have hCX : ∀ i, (CX i : E) = c (X i : E) := by rintro (_ | k) <;> simp [X, CX, hs]
  have hXY : ∑ i, Y i * X i = 1 := by
    rw [Fintype.sum_option, ← hrts]
    simp only [X, Y, Option.elim_none, Option.elim_some, mul_one, mul_sub, Finset.sum_sub_distrib]
    ring
  have hCXY : ∑ i, Y i * CX i = 0 := by
    rw [Fintype.sum_option]
    simp only [CX, Y, Option.elim_none, Option.elim_some, mul_one]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  let ρ : 𝓞 E →+* _root_.GlobalTheory.AdLat.RA F E :=
    (Algebra.TensorProduct.includeRight : E →ₐ[F] _root_.GlobalTheory.AdLat.RA F E).toRingHom.comp
      (algebraMap (𝓞 E) E)
  have hρ : ∀ x, ρ x = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) := fun x => rfl
  have hσX : ∀ i, σ (ρ (X i)) = ρ (CX i) := fun i => by rw [hρ, hσ, hρ, hCX]
  have hσCX : ∀ i, σ (ρ (CX i)) = ρ (X i) := fun i => by
    rw [hρ, hσ, hρ, hCX, ← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  let m : Option (Fin n) → _root_.GlobalTheory.AdLat.RA F E := fun i => ρ (X i) + u * ρ (CX i)
  have hum : ∀ i, u * σ (m i) = m i := fun i => by
    simp only [m, map_add, map_mul, hσX, hσCX]
    linear_combination ρ (X i) * hnorm
  let H := _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))
  have hρmem : ∀ x, ρ x ∈ H := fun x => _root_.GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  have hmul : ∀ a b, a ∈ H → b ∈ H → a * b ∈ H := fun a b ha hb =>
    _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩) ha hb
  have hσmem : ∀ z ∈ H, σ z ∈ H := fun z hz =>
    _root_.GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet F c (_root_.GlobalTheory.AdLat.UnitRoot.conj_mem c) hz
  have hmmem : ∀ i, m i ∈ H := fun i => add_mem (hρmem _) (hmul _ _ hu (hρmem _))
  let Pint : FiniteAdeleRing (𝓞 F) F → Prop := fun a => ∀ v, a v ∈ v.adicCompletionIntegers F
  have hsmI : ∀ (f : 𝓞 F) a, Pint a → Pint (algebraMap F _ (f : F) * a) := fun f a ha v =>
    _root_.GlobalTheory.AdLat.adele_mul_integral F
      ((_root_.GlobalTheory.AdLat.mem_range_iff_adele_integral F (f : F)).1 ⟨f, rfl⟩ v) (ha v)
  have h0I : Pint 0 := fun v => zero_mem _
  have haddI : ∀ a b, Pint a → Pint b → Pint (a + b) := fun a b ha hb v =>
    _root_.GlobalTheory.AdLat.adele_add_integral F (ha v) (hb v)
  have hnegI : ∀ a, Pint a → Pint (-a) := fun a ha v => neg_mem (ha v)
  have hmulI : ∀ a b, Pint a → Pint b → Pint (a * b) := fun a b ha hb v =>
    _root_.GlobalTheory.AdLat.adele_mul_integral F (ha v) (hb v)
  have hp : ∀ i j, ∃ q, Pint q ∧ m i * σ (m j) = q ⊗ₜ[F] (1 : E) := by
    intro i j
    obtain ⟨q, hq, e⟩ := exists_add_sg_eq_tmul_one_of_mem_closure c h2 hc Pint h0I haddI hnegI hsmI (ρ (X i) * σ (m j))
      (hmul _ _ (hρmem _) (hσmem _ (hmmem j)))
    refine ⟨q, hq, ?_⟩
    rw [← e, map_mul, hσσ, hσX]
    have := hum j
    simp only [m] at this ⊢
    linear_combination ρ (CX i) * this
  choose p hpint hpe using hp
  let Pv : HeightOneSpectrum (𝓞 F) → FiniteAdeleRing (𝓞 F) F → Prop := fun v a =>
    Pint a ∧ Valued.v (a v) < 1
  have hkey : ∀ v, ∃ ij : Option (Fin n) × Option (Fin n), ¬ Valued.v (p ij.1 ij.2 v) < 1 := by
    intro v
    by_contra hcon
    push_neg at hcon
    choose cy hcy using fun j => _root_.GlobalTheory.AdLat.UnitRoot.conj_mem c _ ⟨Y j, rfl⟩
    have h1 : ∑ i, ρ (Y i) * m i = 1 := by
      simp only [m, mul_add, Finset.sum_add_distrib, mul_left_comm _ u, ← Finset.mul_sum,
        ← map_mul, ← map_sum, hXY, hCXY, map_one, map_zero, mul_zero, add_zero]
    have h1' : ∑ j, ρ (cy j) * σ (m j) = 1 := by
      have := congrArg σ h1
      rw [map_sum, map_one] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hρ (Y j), hσ, ← hcy]
      rfl
    have hZ : ∑ ij : Option (Fin n) × Option (Fin n),
        p ij.1 ij.2 ⊗ₜ[F] ((Y ij.1 * cy ij.2 : 𝓞 E) : E) = 1 := by
      rw [← mul_one (1 : _root_.GlobalTheory.AdLat.RA F E)]
      nth_rewrite 1 [← h1]
      rw [← h1', Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [show ρ (Y ij.1) * m ij.1 * (ρ (cy ij.2) * σ (m ij.2)) =
          ρ (Y ij.1 * cy ij.2) * (m ij.1 * σ (m ij.2)) by rw [map_mul]; ring, hpe, hρ,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have h0v : Pv v 0 := ⟨h0I, by
      show Valued.v (0 : v.adicCompletion F) < 1
      rw [map_zero]; exact zero_lt_one⟩
    have haddv : ∀ a b, Pv v a → Pv v b → Pv v (a + b) := fun a b ha hb =>
      ⟨haddI a b ha.1 hb.1, by
        show Valued.v (a v + b v) < 1
        exact Valuation.map_add_lt _ ha.2 hb.2⟩
    have hnegv : ∀ a, Pv v a → Pv v (-a) := fun a ha =>
      ⟨hnegI a ha.1, by
        show Valued.v (-(a v)) < 1
        rw [Valuation.map_neg]; exact ha.2⟩
    have hmulv : ∀ a b, Pint a → Pv v b → Pv v (a * b) := fun a b ha hb =>
      ⟨hmulI a b ha hb.1, by
        show Valued.v (a v * b v) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (ha v))) hb.2⟩
    have hPv : ∀ ij : Option (Fin n) × Option (Fin n), Pv v (p ij.1 ij.2) :=
      fun ij => ⟨hpint ij.1 ij.2, hcon ij⟩
    clear_value m ρ H X CX Y
    obtain ⟨N, hN, eN⟩ := exists_norm_sum_tmul_eq_tmul_one c h2 hc (Pv v) h0v haddv hnegv
      (fun f a ha => by
        have := hmulv _ a (hsmI f 1 (_root_.GlobalTheory.AdLat.adele_one_integral F)) ha
        rwa [mul_one] at this)
      (fun a b ha hb => hmulv a b ha.1 hb) Finset.univ
      (fun ij : Option (Fin n) × Option (Fin n) => p ij.1 ij.2)
      (fun ij : Option (Fin n) × Option (Fin n) => Y ij.1 * cy ij.2) hPv
    beta_reduce at eN
    rw [hZ, map_one, mul_one, Algebra.TensorProduct.one_def] at eN
    have hN1 : N = 1 := (Algebra.TensorProduct.includeLeft_injective (R := F)
      (S := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) (algebraMap F E).injective eN).symm
    have := hN.2
    rw [hN1] at this
    exact absurd this (by
      show ¬ Valued.v (1 : v.adicCompletion F) < 1
      rw [map_one]; exact lt_irrefl 1)
  choose ij hij using hkey
  have hval1 : ∀ v, Valued.v (p (ij v).1 (ij v).2 v) = 1 := fun v =>
    le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hpint _ _ v)) (not_lt.1 (hij v))
  have hne : ∀ v, p (ij v).1 (ij v).2 v ≠ 0 := fun v h => by
    have := hval1 v; rw [h, map_zero] at this; exact zero_ne_one this
  have hE0 : ∀ (q : Option (Fin n) × Option (Fin n)) (v : HeightOneSpectrum (𝓞 F)),
      (if ij v = q then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro q v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hD0 : ∀ v : HeightOneSpectrum (𝓞 F),
      (p (ij v).1 (ij v).2 v)⁻¹ ∈ v.adicCompletionIntegers F := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval1, inv_one]
  let e : Option (Fin n) × Option (Fin n) → FiniteAdeleRing (𝓞 F) F := fun q =>
    ⟨fun v => if ij v = q then 1 else 0, Filter.Eventually.of_forall fun v => hE0 q v⟩
  let d : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun v => (p (ij v).1 (ij v).2 v)⁻¹, Filter.Eventually.of_forall hD0⟩
  have heI : ∀ q, Pint (e q) := fun q v => hE0 q v
  have hdI : Pint d := hD0
  let ev : ∀ v : HeightOneSpectrum (𝓞 F), FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F := fun v =>
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have hsum1 : d * ∑ q : Option (Fin n) × Option (Fin n), ∑ q' : Option (Fin n) × Option (Fin n),
      e q * e q' * p q.1 q'.2 = 1 := by
    apply FiniteAdeleRing.ext F
    intro v
    have := map_sum (ev v) (fun q => ∑ q' : Option (Fin n) × Option (Fin n), e q * e q' * p q.1 q'.2)
      Finset.univ
    show d v * (ev v) _ = 1
    rw [this]
    have hevv : ∀ a : FiniteAdeleRing (𝓞 F) F, ev v a = a v := fun _ => rfl
    have hev : ∀ q, e q v = if ij v = q then 1 else 0 := fun _ => rfl
    have hdv : d v = (p (ij v).1 (ij v).2 v)⁻¹ := rfl
    simp only [map_sum, map_mul]
    simp only [hevv, hev, hdv, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact inv_mul_cancel₀ (hne v)
  refine ⟨∑ q, (e q ⊗ₜ[F] (1 : E)) * m q.1, ?_, ⟨(d ⊗ₜ[F] (1 : E)) *
    ∑ q, (e q ⊗ₜ[F] (1 : E)) * σ (m q.2), ?_, ?_⟩, ?_⟩
  · exact AddSubgroup.sum_mem _ fun q _ => hmul _ _
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hmmem _)
  · exact hmul _ _ (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F hdI ⟨1, map_one _⟩)
      (AddSubgroup.sum_mem _ fun q _ => hmul _ _
        (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F (heI q) ⟨1, map_one _⟩) (hσmem _ (hmmem _)))
  · rw [mul_left_comm, Finset.sum_mul_sum]
    have hterm : ∀ q q' : Option (Fin n) × Option (Fin n),
        (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) =
          (e q * e q' * p q.1 q'.2) ⊗ₜ[F] (1 : E) := fun q q' => by
      rw [show (e q ⊗ₜ[F] (1 : E)) * m q.1 * ((e q' ⊗ₜ[F] (1 : E)) * σ (m q'.2)) =
        (e q ⊗ₜ[F] (1 : E)) * (e q' ⊗ₜ[F] (1 : E)) * (m q.1 * σ (m q'.2)) by ring, hpe,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
    simp only [hterm, ← TensorProduct.sum_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsum1]
    rfl
  · rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, hσ, map_one, mul_left_comm, hum]

end GlobalTheory.AdLat
