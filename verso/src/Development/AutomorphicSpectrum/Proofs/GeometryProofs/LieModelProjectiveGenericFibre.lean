import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Alg

variable {A K V T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module A V] [AddCommGroup T] [Module K T] [Module A T] [IsScalarTower A K T]

/- English proof (translation)
Establish `h1` using `IsLocalizedModule.finrank_eq (nonZeroDivisors A) j le_rfl`. Establish `h2 : Module.finrank K T = Module.finrank A T` using `congrArg Cardinal.toNat (IsLocalization.rank_eq K (N := T) (nonZeroDivisors A) le_rfl)`. Conclude with `h1.symm.trans h2.symm`.
-/
theorem finrank_eq_of_isLocalized (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Module K T]
    [IsScalarTower A K T] (j : V →ₗ[A] T) [IsLocalizedModule (nonZeroDivisors A) j] :
    Module.finrank A V = Module.finrank K T := by
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors A) j le_rfl
  have h2 : Module.finrank K T = Module.finrank A T :=
    congrArg Cardinal.toNat (IsLocalization.rank_eq K (N := T) (nonZeroDivisors A) le_rfl)
  exact h1.symm.trans h2.symm

/- English proof (translation)
Introduce `x y h`. Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_iff_exists (nonZeroDivisors A) j).1 h`. Conclude with `smul_right_injective V (nonZeroDivisors.ne_zero c.2) hc`.
-/
theorem injective_of_isLocalized [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] : Function.Injective j := by
  intro x y h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A) j).1 h
  exact smul_right_injective V (nonZeroDivisors.ne_zero c.2) hc

def resMap (j : V →ₗ[A] T) (W : Submodule K T) : (W.restrictScalars A).comap j →ₗ[A] W where
  toFun x := ⟨j x, x.2⟩
  map_add' x y := Subtype.ext (map_add j _ _)
  map_smul' c x := Subtype.ext (map_smul j c _)

/- English proof (translation)
Establish `hk : algebraMap A K a ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2`. Establish `key : ∀ w : W, algebraMap A (Module.End A W) a w = algebraMap A K a • w` using `fun w => by`. Rewrite using `[Module.algebraMap_end_apply, algebraMap_smul]`. Use `(Module.End.isUnit_iff _).2 ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A K a)⁻¹ • w, ?_⟩⟩` and prove the remaining obligations. Rewrite `h` using `[key, key]`.

Conclude with `smul_right_injective W hk h`. Rewrite using `[key, smul_smul, mul_inv_cancel₀ hk, one_smul]`. Use `surj w := by`. Take `⟨⟨y, a⟩, h⟩` from `IsLocalizedModule.surj (nonZeroDivisors A) j (w : T)`. Establish `h' : (a : A) • (w : T) = j y` using `h`.

Establish `hy : j y ∈ W`. Rewrite using `[← h', ← algebraMap_smul K (a : A) (w : T)]`. Conclude with `W.smul_mem _ w.2`. Conclude with `⟨(⟨y, hy⟩, a), Subtype.ext h⟩`. Use `exists_of_eq {x y} h := by`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, one_smul]`. Conclude with `Subtype.ext (injective_of_isLocalized j (congrArg Subtype.val h))`.
-/
theorem isLocalized_resMap [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    IsLocalizedModule (nonZeroDivisors A) (resMap j W) where
  map_units a := by
    have hk : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have key : ∀ w : W, algebraMap A (Module.End A W) a w = algebraMap A K a • w := fun w => by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    refine (Module.End.isUnit_iff _).2 ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A K a)⁻¹ • w, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective W hk h
    · rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  surj w := by
    obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors A) j (w : T)
    have h' : (a : A) • (w : T) = j y := h
    have hy : j y ∈ W := by
      rw [← h', ← algebraMap_smul K (a : A) (w : T)]
      exact W.smul_mem _ w.2
    exact ⟨(⟨y, hy⟩, a), Subtype.ext h⟩
  exists_of_eq {x y} h := by
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul]
    exact Subtype.ext (injective_of_isLocalized j (congrArg Subtype.val h))

/- English proof (translation)
Use `haveI := isLocalized_resMap j W`. Conclude with `finrank_eq_of_isLocalized K (resMap j W)`.
-/
theorem finrank_comap_eq [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    Module.finrank A ((W.restrictScalars A).comap j) = Module.finrank K W := by
  haveI := isLocalized_resMap j W
  exact finrank_eq_of_isLocalized K (resMap j W)

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw => exact hB w hw`. Consider the case `zero => exact ⟨1, one_ne_zero, 0, S.zero_mem, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨a, ha, y, hy, e⟩` from `hu`.

Take `⟨b, hb, y', hy', e'⟩` from `hv`. Use `⟨a * b, mul_ne_zero ha hb, b • y + a • y', S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hy'), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm a b, mul_comm b a, mul_comm a b]`. Consider the case `smul c u _ hu`. Take `⟨a, ha, y, hy, e⟩` from `hu`.

Take `⟨b, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := A) c`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hk : algebraMap A K d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Use `⟨d * a, mul_ne_zero hd0 ha, b • y, S.smul_mem _ hy, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← e, ← algebraMap_smul K (d * a), ← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_smul_mem (j : V →ₗ[A] T) (S : Submodule A V) (B : Set T)
    (hB : ∀ w ∈ B, ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y) {w : T} (hw : w ∈ Submodule.span K B) :
    ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hB w hw
  | zero => exact ⟨1, one_ne_zero, 0, S.zero_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, hb, y', hy', e'⟩ := hv
    refine ⟨a * b, mul_ne_zero ha hb, b • y + a • y', S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hy'), ?_⟩
    rw [map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm a b, mul_comm b a,
      mul_comm a b]
  | smul c u _ hu =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hk : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨d * a, mul_ne_zero hd0 ha, b • y, S.smul_mem _ hy, ?_⟩
    rw [map_smul, ← e, ← algebraMap_smul K (d * a), ← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp

end Alg

section Num

variable {L V T : Type} [Field L] [NumberField L] [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup T]
  [Module (𝓞 L) T]

/- English proof (translation)
Take `⟨⟨y, a⟩, h⟩` from `IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j w`. Establish `ha : (a : 𝓞 L) ≠ 0` using `nonZeroDivisors.ne_zero a.2`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(a : 𝓞 L)}))`. Use `⟨Ideal.absNorm (Ideal.span {(a : 𝓞 L)}), ?_, b • y, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `ha`. Establish `h' : (a : 𝓞 L) • w = j y` using `h`. Rewrite using `[← hb, mul_smul, map_smul, ← h']`.
-/
theorem exists_nat_smul (j : V →ₗ[𝓞 L] T) [IsLocalizedModule (nonZeroDivisors (𝓞 L)) j] (w : T) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : V, (n : 𝓞 L) • w = j y := by
  obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j w
  have ha : (a : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero a.2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(a : 𝓞 L)}))
  refine ⟨Ideal.absNorm (Ideal.span {(a : 𝓞 L)}), ?_, b • y, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  · have h' : (a : 𝓞 L) • w = j y := h
    rw [← hb, mul_smul, map_smul, ← h']

end Num

section Geo

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li] {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
  [Module (𝓞 L) V] {T : Type} [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T]

/- English proof (translation)
Establish `e : v.left ≫ 𝟙 G.left = (TL.pt (j x)).left ≫ 𝟙 G.left` using `h.trans (hl x).symm`. Rewrite `e` using `[Category.comp_id, Category.comp_id]`. Conclude with `Over.OverMorphism.ext e`.
-/
theorem eq_pt_of_lifts {MB : LieModel G z V} {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T}
    {j : V →ₗ[𝓞 L] T} (hl : ∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (TL.pt (j x))) {x : V}
    {v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G} (h : MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v) :
    v = TL.pt (j x) := by
  have e : v.left ≫ 𝟙 G.left = (TL.pt (j x)).left ≫ 𝟙 G.left := h.trans (hl x).symm
  rw [Category.comp_id, Category.comp_id] at e
  exact Over.OverMorphism.ext e

/- English proof (translation)
Take `⟨h1, -⟩` from `id hv`. Establish `key` using `hv.smul h1 (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))`. Establish `e1 : (Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z))) = (n : L)` using `map_natCast _ n`. Rewrite `key` using `[map_natCast, e1, ← TL.pt_smul]`. Establish `e2 : (n : L) • w = j y`.

Rewrite using `[← hy, ← algebraMap_smul L (n : 𝓞 L) w, map_natCast]`. Rewrite `key` using `[e2]`. Conclude with `⟨_, U.smul_mem _ he, _, key, hl y⟩`.
-/
theorem mem_subGens_of_nat {M : LieModel G ξ Li} {U : Submodule Ω Li} {MB : LieModel G z V}
    {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T} {j : V →ₗ[𝓞 L] T}
    (hl : ∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (TL.pt (j x))) {e : Li} (he : e ∈ U) {w : T}
    (hv : M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)) (n : ℕ) {y : V} (hy : (n : 𝓞 L) • w = j y) :
    y ∈ subGens M U z MB := by
  obtain ⟨h1, -⟩ := id hv
  have key := hv.smul h1 (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
  have e1 : (Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom
      (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z))) = (n : L) := map_natCast _ n
  rw [map_natCast, e1, ← TL.pt_smul] at key
  have e2 : (n : L) • w = j y := by
    rw [← hy, ← algebraMap_smul L (n : 𝓞 L) w, map_natCast]
  rw [e2] at key
  exact ⟨_, U.smul_mem _ he, _, key, hl y⟩

end Geo

/- English proof (translation)
Introduce `X G _ Ω _ ξ Li _ _ M L _ _ z V _ _ _ _ MB T _ _ _ _ TL j U _ hl hj`. Use `haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 hj`. Use `⟨finrank_eq_of_isLocalized L j, ?_⟩` and prove the remaining obligations. Use `set B : Set T := {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)} with hBdef`. Establish `hinj : Function.Injective j` using `injective_of_isLocalized j`.

Establish `hS : ∀ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), j y ∈ Submodule.span L B`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨e, he, v, hv, hlift⟩` from `hy`.

Establish `hv'` using `eq_pt_of_lifts hl hlift`. Conclude with `Submodule.subset_span ⟨e, he, hv' ▸ hv⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul c a _ ha`. Rewrite using `[map_smul, ← algebraMap_smul L c (j a)]`. Conclude with `Submodule.smul_mem _ _ ha`. Establish `hB : ∀ w ∈ B, ∃ a : 𝓞 L, a ≠ 0 ∧ ∃ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), a • w = j y`. Introduce and unpack `w ⟨e, he, hv⟩`.

Take `⟨n, hn, y, hy⟩` from `exists_nat_smul j w`. Conclude with `⟨n, Nat.cast_ne_zero.2 hn, y, Submodule.subset_span (mem_subGens_of_nat hl he hv n hy), hy⟩`. Establish `e : subFib M U z MB = ((Submodule.span L B).restrictScalars (𝓞 L)).comap j`. Use extensionality with `x`. Rewrite using `[mem_subFib]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hx⟩`. Establish `h1` using `hS _ hx`. Rewrite `h1` using `[map_smul, ← algebraMap_smul L a (j x)]`. Establish `hk : algebraMap (𝓞 L) L a ≠ 0` using `fun h0 => ha (by simpa using h0)`.

Conclude with `(Submodule.smul_mem_iff (Submodule.span L B) hk).1 h1`. Introduce `hx`. Take `⟨a, ha, y, hy, h⟩` from `exists_smul_mem j _ B hB (K := L) hx`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hinj (by rw [map_smul]; exact h : j (a • x) = j y)]` and apply the resulting hypothesis.

Rewrite using `[e]`. Conclude with `finrank_comap_eq j _`.
-/
theorem finrank_subFib : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (TL.pt (j x))) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  intro X G _ Ω _ ξ Li _ _ M L _ _ z V _ _ _ _ MB T _ _ _ _ TL j U _ hl hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 hj
  refine ⟨finrank_eq_of_isLocalized L j, ?_⟩
  set B : Set T := {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)} with hBdef
  have hinj : Function.Injective j := injective_of_isLocalized j
  have hS : ∀ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), j y ∈ Submodule.span L B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, v, hv, hlift⟩ := hy
      have hv' := eq_pt_of_lifts hl hlift
      exact Submodule.subset_span ⟨e, he, hv' ▸ hv⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← algebraMap_smul L c (j a)]
      exact Submodule.smul_mem _ _ ha
  have hB : ∀ w ∈ B, ∃ a : 𝓞 L, a ≠ 0 ∧ ∃ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), a • w = j y := by
    rintro w ⟨e, he, hv⟩
    obtain ⟨n, hn, y, hy⟩ := exists_nat_smul j w
    exact ⟨n, Nat.cast_ne_zero.2 hn, y, Submodule.subset_span (mem_subGens_of_nat hl he hv n hy), hy⟩
  have e : subFib M U z MB = ((Submodule.span L B).restrictScalars (𝓞 L)).comap j := by
    ext x
    rw [mem_subFib]
    constructor
    · rintro ⟨a, ha, hx⟩
      have h1 := hS _ hx
      rw [map_smul, ← algebraMap_smul L a (j x)] at h1
      have hk : algebraMap (𝓞 L) L a ≠ 0 := fun h0 => ha (by simpa using h0)
      exact (Submodule.smul_mem_iff (Submodule.span L B) hk).1 h1
    · intro hx
      obtain ⟨a, ha, y, hy, h⟩ := exists_smul_mem j _ B hB (K := L) hx
      refine ⟨a, ha, ?_⟩
      rwa [hinj (by rw [map_smul]; exact h : j (a • x) = j y)]
  rw [e]
  exact finrank_comap_eq j _

end GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge
