import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

/- English proof (translation)
Establish `key : ∀ e : ↥D.LL0 →+* FractionRing (T.O0 i), ∃ y : T.O0 i, algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = e x`. Introduce `e`. Establish `h1 : IsIntegral ℤ (e x)`. Take `⟨p, hp, hpx⟩` from `hx`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Establish `h3` using `congrArg e hpx`. Rewrite `h3` using `[map_zero, Polynomial.hom_eval₂]`. Rewrite `h3` using `[RingHom.ext_int (e.comp (algebraMap ℤ _)) (algebraMap ℤ _)]`. Then use the resulting hypothesis. Establish `h2 : IsIntegral (T.O0 i) (e x)` using `h1.tower_top`. Conclude with `IsIntegrallyClosed.isIntegral_iff.mp h2`.

Take `⟨y, hy⟩` from `key (if b then T.emb0 i else T.emb0b i)`. Use `⟨algebraMap (T.O0 i) (T.O i) y, ?_⟩` and prove the remaining obligations. Unfold `readT`. Rewrite using `[RingHom.comp_apply, ← hy]`. Conclude with `(IsLocalization.map_eq _ _).symm`.
-/
theorem readT_integral (i : T.Tw) (b : Bool) (x : ↥D.LL0) (hx : IsIntegral ℤ x) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = readT D T i b x := by
  have key : ∀ e : ↥D.LL0 →+* FractionRing (T.O0 i),
      ∃ y : T.O0 i, algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = e x := by
    intro e
    have h1 : IsIntegral ℤ (e x) := by
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p, hp, ?_⟩
      have h3 := congrArg e hpx
      rw [map_zero, Polynomial.hom_eval₂] at h3
      rwa [RingHom.ext_int (e.comp (algebraMap ℤ _)) (algebraMap ℤ _)] at h3
    have h2 : IsIntegral (T.O0 i) (e x) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  obtain ⟨y, hy⟩ := key (if b then T.emb0 i else T.emb0b i)
  refine ⟨algebraMap (T.O0 i) (T.O i) y, ?_⟩
  unfold readT
  rw [RingHom.comp_apply, ← hy]
  exact (IsLocalization.map_eq _ _).symm

/- English proof (translation)
The claim follows from `readT_integral D T i b _ ((RingOfIntegers.isIntegral_coe a).map S.kKs.toIntAlgHom)`.
-/
theorem ksInt_mem (i : T.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = algebraMap S.Ks (KT D T i b) (a : S.Ks) :=
  readT_integral D T i b _ ((RingOfIntegers.isIntegral_coe a).map S.kKs.toIntAlgHom)

/- English proof (translation)
Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]`.
-/
theorem one_tmul_smul (i : T.Tw) (j : ℕ) (b : Bool) (c : S.Ks) (m : ↥(WKr D S j)) :
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (c • m) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
      algebraMap S.Ks (KT D T i b) c • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul k m`. Establish `hm : m = 0`. Conclude with `Subtype.ext (Submodule.mem_bot _ |>.mp ((WKr_off D S h).le m.2))`.

Rewrite using `[hm, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`.
-/
theorem fmT_eq_zero (i : T.Tw) (j : ℕ) (b : Bool) (h : ¬ (1 ≤ j ∧ j ≤ D.R.m)) (z : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    have hm : m = 0 := by
      exact Subtype.ext (Submodule.mem_bot _ |>.mp ((WKr_off D S h).le m.2))
    rw [hm, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/- English proof (translation)
Distinguish the cases in `h : 1 ≤ j ∧ j ≤ D.R.m`. Use `swap`. Establish `hz` using `fmT_eq_zero D T S i j b h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: BsupT D T S i j b = ⊥` using `(Submodule.eq_bot_iff _).mpr fun z _ => hz z`.

Rewrite using `[this]`. Conclude with `Submodule.fg_bot`. Conclude with `Submodule.eq_top_iff'.mpr fun z => by rw [hz z]; exact Submodule.zero_mem _`. Take `⟨T0, hT, hMK, hWK⟩` from `In.mk_fg j h.1 h.2`. Establish `hmem : ∀ t ∈ T0, t ∈ WKr D S j` using `fun t ht => by`.

Rewrite using `[WKr_of D S h.1 h.2]`. Conclude with `(hMK t (hT t ht)).1`. Set `g : ↥T0 → FmT D T S i j b` to `fun t => ((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨t.1, hmem t.1 t.2⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j))`. Establish `hgB : Set.range g ⊆ BsupT D T S i j b`. Introduce and unpack `_ ⟨t, rfl⟩`.

Conclude with `Submodule.subset_span ⟨⟨t.1, hmem t.1 t.2⟩, hT t.1 t.2, rfl⟩`. Establish `hO : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j, (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈ Submodule.span (T.O i) (Set.range g)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩`.

Consider the case `zero`. Use `⟨Submodule.zero_mem _, fun hy => ?_⟩` and prove the remaining obligations. Establish `: (⟨0, hy⟩ : ↥(WKr D S j)) = 0` using `rfl`. Rewrite using `[this, TensorProduct.tmul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y z _ _ hy hz`. Use `⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩` and prove the remaining obligations. Establish `: (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩` using `rfl`. Rewrite using `[this, TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)`.

Consider the case `smul a y _ hy`. Establish `hay : a • y = (a : S.Ks) • y` using `(algebraMap_smul S.Ks a y).symm`. Establish `hm : a • y ∈ WKr D S j` using `by rw [hay]; exact Submodule.smul_mem _ _ hy.1`. Use `⟨hm, fun hy' => ?_⟩` and prove the remaining obligations. Establish `: (⟨a • y, hy'⟩ : ↥(WKr D S j)) = (a : S.Ks) • ⟨y, hy.1⟩` using `Subtype.ext hay`.

Rewrite using `[this, one_tmul_smul]`. Take `⟨o, ho⟩` from `ksInt_mem D T S i b a`. Rewrite using `[← ho]`. Conclude with `Submodule.smul_mem _ o (hy.2 hy.1)`. Establish `hBeq : BsupT D T S i j b = Submodule.span (T.O i) (Set.range g)`.

Use `le_antisymm ?_ (Submodule.span_le.mpr hgB)` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(hO x.1 (hMK x.1 hx).2).2 x.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hBeq]`. Conclude with `Submodule.fg_span (Set.finite_range g)`. Establish `hK : ∀ y ∈ Submodule.span S.Ks (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j, (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈ Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b))`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span (hgB ⟨⟨t, ht⟩, rfl⟩)⟩`. Consider the case `zero`. Use `⟨Submodule.zero_mem _, fun hy => ?_⟩` and prove the remaining obligations. Establish `: (⟨0, hy⟩ : ↥(WKr D S j)) = 0` using `rfl`. Rewrite using `[this, TensorProduct.tmul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`. Use `⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩` and prove the remaining obligations. Establish `: (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩` using `rfl`. Rewrite using `[this, TensorProduct.tmul_add]`.

Conclude with `Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)`. Consider the case `smul c y _ hy`. Establish `hm : c • y ∈ WKr D S j` using `Submodule.smul_mem _ _ hy.1`. Use `⟨hm, fun hy' => ?_⟩` and prove the remaining obligations. Establish `: (⟨c • y, hy'⟩ : ↥(WKr D S j)) = c • ⟨y, hy.1⟩` using `rfl`.

Rewrite using `[this, one_tmul_smul]`. Conclude with `Submodule.smul_mem _ _ (hy.2 hy.1)`. Use `Submodule.eq_top_iff'.mpr fun z => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `KT D T i b ⊗[S.Ks] ↥(WKr D S j) at z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul k m`. Establish `hm : (m : S.WL j) ∈ Submodule.span S.Ks (T0 : Set (S.WL j))`. Conclude with `hWK _ ((WKr_of D S h.1 h.2).le m.2)`. Establish `h1` using `(hK m.1 hm).2 m.2`.

Establish `h2 : (k ⊗ₜ[S.Ks] m : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = k • ((1 : KT D T i b) ⊗ₜ[S.Ks] m)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ k h1`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.
-/
theorem bsupT_fg_span (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) :
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  swap
  · have hz := fmT_eq_zero D T S i j b h
    refine ⟨?_, ?_⟩
    · have : BsupT D T S i j b = ⊥ := (Submodule.eq_bot_iff _).mpr fun z _ => hz z
      rw [this]; exact Submodule.fg_bot
    · exact Submodule.eq_top_iff'.mpr fun z => by rw [hz z]; exact Submodule.zero_mem _
  obtain ⟨T0, hT, hMK, hWK⟩ := In.mk_fg j h.1 h.2
  have hmem : ∀ t ∈ T0, t ∈ WKr D S j := fun t ht => by
    rw [WKr_of D S h.1 h.2]; exact (hMK t (hT t ht)).1
  let g : ↥T0 → FmT D T S i j b := fun t =>
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨t.1, hmem t.1 t.2⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j))
  have hgB : Set.range g ⊆ BsupT D T S i j b := by
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span ⟨⟨t.1, hmem t.1 t.2⟩, hT t.1 t.2, rfl⟩

  have hO : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (T.O i) (Set.range g) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul a y _ hy =>
      have hay : a • y = (a : S.Ks) • y := (algebraMap_smul S.Ks a y).symm
      have hm : a • y ∈ WKr D S j := by rw [hay]; exact Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨a • y, hy'⟩ : ↥(WKr D S j)) = (a : S.Ks) • ⟨y, hy.1⟩ := Subtype.ext hay
      rw [this, one_tmul_smul]
      obtain ⟨o, ho⟩ := ksInt_mem D T S i b a
      rw [← ho]
      exact Submodule.smul_mem _ o (hy.2 hy.1)
  have hBeq : BsupT D T S i j b = Submodule.span (T.O i) (Set.range g) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr hgB)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hO x.1 (hMK x.1 hx).2).2 x.2
  refine ⟨?_, ?_⟩
  · rw [hBeq]; exact Submodule.fg_span (Set.finite_range g)

  have hK : ∀ y ∈ Submodule.span S.Ks (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span (hgB ⟨⟨t, ht⟩, rfl⟩)⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul c y _ hy =>
      have hm : c • y ∈ WKr D S j := Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨c • y, hy'⟩ : ↥(WKr D S j)) = c • ⟨y, hy.1⟩ := rfl
      rw [this, one_tmul_smul]
      exact Submodule.smul_mem _ _ (hy.2 hy.1)
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at z
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul k m =>
    have hm : (m : S.WL j) ∈ Submodule.span S.Ks (T0 : Set (S.WL j)) := by
      exact hWK _ ((WKr_of D S h.1 h.2).le m.2)
    have h1 := (hK m.1 hm).2 m.2
    have h2 : (k ⊗ₜ[S.Ks] m : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = k • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ k h1
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/- English proof (translation)
Introduce `D S In T i j b` and use `bsupT_fg_span D T S In i j b`.
-/
theorem bsupT_fg_span_all : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ :=
  fun D S In T i j b => bsupT_fg_span D T S In i j b

end GlobalTheory.HeightCounting.FormsStep
