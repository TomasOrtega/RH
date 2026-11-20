import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.LocusQA

open GlobalTheory.Cartier.CartierDiv

variable {Y : Scheme.{0}} [IsIntegral Y] {y : Y}

/- English proof (translation)
Take `⟨a, rfl⟩` from `hf`. Conclude with `⟨a ^ n, map_pow _ _ _⟩`.
-/
theorem regAt_pow {f : Y.functionField} (hf : RegAt y f) (n : ℕ) : RegAt y (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hf`. Use `⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩` and prove the remaining obligations. Rewrite `e` using `[← map_pow]`. Take `rfl` from `IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e`. Conclude with `⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩`.
-/
theorem unitAt_pow_iff {f : Y.functionField} (hf : RegAt y f) {n : ℕ} (hn : n ≠ 0) :
    UnitAt y (f ^ n) ↔ UnitAt y f := by
  obtain ⟨a, rfl⟩ := hf
  refine ⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e
  exact ⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩

/- English proof (translation)
Rewrite using `[div_eq_mul_inv]`. Conclude with `hf.mul hg.inv.regAt`.
-/
theorem regAt_div {f g : Y.functionField} (hf : RegAt y f) (hg : UnitAt y g) : RegAt y (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv.regAt

/- English proof (translation)
Use `⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩` and prove the remaining obligations. Use `h.mul hg` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hg.ne_zero]`. Then use the resulting hypothesis.
-/
theorem unitAt_div_iff {f g : Y.functionField} (hg : UnitAt y g) : UnitAt y (f / g) ↔ UnitAt y f := by
  refine ⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩
  have := h.mul hg
  rwa [div_mul_cancel₀ _ hg.ne_zero] at this

/- English proof (translation)
Rewrite using `[mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]`.
-/
theorem pow_div_pow_eqn {K : Type} [Field K] (a b c : K) (hc : c ≠ 0) (m n : ℕ) :
    (a * c ^ m) ^ n / (b * c ^ n) ^ m = a ^ n / b ^ m := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]

/- English proof (translation)
Introduce `Y _ _ _ D hD k hk s hs V hV`. Establish `memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s` using `fun y => by`. Rewrite using `[← SetLike.mem_coe, hV]`. Both sides reduce to the same expression. Establish `loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e → RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k))`.

Introduce `y e he`. Establish `h` using `he.nsmul k`. Establish `h1` using `h.regularAt_iff.1 (hs y)`. Establish `h2` using `(memV y).trans h.generatesAt_iff`. Rewrite `h1`, `h2` using `[Units.val_pow_eq_pow_val]`.

Conclude with `⟨h1, h2⟩`. Establish `stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u → IsAffineOpen (V ⊓ U)`. Introduce `k' hk' u hu U hUa hUl`. Establish `memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u` using `fun y => by`. Rewrite using `[← SetLike.mem_coe, hUl]`.

Both sides reduce to the same expression. Establish `locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e → (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k'))`. Introduce `y e he`. Establish `h` using `he.nsmul k'`. Establish `h2` using `(memU y).trans h.generatesAt_iff`.

Rewrite `h2` using `[Units.val_pow_eq_pow_val]`. Conclude with `h2`. Distinguish the cases in `hg : genericPoint Y ∈ U`. Use `swap`. Establish `: U = ⊥` using `eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim`.

Rewrite using `[this, inf_bot_eq]`. Conclude with `isAffineOpen_bot Y`. Establish `hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k)`. Introduce `y hy`. Take `⟨e, he⟩` from `D.exists_isEqn y`.

Establish `hB` using `(locU y e he).1 hy`. Rewrite using `[← pow_div_pow_eqn s u _ e.ne_zero k k']`. Conclude with `regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)`. Take `⟨a, ha⟩` from `exists_fnOf_eq hg hreg`. Establish `e₁ : V ⊓ U = Y.basicOpen a`.

Use extensionality with `y`. Use `⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `D.exists_isEqn y`. Establish `hB` using `(locU y e he).1 hyU`. Use `(unitAt_fnOf_iff hyU hg a).1 ?_` and prove the remaining obligations.

Rewrite using `[ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB), unitAt_pow_iff (loc y e he).1 (by omega)]`. Conclude with `(loc y e he).2.1 hyV`. Establish `hyU : y ∈ U` using `Y.basicOpen_le a hy`. Take `⟨e, he⟩` from `D.exists_isEqn y`. Establish `hB` using `(locU y e he).1 hyU`.

Establish `h` using `(unitAt_fnOf_iff hyU hg a).2 hy`. Rewrite `h` using `[ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB), unitAt_pow_iff (loc y e he).1 (by omega)]`. Conclude with `⟨(loc y e he).2.2 h, hyU⟩`. Rewrite using `[e₁]`. Conclude with `hUa.basicOpen a`.

Establish `: CompactSpace V` using `by choose kk hkk u hu U hUa hUl hxU using hD`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)`. Establish `e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y)`. Use `Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)` and prove the remaining obligations. Take `⟨y, hy, hzy⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ z))`.

Conclude with `Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩`. Establish `hc : IsCompact (V : Set Y)` using `e ▸ t.isCompact_biUnion fun y _ => (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact`. Conclude with `isCompact_iff_compactSpace.mp hc`. Establish `: CompactSpace V.toScheme` using `inferInstanceAs (CompactSpace V)`. Use `Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_` and prove the remaining obligations.

Take `⟨k', hk', u, hu, U, hUa, hUl, hxU⟩` from `hD x.1`. Establish `memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u` using `fun y => by`. Rewrite using `[← SetLike.mem_coe, hUl]`. Both sides reduce to the same expression. Establish `locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e → RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k'))`.

Introduce `y e he`. Establish `h` using `he.nsmul k'`. Establish `h1` using `h.regularAt_iff.1 (hu y)`. Establish `h2` using `(memU y).trans h.generatesAt_iff`. Rewrite `h1`, `h2` using `[Units.val_pow_eq_pow_val]`.

Conclude with `⟨h1, h2⟩`. Establish `hg : genericPoint Y ∈ V` using `gen_mem x.2`. Establish `hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k')`. Introduce `y hy`. Take `⟨e, he⟩` from `D.exists_isEqn y`.

Establish `hA` using `(loc y e he).2.1 hy`. Rewrite using `[← pow_div_pow_eqn u s _ e.ne_zero k' k]`. Conclude with `regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)`. Take `⟨a, ha⟩` from `exists_fnOf_eq hg hreg`. Establish `e₁ : Y.basicOpen a = V ⊓ U`.

Use extensionality with `y`. Use `⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩` and prove the remaining obligations. Establish `hyV : y ∈ V` using `Y.basicOpen_le a hy`. Take `⟨e, he⟩` from `D.exists_isEqn y`. Establish `hA` using `(loc y e he).2.1 hyV`.

Establish `h` using `(unitAt_fnOf_iff hyV hg a).2 hy`. Rewrite `h` using `[ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA), unitAt_pow_iff (locU y e he).1 (by omega)]`. Conclude with `⟨hyV, (locU y e he).2.2 h⟩`. Take `⟨e, he⟩` from `D.exists_isEqn y`. Establish `hA` using `(loc y e he).2.1 hyV`.

Use `(unitAt_fnOf_iff hyV hg a).1 ?_` and prove the remaining obligations. Rewrite using `[ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA), unitAt_pow_iff (locU y e he).1 (by omega)]`. Conclude with `(locU y e he).2.1 hyU`. Establish `him` using `Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a`. Rewrite `him` using `[e₁]`.

Use `⟨V.topIso.inv a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]`. Conclude with `stepC k' hk' u hu U hUa hUl`. Establish `hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a)`. Rewrite using `[him]`.

Conclude with `⟨x.2, hxU⟩`. Take `⟨z, hz, hzx⟩` from `hm`. Rewrite `hz` using `[V.ι.isOpenEmbedding.injective hzx]`. Then use the resulting hypothesis.
-/
theorem isQuasiAffine_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens,
    (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  intro Y _ _ _ D hD k hk s hs V hV
  have memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s := fun y => by
    rw [← SetLike.mem_coe, hV]; rfl
  have loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k)) := by
    intro y e he
    have h := he.nsmul k
    have h1 := h.regularAt_iff.1 (hs y)
    have h2 := (memV y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u →
      IsAffineOpen (V ⊓ U) := by
    intro k' hk' u hu U hUa hUl
    have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
      rw [← SetLike.mem_coe, hUl]; rfl
    have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
        (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
      intro y e he
      have h := he.nsmul k'
      have h2 := (memU y).trans h.generatesAt_iff
      rw [Units.val_pow_eq_pow_val] at h2
      exact h2
    by_cases hg : genericPoint Y ∈ U
    swap
    · have : U = ⊥ := eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim
      rw [this, inf_bot_eq]
      exact isAffineOpen_bot Y
    have hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k) := by
      intro y hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hB := (locU y e he).1 hy
      rw [← pow_div_pow_eqn s u _ e.ne_zero k k']
      exact regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)
    obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
    have e₁ : V ⊓ U = Y.basicOpen a := by
      ext y
      refine ⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩
      · obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        refine (unitAt_fnOf_iff hyU hg a).1 ?_
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)]
        exact (loc y e he).2.1 hyV
      · have hyU : y ∈ U := Y.basicOpen_le a hy
        obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        have h := (unitAt_fnOf_iff hyU hg a).2 hy
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)] at h
        exact ⟨(loc y e he).2.2 h, hyU⟩
    rw [e₁]
    exact hUa.basicOpen a
  have : CompactSpace V := by
    choose kk hkk u hu U hUa hUl hxU using hD
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)
    have e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩
    have hc : IsCompact (V : Set Y) := e ▸ t.isCompact_biUnion fun y _ =>
      (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨k', hk', u, hu, U, hUa, hUl, hxU⟩ := hD x.1
  have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
    rw [← SetLike.mem_coe, hUl]; rfl
  have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
    intro y e he
    have h := he.nsmul k'
    have h1 := h.regularAt_iff.1 (hu y)
    have h2 := (memU y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have hg : genericPoint Y ∈ V := gen_mem x.2
  have hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k') := by
    intro y hy
    obtain ⟨e, he⟩ := D.exists_isEqn y
    have hA := (loc y e he).2.1 hy
    rw [← pow_div_pow_eqn u s _ e.ne_zero k' k]
    exact regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
  have e₁ : Y.basicOpen a = V ⊓ U := by
    ext y
    refine ⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩
    · have hyV : y ∈ V := Y.basicOpen_le a hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      have h := (unitAt_fnOf_iff hyV hg a).2 hy
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)] at h
      exact ⟨hyV, (locU y e he).2.2 h⟩
    · obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      refine (unitAt_fnOf_iff hyV hg a).1 ?_
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)]
      exact (locU y e he).2.1 hyU
  have him := Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a
  rw [e₁] at him
  refine ⟨V.topIso.inv a, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]
    exact stepC k' hk' u hu U hUa hUl
  · have hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a) := by
      rw [him]; exact ⟨x.2, hxU⟩
    obtain ⟨z, hz, hzx⟩ := hm
    rwa [V.ι.isOpenEmbedding.injective hzx] at hz

end GlobalTheory.Desc.LocusQA
