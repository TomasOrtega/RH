import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.BaseNoeth

/- English proof (translation)
Establish `hu : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom A y)`. Introduce and unpack `⟨y, hy⟩`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hn` using `h y.natAbs (Int.natAbs_ne_zero.mpr hy0)`. Break down `Int.natAbs_eq y with e | e` into its components or cases.

Establish `: Int.castRingHom A y = (y.natAbs : A)` using `by conv_lhs => rw [e]`. Simplify using the standard rewrite rules. Simplify `hn` using `[this]`. Establish `: Int.castRingHom A y = -(y.natAbs : A)` using `by conv_lhs => rw [e]`. Simplify using the standard rewrite rules.

Simplify `hn.neg` using `[this]`. Conclude with `⟨IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu⟩`.
-/
private theorem exists_ratHom {A : Type} [CommRing A] (h : ∀ k : ℕ, k ≠ 0 → IsUnit (k : A)) :
    Nonempty (ℚ →+* A) := by
  have hu : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom A y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hn := h y.natAbs (Int.natAbs_ne_zero.mpr hy0)
    rcases Int.natAbs_eq y with e | e
    · have : Int.castRingHom A y = (y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn
    · have : Int.castRingHom A y = -(y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn.neg
  exact ⟨IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu⟩

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `pp : p.Prime` using `Fact.out`. Take `⟨e, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk p pp.ne_one`. Establish `hcop : m.Coprime p` using `((Nat.Prime.coprime_iff_not_dvd pp).mpr hm).symm`. Rewrite using `[Nat.cast_mul, Nat.cast_pow]`. Conclude with `(hp.pow e).mul (hu m hcop)`.
-/
private theorem units_of {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (k : ℕ) (hk : k ≠ 0) : IsUnit (k : A) := by
  have pp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p pp.ne_one
  have hcop : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd pp).mpr hm).symm
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow e).mul (hu m hcop)

/- English proof (translation)
Take `⟨f⟩` from `exists_ratHom (units_of hp hu)`. Use `letI : Algebra ℚ A := f.toAlgebra`. Take `⟨G, hG⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 D.F)).FG)`. Establish `hw : ∀ ij : Fin D.a × Fin D.a, ∃ c : 𝓞 D.F →₀ A, ij.1 ≠ ij.2 → (c.sum fun x a => a * (t ij.1 x - t ij.2 x)) = 1`. Introduce and unpack `⟨i, j⟩`.

Distinguish the cases in `hij : i = j`. Conclude with `⟨0, fun h => absurd hij h⟩`. Establish `h1 : (1 : A) ∈ Ideal.span (Set.range fun x => t i x - t j x)`. Rewrite using `[hc i j hij]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨c, hc'⟩` from `(Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp h1`. Conclude with `⟨c, fun _ => hc'⟩`. Use `choose w hw using hw`. Set `T : Finset A` to `insert ρ ((Finset.univ.biUnion fun i : Fin D.a => G.image (t i)) ∪ (Finset.univ.biUnion fun ij : Fin D.a × Fin D.a => (w ij).support.image (w ij)))`. Set `B : Subalgebra ℚ A` to `Algebra.adjoin ℚ (T : Set A)`.

Establish `hfg : B.FG` using `Subalgebra.fg_adjoin_finset T`. Use `haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType B).mp hfg`. Use `haveI hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B`. Establish `hTB : ∀ a ∈ T, a ∈ B` using `fun a ha => Algebra.subset_adjoin (by exact_mod_cast ha)`. Establish `hρB : ρ ∈ B` using `hTB _ (Finset.mem_insert_self _ _)`.

Establish `htB : ∀ i c, t i c ∈ B`. Introduce `i c`. Establish `hcG : c ∈ Submodule.span ℤ (G : Set (𝓞 D.F))` using `by rw [hG]; trivial`. Proceed by induction on `hcG using Submodule.span_induction with`. Consider the case `mem x hx`.

Use `hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))` and prove the remaining obligations. Conclude with `Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (by exact_mod_cast hx)⟩`. Consider the case `zero => simpa using B.zero_mem`. Consider the case `add x y _ _ hx hy => simpa using B.add_mem hx hy`. Consider the case `smul a x _ hx`.

Establish `: t i (a • x) = (a : A) * t i x` using `by simp`. Rewrite using `[this]`. Conclude with `B.mul_mem (by simpa using B.toSubring.intCast_mem a) hx`. Establish `hwB : ∀ ij x, w ij x ∈ B`. Introduce `ij x`.

Distinguish the cases in `hx : x ∈ (w ij).support`. Use `hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))` and prove the remaining obligations. Conclude with `Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩`. Rewrite using `[Finsupp.notMem_support_iff.mp hx]`. Conclude with `B.zero_mem`.

Establish `hun : ∀ k : ℕ, k ≠ 0 → IsUnit ((k : ℕ) : B.toSubring)`. Introduce `k hk`. Establish `h` using `(IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk)).map (algebraMap ℚ B)`. Simplify using `using h`. Set `t₁ : Fin D.a → (𝓞 D.F →+* B.toSubring)` to `fun i => (t i).codRestrict B.toSubring (htB i)`.

Set `ρ₁ : B.toSubring` to `⟨ρ, hρB⟩`. Establish `pp : p.Prime` using `Fact.out`. Establish `hpu : IsUnit ((p : ℕ) : B.toSubring)` using `hun p pp.ne_zero`. Use `⟨B.toSubring, hN, ?_⟩` and prove the remaining obligations. Use `⟨⟨fun k hk => hun k ?_, ρ₁, ?_, t₁, ?_, ?_, ?_⟩, hpu, rfl, fun i c => rfl⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Use `(Nat.coprime_zero_left p).mp hk` as an intermediate fact. Conclude with `pp.ne_one this`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hρ` using `[ρ₁]`.

Introduce `i`. Conclude with `Subtype.ext (hω i)`. Introduce `i j hij`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `key : ((((w (i, j)).support.sum fun x => (⟨w (i, j) x, hwB _ x⟩ : B.toSubring) * (t₁ i x - t₁ j x)) : B.toSubring)) = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `hw (i, j) hij` as an intermediate fact. Rewrite `this` using `[Finsupp.sum]`. Simplify `this` using `[t₁]`. Rewrite using `[← key]`.

Conclude with `Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)`. Introduce `i j _ k _ _ β`. It suffices to derive a contradiction. Establish `h1` using `hpu.map β`. Simplify using `at h1`.
-/
private theorem core (D : Datum p) {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (ρ : A) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0)
    (t : Fin D.a → (𝓞 D.F →+* A)) (hω : ∀ i, t i D.ω = ρ)
    (hc : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) :
    ∃ (R₁ : Subring A) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁), IsUnit ((p : ℕ) : R₁) ∧
      ((b₁.ρ : R₁) : A) = ρ ∧ ∀ i c, ((b₁.t i c : R₁) : A) = t i c := by
  classical
  obtain ⟨f⟩ := exists_ratHom (units_of hp hu)
  letI : Algebra ℚ A := f.toAlgebra

  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 D.F)).FG)

  have hw : ∀ ij : Fin D.a × Fin D.a, ∃ c : 𝓞 D.F →₀ A, ij.1 ≠ ij.2 →
      (c.sum fun x a => a * (t ij.1 x - t ij.2 x)) = 1 := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h1 : (1 : A) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hc i j hij]; trivial
      obtain ⟨c, hc'⟩ := (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp h1
      exact ⟨c, fun _ => hc'⟩
  choose w hw using hw

  let T : Finset A := insert ρ ((Finset.univ.biUnion fun i : Fin D.a => G.image (t i)) ∪
    (Finset.univ.biUnion fun ij : Fin D.a × Fin D.a => (w ij).support.image (w ij)))
  let B : Subalgebra ℚ A := Algebra.adjoin ℚ (T : Set A)
  have hfg : B.FG := Subalgebra.fg_adjoin_finset T
  haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  have hTB : ∀ a ∈ T, a ∈ B := fun a ha => Algebra.subset_adjoin (by exact_mod_cast ha)
  have hρB : ρ ∈ B := hTB _ (Finset.mem_insert_self _ _)
  have htB : ∀ i c, t i c ∈ B := by
    intro i c
    have hcG : c ∈ Submodule.span ℤ (G : Set (𝓞 D.F)) := by rw [hG]; trivial
    induction hcG using Submodule.span_induction with
    | mem x hx =>
      refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (by exact_mod_cast hx)⟩
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => simpa using B.add_mem hx hy
    | smul a x _ hx =>
      have : t i (a • x) = (a : A) * t i x := by simp
      rw [this]
      exact B.mul_mem (by simpa using B.toSubring.intCast_mem a) hx
  have hwB : ∀ ij x, w ij x ∈ B := by
    intro ij x
    by_cases hx : x ∈ (w ij).support
    · refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
      exact Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    · rw [Finsupp.notMem_support_iff.mp hx]; exact B.zero_mem
  have hun : ∀ k : ℕ, k ≠ 0 → IsUnit ((k : ℕ) : B.toSubring) := by
    intro k hk
    have h := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk)).map (algebraMap ℚ B)
    simpa using h
  let t₁ : Fin D.a → (𝓞 D.F →+* B.toSubring) := fun i => (t i).codRestrict B.toSubring (htB i)
  let ρ₁ : B.toSubring := ⟨ρ, hρB⟩
  have pp : p.Prime := Fact.out
  have hpu : IsUnit ((p : ℕ) : B.toSubring) := hun p pp.ne_zero
  refine ⟨B.toSubring, hN, ?_⟩
  refine ⟨⟨fun k hk => hun k ?_, ρ₁, ?_, t₁, ?_, ?_, ?_⟩, hpu, rfl, fun i c => rfl⟩
  · rintro rfl
    have := (Nat.coprime_zero_left p).mp hk
    exact pp.ne_one this
  · apply Subtype.ext
    simpa [ρ₁] using hρ
  · intro i
    exact Subtype.ext (hω i)
  · intro i j hij
    rw [Ideal.eq_top_iff_one]
    have key : ((((w (i, j)).support.sum fun x =>
        (⟨w (i, j) x, hwB _ x⟩ : B.toSubring) * (t₁ i x - t₁ j x)) : B.toSubring)) = 1 := by
      apply Subtype.ext
      have := hw (i, j) hij
      rw [Finsupp.sum] at this
      simpa [t₁] using this
    rw [← key]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
  · intro i j _ k _ _ β
    exfalso
    have h1 := hpu.map β
    simp at h1

/- English proof (translation)
Establish `h : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫ (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f`. Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Conclude with `congrArg (fun g => CommRingCat.Hom.hom g a) h`.
-/
private theorem gam_toSpecΓ {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (f : R₁ →+* Γ(S, ⊤)) (a : R₁) :
    gam (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) : S ⟶ Sp R₁) a = f a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => CommRingCat.Hom.hom g a) h

end UpperTheory.BaseNoeth

open UpperTheory.BaseNoeth in
/- English proof (translation)
Introduce `p _ D R _ b S s hp`. Set `g : R →+* Γ(S, ⊤)` to `gam s`. Take `⟨R₁, hN, b₁, hpu, h1, h2⟩` from `core D (A := Γ(S, ⊤)) hp (fun k hk => by simpa using (b.unit k hk).map g) (g b.ρ) (by simpa using congrArg g b.ρ_root) (fun i => g.comp (b.t i)) (fun i => by simp [b.t_ω]) (fun i j hij => by`. Establish `h` using `congrArg (Ideal.map g) (b.comax i j hij)`. Rewrite `h` using `[Ideal.map_span, Ideal.map_top, ← Set.range_comp]`.

Simplify `h)` using `[Function.comp_def]`. Use `⟨R₁, inferInstance, hN, b₁, S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom R₁.subtype), hpu, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gam_toSpecΓ]`. Conclude with `h1.symm`. Introduce `i c`.

Rewrite using `[gam_toSpecΓ]`. Conclude with `(h2 i c).symm`.
-/
theorem UpperTheory.exists_noetherian_base_link :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0}) (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁) (s₁ : S ⟶ Sp R₁), IsUnit ((p : ℕ) : R₁) ∧ Link b b₁ s s₁ := by
  intro p _ D R _ b S s hp
  let g : R →+* Γ(S, ⊤) := gam s
  obtain ⟨R₁, hN, b₁, hpu, h1, h2⟩ := core D (A := Γ(S, ⊤)) hp
    (fun k hk => by simpa using (b.unit k hk).map g) (g b.ρ)
    (by simpa using congrArg g b.ρ_root)
    (fun i => g.comp (b.t i)) (fun i => by simp [b.t_ω])
    (fun i j hij => by
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      simpa [Function.comp_def] using h)
  refine ⟨R₁, inferInstance, hN, b₁, S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom R₁.subtype), hpu, ?_, ?_⟩
  · rw [gam_toSpecΓ]
    exact h1.symm
  · intro i c
    rw [gam_toSpecΓ]
    exact (h2 i c).symm
