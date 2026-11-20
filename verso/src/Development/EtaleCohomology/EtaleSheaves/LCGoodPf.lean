import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

open LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LCGoodPf

/- English proof (translation)
Take `⟨I, rfl⟩` from `(PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ`. Distinguish the cases in `hI : I = ⊤`. Substitute `hI` using the available equality. Simplify using the standard rewrite rules. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hI`.

It suffices to derive a contradiction. Establish `hJM : J ≤ M` using `le_trans hJ (sInf_le ⟨bot_le, hM⟩)`. Establish `hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))`. Establish `hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M` using `by rw [Ideal.mk_ker]; exact hJM`. Use `hM.isPrime` as an intermediate fact.

Establish `hpr : (M.map (Ideal.Quotient.mk J)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker`. Use `⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩` and prove the remaining obligations. Use `ext1`. Use `show Ideal.comap _ (Ideal.map _ M) = M`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]`.

Use `sup_eq_left.2 ?_` and prove the remaining obligations. Rewrite using `[← RingHom.ker_eq_comap_bot]`. Conclude with `hker`. Take `⟨z, hz⟩` from `hp`. Apply `h z` to reduce the goal to its premises.

Rewrite using `[hz]`. Conclude with `hIM`.
-/
theorem closed_empty {C : Type} [CommRing C] {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z)
    (h : ∀ z : PrimeSpectrum (C ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∉ Z) : Z = ∅ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  by_cases hI : I = ⊤
  · subst hI; simp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exfalso
  have hJM : J ≤ M := le_trans hJ (sInf_le ⟨bot_le, hM⟩)
  have hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M := by rw [Ideal.mk_ker]; exact hJM
    have := hM.isPrime
    have hpr : (M.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    refine ⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.map _ M) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.2 ?_
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  obtain ⟨z, hz⟩ := hp
  apply h z
  rw [hz]
  exact hIM

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lcMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type}
    (φ : LocallyConstant (PrimeSpectrum A) Y) (z : PrimeSpectrum B) :
    lcMap f φ z = φ (PrimeSpectrum.comap f z) := rfl

/- English proof (translation)
Establish `: IsLocallyConstant (fun x => (a x = b x : Prop))` using `IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))`. Establish `h2` using `this.isClosed_fiber False`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem isClosed_ne {X Y : Type} [TopologicalSpace X] (a b : LocallyConstant X Y) :
    IsClosed {x | a x ≠ b x} := by
  have : IsLocallyConstant (fun x => (a x = b x : Prop)) :=
    IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))
  have h2 := this.isClosed_fiber False
  convert h2 using 1
  ext x; simp

/- English proof (translation)
Introduce `C _ J hG Y`. Take `⟨hJ, hlift⟩` from `hG`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `hZ` using `closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by`.

Use `congrArg (fun φ => φ z) hab` as an intermediate fact. Simplify `this))` using `[lcMap_apply]`. Use extensionality with `x`. Assume the negation of the conclusion as `hx`. Establish `: x ∈ ({x | a x ≠ b x} : Set _)` using `hx`.

Rewrite `this` using `[hZ]`. Conclude with `this`. Introduce `ψ`. Establish `hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧ PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y}`. Introduce `y`.

Take `⟨e, he, hF⟩` from `PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)`. Take `⟨x, hx, hxe⟩` from `hlift e he`. Use `⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J)))` using `hF`. Rewrite using `[hF', ← hxe]`.

Use extensionality with `p`. Simplify using the standard rewrite rules. Use `choose U hUc hUp using hU`. Establish `hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y`. Introduce `z y`.

Use `congrArg (fun s => z ∈ s) (hUp y)` as an intermediate fact. Simplify using `using this`. Establish `hcover : ∀ x, ∃ y, x ∈ U y`. Establish `hE` using `closed_empty hJ (⋃ y, U y)ᶜ (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))`. Introduce `x`.

Assume the negation of the conclusion as `hx`. Use `push Not at hx`. Establish `: x ∈ (⋃ y, U y)ᶜ` using `by simpa using hx`. Rewrite `this` using `[hE]`. Conclude with `this`.

Establish `huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y'`. Introduce `x y y' h1 h2`. Assume the negation of the conclusion as `hne`. Use `closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed) (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))` as an intermediate fact. Establish `hx : x ∈ U y ∩ U y'` using `⟨h1, h2⟩`.

Rewrite `hx` using `[this]`. Conclude with `hx`. Set `g : PrimeSpectrum C → Y` to `fun x => Classical.choose (hcover x)`. Establish `hg : ∀ x y, g x = y ↔ x ∈ U y`. Introduce `x y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `Classical.choose_spec (hcover x)`. Introduce `h`. Conclude with `huniq x _ _ (Classical.choose_spec (hcover x)) h`.

Establish `hgl : IsLocallyConstant g`. Rewrite using `[IsLocallyConstant.iff_isOpen_fiber]`. Introduce `y`. Establish `: g ⁻¹' {y} = U y` using `by ext x; simp [hg]`. Rewrite using `[this]`.

Conclude with `(hUc y).isOpen`. Use `⟨⟨g, hgl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Rewrite using `[lcMap_apply]`. Conclude with `(hg _ _).2 ((hmem z _).2 rfl)`.
-/
theorem LCGood_of : LCGood := by
  intro C _ J hG Y
  obtain ⟨hJ, hlift⟩ := hG
  constructor
  · intro a b hab
    have hZ := closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by
      have := congrArg (fun φ => φ z) hab
      simpa [lcMap_apply] using this))
    ext x
    by_contra hx
    have : x ∈ ({x | a x ≠ b x} : Set _) := hx
    rw [hZ] at this; exact this
  · intro ψ

    have hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y} := by
      intro y
      obtain ⟨e, he, hF⟩ := PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)
      obtain ⟨x, hx, hxe⟩ := hlift e he
      refine ⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩
      have hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J))) := hF
      rw [hF', ← hxe]
      ext p
      simp
    choose U hUc hUp using hU
    have hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y := by
      intro z y
      have := congrArg (fun s => z ∈ s) (hUp y)
      simpa using this
    have hcover : ∀ x, ∃ y, x ∈ U y := by
      have hE := closed_empty hJ (⋃ y, U y)ᶜ
        (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl
        (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))
      intro x
      by_contra hx
      push Not at hx
      have : x ∈ (⋃ y, U y)ᶜ := by simpa using hx
      rw [hE] at this
      exact this
    have huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y' := by
      intro x y y' h1 h2
      by_contra hne
      have := closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed)
        (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))
      have hx : x ∈ U y ∩ U y' := ⟨h1, h2⟩
      rw [this] at hx; exact hx
    classical
    let g : PrimeSpectrum C → Y := fun x => Classical.choose (hcover x)
    have hg : ∀ x y, g x = y ↔ x ∈ U y := by
      intro x y
      constructor
      · rintro rfl; exact Classical.choose_spec (hcover x)
      · intro h; exact huniq x _ _ (Classical.choose_spec (hcover x)) h
    have hgl : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      have : g ⁻¹' {y} = U y := by ext x; simp [hg]
      rw [this]; exact (hUc y).isOpen
    refine ⟨⟨g, hgl⟩, ?_⟩
    ext z
    rw [lcMap_apply]
    exact (hg _ _).2 ((hmem z _).2 rfl)

end LateralTheory.E.LCGoodPf
