import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Use `letI : Module (ResidueField O) M := h.module`. Use `haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower`. Use `(Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx` as an intermediate fact. Use `push Not at this`. Take `⟨φ, hφ⟩` from `this`.

Conclude with `⟨φ.restrictScalars O, hφ⟩`.
-/
private theorem co_span_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

/- English proof (translation)
Introduce `O _ _ R _ _ _ B _ _ _ i S hS H x hx`. Use `set I : Ideal R := Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 with hI`. Assume the negation of the conclusion as `hxI`. Establish `hIm : I ≤ maximalIdeal R`. Use `sup_le (sup_le (Ideal.span_le.2 hS) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)) (Ideal.pow_le_self two_ne_zero)` and prove the remaining obligations.

Use `show i b ∈ maximalIdeal R`. Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`. Conclude with `hb`. Establish `hB : ∀ b ∈ maximalIdeal B, i b ∈ I` using `fun b hb => Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))`. Establish `hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I` using `fun a ha => by`.

Use `hB (algebraMap O B a) (fun h => ha (IsLocalHom.map_nonunit a h))` as an intermediate fact. Rewrite `this` using `[AlgHom.commutes]`. Then use the resulting hypothesis. Set `N : Submodule O R` to `I.restrictScalars O ⊔ Submodule.span O {1}`. Establish `hIN : ∀ y ∈ I, y ∈ N` using `fun y hy => Submodule.mem_sup_left hy`. Establish `hON : ∀ a : O, algebraMap O R a ∈ N` using `fun a => Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)`.

Establish `hxN : N.mkQ x ≠ 0`. Introduce `h`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Rewrite `hyz` using `[← Algebra.algebraMap_eq_smul_one]`.

Establish `h1 : algebraMap O R a ∈ maximalIdeal R`. Use `Ideal.sub_mem _ hx (hIm hy)` as an intermediate fact. Rewrite `this` using `[← hyz, add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `h2 : a ∈ maximalIdeal O` using `fun h => h1 (h.map _)`. Conclude with `hxI (hyz ▸ I.add_mem hy (hO a h2))`.

Establish `htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O)`. Introduce and unpack `y ⟨a, ha⟩`. Take `⟨y, rfl⟩` from `N.mkQ_surjective y`. Use `show a • N.mkQ y = 0`. Rewrite using `[← map_smul]`.

Use `(Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `I.mul_mem_right _ (hO a ha)`. Take `⟨φ, hφ⟩` from `co_span_dual O _ htor _ hxN`. Set `D : R →ₗ[O] ResidueField O` to `φ ∘ₗ N.mkQ`.

Establish `hD : ∀ y ∈ N, D y = 0` using `fun y hy => by show φ (N.mkQ y) = 0`. Rewrite using `[show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]`. Establish `hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a` using `fun y a ha => by`. Use `(res_eq_zero_iff O R _).2 ha` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z` using `fun y z => by`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) y`. Take `⟨b, hb⟩` from `IsCO.res_surj (O := O) z`. Establish `h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0` using `hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))`. Establish `h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y - algebraMap O R (a * b)`.

Simplify using `only [Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, map_sub, map_add, map_add, h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]`. Simplify using `only [Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Set `f : R →ₐ[O] DualNumber (ResidueField O)` to `{ toFun := fun y => (res O R y, D y) map_one' := by`. Use `ext`. Conclude with `map_one (res O R)`. Conclude with `hD _ (by simpa using hON 1)`. Use the proof step `map_mul' := fun y z => by`.

Use `ext`. Conclude with `map_mul (res O R) y z`. Conclude with `hmul y z`. Use the proof step `map_zero' := by`. Use `ext`.

Conclude with `map_zero (res O R)`. Conclude with `map_zero D`. Use the proof step `map_add' := fun y z => by`. Use `ext`. Conclude with `map_add (res O R) y z`.

Conclude with `map_add D y z`. Use the proof step `commutes' := fun a => by`. Use `ext`. Conclude with `(res O R).commutes a`. Conclude with `hD _ (hON a) }`.

Set `f' : R →ₐ[O] DualNumber (ResidueField O)` to `(TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)`. Establish `key : ∀ y, D y = 0 → f y = f' y` using `fun y hy => by`. Use `ext`. Both sides reduce to the same expression. Conclude with `hy`.

Establish `hff : f = f'`. Use `H f f' (AlgHom.ext fun b => key _ ?_) fun s hs => key _ (hD _ (hIN _ ?_))` and prove the remaining obligations. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) b`. Use `hD _ (hIN _ (hB _ ha))` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes, map_sub, hD _ (hON a), sub_zero]`. Then use the resulting hypothesis.

Conclude with `Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span hs))`. Conclude with `hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)`.
-/
theorem UpperTheory.V.Alg.co_span :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R →
      (∀ f f' : R →ₐ[O] DualNumber (ResidueField O), f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f') →
      maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
  intro O _ _ R _ _ _ B _ _ _ i S hS H x hx
  set I : Ideal R := Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R := by
    refine sup_le (sup_le (Ideal.span_le.2 hS) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_))
      (Ideal.pow_le_self two_ne_zero)
    show i b ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hb
  have hB : ∀ b ∈ maximalIdeal B, i b ∈ I := fun b hb =>
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha => by
    have := hB (algebraMap O B a) (fun h => ha (IsLocalHom.map_nonunit a h))
    rwa [AlgHom.commutes] at this
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := co_span_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z := fun y z => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
    have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
      hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))
    have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
        - algebraMap O R (a * b) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [h2, map_sub, map_add, map_add, h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
    simp only [Algebra.smul_def]; ring
  let f : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, D y)
      map_one' := by
        ext
        · exact map_one (res O R)
        · exact hD _ (by simpa using hON 1)
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · exact hmul y z
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · exact map_zero D
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · exact map_add D y z
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · exact hD _ (hON a) }
  let f' : R →ₐ[O] DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
  have key : ∀ y, D y = 0 → f y = f' y := fun y hy => by
    ext
    · rfl
    · exact hy
  have hff : f = f' := by
    refine H f f' (AlgHom.ext fun b => key _ ?_) fun s hs => key _ (hD _ (hIN _ ?_))
    · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) b
      have := hD _ (hIN _ (hB _ ha))
      rwa [map_sub, AlgHom.commutes, map_sub, hD _ (hON a), sub_zero] at this
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span hs))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)
