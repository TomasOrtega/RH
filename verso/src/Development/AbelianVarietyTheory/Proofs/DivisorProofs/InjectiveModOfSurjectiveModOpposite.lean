import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMul

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

noncomputable section

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `haveI := D.fin`. Conclude with `Module.Finite.trans (𝓞 E) D.La`.
-/
theorem datum_finite_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

/- English proof (translation)
Use `Module.isTorsionFree_iff_smul_eq_zero.2 ?_` and prove the remaining obligations. Introduce `k x hkx`. Assume the negation of the conclusion as `hk`. Use `push_neg at hk`. Establish `hx : x = 0` using `D.unimod.1 (LinearMap.ext fun b => by`.

Use `congrArg (fun v => D.EF v b) hkx` as an intermediate fact. Simplify using `only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this`. Simplify using `using this.resolve_left hk.1)`. Conclude with `hk.2 hx`.
-/
theorem datum_isTorsionFree_int (D : Datum H) : Module.IsTorsionFree ℤ D.La := by
  refine Module.isTorsionFree_iff_smul_eq_zero.2 ?_
  intro k x hkx
  by_contra hk
  push_neg at hk
  have hx : x = 0 := D.unimod.1 (LinearMap.ext fun b => by
    have := congrArg (fun v => D.EF v b) hkx
    simp only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hk.1)
  exact hk.2 hx

/- English proof (translation)
Use `haveI := datum_finite_int D`. Use `haveI := datum_isTorsionFree_int D`. Use `haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La`. Set `f : Z →ₗ[ℤ] D.La` to `Z.subtype.toAddMonoidHom.toIntLinearMap`. Establish `hf : Function.Injective f` using `Subtype.val_injective`.

Use `haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf`. Use `haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem sub_free_finite (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Module.Free ℤ Z ∧ Module.Finite ℤ Z := by
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La
  let f : Z →ₗ[ℤ] D.La := Z.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Take `⟨hZf, hZn⟩` from `sub_free_finite D Z`. Set `ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z` to `{ toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap map_add' := fun b b' => by ext a; simp map_smul' := fun k b => by ext a; simp }`. Establish `hψ : Function.Bijective ψ`. Use `⟨fun b b' hbb => ?_, fun φ => ?_⟩` and prove the remaining obligations. Take `⟨c, -, hu⟩` from `h.2.2.1 ((ψ b).toAddMonoidHom)`.

Establish `e1` using `hu b (fun a => rfl)`. Establish `e2` using `hu b' (fun a => by rw [hbb]; rfl)`. Conclude with `e1.trans e2.symm`. Take `⟨b, hb, -⟩` from `h.2.2.1 φ.toAddMonoidHom`. Conclude with `⟨b, LinearMap.ext fun a => hb a⟩`.

Rewrite using `[(LinearEquiv.ofBijective ψ hψ).finrank_eq]`. Set `bZ` to `Module.Free.chooseBasis ℤ Z`. Rewrite using `[Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]`.
-/
theorem IsOpp.finrank_int_eq {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La} (h : IsOpp D Z Z') :
    Module.finrank ℤ Z' = Module.finrank ℤ Z := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  let ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z :=
    { toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap
      map_add' := fun b b' => by ext a; simp
      map_smul' := fun k b => by ext a; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hbb => ?_, fun φ => ?_⟩
    · obtain ⟨c, -, hu⟩ := h.2.2.1 ((ψ b).toAddMonoidHom)
      have e1 := hu b (fun a => rfl)
      have e2 := hu b' (fun a => by rw [hbb]; rfl)
      exact e1.trans e2.symm
    · obtain ⟨b, hb, -⟩ := h.2.2.1 φ.toAddMonoidHom
      exact ⟨b, LinearMap.ext fun a => hb a⟩
  rw [(LinearEquiv.ofBijective ψ hψ).finrank_eq]
  classical
  let bZ := Module.Free.chooseBasis ℤ Z
  rw [Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]

/- English proof (translation)
Take `⟨hZf, hZn⟩` from `sub_free_finite D Z`. Take `⟨hZf', hZn'⟩` from `sub_free_finite D Z'`. Establish `hrank : Module.finrank ℤ Z' = Module.finrank ℤ X`. Rewrite using `[h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]`. Set `nB : AddSubgroup X` to `(nsmulAddMonoidHom n : X →+ X).range`.

Set `nA : AddSubgroup Z'` to `(nsmulAddMonoidHom n : Z' →+ Z').range`. Set `g : Z' →+ X` to `y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom`. Set `f : Z' →+ X ⧸ nB` to `(QuotientAddGroup.mk' nB).comp g`. Establish `hf : Function.Surjective f`. Introduce and unpack `⟨x⟩`.

Take `⟨c, hc, e, he⟩` from `hs x`. Use `⟨⟨c, hc⟩, ?_⟩` and prove the remaining obligations. Use `show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x`. Rewrite using `[he, QuotientAddGroup.eq]`. Conclude with `⟨-e, by simp⟩`.

Establish `hAK : nA ≤ f.ker`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[AddMonoidHom.mem_ker]`. Use `show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0`. Rewrite using `[QuotientAddGroup.eq_zero_iff]`.

Conclude with `⟨y a, by simp⟩`. Establish `hK : f.ker.index = n ^ Module.finrank ℤ X`. Rewrite using `[AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]`. Conclude with `AddSubgroup.index_range_nsmul X n`. Establish `hA : nA.index = n ^ Module.finrank ℤ X`.

Rewrite using `[← hrank]`. Conclude with `AddSubgroup.index_range_nsmul Z' n`. Establish `hpos : 0 < n ^ Module.finrank ℤ X` using `pow_pos hn _`. Establish `hrel : nA.relIndex f.ker = 1`. Use `AddSubgroup.relIndex_mul_index hAK` as an intermediate fact.

Rewrite `this` using `[hK, hA]`. Conclude with `(Nat.mul_eq_right hpos.ne').1 this`. Establish `hmem : (⟨b, hb⟩ : Z') ∈ f.ker`. Take `⟨e, he⟩` from `hy`. Rewrite using `[AddMonoidHom.mem_ker]`.

Use `show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0`. Rewrite using `[QuotientAddGroup.eq_zero_iff, he]`. Conclude with `⟨e, rfl⟩`. Take `⟨c, hc⟩` from `AddSubgroup.relIndex_eq_one.1 hrel hmem`. Conclude with `⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩`.
-/
theorem IsOpp.mem_nsmul_of_surj_mod {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (Z Z' : Submodule (𝓞 E) D.La)
    (h : IsOpp D Z Z') (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X)
    (hs : ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) (b : D.La) (hb : b ∈ Z') (hy : ∃ e, y b = n • e) :
    ∃ e ∈ Z', b = n • e := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
    rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
      GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
  let nB : AddSubgroup X := (nsmulAddMonoidHom n : X →+ X).range
  let nA : AddSubgroup Z' := (nsmulAddMonoidHom n : Z' →+ Z').range
  let g : Z' →+ X := y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom
  let f : Z' →+ X ⧸ nB := (QuotientAddGroup.mk' nB).comp g
  have hf : Function.Surjective f := by
    rintro ⟨x⟩
    obtain ⟨c, hc, e, he⟩ := hs x
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x
    rw [he, QuotientAddGroup.eq]
    exact ⟨-e, by simp⟩
  have hAK : nA ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨y a, by simp⟩
  have hK : f.ker.index = n ^ Module.finrank ℤ X := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]
    exact AddSubgroup.index_range_nsmul X n
  have hA : nA.index = n ^ Module.finrank ℤ X := by
    rw [← hrank]
    exact AddSubgroup.index_range_nsmul Z' n
  have hpos : 0 < n ^ Module.finrank ℤ X := pow_pos hn _
  have hrel : nA.relIndex f.ker = 1 := by
    have := AddSubgroup.relIndex_mul_index hAK
    rw [hK, hA] at this
    exact (Nat.mul_eq_right hpos.ne').1 this
  have hmem : (⟨b, hb⟩ : Z') ∈ f.ker := by
    obtain ⟨e, he⟩ := hy
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff, he]
    exact ⟨e, rfl⟩
  obtain ⟨c, hc⟩ := AddSubgroup.relIndex_eq_one.1 hrel hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩

end GlobalTheory.LowFilt

/- English proof (translation)
Introduce `D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy` and use `IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy`.
-/
theorem GlobalTheory.LowFilt.inj_mod_of_surj_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e :=
  fun D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy => IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy
