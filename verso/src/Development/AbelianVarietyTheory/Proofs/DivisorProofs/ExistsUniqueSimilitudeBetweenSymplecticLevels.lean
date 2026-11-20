import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOnFibreUniqueTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

open scoped TensorProduct

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[TensorProduct.piScalarRight_apply, reduceMod]`.
-/
theorem piScalarRight_tmul_one {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) :
    TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h) ((1 : ZMod M) ⊗ₜ[ℤ] a) = reduceMod M a := by
  funext i
  simp [TensorProduct.piScalarRight_apply, reduceMod]

/- English proof (translation)
Simplify using `[omegaMod, omegaStd, reduceMod]`.
-/
theorem omegaMod_reduceMod {h M : ℕ} (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage g).hom, by simp [spMap]⟩`.
-/
theorem sp_exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp B ⟶ Sp A) : ∃ f : A →+* B, g = spMap f :=
  ⟨(Spec.preimage g).hom, by simp [spMap]⟩

/- English proof (translation)
Introduce `p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Take `⟨hadd, -, hgeo⟩` from `H`. Take `⟨hadd', -, hgeo'⟩` from `H'`. Take `⟨β, hβ⟩` from `sp_exists_spMap t₁`.

Take `⟨β', hβ'⟩` from `sp_exists_spMap t₁'`. Establish `hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1` using `fun g₀ => by`. Rewrite using `[← map_pow, zetaAway_pow_self M hM.ne', map_one]`. Set `z : Kˣ` to `Units.ofPowEqOne _ M (hζ β) hM.ne'`. Set `z' : Kˣ` to `Units.ofPowEqOne _ M (hζ β') hM.ne'`.

Take `⟨hk, hon, hW⟩` from `hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl`. Take `⟨hk', hon', hW'⟩` from `hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl`. Set `jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x` to `Over.homMk (𝟙 _) rfl`. Establish `canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g`. Introduce `f g e`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `congrArg CommaMorphism.left e` as an intermediate fact. Simplify `this` using `[jx]`. Set `φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A)` to `fun a => jx ≫ lv a`. Set `φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A)` to `fun a => jx ≫ lv' a`.

Establish `hφ : ∀ a c, φ (a + c) = φ a * φ c` using `fun a c => by simp only [φ, hadd, MonObj.comp_mul]`. Establish `hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c` using `fun a c => by simp only [φ', hadd', MonObj.comp_mul]`. Establish `hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c` using `fun a => hk a`. Establish `hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c` using `fun a => hk' a`. Establish `hr : ∀ b, ∃ c, φ c = φ' b` using `fun b => hon (φ' b) (by`.

Rewrite using `[← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])`. Establish `hr' : ∀ c, ∃ b, φ' b = φ c` using `fun c => hon' (φ c) (by`. Rewrite using `[← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])`. Take `⟨e, he⟩` from `GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'`. Set `E` to `TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)`.

Set `e'` to `E.symm.trans (e.trans E)`. Establish `he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b`. Introduce `b c`. Rewrite using `[← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]`. Use `show E (e (E.symm (E _))) = E _ ↔ _`.

Rewrite using `[LinearEquiv.symm_apply_apply, E.injective.eq_iff]`. Establish `hz : IsPrimitiveRoot z M` using `IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)`. Take `⟨i, hcop, he_i⟩` from `exists_pow_of_isLocalRing hM.ne' β β'`. Establish `hzi : z ^ i = z'` using `Units.ext (by`. Rewrite using `[Units.val_pow_eq_pow_val]`.

Conclude with `he_i.symm)`. Establish `h2u : IsUnit (2 : ZMod M)`. Use `(ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hval : ∀ a b c d, φ c = φ' a → φ d = φ' b → ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M)`.

Introduce `a b c d hc hd`. Establish `w₁` using `hW c d`. Establish `w₂` using `hW' a b`. Express the relevant statement in the definitionally equal form `Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂`. Express the relevant statement in the definitionally equal form `Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁`.

Rewrite `w₂` using `[← hc, ← hd]`. Establish `e₁` using `H1.unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)`. Rewrite `e₁` using `[← hzi, ← zpow_natCast, ← zpow_mul]`. Establish `h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1`. Rewrite using `[zpow_sub, e₁, mul_inv_cancel]`.

Rewrite `h2` using `[hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at h2`. Establish `h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0`. Take the linear combination `h2`. Establish `h4` using `h2u.mul_right_eq_zero.1 h3`.

Take the linear combination `-h4`. Establish `hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y`. Introduce `X Y`. Take `⟨a, rfl⟩ : ∃ a, reduceMod M a = X` from `⟨liftMod X, reduceMod_liftMod X⟩`. Take `⟨b, rfl⟩ : ∃ b, reduceMod M b = Y` from `⟨liftMod Y, reduceMod_liftMod Y⟩`.

Take `⟨c, hc⟩` from `hr a`. Take `⟨d, hd⟩` from `hr b`. Rewrite using `[(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]`. Conclude with `hval a b c d hc hd`. Establish `hsim : e' ∈ sympSimGrp h M` using `⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩`.

Set `a₀ : sympSimGrp h M` to `⟨e', hsim⟩`. Establish `hmul₀ : IsMultOf a₀ i` using `hmul`. Use `⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨n, hn, hσn⟩` from `hσ a₀`. Establish `hni : (n : ZMod M) = i` using `isMultOf_unique hh hn hmul₀`.

Establish `hc : β.comp (σ a₀) = β'` using `cycAway_hom_ext hM.ne' (by`. Rewrite using `[RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])`. Rewrite using `[hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]`. Express the relevant statement in the definitionally equal form `φ (liftMod (e' (reduceMod M c))) = φ' c`. Conclude with `(he' c _).1 (reduceMod_liftMod _).symm`.

Introduce and unpack `a ⟨-, ha⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearEquiv.ext` to reduce the goal to its premises. Introduce `X`. Take `⟨b', rfl⟩ : ∃ b', reduceMod M b' = X` from `⟨liftMod X, reduceMod_liftMod X⟩`.

Establish `h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b'` using `congrArg (jx ≫ ·) (ha b')`. Rewrite using `[← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]`. Conclude with `((he' b' _).2 h1).symm`.
-/
theorem sympCond_fibre_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  intro p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, -, hgeo⟩ := H
  obtain ⟨hadd', -, hgeo'⟩ := H'
  obtain ⟨β, hβ⟩ := sp_exists_spMap t₁
  obtain ⟨β', hβ'⟩ := sp_exists_spMap t₁'
  have hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1 := fun g₀ => by
    rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
  let z : Kˣ := Units.ofPowEqOne _ M (hζ β) hM.ne'
  let z' : Kˣ := Units.ofPowEqOne _ M (hζ β') hM.ne'
  obtain ⟨hk, hon, hW⟩ := hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl
  obtain ⟨hk', hon', hW'⟩ := hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl
  let jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 _) rfl
  have canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g := by
    intro f g e
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left e
    simpa [jx] using this
  let φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv a
  let φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv' a
  have hφ : ∀ a c, φ (a + c) = φ a * φ c := fun a c => by simp only [φ, hadd, MonObj.comp_mul]
  have hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c := fun a c => by simp only [φ', hadd', MonObj.comp_mul]
  have hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c := fun a => hk a
  have hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c := fun a => hk' a
  have hr : ∀ b, ∃ c, φ c = φ' b := fun b => hon (φ' b) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])
  have hr' : ∀ c, ∃ b, φ' b = φ c := fun c => hon' (φ c) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])
  obtain ⟨e, he⟩ := GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'
  let E := TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)
  let e' := E.symm.trans (e.trans E)
  have he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b := by
    intro b c
    rw [← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]
    show E (e (E.symm (E _))) = E _ ↔ _
    rw [LinearEquiv.symm_apply_apply, E.injective.eq_iff]
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)
  obtain ⟨i, hcop, he_i⟩ := exists_pow_of_isLocalRing hM.ne' β β'
  have hzi : z ^ i = z' := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact he_i.symm)
  have h2u : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)
    exact_mod_cast this
  have hval : ∀ a b c d, φ c = φ' a → φ d = φ' b →
      ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) := by
    intro a b c d hc hd
    have w₁ := hW c d
    have w₂ := hW' a b
    change Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂
    change Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁
    rw [← hc, ← hd] at w₂
    have e₁ := H1.unitOn_injective
      (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)
    rw [← hzi, ← zpow_natCast, ← zpow_mul] at e₁
    have h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1 := by
      rw [zpow_sub, e₁, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0 := by
      linear_combination h2
    have h4 := h2u.mul_right_eq_zero.1 h3
    linear_combination -h4
  have hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y := by
    intro X Y
    obtain ⟨a, rfl⟩ : ∃ a, reduceMod M a = X := ⟨liftMod X, reduceMod_liftMod X⟩
    obtain ⟨b, rfl⟩ : ∃ b, reduceMod M b = Y := ⟨liftMod Y, reduceMod_liftMod Y⟩
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hr b
    rw [(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]
    exact hval a b c d hc hd
  have hsim : e' ∈ sympSimGrp h M :=
    ⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩
  let a₀ : sympSimGrp h M := ⟨e', hsim⟩
  have hmul₀ : IsMultOf a₀ i := hmul
  refine ⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hσn⟩ := hσ a₀
    have hni : (n : ZMod M) = i := isMultOf_unique hh hn hmul₀
    have hc : β.comp (σ a₀) = β' := cycAway_hom_ext hM.ne' (by
      rw [RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])
    rw [hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · change φ (liftMod (e' (reduceMod M c))) = φ' c
    exact (he' c _).1 (reduceMod_liftMod _).symm
  · rintro a ⟨-, ha⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    obtain ⟨b', rfl⟩ : ∃ b', reduceMod M b' = X := ⟨liftMod X, reduceMod_liftMod X⟩
    have h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b' :=
      congrArg (jx ≫ ·) (ha b')
    rw [← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]
    exact ((he' b' _).2 h1).symm

end GlobalTheory.HTSympCover
