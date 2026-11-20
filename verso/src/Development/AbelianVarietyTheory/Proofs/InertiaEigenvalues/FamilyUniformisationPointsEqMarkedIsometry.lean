import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.PermUnif

variable {g g' : ℕ}

def permCLE (π : Fin g ≃ Fin g') : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem permCLE_apply (π : Fin g ≃ Fin g') (z : Fin g' → ℂ) (j : Fin g) : permCLE π z j = z (π j) := rfl

/- English proof (translation)
Establish `: permCLE π (fun j' => z (π.symm j')) = z` using `funext fun j => by simp`. Rewrite using `[(permCLE π).symm_apply_eq.2 this.symm]`.
-/
@[simp] theorem permCLE_symm_apply (π : Fin g ≃ Fin g') (z : Fin g → ℂ) (j : Fin g') :
    (permCLE π).symm z j = z (π.symm j) := by
  have : permCLE π (fun j' => z (π.symm j')) = z := funext fun j => by simp
  rw [(permCLE π).symm_apply_eq.2 this.symm]

def permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) : L →+ (Fin g' → ℂ) where
  toFun a j := P a (π.symm j)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem permP_apply {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L)
    (j : Fin g') : permP π P a j = P a (π.symm j) := rfl

/- English proof (translation)
The claim follows from `funext fun j => by simp`.
-/
theorem permCLE_permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L) :
    permCLE π (permP π P a) = P a := funext fun j => by simp

/- English proof (translation)
Unfold `hermForm`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, permCLE_apply]`. Rewrite using `[← Equiv.sum_comp π]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp π]`.

Simplify using the standard rewrite rules.
-/
theorem hermForm_perm (π : Fin g ≃ Fin g') (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g' → ℂ) :
    hermForm (Hm.submatrix π.symm π.symm) z w = hermForm Hm (permCLE π z) (permCLE π w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, permCLE_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Take `⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hEF⟩` from `hP`. Use `⟨fun a x j => ?_, fun x y hxy => hinj (funext fun j => ?_), ?_, ?_, ⟨Hm.submatrix π.symm π.symm, hH.submatrix _, fun z hz => ?_, fun x y => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[permP_apply, permP_apply, hlin, ← hπ, Equiv.apply_symm_apply]`. Use `congrFun hxy (π j)` as an intermediate fact. Simplify using `using this`.

Use `haveI := hdisc`. Use `DiscreteTopology.of_continuous_injective (f := fun v : (permP π P).range => (⟨permCLE π v.1, ?_⟩ : P.range)) ?_ ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `v.2`. Conclude with `⟨x, by rw [← hx, permCLE_permP]⟩`. Conclude with `Continuous.subtype_mk ((permCLE π).continuous.comp continuous_subtype_val) _`.

Introduce `v w hvw`. Conclude with `Subtype.ext ((permCLE π).injective (congrArg Subtype.val hvw))`. Establish `hr : Set.range (permP π P) = ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range P`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Use `⟨P x, ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Introduce and unpack `⟨w, ⟨x, rfl⟩, rfl⟩`.

Conclude with `⟨x, funext fun j => by simp⟩`. Rewrite using `[hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).surjective`. Rewrite using `[hermForm_perm]`. Use `hpos _ fun h0 => hz (funext fun j => ?_)` and prove the remaining obligations.

Use `congrFun h0 (π.symm j)` as an intermediate fact. Simplify using `using this`. Rewrite using `[hermForm_perm, permCLE_permP, permCLE_permP, hEF]`.
-/
theorem isPeriod_permP {D : Datum H} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (π : Fin g ≃ Fin g')
    (hπ : ∀ j, ty' (π j) = ty j) {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : IsPeriod D ty' (permP π P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hEF⟩ := hP
  refine ⟨fun a x j => ?_, fun x y hxy => hinj (funext fun j => ?_), ?_, ?_,
    ⟨Hm.submatrix π.symm π.symm, hH.submatrix _, fun z hz => ?_, fun x y => ?_⟩⟩
  · rw [permP_apply, permP_apply, hlin, ← hπ, Equiv.apply_symm_apply]
  · have := congrFun hxy (π j)
    simpa using this
  · haveI := hdisc
    refine DiscreteTopology.of_continuous_injective (f := fun v : (permP π P).range =>
      (⟨permCLE π v.1, ?_⟩ : P.range)) ?_ ?_
    · obtain ⟨x, hx⟩ := v.2
      exact ⟨x, by rw [← hx, permCLE_permP]⟩
    · exact Continuous.subtype_mk ((permCLE π).continuous.comp continuous_subtype_val) _
    · intro v w hvw
      exact Subtype.ext ((permCLE π).injective (congrArg Subtype.val hvw))
  · have hr : Set.range (permP π P) = ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range P := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨P x, ⟨x, rfl⟩, ?_⟩
        funext j
        simp
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, funext fun j => by simp⟩
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).surjective
  · rw [hermForm_perm]
    refine hpos _ fun h0 => hz (funext fun j => ?_)
    have := congrFun h0 (π.symm j)
    simpa using this
  · rw [hermForm_perm, permCLE_permP, permCLE_permP, hEF]

/- English proof (translation)
Introduce `U f`. Take `⟨ho, hd⟩` from `hy U f`. Establish `hs : {b ∈ (Set.univ : Set (Fin g' → ℂ)) | ⊤ ≤ y (L b) ⁻¹ᵁ U} = L ⁻¹' {b ∈ Set.univ | ⊤ ≤ y b ⁻¹ᵁ U}`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Rewrite using `[hs]`. Conclude with `⟨ho.preimage L.continuous, hd.comp L.differentiableOn (fun b hb => hb)⟩`.
-/
theorem isHolTo_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) {y : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (hy : IsHolTo Set.univ y) : IsHolTo Set.univ (fun z => y (L z)) := by
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hs : {b ∈ (Set.univ : Set (Fin g' → ℂ)) | ⊤ ≤ y (L b) ⁻¹ᵁ U} = L ⁻¹' {b ∈ Set.univ | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp
  rw [hs]
  exact ⟨ho.preimage L.continuous, hd.comp L.differentiableOn (fun b hb => hb)⟩

/- English proof (translation)
Unfold `IsDerivAt0`. Simplify using `only [map_zero]`. Use `and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)` and prove the remaining obligations. Rewrite using `[show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv, map_zero]`. Both sides reduce to the same expression.
-/
theorem isDerivAt0_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) (y : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo σ' g g' ty ty' F F' hpq hσ hty hty' π hπ k k' P P' hP hP' h`. Establish `hL : ∀ a, permCLE π (permP π P a) = P a` using `permCLE_permP π P`. Establish `hd` using `F.ex_diff k P hP`. Establish `key` using `GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g' ty' hpq hσ hty' (F.Di k) (F'.Di k') (F.t k) (F'.t k') (permP π P) P' (F.u k P) (F'.u k' P') (fun z => F.ex k P (permCLE π z)) (F'.ex k' P')`. Take `⟨gam, -, hEF, hM, -, -⟩` from `(key (by`.

Use `⟨F.over_σ k P hP, isPeriod_permP π hπ hP, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z w`. Rewrite using `[map_add]`. Conclude with `F.ex_add k P hP _ _`. Conclude with `(F.ex_onto k P hP).comp (permCLE π).surjective`.

Conclude with `isHolTo_comp_cle (permCLE π) (y := fun z => (F.ex k P z).left) (GlobalTheory.ClassUniq.isHolTo_ex F k P hP)`. Introduce `w`. Take `⟨v, hv, hu⟩` from `hd.1 (permCLE π w)`. Conclude with `⟨v, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v.left).2 hv, fun v' hv' => hu v' ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v'.left).1 hv')⟩`. Introduce `v hv`.

Establish `h0 : (permCLE π) 0 = 0` using `map_zero _`. Establish `hv0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (F.ex k P 0).left`. Rewrite using `[← h0]`. Conclude with `hv`. Take `⟨w, hw, hu⟩` from `hd.2 v hv0`.

Use `⟨(permCLE π).symm w, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) _ v.left).2 (by` and prove the remaining obligations. Rewrite using `[(permCLE π).apply_symm_apply]), fun w' hw' => ?_⟩` and apply the resulting hypothesis. Rewrite using `[← hu _ ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w' v.left).1 hw'), (permCLE π).symm_apply_apply]`. Introduce `z`. Use `(F.ex_ker k P hP (permCLE π z)).trans ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨x, hx⟩`. Use `⟨x, funext fun j => ?_⟩` and prove the remaining obligations. Use `congrFun hx (π.symm j)` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨x, (hL x).symm⟩`. Introduce `a z`. Establish `e : permCLE π (fun j => ty' j (a : E) * z j) = fun j => ty j (a : E) * permCLE π z j`. Use function extensionality and compare the values at `fun j => by simp [hπ]`. Rewrite using `[e]`.

Conclude with `F.ex_lin k P hP a (permCLE π z)`. Introduce `n a a₂ c hn hc`. Rewrite using `[map_smul, map_smul, hL, hL]`. Conclude with `F.ex_weil k P hP n a a₂ c hn hc`. Introduce `a ha`.

Rewrite using `[map_smul, hL]`. Conclude with `F.ex_eta k P hP a ha`. Introduce `a`. Rewrite using `[map_smul, hL]`. Conclude with `F.ex_etaA k P hP a) (by`.

Conclude with `⟨F'.over_σ k' P' hP', hP', ⟨F'.ex_add k' P' hP', F'.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F' k' P' hP', (F'.ex_diff k' P' hP').1, (F'.ex_diff k' P' hP').2⟩, F'.ex_ker k' P' hP', F'.ex_lin k' P' hP', F'.ex_weil k' P' hP', F'.ex_eta k' P' hP', F'.ex_etaA k' P' hP'⟩)) …`. Conclude with `⟨gam, hEF, hM⟩`.
-/
theorem isometry_of_point_eq_perm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  intro E _ _ _ H Dw l Xo σ' g g' ty ty' F F' hpq hσ hty hty' π hπ k k' P P' hP hP' h
  have hL : ∀ a, permCLE π (permP π P a) = P a := permCLE_permP π P
  have hd := F.ex_diff k P hP
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all
    GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g' ty' hpq hσ hty' (F.Di k) (F'.Di k') (F.t k) (F'.t k') (permP π P) P'
    (F.u k P) (F'.u k' P') (fun z => F.ex k P (permCLE π z)) (F'.ex k' P')
  obtain ⟨gam, -, hEF, hM, -, -⟩ := (key (by
    refine ⟨F.over_σ k P hP, isPeriod_permP π hπ hP, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro z w
      rw [map_add]
      exact F.ex_add k P hP _ _
    · exact (F.ex_onto k P hP).comp (permCLE π).surjective
    · exact isHolTo_comp_cle (permCLE π) (y := fun z => (F.ex k P z).left) (GlobalTheory.ClassUniq.isHolTo_ex F k P hP)
    · intro w
      obtain ⟨v, hv, hu⟩ := hd.1 (permCLE π w)
      exact ⟨v, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v.left).2 hv,
        fun v' hv' => hu v' ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v'.left).1 hv')⟩
    · intro v hv
      have h0 : (permCLE π) 0 = 0 := map_zero _
      have hv0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (F.ex k P 0).left := by
        rw [← h0]; exact hv
      obtain ⟨w, hw, hu⟩ := hd.2 v hv0
      refine ⟨(permCLE π).symm w, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) _ v.left).2 (by
        rwa [(permCLE π).apply_symm_apply]), fun w' hw' => ?_⟩
      rw [← hu _ ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w' v.left).1 hw'),
        (permCLE π).symm_apply_apply]
    · intro z
      refine (F.ex_ker k P hP (permCLE π z)).trans ⟨?_, ?_⟩
      · rintro ⟨x, hx⟩
        refine ⟨x, funext fun j => ?_⟩
        have := congrFun hx (π.symm j)
        simpa using this
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hL x).symm⟩
    · intro a z
      have e : permCLE π (fun j => ty' j (a : E) * z j) = fun j => ty j (a : E) * permCLE π z j :=
        funext fun j => by simp [hπ]
      rw [e]
      exact F.ex_lin k P hP a (permCLE π z)
    · intro n a a₂ c hn hc
      rw [map_smul, map_smul, hL, hL]
      exact F.ex_weil k P hP n a a₂ c hn hc
    · intro a ha
      rw [map_smul, hL]
      exact F.ex_eta k P hP a ha
    · intro a
      rw [map_smul, hL]
      exact F.ex_etaA k P hP a) (by
    exact ⟨F'.over_σ k' P' hP', hP', ⟨F'.ex_add k' P' hP', F'.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F' k' P' hP',
      (F'.ex_diff k' P' hP').1, (F'.ex_diff k' P' hP').2⟩, F'.ex_ker k' P' hP', F'.ex_lin k' P' hP',
      F'.ex_weil k' P' hP', F'.ex_eta k' P' hP', F'.ex_etaA k' P' hP'⟩)).1 h
  exact ⟨gam, hEF, hM⟩

end GlobalTheory.PermUnif
