import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LieCharpolyRootPairs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

noncomputable section

namespace GlobalTheory.DetCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit

section Linear

variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_bijOn_iff (W : Submodule k N) (n : ℕ) :
    (∃ v : Fin n → N, (∀ i, v i ∈ W) ∧ Set.BijOn (fun c : Fin n → k => ∑ i, c i • v i) Set.univ W) ↔
      Module.Finite k W ∧ Module.finrank k W = n := by
  constructor
  · rintro ⟨v, -, hm, hi, hs⟩
    let f : (Fin n → k) →ₗ[k] W := (Fintype.linearCombination k v).codRestrict W fun c => hm trivial
    have hf : Function.Bijective f := by
      refine ⟨fun c c' h => hi trivial trivial (congrArg Subtype.val h), fun w => ?_⟩
      obtain ⟨c, -, hc⟩ := hs w.2
      exact ⟨c, Subtype.ext hc⟩
    have e := LinearEquiv.ofBijective f hf
    exact ⟨Module.Finite.equiv e, by simpa using e.finrank_eq.symm⟩
  · rintro ⟨_, h⟩
    let b := Module.finBasisOfFinrankEq k W h
    have hb : ∀ c : Fin n → k, ∑ i, c i • (b i : N) = (b.equivFun.symm c : W) := fun c => by
      simp [Module.Basis.equivFun_symm_apply]
    refine ⟨fun i => b i, fun i => (b i).2, fun c _ => ?_, fun c _ c' _ h => ?_, fun w hw => ?_⟩
    · simp only [hb]; exact Subtype.property _
    · simp only [hb] at h; exact b.equivFun.symm.injective (Subtype.ext h)
    · exact ⟨b.equivFun ⟨w, hw⟩, trivial, by simp only [hb, LinearEquiv.symm_apply_apply]⟩

end Linear

variable {S : Scheme.{0}} {k : Type} [Field k]

variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem mem_lie_iff (t : Sp k ⟶ S) (v : epsPt t ⟶ G) :
    v ∈ Lie G t ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left :=
  ⟨fun h => congrArg (fun φ => φ.left) (show origin t ≫ v = 1 from h), fun h => Over.OverMorphism.ext h⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isLieEigen_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔ ∃ h : v ∈ Lie G t, (⟨v, h⟩ : Lie G t) ∈ eigenspace act t τ :=
  ⟨fun h => ⟨(mem_lie_iff t v).2 h.1, fun a => Subtype.ext (Over.OverMorphism.ext (h.2 a))⟩,
    fun ⟨h, h'⟩ => ⟨(mem_lie_iff t v).1 h, fun a => congrArg (fun φ : Lie G t => φ.1.left) (h' a)⟩⟩

variable [IsCommMonObj G]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem comb_iff {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) (w : epsPt t ⟶ G) :
    (∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).1.left) ∧ w = (List.ofFn u).prod) ↔
      w = (comb v c).1 := by
  have key : (comb v c).1 = (List.ofFn fun i => (smulLie (c i) (v i)).1).prod := by
    rw [List.prod_ofFn]
    exact SubmonoidClass.coe_finset_prod (fun i => smulLie (c i) (v i)) Finset.univ
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain rfl : u = fun i => (smulLie (c i) (v i)).1 := funext fun i => Over.OverMorphism.ext (hu i)
    exact key.symm
  · rintro rfl
    exact ⟨fun i => (smulLie (c i) (v i)).1, fun _ => rfl, key⟩

def lieEquiv (t : Sp k ⟶ S) : Lie G t ≃ TanSp t G where
  toFun v := TanSp.mk v.1 (smT_zero_of t _ ((mem_lie_iff t _).1 v.2))
  invFun m := ⟨m.pt, (mem_lie_iff t _).2 (unit_of_smT_zero t _ m.tan)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lieEquiv_smul {t : Sp k ⟶ S} (c : k) (v : Lie G t) : lieEquiv t (smulLie c v) = c • lieEquiv t v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lieEquiv_act (act : OAct O G) (t : Sp k ⟶ S) (a : O) (v : Lie G t) :
    lieEquiv t (actLie act t a v) = TanSp.act t act a (lieEquiv t v) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lieEquiv_comb {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) :
    lieEquiv t (comb v c) = ∑ i, c i • lieEquiv t (v i) := by
  apply TanSp.ext
  rw [TanSp.pt_sum]
  exact SubmonoidClass.coe_finset_prod (fun i => smulLie (c i) (v i)) Finset.univ

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem mem_eigenspace_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : Lie G t) :
    v ∈ eigenspace act t τ ↔ lieEquiv t v ∈ eigenSub (TanSp.act t act) τ := by
  rw [mem_eigenSub]
  refine forall_congr' fun a => ?_
  rw [← lieEquiv_act, ← lieEquiv_smul, (lieEquiv t).injective.eq_iff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comb_mem {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by
  rw [mem_eigenspace_iff, lieEquiv_comb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((mem_eigenspace_iff act t τ _).1 (hv i))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem lieMult_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    LieMult act t τ n ↔ HasEigenDim act t τ n := by
  constructor
  · rintro ⟨v, hv, h⟩
    choose h1 h2 using fun i => (isLieEigen_iff act t τ _).1 (hv i)
    let v' : Fin n → Lie G t := fun i => ⟨v i, h1 i⟩
    have h' : ∀ w ∈ eigenspace act t τ, ∃! c, w = comb v' c := fun w hw => by
      have := h w.1 ((isLieEigen_iff act t τ _).2 ⟨w.2, hw⟩)
      exact (existsUnique_congr fun c => (comb_iff v' c w.1).trans Subtype.ext_iff.symm).1 this
    refine ⟨v', h2, fun c _ => comb_mem h2 c, fun c _ c' _ e => (h' _ (comb_mem h2 c)).unique rfl e,
      fun w hw => ?_⟩
    obtain ⟨c, hc, -⟩ := h' w hw
    exact ⟨c, trivial, hc.symm⟩
  · rintro ⟨v, hv, -, hi, hs⟩
    refine ⟨fun i => (v i).1, fun i => (isLieEigen_iff act t τ _).2 ⟨(v i).2, hv i⟩, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := (isLieEigen_iff act t τ _).1 hw
    obtain ⟨c, -, hc⟩ := hs h2
    refine (existsUnique_congr fun c => comb_iff v c w).2 ⟨c, (congrArg Subtype.val hc).symm, fun c' hc' => ?_⟩
    exact hi trivial trivial ((Subtype.ext hc' : (⟨w, h1⟩ : Lie G t) = comb v c').symm.trans hc.symm)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem hasEigenDim_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    HasEigenDim act t τ n ↔ Module.Finite k (eigenSub (TanSp.act t act) τ) ∧
      Module.finrank k (eigenSub (TanSp.act t act) τ) = n := by
  rw [← exists_bijOn_iff]
  refine (Equiv.piCongrRight fun _ => lieEquiv t).exists_congr fun v => and_congr
    (forall_congr' fun i => mem_eigenspace_iff act t τ _) ?_
  have h1 : (fun c : Fin n → k => ∑ i, c i • (Equiv.piCongrRight fun _ => lieEquiv t) v i) =
      lieEquiv t ∘ comb v := funext fun c => (lieEquiv_comb v c).symm
  have h2 : Set.BijOn (lieEquiv t) (eigenspace act t τ) (eigenSub (TanSp.act t act) τ) :=
    (lieEquiv t).bijOn (mem_eigenspace_iff act t τ · |>.symm)
  rw [h1]
  refine ⟨h2.comp, fun h => ?_⟩
  have := ((lieEquiv t).bijOn_symm.2 h2).comp h
  rwa [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp] at this

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem bijective_restrict [CharZero k] :
    Function.Bijective fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
  refine ⟨fun φ ψ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => RingHom.congr_fun h a, fun τ => ?_⟩
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem exists_splitting [CharZero k] [IsAlgClosed k] :
    ∃ _ : Fintype (𝓞 E →+* k), IsSplitting fun τ : 𝓞 E →+* k => τ := by
  classical
  let e := Equiv.ofBijective _ (bijective_restrict (E := E) (k := k))
  let F : Fintype (𝓞 E →+* k) := Fintype.ofEquiv _ e
  refine ⟨F, isSplitting_of_isDomain (σ := fun τ : 𝓞 E →+* k => τ) Function.injective_id ?_ (RingHom.id k) ?_⟩
  · rw [← NumberField.Embeddings.card E k]
    exact Fintype.card_congr e.symm
  · simpa using NumberField.discr_ne_zero E

variable [IsCMField E]

end GlobalTheory.DetCompare
