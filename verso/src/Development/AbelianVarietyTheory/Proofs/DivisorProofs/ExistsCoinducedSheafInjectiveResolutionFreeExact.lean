import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionComplexAugmentationQuasiIsoStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Introduce `R S _ _ φ J _ hJ`. Use `haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ`. Set `I : InjectiveResolution ((restr φ).obj ((coind φ).obj J))` to `{ cocomplex := coindCx φ J injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n) ι := coindAug φ J }`. Use `⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `P n hn`.

Take `⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1` from `⟨(n - 1).toNat, by omega⟩`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. It suffices to establish `h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by`. Rewrite using `[h x, h y]`. Introduce `x`.

Take `⟨α, rfl⟩` from `x.mk_surjective`. Take `⟨f, hf, rfl⟩` from `Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl`. Rewrite using `[CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]`. Establish `hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b`. Introduce `b hb`.

Conclude with `((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb`. Establish `hd1` using `I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)`. Rewrite `hf` using `[hd1]`. Establish `h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0`. Rewrite using `[← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]`.

Simplify using `using hf`. Establish `hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0`. Rewrite using `[← coindCx_d]`. Conclude with `h2`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'`.

Use `⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩` and prove the remaining obligations. Rewrite using `[I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]`. Use `erw [Category.assoc, Iso.inv_hom_id_assoc]`. Establish `hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom`. Rewrite using `[← hg, ← coindCx_d]`.

Both sides reduce to the same expression. Use `erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
