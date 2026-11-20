import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionOfEigenCentralSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller

namespace UpperTheory.GalC

attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk

/- English proof (translation)
Set `zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))` to `fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose`. Set `z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))` to `∑ p, if goodVec D p then zc p else 0`. Establish `hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv))`. Introduce `p`. Take `⟨L, hnd, hall, he⟩` from `(hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec`.

Rewrite using `[he]`. Use `congr 1`. Establish `e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) = L.map fun kv => plc kv (ESer D kv (p kv))` using `List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _`. Rewrite using `[e1, GlobalTheory.PassOp.prod_plc _ L hnd]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[if_pos (hall j)]`. Establish `hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0`. Rewrite using `[e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]`. Use `show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `split_ifs with hg`. Conclude with `hp p`. Simplify using the standard rewrite rules.

Establish `hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))` using `Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm`. Use `⟨z, fun F => ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Unfold `NTypes.onMt`. Rewrite using `[dif_pos (Subalgebra.smul_mem _ hcen _), dif_pos hcen, ← LinearMap.smul_apply, ← map_smul]`.

Both sides reduce to the same expression.
-/
theorem exists_unit_one_add_generator (D : D7) (hCen : GlobalTheory.Pass.CentralElt D) (i : D.nd.Loc) :
    ∃ z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))), ∀ F,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  refine ⟨z, fun F => ?_⟩
  rw [hz]
  unfold NTypes.onMt
  rw [dif_pos (Subalgebra.smul_mem _ hcen _), dif_pos hcen, ← LinearMap.smul_apply, ← map_smul]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hF` to reduce the goal to its premises. Set `ef` to `fun p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) => GlobalTheory.CutAtGood.ef (D := D) (fun kv => Formalism.CyclotomicNorms.monicOf (p kv))`. Establish `ht : ∀ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)), tens (fun kv => ESer D kv (p kv)) = ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd))`.

Introduce `p`. Establish `hnd` using `(Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).nodup_toList`. Establish `hall : ∀ kv, kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList` using `fun kv => by simp`. Rewrite using `[← GlobalTheory.CutAtGood.list_prod_eq _ _ hnd hall]`. Establish `e1 : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) = (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => plc kv (ESer D kv (p kv))` using `List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _`.

Rewrite using `[e1, GlobalTheory.PassOp.prod_plc _ _ hnd]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Rewrite using `[if_pos (hall q)]`. Establish `he : D.ntypes.e0 = ((∑ p, if goodVec D p then ∏ kv, ef p kv else 0 : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd))`.

Rewrite using `[e0_eq, eGood, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `split_ifs with hg`. Conclude with `ht p`. Both sides reduce to the same expression.

Rewrite using `[he, GlobalTheory.CutAtGood.onMt_coe, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Use `split_ifs with hg`. Assume the negation of the conclusion as `hc`. Take `⟨k, v, h0⟩` from `hcon (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩)) hg`.

Use `GlobalTheory.CutAtGood.cen_prod_ne _ _ _ F hc ⟨k, v⟩ (Finset.mem_univ _) ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.CutAtGood.onMt_coe]`. Conclude with `h0`. Rewrite using `[map_zero]`. Both sides reduce to the same expression.
-/
theorem exists_tuple (D : D7) (μ : D.what₂.Tup) (j : ℕ) (F : D.what₂.Mt μ j) (hF : D.ntypes.onMt μ j D.ntypes.e0 F ≠ 0) :
    ∃ s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X], D.ntypes.goodTuple s ∧
      ∀ k v, D.ntypes.onMt μ j (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s k v))) F ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hF
  let ef := fun p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) =>
    GlobalTheory.CutAtGood.ef (D := D) (fun kv => Formalism.CyclotomicNorms.monicOf (p kv))
  have ht : ∀ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      tens (fun kv => ESer D kv (p kv)) = ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) := by
    intro p
    have hnd := (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).nodup_toList
    have hall : ∀ kv, kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList := fun kv => by simp
    rw [← GlobalTheory.CutAtGood.list_prod_eq _ _ hnd hall]
    have e1 : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ _ hnd]
    congr 1
    funext q
    rw [if_pos (hall q)]
  have he : D.ntypes.e0 = ((∑ p, if goodVec D p then ∏ kv, ef p kv else 0 :
      ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    rw [e0_eq, eGood, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact ht p
    · rfl
  rw [he, GlobalTheory.CutAtGood.onMt_coe, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hg
  · by_contra hc
    obtain ⟨k, v, h0⟩ := hcon (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩)) hg
    refine GlobalTheory.CutAtGood.cen_prod_ne _ _ _ F hc ⟨k, v⟩ (Finset.mem_univ _) ?_
    rw [← GlobalTheory.CutAtGood.onMt_coe]
    exact h0
  · rw [map_zero]; rfl

/- English proof (translation)
Establish `hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)), Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0) ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))`. Introduce `τ _`. Use `split_ifs`. Conclude with `GlobalTheory.CutAtGood.atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b`. Rewrite using `[GlobalTheory.CutAtGood.atPlace_zero]`.

Conclude with `Subalgebra.zero_mem _`. Rewrite `h1` using `[P.eSer_eq k, GlobalTheory.CutAtGood.atPlace_sum, GlobalTheory.CutAtGood.onMt_sum D _ _ _ _ hc, LinearMap.sum_apply]`. Take `⟨τ, -, hτ⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h1`. Distinguish the cases in `hlab : (P.lz k).lab τ = f`. Rewrite `hτ` using `[if_pos hlab]`.

Conclude with `⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩`. It suffices to derive a contradiction. Apply `hτ` to reduce the goal to its premises. Rewrite using `[if_neg hlab, GlobalTheory.CutAtGood.atPlace_zero]`. Unfold `NTypes.onMt`.

Rewrite using `[dif_pos (Subalgebra.zero_mem _)]`. Establish `e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0` using `rfl`. Rewrite using `[e0, map_zero]`. Both sides reduce to the same expression.
-/
theorem exists_type (D : D7) (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (PI : D.naut.AV i) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X])
    (h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) :
    ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = f := by
  classical
  have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
      Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
    intro τ _
    split_ifs
    · exact GlobalTheory.CutAtGood.atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
    · rw [GlobalTheory.CutAtGood.atPlace_zero]
      exact Subalgebra.zero_mem _
  rw [P.eSer_eq k, GlobalTheory.CutAtGood.atPlace_sum, GlobalTheory.CutAtGood.onMt_sum D _ _ _ _ hc, LinearMap.sum_apply] at h1
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hlab : (P.lz k).lab τ = f
  · rw [if_pos hlab] at hτ
    exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
  · exfalso
    apply hτ
    rw [if_neg hlab, GlobalTheory.CutAtGood.atPlace_zero]
    unfold NTypes.onMt
    rw [dif_pos (Subalgebra.zero_mem _)]
    have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
    rw [e0, map_zero]
    rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `hg k`. Use `⟨h1.1 v, h1.2.1 v, fun u hu hr => ?_⟩` and prove the remaining obligations. Take `⟨ℓ, hℓg, hℓ⟩` from `Nat.exists_infinite_primes (D.host.g k + 1)`. Establish `hℓne : ℓ ≠ D.host.g k` using `by omega`. Establish `hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈ Formalism.CyclotomicNorms.rootsBar (s k v)`.

Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[Polynomial.mem_roots (Polynomial.map_monic_ne_zero (h1.1 v).1)]`. Conclude with `hr.map`. Break down `hu with rfl | rfl` into its components or cases. Conclude with `h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl`.

Conclude with `h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl`.
-/
theorem tuple_labels {D : D7} {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s) (i : D.nd.Loc)
    (k : Fin 2) (v : D.nd.PlG k) :
    ((s k v).Monic ∧ (s k v).natDegree = D.R.r ∧ (s k v).coeff 0 ≠ 0) ∧ Squarefree (s k v) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (s k v).IsRoot (u : ZMod (D.host.g k)) := by
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.1 v, h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (s k v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (h1.1 v).1)]
    exact hr.map
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.TypePlaceCover.place_cover D k w hw`. Take `⟨τ, hτ, e⟩` from `hs k v`. Take `⟨-, a, b⟩` from `tuple_labels hg i k v`. Conclude with `UpperTheory.GalS.nc_of_label Q hDZ h1 i k v PI τ hτ (e ▸ a) (e ▸ b) w hv`.
-/
theorem nc_of_type (D : D7) (Q : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ Q) (h1 : SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (i : D.nd.Loc) (PI : D.naut.AV i)
    {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s)
    (hs : ∀ k v, ∃ τ ∈ Q.kty i PI k v, (Q.lz k).lab τ = s k v) (k : Fin 2) (w : PlE D.host)
    (hw : w ∈ placesOver D.host.E (D.host.g k)) : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i PI w) := by
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  obtain ⟨τ, hτ, e⟩ := hs k v
  obtain ⟨-, a, b⟩ := tuple_labels hg i k v
  exact UpperTheory.GalS.nc_of_label Q hDZ h1 i k v PI τ hτ (e ▸ a) (e ▸ b) w hv

/- English proof (translation)
Take `⟨-, ⟨Q, hDZ, hEig⟩, -, hSer⟩` from `hT`. Establish `h0 : SumRepresentations.tie0 D` using `hP.adm.1.1.1`. Establish `h1 : SumRepresentations.adm1 D` using `hP.adm.1.1.2.2.1`. Establish `h5 : SumRepresentations.adm5 D` using `hP.adm.1.1.2.2.2.2.2.2`. Establish `h41 : SumRepresentations.Conclusion41 D` using `hP.Conclusion1.1`.

Set `Xs : ∀ i, Set (D.nd.X i)` to `fun i => {x | ∃ PI, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F ≠ 0}`. Establish `hZ : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ D.nd.Z i` using `fun i x hx => (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1`. Establish `hgood : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ Xs i` using `fun i x hx => by`. Take `⟨PI, hPI⟩` from `D.naut.pt_surj i x`. Take `⟨F, hF, hF0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i PI)`.

Conclude with `⟨PI, hPI, F, hF, by`. Rewrite using `[(GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx]`. Conclude with `hF0⟩`. Use `⟨⟨fun i => (D.nd.Zgood i).Nonempty, Xs, fun i ⟨x, hx⟩ => ⟨x, hgood i x hx⟩⟩, fun _ => Iff.rfl, hgood, fun i x hx ⟨PI, hPI, F, hF, hne⟩ => ?_, fun i _ => ?_, fun i _ P x ⟨PI, hPI, F, hF, hne⟩ hx k w hw => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxg`.

Conclude with `hne ((GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg)`. Take `⟨z, hact⟩` from `exists_unit_one_add_generator D (hCen D Q) i`. Use `⟨Q.zO i z, Q.zO_comm i z, fun x hx u hu => ?_, fun x hx u hu => ?_⟩` and prove the remaining obligations. Use `hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by` as an intermediate fact. Rewrite using `[hact, (GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx, map_natCast]) u hu`.

Rewrite using `[this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]`. Use `hEig i z x 0 (fun PI hPI F hF => by` as an intermediate fact. Establish `e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨PI, hPI, F, hF, hne⟩`.

Rewrite using `[hact, e, smul_zero, map_zero, zero_smul]) u hu`. Rewrite using `[this, zero_smul]`. Take `⟨s, hg, hs⟩` from `exists_tuple D _ _ F hne`. Establish `hn` using `nc_of_type D Q hDZ h1 h0 i PI hg (fun k v => exists_type D Q i PI F hF k v _ (hs k v)) k w hw`. Take `⟨Pa, hB⟩` from `h1 i PI`.

Take `⟨Pa', hB'⟩` from `h1 i P`. Establish `hperm : Pa.Perm Pa'` using `((h41 i).2.1 PI P (by rw [hPI]; exact Option.some_ne_none x) (hPI.trans hx.symm)).1 Pa Pa' hB hB'`. Establish `hB2` using `GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB'`. Establish `hsp` using `GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw`. Rewrite `hn` using `[← hB.2.2.2.1 w hsp, hB2.2.2.2.1 w hsp]`. Then use the resulting hypothesis.
-/
theorem exists_good (hCen : ∀ (D : D7) (_ : PairedCharacterCondition.Pend D), GlobalTheory.Pass.CentralElt D) {D : D7} {nch : NChoice D} (hP : Pre D nch)
    (hT : Tie4 D) : ∃ c : CutD D, c.Good := by
  classical
  obtain ⟨-, ⟨Q, hDZ, hEig⟩, -, hSer⟩ := hT
  have h0 : SumRepresentations.tie0 D := hP.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := hP.adm.1.1.2.2.1
  have h5 : SumRepresentations.adm5 D := hP.adm.1.1.2.2.2.2.2.2
  have h41 : SumRepresentations.Conclusion41 D := hP.Conclusion1.1
  let Xs : ∀ i, Set (D.nd.X i) := fun i => {x | ∃ PI, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F ≠ 0}
  have hZ : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ D.nd.Z i := fun i x hx => (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
  have hgood : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ Xs i := fun i x hx => by
    obtain ⟨PI, hPI⟩ := D.naut.pt_surj i x
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i PI)
    exact ⟨PI, hPI, F, hF, by
      rw [(GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx]; exact hF0⟩
  refine ⟨⟨fun i => (D.nd.Zgood i).Nonempty, Xs, fun i ⟨x, hx⟩ => ⟨x, hgood i x hx⟩⟩,
    fun _ => Iff.rfl, hgood, fun i x hx ⟨PI, hPI, F, hF, hne⟩ => ?_, fun i _ => ?_, fun i _ P x ⟨PI, hPI, F, hF, hne⟩ hx k w hw => ?_⟩
  · by_contra hxg
    exact hne ((GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg)
  · obtain ⟨z, hact⟩ := exists_unit_one_add_generator D (hCen D Q) i
    refine ⟨Q.zO i z, Q.zO_comm i z, fun x hx u hu => ?_, fun x hx u hu => ?_⟩
    · have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
        rw [hact, (GlobalTheory.PassOp.eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx, map_natCast]) u hu
      rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
    · have := hEig i z x 0 (fun PI hPI F hF => by
        have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0 := by
          by_contra hne
          exact hx ⟨PI, hPI, F, hF, hne⟩
        rw [hact, e, smul_zero, map_zero, zero_smul]) u hu
      rw [this, zero_smul]
  · obtain ⟨s, hg, hs⟩ := exists_tuple D _ _ F hne
    have hn := nc_of_type D Q hDZ h1 h0 i PI hg (fun k v => exists_type D Q i PI F hF k v _ (hs k v)) k w hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨Pa', hB'⟩ := h1 i P
    have hperm : Pa.Perm Pa' := ((h41 i).2.1 PI P (by rw [hPI]; exact Option.some_ne_none x)
      (hPI.trans hx.symm)).1 Pa Pa' hB hB'
    have hB2 := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB'
    have hsp := GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw
    rwa [← hB.2.2.2.1 w hsp, hB2.2.2.2.1 w hsp] at hn

end UpperTheory.GalC
