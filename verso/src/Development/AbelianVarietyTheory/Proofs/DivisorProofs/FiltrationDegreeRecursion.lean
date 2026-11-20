import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldLatticeClearsDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapMulRelIndexKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetScaleVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetSnocTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeStepCoordinateVectorsStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt

namespace GlobalTheory.LieRead

/- English proof (translation)
Take `⟨p, hp, hvec, hcoef, hW', hW⟩` from `GlobalTheory.T.lie_lattice_step_coordinate_vectors D O K F hg τ i hi`. Use `set e : Fin (i + 1) → (Fin F.P₀.g → K) := fun j => Pi.single (p j) 1 with he`. Use `set q := p (Fin.last i) with hq`. Use `set L := F.lieLat with hLdef`. Use `set S' := Submodule.span K (Set.range e) with hS'`.

Use `set S := Submodule.span K (Set.range fun j : Fin i => e j.castSucc) with hS`. Use `set W' := stepLat O F τ (i + 1) with hW'def`. Use `set W := stepLat O F τ i with hWdef`. Use `set f := (stepCoef O F τ i).restrictScalars (𝓞 K) with hfdef`. Establish `hf : ∀ v, f v = v q` using `fun v => hcoef v`.

Establish `he_app : ∀ j k, e j (p k) = if j = k then 1 else 0`. Introduce `j k`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using `[e]`.

Establish `: p k ≠ p j` using `fun h' => hjk (hp h').symm`. Simplify using `[e, Pi.single_apply, this, hjk]`. Establish `hrep : ∀ v ∈ S', v = ∑ k, v (p k) • e k`. Introduce `v hv`. Set `Φ : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)` to `∑ k, (LinearMap.proj (p k)).smulRight (e k)`.

Establish `hΦ : Set.EqOn Φ (LinearMap.id : (Fin F.P₀.g → K) →ₗ[K] _) (Set.range e)`. Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `[Φ, LinearMap.sum_apply, he_app]`. Use `LinearMap.eqOn_span' hΦ hv` as an intermediate fact. Simplify `this.symm` using `[Φ]`.

Establish `hSq : ∀ v ∈ S, v q = 0`. Introduce `v hv`. Establish `: S ≤ LinearMap.ker (LinearMap.proj q : (Fin F.P₀.g → K) →ₗ[K] K)`. Rewrite using `[hS, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `he_app j.castSucc (Fin.last i)` as an intermediate fact. Simplify using `only [Fin.castSucc_ne_last, if_false] at this`. Simplify `this` using `[q]`. Conclude with `this hv`. Establish `hSS' : S ≤ S'` using `Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.castSucc, rfl⟩)`.

Establish `hSS : ∀ v ∈ S', v q = 0 → v ∈ S`. Introduce `v hv hv0`. Rewrite using `[hrep v hv, Fin.sum_univ_castSucc, ← hq, hv0, zero_smul, add_zero]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hW'mem : ∀ x, x ∈ W' ↔ x ∈ L ∧ x ∈ S'` using `fun x => by rw [hW']; exact Iff.rfl`.

Establish `hWmem : ∀ x, x ∈ W ↔ x ∈ L ∧ x ∈ S` using `fun x => by rw [hW]; exact Iff.rfl`. Establish `hWW' : W ≤ W'` using `fun x hx => (hW'mem x).2 ⟨((hWmem x).1 hx).1, hSS' ((hWmem x).1 hx).2⟩`. Establish `hfg : ∀ N : Submodule (𝓞 K) (Fin F.P₀.g → K), N ≤ L → N.FG`. Introduce `N hN`. Use `haveI := isNoetherian_of_fg_of_noetherian L hL.1`.

Establish `h1 : (N.comap L.subtype).FG` using `IsNoetherian.noetherian _`. Use `h1.map L.subtype` as an intermediate fact. Rewrite `this` using `[Submodule.map_comap_subtype, inf_eq_right.2 hN]`. Then use the resulting hypothesis. Establish `hWfg : W.FG` using `hfg W fun x hx => ((hWmem x).1 hx).1`. Establish `hW'fg : W'.FG` using `hfg W' fun x hx => ((hW'mem x).1 hx).1`.

Establish `hden : ∀ j, ∃ d : 𝓞 K, d ≠ 0 ∧ d • e j ∈ L` using `fun j => GlobalTheory.T.number_field_lattice_clears_denominator L hL.2 (e j)`. Use `choose d hd0 hdL using hden`. Use `set dK : Fin (i + 1) → K := fun j => algebraMap (𝓞 K) K (d j) with hdK_def`. Establish `hdK : ∀ j, dK j ≠ 0` using `fun j h0 => hd0 j (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa [dK] using h0))`. Establish `hdKL : ∀ j, dK j • e j ∈ L` using `fun j => by simpa [dK, algebraMap_smul] using hdL j`.

Establish `hex : ∃ a ∈ stepIdeal O F τ i, a ≠ 0`. Use `⟨f (dK (Fin.last i) • e (Fin.last i)), ?_, ?_⟩` and prove the remaining obligations. Use `show _ ∈ W'.map f`. Use `Submodule.mem_map_of_mem ((hW'mem _).2 ⟨hdKL _, ?_⟩)` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.

Rewrite using `[hf]`. Simplify `hdK (Fin.last i)` using `[e, q]`. Use `set a := hex.choose with ha_def`. Take `⟨haI, ha0⟩` from `hex.choose_spec`. Rewrite `haI`, `ha0` using `[← ha_def]`.

Take `⟨w, hwW', hwa⟩` from `Submodule.mem_map.1 (show a ∈ W'.map f from haI)`. Establish `hwq : w q = a` using `by rw [← hf w]; exact hwa`. Use `set u : Fin i → (Fin F.P₀.g → K) := fun j => dK j.castSucc • e j.castSucc with hu_def`. Establish `huS : ∀ j, u j ∈ S` using `fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `heli : LinearIndependent K e`.

Use `(Pi.basisFun K (Fin F.P₀.g)).linearIndependent.comp p hp` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j : 1`. Simplify using `[e]`. Establish `huli : LinearIndependent K u`.

Use `(heli.comp Fin.castSucc (Fin.castSucc_injective _)).units_smul (fun j => Units.mk0 (dK j.castSucc) (hdK _))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j : 1`. Simplify using `[u, Units.smul_def]`. Establish `hSu : S ≤ Submodule.span K (Set.range u)`.

Rewrite using `[hS, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `: e j.castSucc = (dK j.castSucc)⁻¹ • u j`. Simplify using `[u, smul_smul, inv_mul_cancel₀ (hdK _)]`. Use `show e j.castSucc ∈ _`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `huS' : Submodule.span K (Set.range u) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `huS j`. Establish `hu : IsFrame K W u`. Use `⟨fun j => (hWmem _).2 ⟨hdKL _, huS j⟩, huli, fun x hx => hSu ((hWmem x).1 hx).2⟩` and prove the remaining obligations. Use `set v' : Fin (i + 1) → (Fin F.P₀.g → K) := Fin.snoc u w with hv'_def`. Establish `hwS' : w ∈ S'` using `((hW'mem w).1 hwW').2`.

Establish `hv' : IsFrame K W' v'`. Use `⟨fun k => ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `k using Fin.lastCases with`. Consider the case `last => simpa [v'] using hwW'`. Consider the case `cast j => simpa [v'] using hWW' (hu.1 j)`.

Use `linearIndependent_finSnoc.2 ⟨huli, fun hmem => ha0 ?_⟩` and prove the remaining obligations. Rewrite using `[← hwq]`. Conclude with `hSq _ (huS' hmem)`. Take `⟨hxL, hxS'⟩` from `(hW'mem x).1 hx`. Establish `hy : x - (x q / a) • w ∈ S`.

Use `hSS _ (Submodule.sub_mem _ hxS' (Submodule.smul_mem _ _ hwS')) ?_` and prove the remaining obligations. Simplify using `[hwq, div_mul_cancel₀ _ ha0]`. Rewrite using `[SetLike.mem_coe, show v' = Fin.snoc u w from rfl, Fin.range_snoc, Submodule.mem_span_insert]`. Conclude with `⟨x q / a, x - (x q / a) • w, hSu hy, by abel⟩`. Use `set U := Submodule.span (𝓞 K) (Set.range u) with hU_def`.

Use `set U' := Submodule.span (𝓞 K) (Set.range v') with hU'_def`. Establish `hUS : ∀ z ∈ U, z ∈ S` using `fun z hz => (Submodule.span_le (p := S.restrictScalars (𝓞 K))).2 (by rintro _ ⟨j, rfl⟩; exact huS j) hz`. Establish `hU'W' : U' ≤ W'` using `Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hv'.1 k)`. Establish `hmapU' : U'.map f = Submodule.span (𝓞 K) {a}`. Rewrite using `[hU'_def, Submodule.map_span, hv'_def, Fin.range_snoc, Set.image_insert_eq, hwa]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ (rfl | ⟨_, ⟨j, rfl⟩, rfl⟩)`. Conclude with `Submodule.subset_span rfl`. Rewrite using `[SetLike.mem_coe, hf, hSq _ (huS j)]`.

Conclude with `zero_mem _`. Conclude with `Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))`. Establish `hU'ker : U' ⊓ LinearMap.ker f = U`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx, hxk⟩`.

Rewrite `hx` using `[hU'_def, hv'_def, Fin.range_snoc]`. Rewrite `hx` using `[SetLike.mem_coe, Submodule.mem_span_insert]`. Take `⟨b, z, hz, rfl⟩` from `hx`. Establish `hz0 : f z = 0` using `by rw [hf]; exact hSq _ (hUS z hz)`. Establish `hba : b • a = 0`.

Use `LinearMap.mem_ker.1 hxk` as an intermediate fact. Rewrite `this` using `[map_add, map_smul, hwa, hz0, add_zero]`. Then use the resulting hypothesis. Rewrite using `[(smul_eq_zero.1 hba).resolve_right ha0, zero_smul, zero_add]`. Conclude with `hz`. Use `le_inf ?_ fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSq _ (hUS z hz))` and prove the remaining obligations.

Rewrite using `[hU_def, hU'_def]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨j.castSucc, by simp [v']⟩`. Establish `hW'ker : W' ⊓ LinearMap.ker f = W`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx, hxk⟩`. Take `⟨hxL, hxS'⟩` from `(hW'mem x).1 hx`. Conclude with `(hWmem x).2 ⟨hxL, hSS _ hxS' (by rw [← hf x]; exact LinearMap.mem_ker.1 hxk)⟩`. Conclude with `le_inf hWW' fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSq _ ((hWmem z).1 hz).2)`.

Establish `hidx : U'.toAddSubgroup.relIndex W'.toAddSubgroup = (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (stepIdeal O F τ i).toAddSubgroup * U.toAddSubgroup.relIndex W.toAddSubgroup`. Rewrite using `[GlobalTheory.T.relIndex_map_mul_relIndex_ker f U' W' hU'W', hmapU', hU'ker, hW'ker]`. Both sides reduce to the same expression. Establish `hne'` using `hv'.relIndex_ne_zero hW'fg`. Establish `hne` using `hu.relIndex_ne_zero hWfg`.

Establish `hne1 : (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (stepIdeal O F τ i).toAddSubgroup ≠ 0`. Introduce `h0`. Apply `hne'` to reduce the goal to its premises. Rewrite using `[← hU'_def, hidx, h0, zero_mul]`. Establish `hpos : ∀ {n : ℕ} (v : Fin n → (Fin F.P₀.g → K)), LinearIndependent K v → ∀ σ, 0 < (h.gram σ v).det.re` using `fun v hv σ => (Complex.pos_iff.1 ((h.posDef σ _ v hv).det_pos)).1`.

Establish `hvec1 : (fun j : Fin (i + 1) => stepVec O F τ j) = e` using `funext hvec`. Establish `hvec0 : (fun j : Fin i => stepVec O F τ j) = fun j => e j.castSucc`. Use function extensionality and compare the values at `j`. Use `hvec j.castSucc` as an intermediate fact. Rewrite `this` using `[Fin.coe_castSucc]`. Then use the resulting hypothesis.

Establish `hG1 : ∀ σ : K →+* ℂ, (h.gram σ v').det.re = (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) * ‖σ a‖ ^ 2 * (h.gram σ e).det.re`. Introduce `σ`. Establish `hw` using `hrep w hwS'`. Establish `: v' = Fin.snoc (fun j => dK j.castSucc • e j.castSucc) (∑ k, w (p k) • e k)`. Rewrite using `[hv'_def, ← hw]`.

Rewrite using `[this, GlobalTheory.T.gram_det_snoc_triangular h σ e (fun j => dK j.castSucc) (fun k => w (p k))]`. Simplify using `only [← hq, hwq]`. Establish `hG0 : ∀ σ : K →+* ℂ, (h.gram σ u).det.re = (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) * (h.gram σ fun j => e j.castSucc).det.re` using `fun σ => GlobalTheory.T.gram_det_scale_vectors h σ (fun j => e j.castSucc) (fun j => dK j.castSucc)`. Establish `hP : ∀ σ : K →+* ℂ, 0 < ∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2` using `fun σ => Finset.prod_pos fun j _ => by`. Establish `: σ (dK j.castSucc) ≠ 0` using `(map_ne_zero σ).2 (hdK _)`.

Check the signs of the components of the expression. Establish `hA : ∀ σ : K →+* ℂ, 0 < ‖σ a‖` using `fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha0)`. Establish `he0 : LinearIndependent K fun j : Fin i => e j.castSucc` using `heli.comp Fin.castSucc (Fin.castSucc_injective _)`. Establish `hlog1 : ∀ σ : K →+* ℂ, Real.log (h.gram σ v').det.re = Real.log (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) + 2 * Real.log ‖σ a‖ + Real.log (h.gram σ e).det.re`. Introduce `σ`.

Rewrite using `[hG1, Real.log_mul (by have := hP σ; have := hA σ; positivity) (hpos e heli σ).ne', Real.log_mul (hP σ).ne' (by have := hA σ; positivity), Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlog0 : ∀ σ : K →+* ℂ, Real.log (h.gram σ u).det.re = Real.log (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) + Real.log (h.gram σ fun j => e j.castSucc).det.re`. Introduce `σ`.

Rewrite using `[hG0, Real.log_mul (hP σ).ne' (hpos _ he0 σ).ne']`. Establish `hlogr : ∀ σ : K →+* ℂ, Real.log ((h.gram σ e).det.re / (h.gram σ fun j => e j.castSucc).det.re) = Real.log (h.gram σ e).det.re - Real.log (h.gram σ fun j => e j.castSucc).det.re` using `fun σ => Real.log_div (hpos e heli σ).ne' (hpos _ he0 σ).ne'`. Rewrite using `[arakelovDegree_eq_degreeOfFamily h hW'fg hv', arakelovDegree_eq_degreeOfFamily h hWfg hu, stepGrDeg, dif_pos hex, ← ha_def]`. Unfold `degreeOfFamily stepGrSq`. Rewrite using `[← hU'_def, ← hU_def, hidx, Nat.cast_mul, Real.log_mul (by exact_mod_cast hne1) (by exact_mod_cast hne)]`.

Simplify using `only [hvec1, hvec0, hlog1, hlog0, hlogr, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_stepLat_succ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K)
    (h : HermFam K (Fin F.P₀.g → K)) (hg : F.P₀.g = (letters O.S.Dw).length) (hL : Full F.lieLat)
    (τ : D.host.E →+* ℂ) (i : ℕ) (hi : i < O.S.Dw.mult τ) :
    deg h (stepLat O F τ (i + 1)) = deg h (stepLat O F τ i) + stepGrDeg O F h τ i := by
  classical
  obtain ⟨p, hp, hvec, hcoef, hW', hW⟩ := GlobalTheory.T.lie_lattice_step_coordinate_vectors D O K F hg τ i hi
  set e : Fin (i + 1) → (Fin F.P₀.g → K) := fun j => Pi.single (p j) 1 with he
  set q := p (Fin.last i) with hq
  set L := F.lieLat with hLdef
  set S' := Submodule.span K (Set.range e) with hS'
  set S := Submodule.span K (Set.range fun j : Fin i => e j.castSucc) with hS
  set W' := stepLat O F τ (i + 1) with hW'def
  set W := stepLat O F τ i with hWdef
  set f := (stepCoef O F τ i).restrictScalars (𝓞 K) with hfdef
  have hf : ∀ v, f v = v q := fun v => hcoef v
  have he_app : ∀ j k, e j (p k) = if j = k then 1 else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; simp [e]
    · have : p k ≠ p j := fun h' => hjk (hp h').symm
      simp [e, Pi.single_apply, this, hjk]
  have hrep : ∀ v ∈ S', v = ∑ k, v (p k) • e k := by
    intro v hv
    let Φ : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K) := ∑ k, (LinearMap.proj (p k)).smulRight (e k)
    have hΦ : Set.EqOn Φ (LinearMap.id : (Fin F.P₀.g → K) →ₗ[K] _) (Set.range e) := by
      rintro _ ⟨j, rfl⟩
      simp [Φ, LinearMap.sum_apply, he_app]
    have := LinearMap.eqOn_span' hΦ hv
    simpa [Φ] using this.symm
  have hSq : ∀ v ∈ S, v q = 0 := by
    intro v hv
    have : S ≤ LinearMap.ker (LinearMap.proj q : (Fin F.P₀.g → K) →ₗ[K] K) := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := he_app j.castSucc (Fin.last i)
      simp only [Fin.castSucc_ne_last, if_false] at this
      simpa [q] using this
    exact this hv
  have hSS' : S ≤ S' := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.castSucc, rfl⟩)
  have hSS : ∀ v ∈ S', v q = 0 → v ∈ S := by
    intro v hv hv0
    rw [hrep v hv, Fin.sum_univ_castSucc, ← hq, hv0, zero_smul, add_zero]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hW'mem : ∀ x, x ∈ W' ↔ x ∈ L ∧ x ∈ S' := fun x => by rw [hW']; exact Iff.rfl
  have hWmem : ∀ x, x ∈ W ↔ x ∈ L ∧ x ∈ S := fun x => by rw [hW]; exact Iff.rfl
  have hWW' : W ≤ W' := fun x hx => (hW'mem x).2 ⟨((hWmem x).1 hx).1, hSS' ((hWmem x).1 hx).2⟩
  have hfg : ∀ N : Submodule (𝓞 K) (Fin F.P₀.g → K), N ≤ L → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian L hL.1
    have h1 : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hN] at this
  have hWfg : W.FG := hfg W fun x hx => ((hWmem x).1 hx).1
  have hW'fg : W'.FG := hfg W' fun x hx => ((hW'mem x).1 hx).1
  have hden : ∀ j, ∃ d : 𝓞 K, d ≠ 0 ∧ d • e j ∈ L := fun j => GlobalTheory.T.number_field_lattice_clears_denominator L hL.2 (e j)
  choose d hd0 hdL using hden
  set dK : Fin (i + 1) → K := fun j => algebraMap (𝓞 K) K (d j) with hdK_def
  have hdK : ∀ j, dK j ≠ 0 := fun j h0 => hd0 j (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa [dK] using h0))
  have hdKL : ∀ j, dK j • e j ∈ L := fun j => by simpa [dK, algebraMap_smul] using hdL j
  have hex : ∃ a ∈ stepIdeal O F τ i, a ≠ 0 := by
    refine ⟨f (dK (Fin.last i) • e (Fin.last i)), ?_, ?_⟩
    · show _ ∈ W'.map f
      refine Submodule.mem_map_of_mem ((hW'mem _).2 ⟨hdKL _, ?_⟩)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [hf]; simpa [e, q] using hdK (Fin.last i)
  set a := hex.choose with ha_def
  obtain ⟨haI, ha0⟩ := hex.choose_spec
  rw [← ha_def] at haI ha0
  obtain ⟨w, hwW', hwa⟩ := Submodule.mem_map.1 (show a ∈ W'.map f from haI)
  have hwq : w q = a := by rw [← hf w]; exact hwa
  set u : Fin i → (Fin F.P₀.g → K) := fun j => dK j.castSucc • e j.castSucc with hu_def
  have huS : ∀ j, u j ∈ S := fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have heli : LinearIndependent K e := by
    have := (Pi.basisFun K (Fin F.P₀.g)).linearIndependent.comp p hp
    convert this using 1
    ext j : 1; simp [e]
  have huli : LinearIndependent K u := by
    have := (heli.comp Fin.castSucc (Fin.castSucc_injective _)).units_smul
      (fun j => Units.mk0 (dK j.castSucc) (hdK _))
    convert this using 1
    ext j : 1; simp [u, Units.smul_def]
  have hSu : S ≤ Submodule.span K (Set.range u) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : e j.castSucc = (dK j.castSucc)⁻¹ • u j := by
      simp [u, smul_smul, inv_mul_cancel₀ (hdK _)]
    show e j.castSucc ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have huS' : Submodule.span K (Set.range u) ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact huS j
  have hu : IsFrame K W u := by
    refine ⟨fun j => (hWmem _).2 ⟨hdKL _, huS j⟩, huli, fun x hx => hSu ((hWmem x).1 hx).2⟩
  set v' : Fin (i + 1) → (Fin F.P₀.g → K) := Fin.snoc u w with hv'_def
  have hwS' : w ∈ S' := ((hW'mem w).1 hwW').2
  have hv' : IsFrame K W' v' := by
    refine ⟨fun k => ?_, ?_, fun x hx => ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa [v'] using hwW'
      | cast j => simpa [v'] using hWW' (hu.1 j)
    · refine linearIndependent_finSnoc.2 ⟨huli, fun hmem => ha0 ?_⟩
      rw [← hwq]; exact hSq _ (huS' hmem)
    · obtain ⟨hxL, hxS'⟩ := (hW'mem x).1 hx
      have hy : x - (x q / a) • w ∈ S := by
        refine hSS _ (Submodule.sub_mem _ hxS' (Submodule.smul_mem _ _ hwS')) ?_
        simp [hwq, div_mul_cancel₀ _ ha0]
      rw [SetLike.mem_coe, show v' = Fin.snoc u w from rfl, Fin.range_snoc, Submodule.mem_span_insert]
      exact ⟨x q / a, x - (x q / a) • w, hSu hy, by abel⟩

  set U := Submodule.span (𝓞 K) (Set.range u) with hU_def
  set U' := Submodule.span (𝓞 K) (Set.range v') with hU'_def
  have hUS : ∀ z ∈ U, z ∈ S := fun z hz =>
    (Submodule.span_le (p := S.restrictScalars (𝓞 K))).2 (by rintro _ ⟨j, rfl⟩; exact huS j) hz
  have hU'W' : U' ≤ W' := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hv'.1 k)
  have hmapU' : U'.map f = Submodule.span (𝓞 K) {a} := by
    rw [hU'_def, Submodule.map_span, hv'_def, Fin.range_snoc, Set.image_insert_eq, hwa]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | ⟨_, ⟨j, rfl⟩, rfl⟩)
      · exact Submodule.subset_span rfl
      · rw [SetLike.mem_coe, hf, hSq _ (huS j)]; exact zero_mem _
    · exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hU'ker : U' ⊓ LinearMap.ker f = U := by
    apply le_antisymm
    · rintro x ⟨hx, hxk⟩
      rw [hU'_def, hv'_def, Fin.range_snoc] at hx
      rw [SetLike.mem_coe, Submodule.mem_span_insert] at hx
      obtain ⟨b, z, hz, rfl⟩ := hx
      have hz0 : f z = 0 := by rw [hf]; exact hSq _ (hUS z hz)
      have hba : b • a = 0 := by
        have := LinearMap.mem_ker.1 hxk
        rwa [map_add, map_smul, hwa, hz0, add_zero] at this
      rw [(smul_eq_zero.1 hba).resolve_right ha0, zero_smul, zero_add]
      exact hz
    · refine le_inf ?_ fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSq _ (hUS z hz))
      rw [hU_def, hU'_def]
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp [v']⟩
  have hW'ker : W' ⊓ LinearMap.ker f = W := by
    apply le_antisymm
    · rintro x ⟨hx, hxk⟩
      obtain ⟨hxL, hxS'⟩ := (hW'mem x).1 hx
      exact (hWmem x).2 ⟨hxL, hSS _ hxS' (by rw [← hf x]; exact LinearMap.mem_ker.1 hxk)⟩
    · exact le_inf hWW' fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSq _ ((hWmem z).1 hz).2)
  have hidx : U'.toAddSubgroup.relIndex W'.toAddSubgroup =
      (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (stepIdeal O F τ i).toAddSubgroup *
        U.toAddSubgroup.relIndex W.toAddSubgroup := by
    rw [GlobalTheory.T.relIndex_map_mul_relIndex_ker f U' W' hU'W', hmapU', hU'ker, hW'ker]; rfl
  have hne' := hv'.relIndex_ne_zero hW'fg
  have hne := hu.relIndex_ne_zero hWfg
  have hne1 : (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (stepIdeal O F τ i).toAddSubgroup ≠ 0 := by
    intro h0; apply hne'; rw [← hU'_def, hidx, h0, zero_mul]

  have hpos : ∀ {n : ℕ} (v : Fin n → (Fin F.P₀.g → K)), LinearIndependent K v → ∀ σ,
      0 < (h.gram σ v).det.re := fun v hv σ => (Complex.pos_iff.1 ((h.posDef σ _ v hv).det_pos)).1
  have hvec1 : (fun j : Fin (i + 1) => stepVec O F τ j) = e := funext hvec
  have hvec0 : (fun j : Fin i => stepVec O F τ j) = fun j => e j.castSucc := by
    funext j; have := hvec j.castSucc; rwa [Fin.coe_castSucc] at this
  have hG1 : ∀ σ : K →+* ℂ, (h.gram σ v').det.re =
      (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) * ‖σ a‖ ^ 2 * (h.gram σ e).det.re := by
    intro σ
    have hw := hrep w hwS'
    have : v' = Fin.snoc (fun j => dK j.castSucc • e j.castSucc) (∑ k, w (p k) • e k) := by
      rw [hv'_def, ← hw]
    rw [this, GlobalTheory.T.gram_det_snoc_triangular h σ e (fun j => dK j.castSucc) (fun k => w (p k))]
    simp only [← hq, hwq]
  have hG0 : ∀ σ : K →+* ℂ, (h.gram σ u).det.re =
      (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) * (h.gram σ fun j => e j.castSucc).det.re := fun σ =>
    GlobalTheory.T.gram_det_scale_vectors h σ (fun j => e j.castSucc) (fun j => dK j.castSucc)
  have hP : ∀ σ : K →+* ℂ, 0 < ∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2 := fun σ =>
    Finset.prod_pos fun j _ => by
      have : σ (dK j.castSucc) ≠ 0 := (map_ne_zero σ).2 (hdK _)
      positivity
  have hA : ∀ σ : K →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha0)
  have he0 : LinearIndependent K fun j : Fin i => e j.castSucc :=
    heli.comp Fin.castSucc (Fin.castSucc_injective _)
  have hlog1 : ∀ σ : K →+* ℂ, Real.log (h.gram σ v').det.re = Real.log (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) +
      2 * Real.log ‖σ a‖ + Real.log (h.gram σ e).det.re := by
    intro σ
    rw [hG1, Real.log_mul (by have := hP σ; have := hA σ; positivity) (hpos e heli σ).ne',
      Real.log_mul (hP σ).ne' (by have := hA σ; positivity), Real.log_pow]
    push_cast; ring
  have hlog0 : ∀ σ : K →+* ℂ, Real.log (h.gram σ u).det.re = Real.log (∏ j : Fin i, ‖σ (dK j.castSucc)‖ ^ 2) +
      Real.log (h.gram σ fun j => e j.castSucc).det.re := by
    intro σ
    rw [hG0, Real.log_mul (hP σ).ne' (hpos _ he0 σ).ne']
  have hlogr : ∀ σ : K →+* ℂ, Real.log ((h.gram σ e).det.re / (h.gram σ fun j => e j.castSucc).det.re) =
      Real.log (h.gram σ e).det.re - Real.log (h.gram σ fun j => e j.castSucc).det.re := fun σ =>
    Real.log_div (hpos e heli σ).ne' (hpos _ he0 σ).ne'
  rw [arakelovDegree_eq_degreeOfFamily h hW'fg hv', arakelovDegree_eq_degreeOfFamily h hWfg hu, stepGrDeg, dif_pos hex, ← ha_def]
  unfold degreeOfFamily stepGrSq
  rw [← hU'_def, ← hU_def, hidx, Nat.cast_mul, Real.log_mul (by exact_mod_cast hne1) (by exact_mod_cast hne)]
  simp only [hvec1, hvec0, hlog1, hlog0, hlogr, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end GlobalTheory.LieRead

end
