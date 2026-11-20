import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckHomCat

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => norm_nonneg _`.
-/
theorem sn_nonneg (X : Obj k r) (W : List (Mx k r)) (x : M X) : 0 ≤ sn X W x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
Unfold `sn`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Simplify using `only [dsigW_eq', Pi.add_apply, Submodule.coe_add]`. Rewrite using `[dsW_add X.2.repOn (x c).2 (y c).2 (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]`.

Conclude with `norm_add_le _ _`.
-/
theorem sn_add_le (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (x y : M X) :
    sn X W (x + y) ≤ sn X W x + sn X W y := by
  unfold sn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [dsigW_eq', Pi.add_apply, Submodule.coe_add]
  rw [dsW_add X.2.repOn (x c).2 (y c).2 (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_add_le _ _

/- English proof (translation)
Unfold `sn`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [dsigW_eq', Pi.smul_apply, Submodule.coe_smul]`. Rewrite using `[dsW_smul X.2.repOn (x c).2 a (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]`.

Conclude with `norm_smul _ _`.
-/
theorem sn_smul (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (a : ℂ) (x : M X) :
    sn X W (a • x) = ‖a‖ * sn X W x := by
  unfold sn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [dsigW_eq', Pi.smul_apply, Submodule.coe_smul]
  rw [dsW_smul X.2.repOn (x c).2 a (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_smul _ _

/- English proof (translation)
The claim follows from `List.sum_nonneg fun t ht => by obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht exact sn_nonneg X W x`.
-/
theorem sum_nonneg' (X : Obj k r) (Ws : List (List (Mx k r))) (x : M X) :
    0 ≤ (Ws.map fun W' => sn X W' x).sum :=
  List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
    exact sn_nonneg X W x

def Dom (X : Obj k r) (φ : M X → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W' ∈ Ws, LieWd k r W') ∧
    ∀ x, φ x ≤ C * (Ws.map fun W' => sn X W' x).sum

/- English proof (translation)
Take `⟨C, Ws, hW, hb⟩` from `h`. Conclude with `⟨C, Ws, hW, fun x => (hle x).trans (hb x)⟩`.
-/
theorem Dom.mono {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X ψ) (hle : ∀ x, φ x ≤ ψ x) : Dom X φ := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  exact ⟨C, Ws, hW, fun x => (hle x).trans (hb x)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, [], by simp, fun _ => by simp⟩`.
-/
theorem Dom.zero (X : Obj k r) : Dom X fun _ => 0 :=
  ⟨0, [], by simp, fun _ => by simp⟩

/- English proof (translation)
Take `⟨C, Ws, hW, hb⟩` from `h`. Take `⟨C', Ws', hW', hb'⟩` from `h'`. Use `⟨|C| + |C'|, Ws ++ Ws', fun W hm => (List.mem_append.1 hm).elim (hW W) (hW' W), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_append, List.sum_append]`. Establish `h1` using `sum_nonneg' X Ws x`.

Establish `h2` using `sum_nonneg' X Ws' x`. Establish `h3` using `hb x`. Establish `h4` using `hb' x`. Establish `h5` using `mul_le_mul_of_nonneg_right (le_abs_self C) h1`. Establish `h6` using `mul_le_mul_of_nonneg_right (le_abs_self C') h2`.

Establish `h7` using `mul_nonneg (abs_nonneg C) h2`. Establish `h8` using `mul_nonneg (abs_nonneg C') h1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Dom.add {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X φ) (h' : Dom X ψ) :
    Dom X fun x => φ x + ψ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hm => (List.mem_append.1 hm).elim (hW W) (hW' W), fun x => ?_⟩
  rw [List.map_append, List.sum_append]
  have h1 := sum_nonneg' X Ws x
  have h2 := sum_nonneg' X Ws' x
  have h3 := hb x
  have h4 := hb' x
  have h5 := mul_le_mul_of_nonneg_right (le_abs_self C) h1
  have h6 := mul_le_mul_of_nonneg_right (le_abs_self C') h2
  have h7 := mul_nonneg (abs_nonneg C) h2
  have h8 := mul_nonneg (abs_nonneg C') h1
  nlinarith

/- English proof (translation)
Take `⟨C, Ws, hW, hb⟩` from `h`. Use `⟨a * C, Ws, hW, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hb x) ha`.
-/
theorem Dom.mul {X : Obj k r} {φ : M X → ℝ} (h : Dom X φ) {a : ℝ} (ha : 0 ≤ a) :
    Dom X fun x => a * φ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨a * C, Ws, hW, fun x => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) ha

/- English proof (translation)
The claim follows from `| [], _ => by simpa using Dom.zero X | i :: l, h => by simpa using (h i List.mem_cons_self).add (Dom.listSum φ l fun j hj => h j (List.mem_cons_of_mem _ hj))`.
-/
theorem Dom.listSum {X : Obj k r} {ι : Type} (φ : ι → M X → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, Dom X (φ i)) → Dom X fun x => (l.map fun i => φ i x).sum
  | [], _ => by simpa using Dom.zero X
  | i :: l, h => by
    simpa using (h i List.mem_cons_self).add
      (Dom.listSum φ l fun j hj => h j (List.mem_cons_of_mem _ hj))

/- English proof (translation)
Introduce `k r`. Use `⟨fun X Y => ⟨fun W hW => ?_, fun g _ => ?_⟩, fun X Y f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩, fun X Y c f hf => ⟨fun W hW => ?_, fun g hg => ?_⟩, fun X => ⟨fun W hW => ?_, fun g _ => ?_⟩, fun X Y Z f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Use `(Dom.zero X).mono fun x => ?_` and prove the remaining obligations. Use `sn_smul Y hW 0 0` as an intermediate fact. Rewrite `this` using `[zero_smul, norm_zero, zero_mul]`.

Conclude with `this.le`. Rewrite using `[LinearMap.zero_comp, LinearMap.comp_zero]`. Conclude with `(Dom.add (hf.cont W hW) (hf'.cont W hW)).mono fun x => sn_add_le Y hW _ _`. Rewrite using `[LinearMap.add_comp, LinearMap.comp_add, hf.equiv g hg, hf'.equiv g hg]`. Conclude with `(Dom.mul (hf.cont W hW) (norm_nonneg c)).mono fun x => (sn_smul Y hW _ _).le`.

Rewrite using `[LinearMap.smul_comp, LinearMap.comp_smul, hf.equiv g hg]`. Conclude with `⟨1, [W], by simpa using hW, fun x => by simp⟩`. Rewrite using `[LinearMap.id_comp, LinearMap.comp_id]`. Take `⟨C, Ws, hWs, hb⟩` from `hf'.cont W hW`. Use `((Dom.listSum (X := X) (fun W' x => sn Y W' (f x)) Ws fun W' h' => hf.cont W' (hWs W' h')).mul (abs_nonneg C)).mono fun x => ?_` and prove the remaining obligations.

Conclude with `(hb (f x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sum_nonneg' Y Ws _))`. Rewrite using `[LinearMap.comp_assoc, hf.equiv g hg, ← LinearMap.comp_assoc, hf'.equiv g hg, LinearMap.comp_assoc]`.
-/
theorem homCat : HomCat := by
  intro k r
  refine ⟨fun X Y => ⟨fun W hW => ?_, fun g _ => ?_⟩, fun X Y f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩,
    fun X Y c f hf => ⟨fun W hW => ?_, fun g hg => ?_⟩, fun X => ⟨fun W hW => ?_, fun g _ => ?_⟩,
    fun X Y Z f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩⟩
  · refine (Dom.zero X).mono fun x => ?_
    have := sn_smul Y hW 0 0
    rw [zero_smul, norm_zero, zero_mul] at this
    exact this.le
  · rw [LinearMap.zero_comp, LinearMap.comp_zero]
  · exact (Dom.add (hf.cont W hW) (hf'.cont W hW)).mono fun x => sn_add_le Y hW _ _
  · rw [LinearMap.add_comp, LinearMap.comp_add, hf.equiv g hg, hf'.equiv g hg]
  · exact (Dom.mul (hf.cont W hW) (norm_nonneg c)).mono fun x => (sn_smul Y hW _ _).le
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf.equiv g hg]
  · exact ⟨1, [W], by simpa using hW, fun x => by simp⟩
  · rw [LinearMap.id_comp, LinearMap.comp_id]
  · obtain ⟨C, Ws, hWs, hb⟩ := hf'.cont W hW
    refine ((Dom.listSum (X := X) (fun W' x => sn Y W' (f x)) Ws
      fun W' h' => hf.cont W' (hWs W' h')).mul (abs_nonneg C)).mono fun x => ?_
    exact (hb (f x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sum_nonneg' Y Ws _))
  · rw [LinearMap.comp_assoc, hf.equiv g hg, ← LinearMap.comp_assoc, hf'.equiv g hg, LinearMap.comp_assoc]

end GlobalTheory.CompanionTheory.ZuckHomCat

end
