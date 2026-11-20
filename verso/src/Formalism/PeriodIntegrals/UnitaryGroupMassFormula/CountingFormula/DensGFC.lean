import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]`.
-/
theorem h_add_right (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

/- English proof (translation)
Rewrite using `[H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]`.
-/
theorem h_smul_right (H : Loc.HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f s`.
-/
theorem h_sum_left (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f s

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => h_add_right H x y y')) f s`.
-/
theorem h_sum_right (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) :=
  map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => h_add_right H x y y')) f s

/- English proof (translation)
Rewrite using `[h_sum_left]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[H.h_smul_left, h_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[h_smul_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_expand (H : Loc.HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    H.h (∑ k, c k • b k) (∑ l, d l • b l) = ∑ k, ∑ l, c k * M.L.cj (d l) * H.h (b k) (b l) := by
  rw [h_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h_smul_right]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_O (o : M.L.O) (v : V) : o • v = (o : E) • v := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Unfold `Loc.HermSp.smulLat at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨w, hw, rfl⟩` from `hx`. Conclude with `⟨w, hw, rfl⟩`. Consider the case `zero => exact ⟨0, Λ.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w, hw, rfl⟩` from `hx`.

Take `⟨w', hw', rfl⟩` from `hy`. Conclude with `⟨w + w', Λ.add_mem hw hw', by simp [smul_add]⟩`. Consider the case `smul o x _ hx`. Take `⟨w, hw, rfl⟩` from `hx`. Use `⟨o • w, Λ.smul_mem o hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_O, smul_O, smul_smul, smul_smul, mul_comm]`. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `Submodule.subset_span ⟨w, hw, rfl⟩`.
-/
theorem smulLat_mem (H : Loc.HermSp M V) (c : E) (Λ : Submodule M.L.O V) (y : V) :
    y ∈ H.smulLat c Λ ↔ ∃ w ∈ Λ, y = c • w := by
  constructor
  · intro hy
    unfold Loc.HermSp.smulLat at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, hw, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', Λ.add_mem hw hw', by simp [smul_add]⟩
    | smul o x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨o • w, Λ.smul_mem o hw, ?_⟩
      rw [smul_O, smul_O, smul_smul, smul_smul, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨w, hw, rfl⟩

/- English proof (translation)
Use `Fintype.linearIndependent_iff.1 hb (c - c') (by` as an intermediate fact. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])`. Use function extensionality and compare the values at `k`. Conclude with `sub_eq_zero.1 (this k)`.
-/
theorem coord_unique {n : ℕ} {b : Fin n → V} (hb : LinearIndependent E b) {c c' : Fin n → E}
    (h : ∑ k, c k • b k = ∑ k, c' k • b k) : c = c' := by
  have := Fintype.linearIndependent_iff.1 hb (c - c') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext k
  exact sub_eq_zero.1 (this k)

/- English proof (translation)
Use `Λ.sum_mem fun k _ => ?_` and prove the remaining obligations. Use `Λ.smul_mem (⟨c k, hc k⟩ : M.L.O) (hbΛ k)` as an intermediate fact. Conclude with `this`.
-/
theorem comb_mem {n : ℕ} {b : Fin n → V} {Λ : Submodule M.L.O V} (hbΛ : ∀ k, b k ∈ Λ)
    (c : Fin n → E) (hc : ∀ k, c k ∈ M.L.O) : ∑ k, c k • b k ∈ Λ := by
  refine Λ.sum_mem fun k _ => ?_
  have := Λ.smul_mem (⟨c k, hc k⟩ : M.L.O) (hbΛ k)
  exact this

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

structure RedData (ϖ : 𝒪[F]) (k : Type) [Field k] (r : M.L.O →+* k) (n : ℕ) (b : Fin n → V)
    (Λ : Submodule M.L.O V) : Prop where
  ker : ∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z
  surj : Function.Surjective r
  bΛ : ∀ j, b j ∈ Λ
  bind : LinearIndependent E b
  crd : ∀ x ∈ Λ, ∃ c : Fin n → E, (∀ j, c j ∈ M.L.O) ∧ x = ∑ j, c j • b j

variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

def cO (hR : RedData ϖ k r n b Λ) (x : V) : Fin n → E :=
  if hx : x ∈ Λ then Classical.choose (hR.crd x hx) else 0

/- English proof (translation)
Unfold `cO`. Use `split_ifs with hx`. Conclude with `(Classical.choose_spec (hR.crd x hx)).1 j`. Conclude with `M.L.O.zero_mem`.
-/
theorem cO_mem (hR : RedData ϖ k r n b Λ) (x : V) (j : Fin n) : cO hR x j ∈ M.L.O := by
  unfold cO
  split_ifs with hx
  · exact (Classical.choose_spec (hR.crd x hx)).1 j
  · exact M.L.O.zero_mem

/- English proof (translation)
Unfold `cO`. Rewrite using `[dif_pos hx]`. Conclude with `(Classical.choose_spec (hR.crd x hx)).2`.
-/
theorem cO_sum (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) : x = ∑ j, cO hR x j • b j := by
  unfold cO
  rw [dif_pos hx]
  exact (Classical.choose_spec (hR.crd x hx)).2

/- English proof (translation)
The claim follows from `coord_unique hR.bind ((cO_sum hR hx).symm.trans hc)`.
-/
theorem cO_eq (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) (c : Fin n → E)
    (hc : x = ∑ j, c j • b j) : cO hR x = c :=
  coord_unique hR.bind ((cO_sum hR hx).symm.trans hc)

def red (hR : RedData ϖ k r n b Λ) (x : V) : Fin n → k := fun j => r ⟨cO hR x j, cO_mem hR x j⟩

/- English proof (translation)
Establish `hmem : ∑ a, h a • v a ∈ Λ`. Use `Λ.sum_mem fun a _ => ?_` and prove the remaining obligations. Conclude with `Λ.smul_mem (⟨h a, hh a⟩ : M.L.O) (hv a)`. Use `cO_eq hR hmem _ ?_` and prove the remaining obligations. Use `conv_lhs => rw [Finset.sum_congr rfl fun a _ => by rw [cO_sum hR (hv a)]]`.

Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem cO_lincomb (hR : RedData ϖ k r n b Λ) {ι : Type} [Fintype ι] (h : ι → E) (v : ι → V)
    (hv : ∀ a, v a ∈ Λ) (hh : ∀ a, h a ∈ M.L.O) :
    cO hR (∑ a, h a • v a) = fun j => ∑ a, h a * cO hR (v a) j := by
  have hmem : ∑ a, h a • v a ∈ Λ := by
    refine Λ.sum_mem fun a _ => ?_
    exact Λ.smul_mem (⟨h a, hh a⟩ : M.L.O) (hv a)
  refine cO_eq hR hmem _ ?_
  conv_lhs => rw [Finset.sum_congr rfl fun a _ => by rw [cO_sum hR (hv a)]]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun (cO_lincomb hR (fun a => (h a : E)) v hv (fun a => (h a).2)) j`. Establish `h2 : (⟨cO hR (∑ a, (h a : E) • v a) j, cO_mem hR _ j⟩ : M.L.O) = ∑ a, h a * ⟨cO hR (v a) j, cO_mem hR _ j⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show cO hR (∑ a, (h a : E) • v a) j = _`.

Rewrite using `[h1]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [red, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[h2, map_sum]`.

Simplify using `only [map_mul]`.
-/
theorem red_lincomb (hR : RedData ϖ k r n b Λ) {ι : Type} [Fintype ι] (h : ι → M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ Λ) :
    red hR (∑ a, (h a : E) • v a) = ∑ a, r (h a) • red hR (v a) := by
  funext j
  have h1 := congrFun (cO_lincomb hR (fun a => (h a : E)) v hv (fun a => (h a).2)) j
  have h2 : (⟨cO hR (∑ a, (h a : E) • v a) j, cO_mem hR _ j⟩ : M.L.O) =
      ∑ a, h a * ⟨cO hR (v a) j, cO_mem hR _ j⟩ := by
    apply Subtype.ext
    show cO hR (∑ a, (h a : E) • v a) j = _
    rw [h1]
    push_cast
    rfl
  simp only [red, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h2, map_sum]
  simp only [map_mul]

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

/- English proof (translation)
Establish `hc : cO hR (x - y) = cO hR x - cO hR y`. Use `cO_eq hR (Λ.sub_mem hx hy) _ ?_` and prove the remaining obligations. Use `conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Use function extensionality and compare the values at `j`.

Simplify using `only [red, Pi.sub_apply]`. Rewrite using `[← map_sub]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show cO hR (x - y) j = _`.

Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem red_sub (hR : RedData ϖ k r n b Λ) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    red hR (x - y) = red hR x - red hR y := by
  have hc : cO hR (x - y) = cO hR x - cO hR y := by
    refine cO_eq hR (Λ.sub_mem hx hy) _ ?_
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  funext j
  simp only [red, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  show cO hR (x - y) j = _
  rw [hc]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `hz : ∀ j, ∃ z ∈ M.L.O, cO hR x j = algebraMap F E (ϖ : F) * z` using `fun j => (hR.ker ⟨cO hR x j, cO_mem hR x j⟩).1 (congrFun h0 j)`. Use `choose z hzO hz using hz`. Use `⟨∑ j, z j • b j, comb_mem hR.bΛ z hzO, ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [cO_sum hR hx]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hz j, smul_smul]`. Introduce and unpack `⟨w, hw, rfl⟩`.

Establish `hc : cO hR (algebraMap F E (ϖ : F) • w) = fun j => algebraMap F E (ϖ : F) * cO hR w j`. Use `cO_eq hR hx _ ?_` and prove the remaining obligations. Use `conv_lhs => rw [cO_sum hR hw]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Use function extensionality and compare the values at `j`. Use `(hR.ker _).2 ⟨cO hR w j, cO_mem hR w j, ?_⟩` and prove the remaining obligations. Use `show cO hR (algebraMap F E (ϖ : F) • w) j = _`. Rewrite using `[hc]`.
-/
theorem red_zero_iff (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) :
    red hR x = 0 ↔ ∃ w ∈ Λ, x = algebraMap F E (ϖ : F) • w := by
  constructor
  · intro h0
    have hz : ∀ j, ∃ z ∈ M.L.O, cO hR x j = algebraMap F E (ϖ : F) * z := fun j =>
      (hR.ker ⟨cO hR x j, cO_mem hR x j⟩).1 (congrFun h0 j)
    choose z hzO hz using hz
    refine ⟨∑ j, z j • b j, comb_mem hR.bΛ z hzO, ?_⟩
    conv_lhs => rw [cO_sum hR hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, smul_smul]
  · rintro ⟨w, hw, rfl⟩
    have hc : cO hR (algebraMap F E (ϖ : F) • w) = fun j => algebraMap F E (ϖ : F) * cO hR w j := by
      refine cO_eq hR hx _ ?_
      conv_lhs => rw [cO_sum hR hw]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
    funext j
    refine (hR.ker _).2 ⟨cO hR w j, cO_mem hR w j, ?_⟩
    show cO hR (algebraMap F E (ϖ : F) • w) j = _
    rw [hc]

/- English proof (translation)
Rewrite using `[smulLat_mem, ← red_zero_iff hR (Λ.sub_mem hx hy), red_sub hR hx hy, sub_eq_zero]`.
-/
theorem class_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    x - y ∈ H.smulLat (algebraMap F E (ϖ : F)) Λ ↔ red hR x = red hR y := by
  rw [smulLat_mem, ← red_zero_iff hR (Λ.sub_mem hx hy), red_sub hR hx hy, sub_eq_zero]

/- English proof (translation)
Use `choose o ho using fun j => hR.surj (X j)`. Use `⟨∑ j, (o j : E) • b j, comb_mem hR.bΛ _ fun j => (o j).2, ?_⟩` and prove the remaining obligations. Establish `hc` using `cO_eq hR (comb_mem hR.bΛ _ fun j => (o j).2) (fun j => (o j : E)) rfl`. Use function extensionality and compare the values at `j`. Simplify using `only [red]`.

Rewrite using `[← ho j]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show cO hR _ j = _`. Rewrite using `[hc]`.
-/
theorem red_lift (hR : RedData ϖ k r n b Λ) (X : Fin n → k) : ∃ x ∈ Λ, red hR x = X := by
  choose o ho using fun j => hR.surj (X j)
  refine ⟨∑ j, (o j : E) • b j, comb_mem hR.bΛ _ fun j => (o j).2, ?_⟩
  have hc := cO_eq hR (comb_mem hR.bΛ _ fun j => (o j).2) (fun j => (o j : E)) rfl
  funext j
  simp only [red]
  rw [← ho j]
  congr 1
  apply Subtype.ext
  show cO hR _ j = _
  rw [hc]

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

/- English proof (translation)
The claim follows from `(M.L.O_def _).2 (by rw [show algebraMap F E (c : F) = algebraMap 𝒪[F] E c from (IsScalarTower.algebraMap_apply 𝒪[F] F E c).symm] exact isIntegral_algebraMap)`.
-/
theorem algO (c : 𝒪[F]) : algebraMap F E (c : F) ∈ M.L.O :=
  (M.L.O_def _).2 (by
    rw [show algebraMap F E (c : F) = algebraMap 𝒪[F] E c from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E c).symm]
    exact isIntegral_algebraMap)

/- English proof (translation)
Establish `h0 : (ϖ : F) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Conclude with `(IsUnit.mk0 _ h0).map _`.
-/
theorem pi_unit (hϖ : Irreducible ϖ) : IsUnit (algebraMap F E (ϖ : F)) := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact (IsUnit.mk0 _ h0).map _

/- English proof (translation)
The claim follows from `M.L.O.pow_mem (algO ϖ) j`.
-/
theorem pi_pow_mem (j : ℕ) : algebraMap F E (ϖ : F) ^ j ∈ M.L.O := M.L.O.pow_mem (algO ϖ) j

/- English proof (translation)
Take `⟨c, hc, hcx⟩` from `o2 x`. Distinguish the cases in `h0 : algebraMap F E (c : F) = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `hc' : (c : F) ≠ 0` using `fun h => hc (Subtype.ext h)`. Establish `h1 : (1 : E) = 0`.

Rewrite using `[← map_one (algebraMap F E), ← inv_mul_cancel₀ hc', map_mul, h0, mul_zero]`. Establish `hx : x = 0` using `by rw [← one_mul x, h1, zero_mul]`. Rewrite using `[hx, mul_zero]`. Conclude with `M.L.O.zero_mem`. Take `⟨j, u, _, ⟨w, hw, huw⟩, hcu⟩` from `o3 _ (algO c) h0`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `: algebraMap F E (ϖ : F) ^ j * x = w * (algebraMap F E (c : F) * x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[huw, one_mul]`. Use `_ = w * (algebraMap F E (ϖ : F) ^ j * u * x) := by ring`.

Use `_ = w * (algebraMap F E (c : F) * x) := by rw [← hcu]`. Rewrite using `[this]`. Conclude with `M.L.O.mul_mem hw hcx`.
-/
theorem clear_den (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u) (x : E) :
    ∃ j : ℕ, algebraMap F E (ϖ : F) ^ j * x ∈ M.L.O := by
  obtain ⟨c, hc, hcx⟩ := o2 x
  by_cases h0 : algebraMap F E (c : F) = 0
  · refine ⟨0, ?_⟩
    have hc' : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have h1 : (1 : E) = 0 := by
      rw [← map_one (algebraMap F E), ← inv_mul_cancel₀ hc', map_mul, h0, mul_zero]
    have hx : x = 0 := by rw [← one_mul x, h1, zero_mul]
    rw [hx, mul_zero]
    exact M.L.O.zero_mem
  · obtain ⟨j, u, _, ⟨w, hw, huw⟩, hcu⟩ := o3 _ (algO c) h0
    refine ⟨j, ?_⟩
    have : algebraMap F E (ϖ : F) ^ j * x = w * (algebraMap F E (c : F) * x) := by
      calc algebraMap F E (ϖ : F) ^ j * x = (u * w) * (algebraMap F E (ϖ : F) ^ j * x) := by
            rw [huw, one_mul]
        _ = w * (algebraMap F E (ϖ : F) ^ j * u * x) := by ring
        _ = w * (algebraMap F E (c : F) * x) := by rw [← hcu]
    rw [this]
    exact M.L.O.mul_mem hw hcx

/- English proof (translation)
Use `choose j hj using fun a => clear_den o2 o3 (g a)`. Use `⟨∑ a, j a, fun a => ?_⟩` and prove the remaining obligations. Establish `hle : j a ≤ ∑ a, j a` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc]`. Conclude with `M.L.O.mul_mem (pi_pow_mem _) (hj a)`.
-/
theorem clear_den_fam (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u) {ι : Type} [Fintype ι] (g : ι → E) :
    ∃ N : ℕ, ∀ a, algebraMap F E (ϖ : F) ^ N * g a ∈ M.L.O := by
  choose j hj using fun a => clear_den o2 o3 (g a)
  refine ⟨∑ a, j a, fun a => ?_⟩
  have hle : j a ≤ ∑ a, j a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact M.L.O.mul_mem (pi_pow_mem _) (hj a)

/- English proof (translation)
Establish `hc : cO hR (0 : V) = 0` using `cO_eq hR Λ.zero_mem 0 (by simp)`. Use function extensionality and compare the values at `j`. Simplify using `only [red, Pi.zero_apply]`. Rewrite using `[← map_zero r]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show cO hR 0 j = 0`. Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem red_zero (hR : RedData ϖ k r n b Λ) : red hR 0 = 0 := by
  have hc : cO hR (0 : V) = 0 := cO_eq hR Λ.zero_mem 0 (by simp)
  funext j
  simp only [red, Pi.zero_apply]
  rw [← map_zero r]
  congr 1
  apply Subtype.ext
  show cO hR 0 j = 0
  rw [hc]
  rfl

/- English proof (translation)
Establish `hex : ∃ j : ℕ, ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j + 1) * z`. Take `⟨j, u, huO, ⟨w, hw, huw⟩, hju⟩` from `o3 _ (hh a0) ha0`. Use `⟨j, a0, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hzO, hz⟩`. Establish `hcan : u = algebraMap F E (ϖ : F) * z`.

Establish `h2 : algebraMap F E (ϖ : F) ^ j * u = algebraMap F E (ϖ : F) ^ j * (algebraMap F E (ϖ : F) * z)`. Rewrite using `[← hju, hz]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `((pi_unit hϖ).pow j).mul_left_cancel h2`. Establish `hr0 : r ⟨u, huO⟩ = 0` using `(hR.ker _).2 ⟨z, hzO, hcan⟩`.

Establish `hr1 : r ⟨u, huO⟩ * r ⟨w, hw⟩ = 1`. Rewrite using `[← map_mul, ← map_one r]`. Use `congr 1`. Conclude with `Subtype.ext huw`. Rewrite `hr1` using `[hr0, zero_mul]`.

Conclude with `zero_ne_one hr1`. Take `⟨j0, hj0, hmin⟩ : ∃ j0 : ℕ, (∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j0 + 1) * z) ∧ ∀ m < j0, ¬ ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (m + 1) * z` from `⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩`. Establish `hall : ∀ a, ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ j0 * z`. Introduce `a`. Break down `Nat.eq_zero_or_pos j0 with h0 | hpos` into its components or cases.

Conclude with `⟨h a, hh a, by rw [h0, pow_zero, one_mul]⟩`. Establish `hm` using `hmin (j0 - 1) (Nat.sub_lt hpos one_pos) push Not at hm`. Take `⟨z, hz, hza⟩` from `hm a`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Rewrite `hza` using `[show j0 - 1 + 1 = j0 from by omega]`. Then use the resulting hypothesis.

Use `choose z hzO hz using hall`. Take `⟨a1, ha1⟩` from `hj0`. Use `⟨j0, z, hzO, hz, a1, ?_⟩` and prove the remaining obligations. Introduce `hr`. Take `⟨z', hz'O, hz'⟩` from `(hR.ker _).1 hr`.

Establish `hz'' : z a1 = algebraMap F E (ϖ : F) * z'` using `hz'`. Apply `ha1` to reduce the goal to its premises. Conclude with `⟨z', hz'O, by rw [hz a1, hz'', pow_succ]; ring⟩`.
-/
theorem minpow (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u) {ι : Type} (h : ι → E) (hh : ∀ a, h a ∈ M.L.O)
    (a0 : ι) (ha0 : h a0 ≠ 0) :
    ∃ j : ℕ, ∃ z : ι → E, ∃ hz : ∀ a, z a ∈ M.L.O, (∀ a, h a = algebraMap F E (ϖ : F) ^ j * z a) ∧
      ∃ a1, r ⟨z a1, hz a1⟩ ≠ 0 := by
  have hex : ∃ j : ℕ, ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j + 1) * z := by
    obtain ⟨j, u, huO, ⟨w, hw, huw⟩, hju⟩ := o3 _ (hh a0) ha0
    refine ⟨j, a0, ?_⟩
    rintro ⟨z, hzO, hz⟩
    have hcan : u = algebraMap F E (ϖ : F) * z := by
      have h2 : algebraMap F E (ϖ : F) ^ j * u = algebraMap F E (ϖ : F) ^ j * (algebraMap F E (ϖ : F) * z) := by
        rw [← hju, hz]; ring
      exact ((pi_unit hϖ).pow j).mul_left_cancel h2
    have hr0 : r ⟨u, huO⟩ = 0 := (hR.ker _).2 ⟨z, hzO, hcan⟩
    have hr1 : r ⟨u, huO⟩ * r ⟨w, hw⟩ = 1 := by
      rw [← map_mul, ← map_one r]
      congr 1
      exact Subtype.ext huw
    rw [hr0, zero_mul] at hr1
    exact zero_ne_one hr1
  obtain ⟨j0, hj0, hmin⟩ : ∃ j0 : ℕ, (∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j0 + 1) * z) ∧
      ∀ m < j0, ¬ ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (m + 1) * z :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hall : ∀ a, ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ j0 * z := by
    intro a
    rcases Nat.eq_zero_or_pos j0 with h0 | hpos
    · exact ⟨h a, hh a, by rw [h0, pow_zero, one_mul]⟩
    · have hm := hmin (j0 - 1) (Nat.sub_lt hpos one_pos)
      push Not at hm
      obtain ⟨z, hz, hza⟩ := hm a
      refine ⟨z, hz, ?_⟩
      rwa [show j0 - 1 + 1 = j0 from by omega] at hza
  choose z hzO hz using hall
  obtain ⟨a1, ha1⟩ := hj0
  refine ⟨j0, z, hzO, hz, a1, ?_⟩
  intro hr
  obtain ⟨z', hz'O, hz'⟩ := (hR.ker _).1 hr
  have hz'' : z a1 = algebraMap F E (ϖ : F) * z' := hz'
  apply ha1
  exact ⟨z', hz'O, by rw [hz a1, hz'', pow_succ]; ring⟩

end FC

end PI.UnitaryGroupMassFormula.CntFormula
