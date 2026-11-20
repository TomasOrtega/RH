import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitOnto

variable {D : D7}

/- English proof (translation)
Take `⟨ε, -, -, -, hA, hO⟩` from `(GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1`. Rewrite using `[← (hA a).1 h1]`. Conclude with `(hO a).1 h2`.
-/
theorem eq_zero_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

/- English proof (translation)
Rewrite `hb` using `[grpOff, PlacesAdeles.mem_congGrp]`. Establish `key : (mt S b - 1) *ᵥ y = 0`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Apply `eq_zero_at_off P` to reduce the goal to its premises. Conclude with `Ideal.mul_mem_left _ _ (hy j)`. Conclude with `Ideal.mul_mem_right _ _ (by simpa using hb i j)`. Rewrite `key` using `[Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec]`. Conclude with `key`.
-/
theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

/- English proof (translation)
Introduce `y hy`. Rewrite using `[mulVec_off hb hy]`.
-/
theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

/- English proof (translation)
Introduce `y _`. Rewrite using `[PlacesAdeles.mt_one, Matrix.one_mulVec]`.
-/
theorem moves_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} : Moves S 1 L L P := by
  intro y _
  rw [PlacesAdeles.mt_one, Matrix.one_mulVec]

/- English proof (translation)
The claim follows from `| [], _ => by rw [List.prod_nil]; exact moves_one | a :: l, h => by rw [List.prod_cons] exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))`.
-/
theorem moves_list_prod {S : HSp D} {L : Lat S} {P : Pl D → Prop} :
    ∀ l : List (GA D S), (∀ a ∈ l, Moves S a L L P) → Moves S l.prod L L P
  | [], _ => by rw [List.prod_nil]; exact moves_one
  | a :: l, h => by
    rw [List.prod_cons]
    exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))

/- English proof (translation)
The claim follows from `| 0, _, i, _ => i.elim0 | r + 1, f, i, h => by rw [List.ofFn_succ, List.prod_cons] by_cases hi : i = 0 · subst hi rw [List.prod_eq_one, mul_one] intro x hx obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx exact h _ (Fin.succ_ne_zero j) · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi rw …`.
-/
theorem prod_ofFn_single {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (i : Fin r), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | r + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi : i = 0
    · subst hi
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero j)
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_single (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

def locHom (S : HSp D) {k : Type} [Ring k] (f : AE D →+* k) : GA D S →* Matrix (Fin S.rank) (Fin S.rank) k where
  toFun a := (mt S a).map f
  map_one' := by rw [PlacesAdeles.mt_one]; exact Matrix.map_one f f.map_zero f.map_one
  map_mul' a b := by rw [PlacesAdeles.mt_mul]; exact Matrix.map_mul

section Place

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : q.e * a = 0` using `eq_zero_at_off (· = q.v) (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)`. Establish `h2 : q.pr q.e = 1` using `by rw [← FrameLat.sec_one (p := q), q.pr_sec]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pr_off (q : SplitPt D k) {a : AE D} (ha : a ∈ idOff D (· = q.v)) : q.pr a = 0 := by
  have h1 : q.e * a = 0 := eq_zero_at_off (· = q.v)
    (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)
  have h2 : q.pr q.e = 1 := by rw [← FrameLat.sec_one (p := q), q.pr_sec]
  calc q.pr a = q.pr q.e * q.pr a := by rw [h2, one_mul]
    _ = 0 := by rw [← map_mul, h1, map_zero]

/- English proof (translation)
Rewrite `hb` using `[grpOff, PlacesAdeles.mem_congGrp]`. Use extensionality with `i j`. Establish `h` using `pr_off q (hb i j)`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_off (q : SplitPt D k) {S : HSp D} {b : GA D S} (hb : b ∈ grpOff S (· = q.v)) :
    (mt S b).map q.pr = 1 := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  ext i j
  have h := pr_off q (hb i j)
  rw [map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `H` using `(GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F`. Use `choose glf hglf using fun gk => (H.1 gk).exists`. Set `gl : GL Y k →* GA D S` to `MonoidHom.mk' glf fun a b => (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))`. Set `β : GlobalTheory.FinPl.Frame q S Y` to `⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩`. Take `⟨Λ, -, hΛ, hK⟩` from `GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN`.

Establish `hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k]` using `fun y => (hΛ y).trans (hI y).symm`. Take `⟨x₀, rfl⟩` from `hx`. Establish `hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) → ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k]`. Introduce `z y hy j`. Express the relevant statement in the definitionally equal form `((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)`. Establish `hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ`. Use extensionality with `y`. Rewrite using `[GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hint x₀ _ h` as an intermediate fact. Rewrite `this` using `[smul_inv_smul]`. Then use the resulting hypothesis. Introduce `h`.

Rewrite using `[← map_inv]`. Conclude with `hint x₀⁻¹ y h`. Conclude with `⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩`.
-/
theorem one_place (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) (q : SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) (hI : IntIn q S F N) (x : GL Y k) (hx : x ∈ GlobalTheory.SplitWeil.KO k Y) :
    ∃ g, InK S N (· = q.v) g ∧ (mt S g).map q.pr = F.β * x.val * F.γ := by
  classical
  have H := (GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F
  choose glf hglf using fun gk => (H.1 gk).exists
  let gl : GL Y k →* GA D S := MonoidHom.mk' glf fun a b =>
    (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))
  let β : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩
  obtain ⟨Λ, -, hΛ, hK⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN
  have hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k] := fun y => (hΛ y).trans (hI y).symm
  obtain ⟨x₀, rfl⟩ := hx
  have hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) →
      ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k] := by
    intro z y hy j
    change ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)
  have hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ := by
    ext y
    rw [GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]
    constructor
    · intro h
      have := hint x₀ _ h
      rwa [smul_inv_smul] at this
    · intro h
      rw [← map_inv]
      exact hint x₀⁻¹ y h
  exact ⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩

end Place

/- English proof (translation)
Introduce `D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx`. Use `choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)`. Establish `hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v)` using `fun i => (hgK i).1`. Establish `hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v)` using `fun i j hji => PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)`. Use `⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `_root_.list_prod_mem fun a ha => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `(List.mem_ofFn' _ _).1 ha`. Conclude with `PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)`. Establish `hlat` using `((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N`. Establish `hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v)` using `fun i => moves_list_prod _ fun a ha => by`.

Take `⟨j, rfl⟩` from `(List.mem_ofFn' _ _).1 ha`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Conclude with `(hgK j).2`. Conclude with `moves_off (hoff i j hji)`.

Introduce `y hy`. Rewrite using `[hlat y hN.1, hlat _ hN.1]`. Establish `hy'` using `PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy`. Establish `hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v)` using `fun v e he i => by`. Simplify `Ideal.mul_mem_right (y i) _ he.1` using `[smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h2⟩`. Use `⟨hy', fun v hv e he => ?_⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `hv`. Rewrite using `[← Matrix.mulVec_smul]`.

Conclude with `(hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)`. Introduce and unpack `⟨-, h2⟩`. Use `⟨hy, fun v hv e he => ?_⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `hv`. Use `h2 _ ⟨i, rfl⟩ e he` as an intermediate fact.

Rewrite `this` using `[← Matrix.mulVec_smul]`. Conclude with `(hloc i _ (hey _ e he)).2 this`. Introduce `i`. Express the relevant statement in the definitionally equal form `locHom S (q i).pr (List.ofFn g).prod = _`. Rewrite using `[map_list_prod, List.map_ofFn, prod_ofFn_single _ i]`.

Conclude with `hgm i`. Introduce `j hji`. Conclude with `map_off (q i) (hoff i j hji)`.
-/
theorem exists_of_local : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  intro D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx
  classical
  choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)
  have hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v) := fun i => (hgK i).1
  have hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v) := fun i j hji =>
    PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)
  refine ⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩
  · refine _root_.list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)
  · have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N
    have hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v) := fun i =>
      moves_list_prod _ fun a ha => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
        by_cases hji : j = i
        · subst hji; exact (hgK j).2
        · exact moves_off (hoff i j hji)
    intro y hy
    rw [hlat y hN.1, hlat _ hN.1]
    have hy' := PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      have := h2 _ ⟨i, rfl⟩ e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · intro i
    change locHom S (q i).pr (List.ofFn g).prod = _
    rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i]
    · exact hgm i
    · intro j hji
      exact map_off (q i) (hoff i j hji)

end GlobalTheory.SplitOnto

end
