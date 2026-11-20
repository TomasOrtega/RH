import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlbHZeroRight

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

/- English proof (translation)
Use `haveI : NoZeroDivisors E := ⟨fun {a b} hab => by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨u, hu⟩` from `hE a hne.1`. Apply `hne.2` to reduce the goal to its premises.

Establish `h2` using `congrArg (fun t => (↑u⁻¹ : E) * t) hab`. Simplify using `only [mul_zero, ← mul_assoc] at h2`. Rewrite using `[← hu, Units.inv_mul, one_mul] at h2⟩` and apply the resulting hypothesis. Use `haveI : IsDomain E := NoZeroDivisors.to_isDomain E`. Take `⟨hfg, hspan, hdual⟩` from `hΛ`.

Use `haveI : Module.Finite M.L.O Λ := Module.Finite.iff_fg.mpr hfg`. Use `haveI : NoZeroSMulDivisors M.L.O Λ := ⟨fun {r x} h => by`. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`.

Establish `hr' : (r : E) ≠ 0` using `fun h0 => hr (Subtype.ext h0)`. Take `⟨u, hu⟩` from `hE _ hr'`. Establish `h1 : (r : E) • (x : V) = 0`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[Submodule.coe_smul, Subring.smul_def]`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `congrArg (fun v => (↑u⁻¹ : E) • v) h1`. Simplify using `only [smul_zero, smul_smul] at h2`. Rewrite `h2` using `[← hu, Units.inv_mul, one_smul]`. Simplify using `using h2⟩`.

Use `haveI : Module.Free M.L.O Λ := Module.free_of_finite_type_torsion_free'`. Set `B` to `Module.Free.chooseBasis M.L.O Λ`. Set `bb : Module.Free.ChooseBasisIndex M.L.O Λ → V` to `fun i => (B i : V)`. Establish `hexp : ∀ (x : V) (hx : x ∈ Λ), x = ∑ i, ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i`. Introduce `x hx`.

Establish `h2` using `congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2`. Conclude with `h2.symm`. Establish `hli : LinearIndependent E bb`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `choose s hsO hs using fun j => hden (g j)`. Use `set t := ∏ j, s j with ht`. Establish `htO : t ∈ M.L.O` using `Subring.prod_mem _ fun j _ => hsO j`. Establish `ht0 : t ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j _ => (hs j).1`.

Establish `htg : ∀ j, t * g j ∈ M.L.O`. Introduce `j`. Establish `e : t * g j = (∏ j' ∈ Finset.univ.erase j, s j') * (s j * g j)`. Rewrite using `[ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `M.L.O.mul_mem (Subring.prod_mem _ fun j' _ => hsO j') (hs j).2`. Set `g' : Module.Free.ChooseBasisIndex M.L.O Λ → M.L.O` to `fun j => ⟨t * g j, htg j⟩`. Establish `hsum : ∑ j, g' j • B j = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero]`. Establish `: ∑ j, (t * g j) • bb j = t • ∑ j, g j • bb j`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [smul_smul]`. Simplify `this` using `[g', bb, hg]`.

Establish `h0` using `Fintype.linearIndependent_iff.mp B.linearIndependent g' hsum i`. Establish `h0' : t * g i = 0` using `congrArg Subtype.val h0`. Conclude with `(mul_eq_zero.mp h0').resolve_left ht0`. Establish `hsp : ⊤ ≤ Submodule.span E (Set.range bb)`. Rewrite using `[← hspan]`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[hexp x hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `BE` to `Basis.mk hli hsp`.

Establish `hcard : Module.finrank E V = Fintype.card (Module.Free.ChooseBasisIndex M.L.O Λ)` using `Module.finrank_eq_card_basis BE`. Set `eι` to `Fintype.equivFinOfCardEq hcard.symm`. Set `b : Fin (Module.finrank E V) → V` to `fun k => bb (eι.symm k)`. Establish `hbΛ : ∀ k, b k ∈ Λ` using `fun k => (B (eι.symm k)).2`. Establish `hlib : LinearIndependent E b` using `hli.comp _ eι.symm.injective`.

Establish `hexpb : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k`. Introduce `x hx`. Use `⟨fun k => ((B.repr ⟨x, hx⟩ (eι.symm k) : M.L.O) : E), fun k => Subtype.property _, ?_⟩` and prove the remaining obligations. Conclude with `(hexp x hx).trans (Equiv.sum_comp eι.symm (fun i => ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i)).symm`. Use `⟨b, hbΛ, hlib, hexpb, ?_⟩` and prove the remaining obligations.

Use `set G : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E := Matrix.of (fun k l => H.h (b k) (b l)) with hG`. Establish `hdet0 : G.det ≠ 0`. Introduce `hd`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hd`. Use `set x := ∑ k, v k • b k with hx`.

Establish `hxb : ∀ l, H.h x (b l) = 0`. Introduce `l`. Rewrite using `[hx, flb_h_sum_left]`. Use `congrFun hv l` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, hG]`.

Establish `hx0 : x = 0`. Apply `H.nondeg` to reduce the goal to its premises. Introduce `y`. Establish `hy` using `BE.sum_repr y`. Rewrite using `[← hy, flb_h_sum_right]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Establish `: BE i = b (eι i)` using `by simp [BE, b]`. Rewrite using `[this, hxb, mul_zero]`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Conclude with `Fintype.linearIndependent_iff.mp hlib v hx0.symm.symm k`. Establish `hdet : IsUnit G.det` using `hE _ hdet0`. Use `⟨G⁻¹, ?_, Matrix.nonsing_inv_mul G hdet⟩` and prove the remaining obligations. Establish `hQG` using `Matrix.nonsing_inv_mul G hdet`.

Introduce `k m`. Use `set d := ∑ m', G⁻¹ k m' • b m' with hd`. Establish `hdb : ∀ l, H.h d (b l) = if k = l then 1 else 0`. Introduce `l`. Rewrite using `[hd, flb_h_sum_left]`.

Use `congrFun (congrFun hQG k) l` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, hG, Matrix.one_apply]`. Establish `hdΛ : d ∈ Λ`. Rewrite using `[hdual]`. Introduce `y hy`.

Take `⟨c, hcO, rfl⟩` from `hexpb y hy`. Rewrite using `[flb_h_sum_right]`. Simplify using `only [hdb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `flb_cj_mem M.L (hcO k)`. Take `⟨c', hc'O, hc'⟩` from `hexpb d hdΛ`.

Establish `hz : ∑ m', (G⁻¹ k m' - c' m') • b m' = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hd, ← hc', sub_self]`. Use `Fintype.linearIndependent_iff.mp hlib _ hz m` as an intermediate fact. Rewrite using `[sub_eq_zero.mp this]`.

Conclude with `hc'O m`.
-/
theorem flb_main {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hnt : Nontrivial E)
    (hden : ∀ x : E, ∃ s ∈ M.L.O, s ≠ 0 ∧ s * x ∈ M.L.O)
    (hpid : IsPrincipalIdealRing M.L.O)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) :
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1 := by
  classical
  haveI : NoZeroDivisors E := ⟨fun {a b} hab => by
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hE a hne.1
    apply hne.2
    have h2 := congrArg (fun t => (↑u⁻¹ : E) * t) hab
    simp only [mul_zero, ← mul_assoc] at h2
    rwa [← hu, Units.inv_mul, one_mul] at h2⟩
  haveI : IsDomain E := NoZeroDivisors.to_isDomain E
  obtain ⟨hfg, hspan, hdual⟩ := hΛ
  haveI : Module.Finite M.L.O Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors M.L.O Λ := ⟨fun {r x} h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
    obtain ⟨u, hu⟩ := hE _ hr'
    have h1 : (r : E) • (x : V) = 0 := by
      have := congrArg Subtype.val h
      simpa [Submodule.coe_smul, Subring.smul_def] using this
    apply Subtype.ext
    have h2 := congrArg (fun v => (↑u⁻¹ : E) • v) h1
    simp only [smul_zero, smul_smul] at h2
    rw [← hu, Units.inv_mul, one_smul] at h2
    simpa using h2⟩
  haveI : Module.Free M.L.O Λ := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis M.L.O Λ
  let bb : Module.Free.ChooseBasisIndex M.L.O Λ → V := fun i => (B i : V)
  have hexp : ∀ (x : V) (hx : x ∈ Λ), x = ∑ i, ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i := by
    intro x hx
    have h2 := congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    exact h2.symm
  have hli : LinearIndependent E bb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose s hsO hs using fun j => hden (g j)
    set t := ∏ j, s j with ht
    have htO : t ∈ M.L.O := Subring.prod_mem _ fun j _ => hsO j
    have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hs j).1
    have htg : ∀ j, t * g j ∈ M.L.O := by
      intro j
      have e : t * g j = (∏ j' ∈ Finset.univ.erase j, s j') * (s j * g j) := by
        rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        ring
      rw [e]
      exact M.L.O.mul_mem (Subring.prod_mem _ fun j' _ => hsO j') (hs j).2
    let g' : Module.Free.ChooseBasisIndex M.L.O Λ → M.L.O := fun j => ⟨t * g j, htg j⟩
    have hsum : ∑ j, g' j • B j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero]
      have : ∑ j, (t * g j) • bb j = t • ∑ j, g j • bb j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      simpa [g', bb, hg] using this
    have h0 := Fintype.linearIndependent_iff.mp B.linearIndependent g' hsum i
    have h0' : t * g i = 0 := congrArg Subtype.val h0
    exact (mul_eq_zero.mp h0').resolve_left ht0
  have hsp : ⊤ ≤ Submodule.span E (Set.range bb) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let BE := Basis.mk hli hsp
  have hcard : Module.finrank E V = Fintype.card (Module.Free.ChooseBasisIndex M.L.O Λ) :=
    Module.finrank_eq_card_basis BE
  let eι := Fintype.equivFinOfCardEq hcard.symm
  let b : Fin (Module.finrank E V) → V := fun k => bb (eι.symm k)
  have hbΛ : ∀ k, b k ∈ Λ := fun k => (B (eι.symm k)).2
  have hlib : LinearIndependent E b := hli.comp _ eι.symm.injective
  have hexpb : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧
      x = ∑ k, c k • b k := by
    intro x hx
    refine ⟨fun k => ((B.repr ⟨x, hx⟩ (eι.symm k) : M.L.O) : E), fun k => Subtype.property _, ?_⟩
    exact (hexp x hx).trans
      (Equiv.sum_comp eι.symm (fun i => ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i)).symm
  refine ⟨b, hbΛ, hlib, hexpb, ?_⟩
  set G : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E :=
    Matrix.of (fun k l => H.h (b k) (b l)) with hG
  have hdet0 : G.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    set x := ∑ k, v k • b k with hx
    have hxb : ∀ l, H.h x (b l) = 0 := by
      intro l
      rw [hx, flb_h_sum_left]
      have := congrFun hv l
      simpa [Matrix.vecMul, dotProduct, hG] using this
    have hx0 : x = 0 := by
      apply H.nondeg
      intro y
      have hy := BE.sum_repr y
      rw [← hy, flb_h_sum_right]
      apply Finset.sum_eq_zero
      intro i _
      have : BE i = b (eι i) := by simp [BE, b]
      rw [this, hxb, mul_zero]
    apply hv0
    funext k
    exact Fintype.linearIndependent_iff.mp hlib v hx0.symm.symm k
  have hdet : IsUnit G.det := hE _ hdet0
  refine ⟨G⁻¹, ?_, Matrix.nonsing_inv_mul G hdet⟩
  have hQG := Matrix.nonsing_inv_mul G hdet
  intro k m
  set d := ∑ m', G⁻¹ k m' • b m' with hd
  have hdb : ∀ l, H.h d (b l) = if k = l then 1 else 0 := by
    intro l
    rw [hd, flb_h_sum_left]
    have := congrFun (congrFun hQG k) l
    simpa [Matrix.mul_apply, hG, Matrix.one_apply] using this
  have hdΛ : d ∈ Λ := by
    rw [hdual]
    intro y hy
    obtain ⟨c, hcO, rfl⟩ := hexpb y hy
    rw [flb_h_sum_right]
    simp only [hdb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact flb_cj_mem M.L (hcO k)
  obtain ⟨c', hc'O, hc'⟩ := hexpb d hdΛ
  have hz : ∑ m', (G⁻¹ k m' - c' m') • b m' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hd, ← hc', sub_self]
  have := Fintype.linearIndependent_iff.mp hlib _ hz m
  rw [sub_eq_zero.mp this]
  exact hc'O m

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ M hF hc hE V _ _ H Λ hΛ`. Use `haveI := hF`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨-, hden0, hfac⟩` from `h1 F E M.L hF hc hE ϖ hϖ`. Establish `hnt : Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)`.

Use `flb_main M hE hnt ?_ (flb_pid M.L.O _ (flb_int_mem M.L ϖ) hfac) V H Λ hΛ` and prove the remaining obligations. Introduce `x`. Take `⟨c, hc0, hcx⟩` from `hden0 x`. Use `⟨_, flb_int_mem M.L c, ?_, hcx⟩` and prove the remaining obligations. Establish `hcF : (c : F) ≠ 0` using `by exact_mod_cast hc0`.

Conclude with `(map_ne_zero_iff _ (algebraMap F E).injective).mpr hcF`.
-/
theorem flatBasis_of (h1 : FLocO) : FLatBasis := by
  intro F E _ _ _ _ _ _ _ M hF hc hE V _ _ H Λ hΛ
  haveI := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hden0, hfac⟩ := h1 F E M.L hF hc hE ϖ hϖ
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  refine flb_main M hE hnt ?_ (flb_pid M.L.O _ (flb_int_mem M.L ϖ) hfac) V H Λ hΛ
  intro x
  obtain ⟨c, hc0, hcx⟩ := hden0 x
  refine ⟨_, flb_int_mem M.L c, ?_, hcx⟩
  have hcF : (c : F) ≠ 0 := by exact_mod_cast hc0
  exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hcF

end PI.UnitaryGroupMassFormula.CntFormula
