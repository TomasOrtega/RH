import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.QCoh RingTheory.Sequence

namespace GlobalTheory.RegBasis

section General

variable {X : Scheme.{0}} {L : LB X} {k : Type} [Field k] [Algebra k Γ(X, ⊤)] {V : Type} [AddCommGroup V]
  [Module k V] (φ : V →ₛₗ[algebraMap k Γ(X, ⊤)] L.Sec)

def vanishAt (x : X) : Submodule k V where
  carrier := {w | x ∉ nonzeroLocus (φ w)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [φ.map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

/- English proof (translation)
The claim follows from `top_le_iff.1 (hv.ge.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)))`.
-/
theorem vanishAt_eq_top {ι : Type} {v : ι → V} (hv : Submodule.span k (Set.range v) = ⊤) {x : X}
    (hx : ∀ i, x ∉ nonzeroLocus (φ (v i))) : vanishAt φ x = ⊤ :=
  top_le_iff.1 (hv.ge.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)))

/- English proof (translation)
Proceed by induction on `m generalizing F W with`. Consider the case `zero`. Use `⟨Fin.elim0, ?_, by rw [List.ofFn_zero]; trivial⟩` and prove the remaining obligations. Rewrite using `[Submodule.eq_top_of_finrank_eq hW, top_sup_eq]`. Consider the case `succ m ih`.

Establish `hne : W ≠ ⊤` using `fun e => by`. Rewrite `hW` using `[e, finrank_top]`. Use linear arithmetic over natural numbers and integers. Establish `: Finite {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤}` using `((finite_assPoints F).subset fun _ hx => hx.1).to_subtype`. Take `⟨w, hw⟩` from `Submodule.exists_forall_notMem_of_forall_ne_top (fun o : Option {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} => o.elim W fun x => vanishAt φ x.1) (by`.

Introduce and unpack `(_ | x)`. Use `exacts [hne, x.2.2])`. Establish `hsup : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = W ⊔ Submodule.span k (Set.range (Fin.cons w v : Fin (m + 1) → V))` using `fun v => by`. Rewrite using `[Fin.range_cons, Submodule.span_insert, sup_assoc]`. Establish `key : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = ⊤ → ∀ x, vanishAt φ x = ⊤ → IsWeaklyRegular (F.presheaf.stalk x :) (X.presheaf.germ _ x (hc x) ((φ w).f (c x)) :: List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x)))` using `fun v hv x hx => by`.

Use `h (Fin.cons w v) ((hsup v).symm.trans hv) x hx` as an intermediate fact. Rewrite `this` using `[List.ofFn_succ]`. Then use the resulting hypothesis. Take `⟨v, hv, hr⟩` from `ih (cut F hL (φ w)) (W ⊔ Submodule.span k {w}) (by rw [Submodule.finrank_sup_span_singleton (p := W) (hw none)]; omega) fun v hv x hx => by`. Take `⟨q⟩` from `CutDegree.nonempty_stalk_cut_equiv F hL (φ w) (c x) (hc x)`. Conclude with `(q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x hx)).2`.

Use `⟨Fin.cons w v, (hsup v).symm.trans hv, ?_⟩` and prove the remaining obligations. Rewrite using `[List.ofFn_succ]`. Use `(regSeq_cons hL F _ _).2 ⟨(mono_cutHom_iff F hL _).2 fun x hx => ?_, hr⟩` and prove the remaining obligations. Distinguish the cases in `e : vanishAt φ x = ⊤`. Establish `hreg` using `((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x e)).1`.

Take `⟨t, ht⟩` from `mem_assPoints_iff_exists.1 hx`. Use `(Cartier.mem_nonzeroLocus_iff (φ w) (c x) (hc x)).2 ((X.mem_basicOpen _ x (hc x)).2 ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Establish `h0 : t = 0` using `hreg (((ht _).2 hu).trans (smul_zero _).symm)`. Conclude with `(ht 1).1 (by rw [h0, smul_zero]) isUnit_one`.

Conclude with `not_not.1 (hw (some ⟨x, hx, e⟩))`.
-/
theorem exists_regSeq [Infinite k] [Module.Finite k V] [AlgebraicGeometry.IsNoetherian X] (hL : L.IsLB)
    (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) (m : ℕ) (F : X.Modules) [IsFiniteQC F] (W : Submodule k V)
    (hW : Module.finrank k W + m = Module.finrank k V)
    (h : ∀ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ → ∀ x, vanishAt φ x = ⊤ →
      IsWeaklyRegular (F.presheaf.stalk x :) (List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x)))) :
    ∃ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ ∧ RegSeq hL F (List.ofFn fun i => φ (v i)) := by
  induction m generalizing F W with
  | zero =>
    refine ⟨Fin.elim0, ?_, by rw [List.ofFn_zero]; trivial⟩
    rw [Submodule.eq_top_of_finrank_eq hW, top_sup_eq]
  | succ m ih =>
    have hne : W ≠ ⊤ := fun e => by
      rw [e, finrank_top] at hW
      omega
    have : Finite {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} :=
      ((finite_assPoints F).subset fun _ hx => hx.1).to_subtype
    obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun o : Option {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} => o.elim W fun x => vanishAt φ x.1)
      (by
        rintro (_ | x)
        exacts [hne, x.2.2])
    have hsup : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) =
        W ⊔ Submodule.span k (Set.range (Fin.cons w v : Fin (m + 1) → V)) := fun v => by
      rw [Fin.range_cons, Submodule.span_insert, sup_assoc]
    have key : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = ⊤ →
        ∀ x, vanishAt φ x = ⊤ → IsWeaklyRegular (F.presheaf.stalk x :)
          (X.presheaf.germ _ x (hc x) ((φ w).f (c x)) ::
            List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x))) := fun v hv x hx => by
      have := h (Fin.cons w v) ((hsup v).symm.trans hv) x hx
      rwa [List.ofFn_succ] at this
    obtain ⟨v, hv, hr⟩ := ih (cut F hL (φ w)) (W ⊔ Submodule.span k {w})
      (by rw [Submodule.finrank_sup_span_singleton (p := W) (hw none)]; omega) fun v hv x hx => by
        obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv F hL (φ w) (c x) (hc x)
        exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x hx)).2
    refine ⟨Fin.cons w v, (hsup v).symm.trans hv, ?_⟩
    rw [List.ofFn_succ]
    refine (regSeq_cons hL F _ _).2 ⟨(mono_cutHom_iff F hL _).2 fun x hx => ?_, hr⟩
    by_cases e : vanishAt φ x = ⊤
    · have hreg := ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x e)).1
      obtain ⟨t, ht⟩ := mem_assPoints_iff_exists.1 hx
      refine (Cartier.mem_nonzeroLocus_iff (φ w) (c x) (hc x)).2 ((X.mem_basicOpen _ x (hc x)).2 ?_)
      by_contra hu
      have h0 : t = 0 := hreg (((ht _).2 hu).trans (smul_zero _).symm)
      exact (ht 1).1 (by rw [h0, smul_zero]) isUnit_one
    · exact not_not.1 (hw (some ⟨x, hx, e⟩))

/- English proof (translation)
Take `⟨e⟩` from `Twist.nonempty_stalkEquiv (F := structureModule X) hB x`. Set `i : twist (structureModule X) B ≅ LB.toMod B` to `Twist.unitTwistIso B`. Conclude with `⟨(LinearEquiv.ofBijective (stalkLinear i.hom x) ⟨stalkLinear_injective _ x, stalkLinear_surjective _ x⟩).symm ≪≫ₗ e ≪≫ₗ structureModuleStalkEquiv x⟩`.
-/
theorem nonempty_stalk_toMod {B : LB X} (hB : B.IsLB) (x : X) :
    Nonempty (((LB.toMod B).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨e⟩ := Twist.nonempty_stalkEquiv (F := structureModule X) hB x
  let i : twist (structureModule X) B ≅ LB.toMod B := Twist.unitTwistIso B
  exact ⟨(LinearEquiv.ofBijective (stalkLinear i.hom x)
    ⟨stalkLinear_injective _ x, stalkLinear_surjective _ x⟩).symm ≪≫ₗ e ≪≫ₗ structureModuleStalkEquiv x⟩

end General

def combMap {k : Type} [Field k] (S : LinSys k) {D : ℕ} (s : Fin D → Fin S.N → k) :
    (Fin D → k) →ₛₗ[algebraMap k Γ(S.Y, ⊤)] S.L.Sec where
  toFun c := S.comb (∑ j, c j • s j)
  map_add' a b := by
    simp only [LinSys.comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
  map_smul' a b := by
    simp only [LinSys.comb, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_mul]

/- English proof (translation)
Introduce `K _ _ G s hs B hB`. Establish `hp` using `G.geom.alg.variety.proj`. Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Establish `: IsFiniteQC (LB.toMod B)` using `isFiniteQC_iff_isFiniteType.2 ⟨LB.isQuasicoherent_toMod hB, LB.isFiniteType_toMod hB⟩`. Establish `hfin : ((G.ideal s).support : Set G.Y).Finite`.

Use `hs.finite` as an intermediate fact. Establish `h` using `((G.ideal s).subschemeι ≫ G.str).finite_preimage_singleton (IsLocalRing.closedPoint K)`. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]`. Conclude with `(h.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _`. Take `⟨v, hv, hr⟩` from `exists_regSeq (combMap G.toLinSys s) G.isLB G.chartAt G.mem_chartAt G.D (LB.toMod B) ⊥ (by simp) fun v hv x hx => by`.

Rewrite `hv` using `[bot_sup_eq]`. Take `⟨q⟩` from `nonempty_stalk_toMod hB x`. Use `(q.isWeaklyRegular_congr _).2 ((ProperCut.topSelf_eq_length_of_smooth G.str G.smooth hp G.isLB (fun i => combMap G.toLinSys s (v i)) (hfin.subset fun y hy => ?_)).2.1 x ?_ _ _).toIsWeaklyRegular` and prove the remaining obligations. Establish `e` using `vanishAt_eq_top _ hv ((mem_support_cutIdeal _ _ y).1 hy)`. Use `(mem_support_cutIdeal _ _ y).2 fun i => ?_` and prove the remaining obligations.

Establish `h : y ∉ nonzeroLocus (G.comb (∑ j, (Pi.single i 1 : Fin G.D → K) j • s j))` using `e.ge (Submodule.mem_top (x := Pi.single i 1))`. Simplify `h` using `[Pi.single_apply]`. Conclude with `(mem_support_cutIdeal _ _ x).2 fun i => hx.ge (Submodule.mem_top (x := v i))`. Rewrite `hv` using `[bot_sup_eq]`. Use `⟨Matrix.of v, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 (linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp))), hr⟩` and prove the remaining obligations.
-/
theorem exists_regular_basis : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K),
    G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧
      RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  intro K _ _ G s hs B hB
  have hp := G.geom.alg.variety.proj
  have := isNoetherian_of_isProjOver hp
  have : IsFiniteQC (LB.toMod B) := isFiniteQC_iff_isFiniteType.2 ⟨LB.isQuasicoherent_toMod hB, LB.isFiniteType_toMod hB⟩
  have hfin : ((G.ideal s).support : Set G.Y).Finite := by
    have := hs.finite
    have h := ((G.ideal s).subschemeι ≫ G.str).finite_preimage_singleton (IsLocalRing.closedPoint K)
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (h.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _
  obtain ⟨v, hv, hr⟩ := exists_regSeq (combMap G.toLinSys s) G.isLB G.chartAt G.mem_chartAt G.D (LB.toMod B) ⊥
    (by simp) fun v hv x hx => by
      rw [bot_sup_eq] at hv
      obtain ⟨q⟩ := nonempty_stalk_toMod hB x
      refine (q.isWeaklyRegular_congr _).2 ((ProperCut.topSelf_eq_length_of_smooth G.str G.smooth hp G.isLB
        (fun i => combMap G.toLinSys s (v i)) (hfin.subset fun y hy => ?_)).2.1 x ?_ _ _).toIsWeaklyRegular
      · have e := vanishAt_eq_top _ hv ((mem_support_cutIdeal _ _ y).1 hy)
        refine (mem_support_cutIdeal _ _ y).2 fun i => ?_
        have h : y ∉ nonzeroLocus (G.comb (∑ j, (Pi.single i 1 : Fin G.D → K) j • s j)) :=
          e.ge (Submodule.mem_top (x := Pi.single i 1))
        simpa [Pi.single_apply] using h
      · exact (mem_support_cutIdeal _ _ x).2 fun i => hx.ge (Submodule.mem_top (x := v i))
  rw [bot_sup_eq] at hv
  refine ⟨Matrix.of v, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
    (linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp))), hr⟩

end GlobalTheory.RegBasis
