import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HasGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Rel

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def SecCorr (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (x : LB.Sec (LB.LinComb L φ' ε')) : Prop :=
  ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' → (∀ k k', φ k = φ' k' → j k = j' k') →
    rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
      rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (x.f j')

/- English proof (translation)
Establish `memw : ∀ {T : Type} [Fintype T] (ψ : T → (Y ⟶ X)) (i : T → L.ι), y ∈ LB.wchart L ψ i ↔ ∀ t, (ψ t).base y ∈ L.U (i t)`. Introduce `T _ ψ i`. Use `first`. Consider the case `exact Set.mem_iInter`. Consider the case `simp [LB.wchart]`.

Establish `hcov : ∀ x : X, ∃ i, x ∈ L.U i`. Introduce `x`. Establish `hx : x ∈ (⨆ i, L.U i)` using `by rw [hL.cover]; trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp hx`. Set `g : (Y ⟶ X) → L.ι` to `fun ψ => if h : ∃ k', φ' k' = ψ then j' h.choose else (hcov (ψ.base y)).choose`.

Use `⟨fun k => g (φ k), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k₁ k₂ h show g (φ k₁) = g (φ k₂)`. Rewrite using `[h]`. Introduce `k k' h`. Establish `hex : ∃ k'', φ' k'' = φ k` using `⟨k', h.symm⟩`.

Use `show g (φ k) = j' k'`. Simplify using `only [g, dif_pos hex]`. Conclude with `hj' _ _ (hex.choose_spec.trans h)`. Rewrite using `[memw]`. Introduce `k`.

Establish `hy'` using `(memw φ' j').mp hy`. Use `show (φ k).base y ∈ L.U (g (φ k))`. Distinguish the cases in `hex : ∃ k'', φ' k'' = φ k`. Simplify using `only [g, dif_pos hex]`. Use `hy' hex.choose` as an intermediate fact.

Rewrite `this` using `[hex.choose_spec]`. Conclude with `this`. Simplify using `only [g, dif_neg hex]`. Conclude with `(hcov _).choose_spec`.
-/
private lemma exists_coh_extending_of_mem_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j' : K' → L.ι)
    (hj' : LB.Coh L φ' j') (y : Y) (hy : y ∈ LB.wchart L φ' j') :
    ∃ j : K → L.ι, LB.Coh L φ j ∧ (∀ k k', φ k = φ' k' → j k = j' k') ∧ y ∈ LB.wchart L φ j := by
  classical
  have memw : ∀ {T : Type} [Fintype T] (ψ : T → (Y ⟶ X)) (i : T → L.ι),
      y ∈ LB.wchart L ψ i ↔ ∀ t, (ψ t).base y ∈ L.U (i t) := by
    intro T _ ψ i
    first
    | exact Set.mem_iInter
    | simp [LB.wchart]
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := by
    intro x
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let g : (Y ⟶ X) → L.ι := fun ψ =>
    if h : ∃ k', φ' k' = ψ then j' h.choose else (hcov (ψ.base y)).choose
  refine ⟨fun k => g (φ k), ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    show g (φ k₁) = g (φ k₂)
    rw [h]
  · intro k k' h
    have hex : ∃ k'', φ' k'' = φ k := ⟨k', h.symm⟩
    show g (φ k) = j' k'
    simp only [g, dif_pos hex]
    exact hj' _ _ (hex.choose_spec.trans h)
  · rw [memw]
    intro k
    have hy' := (memw φ' j').mp hy
    show (φ k).base y ∈ L.U (g (φ k))
    by_cases hex : ∃ k'', φ' k'' = φ k
    · simp only [g, dif_pos hex]
      have := hy' hex.choose
      rw [hex.choose_spec] at this
      exact this
    · simp only [g, dif_neg hex]
      exact (hcov _).choose_spec

/- English proof (translation)
Use `first`. Consider the case `(apply TopCat.Presheaf.section_ext Z.sheaf W a b`. Introduce `z hz`. Take `⟨V, hV, hzV, he⟩` from `h z hz`. Establish `ha` using `congrArg (fun f => f.hom a) (Z.presheaf.germ_res (homOfLE hV) z hzV)`.

Establish `hb` using `congrArg (fun f => f.hom b) (Z.presheaf.germ_res (homOfLE hV) z hzV)`. Establish `hc` using `congrArg (Z.presheaf.germ V z hzV).hom he`. Conclude with `ha.symm.trans (hc.trans hb))`. Consider the case `(choose V hV hzV he using h`. Conclude with `TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : W => V z.1 z.2) W (fun z => homOfLE (hV z.1 z.2)) (by intro z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩) a b (fun z => he z.1 z.2))`.
-/
private lemma sections_eq_of_locally_rs_eq {Z : Scheme.{0}} {W : Z.Opens} (a b : Γ(Z, W))
    (h : ∀ z ∈ W, ∃ (V : Z.Opens) (hV : V ≤ W), z ∈ V ∧ rs hV a = rs hV b) : a = b := by
  first
  | (apply TopCat.Presheaf.section_ext Z.sheaf W a b
     intro z hz
     obtain ⟨V, hV, hzV, he⟩ := h z hz
     have ha := congrArg (fun f => f.hom a) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hb := congrArg (fun f => f.hom b) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hc := congrArg (Z.presheaf.germ V z hzV).hom he
     exact ha.symm.trans (hc.trans hb))
  | (choose V hV hzV he using h
     exact TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : W => V z.1 z.2) W
       (fun z => homOfLE (hV z.1 z.2))
       (by intro z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩) a b
       (fun z => he z.1 z.2))

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(simp only [rs, resTop]; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)`. Consider the case `(unfold rs; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)`. Consider the case `(simp [rs, resTop, ← Functor.map_comp])`.
-/
lemma rs_resTop {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (c : Γ(Z, ⊤)) :
    rs h (resTop U c) = resTop V c := by
  first
  | rfl
  | (simp only [rs, resTop]; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (unfold rs; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp [rs, resTop, ← Functor.map_comp])

/- English proof (translation)
Use `first`. Consider the case `exact map_mul _ a b`. Consider the case `simp [rs]`.
-/
private lemma map_mul_rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (a b : Γ(Z, U)) :
    rs h (a * b) = rs h a * rs h b := by
  first
  | exact map_mul _ a b
  | simp [rs]

/- English proof (translation)
Establish `memE : ∀ z : Y, z ∈ LB.wchart L (K` using `Empty) (fun e => e.elim : Empty → (Y ⟶ X)) (fun e => e.elim) := by`. Introduce `z`. Use `first`. Consider the case `exact Set.mem_iInter.mpr (fun e => e.elim)`. Consider the case `simp [LB.wchart]`.

Establish `stepA : ∀ j : K → L.ι, LB.Coh L φ j → resTop _ c * s₁.f j = resTop _ d * s₂.f j`. Introduce `j hj`. Apply `sections_eq_of_locally_rs_eq` to reduce the goal to its premises. Introduce `z hz`. Take `⟨j', hj', hjj, hzj'⟩` from `exists_coh_extending_of_mem_wchart (K := K') (K' := K) hL φ' φ j hj z hz`.

Establish `hcomp : ∀ k k', φ k = φ' k' → j k = j' k'` using `fun k k' h => (hjj k' k h.symm).symm`. Use `⟨LB.wchart L φ j ⊓ LB.wchart L φ' j', inf_le_left, ?_, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact ⟨hz, hzj'⟩`. Consider the case `exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hzj'⟩`.

Establish `e1` using `h1 j j' hj hj' hcomp`. Establish `e2` using `h2 j j' hj hj' hcomp`. Establish `e3` using `congrArg (rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _)) (hx j')`. Establish `m1` using `map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (s₁.f j)`. Establish `m2` using `map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (s₂.f j)`.

Establish `m3` using `map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (x₁.f j')`. Establish `m4` using `map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (x₂.f j')`. Rewrite `m1`, `m2`, `m3`, `m4` using `[rs_resTop]`. Conclude with `m1.trans ((congrArg (fun t => resTop _ c * t) e1).trans (m3.symm.trans (e3.trans (m4.trans ((congrArg (fun t => resTop _ d * t) e2.symm).trans m2.symm)))))`. Introduce `j`.

Apply `sections_eq_of_locally_rs_eq` to reduce the goal to its premises. Introduce `z hz`. Take `⟨j'', hj'', -, hz''⟩` from `exists_coh_extending_of_mem_wchart (K' := Empty) hL φ (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) z (memE z)`. Use `⟨(LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'', inf_le_left, ?_, ?_⟩` and prove the remaining obligations. Use `first`.

Consider the case `exact ⟨hz, hz''⟩`. Consider the case `exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hz''⟩`. Establish `e1` using `s₁.compat j j''`. Establish `e2` using `s₂.compat j j''`. Establish `e3` using `congrArg (rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)) (stepA j'' hj'')`.

Establish `m1` using `map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _) (resTop _ c) (s₁.f j)`. Establish `m2` using `map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _) (resTop _ d) (s₂.f j)`. Establish `m3` using `map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _) (resTop _ c) (s₁.f j'')`. Establish `m4` using `map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _) (resTop _ d) (s₂.f j'')`. Rewrite `m1`, `m2`, `m3`, `m4` using `[rs_resTop]`.

Establish `key` using `m3.symm.trans (e3.trans m4)`. Rewrite using `[m1, m2]`. Simplify using `only [rs]`. Rewrite using `[e1, e2, _root_.mul_left_comm, _root_.mul_left_comm (resTop _ d)]`. Use `congr 1`.
-/
theorem secCorr_scal (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    {s₁ s₂ : LB.Sec (LB.LinComb L φ ε)} {x₁ x₂ : LB.Sec (LB.LinComb L φ' ε')}
    (h1 : SecCorr φ ε φ' ε' s₁ x₁) (h2 : SecCorr φ ε φ' ε' s₂ x₂) (c d : Γ(Y, ⊤))
    (hx : ∀ j' : K' → L.ι, resTop _ c * x₁.f j' = resTop _ d * x₂.f j') :
    ∀ j : K → L.ι, resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
  have memE : ∀ z : Y, z ∈ LB.wchart L (K := Empty) (fun e => e.elim : Empty → (Y ⟶ X)) (fun e => e.elim) := by
    intro z
    first
    | exact Set.mem_iInter.mpr (fun e => e.elim)
    | simp [LB.wchart]
  have stepA : ∀ j : K → L.ι, LB.Coh L φ j → resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
    intro j hj
    apply sections_eq_of_locally_rs_eq
    intro z hz
    obtain ⟨j', hj', hjj, hzj'⟩ := exists_coh_extending_of_mem_wchart (K := K') (K' := K) hL φ' φ j hj z hz
    have hcomp : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' h => (hjj k' k h.symm).symm
    refine ⟨LB.wchart L φ j ⊓ LB.wchart L φ' j', inf_le_left, ?_, ?_⟩
    · first
      | exact ⟨hz, hzj'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hzj'⟩
    · have e1 := h1 j j' hj hj' hcomp
      have e2 := h2 j j' hj hj' hcomp
      have e3 := congrArg (rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _)) (hx j')
      have m1 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (s₁.f j)
      have m2 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (s₂.f j)
      have m3 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (x₁.f j')
      have m4 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (x₂.f j')
      rw [rs_resTop] at m1 m2 m3 m4
      exact m1.trans ((congrArg (fun t => resTop _ c * t) e1).trans (m3.symm.trans (e3.trans
        (m4.trans ((congrArg (fun t => resTop _ d * t) e2.symm).trans m2.symm)))))
  intro j
  apply sections_eq_of_locally_rs_eq
  intro z hz
  obtain ⟨j'', hj'', -, hz''⟩ := exists_coh_extending_of_mem_wchart (K' := Empty) hL φ
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) z (memE z)
  refine ⟨(LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'', inf_le_left, ?_, ?_⟩
  · first
    | exact ⟨hz, hz''⟩
    | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hz''⟩
  · have e1 := s₁.compat j j''
    have e2 := s₂.compat j j''
    have e3 := congrArg (rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _))
      (stepA j'' hj'')
    have m1 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j)
    have m2 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j)
    have m3 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j'')
    have m4 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j'')
    rw [rs_resTop] at m1 m2 m3 m4
    have key := m3.symm.trans (e3.trans m4)
    rw [m1, m2]
    dsimp only [rs]
    rw [e1, e2, _root_.mul_left_comm, _root_.mul_left_comm (resTop _ d)]
    congr 1

end Rel

section SameSum

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)

/- English proof (translation)
Establish `h` using `D.toPre.c_add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h' : D.toPre.c 0 * D.toPre.c 0 = D.toPre.c 0 * 1`. Rewrite using `[_root_.mul_one]`. Conclude with `h.symm`.

Conclude with `_root_.mul_left_cancel h'`.
-/
lemma c_zero : D.toPre.c 0 = 1 := by
  have h := D.toPre.c_add 0 0
  rw [add_zero] at h
  have h' : D.toPre.c 0 * D.toPre.c 0 = D.toPre.c 0 * 1 := by
    rw [_root_.mul_one]
    exact h.symm
  exact _root_.mul_left_cancel h'

/- English proof (translation)
Establish `h1 : (toUnit D.toPre.P.A ≫ D.toPre.c 0) = 1`. Rewrite using `[c_zero D]`. Use `first`. Consider the case `simp [Hom.one_def]`. Consider the case `(rw [Hom.one_def, Hom.one_def, ← Category.assoc]; congr 1)`.

Use `show (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = 𝟙 _`. Rewrite using `[h1]`. Use `show ((𝟙 D.toPre.P.A) * 1 : D.toPre.P.A ⟶ D.toPre.P.A).left = _`. Rewrite using `[_root_.mul_one]`. Use `first`.

Consider the case `rfl`. Consider the case `simp`.
-/
lemma famφB0_one : D.toPre.famφB 0 1 = 𝟙 _ := by
  have h1 : (toUnit D.toPre.P.A ≫ D.toPre.c 0) = 1 := by
    rw [c_zero D]
    first
    | simp [Hom.one_def]
    | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]; congr 1)
  show (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = 𝟙 _
  rw [h1]
  show ((𝟙 D.toPre.P.A) * 1 : D.toPre.P.A ⟶ D.toPre.P.A).left = _
  rw [_root_.mul_one]
  first
  | rfl
  | simp

/- English proof (translation)
Use `show (toUnit D.toPre.P.A ≫ D.toPre.c 0).left = (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left`. Rewrite using `[c_zero D, Hom.one_def]`. Use `first`. Consider the case `simp`. Consider the case `(congr 1; rw [← Category.assoc]; congr 1)`.
-/
lemma famφB0_two : D.toPre.famφB 0 2 = D.toPre.famφB 0 3 := by
  show (toUnit D.toPre.P.A ≫ D.toPre.c 0).left = (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left
  rw [c_zero D, Hom.one_def]
  first
  | simp
  | (congr 1; rw [← Category.assoc]; congr 1)

/- English proof (translation)
Introduce `ψ`. Establish `h0 : D.toPre.famφB 0 0 = 𝟙 _` using `rfl`. Establish `e1` using `famφB0_one D`. Establish `e2` using `famφB0_two D`. Rewrite using `[Fin.sum_univ_four, Fin.sum_univ_one]`.

Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `(exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (h0.symm.trans ‹D.toPre.famφB 0 0 = ψ›))`. Consider the case `(exfalso; exact ‹¬ D.toPre.famφB 0 0 = ψ› (h0.trans ‹𝟙 D.toPre.P.A.left = ψ›))`. Consider the case `(exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (e1.symm.trans ‹D.toPre.famφB 0 1 = ψ›))`.

Consider the case `(exfalso; exact ‹¬ D.toPre.famφB 0 1 = ψ› (e1.trans ‹𝟙 D.toPre.P.A.left = ψ›))`. Consider the case `(exfalso; exact ‹¬ D.toPre.famφB 0 3 = ψ› (e2.symm.trans ‹D.toPre.famφB 0 2 = ψ›))`. Consider the case `(exfalso; exact ‹¬ D.toPre.famφB 0 2 = ψ› (e2.trans ‹D.toPre.famφB 0 3 = ψ›))`. Consider the case `(simp [DegPre.famε]; done)`. Consider the case `rfl`.

Consider the case `decide`.
-/
lemma sameSum_famφB0 : LB.SameSum (D.toPre.famφB 0) (DegPre.famε 1)
    (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) := by
  intro ψ
  have h0 : D.toPre.famφB 0 0 = 𝟙 _ := rfl
  have e1 := famφB0_one D
  have e2 := famφB0_two D
  rw [Fin.sum_univ_four, Fin.sum_univ_one]
  split_ifs
  all_goals first
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (h0.symm.trans ‹D.toPre.famφB 0 0 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 0 = ψ› (h0.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (e1.symm.trans ‹D.toPre.famφB 0 1 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 1 = ψ› (e1.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 3 = ψ› (e2.symm.trans ‹D.toPre.famφB 0 2 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 2 = ψ› (e2.trans ‹D.toPre.famφB 0 3 = ψ›))
    | (simp [DegPre.famε]; done)
    | rfl
    | decide

end SameSum

section Rank

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} (D : DegData R I)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Take `⟨V, hpV, b, hb⟩` from `hLaws.secBaseChange (Spec (CommRingCat.of R)) D.toPre.P 1 le_rfl (IsLocalRing.closedPoint R)`. Establish `hV : V = ⊤` using `eq_top_of_closedPoint_mem V hpV`. Set `t0 : Spec (CommRingCat.of R) ⟶ (overRes (T` to `baseOver (Spec (CommRingCat.of R))) V).left := IsOpenImmersion.lift V.ι (𝟙 _) (by`. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `⟨⟨x, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[hV]`. Use the proof step `trivial)`. Establish `ht0 : t0 ≫ V.ι = 𝟙 _` using `IsOpenImmersion.lift_fac _ _ _`. Use `set T := baseAt t0 with hTdef`.

Establish `hT : T.hom = 𝟙 _` using `by show t0 ≫ V.ι ≫ 𝟙 _ = 𝟙 _`. Rewrite using `[Category.comp_id, ht0]`. Set `b' : Fin (1 ^ D.toPre.P.g) → LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T)` to `fun i => pullSec' D.toPre.P.L _ _ (b i) (homAt t0 ▷ D.toPre.P.A).left (fun _ => (snd T D.toPre.P.A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])`. Establish `hpull : ∀ i, IsPullSec D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) (homAt t0 ▷ D.toPre.P.A) (whiskerRight_snd (homAt t0) D.toPre.P.A) (b i) (b' i)` using `fun i j => pullSec'_f _ _ _ _ _ _ _ j`. Take `⟨-, hspan⟩` from `hb R t0 b' hpull`.

Establish `hsub : Subsingleton (Fin (1 ^ D.toPre.P.g))` using `by rw [one_pow]; infer_instance`. Establish `i0 : Fin (1 ^ D.toPre.P.g)` using `⟨0, by rw [one_pow]; exact Nat.one_pos⟩`. Establish `mem : ∀ x : LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T), ∃ c : Γ(T.left, ⊤), (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) = c • SecM.ofSec D.toPre.P.A (b' i0)`. Introduce `x`. Establish `hx : (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) ∈ Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec D.toPre.P.A (b' i) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T))` using `by rw [hspan]; trivial`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Use `⟨c i0, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Finset.sum_eq_single i0 (fun i _ hi => absurd (Subsingleton.elim i i0) hi) (fun h => absurd (Finset.mem_univ i0) h)]`. Take `⟨ut, hut⟩` from `sec_transport hL (sameSum_famφB0 D) t`. Take `⟨us, hus⟩` from `sec_transport hL (sameSum_famφB0 D) s'`.

Use `set π₂ := (snd T D.toPre.P.A).left with hπ₂`. Establish `: IsIso T.hom` using `by rw [hT]; infer_instance`. Establish `hiso : IsIso π₂` using `by show IsIso (pullback.snd T.hom D.toPre.P.A.hom) infer_instance`. Set `pl : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ))) → LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T)` to `fun u => pullSec' D.toPre.P.L _ _ u π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm)`. Take `⟨c0, hc0⟩` from `mem (pl ut)`.

Take `⟨c1, hc1⟩` from `mem (pl us)`. Establish `hrel : c0 • (SecM.ofSec D.toPre.P.A (pl us) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) = c1 • SecM.ofSec D.toPre.P.A (pl ut)`. Rewrite using `[hc0, hc1, smul_smul, smul_smul, mul_comm]`. Establish `hfstp : (fst T D.toPre.P.A).left = π₂ ≫ D.toPre.P.A.hom`. Establish `h1 : (fst T D.toPre.P.A).left ≫ T.hom = (T ⊗ D.toPre.P.A).hom` using `Over.w _`.

Establish `h2 : π₂ ≫ D.toPre.P.A.hom = (T ⊗ D.toPre.P.A).hom` using `Over.w _`. Rewrite `h1` using `[hT, Category.comp_id]`. Rewrite using `[h1, h2]`. Establish `eR' : ∀ c : Γ(T.left, ⊤), (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) = c` using `fun c => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl`. Establish `hlift : ∀ (W : (T ⊗ D.toPre.P.A).left.Opens) (c : Γ(T.left, ⊤)), liftHom D.toPre.P.A W c = toW ((fst T D.toPre.P.A).left) W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c)`.

Introduce `W c`. Simplify using `only [liftHom, toW, RingHom.comp_apply]`. Rewrite using `[eR']`. Both sides reduce to the same expression. Establish `key : ∀ (u₁ u₂ : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)))) (c c' : Γ(T.left, ⊤)), c • (SecM.ofSec D.toPre.P.A (pl u₁) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) = c' • SecM.ofSec D.toPre.P.A (pl u₂) → ∀ j : Fin 1 → D.toPr …`.

Introduce `u₁ u₂ c c' h j`. Establish `hj` using `congrArg (fun z => z.1 j) h`. Express the relevant statement in the definitionally equal form `liftHom _ _ c * (pl u₁).f j = liftHom _ _ c' * (pl u₂).f j at hj`. Rewrite `hj` using `[hlift, hlift]`. Simplify using `only [pl] at hj`.

Rewrite `hj` using `[pullSec'_f, pullSec'_f, toW_congr hfstp, toW_congr hfstp]`. Apply `Scheme.Hom.app_injective π₂` to reduce the goal to its premises. Apply `map_inj_of_le_ge (wchart_le_preimage D.toPre.P.L π₂ (fun _ => 𝟙 _) (fun _ => π₂) (fun _ => (Category.comp_id _).symm) j) (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k)` to reduce the goal to its premises. Use `erw [map_mul, map_mul, app_toW, map_mul, map_mul, app_toW, toW_res, toW_res]`. Conclude with `hj`.

Establish `e1` using `key us ut c0 c1 hrel`. Establish `hsc` using `secCorr_scal hL _ _ _ _ hus hut (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0)) (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1)) (fun j' => by`. Rewrite using `[resTop_scal, resTop_scal]`. Conclude with `e1 j')`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1, fun j => by rw [← resTop_scal, ← resTop_scal]; exact hsc j, fun h0 => ?_⟩` and prove the remaining obligations.

Establish `hc00 : c0 = 0` using `by rw [← eR' c0, h0, map_zero]`. Establish `hut0 : ∀ j : Fin 1 → D.toPre.P.L.ι, ut.f j = 0`. Establish `h` using `key ut ut 1 0 (by rw [one_smul, zero_smul, hc0, hc00, zero_smul])`. Introduce `j`. Establish `hj` using `h j`.

Rewrite `hj` using `[map_one, map_zero, map_one, map_zero, _root_.one_mul, zero_mul]`. Conclude with `hj`. Establish `ht` using `secCorr_scal hL _ _ _ _ hut hut 1 0 (fun j' => by rw [hut0 j', mul_zero, mul_zero])`. Introduce `j`. Establish `hj` using `ht j`.

Simplify using `only [resTop, map_one, map_zero, _root_.one_mul, zero_mul] at hj`. Conclude with `hj`.
-/
theorem secB_rank_one (hLaws : Laws) (t s' : D.toPre.SecB 1 0) :
    ∃ c₀ c' : R, (∀ j, toW D.toPre.P.A.hom _ c₀ * s'.f j = toW D.toPre.P.A.hom _ c' * t.f j) ∧
      (c₀ = 0 → ∀ j, t.f j = 0) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨V, hpV, b, hb⟩ := hLaws.secBaseChange (Spec (CommRingCat.of R)) D.toPre.P 1 le_rfl
    (IsLocalRing.closedPoint R)
  have hV : V = ⊤ := eq_top_of_closedPoint_mem V hpV
  let t0 : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) V).left :=
    IsOpenImmersion.lift V.ι (𝟙 _) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [hV]; trivial)
  have ht0 : t0 ≫ V.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  set T := baseAt t0 with hTdef
  have hT : T.hom = 𝟙 _ := by
    show t0 ≫ V.ι ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ht0]
  let b' : Fin (1 ^ D.toPre.P.g) → LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun i =>
    pullSec' D.toPre.P.L _ _ (b i) (homAt t0 ▷ D.toPre.P.A).left (fun _ => (snd T D.toPre.P.A).left)
      (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  have hpull : ∀ i, IsPullSec D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) (homAt t0 ▷ D.toPre.P.A)
      (whiskerRight_snd (homAt t0) D.toPre.P.A) (b i) (b' i) := fun i j => pullSec'_f _ _ _ _ _ _ _ j
  obtain ⟨-, hspan⟩ := hb R t0 b' hpull
  have hsub : Subsingleton (Fin (1 ^ D.toPre.P.g)) := by rw [one_pow]; infer_instance
  have i0 : Fin (1 ^ D.toPre.P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have mem : ∀ x : LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T), ∃ c : Γ(T.left, ⊤),
      (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c • SecM.ofSec D.toPre.P.A (b' i0) := by
    intro x
    have hx : (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) ∈
        Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec D.toPre.P.A (b' i) :
          SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine ⟨c i0, ?_⟩
    rw [← hc, Finset.sum_eq_single i0 (fun i _ hi => absurd (Subsingleton.elim i i0) hi)
      (fun h => absurd (Finset.mem_univ i0) h)]
  obtain ⟨ut, hut⟩ := sec_transport hL (sameSum_famφB0 D) t
  obtain ⟨us, hus⟩ := sec_transport hL (sameSum_famφB0 D) s'
  set π₂ := (snd T D.toPre.P.A).left with hπ₂
  have : IsIso T.hom := by rw [hT]; infer_instance
  have hiso : IsIso π₂ := by
    show IsIso (pullback.snd T.hom D.toPre.P.A.hom)
    infer_instance
  let pl : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ))) →
      LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun u =>
    pullSec' D.toPre.P.L _ _ u π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm)
  obtain ⟨c0, hc0⟩ := mem (pl ut)
  obtain ⟨c1, hc1⟩ := mem (pl us)
  have hrel : c0 • (SecM.ofSec D.toPre.P.A (pl us) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
      c1 • SecM.ofSec D.toPre.P.A (pl ut) := by
    rw [hc0, hc1, smul_smul, smul_smul, mul_comm]
  have hfstp : (fst T D.toPre.P.A).left = π₂ ≫ D.toPre.P.A.hom := by
    have h1 : (fst T D.toPre.P.A).left ≫ T.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    have h2 : π₂ ≫ D.toPre.P.A.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    rw [hT, Category.comp_id] at h1
    rw [h1, h2]
  have eR' : ∀ c : Γ(T.left, ⊤), (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) = c :=
    fun c => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hlift : ∀ (W : (T ⊗ D.toPre.P.A).left.Opens) (c : Γ(T.left, ⊤)), liftHom D.toPre.P.A W c =
      toW ((fst T D.toPre.P.A).left) W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
    intro W c
    simp only [liftHom, toW, RingHom.comp_apply]
    rw [eR']
    rfl
  have key : ∀ (u₁ u₂ : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left)
      (fun _ => ((1 : ℕ) : ℤ)))) (c c' : Γ(T.left, ⊤)),
      c • (SecM.ofSec D.toPre.P.A (pl u₁) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c' • SecM.ofSec D.toPre.P.A (pl u₂) →
      ∀ j : Fin 1 → D.toPre.P.L.ι, toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) * u₁.f j =
        toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c') * u₂.f j := by
    intro u₁ u₂ c c' h j
    have hj := congrArg (fun z => z.1 j) h
    change liftHom _ _ c * (pl u₁).f j = liftHom _ _ c' * (pl u₂).f j at hj
    rw [hlift, hlift] at hj
    simp only [pl] at hj
    rw [pullSec'_f, pullSec'_f, toW_congr hfstp, toW_congr hfstp] at hj
    apply Scheme.Hom.app_injective π₂
    apply map_inj_of_le_ge (wchart_le_preimage D.toPre.P.L π₂ (fun _ => 𝟙 _) (fun _ => π₂)
      (fun _ => (Category.comp_id _).symm) j) (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k)
    erw [map_mul, map_mul, app_toW, map_mul, map_mul, app_toW, toW_res, toW_res]
    exact hj
  have e1 := key us ut c0 c1 hrel
  have hsc := secCorr_scal hL _ _ _ _ hus hut (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0))
    (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1)) (fun j' => by
      rw [resTop_scal, resTop_scal]; exact e1 j')
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1,
    fun j => by rw [← resTop_scal, ← resTop_scal]; exact hsc j, fun h0 => ?_⟩
  have hc00 : c0 = 0 := by rw [← eR' c0, h0, map_zero]
  have hut0 : ∀ j : Fin 1 → D.toPre.P.L.ι, ut.f j = 0 := by
    have h := key ut ut 1 0 (by rw [one_smul, zero_smul, hc0, hc00, zero_smul])
    intro j
    have hj := h j
    rw [map_one, map_zero, map_one, map_zero, _root_.one_mul, zero_mul] at hj
    exact hj
  have ht := secCorr_scal hL _ _ _ _ hut hut 1 0 (fun j' => by rw [hut0 j', mul_zero, mul_zero])
  intro j
  have hj := ht j
  simp only [resTop, map_one, map_zero, _root_.one_mul, zero_mul] at hj
  exact hj

end Rank

end ReciprocityTheory.ChartRestriction.G.DVR.TG
