import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

/- English proof (translation)
Establish `glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j)ˣ, ∀ a y, y ∈ LB.wchart L φ j → y ∈ V a → gm (𝟙 Y) y _ s = trF φ ε (𝟙 Y) y j (J a)`. Introduce `j`. Establish `le : ∀ a, LB.wchart L φ j ⊓ V a ≤ LB.wchart L φ j ⊓ LB.wchart L φ (J a)` using `fun a => inf_le_inf_left _ (hV a)`. Establish `hu : ∀ a y, y ∈ LB.wchart L φ j ⊓ V a → gm (𝟙 Y) y _ (res (le a) ((LB.LinComb L φ ε).g j (J a))) = trF φ ε (𝟙 Y) y j (J a)` using `fun a y hy => (gm_res (𝟙 Y) y (le a) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j (J a) hy.1 (hV a hy.2))`. Take `⟨s, hs⟩` from `glue_unit (LB.wchart L φ j) (fun a => LB.wchart L φ j ⊓ V a) (fun _ => inf_le_left) (fun y hy => by`.

Take `⟨a, ha⟩` from `hc y`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)`. Use the proof step `(fun a => res (le a) ((LB.LinComb L φ ε).g j (J a))) (fun a b y hy => by`. Use `(hu a y hy.1).trans (Eq.trans ?_ (hu b y hy.2).symm)` and prove the remaining obligations. Rewrite using `[← trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hV a hy.1.2) (hV b hy.2.2), h1 a b y hy.1.2 hy.2.2, _root_.mul_one])`.

Use `⟨s, fun a y h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j ⊓ V a` using `⟨h₁, h₂⟩`. Conclude with `(gm_res (𝟙 Y) y inf_le_left hm s).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs a)).trans (hu a y hm))`. Use `choose s hs using glue`. Use `⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hc y`. Use `((gm_res (𝟙 Y) y _ hy _).trans (hs j a y hy.1 ha)).trans (Eq.symm ?_)` and prove the remaining obligations. Use `(map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (hs j' a y hy.2 ha))).trans ?_)` and prove the remaining obligations. Conclude with `trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hV a ha)`.
-/
theorem gen_of_cover {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} (V : A → Y.Opens) (J : A → K → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ LB.wchart L φ (J a))
    (h1 : ∀ a b y, y ∈ V a → y ∈ V b → trF φ ε (𝟙 Y) y (J a) (J b) = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j)ˣ, ∀ a y, y ∈ LB.wchart L φ j → y ∈ V a →
      gm (𝟙 Y) y _ s = trF φ ε (𝟙 Y) y j (J a) := by
    intro j
    have le : ∀ a, LB.wchart L φ j ⊓ V a ≤ LB.wchart L φ j ⊓ LB.wchart L φ (J a) :=
      fun a => inf_le_inf_left _ (hV a)
    have hu : ∀ a y, y ∈ LB.wchart L φ j ⊓ V a →
        gm (𝟙 Y) y _ (res (le a) ((LB.LinComb L φ ε).g j (J a))) = trF φ ε (𝟙 Y) y j (J a) := fun a y hy =>
      (gm_res (𝟙 Y) y (le a) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j (J a) hy.1 (hV a hy.2))
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ j) (fun a => LB.wchart L φ j ⊓ V a) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨a, ha⟩ := hc y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)
      (fun a => res (le a) ((LB.LinComb L φ ε).g j (J a))) (fun a b y hy => by
        refine (hu a y hy.1).trans (Eq.trans ?_ (hu b y hy.2).symm)
        rw [← trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hV a hy.1.2) (hV b hy.2.2), h1 a b y hy.1.2 hy.2.2, _root_.mul_one])
    refine ⟨s, fun a y h₁ h₂ => ?_⟩
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j ⊓ V a := ⟨h₁, h₂⟩
    exact (gm_res (𝟙 Y) y inf_le_left hm s).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs a)).trans (hu a y hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  refine ((gm_res (𝟙 Y) y _ hy _).trans (hs j a y hy.1 ha)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (hs j' a y hy.2 ha))).trans ?_)
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hV a ha)

def Fix {X : Scheme.{0}} (φ : X ⟶ X) (U : X.Opens) (f : Γ(X, U)) (n : ℕ) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

/- English proof (translation)
Use `⟨rfl, ?_⟩` and prove the remaining obligations. Simplify using `[Scheme.Hom.appLE]`. Conclude with `rs_self (X := X) le_rfl f`.
-/
theorem Fix.id {X : Scheme.{0}} (U : X.Opens) (f : Γ(X, U)) : Fix (𝟙 X) U f 1 := by
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.appLE]
  exact rs_self (X := X) le_rfl f

/- English proof (translation)
Take `⟨e, h⟩` from `h`. Take `⟨e', h'⟩` from `h'`. Use `⟨by rw [Scheme.Hom.comp_preimage, ← e', ← e], ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.appLE_comp_appLE φ ψ U U U e'.le e.le, CommRingCat.hom_comp, RingHom.comp_apply, h', map_pow, h, pow_mul]`.
-/
theorem Fix.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)} {a b : ℕ}
    (h : Fix φ U f a) (h' : Fix ψ U f b) : Fix (φ ≫ ψ) U f (a * b) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨e', h'⟩ := h'
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e', ← e], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e'.le e.le, CommRingCat.hom_comp, RingHom.comp_apply, h', map_pow, h,
    pow_mul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => exact Fix.id U f`. Consider the case `succ l ih`. Rewrite using `[mul_add, Nat.mul_one, pow_add, pow_add, mul_comm (q ^ _)]`. Conclude with `h.comp ih`.
-/
theorem Fix.pow {S : Scheme.{0}} {G : Over S} {F : End G} {U : G.left.Opens} {f : Γ(G.left, U)} {q m : ℕ}
    (h : Fix (show G ⟶ G from F ^ m).left U f (q ^ m)) (l : ℕ) :
    Fix (show G ⟶ G from F ^ (m * l)).left U f (q ^ (m * l)) := by
  induction l with
  | zero => exact Fix.id U f
  | succ l ih =>
    rw [mul_add, Nat.mul_one, pow_add, pow_add, mul_comm (q ^ _)]
    exact h.comp ih

/- English proof (translation)
Take `⟨e, h⟩` from `h`. Establish `hx' : φ x ∈ U` using `e.le hx`. Establish `h2 : res e.le (pullU φ U f) = f ^ n` using `Units.ext h`. Rewrite using `[← map_pow, ← h2, gm_res (𝟙 X) x e.le hx, gm_pull (𝟙 X) φ x U hx', Category.id_comp]`.
-/
theorem Fix.gm {X : Scheme.{0}} {φ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {n : ℕ} (h : Fix φ U f.val n)
    (x : X) (hx : x ∈ U) : gm φ x U f = gm (𝟙 X) x U f ^ n := by
  obtain ⟨e, h⟩ := h
  have hx' : φ x ∈ U := e.le hx
  have h2 : res e.le (pullU φ U f) = f ^ n := Units.ext h
  rw [← map_pow, ← h2, gm_res (𝟙 X) x e.le hx, gm_pull (𝟙 X) φ x U hx', Category.id_comp]

/- English proof (translation)
Use `gen_of_cover hL _ _ V (fun a _ => c a) hc (fun a y hy => Set.mem_iInter.2 fun k => ?_) fun a b y ha hb => ?_` and prove the remaining obligations. Use `fin_cases k`. Conclude with `hV a ((h a a).1.le ⟨hy, hy⟩).1`. Conclude with `hV a hy`. Establish `hm : y ∈ V a ⊓ V b` using `⟨ha, hb⟩`.

Establish `e` using `(h a b).gm y hm`. Establish `hm' : φ y ∈ V a ⊓ V b` using `(show V a ⊓ V b ≤ φ ⁻¹ᵁ (V a ⊓ V b) from (h a b).1.le) hm`. Rewrite `e` using `[gm_res φ y _ hm', gm_res (𝟙 X) y _ hm]`. Simplify using `only [trF, Fin.prod_univ_two, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, e]`. Simplify using the standard rewrite rules.
-/
theorem pullPow_of_fix {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : X ⟶ X) (n : ℕ)
    {A : Type} (V : A → X.Opens) (c : A → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ L.U (c a))
    (h : ∀ a b, Fix φ (V a ⊓ V b) (res (inf_le_inf (hV a) (hV b)) (L.g (c a) (c b))).val n) :
    PullPow φ L n := by
  refine gen_of_cover hL _ _ V (fun a _ => c a) hc (fun a y hy => Set.mem_iInter.2 fun k => ?_) fun a b y ha hb => ?_
  · fin_cases k
    · exact hV a ((h a a).1.le ⟨hy, hy⟩).1
    · exact hV a hy
  · have hm : y ∈ V a ⊓ V b := ⟨ha, hb⟩
    have e := (h a b).gm y hm
    have hm' : φ y ∈ V a ⊓ V b := (show V a ⊓ V b ≤ φ ⁻¹ᵁ (V a ⊓ V b) from (h a b).1.le) hm
    rw [gm_res φ y _ hm', gm_res (𝟙 X) y _ hm] at e
    simp only [trF, Fin.prod_univ_two, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, e]
    simp

/- English proof (translation)
Introduce `k _ G _ hG F q hF L hL`. Take `⟨-, -, hsep, hqc, -⟩` from `hG`. Establish `: CompactSpace G.left` using `QuasiCompact.compactSpace_of_compactSpace G.hom`. Establish `: G.left.IsSeparated` using `⟨by`. Rewrite using `[← terminal.comp_from G.hom]`.

Use the proof step `infer_instance⟩`. Establish `hx : ∀ x : G.left, ∃ (V : G.left.Opens) (i : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U i` using `fun x => by`. Take `⟨i, hi⟩` from `exists_chart hL x`. Take `⟨_, ⟨V, hV, rfl⟩, h₁, h₂⟩` from `G.left.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen`. Conclude with `⟨V, i, hV, h₁, h₂⟩`.

Use `choose V c hA hxV hV using hx`. Take `⟨s, hs⟩` from `isCompact_univ.elim_finite_subcover (fun x => (V x : Set G.left)) (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)`. Use `choose m hm hfix using fun p : s × s => hF.2 (V p.1 ⊓ V p.2) ((hA p.1).inf (hA p.2)) (res (inf_le_inf (hV p.1) (hV p.2)) (L.g (c p.1) (c p.2))).val`. Use `⟨∏ p, m p, Finset.one_le_prod' fun p _ => hm p, fun l => ?_⟩` and prove the remaining obligations. Use `pullPow_of_fix hL (show G ⟶ G from F ^ ((∏ p, m p) * l)).left (q ^ ((∏ p, m p) * l)) (fun a : s => V a) (fun a => c a) (fun y => by` as an intermediate fact.

Take `⟨a, ha, hy⟩` from `Set.mem_iUnion₂.1 (hs (Set.mem_univ y))`. Conclude with `⟨⟨a, ha⟩, hy⟩) (fun a => hV a) (fun a b => by`. Take `⟨r, hr⟩` from `Finset.dvd_prod_of_mem m (Finset.mem_univ (a, b))`. Rewrite using `[hr, Nat.mul_assoc]`. Conclude with `Fix.pow (hfix (a, b)) _)`.

Conclude with `this` after adjusting the coercions.
-/
theorem frob_pullPow : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → ∀ L : LB G.left, L.IsLB → ∃ m, 1 ≤ m ∧ ∀ l, PullPow (show G ⟶ G from F ^ (m * l)).left L ((q : ℤ) ^ (m * l)) := by
  intro k _ G _ hG F q hF L hL
  classical
  obtain ⟨-, -, hsep, hqc, -⟩ := hG
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hx : ∀ x : G.left, ∃ (V : G.left.Opens) (i : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, h₁, h₂⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    exact ⟨V, i, hV, h₁, h₂⟩
  choose V c hA hxV hV using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set G.left)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  choose m hm hfix using fun p : s × s => hF.2 (V p.1 ⊓ V p.2) ((hA p.1).inf (hA p.2))
    (res (inf_le_inf (hV p.1) (hV p.2)) (L.g (c p.1) (c p.2))).val
  refine ⟨∏ p, m p, Finset.one_le_prod' fun p _ => hm p, fun l => ?_⟩
  have := pullPow_of_fix hL (show G ⟶ G from F ^ ((∏ p, m p) * l)).left (q ^ ((∏ p, m p) * l))
    (fun a : s => V a) (fun a => c a) (fun y => by
      obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact ⟨⟨a, ha⟩, hy⟩) (fun a => hV a) (fun a b => by
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (a, b))
      rw [hr, Nat.mul_assoc]
      exact Fix.pow (hfix (a, b)) _)
  exact_mod_cast this

end GlobalTheory.SS.FrobLB
end
