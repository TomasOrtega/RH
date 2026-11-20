import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.LocSecOfImm

/- English proof (translation)
Take `rfl : V = q ⁻¹ᵁ U` from `le_antisymm h h'`. Use `q.isIso_app U hU` as an intermediate fact. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Conclude with `ConcreteCategory.bijective_of_isIso (q.app U)`.
-/
theorem bij_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) [IsOpenImmersion q] (U : Y.Opens) (hU : U ≤ q.opensRange)
    (V : X.Opens) (h : V ≤ q ⁻¹ᵁ U) (h' : q ⁻¹ᵁ U ≤ V) : Function.Bijective (q.appLE U V h).hom := by
  obtain rfl : V = q ⁻¹ᵁ U := le_antisymm h h'
  have := q.isIso_app U hU
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (q.app U)

/- English proof (translation)
The claim follows from `congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)`.
-/
theorem appLE_res {X Y : Scheme.{0}} (q : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (e' : V ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : (q.appLE U' V e).hom (resG Y h a) = (q.appLE U V e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)

/- English proof (translation)
The claim follows from `congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)`.
-/
theorem res_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V' ≤ V) (e : V ≤ q ⁻¹ᵁ U)
    (e' : V' ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : resG X h ((q.appLE U V e).hom a) = (q.appLE U V' e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)

/- English proof (translation)
Substitute `hr` using the available equality. Conclude with `congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)`.
-/
theorem appLE_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hr : p ≫ q = r) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ p ⁻¹ᵁ V) (e₃ : W ≤ r ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (p.appLE V W e₂).hom ((q.appLE U V e₁).hom a) = (r.appLE U W e₃).hom a := by
  subst hr
  exact congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)

/- English proof (translation)
Establish `h : ⊤ ≤ x ⁻¹ᵁ U` using `hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))`. Establish `e1` using `Scheme.basicOpen_appLE x ⊤ U h a`. Rewrite `e1` using `[top_inf_eq]`. Establish `e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a`. Rewrite using `[valF, dif_pos h]`.

Conclude with `(Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _`. Establish `e3 : x ⁻¹ᵁ X.basicOpen a = (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a))`. Rewrite using `[e2]`. Conclude with `e1.symm`. Introduce `h0`.

Rewrite `hle` using `[e3, h0, map_zero, Scheme.basicOpen_zero]`. Conclude with `hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)`.
-/
theorem valF_ne_zero_of_le {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (a : Γ(X, U))
    (hle : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a) : valF x U a ≠ 0 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  intro h0
  rw [e3, h0, map_zero, Scheme.basicOpen_zero] at hle
  exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

/- English proof (translation)
Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx`. Use `LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)` as an intermediate fact. Take `⟨c, hcO, hc'⟩` from `nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _)) ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed`. Establish `hc : IsClosed {c}` using `hc'`. Use `⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]`. Use `show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O`. Rewrite using `[pointOfClosedPoint_apply]`. Conclude with `hcO`.
-/
theorem exists_point {X Y : Scheme.{0}} {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

/- English proof (translation)
Introduce `S G _ L R _ χ _ σ hft hnz`. Set `q : (Over.mk χ ⊗ G).left ⟶ G.left` to `(snd (Over.mk χ) G).left`. Establish `hq : IsOpenImmersion q` using `inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))`. Establish `ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ` using `(Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm`. Establish `hN : ∀ y, G.hom (q y) ∈ χ.opensRange` using `fun y => by`.

Rewrite using `[← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Establish `hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange` using `fun y hy => (Scheme.Pullback.range_snd χ G.hom).ge hy`. Establish `hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤ q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange)` using `fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩`. Establish `hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange) ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom` using `fun i => bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1`.

Use `choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)`. Establish `hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j` using `fun j => by`. Take `⟨i, rfl⟩ : ∃ i, j = fun _ => i` from `⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩`. Conclude with `hs i`. Use `⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩` and prove the remaining obligations.

Establish `hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤ q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange)` using `fun y hy => ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩`. Use `(bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy => ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_` and prove the remaining obligations. Establish `hc` using `σ.compat (fun _ => i) (fun _ => j)`. Rewrite `hc` using `[← hs i, ← hs j]`. Rewrite using `[map_mul]`.

Use `(appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))` and prove the remaining obligations. Use `Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm` and prove the remaining obligations. Simplify using `only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]`. Both sides reduce to the same expression. Conclude with `(res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm`.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Use `show genPull _ s j = (SecAt.pull G L σ i).f j`. Unfold `genPull SecAt.pull VVRank.pullS VVRank.pullTo`. Simplify using `only`.

Rewrite using `[← hs' j]`. Conclude with `(appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm`. Take `⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange` from `hx ⟨_, rfl⟩`. Take `⟨z, hz, hz'⟩` from `hnz s₀`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz'`.

Rewrite `hj` using `[← hs' j]`. Establish `hb` using `((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2`. Take `⟨y, hy, hy'⟩` from `exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by`. Rewrite using `[← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]`. Conclude with `hs₀)`.

Use `⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))`.
-/
theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  intro S G _ L R _ χ _ σ hft hnz
  let q : (Over.mk χ ⊗ G).left ⟶ G.left := (snd (Over.mk χ) G).left
  have hq : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))
  have ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ :=
    (Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm
  have hN : ∀ y, G.hom (q y) ∈ χ.opensRange := fun y => by
    rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange := fun y hy =>
    (Scheme.Pullback.range_snd χ G.hom).ge hy
  have hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤
      q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩
  have hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange)
      ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom := fun i =>
    bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1
  choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)
  have hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact hs i
  refine ⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩
  · have hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤
        q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun y hy =>
      ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩
    refine (bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy =>
      ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_
    have hc := σ.compat (fun _ => i) (fun _ => j)
    rw [← hs i, ← hs j] at hc
    rw [map_mul]
    refine (appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans
      (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm
      simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    · exact (res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm
  · rintro _ ⟨y, rfl⟩
    exact ⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · show genPull _ s j = (SecAt.pull G L σ i).f j
    unfold genPull SecAt.pull VVRank.pullS VVRank.pullTo
    dsimp only
    rw [← hs' j]
    exact (appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm
  · obtain ⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange := hx ⟨_, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hnz s₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    rw [← hs' j] at hj
    have hb := ((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2
    obtain ⟨y, hy, hy'⟩ := exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by
      rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]
      exact hs₀)
    refine ⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩
    rintro _ ⟨a, rfl⟩
    exact G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))

end GlobalTheory.UMin.LocSecOfImm
