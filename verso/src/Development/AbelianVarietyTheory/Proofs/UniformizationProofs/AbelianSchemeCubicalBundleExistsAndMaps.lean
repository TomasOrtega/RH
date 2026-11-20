import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AbPackage

/- English proof (translation)
Take `⟨t, -, hv⟩` from `exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)` and prove the remaining obligations. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])`. Use the proof step `(LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))`. Establish `le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`.

Use `⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val u r z J * (val u' r z J)⁻¹` using `(gm_res r z le trivial _).trans ((val_of t r z J PEmpty.elim (fun k => k.elim)).symm.trans ((hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_inv _ _)))))`. Conclude with `(inv_mul_cancel_right _ _).symm.trans (congrArg (· * val u' r z J) e.symm)`.
-/
theorem exists_unit_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val u r z J * (val u' r z J)⁻¹ :=
    (gm_res r z le trivial _).trans ((val_of t r z J PEmpty.elim (fun k => k.elim)).symm.trans
      ((hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_inv _ _)))))
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * val u' r z J) e.symm)

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

omit [IsCommMonObj B] in

/- English proof (translation)
Establish `he : eSec B ≫ (ι[B]).left = eSec B` using `congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)`. Set `n : B.left ⟶ B.left` to `(toUnit B).left ≫ eSec B`. Establish `hn : eSec B ≫ n = eSec B`. Rewrite using `[← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]`. Take `⟨u, hu, hv⟩` from `exists_gen hL (K' := Fin 2) (φ' := ![(ι[B]).left, 𝟙 _]) (ε' := ![1, -1]) (fun V _ k => by`.

Establish `e : n ≫ (ι[B]).left = n` using `by rw [Category.assoc, he]`. Simplify using `[Fintype.prod_sum_type, Fin.prod_univ_succ, e])`. Use the proof step `(LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))`. Use `⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩` and prove the remaining obligations.

Rewrite using `[val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel, val_one]`.
-/
theorem exists_rigidified_sym {L : LB B.left} (hL : L.IsLB)
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec B)) (LB.oneGen L) := by
  have he : eSec B ≫ (ι[B]).left = eSec B :=
    congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)
  let n : B.left ⟶ B.left := (toUnit B).left ≫ eSec B
  have hn : eSec B ≫ n = eSec B := by
    rw [← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from
      congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(ι[B]).left, 𝟙 _]) (ε' := ![1, -1])
    (fun V _ k => by
      have e : n ≫ (ι[B]).left = n := by rw [Category.assoc, he]
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, e])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel, val_one]

/- English proof (translation)
Take `⟨t, ht⟩` from `h₁`. Take `⟨s, hs⟩` from `h₂`. Take `⟨t', ht', hn⟩` from `GlobalTheory.AbLaw.Cube.exists_normalised L.isLB t ht`. Take `⟨u, hu, hr⟩` from `exists_rigidified_sym L.isLB s hs`. Conclude with `⟨CP.ofSurjective (surjective_cube hG hB) L (GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB L t' ht' hn) u hu hr, rfl⟩`.
-/
theorem exists_cp (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (L : RigLB B)
    (h₁ : ∃ t : LB.Gen (Theta B L.L), t.IsGen)
    (h₂ : ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) :
    ∃ M : CP B, M.L = L := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised L.isLB t ht
  obtain ⟨u, hu, hr⟩ := exists_rigidified_sym L.isLB s hs
  exact ⟨CP.ofSurjective (surjective_cube hG hB) L (GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB L t' ht' hn) u hu hr, rfl⟩

/- English proof (translation)
Take `⟨rig, hr, c, s, hs, h₂, h₃, H⟩` from `exists_isCPMap M mul M'.L.L M'.L.isLB w hg`. Set `N : CP B'` to `⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩`. Take `⟨a, ha⟩` from `exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) hr M'.L.rigGen`. Set `b : Γ(B'.left, ⊤)ˣ` to `pullU B'.hom ⊤ a`. Establish `es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J` using `gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm`.

Establish `ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B', cubV c z J x y u = cubV M'.c z J x y u` using `fun T z J hJ x y u => gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ …`. Use `⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩` and prove the remaining obligations. Take `⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ B') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x = gw w x.left z (J (x.left ≫ β)) (J' x.left)` from `⟨_, fun _ => rfl⟩`. Take `⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y` from `T.left) T.hom z ⊤ a := ⟨_, rfl⟩`. Establish `e : ∀ x, W x = α * W₀ x` using `fun x => by`.

Establish `hm : x.left z ∈ (M.L.L.pull β).U (fun _ => J (x.left ≫ β)) ⊓ M'.L.L.U (J' x.left)` using `⟨mem_pull.2 (hJ (x.left ≫ β)), hJ' x.left⟩`. Rewrite using `[hW, hW₀, hα, ← Over.w x]`. Conclude with `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans (gm_pull x.left B'.hom z ⊤ trivial a)) rfl)`. Take `⟨a₁, a₂, a₃⟩` from `H.vals T z J' J hJ' hJ W₀ hW₀`. Use `⟨?_, fun x => ?_, fun x y u => ?_⟩` and prove the remaining obligations.

Use `a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)` and prove the remaining obligations. Rewrite using `[e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]`. Establish `q : val M.sym (x.left ≫ β) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J'` using `(a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))`. Rewrite using `[e, e, mul_left_comm, q, _root_.mul_assoc]`. Establish `q` using `(a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))`.

Simplify using `only [e]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `q'` using `congrArg Additive.ofMul q`. Simplify using `only [ofMul_mul] at q' ⊢`. Take the linear combination `(norm := abel) q'`.
-/
theorem exists_isCPMap_of_iso (hG : GlobalFnsSt) {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B']
    [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B') {β : B'.left ⟶ B.left}
    {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen) : ∃ v, IsCPMap M' M f β hw v := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) hr M'.L.rigGen
  let b : Γ(B'.left, ⊤)ˣ := pullU B'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ B') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ β)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull β).U (fun _ => J (x.left ≫ β)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ β)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left B'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ β) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

/- English proof (translation)
Introduce `hG S B _ _ hB`. Use `⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩` and prove the remaining obligations. Conclude with `exists_isCPMap_of_iso hG hB' M M' (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg`.
-/
theorem abelian_cp : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  intro hG S B _ _ hB
  refine ⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩
  exact exists_isCPMap_of_iso hG hB' M M'
    (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg

end GlobalTheory.AbPackage
