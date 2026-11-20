import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Primitive

open GlobalTheory.KuennethOne

variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}

/- English proof (translation)
Rewrite using `[rsT, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem rsT_eq_rs {O₀ O : A.Opens} (s : Γ(A, O₀)) (h : O ≤ O₀) : rsT s O = rs h s := by
  rw [rsT, dif_pos h]
  rfl

/- English proof (translation)
Unfold `pbT`. Conclude with `dif_pos h`.
-/
theorem pbT_eq (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀) :
    pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  exact dif_pos h

/- English proof (translation)
Rewrite using `[pbT_eq f s h, pbT_eq f s (h'.trans h)]`. Use `show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`.
-/
theorem rs_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀)
    (h' : O' ≤ O) : rs h' (pbT f s O) = pbT f s O' := by
  rw [pbT_eq f s h, pbT_eq f s (h'.trans h)]
  show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`.
-/
theorem app_pbT (r : T ⟶ Z) (f : Z ⟶ A) (g : T ⟶ A) (e : r ≫ f = g) {O₀ : A.Opens} (s : Γ(A, O₀))
    {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : (r.app O).hom (pbT f s O) = pbT g s (r ⁻¹ᵁ O) := by
  subst e
  rw [pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Introduce `_ hx` and use `⟨h hx, h' hx⟩`.
-/
theorem le_pre_inf (f : T ⟶ A) {N : T.Opens} {V W : A.Opens} (h : N ≤ f ⁻¹ᵁ V) (h' : N ≤ f ⁻¹ᵁ W) :
    N ≤ f ⁻¹ᵁ (V ⊓ W) :=
  fun _ hx => ⟨h hx, h' hx⟩

/- English proof (translation)
Simplify using `only [pbT_eq f _ hN, map_add]`.
-/
private lemma pbT_add' (f : T ⟶ A) {O₀ : A.Opens} (s s' : Γ(A, O₀)) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O₀) : pbT f (s + s') N = pbT f s N + pbT f s' N := by
  simp only [pbT_eq f _ hN, map_add]

/- English proof (translation)
Rewrite using `[rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]`. Use `show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
private lemma pbT_rsT' (f : T ⟶ A) {O₀ O : A.Opens} (s : Γ(A, O₀)) (hO : O ≤ O₀) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O) : pbT f (rsT s O) N = pbT f s N := by
  rw [rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]
  show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Establish `hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k)` using `le_pre_inf f (le_pre_inf f hi hj) hk`. Establish `l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j` using `inf_le_left`. Establish `l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k` using `le_inf (inf_le_left.trans inf_le_right) inf_le_right`. Establish `l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k` using `le_inf (inf_le_left.trans inf_le_left) inf_le_right`. Rewrite using `[← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN, ← pbT_add' f _ _ hN, hc i j k]`.
-/
theorem pbT_coc (hc : IsCoc U c) (f : T ⟶ A) (i j k : I) {N : T.Opens} (hi : N ≤ f ⁻¹ᵁ U i)
    (hj : N ≤ f ⁻¹ᵁ U j) (hk : N ≤ f ⁻¹ᵁ U k) :
    pbT f (c i j) N + pbT f (c j k) N = pbT f (c i k) N := by
  have hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := le_pre_inf f (le_pre_inf f hi hj) hk
  have l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN,
    ← pbT_add' f _ _ hN, hc i j k]

/- English proof (translation)
Use `⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩` and prove the remaining obligations. Introduce `a b M ha hb`. Establish `hg' : M ≤ g ⁻¹ᵁ U i₀` using `le_top.trans hg`. Establish `e1` using `pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))`. Establish `e2` using `pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))`.

Establish `e3` using `pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))`. Establish `e4` using `pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))`. Establish `e5` using `pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))`. Establish `r1` using `rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha`. Establish `r2` using `rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb`.

Establish `r3` using `rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha`. Establish `r4` using `rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb`. Simplify using `only [map_sub, r1, r2, r3, r4]`. Take the linear combination `e2 - e1 + e3 - e4 - e5`.
-/
theorem exists_split (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by
  refine ⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩
  intro a b M ha hb
  have hg' : M ≤ g ⁻¹ᵁ U i₀ := le_top.trans hg
  have e1 := pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))
  have e2 := pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))
  have e3 := pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))
  have e4 := pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))
  have e5 := pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))
  have r1 := rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha
  have r2 := rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb
  have r3 := rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha
  have r4 := rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb
  simp only [map_sub, r1, r2, r3, r4]
  linear_combination e2 - e1 + e3 - e4 - e5

/- English proof (translation)
Establish `cov : ∀ y : A, ∃ i, y ∈ U i` using `fun y => by`. Establish `hy : y ∈ (⨆ i, U i)` using `hU ▸ trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp hy`. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `cov (m x)`.

Take `⟨j, hj⟩` from `cov (p x)`. Take `⟨k, hk⟩` from `cov (q x)`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩`.
-/
theorem iSup_triple (hU : ⨆ i, U i = ⊤) (m p q : Z ⟶ A) :
    ⨆ α : I × I × I, m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2 = ⊤ := by
  have cov : ∀ y : A, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, hi⟩ := cov (m x)
  obtain ⟨j, hj⟩ := cov (p x)
  obtain ⟨k, hk⟩ := cov (q x)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩

/- English proof (translation)
Substitute `e` using the available equality. Introduce `x hx`. Use `show (s ≫ m) x ∈ O`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `h hx`.
-/
private lemma preimage_le_preimage_of_comp_eq {X₁ X₂ X₃ : Scheme.{0}} (s : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g : X₁ ⟶ X₃)
    (e : s ≫ m = g) {W : X₂.Opens} {O : X₃.Opens} (h : W ≤ m ⁻¹ᵁ O) : s ⁻¹ᵁ W ≤ g ⁻¹ᵁ O := by
  subst e
  intro x hx
  show (s ≫ m) x ∈ O
  rw [Scheme.Hom.comp_apply]
  exact h hx

/- English proof (translation)
The claim follows from `rs_pbT f s h h'`.
-/
private lemma presheaf_map_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) :
    (T.presheaf.map (homOfLE h').op).hom (pbT f s O) = pbT f s O' :=
  rs_pbT f s h h'

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hL _ _ K _ P₀ I U c hU hc`. Establish `: IsProper P₀.A.hom` using `P₀.isAb.proper`. Establish `hsub : Subsingleton (𝟙_ (Over (Sp K))).left` using `inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))`. Set `_ : Inhabited (𝟙_ (Over (Sp K))).left` to `inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))`. Establish `hbij : Function.Bijective P₀.A.hom.appTop.hom` using `hL.globalFns _ P₀.A P₀.isAb`.

Set `e : 𝟙_ (Over (Sp K)) ⟶ P₀.A` to `MonObj.one`. Set `g₀ : P₀.A.left ⟶ P₀.A.left` to `(toUnit P₀.A ≫ e).left`. Set `m` to `(fst P₀.A P₀.A * snd P₀.A P₀.A).left`. Set `p` to `(fst P₀.A P₀.A).left`. Set `q` to `(snd P₀.A P₀.A).left`.

Establish `hpt : ∀ x : P₀.A.left, g₀ x = e.left default`. Introduce `x`. Use `show ((toUnit P₀.A).left ≫ e.left) x = _`. Rewrite using `[Scheme.Hom.comp_apply]`. Use `congr 1`.

Conclude with `Subsingleton.elim _ _`. Establish `cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i` using `fun y => by`. Establish `hy : y ∈ (⨆ i, U i)` using `hU ▸ trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp hy`. Take `⟨i₀, hi₀⟩` from `cov (e.left default)`.

Establish `hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀` using `fun x _ => by show g₀ x ∈ U i₀`. Rewrite using `[hpt x]`. Conclude with `hi₀`. Establish `es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _`. Rewrite using `[← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]`.

Conclude with `congrArg Over.Hom.left (mul_one (𝟙 P₀.A))`. Establish `es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Establish `es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀`.

Rewrite using `[← Over.comp_left, lift_snd]`. Establish `et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _`. Rewrite using `[← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]`. Conclude with `congrArg Over.Hom.left (one_mul (𝟙 P₀.A))`. Establish `et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀`.

Rewrite using `[← Over.comp_left, lift_fst]`. Establish `et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _`. Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Set `V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens` to `fun α => m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2`.

Establish `hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1` using `fun α => inf_le_left.trans inf_le_left`. Establish `hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1` using `fun α => inf_le_left.trans inf_le_right`. Establish `hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2` using `fun α => inf_le_right`. Take `⟨ψ, hK⟩` from `kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q) (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) - pbT q (c a.2.2 b.2.2) (V a ⊓ V b)) (by`. Introduce `a b d`.

Establish `w1 : V a ⊓ V b ⊓ V d ≤ V a` using `inf_le_left.trans inf_le_left`. Establish `w2 : V a ⊓ V b ⊓ V d ≤ V b` using `inf_le_left.trans inf_le_right`. Establish `w3 : V a ⊓ V b ⊓ V d ≤ V d` using `inf_le_right`. Simplify using `only [map_sub]`. Rewrite using `[presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)) …`.

Establish `cm` using `pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))`. Establish `cp` using `pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))`. Establish `cq` using `pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))`. Take the linear combination `cm - cp - cq)`. Use the proof step `(by`.

Set `s` to `(lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left`. Take `⟨χ, hχ⟩` from `exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1) (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α)) (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q …`. Use `⟨χ, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))), app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) ( …`. Conclude with `hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))`.

Use the proof step `(by`. Set `s` to `(lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left`. Take `⟨χ, hχ⟩` from `exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2) (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α)) (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p …`. Use `⟨χ, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))), app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) ( …`.

Conclude with `hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))`. Unfold `IsCob`. Use `⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩` and prove the remaining obligations. Rewrite using `[rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]`. Conclude with `(neg_sub_neg _ _).symm`.
-/
private theorem cech_coboundary_mul_sub_fst_sub_snd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) := by
  intro hL _ _ K _ P₀ I U c hU hc
  have : IsProper P₀.A.hom := P₀.isAb.proper
  have hsub : Subsingleton (𝟙_ (Over (Sp K))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let _ : Inhabited (𝟙_ (Over (Sp K))).left := inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))
  have hbij : Function.Bijective P₀.A.hom.appTop.hom := hL.globalFns _ P₀.A P₀.isAb
  let e : 𝟙_ (Over (Sp K)) ⟶ P₀.A := MonObj.one
  let g₀ : P₀.A.left ⟶ P₀.A.left := (toUnit P₀.A ≫ e).left
  let m := (fst P₀.A P₀.A * snd P₀.A P₀.A).left
  let p := (fst P₀.A P₀.A).left
  let q := (snd P₀.A P₀.A).left

  have hpt : ∀ x : P₀.A.left, g₀ x = e.left default := by
    intro x
    show ((toUnit P₀.A).left ≫ e.left) x = _
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨i₀, hi₀⟩ := cov (e.left default)
  have hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀ := fun x _ => by
    show g₀ x ∈ U i₀
    rw [hpt x]
    exact hi₀

  have es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (mul_one (𝟙 P₀.A))
  have es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀ := by
    rw [← Over.comp_left, lift_snd]
  have et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (one_mul (𝟙 P₀.A))
  have et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀ := by
    rw [← Over.comp_left, lift_fst]
  have et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  let V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens := fun α =>
    m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2
  have hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1 := fun α => inf_le_left.trans inf_le_left
  have hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1 := fun α => inf_le_left.trans inf_le_right
  have hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2 := fun α => inf_le_right
  obtain ⟨ψ, hK⟩ := kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance
    inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q)
    (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) -
      pbT q (c a.2.2 b.2.2) (V a ⊓ V b))
    (by
      intro a b d
      have w1 : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
      have w2 : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
      have w3 : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
      simp only [map_sub]
      rw [presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm b)) (inf_le_right.trans (hVm d))),
        presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp b)) (inf_le_right.trans (hVp d))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq b)) (inf_le_right.trans (hVq d))),
        presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm d))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp d))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq d)))]
      have cm := pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))
      have cp := pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))
      have cq := pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))
      linear_combination cm - cp - cq)
    (by
      let s := (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1)
        (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q _ es_q (hVq α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)))]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
    (by
      let s := (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2)
        (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p _ et_p (hVp α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), sub_right_comm]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
  unfold IsCob
  refine ⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩
  rw [rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]
  exact (neg_sub_neg _ _).symm

/- English proof (translation)
The claim follows from `cech_coboundary_mul_sub_fst_sub_snd`.
-/
theorem cech_primitive : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) :=
  cech_coboundary_mul_sub_fst_sub_snd

end GlobalTheory.KS.Primitive
