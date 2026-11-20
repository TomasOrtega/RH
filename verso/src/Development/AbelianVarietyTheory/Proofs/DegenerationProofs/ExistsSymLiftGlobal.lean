import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftGlobal

open CommPairing GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

/- English proof (translation)
Take `⟨rfl, hp, ν, hν, hs⟩` from `H`. Take `⟨θ', e, v⟩` from `exists_pull hL h θ`. Take `⟨ν', hν', w⟩` from `exists_neg_pull hL h ν hν`. Establish `t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left = (r ≫ (h ▷ A).left) ≫ (translT A x).left` using `fun r x => by`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]`.

Establish `u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left = (r ≫ (h ▷ A).left) ≫ (negT A T).left` using `fun r => by`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]`. Use `⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩` and prove the remaining obligations. Establish `q` using `val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)`. Rewrite `q`, the goal using `[val_powGen _ _ _ hJ, val_one]`.

Use `Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q` and prove the remaining obligations. Rewrite using `[v _ _ y J hJ, e, ← MonObj.comp_pow, t]`. Establish `q` using `val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)`. Rewrite `q`, the goal using `[val_symGen _ _ _ hJ, val_one]`. Rewrite using `[v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]`.

Conclude with `q`.
-/
theorem exists_symLift_pull_val (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) :
    ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q

omit [GrpObj A] in

/- English proof (translation)
Take `⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left` from `⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hρ y), IsOpenImmersion.lift_fac _ _ _⟩`. Set `ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A` to `Over.homMk ρ rfl`.

Set `v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V` to `Over.homMk v (by show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom`. Rewrite using `[← Category.assoc, hv, Category.assoc, Over.w (fst T A)])`. Establish `e : v' ≫ overResι V = ρ' ≫ fst T A` using `Over.OverMorphism.ext hv`. Establish `e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ'`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, whiskerRight_fst, lift_fst_assoc, e]`. Rewrite using `[Category.assoc, whiskerRight_snd, lift_snd]`. Conclude with `⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩`.
-/
theorem exists_lift_res {T : Over S} (V : T.left.Opens) {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left)
    (hρ : ∀ z, (fst T A).left (ρ z) ∈ V) :
    ∃ n : Z ⟶ (overRes V ⊗ A).left, n ≫ (overResι V ▷ A).left = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left :=
    ⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hρ y), IsOpenImmersion.lift_fac _ _ _⟩
  let ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A := Over.homMk ρ rfl
  let v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V := Over.homMk v (by
    show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom
    rw [← Category.assoc, hv, Category.assoc, Over.w (fst T A)])
  have e : v' ≫ overResι V = ρ' ≫ fst T A := Over.OverMorphism.ext hv
  have e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, e]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
  exact ⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩

omit [GrpObj A] in
/- English proof (translation)
Establish `: Mono (overResι V).left` using `inferInstanceAs (Mono V.ι)`. Establish `: Mono (overResι V)` using `Over.mono_of_mono_left _`. Establish `: Mono (overResι V ▷ A)` using `⟨fun a b e => by`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e, Category.assoc]`.

Rewrite using `[← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩`. Use `infer_instance`.
-/
theorem mono_res {T : Over S} (V : T.left.Opens) : Mono (overResι V ▷ A).left := by
  have : Mono (overResι V).left := inferInstanceAs (Mono V.ι)
  have : Mono (overResι V) := Over.mono_of_mono_left _
  have : Mono (overResι V ▷ A) := ⟨fun a b e => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e,
        Category.assoc]
    · rw [← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩
  infer_instance

/- English proof (translation)
Establish `mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z), (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W` using `fun W s y => by`. Establish `e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι`. Rewrite using `[← Over.comp_left, whiskerRight_fst]`. Both sides reduce to the same expression. Conclude with `(congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2`.

Take `⟨m, hm⟩` from `exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left) (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)`. Establish `inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W, i ≫ overResι W = overResι (V ⊓ V')` using `fun W hW => ⟨Over.homMk (T.left.homOfLE hW) (by show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom`. Rewrite using `[← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩`. Take `⟨i, hi⟩` from `inc V inf_le_left`. Take `⟨i', hi'⟩` from `inc V' inf_le_right`.

Take `⟨ξ, Hξ, vξ⟩` from `exists_symLift_pull_val hL i H`. Take `⟨ξ', Hξ', vξ'⟩` from `exists_symLift_pull_val hL i' H'`. Rewrite `Hξ` using `[← Category.assoc, hi]`. Rewrite `Hξ'` using `[← Category.assoc, hi']`. Use `mono_res (A := A) V` as an intermediate fact.

Use `mono_res (A := A) V'` as an intermediate fact. Establish `e : m ≫ (i ▷ A).left = r`. Rewrite using `[← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]`. Establish `e' : m ≫ (i' ▷ A).left = r'`. Rewrite using `[← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]`.

Rewrite using `[← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]`. Conclude with `val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m`.
-/
theorem tval_agree (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {T : Over S}
    {x : T ⟶ A} {V V' : T.left.Opens} {θ : ThetaGrp A L k (overRes V)} {θ' : ThetaGrp A L k (overRes V')}
    (H : SymLift A L k n (overResι V ≫ x) θ) (H' : SymLift A L k n (overResι V' ≫ x) θ')
    {Z : Scheme.{0}} (r : Z ⟶ (overRes V ⊗ A).left) (r' : Z ⟶ (overRes V' ⊗ A).left)
    (hr : r ≫ (overResι V ▷ A).left = r' ≫ (overResι V' ▷ A).left) (z : Z) (J) (hJ : Good L z J) :
    tval θ r z J = tval θ' r' z J := by
  have mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z),
      (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W := fun W s y => by
    have e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι := by
      rw [← Over.comp_left, whiskerRight_fst]; rfl
    exact (congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2
  obtain ⟨m, hm⟩ := exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left)
    (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)
  have inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W,
      i ≫ overResι W = overResι (V ⊓ V') := fun W hW =>
    ⟨Over.homMk (T.left.homOfLE hW) (by
      show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩
  obtain ⟨i, hi⟩ := inc V inf_le_left
  obtain ⟨i', hi'⟩ := inc V' inf_le_right
  obtain ⟨ξ, Hξ, vξ⟩ := exists_symLift_pull_val hL i H
  obtain ⟨ξ', Hξ', vξ'⟩ := exists_symLift_pull_val hL i' H'
  rw [← Category.assoc, hi] at Hξ
  rw [← Category.assoc, hi'] at Hξ'
  have := mono_res (A := A) V
  have := mono_res (A := A) V'
  have e : m ≫ (i ▷ A).left = r := by
    rw [← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]
  have e' : m ≫ (i' ▷ A).left = r' := by
    rw [← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]
  rw [← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]
  exact val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m

/- English proof (translation)
Use `choose V hV θ hθ using h`. Use `choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)`. Establish `loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K` using `Fin 2) (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J → val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by`. Establish `e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left`. Rewrite using `[← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]`.

Establish `e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left`. Rewrite using `[← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]`. Take `⟨t, ht, hv⟩` from `exists_gen hL (K' := Fin 2) (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k]) (fun U _ f => by`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `fin_cases i`.

Conclude with `congrArg (fun q => f q ^ k) e₀`. Conclude with `congrArg (fun q => f q ^ (-k)) e₁)`. Use the proof step `(LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))`. Use the proof step `(DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)`. Conclude with `⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩`.

Use `choose t ht hv using loc`. Take `⟨u, hu, -⟩` from `glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k] (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht (fun p q Z r r' z J hJ e => by`. Rewrite using `[hv p Z r z J hJ, hv q Z r' z J hJ]`. Conclude with `tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)`. Conclude with `⟨⟨x, u, hu⟩, rfl⟩`.
-/
theorem exists_lift_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {T : Over S} {x : T ⟶ A}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L k (overRes V), SymLift A L k n (overResι V ≫ x) θ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  choose V hV θ hθ using h
  choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)
  have loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J →
        val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by
    have e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]
    obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2)
      (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ k) e₀
        · exact congrArg (fun q => f q ^ (-k)) e₁)
      (LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))
      (DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
  choose t ht hv using loc
  obtain ⟨u, hu, -⟩ := glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht
    (fun p q Z r r' z J hJ e => by
      rw [hv p Z r z J hJ, hv q Z r' z J hJ]
      exact tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)
  exact ⟨⟨x, u, hu⟩, rfl⟩

end GlobalTheory.SymLiftGlobal

namespace GlobalTheory

/- English proof (translation)
Introduce `hLaw S _ P k hk hu T x hx`. Take `⟨θ, hθ⟩` from `SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk (hLaw.symLift S P k hk hu T x hx).1`. Take `⟨nu, hnu⟩` from `exists_gen_negLB hLaw.globalFns S P k T`. Conclude with `SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu`.
-/
theorem exists_symLift_global : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k →
    IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  intro hLaw S _ P k hk hu T x hx
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk
    (hLaw.symLift S P k hk hu T x hx).1
  obtain ⟨nu, hnu⟩ := exists_gen_negLB hLaw.globalFns S P k T
  exact SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu

end GlobalTheory
