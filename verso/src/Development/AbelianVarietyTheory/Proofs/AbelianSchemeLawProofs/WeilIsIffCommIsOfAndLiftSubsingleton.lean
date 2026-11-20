import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlobalLift

open CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

/- English proof (translation)
Introduce `p`. Take `⟨a, b, ha, hb, H'⟩` from `exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H`. Conclude with `⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' => commIsOf_change hG hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩`.
-/
theorem weilIs_of_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) : WeilIs A L k θx.pt θy.pt c := by
  intro p
  obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
  exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
    commIsOf_change hG hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

/- English proof (translation)
Use `⟨fun H => ?_, weilIs_of_commIsOf hG hA hL⟩` and prove the remaining obligations. Take `⟨c₀, h₀⟩` from `CommutatorPairing.exists_commIsOf hG hA hL θx θy`. Rewrite using `[CommutatorPairing.weilIs_unique hG hA hL H (weilIs_of_commIsOf hG hA hL h₀)]`. Conclude with `h₀`.
-/
theorem weilIs_iff_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k θx.pt θy.pt c ↔ CommIsOf A L k θx θy c := by
  refine ⟨fun H => ?_, weilIs_of_commIsOf hG hA hL⟩
  obtain ⟨c₀, h₀⟩ := CommutatorPairing.exists_commIsOf hG hA hL θx θy
  rw [CommutatorPairing.weilIs_unique hG hA hL H (weilIs_of_commIsOf hG hA hL h₀)]
  exact h₀

/- English proof (translation)
Use `Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _ (Finset.univ : Finset (Fin n))) ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)`.
-/
theorem val_powGen {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by
  refine Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _
    (Finset.univ : Finset (Fin n))) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ
    (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)

def nval {T : Over S} (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (· * nval ν r z J) (val_pull hJ _ _ _))) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))`.
-/
theorem val_symGen {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J * nval ν r z J) *
      (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * nval ν r z J) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

/- English proof (translation)
Establish `e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left` using `by rw [← Over.comp_left, whiskerRight_snd]`. Establish `e₁ : (h ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left`. Rewrite using `[← Over.comp_left, whiskerRight_snd_assoc]`. Take `⟨t, ht, hv⟩` from `exists_gen hL (φ' := ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε' := ![k, -k]) (fun U _ f => by`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `fin_cases i`. Conclude with `congrArg (fun q => f q ^ k) e₀`. Conclude with `congrArg (fun q => f q ^ (-k)) e₁)`. Use the proof step `(LB.pullGen L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (h ▷ A).left)`. Use the proof step `(DVR.pullGen_isGen _ _ _ _ hν _)`.

Conclude with `⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩`.
-/
theorem exists_neg_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (ν : LB.Gen (negLB A L k T)) (hν : ν.IsGen) :
    ∃ ν' : LB.Gen (negLB A L k T'), ν'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → nval ν' r z J = nval ν (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, whiskerRight_snd_assoc]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ hν _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[negT]`. Simplify using `[negT]`.
-/
theorem whisker_negT {T T' : Over S} (h : T' ⟶ T) : negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

/- English proof (translation)
Take `⟨rfl, hp, ν, hν, hs⟩` from `H`. Take `⟨θ', e, v⟩` from `exists_pull hL h θ`. Take `⟨ν', hν', w⟩` from `exists_neg_pull hL h ν hν`. Establish `t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left = (r ≫ (h ▷ A).left) ≫ (translT A x).left` using `fun r x => by`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]`.

Establish `u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left = (r ≫ (h ▷ A).left) ≫ (negT A T).left` using `fun r => by`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]`. Use `⟨θ', e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩` and prove the remaining obligations. Establish `q` using `val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)`. Rewrite `q`, the goal using `[val_powGen _ _ _ hJ, val_one]`.

Use `Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q` and prove the remaining obligations. Rewrite using `[v _ _ y J hJ, e, ← MonObj.comp_pow, t]`. Establish `q` using `val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)`. Rewrite `q`, the goal using `[val_symGen _ _ _ hJ, val_one]`. Rewrite using `[v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]`.

Conclude with `q`.
-/
theorem exists_symLift_pull (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (H : SymLift A L k n x θ) : ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q

/- English proof (translation)
Establish `he : ∀ {Q : Prop} (_ : (T ⊗ A).left), Q` using `fun y => isEmptyElim ((fst T A).left y)`. Conclude with `⟨⟨x, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y⟩, rfl, corr_of_val hL fun y _ _ => he y, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y, corr_of_val hL fun y _ _ => he y⟩`.
-/
theorem exists_symLift_empty (hL : L.IsLB) (n : ℕ) {T : Over S} [IsEmpty T.left] (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n x θ := by
  have he : ∀ {Q : Prop} (_ : (T ⊗ A).left), Q := fun y => isEmptyElim ((fst T A).left y)
  exact ⟨⟨x, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y⟩, rfl, corr_of_val hL fun y _ _ => he y,
    ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y, corr_of_val hL fun y _ _ => he y⟩

omit [GrpObj A] in

/- English proof (translation)
Take `rfl : V = ⊤` from `eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]`. Conclude with `⟨Over.homMk T.left.topIso.inv (by show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom`. Rewrite using `[← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩`.
-/
theorem exists_section {T : Over S} [Subsingleton T.left] {V : T.left.Opens} {p : T.left} (hp : p ∈ V) :
    ∃ h : T ⟶ overRes V, h ≫ overResι V = 𝟙 T := by
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  exact ⟨Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩

end GlobalTheory.GlobalLift

namespace GlobalTheory

open GlobalLift in

/- English proof (translation)
Introduce `hG hlift hsym S P k T`. Use `⟨weilIs_iff_commIsOf hG P.isAb P.isLB, fun x hx hT => ?_⟩` and prove the remaining obligations. Break down `isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩` into its components or cases. Take `⟨θ, H⟩` from `exists_symLift_empty (k := (k : ℤ)) P.isLB k x`. Conclude with `⟨θ, H.pt_eq, fun _ => H⟩`.

Distinguish the cases in `hk : Odd k`. Take `⟨V, hp, θ, H⟩` from `(hsym S P k hk T x hx).1 p`. Take `⟨h, e⟩` from `exists_section hp`. Take `⟨θ', H'⟩` from `exists_symLift_pull P.isLB h H`. Rewrite `H'` using `[← Category.assoc, e, Category.id_comp]`.

Conclude with `⟨θ', H'.pt_eq, fun _ => H'⟩`. Take `⟨V, hp, θ, H⟩` from `hlift S P k T x hx p`. Take `⟨h, e⟩` from `exists_section hp`. Take `⟨θ', e', -⟩` from `CommPairing.exists_pull P.isLB h θ`. Rewrite `e'` using `[H, ← Category.assoc, e, Category.id_comp]`.

Conclude with `⟨θ', e', fun h => absurd h hk⟩`.
-/
theorem weilIs_iff_commIsOf_and_lift_subsingleton : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ)) := by
  intro hG hlift hsym S P k T
  refine ⟨weilIs_iff_commIsOf hG P.isAb P.isLB, fun x hx hT => ?_⟩
  rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
  · obtain ⟨θ, H⟩ := exists_symLift_empty (k := (k : ℤ)) P.isLB k x
    exact ⟨θ, H.pt_eq, fun _ => H⟩
  by_cases hk : Odd k
  · obtain ⟨V, hp, θ, H⟩ := (hsym S P k hk T x hx).1 p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', H'⟩ := exists_symLift_pull P.isLB h H
    rw [← Category.assoc, e, Category.id_comp] at H'
    exact ⟨θ', H'.pt_eq, fun _ => H'⟩
  · obtain ⟨V, hp, θ, H⟩ := hlift S P k T x hx p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', e', -⟩ := CommPairing.exists_pull P.isLB h θ
    rw [H, ← Category.assoc, e, Category.id_comp] at e'
    exact ⟨θ', e', fun h => absurd h hk⟩

end GlobalTheory
