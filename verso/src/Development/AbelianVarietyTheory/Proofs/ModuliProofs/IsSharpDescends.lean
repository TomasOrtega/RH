import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpDescent

/- English proof (translation)
Set `Q₁ : Over S₁` to `∏ᶜ (fun _ : I => C₁)`. Set `π : I → (Q₁ ⟶ C₁)` to `fun u => Pi.π (fun _ : I => C₁) u`. Set `m₁ : A₁ ⟶ Q₁` to `Pi.lift pr₁`. Establish `hm₁ : ∀ u, m₁ ≫ π u = pr₁ u` using `fun u => Pi.lift_π _ _`. Establish `ext₁ : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Q₁.left), a ≫ Q₁.hom = b ≫ Q₁.hom → (∀ u, a ≫ (π u).left = b ≫ (π u).left) → a = b`.

Introduce `Z a b h1 h2`. Establish `: (Over.homMk a rfl : Over.mk (a ≫ Q₁.hom) ⟶ Q₁) = Over.homMk b h1.symm` using `Pi.hom_ext _ _ fun u => Over.OverMorphism.ext (h2 u)`. Conclude with `congrArg (fun z => z.left) this`. Set `Q : Over S` to `Over.mk (pullback.snd Q₁.hom i)`. Set `q : I → (Q ⟶ C)` to `fun u => Over.homMk (hχ.lift (pullback.fst Q₁.hom i ≫ (π u).left) (pullback.snd Q₁.hom i) (by rw [Category.assoc, Over.w, pullback.condition])) (hχ.lift_snd _ _ _)`.

Establish `hq : ∀ u, (q u).left ≫ χ = pullback.fst Q₁.hom i ≫ (π u).left` using `fun u => hχ.lift_fst _ _ _`. Set `m : A ⟶ Q` to `Over.homMk (pullback.lift (ψ ≫ m₁.left) A.hom (by rw [Category.assoc, Over.w, hψ.w])) (pullback.lift_snd _ _ _)`. Establish `hm : m.left ≫ pullback.fst Q₁.hom i = ψ ≫ m₁.left` using `pullback.lift_fst _ _ _`. Establish `hm' : m.left ≫ pullback.snd Q₁.hom i = A.hom` using `pullback.lift_snd _ _ _`. Establish `hmq : ∀ u, m ≫ q u = pr u` using `fun u => Over.OverMorphism.ext (hχ.hom_ext (by rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, hm, Category.assoc, ← Over.comp_left, hm₁, hc]) (by rw [Over.w, Over.w]))`.

Take `⟨n, hn, -⟩` from `hU Q q`. Establish `h1 : m ≫ n = 𝟙 A` using `(hU A pr).unique (fun u => by rw [Category.assoc, hn, hmq]) (fun u => Category.id_comp _)`. Establish `h2 : n.left ≫ m.left = 𝟙 Q.left`. Establish `hs : (n.left ≫ m.left) ≫ pullback.snd Q₁.hom i = 𝟙 Q.left ≫ pullback.snd Q₁.hom i`. Rewrite using `[Category.assoc, hm', Over.w, Category.id_comp]`.

Both sides reduce to the same expression. Use `pullback.hom_ext (ext₁ _ _ ?_ fun u => ?_) hs` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc (𝟙 _), pullback.condition, ← Category.assoc, hs, Category.assoc]`. Rewrite using `[Category.assoc, Category.assoc (𝟙 _), ← hq, Category.id_comp, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, Category.assoc, hmq, hn]`. Establish `hI : IsIso m.left` using `⟨⟨n.left, by rw [← Over.comp_left, h1, Over.id_left], h2⟩⟩`.

Establish `hp : IsPullback m.left ψ (pullback.fst Q₁.hom i) m₁.left`. Use `IsPullback.of_right (h₁₂ := pullback.snd Q₁.hom i) (v₁₃ := i) (h₂₂ := Q₁.hom) ?_ hm (IsPullback.of_hasPullback Q₁.hom i).flip` and prove the remaining obligations. Rewrite using `[hm', Over.w]`. Conclude with `hψ.flip`. Establish `hI₁ : IsIso m₁.left` using `MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hI`.

Establish `: IsIso ((Over.forget S₁).map m₁)` using `hI₁`. Establish `: IsIso m₁` using `isIso_of_reflects_iso m₁ (Over.forget S₁)`. Use `⟨Pi.lift y ≫ inv m₁, fun u => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hm₁, Category.assoc, IsIso.inv_hom_id_assoc]`. Conclude with `Pi.lift_π _ _`.

Rewrite using `[IsIso.eq_comp_inv]`. Use `Pi.hom_ext _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Pi.lift_π]`. Conclude with `(hx u).trans (Pi.lift_π _ _).symm`.
-/
theorem univ_descend {S S₁ : Scheme.{0}} (i : S ⟶ S₁) [Surjective i] [Flat i] [QuasiCompact i]
    {A C : Over S} {A₁ C₁ : Over S₁} {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left}
    (hψ : IsPullback ψ A.hom A₁.hom i) (hχ : IsPullback χ C.hom C₁.hom i) {I : Type} [Finite I]
    (pr : I → (A ⟶ C)) (pr₁ : I → (A₁ ⟶ C₁)) (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ)
    (hU : ∀ (T : Over S) (y : I → (T ⟶ C)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u)
    (T : Over S₁) (y : I → (T ⟶ C₁)) : ∃! x : T ⟶ A₁, ∀ u, x ≫ pr₁ u = y u := by
  let Q₁ : Over S₁ := ∏ᶜ (fun _ : I => C₁)
  let π : I → (Q₁ ⟶ C₁) := fun u => Pi.π (fun _ : I => C₁) u
  let m₁ : A₁ ⟶ Q₁ := Pi.lift pr₁
  have hm₁ : ∀ u, m₁ ≫ π u = pr₁ u := fun u => Pi.lift_π _ _
  have ext₁ : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Q₁.left), a ≫ Q₁.hom = b ≫ Q₁.hom →
      (∀ u, a ≫ (π u).left = b ≫ (π u).left) → a = b := by
    intro Z a b h1 h2
    have : (Over.homMk a rfl : Over.mk (a ≫ Q₁.hom) ⟶ Q₁) = Over.homMk b h1.symm :=
      Pi.hom_ext _ _ fun u => Over.OverMorphism.ext (h2 u)
    exact congrArg (fun z => z.left) this
  let Q : Over S := Over.mk (pullback.snd Q₁.hom i)
  let q : I → (Q ⟶ C) := fun u => Over.homMk (hχ.lift (pullback.fst Q₁.hom i ≫ (π u).left) (pullback.snd Q₁.hom i)
    (by rw [Category.assoc, Over.w, pullback.condition])) (hχ.lift_snd _ _ _)
  have hq : ∀ u, (q u).left ≫ χ = pullback.fst Q₁.hom i ≫ (π u).left := fun u => hχ.lift_fst _ _ _
  let m : A ⟶ Q := Over.homMk (pullback.lift (ψ ≫ m₁.left) A.hom (by rw [Category.assoc, Over.w, hψ.w]))
    (pullback.lift_snd _ _ _)
  have hm : m.left ≫ pullback.fst Q₁.hom i = ψ ≫ m₁.left := pullback.lift_fst _ _ _
  have hm' : m.left ≫ pullback.snd Q₁.hom i = A.hom := pullback.lift_snd _ _ _
  have hmq : ∀ u, m ≫ q u = pr u := fun u => Over.OverMorphism.ext (hχ.hom_ext
    (by rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, hm, Category.assoc, ← Over.comp_left, hm₁, hc])
    (by rw [Over.w, Over.w]))
  obtain ⟨n, hn, -⟩ := hU Q q
  have h1 : m ≫ n = 𝟙 A := (hU A pr).unique (fun u => by rw [Category.assoc, hn, hmq]) (fun u => Category.id_comp _)
  have h2 : n.left ≫ m.left = 𝟙 Q.left := by
    have hs : (n.left ≫ m.left) ≫ pullback.snd Q₁.hom i = 𝟙 Q.left ≫ pullback.snd Q₁.hom i := by
      rw [Category.assoc, hm', Over.w, Category.id_comp]; rfl
    refine pullback.hom_ext (ext₁ _ _ ?_ fun u => ?_) hs
    · rw [Category.assoc, Category.assoc (𝟙 _), pullback.condition, ← Category.assoc, hs, Category.assoc]
    · rw [Category.assoc, Category.assoc (𝟙 _), ← hq, Category.id_comp, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, Category.assoc, hmq, hn]
  have hI : IsIso m.left := ⟨⟨n.left, by rw [← Over.comp_left, h1, Over.id_left], h2⟩⟩
  have hp : IsPullback m.left ψ (pullback.fst Q₁.hom i) m₁.left := by
    refine IsPullback.of_right (h₁₂ := pullback.snd Q₁.hom i) (v₁₃ := i) (h₂₂ := Q₁.hom) ?_ hm
      (IsPullback.of_hasPullback Q₁.hom i).flip
    rw [hm', Over.w]; exact hψ.flip
  have hI₁ : IsIso m₁.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hI
  have : IsIso ((Over.forget S₁).map m₁) := hI₁
  have : IsIso m₁ := isIso_of_reflects_iso m₁ (Over.forget S₁)
  refine ⟨Pi.lift y ≫ inv m₁, fun u => ?_, fun x hx => ?_⟩
  · rw [← hm₁, Category.assoc, IsIso.inv_hom_id_assoc]; exact Pi.lift_π _ _
  · rw [IsIso.eq_comp_inv]
    refine Pi.hom_ext _ _ fun u => ?_
    rw [Category.assoc, Pi.lift_π]
    exact (hx u).trans (Pi.lift_π _ _).symm

/- English proof (translation)
Set `U : Over.mk (A.hom ≫ i) ⟶ A₁` to `Over.homMk ψ hψ`. Establish `key : ∀ (x : A ⟶ C) (x₁ : A₁ ⟶ C₁), ψ ≫ x₁.left = x.left ≫ χ → preHom U x₁ = pushHom hχ A x` using `fun x x₁ hx => Over.OverMorphism.ext hx`. Establish `E : preHom U z₁ = preHom U (List.ofFn fun v => pr₁ v ^ e v).prod`. Rewrite using `[key z z₁ hz, h, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]`. Use `congr 2`.

Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp, map_zpow, key _ _ (hc v)]`. Conclude with `Over.OverMorphism.ext ((cancel_epi ψ).1 (congrArg (fun w => w.left) E))`.
-/
theorem prod_descend {S S₁ : Scheme.{0}} {i : S ⟶ S₁} {A C : Over S} {A₁ C₁ : Over S₁} [GrpObj C] [GrpObj C₁]
    {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left} [Epi ψ] (hψ : ψ ≫ A₁.hom = A.hom ≫ i)
    (hχ : IsGrpPullback C C₁ i χ) {n : ℕ} (pr : Fin n → (A ⟶ C)) (pr₁ : Fin n → (A₁ ⟶ C₁))
    (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ) (e : Fin n → ℤ) (z : A ⟶ C) (z₁ : A₁ ⟶ C₁)
    (hz : ψ ≫ z₁.left = z.left ≫ χ) (h : z = (List.ofFn fun v => pr v ^ e v).prod) :
    z₁ = (List.ofFn fun v => pr₁ v ^ e v).prod := by
  let U : Over.mk (A.hom ≫ i) ⟶ A₁ := Over.homMk ψ hψ
  have key : ∀ (x : A ⟶ C) (x₁ : A₁ ⟶ C₁), ψ ≫ x₁.left = x.left ≫ χ → preHom U x₁ = pushHom hχ A x :=
    fun x x₁ hx => Over.OverMorphism.ext hx
  have E : preHom U z₁ = preHom U (List.ofFn fun v => pr₁ v ^ e v).prod := by
    rw [key z z₁ hz, h, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp, map_zpow, key _ _ (hc v)]
  exact Over.OverMorphism.ext ((cancel_epi ψ).1 (congrArg (fun w => w.left) E))

/- English proof (translation)
Take `⟨w, hw⟩` from `h₁`. Use `iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => ψ) (fun _ => 1)` as an intermediate fact. Substitute `e` using the available equality. Conclude with `LBIso.trans hL (pull_isLB hL₀ _) (pull_isLB hL₁ _) h (LBIso.symm this)`.
-/
theorem iso_pull_cancel {X X₁ X₀ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₀ : LB X₀} (hL : L.IsLB) (hL₁ : L₁.IsLB)
    (hL₀ : L₀.IsLB) {φ : X ⟶ X₀} {φ₁ : X₁ ⟶ X₀} {ψ : X ⟶ X₁} (e : ψ ≫ φ₁ = φ) (h : LBIso L (L₀.pull φ))
    (h₁ : LBIso L₁ (L₀.pull φ₁)) : LBIso L (L₁.pull ψ) := by
  obtain ⟨w, hw⟩ := h₁
  have := iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => ψ) (fun _ => 1)
  subst e
  exact LBIso.trans hL (pull_isLB hL₀ _) (pull_isLB hL₁ _) h (LBIso.symm this)

/- English proof (translation)
Introduce `h g k W J a bas o _ b K _ K₀ β₀ s t c t₀ c₀ hs ⟨φ, hφ, hφL, hφp, hφa⟩ ⟨ξ, ξ₂, hξ, hξs, hξL, hξl⟩ hP ⟨pr, hm, hU, hL, hA, hp⟩`. Use `t₀.ab.proper` as an intermediate fact. Use `c₀.ab.smooth` as an intermediate fact. Establish `hf : ∀ u, ((pr u).left ≫ ξ) ≫ c₀.A.hom = φ ≫ t₀.A.hom` using `fun u => by`. Rewrite using `[Category.assoc, hξ.1.w, ← Category.assoc, Over.w, hφ.1.w]`.

Take `⟨F, hF⟩` from `GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K₀ _ _ t₀.A.hom t.A.hom φ _ c₀.A.hom (Fin 8) (fun u => (pr u).left ≫ ξ) hφ.1 hf`. Use `⟨F, ?_⟩` and prove the remaining obligations. Establish `hle : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F)` using `fun x hx => Subfield.subset_closure (Or.inl hx)`. Establish `hFs : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F)` using `fun x hx => Subfield.subset_closure (Or.inr hx)`. Establish `hF₁` using `hF _ hle hFs`.

Generalize the expression as in `Subfield.closure ((K₀ : Set K) ∪ F) = K₁ at hle hF₁ ⊢`. Use `clear hF hFs`. Establish `e₁ : spMap (Subfield.inclusion hle) ≫ spMap β₀ = spMap ((Subfield.inclusion hle).comp β₀)` using `(Spec.map_comp _ _).symm`. Establish `e₂ : spMap K₁.subtype ≫ spMap (Subfield.inclusion hle) = spMap K₀.subtype` using `(Spec.map_comp _ _).symm`. Take `⟨t₁, φ₁, hφ₁, hφ₁L, hφ₁p, hφ₁a⟩` from `GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ _ t₀ e₁`.

Take `⟨⟨c₁, hc₁⟩, hc₁P⟩` from `GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) _ _ _ _ _ c₀ e₁`. Establish `hP₁` using `hc₁P c₁ hc₁ hP`. Take `⟨ξ₁, ξ₁₂, hξ₁, hξ₁s, hξ₁L, hξ₁l⟩` from `hc₁`. Take `⟨ψ, hψ, hψw⟩ : ∃ ψ : t.A.left ⟶ t₁.A.left, ψ ≫ φ₁ = φ ∧ ψ ≫ t₁.A.hom = t.A.hom ≫ spMap K₁.subtype` from `⟨hφ₁.1.lift φ (t.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hφ.1.w]), hφ₁.1.lift_fst _ _ _, hφ₁.1.lift_snd _ _ _⟩`. Take `⟨χ, hχ, hχw⟩ : ∃ χ : c.A.left ⟶ c₁.A.left, χ ≫ ξ₁ = ξ ∧ χ ≫ c₁.A.hom = c.A.hom ≫ spMap K₁.subtype` from `⟨hξ₁.1.lift ξ (c.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hξ.1.w]), hξ₁.1.lift_fst _ _ _, hξ₁.1.lift_snd _ _ _⟩`.

Establish `gψ : IsGrpPullback t.A t₁.A (spMap K₁.subtype) ψ` using `hφ₁.cancel (hφ.congr e₂.symm hψ.symm) hψw`. Establish `gχ : IsGrpPullback c.A c₁.A (spMap K₁.subtype) χ` using `hξ₁.cancel (hξ.congr e₂.symm hχ.symm) hχw`. Take `⟨f₁, hf₁⟩` from `hF₁ _ t₁.A.hom φ₁ ψ hφ₁.1 hψ hψw`. Take `⟨pr₁, hpr₁⟩ : ∃ pr₁ : Fin 8 → (t₁.A ⟶ c₁.A), ∀ u, (pr₁ u).left ≫ ξ₁ = f₁ u` from `⟨fun u => Over.homMk (hξ₁.1.lift (f₁ u) t₁.A.hom ((hf₁ u).2.trans hφ₁.1.w)) (hξ₁.1.lift_snd _ _ _), fun u => hξ₁.1.lift_fst _ _ _⟩`. Establish `hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ` using `fun u => hξ₁.1.hom_ext (by rw [Category.assoc, hpr₁, (hf₁ u).1, Category.assoc, hχ]) (by rw [Category.assoc, Over.w, hψw, Category.assoc, hχw, ← Category.assoc, Over.w])`.

Take `⟨D₁, D₂⟩` from `GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₁ K K₁.subtype`. Take `⟨i₁, i₂, i₃, i₄, -⟩` from `D₁ _ _ (𝟙 _) (𝟙 _) (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp⟩)`. Take `⟨j₁, -⟩` from `D₁ _ _ _ _ ψ gψ.1`. Establish `hψL : LBIso t.L (t₁.L.pull ψ)` using `iso_pull_cancel t.isLB t₁.isLB t₀.isLB hψ hφL hφ₁L`. Establish `hψp : ∀ i, (t.pt i).left ≫ ψ = spMap K₁.subtype ≫ (t₁.pt i).left` using `fun i => hφ₁.1.hom_ext (by rw [Category.assoc, hψ, hφp, Category.assoc, hφ₁p, ← Category.assoc, e₂]) (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)`.

Establish `hψa : ∀ j, (t.act j).left ≫ ψ = ψ ≫ (t₁.act j).left` using `fun j => hφ₁.1.hom_ext (by rw [Category.assoc, hψ, hφa, Category.assoc, hφ₁a, ← Category.assoc, hψ]) (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w, hψw])`. Establish `hχl : ∀ v, (c.lev v).left ≫ χ = spMap K₁.subtype ≫ (c₁.lev v).left` using `fun v => hξ₁.1.hom_ext (by rw [Category.assoc, hχ, hξl, Category.assoc, hξ₁l, ← Category.assoc, e₂]) (by rw [Category.assoc, hχw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)`. Use `⟨_, t₁, c₁, by rw [hs, ← e₁, ← Category.assoc, e₂], ⟨ψ, gψ, hψL, hψp, hψa⟩, hP₁, pr₁, fun u => (D₂ _ _ _ _ ψ χ (pr₁ u) (pr u) gψ gχ (hc u)).1 (hm u), univ_descend _ gψ.1 gχ.1 pr pr₁ hc hU, ?_, fun j u => prod_descend hψw gχ pr pr₁ hc _ (t.act j ≫ pr u) _ ?_ (hA j u), fun i u => ? …` and prove the remaining obligations. Establish `lb` using `fun {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (φ : Fin 8 × Fin 8 → (Y ⟶ X)) => DVR.linComb_isLB L hL φ (fun uv => W uv.1 uv.2)`. Use `(GlobalTheory.T.lineBundle_trivial_iso_descend_field K₁ K K₁.subtype _ _ _ _ ψ t₁.ab.smooth t₁.ab.proper t₁.ab.geomConnected gψ.1).2 _ _ t₁.isLB (lb _ c₁.isLB _) ?_` and prove the remaining obligations.

Take `⟨w, hw⟩` from `hξL`. Take `⟨w₁, hw₁⟩` from `hξ₁L`. Establish `a₁` using `iso_linComb ((isGen_iff w).1 hw) (fun uv : Fin 8 × Fin 8 => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)`. Establish `a₂` using `iso_linComb ((isGen_iff w₁).1 hw₁) (fun uv : Fin 8 × Fin 8 => ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left) (fun uv => W uv.1 uv.2)`. Establish `e : (fun uv : Fin 8 × Fin 8 => (ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left) ≫ ξ₁₂) = fun uv => (lift (pr uv.1) (pr uv.2)).left ≫ ξ₂`.

Use function extensionality and compare the values at `uv`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show (_ ≫ ξ₁₂) ≫ (fst c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (fst c₀.A c₀.A).left`. Rewrite using `[Category.assoc, hξ₁s.1, Category.assoc, Category.assoc, hξs.1, ← Over.comp_left_assoc, ← Over.comp_left_assoc, lift_fst, lift_fst, hpr₁, (hf₁ _).1]`. Use `show (_ ≫ ξ₁₂) ≫ (snd c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (snd c₀.A c₀.A).left`.

Rewrite using `[Category.assoc, hξ₁s.2, Category.assoc, Category.assoc, hξs.2, ← Over.comp_left_assoc, ← Over.comp_left_assoc, lift_snd, lift_snd, hpr₁, (hf₁ _).1]`. Rewrite `a₂` using `[e]`. Establish `a₃` using `LBIso.trans t.isLB (lb _ c.isLB _) (lb _ c₀.isLB _) hL a₁`. Establish `a₄` using `LBIso.trans t.isLB (lb _ c₀.isLB _) (lb _ c₁.isLB _) a₃ a₂.symm`. Establish `a₅` using `LBIso.trans (pull_isLB t₁.isLB ψ) t.isLB (lb _ c₁.isLB _) hψL.symm a₄`.

Conclude with `LBIso.chartPull (chartPullId _) (chartPullOut c₁.P _ _ ψ _ fun _ => rfl) a₅`. Rewrite using `[Over.comp_left, Over.comp_left, ← Category.assoc, ← hψa, Category.assoc, hc, Category.assoc]`. Rewrite using `[← cancel_epi (spMap K₁.subtype), Over.comp_left, ← Category.assoc, ← hψp, Category.assoc, hc, ← Category.assoc, ← Over.comp_left, hp]`. Conclude with `hχl _`.
-/
theorem isSharp_descends : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (K : Type) [Field K] (K₀ : Subfield K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t : TObj g k J b s) (c : SiegPre h k (b.ζ : o) s) (t₀ : TObj g k J b (spMap β₀)) (c₀ : SiegPre h k (b.ζ : o) (spMap β₀)), s = spMap K₀.subtype ≫ spMap β₀ → TMap t t₀ (spMap K₀.subtype) → SiegPB c c₀ (spMap K₀.subtype) → c₀.Principal → IsSharp W a bas t c → ∃ (F : Finset K) (β₁ : o →+* Subfield.closure ((K₀ : Set K) ∪ F)) (t₁ : TObj g k J b (spMap β₁)) (c₁ : SiegPre h k (b.ζ : o) (spMap β₁)), s = spMap (Subfield.subtype _) ≫ spMap β₁ ∧ TMap t t₁ (spMap (Subfield.subtype _)) ∧ c₁.Principal ∧ IsSharp W a bas t₁ c₁ := by
  intro h g k W J a bas o _ b K _ K₀ β₀ s t c t₀ c₀ hs ⟨φ, hφ, hφL, hφp, hφa⟩ ⟨ξ, ξ₂, hξ, hξs, hξL, hξl⟩ hP
    ⟨pr, hm, hU, hL, hA, hp⟩
  have := t₀.ab.proper
  have := c₀.ab.smooth
  have hf : ∀ u, ((pr u).left ≫ ξ) ≫ c₀.A.hom = φ ≫ t₀.A.hom := fun u => by
    rw [Category.assoc, hξ.1.w, ← Category.assoc, Over.w, hφ.1.w]
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K₀ _ _ t₀.A.hom t.A.hom φ _ c₀.A.hom (Fin 8) (fun u => (pr u).left ≫ ξ) hφ.1 hf
  refine ⟨F, ?_⟩
  have hle : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inl hx)
  have hFs : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inr hx)
  have hF₁ := hF _ hle hFs
  generalize Subfield.closure ((K₀ : Set K) ∪ F) = K₁ at hle hF₁ ⊢
  clear hF hFs
  have e₁ : spMap (Subfield.inclusion hle) ≫ spMap β₀ = spMap ((Subfield.inclusion hle).comp β₀) :=
    (Spec.map_comp _ _).symm
  have e₂ : spMap K₁.subtype ≫ spMap (Subfield.inclusion hle) = spMap K₀.subtype := (Spec.map_comp _ _).symm
  obtain ⟨t₁, φ₁, hφ₁, hφ₁L, hφ₁p, hφ₁a⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ _ t₀ e₁
  obtain ⟨⟨c₁, hc₁⟩, hc₁P⟩ := GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) _ _ _ _ _ c₀ e₁
  have hP₁ := hc₁P c₁ hc₁ hP
  obtain ⟨ξ₁, ξ₁₂, hξ₁, hξ₁s, hξ₁L, hξ₁l⟩ := hc₁

  obtain ⟨ψ, hψ, hψw⟩ : ∃ ψ : t.A.left ⟶ t₁.A.left, ψ ≫ φ₁ = φ ∧ ψ ≫ t₁.A.hom = t.A.hom ≫ spMap K₁.subtype :=
    ⟨hφ₁.1.lift φ (t.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hφ.1.w]), hφ₁.1.lift_fst _ _ _,
      hφ₁.1.lift_snd _ _ _⟩
  obtain ⟨χ, hχ, hχw⟩ : ∃ χ : c.A.left ⟶ c₁.A.left, χ ≫ ξ₁ = ξ ∧ χ ≫ c₁.A.hom = c.A.hom ≫ spMap K₁.subtype :=
    ⟨hξ₁.1.lift ξ (c.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hξ.1.w]), hξ₁.1.lift_fst _ _ _,
      hξ₁.1.lift_snd _ _ _⟩
  have gψ : IsGrpPullback t.A t₁.A (spMap K₁.subtype) ψ := hφ₁.cancel (hφ.congr e₂.symm hψ.symm) hψw
  have gχ : IsGrpPullback c.A c₁.A (spMap K₁.subtype) χ := hξ₁.cancel (hξ.congr e₂.symm hχ.symm) hχw
  obtain ⟨f₁, hf₁⟩ := hF₁ _ t₁.A.hom φ₁ ψ hφ₁.1 hψ hψw
  obtain ⟨pr₁, hpr₁⟩ : ∃ pr₁ : Fin 8 → (t₁.A ⟶ c₁.A), ∀ u, (pr₁ u).left ≫ ξ₁ = f₁ u :=
    ⟨fun u => Over.homMk (hξ₁.1.lift (f₁ u) t₁.A.hom ((hf₁ u).2.trans hφ₁.1.w)) (hξ₁.1.lift_snd _ _ _),
      fun u => hξ₁.1.lift_fst _ _ _⟩
  have hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ := fun u => hξ₁.1.hom_ext
    (by rw [Category.assoc, hpr₁, (hf₁ u).1, Category.assoc, hχ])
    (by rw [Category.assoc, Over.w, hψw, Category.assoc, hχw, ← Category.assoc, Over.w])
  obtain ⟨D₁, D₂⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₁ K K₁.subtype
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := D₁ _ _ (𝟙 _) (𝟙 _) (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp⟩)
  obtain ⟨j₁, -⟩ := D₁ _ _ _ _ ψ gψ.1
  have hψL : LBIso t.L (t₁.L.pull ψ) := iso_pull_cancel t.isLB t₁.isLB t₀.isLB hψ hφL hφ₁L
  have hψp : ∀ i, (t.pt i).left ≫ ψ = spMap K₁.subtype ≫ (t₁.pt i).left := fun i => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφp, Category.assoc, hφ₁p, ← Category.assoc, e₂])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  have hψa : ∀ j, (t.act j).left ≫ ψ = ψ ≫ (t₁.act j).left := fun j => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφa, Category.assoc, hφ₁a, ← Category.assoc, hψ])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w, hψw])
  have hχl : ∀ v, (c.lev v).left ≫ χ = spMap K₁.subtype ≫ (c₁.lev v).left := fun v => hξ₁.1.hom_ext
    (by rw [Category.assoc, hχ, hξl, Category.assoc, hξ₁l, ← Category.assoc, e₂])
    (by rw [Category.assoc, hχw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  refine ⟨_, t₁, c₁, by rw [hs, ← e₁, ← Category.assoc, e₂], ⟨ψ, gψ, hψL, hψp, hψa⟩, hP₁, pr₁,
    fun u => (D₂ _ _ _ _ ψ χ (pr₁ u) (pr u) gψ gχ (hc u)).1 (hm u), univ_descend _ gψ.1 gχ.1 pr pr₁ hc hU, ?_,
    fun j u => prod_descend hψw gχ pr pr₁ hc _ (t.act j ≫ pr u) _ ?_ (hA j u), fun i u => ?_⟩
  · have lb := fun {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (φ : Fin 8 × Fin 8 → (Y ⟶ X)) =>
      DVR.linComb_isLB L hL φ (fun uv => W uv.1 uv.2)
    refine (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₁ K K₁.subtype _ _ _ _ ψ t₁.ab.smooth t₁.ab.proper t₁.ab.geomConnected gψ.1).2 _ _ t₁.isLB
      (lb _ c₁.isLB _) ?_
    obtain ⟨w, hw⟩ := hξL
    obtain ⟨w₁, hw₁⟩ := hξ₁L
    have a₁ := iso_linComb ((isGen_iff w).1 hw) (fun uv : Fin 8 × Fin 8 => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have a₂ := iso_linComb ((isGen_iff w₁).1 hw₁) (fun uv : Fin 8 × Fin 8 => ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have e : (fun uv : Fin 8 × Fin 8 => (ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left) ≫ ξ₁₂) =
        fun uv => (lift (pr uv.1) (pr uv.2)).left ≫ ξ₂ := by
      funext uv
      apply pullback.hom_ext
      · show (_ ≫ ξ₁₂) ≫ (fst c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (fst c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.1, Category.assoc, Category.assoc, hξs.1, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_fst, lift_fst, hpr₁, (hf₁ _).1]
      · show (_ ≫ ξ₁₂) ≫ (snd c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (snd c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.2, Category.assoc, Category.assoc, hξs.2, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_snd, lift_snd, hpr₁, (hf₁ _).1]
    rw [e] at a₂
    have a₃ := LBIso.trans t.isLB (lb _ c.isLB _) (lb _ c₀.isLB _) hL a₁
    have a₄ := LBIso.trans t.isLB (lb _ c₀.isLB _) (lb _ c₁.isLB _) a₃ a₂.symm
    have a₅ := LBIso.trans (pull_isLB t₁.isLB ψ) t.isLB (lb _ c₁.isLB _) hψL.symm a₄
    exact LBIso.chartPull (chartPullId _) (chartPullOut c₁.P _ _ ψ _ fun _ => rfl) a₅
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← hψa, Category.assoc, hc, Category.assoc]
  · rw [← cancel_epi (spMap K₁.subtype), Over.comp_left, ← Category.assoc, ← hψp, Category.assoc, hc,
      ← Category.assoc, ← Over.comp_left, hp]
    exact hχl _

end GlobalTheory.SharpDescent
end
