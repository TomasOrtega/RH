import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.OrthKer

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `H`.
-/
theorem fibreDescent_transport' {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H

open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Chart in

/- English proof (translation)
Set `A : Over (Spec (CommRingCat.of K))` to `(Over.pullback f).obj G`. Set `ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t), (T ⟶ A) ≃* (Over.mk t ⟶ G)` to `fun T t ht => TorsionLift.ptsEquiv f G T t ht`. Establish `hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f` using `fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x`. Establish `hA : A.hom ≫ f = (G ⊗ Over.mk f).hom` using `Limits.pullback.condition.symm`. Establish `hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f)` using `Over.OverMorphism.ext (by`.

Rewrite using `[hρ]`. Conclude with `Category.id_comp _)`. Establish `ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f), v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left`. Introduce `u v h1 h2`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises.

Conclude with `(congrArg (·.left) h1).trans (hρ _ _ _ _)`. Conclude with `(congrArg (·.left) h2).trans (Over.w u).symm`. Establish `hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left`. Use `ext _ _ ?_ (whiskerRight_snd _ _)` and prove the remaining obligations. Rewrite using `[map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]`.

Establish `hAb : IsAbelianScheme A` using `TLinPf.isAb_pullback f G hG`. Establish `hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤))`. Simplify using `using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Take `⟨-, h3, h1, h2⟩` from `abelianScheme_id_pow_finite_etale_surjective _ A N hAb hu`. Use `fibreDescent_transport' hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧ t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_` and prove the remaining obligations.

Introduce `V a ha`. Use `existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_` and prove the remaining obligations. Use `ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩` and prove the remaining obligations. Use `(ext _ _ ?_ (lift_snd _ _)).symm` and prove the remaining obligations. Rewrite using `[lift_fst, map_mul, hid, _root_.mul_comm]`.

Use `congr 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `ha y hy`.
-/
theorem descends_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (hN : (N : K) ≠ 0)
    (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V))
    (ha : ∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤
      (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ
        ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V),
      ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) :
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a := by
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hAb : IsAbelianScheme A := TLinPf.isAb_pullback f G hG
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, h3, h1, h2⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hAb hu
  refine fibreDescent_transport' hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy

/- English proof (translation)
Introduce `K _ _ S t A _ _ hA L c n hn x hx hp`. Set `T : Over S` to `Over.mk t`. Set `m : A ⊗ T ⟶ A ⊗ T` to `((𝟙 A) ^ n : A ⟶ A) ▷ T`. Establish `m₁ : m ≫ fst A T = fst A T ^ n`. Rewrite using `[whiskerRight_fst, MonObj.comp_pow, Category.comp_id]`.

Establish `m₂ : m ≫ snd A T ≫ x = snd A T ≫ x` using `by rw [whiskerRight_snd_assoc]`. Set `ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left)` to `![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]`. Take `⟨σ, hσ, hv⟩` from `CubNondeg.exists_sigma c n (fst A T) (snd A T ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by`. Use function extensionality and compare the values at `k`. Use `fin_cases k`.

Use `show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left`. Rewrite using `[MonObj.comp_mul, m₁, m₂]`. Conclude with `congrArg (fun q => q.left) m₁`. Conclude with `congrArg (fun q => q.left) m₂`. Conclude with `congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))`.

Take `⟨u, hu⟩` from `CubNondeg.descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1}) (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Use `ext1`. Rewrite using `[Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]`.

Simplify using `[m])`. Use the proof step `(fun V a ha => descends_fibre S A hA K t n hn V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ`. Use the proof step `(fun y z J hJ => by`. Establish `e₁` using `hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ`. Establish `e₂` using `hv _ (𝟙 (A ⊗ T)) z J hJ`.

Rewrite `e₁` using `[lift_fst, lift_snd_assoc]`. Rewrite `e₂` using `[Category.id_comp, Category.id_comp]`. Establish `w` using `(hp y.1 y.2).comp (snd A T)`. Establish `w'` using `w.2.2 z J hJ`. Rewrite `w'` using `[map_one, map_one, _root_.one_mul]`.

Conclude with `e₁.trans ((CubNondeg.ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))`. Take `⟨g, hg⟩` from `DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]`. Set `s : T ⊗ A ⟶ A ⊗ T` to `lift (snd T A) (fst T A)`. Establish `s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left` using `by show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left`. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]`.

Establish `s₁ : s.left ≫ ψ 1 = (snd T A).left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)`. Establish `s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)`. Establish `s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)`. Take `⟨w, hw, -⟩` from `exists_gen L.isLB (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1]) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans ?_` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]`. Use `show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) * h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) * h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) = h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd …`. Rewrite using `[s₀, s₁, s₂, s₃]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`.

Use the proof step `module)`. Use the proof step `(LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))`. Conclude with `⟨w, hw⟩`.
-/
theorem mem_kernel_of_cubWeil_orthogonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) (p : Sp K ⟶ S) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ), (N : K) ≠ 0 → ∀ x : Over.mk p ⟶ B, x ^ N = 1 → (∀ y : Over.mk p ⟶ B, y ^ N = 1 → CubWeil c N x y 1) → Triv (translDiff B L.L x) := by
  intro K _ _ S t A _ _ hA L c n hn x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := CubNondeg.exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := CubNondeg.descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => descends_fibre S A hA K t n hn V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ
    (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((CubNondeg.ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.OrthKer
end
