import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquareStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartFibreConjugateIsoMumfordStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjFib

/- English proof (translation)
Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Set `ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`. Establish `ex : x₀ = ρ ≫ x` using `Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Establish `ey : y₀ = ρ ≫ y` using `Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Rewrite using `[ex, ey, ← MonObj.comp_mul]`.

Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.
-/
theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.Poinc.Sep.ConjFib

open GlobalTheory.Poinc.Sep.ConjFib in

/- English proof (translation)
Introduce `g l hl hlo W hW`. Take `⟨j₀, hj₀⟩` from `GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford g l hl hlo W hW`. Use `⟨j₀, ?_⟩` and prove the remaining obligations. Introduce `j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf hps`. Take `⟨f, f₂, hf, hfs, hfL, hfp⟩` from `hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ a p hpf hps`.

Take `⟨hpbσ, φσ₂, hsqσ⟩` from `GlobalTheory.T.isGrpPullback_baseChange_with_square F'.univ.A Q.B lam β hpb (spMap (σ.toRingHom.comp (ev.comp ρ)))`. Take `⟨-, ψ₀, hψ₀⟩` from `GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (ev.comp ρ))`. Take `⟨-, ψσ, hψσ⟩` from `GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (σ.toRingHom.comp (ev.comp ρ)))`. Rewrite `hψ₀`, `hψσ` using `[Category.comp_id]`. Use `⟨spMap (σ.toRingHom.comp (ev.comp ρ)) ≫ lam, f ≫ pullback.fst Q.B.hom _ ≫ β, f₂ ≫ φσ₂, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨P₀, hP₀⟩` from `hdef`. Establish `hk : (σ.toRingHom).comp k₀.subtype = k₀.subtype`. Use extensionality with `r`. Conclude with `hσ r r.2`. Establish `hk' : spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype`.

Rewrite using `[← spMap_comp', hk]`. Rewrite using `[spMap_comp' (ev.comp ρ) σ.toRingHom]`. Simplify using `only [Category.assoc]`. Rewrite using `[← hP₀, ← Category.assoc, hk']`. Simplify `hf.comp hpbσ` using `only [Category.id_comp]`.

Conclude with `⟨by rw [Category.assoc, hsqσ.1, ← Category.assoc, hfs.1, Category.assoc], by rw [Category.assoc, hsqσ.2, ← Category.assoc, hfs.2, Category.assoc]⟩`. Establish `e0 : φ₀₂ = ψ₀ ≫ β₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ₀₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left`. Rewrite using `[hsq0.1, Category.assoc, hsq.1, ← Category.assoc ψ₀, hψ₀.1, Category.assoc]`.

Express the relevant statement in the definitionally equal form `φ₀₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left`. Rewrite using `[hsq0.2, Category.assoc, hsq.2, ← Category.assoc ψ₀, hψ₀.2, Category.assoc]`. Establish `eσ : φσ₂ = ψσ ≫ β₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φσ₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left`.

Rewrite using `[hsqσ.1, Category.assoc, hsq.1, ← Category.assoc ψσ, hψσ.1, Category.assoc]`. Express the relevant statement in the definitionally equal form `φσ₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left`. Rewrite using `[hsqσ.2, Category.assoc, hsq.2, ← Category.assoc ψσ, hψσ.2, Category.assoc]`. Establish `hP` using `F'.univ.isLB`. Establish `hΛ : (abelian₂ Q.B Q.M.L).IsLB` using `LB.isLB_linComb (RigLB.isLB Q.M) _ _`.

Establish `hA` using `GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB ψ₀ (a' := ψ₀ ≫ β₂) rfl`. Establish `hB` using `GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB (f₂ ≫ ψσ) (a' := f₂ ≫ φσ₂) (by rw [eσ, Category.assoc])`. Rewrite using `[e0]`. Conclude with `LBIso.trans (pull_isLB hP _) (pull_isLB hΛ _) (pull_isLB hP _) (LBIso.symm hA) (LBIso.trans (pull_isLB hΛ _) (pull_isLB hΛ _) (pull_isLB hP _) (hfL ψ₀ ψσ hψ₀ hψσ) hB)`. Establish `h5` using `congrArg (· ≫ β) hfp`.

Simplify using `only [Category.assoc] at h5`. Conclude with `h5.symm`.
-/
theorem GlobalTheory.Poinc.Sep.conj_fibre_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ (φ₀₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β) φ₀₂ → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (x' : Sp K ⟶ F'.X) (φ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ F'.univ.A.left) (φ₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = spMap (ev.comp ρ) ≫ lam ≫ F'.s ∧ IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β = p ≫ φ := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf hps
  obtain ⟨f, f₂, hf, hfs, hfL, hfp⟩ :=
    hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨hpbσ, φσ₂, hsqσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square F'.univ.A Q.B lam β hpb (spMap (σ.toRingHom.comp (ev.comp ρ)))
  obtain ⟨-, ψ₀, hψ₀⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (ev.comp ρ))
  obtain ⟨-, ψσ, hψσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B)
    (spMap (σ.toRingHom.comp (ev.comp ρ)))
  rw [Category.comp_id] at hψ₀ hψσ
  refine ⟨spMap (σ.toRingHom.comp (ev.comp ρ)) ≫ lam, f ≫ pullback.fst Q.B.hom _ ≫ β, f₂ ≫ φσ₂, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P₀, hP₀⟩ := hdef
    have hk : (σ.toRingHom).comp k₀.subtype = k₀.subtype := by
      ext r; exact hσ r r.2
    have hk' : spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
      rw [← spMap_comp', hk]
    rw [spMap_comp' (ev.comp ρ) σ.toRingHom]
    simp only [Category.assoc]
    rw [← hP₀, ← Category.assoc, hk']
  · simpa only [Category.id_comp] using hf.comp hpbσ
  · exact ⟨by rw [Category.assoc, hsqσ.1, ← Category.assoc, hfs.1, Category.assoc],
      by rw [Category.assoc, hsqσ.2, ← Category.assoc, hfs.2, Category.assoc]⟩
  · have e0 : φ₀₂ = ψ₀ ≫ β₂ := by
      apply pullback.hom_ext
      · change φ₀₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsq0.1, Category.assoc, hsq.1, ← Category.assoc ψ₀, hψ₀.1, Category.assoc]
      · change φ₀₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsq0.2, Category.assoc, hsq.2, ← Category.assoc ψ₀, hψ₀.2, Category.assoc]
    have eσ : φσ₂ = ψσ ≫ β₂ := by
      apply pullback.hom_ext
      · change φσ₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsqσ.1, Category.assoc, hsq.1, ← Category.assoc ψσ, hψσ.1, Category.assoc]
      · change φσ₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsqσ.2, Category.assoc, hsq.2, ← Category.assoc ψσ, hψσ.2, Category.assoc]
    have hP := F'.univ.isLB
    have hΛ : (abelian₂ Q.B Q.M.L).IsLB := LB.isLB_linComb (RigLB.isLB Q.M) _ _
    have hA := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB ψ₀ (a' := ψ₀ ≫ β₂) rfl
    have hB := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB (f₂ ≫ ψσ) (a' := f₂ ≫ φσ₂) (by rw [eσ, Category.assoc])
    rw [e0]
    exact LBIso.trans (pull_isLB hP _) (pull_isLB hΛ _) (pull_isLB hP _) (LBIso.symm hA)
      (LBIso.trans (pull_isLB hΛ _) (pull_isLB hΛ _) (pull_isLB hP _) (hfL ψ₀ ψσ hψ₀ hψσ) hB)
  · have h5 := congrArg (· ≫ β) hfp
    simp only [Category.assoc] at h5
    exact h5.symm
