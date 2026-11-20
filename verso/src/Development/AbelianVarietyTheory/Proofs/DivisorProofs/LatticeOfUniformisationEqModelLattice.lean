import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat.UnifLat

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Use `haveI : NeZero L := ⟨hL.ne'⟩`. Establish `hu : Units.map b.toMonoidHom ζ ^ L = 1` using `by rw [← map_pow, hζ, map_one]`. Use `⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val map_one' := by simp map_mul' := fun χ χ' => by` and prove the remaining obligations. Simplify using `only [toAdd_mul, map_add, ZMod.val_add]`. Rewrite using `[← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩`.

Use `MonoidHom.ext fun χ => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Use `show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hu, one_pow]`.
-/
theorem exists_tau {o B X : Type} [CommRing o] [CommRing B] [AddCommGroup X] (b : o →+* B) (ζ : oˣ) {L : ℕ}
    (hL : 0 < L) (hζ : ζ ^ L = 1) (c : X →+ ZMod L) :
    ∃ τ : Multiplicative X →* Bˣ,
      (∀ χ, τ χ = Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ∧ τ ^ L = 1 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hu : Units.map b.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
  refine ⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val
            map_one' := by simp
            map_mul' := fun χ χ' => by
              simp only [toAdd_mul, map_add, ZMod.val_add]
              rw [← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩
  refine MonoidHom.ext fun χ => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

end GlobalTheory.Poinc.FibLat.UnifLat

open GlobalTheory.Poinc.FibLat.UnifLat in

/- English proof (translation)
Introduce `o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β' hβ hβ' hF' K _ _ _ iK hiK hKf c hc`. Use `haveI : IsSeparated G.hom := hG.separated`. Use `haveI : IsSeparated Gu.hom := hGu.separated`. Use `haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance`. Take `⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V'` from `⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩`.

Establish `hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0` using `fun x hx => by`. Rewrite `hx` using `[zero_add, pow_one]`. Conclude with `(hr _).2 (map_nonunit fV x hx)`. Take `⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left), IsGrpPullback G₀ G' (spMap r) ψ` from `⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩`. Establish `h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β)` using `(hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl`.

Establish `hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β')` using `hψ.comp hβ'`. Take `⟨s, hs1, hs2, hs3, hs4⟩` from `GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL`. Use `⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β', GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩` and prove the remaining obligations. Use `show ξ ((spMap r) (closedPoint (ResidueField V'))) = _`. Rewrite using `[spMap, Spec_closedPoint]`.

Rewrite using `[Category.assoc, hξ, spMap_comp_eq a r]`. Use `⟨fun e => ?_, fun t => ?_⟩` and prove the remaining obligations. Take `⟨F', hF1, hF2⟩` from `hF' e`. Establish `w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r`. Rewrite using `[Category.assoc, Over.w F', hψ.1.w]`.

Take `⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left` from `⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩`. Establish `hE` using `hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀ (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])`. Establish `k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left = (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left`. Rewrite using `[← Over.comp_left, hE]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Category.assoc, reassoc_of% hF₀]`. Use `_ = _ := by rw [k]`. Take `⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩` from `hc t`. Take `⟨τV, hτVv, hτV⟩` from `exists_tau a ζ hL hζ (c t)`. Take `⟨τκ, hτκv, hτκ⟩` from `exists_tau (r.comp a) ζ hL hζ (c t)`.

Establish `hchar : ∀ χ, (τ χ : K) = iK (τV χ : V')` using `fun χ => by`. Rewrite using `[hτVv]`. Use `(hτ (Multiplicative.toAdd χ)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V')` using `fun χ => by`.

Rewrite using `[hτVv, hτκv]`. Simplify using the standard rewrite rules. Establish `hτL : τ ^ L = 1` using `MonoidHom.ext fun χ => Units.ext (by`. Rewrite using `[MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτV]`. Use the proof step `simp)`.

Establish `hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV` using `(Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm`. Take `⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _` from `⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩`. Take `⟨v, hv⟩` from `ExtNear.exists_valAt ξ hext`. Take `⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _` from `⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩`. Establish `eσK : spMap iK ≫ σ = x'` using `hβ.1.hom_ext (by`.

Rewrite using `[Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx, hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])`. Use the proof step `(by rw [Category.assoc, hσG, hx'1, Category.comp_id])`. Establish `eσ'K : spMap iK ≫ σ' = x'` using `hβ'.1.hom_ext (by`. Rewrite using `[Category.assoc, hσ'β]`. Conclude with `ValAt.unique (hv.comp (spMap iK)) hx'3)`.

Use the proof step `(by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])`. Use `haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩`. Establish `eσ : σ = σ'` using `ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK) (eσK.trans eσ'K.symm)`. Set `φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ` to `(Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ`. Take `⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X, ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ))` from `⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _`.

Rewrite using `[MulEquiv.apply_symm_apply]`. Use the proof step `rfl⟩`. Establish `hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom = (Over.mk (spMap (RingHom.id (ResidueField V')))).hom`. Rewrite using `[Over.w z]`. Use `show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))`.

Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Set `z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X` to `Over.homMk z.left hz1w`. Establish `hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ))` using `fun χ => (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)`. Establish `e3` using `hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ z₁ (RingHom.id_comp _).symm hz₁`. Establish `e2` using `hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ`.

Establish `ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ` using `hβ.1.hom_ext (by`. Rewrite using `[Category.assoc, Category.assoc, hσβ, ← e2, e3]`. Use the proof step `rfl)`. Use the proof step `(by`. Rewrite using `[Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc, Over.w (z ≫ _)]`.

Conclude with `Category.id_comp _)`. Use `⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ez, eσ, Category.assoc, hσ'β]`. Conclude with `hv.comp (spMap r)`.
-/
theorem GlobalTheory.Poinc.FibLat.latAt_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β'
    hβ hβ' hF' K _ _ _ iK hiK hKf c hc
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsSeparated Gu.hom := hGu.separated
  haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance
  obtain ⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V' :=
    ⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0 := fun x hx => by
    rw [zero_add, pow_one] at hx
    exact (hr _).2 (map_nonunit fV x hx)
  obtain ⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left),
      IsGrpPullback G₀ G' (spMap r) ψ := ⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩
  have h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β) := (hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl
  have hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β') := hψ.comp hβ'
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL
  refine ⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β',
    GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩
  · show ξ ((spMap r) (closedPoint (ResidueField V'))) = _
    rw [spMap, Spec_closedPoint]
  · rw [Category.assoc, hξ, spMap_comp_eq a r]
  refine ⟨fun e => ?_, fun t => ?_⟩
  · obtain ⟨F', hF1, hF2⟩ := hF' e
    have w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r := by
      rw [Category.assoc, Over.w F', hψ.1.w]
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left :=
      ⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
    have hE := hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀
      (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])
    have k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left =
        (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left := by
      rw [← Over.comp_left, hE]
    calc (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ (ψ ≫ β') ≫ (f e).left
        = (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ ≫ F'.left ≫ β' := by rw [hF2]; simp only [Category.assoc]
      _ = ((GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left) ≫ ψ ≫ β' := by
          rw [Category.assoc, reassoc_of% hF₀]
      _ = _ := by rw [k]
  · obtain ⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩ := hc t
    obtain ⟨τV, hτVv, hτV⟩ := exists_tau a ζ hL hζ (c t)
    obtain ⟨τκ, hτκv, hτκ⟩ := exists_tau (r.comp a) ζ hL hζ (c t)
    have hchar : ∀ χ, (τ χ : K) = iK (τV χ : V') := fun χ => by
      rw [hτVv]
      refine (hτ (Multiplicative.toAdd χ)).trans ?_
      simp
    have hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V') := fun χ => by
      rw [hτVv, hτκv]
      simp
    have hτL : τ ^ L = 1 := MonoidHom.ext fun χ => Units.ext (by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← MonoidHom.pow_apply, hτV]
      simp)
    have hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV :=
      (Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm
    obtain ⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _ :=
      ⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ hext
    obtain ⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _ :=
      ⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩
    have eσK : spMap iK ≫ σ = x' := hβ.1.hom_ext (by
        rw [Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx,
          hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])
      (by rw [Category.assoc, hσG, hx'1, Category.comp_id])
    have eσ'K : spMap iK ≫ σ' = x' := hβ'.1.hom_ext (by
        rw [Category.assoc, hσ'β]; exact ValAt.unique (hv.comp (spMap iK)) hx'3)
      (by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])
    haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩
    have eσ : σ = σ' := ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK)
      (eσK.trans eσ'K.symm)
    let φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ :=
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X,
        ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ)) :=
      ⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by
        show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _
        rw [MulEquiv.apply_symm_apply]; rfl⟩
    have hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom =
        (Over.mk (spMap (RingHom.id (ResidueField V')))).hom := by
      rw [Over.w z]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))
      rw [CommRingCat.ofHom_id, Spec.map_id]
    let z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X :=
      Over.homMk z.left hz1w
    have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := fun χ =>
      (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)
    have e3 := hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ
      z₁ (RingHom.id_comp _).symm hz₁
    have e2 := hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ
    have ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ := hβ.1.hom_ext
      (by
        rw [Category.assoc, Category.assoc, hσβ, ← e2, e3]
        rfl)
      (by
        rw [Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc,
          Over.w (z ≫ _)]
        exact Category.id_comp _)
    refine ⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩
    rw [← Category.assoc, ez, eσ, Category.assoc, hσ'β]
    exact hv.comp (spMap r)
