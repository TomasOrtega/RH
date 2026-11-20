import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ G e K _ a`. Set `f` to `a ≫ (thickObj R (maximalIdeal R) e G).hom`. Set `φ` to `Spec.preimage f`. Establish `hφ : Spec.map φ = f` using `Spec.map_preimage f`. Establish `hker : ∀ r ∈ maximalIdeal R ^ (0 + 1), (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r = 0`.

Introduce `r hr`. Rewrite `hr` using `[zero_add, pow_one]`. Establish `h1 : r ^ (e + 1) ∈ maximalIdeal R ^ (e + 1)` using `Ideal.pow_mem_pow hr _`. Establish `h2 : (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r ^ (e + 1) = 0`. Rewrite using `[← map_pow, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h1, map_zero]`.

Conclude with `pow_eq_zero_iff (Nat.succ_ne_zero e) |>.1 h2`. Set `ψ : R ⧸ maximalIdeal R ^ (0 + 1) →+* K` to `Ideal.Quotient.lift _ _ hker`. Establish `hψ : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) ≫ φ`. Use extensionality with `r`. Conclude with `Ideal.Quotient.lift_mk (maximalIdeal R ^ (0 + 1)) (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) hker`.

Establish `hc : (a ≫ pullback.fst G.hom (thick R (maximalIdeal R) e)) ≫ G.hom = Spec.map (CommRingCat.ofHom ψ) ≫ thick R (maximalIdeal R) 0`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Express the relevant statement in the definitionally equal form `f ≫ _ = _`. Rewrite using `[← hφ, thick, thick, ← Spec.map_comp, ← Spec.map_comp, hψ]`. Use `⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `pullback.lift _ _ hc ≫ pullback.snd _ _ ≫ _ = a ≫ pullback.snd _ _ ≫ _`. Rewrite using `[pullback.lift_snd_assoc, ← hc, Category.assoc, pullback.condition]`.
-/
theorem exists_closedFibre_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (e : ℕ) (K : Type) [Field K] (a : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) e G).left), ∃ g : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) 0 G).left, g ≫ (fstG (maximalIdeal R) 0 G).left = a ≫ (fstG (maximalIdeal R) e G).left ∧ g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = a ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
  intro R _ _ _ G e K _ a
  let f := a ≫ (thickObj R (maximalIdeal R) e G).hom
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have hker : ∀ r ∈ maximalIdeal R ^ (0 + 1),
      (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r = 0 := by
    intro r hr
    rw [zero_add, pow_one] at hr
    have h1 : r ^ (e + 1) ∈ maximalIdeal R ^ (e + 1) := Ideal.pow_mem_pow hr _
    have h2 : (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r ^ (e + 1) = 0 := by
      rw [← map_pow, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h1, map_zero]
    exact pow_eq_zero_iff (Nat.succ_ne_zero e) |>.1 h2
  let ψ : R ⧸ maximalIdeal R ^ (0 + 1) →+* K := Ideal.Quotient.lift _ _ hker
  have hψ : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) ≫ φ := by
    ext r
    exact Ideal.Quotient.lift_mk (maximalIdeal R ^ (0 + 1)) (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) hker
  have hc : (a ≫ pullback.fst G.hom (thick R (maximalIdeal R) e)) ≫ G.hom =
      Spec.map (CommRingCat.ofHom ψ) ≫ thick R (maximalIdeal R) 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change f ≫ _ = _
    rw [← hφ, thick, thick, ← Spec.map_comp, ← Spec.map_comp, hψ]
  refine ⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, ?_⟩
  change pullback.lift _ _ hc ≫ pullback.snd _ _ ≫ _ = a ≫ pullback.snd _ _ ≫ _
  rw [pullback.lift_snd_assoc, ← hc, Category.assoc, pullback.condition]

/- English proof (translation)
Introduce `R _ _ _ hB D A G _ _ hG U`. Take `⟨Y⟩ : Nonempty (Ext D.toPre)` from `inferInstance`. Take `⟨S, k₁, hk₁⟩` from `GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y`. Use `choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1`. Use `⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩` and prove the remaining obligations.

Introduce `e k hk Z u u' hu s₀ i i'' z h`. Establish `hk3 : 3 ≤ k` using `le_trans (le_max_left _ _) hk`. Establish `hkk₁ : k₁ ≤ k` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk`. Establish `hkS : S.sup k₀f ≤ k` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk`. Take `⟨N, α, b, τ, hτ, hαb, himm⟩` from `hk₁ k hkk₁`.

Establish `hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j)` using `fun j => hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)`. Use `choose F hF using hF`. Establish `hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f` using `fun j => IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)`. Use `choose s hs using hs`. Take `⟨hzi, hzi'', hu0, hu0', hrat⟩` from `h`.

Use `set p := (fstG (maximalIdeal R) e G).left with hp`. Establish `minor : ∀ j l, secGerm (u ≫ p) z (s j) i * secGerm (u' ≫ p) z (s l) i'' = secGerm (u ≫ p) z (s l) i * secGerm (u' ≫ p) z (s j) i''`. Introduce `j l`. Establish `h1` using `hrat (s j)`. Establish `h2` using `hrat (s l)`.

Apply `(hu0.mul hu0').mul_left_cancel` to reduce the goal to its premises. Take the linear combination `(secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s l) i'') * h1 - (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s j) i'') * h2`. Set `K` to `Z.residueField z`. Set `x : Spec (CommRingCat.of K) ⟶ Z` to `Z.fromSpecResidueField z`. Take `⟨pt⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`.

Establish `hx : x pt = z` using `Scheme.fromSpecResidueField_apply z pt`. Establish `minorx : ∀ j l, secGerm (x ≫ u ≫ p) pt (s j) i * secGerm (x ≫ u' ≫ p) pt (s l) i'' = secGerm (x ≫ u ≫ p) pt (s l) i * secGerm (x ≫ u' ≫ p) pt (s j) i''`. Introduce `j l`. Establish `hi : (u ≫ p) (x pt) ∈ secChart U.LG.L i` using `hx ▸ hzi`. Establish `hi'' : (u' ≫ p) (x pt) ∈ secChart U.LG.L i''` using `hx ▸ hzi''`.

Establish `m` using `hx ▸ minor j l`. Rewrite using `[secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u' ≫ p) pt _ hi'', secGerm_comp x (u' ≫ p) pt _ hi'', ← map_mul, ← map_mul, m]`. Take `⟨g, hg1, hg2⟩` from `exists_closedFibre_factor R G e K (x ≫ u)`. Take `⟨g', hg1', hg2'⟩` from `exists_closedFibre_factor R G e K (x ≫ u')`. Set `T : Over (Sp R)` to `Over.mk ((x ≫ u) ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e)`.

Establish `hgT : g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom` using `hg2`. Establish `hgT' : g' ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom`. Rewrite using `[hg2']`. Use `show _ = (x ≫ u) ≫ _`. Simplify using `only [Category.assoc, ← reassoc_of% hu]`.

Take `⟨ξ, hξ⟩` from `GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g hgT`. Take `⟨ξ', hξ'⟩` from `GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g' hgT'`. Use `set y := (Y.Φ T).symm ξ with hy`. Use `set y' := (Y.Φ T).symm ξ' with hy'`. Establish `hyξ : Y.Φ T y = ξ` using `Equiv.apply_symm_apply _ _`.

Establish `hyξ' : Y.Φ T y' = ξ'` using `Equiv.apply_symm_apply _ _`. Take `⟨J, hJ⟩` from `GlobalTheory.TorusCoord.exists_good' U.LG.isLB pt`. Take `⟨J', hJ'⟩` from `GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB pt`. Take `⟨c, hc⟩` from `GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g y (hyξ ▸ hξ) k pt J J' hJ hJ'`. Take `⟨c', hc'⟩` from `GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g' y' (hyξ' ▸ hξ') k pt J J' hJ hJ'`.

Establish `hv : ∀ j, secGerm (x ≫ u ≫ p) pt (s j) (fun _ => J ((x ≫ u ≫ p) ≫ 𝟙 _)) = c.val * sval (τ j) y.left pt J'`. Introduce `j`. Use `hc (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)` as an intermediate fact. Rewrite `this` using `[hg1, Category.assoc]`. Conclude with `this`.

Establish `hv' : ∀ j, secGerm (x ≫ u' ≫ p) pt (s j) (fun _ => J ((x ≫ u' ≫ p) ≫ 𝟙 _)) = c'.val * sval (τ j) y'.left pt J'`. Introduce `j`. Use `hc' (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)` as an intermediate fact. Rewrite `this` using `[hg1', Category.assoc]`. Conclude with `this`.

Establish `hi : (x ≫ u ≫ p) pt ∈ secChart U.LG.L i`. Rewrite using `[Scheme.Hom.comp_apply, hx]`. Conclude with `hzi`. Establish `hi'' : (x ≫ u' ≫ p) pt ∈ secChart U.LG.L i''`. Rewrite using `[Scheme.Hom.comp_apply, hx]`.

Conclude with `hzi''`. Take `⟨a, ha⟩` from `exists_unit_secGerm k (x ≫ u ≫ p) pt hi (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u ≫ p))`. Take `⟨a', ha'⟩` from `exists_unit_secGerm k (x ≫ u' ≫ p) pt hi'' (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u' ≫ p))`. Establish `minorτ : ∀ j l, sval (τ j) y.left pt J' * sval (τ l) y'.left pt J' = sval (τ l) y.left pt J' * sval (τ j) y'.left pt J'`. Introduce `j l`.

Establish `m` using `minorx j l`. Rewrite `m` using `[ha, ha, ha', ha', hv, hv, hv', hv']`. Apply `(((a.isUnit.mul a'.isUnit).mul c.isUnit).mul c'.isUnit).mul_left_cancel` to reduce the goal to its premises. Take the linear combination `m`. Take `⟨W, hW, hWy⟩` from `GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios R D.toPre Y k N τ hτ himm T y y' pt J' hJ' minorτ`.

Establish `hWt : W = ⊤`. Conclude with `eq_top_iff.2 fun q _ => (Subsingleton.elim (α := Spec (CommRingCat.of K)) q pt) ▸ hW`. Substitute `hWt` using the available equality. Establish `: IsIso (⊤ : (T.left).Opens).ι` using `by rw [← Scheme.topIso_hom]; infer_instance`. Establish `hyy : y = y'` using `Over.OverMorphism.ext ((cancel_epi _).1 hWy)`.

Establish `hξξ : ξ = ξ'` using `by rw [← hyξ, ← hyξ', hyy]`. Establish `hgg : g = g'` using `GlobalTheory.TorusCoord.IsPointOf.unique_left (U.gt 0) hξ (hξξ ▸ hξ')`. Establish `hpp : (x ≫ u ≫ p) pt = (x ≫ u' ≫ p) pt`. Rewrite using `[← Category.assoc, ← hg1, ← Category.assoc, ← hg1', hgg]`. Rewrite `hpp` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]`.

Establish `: IsClosedImmersion p` using `by show IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e))`. Establish `: IsClosedImmersion (thick R (maximalIdeal R) e)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `infer_instance`. Conclude with `p.isClosedEmbedding.injective hpp`.
-/
theorem eq_of_germRatioAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro e k hk Z u u' hu s₀ i i'' z h
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  obtain ⟨hzi, hzi'', hu0, hu0', hrat⟩ := h
  set p := (fstG (maximalIdeal R) e G).left with hp
  have minor : ∀ j l, secGerm (u ≫ p) z (s j) i * secGerm (u' ≫ p) z (s l) i'' =
      secGerm (u ≫ p) z (s l) i * secGerm (u' ≫ p) z (s j) i'' := by
    intro j l
    have h1 := hrat (s j)
    have h2 := hrat (s l)
    apply (hu0.mul hu0').mul_left_cancel
    linear_combination (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s l) i'') * h1 -
      (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s j) i'') * h2

  let K := Z.residueField z
  let x : Spec (CommRingCat.of K) ⟶ Z := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hx : x pt = z := Scheme.fromSpecResidueField_apply z pt
  have minorx : ∀ j l, secGerm (x ≫ u ≫ p) pt (s j) i * secGerm (x ≫ u' ≫ p) pt (s l) i'' =
      secGerm (x ≫ u ≫ p) pt (s l) i * secGerm (x ≫ u' ≫ p) pt (s j) i'' := by
    intro j l
    have hi : (u ≫ p) (x pt) ∈ secChart U.LG.L i := hx ▸ hzi
    have hi'' : (u' ≫ p) (x pt) ∈ secChart U.LG.L i'' := hx ▸ hzi''
    have m := hx ▸ minor j l
    rw [secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u' ≫ p) pt _ hi'',
      secGerm_comp x (u' ≫ p) pt _ hi'', ← map_mul, ← map_mul, m]

  obtain ⟨g, hg1, hg2⟩ := exists_closedFibre_factor R G e K (x ≫ u)
  obtain ⟨g', hg1', hg2'⟩ := exists_closedFibre_factor R G e K (x ≫ u')
  let T : Over (Sp R) := Over.mk ((x ≫ u) ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e)
  have hgT : g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := hg2
  have hgT' : g' ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := by
    rw [hg2']; show _ = (x ≫ u) ≫ _
    simp only [Category.assoc, ← reassoc_of% hu]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g hgT
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g' hgT'
  set y := (Y.Φ T).symm ξ with hy
  set y' := (Y.Φ T).symm ξ' with hy'
  have hyξ : Y.Φ T y = ξ := Equiv.apply_symm_apply _ _
  have hyξ' : Y.Φ T y' = ξ' := Equiv.apply_symm_apply _ _
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB pt
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB pt
  obtain ⟨c, hc⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g y (hyξ ▸ hξ) k pt J J' hJ hJ'
  obtain ⟨c', hc'⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g' y' (hyξ' ▸ hξ') k pt J J' hJ hJ'
  have hv : ∀ j, secGerm (x ≫ u ≫ p) pt (s j) (fun _ => J ((x ≫ u ≫ p) ≫ 𝟙 _)) = c.val * sval (τ j) y.left pt J' := by
    intro j
    have := hc (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1, Category.assoc] at this
    exact this
  have hv' : ∀ j, secGerm (x ≫ u' ≫ p) pt (s j) (fun _ => J ((x ≫ u' ≫ p) ≫ 𝟙 _)) = c'.val * sval (τ j) y'.left pt J' := by
    intro j
    have := hc' (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1', Category.assoc] at this
    exact this
  have hi : (x ≫ u ≫ p) pt ∈ secChart U.LG.L i := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi
  have hi'' : (x ≫ u' ≫ p) pt ∈ secChart U.LG.L i'' := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi''
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (x ≫ u ≫ p) pt hi (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u ≫ p))
  obtain ⟨a', ha'⟩ := exists_unit_secGerm k (x ≫ u' ≫ p) pt hi'' (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u' ≫ p))
  have minorτ : ∀ j l, sval (τ j) y.left pt J' * sval (τ l) y'.left pt J' = sval (τ l) y.left pt J' * sval (τ j) y'.left pt J' := by
    intro j l
    have m := minorx j l
    rw [ha, ha, ha', ha', hv, hv, hv', hv'] at m
    apply (((a.isUnit.mul a'.isUnit).mul c.isUnit).mul c'.isUnit).mul_left_cancel
    linear_combination m
  obtain ⟨W, hW, hWy⟩ := GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios R D.toPre Y k N τ hτ himm T y y' pt J' hJ' minorτ
  have hWt : W = ⊤ := by
    exact eq_top_iff.2 fun q _ => (Subsingleton.elim (α := Spec (CommRingCat.of K)) q pt) ▸ hW
  subst hWt
  have : IsIso (⊤ : (T.left).Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hyy : y = y' := Over.OverMorphism.ext ((cancel_epi _).1 hWy)
  have hξξ : ξ = ξ' := by rw [← hyξ, ← hyξ', hyy]
  have hgg : g = g' := GlobalTheory.TorusCoord.IsPointOf.unique_left (U.gt 0) hξ (hξξ ▸ hξ')
  have hpp : (x ≫ u ≫ p) pt = (x ≫ u' ≫ p) pt := by
    rw [← Category.assoc, ← hg1, ← Category.assoc, ← hg1', hgg]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx] at hpp
  have : IsClosedImmersion p := by
    show IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e))
    have : IsClosedImmersion (thick R (maximalIdeal R) e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  exact p.isClosedEmbedding.injective hpp

end GlobalTheory.Mum
