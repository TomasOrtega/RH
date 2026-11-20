import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Use `show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _`. Rewrite using `[Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]`.
-/
theorem jFK_self : jFK (R := R) (FractionRing R) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

def rhoK : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) (by
    show _ ≫ (jFK (R := R) (FractionRing R) ≫ jK R) = jFK (R := R) F ≫ jK R
    rw [jFK_self, Category.id_comp])

/- English proof (translation)
Rewrite using `[jFK_self]`. Use `erw [Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem rhoK_jFK : (rhoK F).left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  rw [jFK_self]; erw [Category.comp_id]; rfl

variable (D : DegPre R)

abbrev bcA : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) := rhoK F ▷ D.P.A

/- English proof (translation)
The claim follows from `whiskerRight_fst _ _`.
-/
theorem bcA_fst : bcA F D ≫ fst _ _ = fst _ _ ≫ rhoK F := whiskerRight_fst _ _

/- English proof (translation)
The claim follows from `whiskerRight_snd _ _`.
-/
theorem bcA_snd : bcA F D ≫ snd _ _ = snd _ _ := whiskerRight_snd _ _

/- English proof (translation)
Rewrite using `[trF_eq, trF_eq]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, tr_fst, bcA_fst, Category.assoc, bcA_fst, ← Category.assoc, tr_fst]`. Rewrite using `[Category.assoc, tr_pr, MonObj.comp_mul, bcA_snd, ← Category.assoc, bcA_fst, Category.assoc, comp_cP, Category.assoc, bcA_snd, tr_pr]`.
-/
theorem bcA_tr (mu : D.X) : bcA F D ≫ DegPre.trF D (FractionRing R) mu = DegPre.trF D F mu ≫ bcA F D := by
  rw [trF_eq, trF_eq]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, bcA_fst, Category.assoc, bcA_fst, ← Category.assoc, tr_fst]
  · rw [Category.assoc, tr_pr, MonObj.comp_mul, bcA_snd, ← Category.assoc, bcA_fst, Category.assoc, comp_cP,
      Category.assoc, bcA_snd, tr_pr]

/- English proof (translation)
Introduce `U _ h` and use `Finset.prod_congr rfl fun i _ => by dsimp only rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, ← Over.comp_left, bcA_snd]`.
-/
theorem formBC (k : ℕ) (α : D.X) :
    FormEq (fun i => (bcA F D).left ≫ DegPre.famφ D (FractionRing R) α i) (DegPre.famε k)
      (DegPre.famφ D F α) (DegPre.famε k) := fun U _ h =>
  Finset.prod_congr rfl fun i _ => by
    dsimp only
    rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, ← Over.comp_left, bcA_snd]

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Use `choose t ht using fun α => exists_sec hL (formBC F D k α) (pullSec D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (bcA F D).left)`. Establish `ht' : ∀ α (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) J, Good D.P.L z J → sval (t α) r z J = sval (s.s α) (r ≫ (bcA F D).left) z J` using `fun α Z r z J hJ => (ht α Z r z J hJ).trans (sval_pullSec _ _ _ _ _ _ hJ)`. Establish `fe : DegPre.FamFE D F k t`. Introduce `mu α u hu hc`.

Use `(secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_` and prove the remaining obligations. Take `⟨⟨uK, huK, hcK⟩, -⟩` from `gen_fe (D := D) (F := FractionRing R) hG k mu α`. Establish `rK` using `(secRel_iff hL _ _ _ _ _ _ _ _ _ uK).1 (s.fe mu α uK huK hcK) _ (bcA F D).left y J hJ`. Establish `vF` using `(gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ`. Establish `vK` using `(gen_fe (D := D) (F := FractionRing R) hG k mu α).2 uK huK hcK _ (bcA F D) y J hJ`.

Rewrite `vF` using `[Over.id_left]`. Rewrite using `[ht' _ _ _ y J hJ, ht' _ _ _ y J hJ]`. Simplify using `only [Category.id_comp]`. Rewrite using `[rK, ← Over.comp_left, bcA_tr, Over.comp_left, vF, vK]`. Establish `e1 : bcA F D ≫ fst _ _ ≫ cP D (TF (R` using `R) (FractionRing R)) mu = cP D _ mu := by`.

Rewrite using `[← Category.assoc, comp_cP]`. Establish `e2 : 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ cP D (TF (R` using `R) F) mu = cP D _ mu := by`. Rewrite using `[Category.id_comp, comp_cP]`. Establish `e3 : bcA F D ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F` using `bcA_snd F D`. Establish `e4 : 𝟙 (DegPre.BF D F) ≫ DegPre.prB D F = DegPre.prB D F` using `Category.id_comp _`.

Establish `e5 : ((bcA F D ≫ fst _ _).left ≫ jFK (R` using `R) (FractionRing R)) = (𝟙 _ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F := by`. Rewrite using `[bcA_fst, Over.comp_left, Category.assoc, rhoK_jFK, Category.id_comp]`. Unfold `uVal`. Rewrite using `[e1, e2, e3, e4]`. Use `congr 1`.

Rewrite using `[val_famMult _ hJ, val_famMult _ hJ, e5]`. Conclude with `⟨⟨t, fe⟩, ht'⟩`.
-/
theorem famBC (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) :
    ∃ s' : Fam D F k, ∀ α (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) J, Good D.P.L z J →
      sval (s'.s α) r z J = sval (s.s α) (r ≫ (bcA F D).left) z J := by
  have hL := D.P.isLB
  choose t ht using fun α => exists_sec hL (formBC F D k α)
    (pullSec D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (bcA F D).left)
  have ht' : ∀ α (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) J, Good D.P.L z J →
      sval (t α) r z J = sval (s.s α) (r ≫ (bcA F D).left) z J := fun α Z r z J hJ =>
    (ht α Z r z J hJ).trans (sval_pullSec _ _ _ _ _ _ hJ)
  have fe : DegPre.FamFE D F k t := by
    intro mu α u hu hc
    refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    obtain ⟨⟨uK, huK, hcK⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG k mu α
    have rK := (secRel_iff hL _ _ _ _ _ _ _ _ _ uK).1 (s.fe mu α uK huK hcK) _ (bcA F D).left y J hJ
    have vF := (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ
    have vK := (gen_fe (D := D) (F := FractionRing R) hG k mu α).2 uK huK hcK _ (bcA F D) y J hJ
    rw [Over.id_left] at vF
    rw [ht' _ _ _ y J hJ, ht' _ _ _ y J hJ]
    simp only [Category.id_comp]
    rw [rK, ← Over.comp_left, bcA_tr, Over.comp_left, vF, vK]
    have e1 : bcA F D ≫ fst _ _ ≫ cP D (TF (R := R) (FractionRing R)) mu = cP D _ mu := by
      rw [← Category.assoc, comp_cP]
    have e2 : 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ cP D (TF (R := R) F) mu = cP D _ mu := by
      rw [Category.id_comp, comp_cP]
    have e3 : bcA F D ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F := bcA_snd F D
    have e4 : 𝟙 (DegPre.BF D F) ≫ DegPre.prB D F = DegPre.prB D F := Category.id_comp _
    have e5 : ((bcA F D ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R)) =
        (𝟙 _ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F := by
      rw [bcA_fst, Over.comp_left, Category.assoc, rhoK_jFK, Category.id_comp]
    unfold uVal
    rw [e1, e2, e3, e4]
    congr 1
    rw [val_famMult _ hJ, val_famMult _ hJ, e5]
  exact ⟨⟨t, fe⟩, ht'⟩

section Descent

open IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := V) x`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Take `⟨m1, u1, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`.

Take `⟨m2, u2, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ`. Use `⟨(m1 : ℤ) - m2, u1 * u2⁻¹, ?_⟩` and prove the remaining obligations. Establish `hp : algebraMap V (FractionRing V) ϖ ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap V (FractionRing V))]`. Conclude with `fun h => hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) h)`.

Establish `hu2 : algebraMap V (FractionRing V) (u2 : V) ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap V (FractionRing V))]`. Conclude with `fun h => u2.ne_zero (IsFractionRing.injective V (FractionRing V) h)`. Establish `hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u2 : V))⁻¹` using `eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])`. Simplify using `only [Units.val_mul, map_mul, map_pow, hinv]`.

Rewrite using `[zpow_sub₀ hp, zpow_natCast, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_hasVal {ϖ : V} (hϖ : Irreducible ϖ) (x : FractionRing V) (hx : x ≠ 0) : ∃ n : ℤ, HasVal ϖ x n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨m1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨m2, u2, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨(m1 : ℤ) - m2, u1 * u2⁻¹, ?_⟩
  have hp : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hu2 : algebraMap V (FractionRing V) (u2 : V) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => u2.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) =
      (algebraMap V (FractionRing V) (u2 : V))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, hinv]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
  field_simp

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, map_zero, AddValuation.map_zero, AddValuation.map_zero]`. Take `⟨n, hn⟩` from `exists_hasVal hϖ x hx`. Rewrite using `[hv x n hn]`. Use `hvK x n hn` as an intermediate fact.

Rewrite `this` using `[Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `this.symm`.
-/
theorem v_alg {ϖ : V} (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {vK : AddValuation (FractionRing V) (WithTop ℚ)}
    (hvK : ValOver ϖ (FractionRing V) vK) (x : FractionRing V) : v (algebraMap (FractionRing V) F x) = vK x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, AddValuation.map_zero, AddValuation.map_zero]
  obtain ⟨n, hn⟩ := exists_hasVal hϖ x hx
  rw [hv x n hn]
  have := hvK x n hn
  rw [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this.symm

variable {D : DegData V (maximalIdeal V)} (F : Type) [Field F] [Algebra (FractionRing V) F]

/- English proof (translation)
Rewrite using `[gF_gs, gF, RingHom.comp_apply]`. Use `(gs_pull _ _ y ⊤ trivial _).trans ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, bcA_fst, Over.comp_left]`. Use `(gs_pull _ _ y ⊤ trivial _).symm.trans ?_` and prove the remaining obligations. Use `congr 1`.

Use `congrArg (fun f => f.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing V) F)))` as an intermediate fact. Conclude with `this.symm`.
-/
theorem gF_bc (c : FractionRing V) (y : (DegPre.BF D.toPre F).left) :
    gs (bcA F D.toPre).left y ⊤ (gF D.toPre (FractionRing V) c) =
      gs (𝟙 _) y ⊤ (gF D.toPre F (algebraMap (FractionRing V) F c)) := by
  rw [gF_gs, gF, RingHom.comp_apply]
  refine (gs_pull _ _ y ⊤ trivial _).trans ?_
  rw [← Over.comp_left, bcA_fst, Over.comp_left]
  refine (gs_pull _ _ y ⊤ trivial _).symm.trans ?_
  congr 1
  have := congrArg (fun f => f.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (FractionRing V) F)))
  exact this.symm

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Take `⟨m, b, hm, hb⟩` from `hT V D.toPre k hk α`. Substitute `hm` using the available equality. Establish `exB : ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] (i : Fin (k ^ D.toPre.P.g)), ∃ bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F' α) (DegPre.famε k)), ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F').left) (z : Z) J, Good D.toPre.P.L z J → sval bF r z J = …` using `fun F' _ _ i => by`. Take `⟨t0, ht0⟩` from `exists_sec hL (hformF (F := F') k α) (pullSec D.toPre.P.L (DegPre.famφB D.toPre α) (DegPre.famε k) (b i) (DegPre.prB D.toPre F').left)`.

Conclude with `⟨t0, fun Z r z J hJ => (ht0 Z r z J hJ).trans (sval_pullSec _ _ _ _ _ _ hJ)⟩`. Use `choose bK hbK using exB (FractionRing V)`. Use `choose bF hbF using exB F`. Establish `hbK1 : ∀ i (y : (DegPre.BF D.toPre (FractionRing V)).left) J, Good D.toPre.P.L y J → sval (bK i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre (FractionRing V)).left y J` using `fun i y J hJ => (hbK i _ _ y J hJ).trans (by rw [Category.id_comp])`. Establish `hbF1 : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J → sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J` using `fun i y J hJ => (hbF i _ _ y J hJ).trans (by rw [Category.id_comp])`.

Take `⟨hEK, -⟩` from `coordsF (F := FractionRing V) b hb bK hbK1`. Take `⟨-, hUF⟩` from `coordsF (F := F) b hb bF hbF1`. Take `⟨cK, hcK⟩` from `hEK t`. Establish `hch` using `chart_of_point hL t (fun i => gF D.toPre (FractionRing V) (cK i)) bK hcK`. Establish `hrep : RepF bF t' (fun i => algebraMap (FractionRing V) F (cK i))` using `fun y J hJ => by`.

Rewrite using `[htt y J hJ, sval_lin (fun i => gF D.toPre (FractionRing V) (cK i)) bK hch (bcA F D.toPre).left y hJ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[gF_bc, hbK i _ _ y J hJ, hbF1 i y J hJ, ← Over.comp_left, bcA_snd]`. Apply the tactic sequence `try rfl`. Establish `hvv` using `vge_coords hϖ hv b hb bF hbF1 hUF hrep h`.

Use `⟨k ^ D.toPre.P.g, cK, b, bK, fun i => secScal_of_sval hL fun y J hJ => ?_, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Conclude with `(hbK1 i y J hJ).symm`. Rewrite using `[← v_alg hϖ hv hvK]`. Conclude with `hvv i`.

Rewrite using `[hch j]`. Apply the tactic sequence `try rfl`.
-/
theorem vge_descent (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ)
    {vK : AddValuation (FractionRing V) (WithTop ℚ)} (hvK : ValOver ϖ (FractionRing V) vK)
    {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k)))
    (t' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)))
    (htt : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval t' (𝟙 _) y J = sval t (bcA F D.toPre).left y J)
    {r : ℚ} (h : VGe D F v k α t' r) : VGe D (FractionRing V) vK k α t r := by
  have hL := D.toPre.P.isLB
  obtain ⟨m, b, hm, hb⟩ := hT V D.toPre k hk α
  subst hm
  have exB : ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] (i : Fin (k ^ D.toPre.P.g)),
      ∃ bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F' α) (DegPre.famε k)),
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F').left) (z : Z) J, Good D.toPre.P.L z J →
          sval bF r z J = sval (b i) (r ≫ (DegPre.prB D.toPre F').left) z J := fun F' _ _ i => by
    obtain ⟨t0, ht0⟩ := exists_sec hL (hformF (F := F') k α)
      (pullSec D.toPre.P.L (DegPre.famφB D.toPre α) (DegPre.famε k) (b i) (DegPre.prB D.toPre F').left)
    exact ⟨t0, fun Z r z J hJ => (ht0 Z r z J hJ).trans (sval_pullSec _ _ _ _ _ _ hJ)⟩
  choose bK hbK using exB (FractionRing V)
  choose bF hbF using exB F
  have hbK1 : ∀ i (y : (DegPre.BF D.toPre (FractionRing V)).left) J, Good D.toPre.P.L y J →
      sval (bK i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre (FractionRing V)).left y J := fun i y J hJ =>
    (hbK i _ _ y J hJ).trans (by rw [Category.id_comp])
  have hbF1 : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J := fun i y J hJ =>
    (hbF i _ _ y J hJ).trans (by rw [Category.id_comp])
  obtain ⟨hEK, -⟩ := coordsF (F := FractionRing V) b hb bK hbK1
  obtain ⟨-, hUF⟩ := coordsF (F := F) b hb bF hbF1
  obtain ⟨cK, hcK⟩ := hEK t
  have hch := chart_of_point hL t (fun i => gF D.toPre (FractionRing V) (cK i)) bK hcK
  have hrep : RepF bF t' (fun i => algebraMap (FractionRing V) F (cK i)) := fun y J hJ => by
    rw [htt y J hJ, sval_lin (fun i => gF D.toPre (FractionRing V) (cK i)) bK hch (bcA F D.toPre).left y hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gF_bc, hbK i _ _ y J hJ, hbF1 i y J hJ, ← Over.comp_left, bcA_snd]
    try rfl
  have hvv := vge_coords hϖ hv b hb bF hbF1 hUF hrep h
  refine ⟨k ^ D.toPre.P.g, cK, b, bK, fun i => secScal_of_sval hL fun y J hJ => ?_, fun i => ?_, fun j => ?_⟩
  · rw [Category.id_comp]; exact (hbK1 i y J hJ).symm
  · rw [← v_alg hϖ hv hvK]; exact hvv i
  · rw [hch j]; try rfl

end Descent

def NuDescentSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
  ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
  ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre (FractionRing V) k) (s' : Fam D.toPre F k),
    (∀ α (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (s'.s α) (𝟙 _) y J = sval (s.s α) (bcA F D.toPre).left y J) →
    NuGe D Q F v k s' 0 → NuGe D Q (FractionRing V) vK k s 0

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ D Q hQ vK hvK F _ _ v hv k hk s s' hss hs'`. Take `⟨rep, hcov, -, -⟩` from `reps_X (X := D.toPre.X) k hk`. Set `S : Finset D.toPre.X` to `Finset.univ.image rep`. Establish `hS : ∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0` using `fun χ => by`. Take `⟨a, mu, h⟩` from `hcov χ`.

Conclude with `⟨rep a, Finset.mem_image_of_mem _ (Finset.mem_univ _), mu, h.symm⟩`. Use `(n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK k hk S hS s 0).2 fun α hα => ?_` and prove the remaining obligations. Conclude with `vge_descent F hT hϖ hvK hv hk (s.s α) (s'.s α) (hss α) ((n1a V ϖ hϖ D Q hQ F v hv k hk S hS s' 0).1 hs' α hα)`.
-/
theorem nuDescent (hT : TwistBaseChangeStatement) : NuDescentSt := by
  intro V _ _ _ ϖ hϖ D Q hQ vK hvK F _ _ v hv k hk s s' hss hs'
  classical
  obtain ⟨rep, hcov, -, -⟩ := reps_X (X := D.toPre.X) k hk
  let S : Finset D.toPre.X := Finset.univ.image rep
  have hS : ∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0 := fun χ => by
    obtain ⟨a, mu, h⟩ := hcov χ
    exact ⟨rep a, Finset.mem_image_of_mem _ (Finset.mem_univ _), mu, h.symm⟩
  refine (n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK k hk S hS s 0).2 fun α hα => ?_
  exact vge_descent F hT hϖ hvK hv hk (s.s α) (s'.s α) (hss α)
    ((n1a V ϖ hϖ D Q hQ F v hv k hk S hS s' 0).1 hs' α hα)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC
