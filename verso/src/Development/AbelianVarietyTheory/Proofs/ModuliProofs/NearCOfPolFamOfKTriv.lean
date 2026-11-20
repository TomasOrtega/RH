import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfGLiesOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowLeftCompOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRetractionNearOfUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TmapOfGlies
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

/- English proof (translation)
Introduce `h1 h2 g n j J hn hodd hj o _ b Mat κ R _ _ _ β v A _ L act Q q₀ hD hv hP hK`. Take `⟨hD1, hD2⟩` from `hD`. Take `⟨hAb, hdim, hLB, hrig, hsym, hamp, hlab, hgood⟩` from `hP`. Take `⟨hl1, hl2, hl3⟩` from `hlab`. Set `P : Out.PolAV (Sp R)` to `{ A := A, isAb := hAb, g := g, smoothDim := hdim, L := L, isLB := hLB, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }`.

Establish `hpos : 0 < n ^ j` using `pow_pos hn.pos j`. Take `⟨R₁, _, _, t₁, ψ₁, hfin, het, ⟨hpb₁, hL₁, hact₁, hpt₁⟩, huniv⟩` from `GlobalTheory.exists_finiteEtale_level_cover h1 h2 o g (n ^ j) J b R β P act Q hpos ⟨rfl, hl1, hl2, hl3⟩`. Establish `hG₁ : GLies A act Q (spMap (algebraMap R R₁)) t₁ ψ₁` using `And.intro hpb₁ (And.intro hact₁ hpt₁)`. Establish `h3 : 3 ≤ n ^ j`. Use `Nat.odd_iff.1 hodd` as an intermediate fact.

Use `hn.two_le` as an intermediate fact. Establish `: n ≤ n ^ j` using `Nat.le_self_pow (by omega) n`. Use linear arithmetic over natural numbers and integers. Take `⟨𝔞, h𝔞⟩` from `GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff h1 h2 o g (n ^ j) J b R₁ (spMap (algebraMap R R₁) ≫ spMap β) t₁ (fun a => algebraMap R R₁ (v a)) hodd.pow h3 (GlobalTheory.ThetaClosed.span_map_eq_top (algebraMap R R₁) hv)`. Establish `kill : ∀ (K : Type) [Field K] (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (y₁ : R₁ →+* K), y₁.comp (algebraMap R R₁) = x → TMap t t₁ (spMap y₁) → t.HasTh (𝟙 _) (fun a => x (v a)) → ∀ r ∈ 𝔞, y₁ r = 0`.

Introduce `K _ x t y₁ hc hT hth`. Apply `(h𝔞 K y₁).1` to reduce the goal to its premises. Establish `h` using `(GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁ (Sp K) _ t (spMap y₁) K (𝟙 _) (fun a => x (v a)) hT).1 hth`. Rewrite `h` using `[Category.id_comp]`. Establish `hw : (fun a => x (v a)) = fun a => y₁ (algebraMap R R₁ (v a))`.

Use function extensionality and compare the values at `a`. Rewrite using `[← hc]`. Both sides reduce to the same expression. Rewrite `h` using `[hw]`. Conclude with `h`.

Establish `key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : R₁ →+* K), y.comp (algebraMap R R₁) = y'.comp (algebraMap R R₁) → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) → y = y'`. Introduce `K _ _ y y' hyy hy hy'`. Establish `th` using `(h𝔞 K y).2 hy`. Establish `th'` using `(h𝔞 K y').2 hy'`. Establish `hw : (fun a => y' (algebraMap R R₁ (v a))) = fun a => y (algebraMap R R₁ (v a))`.

Use function extensionality and compare the values at `a`. Conclude with `(RingHom.congr_fun hyy (v a)).symm`. Establish `hc : spMap y ≫ spMap (algebraMap R R₁) = spMap y' ≫ spMap (algebraMap R R₁)`. Rewrite using `[← spMap_comp, ← spMap_comp, hyy]`. Establish `heq` using `level_eq_of_gLies_of_hasTh h1 h2 g n j J hn hodd hj o b (Sp R) (Sp R₁) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ K (spMap y) (spMap y') (fun a => y (algebraMap R R₁ (v a))) hLB hG₁ hL₁ hc (by rw [← Category.assoc, ← Category.assoc, hc]) th (by …`.

Take `⟨u, ψ, hTu, hGu, hLu, hptu⟩` from `gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y) (spMap (y.comp (algebraMap R R₁)) ≫ spMap β) hLB hG₁ hL₁ (by rw [spMap_comp, Category.assoc])`. Establish `hc' : spMap y' ≫ spMap (algebraMap R R₁) = spMap (y.comp (algebraMap R R₁))`. Rewrite using `[← hc, spMap_comp]`. Establish `hGu' : GLies A act Q (spMap (y.comp (algebraMap R R₁))) u ψ`. Establish `⟨g1, g2, g3⟩` using `hGu`.

Rewrite `g1`, `g3` using `[← spMap_comp y (algebraMap R R₁)]`. Conclude with `And.intro g1 (And.intro g2 g3)`. Establish `hTu' : TMap u t₁ (spMap y')` using `tmap_of_glies o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y') _ u ψ hLB hG₁ hL₁ (by rw [hc']; exact hGu') hLu (fun i => (hptu i).trans (heq i))`. Establish `⟨hg1, hg2, hg3⟩` using `hGu'`. Take `⟨y₀, -, huq⟩` from `huniv K (y.comp (algebraMap R R₁)) u ψ ⟨hg1, hLu, hg2, hg3⟩`.

Conclude with `(huq y ⟨rfl, hptu, hTu⟩).trans (huq y' ⟨hyy.symm, fun i => (hptu i).trans (heq i), hTu'⟩).symm`. Establish `hqa : algebraMap R (R₁ ⧸ 𝔞) = (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁)` using `IsScalarTower.algebraMap_eq R R₁ (R₁ ⧸ 𝔞)`. Establish `: Module.Finite R (R₁ ⧸ 𝔞)` using `Module.Finite.trans R₁ (R₁ ⧸ 𝔞)`. Establish `: Algebra.FormallyUnramified R (R₁ ⧸ 𝔞)` using `inferInstance`. Establish `hup : ∀ q ∈ objPrimes b Mat κ β v, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : R₁ ⧸ 𝔞 →+* K, y.comp (algebraMap R (R₁ ⧸ 𝔞)) = x`.

Introduce `q hq`. Take `⟨K, _, _, x, t, hker, hsh, hth⟩` from `hq`. Take `⟨ψ, hG, hLψ⟩` from `hgood K x _ t (And.intro rfl (And.intro hsh hth))`. Establish `⟨hg1, hg2, hg3⟩` using `hG`. Take `⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩` from `huniv K x t ψ ⟨hg1, hLψ, hg2, hg3⟩`.

Establish `hk` using `kill K x t y₁ hy₁c hy₁T hth`. Use `⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y₁ hk, ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hqa, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hy₁c]`. Introduce `y hy`.

Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Rewrite using `[Ideal.Quotient.lift_comp_mk]`. Apply `key K (y.comp (Ideal.Quotient.mk 𝔞)) y₁` to reduce the goal to its premises. Rewrite using `[RingHom.comp_assoc, ← hqa, hy, hy₁c]`. Introduce `r hr`.

Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]`. Conclude with `hk`. Take `⟨f, hfq, r, hr, -⟩` from `exists_retraction_near_of_unique_point R (R₁ ⧸ 𝔞) (objPrimes b Mat κ β v) hD1 hup q₀ hD2`. Take `⟨z, hzdef⟩ : ∃ z : R₁ →+* Localization.Away f, z = r.comp (Ideal.Quotient.mk 𝔞)` from `⟨_, rfl⟩`. Establish `hz : z.comp (algebraMap R R₁) = loc f`.

Rewrite using `[hzdef, RingHom.comp_assoc, ← hqa, hr]`. Establish `hzk : ∀ x ∈ 𝔞, z x = 0`. Introduce `x hx`. Rewrite using `[hzdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]`. Take `⟨u, ψ, hTu, hGu, hLu, hptu⟩` from `gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp (Localization.Away f)) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap z) (spMap ((loc f).comp β)) hLB hG₁ hL₁ (by rw [← hz, spMap_comp (z.comp (algebraMap R R₁)) β, spMap_comp z (algebraMap R R₁), …`.

Use `Exists.intro f (And.intro hfq (Exists.intro u (And.intro ?_ ?_)))` and prove the remaining obligations. Establish `h` using `(h𝔞 _ z).2 hzk`. Apply `(GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁ (Sp (Localization.Away f)) _ u (spMap z) (Localization.Away f) (𝟙 _) (fun a => loc f (v a)) hTu).2` to reduce the goal to its premises. Rewrite using `[Category.id_comp]`. Establish `hw : (fun a => loc f (v a)) = fun a => z (algebraMap R R₁ (v a))`.

Use function extensionality and compare the values at `a`. Rewrite using `[← hz]`. Both sides reduce to the same expression. Rewrite using `[hw]`. Conclude with `h`.

Introduce `K _ _ x s t' hg`. Take `⟨rfl, hsh, hth⟩` from `(good_comp (loc f) x t').1 hg`. Take `⟨ψ', hG', hLψ'⟩` from `hgood K (x.comp (loc f)) _ t' (And.intro rfl (And.intro hsh hth))`. Establish `⟨hg1, hg2, hg3⟩` using `hG'`. Take `⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩` from `huniv K (x.comp (loc f)) t' ψ' ⟨hg1, hLψ', hg2, hg3⟩`.

Establish `hk` using `kill K (x.comp (loc f)) t' y₁ hy₁c hy₁T hth`. Establish `hyz : y₁ = x.comp z` using `key K y₁ (x.comp z) (by rw [hy₁c, RingHom.comp_assoc, hz]) hk (by intro r' hr'; rw [RingHom.comp_apply, hzk r' hr', map_zero])`. Rewrite `hy₁T` using `[hyz, spMap_comp x z]`. Conclude with `TMap.cancel hTu hy₁T`.
-/
theorem nearC_of_polFam_of_kTriv : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Ideal.span (Set.range v) = ⊤ → PolFam b Mat κ β v A L act Q → Out.KTriv A L → NearC b Mat κ β v q₀ := by
  intro h1 h2 g n j J hn hodd hj o _ b Mat κ R _ _ _ β v A _ L act Q q₀ hD hv hP hK
  obtain ⟨hD1, hD2⟩ := hD
  obtain ⟨hAb, hdim, hLB, hrig, hsym, hamp, hlab, hgood⟩ := hP
  obtain ⟨hl1, hl2, hl3⟩ := hlab
  let P : Out.PolAV (Sp R) :=
    { A := A, isAb := hAb, g := g, smoothDim := hdim, L := L, isLB := hLB, rigid := hrig, sym := hsym,
      ample := hamp, ktriv := hK }
  have hpos : 0 < n ^ j := pow_pos hn.pos j

  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, ⟨hpb₁, hL₁, hact₁, hpt₁⟩, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_level_cover h1 h2 o g (n ^ j) J b R β P act Q hpos ⟨rfl, hl1, hl2, hl3⟩
  have hG₁ : GLies A act Q (spMap (algebraMap R R₁)) t₁ ψ₁ := And.intro hpb₁ (And.intro hact₁ hpt₁)
  have h3 : 3 ≤ n ^ j := by
    have := Nat.odd_iff.1 hodd
    have := hn.two_le
    have : n ≤ n ^ j := Nat.le_self_pow (by omega) n
    omega

  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff h1 h2 o g (n ^ j) J b R₁
    (spMap (algebraMap R R₁) ≫ spMap β) t₁ (fun a => algebraMap R R₁ (v a)) hodd.pow h3
    (GlobalTheory.ThetaClosed.span_map_eq_top (algebraMap R R₁) hv)

  have kill : ∀ (K : Type) [Field K] (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (y₁ : R₁ →+* K), y₁.comp (algebraMap R R₁) = x → TMap t t₁ (spMap y₁) →
      t.HasTh (𝟙 _) (fun a => x (v a)) → ∀ r ∈ 𝔞, y₁ r = 0 := by
    intro K _ x t y₁ hc hT hth
    apply (h𝔞 K y₁).1
    have h := (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp K) _ t (spMap y₁) K (𝟙 _) (fun a => x (v a)) hT).1 hth
    rw [Category.id_comp] at h
    have hw : (fun a => x (v a)) = fun a => y₁ (algebraMap R R₁ (v a)) := by
      funext a; rw [← hc]; rfl
    rw [hw] at h
    exact h

  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = y'.comp (algebraMap R R₁) →
      (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) → y = y' := by
    intro K _ _ y y' hyy hy hy'
    have th := (h𝔞 K y).2 hy
    have th' := (h𝔞 K y').2 hy'
    have hw : (fun a => y' (algebraMap R R₁ (v a))) = fun a => y (algebraMap R R₁ (v a)) := by
      funext a; exact (RingHom.congr_fun hyy (v a)).symm
    have hc : spMap y ≫ spMap (algebraMap R R₁) = spMap y' ≫ spMap (algebraMap R R₁) := by
      rw [← spMap_comp, ← spMap_comp, hyy]
    have heq := level_eq_of_gLies_of_hasTh h1 h2 g n j J hn hodd hj o b (Sp R) (Sp R₁) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ K (spMap y) (spMap y')
      (fun a => y (algebraMap R R₁ (v a))) hLB hG₁ hL₁ hc
      (by rw [← Category.assoc, ← Category.assoc, hc]) th (by rw [← hw]; exact th')
    obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y)
      (spMap (y.comp (algebraMap R R₁)) ≫ spMap β) hLB hG₁ hL₁
      (by rw [spMap_comp, Category.assoc])
    have hc' : spMap y' ≫ spMap (algebraMap R R₁) = spMap (y.comp (algebraMap R R₁)) := by
      rw [← hc, spMap_comp]
    have hGu' : GLies A act Q (spMap (y.comp (algebraMap R R₁))) u ψ := by
      have ⟨g1, g2, g3⟩ := hGu
      rw [← spMap_comp y (algebraMap R R₁)] at g1 g3
      exact And.intro g1 (And.intro g2 g3)
    have hTu' : TMap u t₁ (spMap y') := tmap_of_glies o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y') _ u ψ hLB hG₁ hL₁
      (by rw [hc']; exact hGu') hLu (fun i => (hptu i).trans (heq i))
    have ⟨hg1, hg2, hg3⟩ := hGu'
    obtain ⟨y₀, -, huq⟩ := huniv K (y.comp (algebraMap R R₁)) u ψ ⟨hg1, hLu, hg2, hg3⟩
    exact (huq y ⟨rfl, hptu, hTu⟩).trans (huq y' ⟨hyy.symm, fun i => (hptu i).trans (heq i), hTu'⟩).symm
  have hqa : algebraMap R (R₁ ⧸ 𝔞) = (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) :=
    IsScalarTower.algebraMap_eq R R₁ (R₁ ⧸ 𝔞)
  have : Module.Finite R (R₁ ⧸ 𝔞) := Module.Finite.trans R₁ (R₁ ⧸ 𝔞)
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) := inferInstance

  have hup : ∀ q ∈ objPrimes b Mat κ β v, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : R₁ ⧸ 𝔞 →+* K, y.comp (algebraMap R (R₁ ⧸ 𝔞)) = x := by
    intro q hq
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    obtain ⟨ψ, hG, hLψ⟩ := hgood K x _ t (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K x t ψ ⟨hg1, hLψ, hg2, hg3⟩
    have hk := kill K x t y₁ hy₁c hy₁T hth
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y₁ hk, ?_, ?_⟩
    · beta_reduce
      rw [hqa, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hy₁c]
    · intro y hy
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.Quotient.lift_comp_mk]
      apply key K (y.comp (Ideal.Quotient.mk 𝔞)) y₁
      · rw [RingHom.comp_assoc, ← hqa, hy, hy₁c]
      · intro r hr
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      · exact hk

  obtain ⟨f, hfq, r, hr, -⟩ := exists_retraction_near_of_unique_point R (R₁ ⧸ 𝔞)
    (objPrimes b Mat κ β v) hD1 hup q₀ hD2
  obtain ⟨z, hzdef⟩ : ∃ z : R₁ →+* Localization.Away f, z = r.comp (Ideal.Quotient.mk 𝔞) := ⟨_, rfl⟩
  have hz : z.comp (algebraMap R R₁) = loc f := by
    rw [hzdef, RingHom.comp_assoc, ← hqa, hr]
  have hzk : ∀ x ∈ 𝔞, z x = 0 := by
    intro x hx
    rw [hzdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

  obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁)
    (Sp (Localization.Away f)) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β)
    t₁ ψ₁ (spMap z) (spMap ((loc f).comp β)) hLB hG₁ hL₁
    (by rw [← hz, spMap_comp (z.comp (algebraMap R R₁)) β, spMap_comp z (algebraMap R R₁), Category.assoc])
  refine Exists.intro f (And.intro hfq (Exists.intro u (And.intro ?_ ?_)))
  · have h := (h𝔞 _ z).2 hzk
    apply (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp (Localization.Away f)) _ u (spMap z) (Localization.Away f) (𝟙 _) (fun a => loc f (v a)) hTu).2
    rw [Category.id_comp]
    have hw : (fun a => loc f (v a)) = fun a => z (algebraMap R R₁ (v a)) := by
      funext a; rw [← hz]; rfl
    rw [hw]; exact h
  · intro K _ _ x s t' hg
    obtain ⟨rfl, hsh, hth⟩ := (good_comp (loc f) x t').1 hg
    obtain ⟨ψ', hG', hLψ'⟩ := hgood K (x.comp (loc f)) _ t' (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG'
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K (x.comp (loc f)) t' ψ' ⟨hg1, hLψ', hg2, hg3⟩
    have hk := kill K (x.comp (loc f)) t' y₁ hy₁c hy₁T hth
    have hyz : y₁ = x.comp z := key K y₁ (x.comp z) (by rw [hy₁c, RingHom.comp_assoc, hz]) hk
      (by intro r' hr'; rw [RingHom.comp_apply, hzk r' hr', map_zero])
    rw [hyz, spMap_comp x z] at hy₁T
    exact TMap.cancel hTu hy₁T

end GlobalTheory.ZM.NearBuild
end
