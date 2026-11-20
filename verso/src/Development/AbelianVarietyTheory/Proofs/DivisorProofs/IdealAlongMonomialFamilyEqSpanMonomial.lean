import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.UGZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

/- English proof (translation)
Introduce `hk`. Establish `hδ : Cm.δ k ≠ 0` using `Cm.cone.linearIndependent.ne_zero k`. Establish `hsym` using `(Cm.cone.mem k).1`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, Cm.δ k y y ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hδ` to reduce the goal to its premises. Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Establish `h1` using `h (a + b)`. Establish `h2` using `h a`.

Establish `h3` using `h b`. Simplify using `only [map_add, LinearMap.add_apply] at h1`. Rewrite `h1` using `[hsym b a]`. Simplify using `only [LinearMap.zero_apply]`. Use linear arithmetic over natural numbers and integers.

Take `⟨u, n, hn, hc⟩` from `Cm.mono y`. Establish `hM : (0 : ℤ) < (l.M' : ℤ)` using `by exact_mod_cast GlobalTheory.LevelExist.M'_pos l`. Establish `hnk : n k ≠ 0`. Introduce `h0`. Establish `e` using `hn k`.

Rewrite `e` using `[h0]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero] at e`. Break down `mul_eq_zero.1 e with e | e` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `hy e`.

Apply `GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hnk), mul_zero]`.
-/
theorem s_ne_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (k : Fin Cm.m) : Cm.s k ≠ 0 := by
  intro hk
  have hδ : Cm.δ k ≠ 0 := Cm.cone.linearIndependent.ne_zero k
  have hsym := (Cm.cone.mem k).1
  obtain ⟨y, hy⟩ : ∃ y, Cm.δ k y y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hδ
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := h (a + b)
    have h2 := h a
    have h3 := h b
    simp only [map_add, LinearMap.add_apply] at h1
    rw [hsym b a] at h1
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨u, n, hn, hc⟩ := Cm.mono y
  have hM : (0 : ℤ) < (l.M' : ℤ) := by exact_mod_cast GlobalTheory.LevelExist.M'_pos l
  have hnk : n k ≠ 0 := by
    intro h0
    have e := hn k
    rw [h0] at e
    simp only [LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero] at e
    rcases mul_eq_zero.1 e with e | e
    · omega
    · exact hy e
  apply GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hnk), mul_zero]

end GlobalTheory.UGZero

namespace GlobalTheory.UGZero

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq l Xo c C φ hpf d J hJ hval S π hbl V _ _ _ Cm hV ξ hξ`. Use `haveI : Module.Projective (𝓞 E) Cm.P.D.toPre.X := GlobalTheory.Forms.projective_of_int _ _`. Establish `hP` using `hpf Cm.P.D.toPre.X Cm.rank`. Establish `key0 : ∀ k, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • Cm.δ k) = n` using `fun k => hP.exists_nat (Submodule.smul_mem _ _ (Cm.cone.mem k)) (fun y => by`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `mul_nonneg (by positivity) (Cm.cone.nonneg k y))`. Use `choose n hn using key0`. Use `⟨fun k => d * n k, fun k => by rw [hn]; push_cast; ring, ?_⟩` and prove the remaining obligations. Use `set f := ∏ k, Cm.s k ^ (d * n k) with hf`. Take `⟨g₀, hg₀⟩` from `GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π _ hbl V ξ`.

Rewrite `hg₀` using `[GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc]`. Rewrite using `[hg₀]`. Establish `hV'` using `hV`. Take `⟨⟨hNoeth, -, hIC, -⟩, hchar⟩` from `hV'`. Establish `key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Ideal.span {ψ g₀} = Ideal.span {ψ f}`.

Introduce `W _ _ _ hW ψ hψi hψl`. Use `haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 hW).1`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `hw : ∀ k, ∃ w : ℕ, Associated (ψ (Cm.s k)) (ϖ ^ w)` using `fun k => by`. Establish `h0 : ψ (Cm.s k) ≠ 0` using `fun h => s_ne_zero Cm k (hψi (h.trans (map_zero ψ).symm))`.

Take `⟨w, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`. Conclude with `⟨w, ⟨u⁻¹, by rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩⟩`. Use `choose w hw using hw`. Establish `hinj : Function.Injective ((algebraMap W (FractionRing W)).comp ψ)` using `(IsFractionRing.injective W (FractionRing W)).comp hψi`. Take `⟨gam, e⟩ : ∃ gam : FractionRing V →+* FractionRing W, gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ψ` from `⟨IsFractionRing.lift hinj, RingHom.ext fun r => by`.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply]`. Conclude with `IsFractionRing.lift_algebraMap hinj r⟩`. Establish `hκ : spMap gam ≫ jK V = jK W ≫ spMap ψ` using `by show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]`. Take `⟨t, tK, P, ⟨a1⟩, ⟨a2⟩, be, hbe, hmono, hφbe⟩` from `GlobalTheory.UChart.pull_trait Xo c φ V hV Cm W hW ψ hψi hψl ϖ hϖ w hw (spMap gam) hκ`.

Establish `hy : (spMap gam ≫ Cm.y) ≫ C.i = jK W ≫ (spMap ψ ≫ ξ ≫ π ≫ pullback.fst C.z (spMap C.b))`. Simplify using `only [UCompact.i, Category.assoc]`. Rewrite using `[reassoc_of% hξ, reassoc_of% hκ]`. Take `⟨N, hN, hid⟩` from `hval W hW ϖ hϖ _ (spMap gam ≫ Cm.y) hy t tK ⟨a1⟩ ⟨a2⟩ P be hbe hmono`. Rewrite `hid` using `[GlobalTheory.TraitOrder.idlAlong_comp, hg₀, Ideal.map_span, Set.image_singleton]`.

Rewrite using `[hid]`. Establish `hNe : N = ∑ k, w k * (d * n k)`. Establish `: (N : ℝ) = ((∑ k, w k * (d * n k) : ℕ) : ℝ)`. Rewrite using `[hN, hφbe]`. Use `push_cast`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.

Use `Ideal.span_singleton_eq_span_singleton.2 ?_` and prove the remaining obligations. Rewrite using `[hf, map_prod, hNe, ← Finset.prod_pow_eq_pow_sum]`. Use `(Associated.prod Finset.univ (fun k => ψ (Cm.s k ^ (d * n k))) (fun k => ϖ ^ (w k * (d * n k))) fun k _ => ?_).symm` and prove the remaining obligations. Rewrite using `[map_pow, pow_mul ϖ (w k)]`. Conclude with `(hw k).pow_pow`.

Use `haveI := hNoeth`. Use `haveI := hIC`. Use `haveI := hchar`. Establish `hf0 : f ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (s_ne_zero Cm k)`. Establish `hg0 : g₀ ≠ 0`.

Introduce and unpack `rfl`. Take `⟨W, _, _, _, ψ, hW, hψi, hψl⟩` from `GlobalTheory.DvrDom.exists_cdvr_dominating V`. Use `key W hW ψ hψi hψl` as an intermediate fact. Rewrite `this` using `[map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hf0 (hψi (this.trans (map_zero ψ).symm))`.

Establish `hkey' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W → ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Associated (ψ g₀) (ψ f)`. Introduce `W _ _ _ hc ψ hψi hψl`. Establish `: CharZero W` using `charZero_of_injective_ringHom hψi`. Conclude with `Ideal.span_singleton_eq_span_singleton.1 (key W ((GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, this⟩) ψ hψi hψl)`. Establish `d1` using `GlobalTheory.Poinc.dvd_of_forall_complete_dvr V g₀ f hf0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).symm.dvd`.

Establish `d2` using `GlobalTheory.Poinc.dvd_of_forall_complete_dvr V f g₀ hg0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).dvd`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)`.
-/
theorem idlAlong_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  intro E _ _ _ H Dw hpq l Xo c C φ hpf d J hJ hval S π hbl V _ _ _ Cm hV ξ hξ
  haveI : Module.Projective (𝓞 E) Cm.P.D.toPre.X := GlobalTheory.Forms.projective_of_int _ _
  have hP := hpf Cm.P.D.toPre.X Cm.rank
  have key0 : ∀ k, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • Cm.δ k) = n := fun k =>
    hP.exists_nat (Submodule.smul_mem _ _ (Cm.cone.mem k)) (fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (Cm.cone.nonneg k y))
  choose n hn using key0
  refine ⟨fun k => d * n k, fun k => by rw [hn]; push_cast; ring, ?_⟩
  set f := ∏ k, Cm.s k ^ (d * n k) with hf
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π _ hbl V ξ
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc] at hg₀
  rw [hg₀]
  have hV' := hV
  obtain ⟨⟨hNoeth, -, hIC, -⟩, hchar⟩ := hV'
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : V →+* W,
      Function.Injective ψ → IsLocalHom ψ → Ideal.span {ψ g₀} = Ideal.span {ψ f} := by
    intro W _ _ _ hW ψ hψi hψl
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 hW).1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hw : ∀ k, ∃ w : ℕ, Associated (ψ (Cm.s k)) (ϖ ^ w) := fun k => by
      have h0 : ψ (Cm.s k) ≠ 0 := fun h => s_ne_zero Cm k (hψi (h.trans (map_zero ψ).symm))
      obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      exact ⟨w, ⟨u⁻¹, by rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩⟩
    choose w hw using hw
    have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp ψ) :=
      (IsFractionRing.injective W (FractionRing W)).comp hψi
    obtain ⟨gam, e⟩ : ∃ gam : FractionRing V →+* FractionRing W,
        gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ψ :=
      ⟨IsFractionRing.lift hinj, RingHom.ext fun r => by
        rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj r⟩
    have hκ : spMap gam ≫ jK V = jK W ≫ spMap ψ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    obtain ⟨t, tK, P, ⟨a1⟩, ⟨a2⟩, be, hbe, hmono, hφbe⟩ :=
      GlobalTheory.UChart.pull_trait Xo c φ V hV Cm W hW ψ hψi hψl ϖ hϖ w hw (spMap gam) hκ
    have hy : (spMap gam ≫ Cm.y) ≫ C.i = jK W ≫ (spMap ψ ≫ ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
      simp only [UCompact.i, Category.assoc]
      rw [reassoc_of% hξ, reassoc_of% hκ]
    obtain ⟨N, hN, hid⟩ := hval W hW ϖ hϖ _ (spMap gam ≫ Cm.y) hy t tK ⟨a1⟩ ⟨a2⟩ P be hbe hmono
    rw [GlobalTheory.TraitOrder.idlAlong_comp, hg₀, Ideal.map_span, Set.image_singleton] at hid
    rw [hid]
    have hNe : N = ∑ k, w k * (d * n k) := by
      have : (N : ℝ) = ((∑ k, w k * (d * n k) : ℕ) : ℝ) := by
        rw [hN, hφbe]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hn]; ring
      exact_mod_cast this
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    rw [hf, map_prod, hNe, ← Finset.prod_pow_eq_pow_sum]
    refine (Associated.prod Finset.univ (fun k => ψ (Cm.s k ^ (d * n k))) (fun k => ϖ ^ (w k * (d * n k)))
      fun k _ => ?_).symm
    rw [map_pow, pow_mul ϖ (w k)]
    exact (hw k).pow_pow
  haveI := hNoeth
  haveI := hIC
  haveI := hchar
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (s_ne_zero Cm k)
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating V
    have := key W hW ψ hψi hψl
    rw [map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hf0 (hψi (this.trans (map_zero ψ).symm))
  have hkey' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
      ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Associated (ψ g₀) (ψ f) := by
    intro W _ _ _ hc ψ hψi hψl
    have : CharZero W := charZero_of_injective_ringHom hψi
    exact Ideal.span_singleton_eq_span_singleton.1 (key W ((GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, this⟩) ψ hψi hψl)
  have d1 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V g₀ f hf0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).symm.dvd
  have d2 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V f g₀ hg0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).dvd
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)

end GlobalTheory.UGZero
