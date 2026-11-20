import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimesStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.DescGraded

/- English proof (translation)
Establish `h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial)` using `rfl`. Rewrite using `[h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

/- English proof (translation)
The claim follows from `regAt_fnOf (U := ⊤) trivial trivial _`.
-/
theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _

/- English proof (translation)
Take `⟨l, hl, hl'⟩` from `σ.hθ x`. Establish `e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x))`. Establish `e1 : spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `e2 : spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) = spMap (Desc.cst (σ.C x).G.hom) ≫ spMap (σ.ρ x)`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc, (σ.cart x).w]`. Simplify using `only [Category.assoc]`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective e)`.
-/
theorem theta_c₀ (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    have e1 : spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) = spMap (Desc.cst (σ.C x).G.hom) ≫ spMap (σ.ρ x) := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc, (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

/- English proof (translation)
Introduce `z _` and use `by have := RingHom.congr_fun (theta_c₀ σ x) r simp only [RingHom.comp_apply] at this rw [this] exact regAt_cst _ _ _`.
-/
theorem c₀_mem_W (σ : Setup) (x : Sp σ.R) (r : σ.R) : σ.c₀ r ∈ σ.W x := fun z _ => by
  have := RingHom.congr_fun (theta_c₀ σ x) r
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact regAt_cst _ _ _

/- English proof (translation)
Introduce `z hz` and use `by rw [map_mul]; exact (ha z hz).mul (hb z hz)`.
-/
theorem W_mul (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a * b ∈ σ.W x := fun z hz => by
  rw [map_mul]; exact (ha z hz).mul (hb z hz)

/- English proof (translation)
Introduce `z hz` and use `by rw [map_add]; exact (ha z hz).add (hb z hz)`.
-/
theorem W_add (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a + b ∈ σ.W x := fun z hz => by
  rw [map_add]; exact (ha z hz).add (hb z hz)

/- English proof (translation)
Introduce `x` and use `by obtain ⟨g, hg, h⟩ := hb x exact ⟨g, hg, _root_.mul_assoc a b g ▸ (ha x).mul h⟩`.
-/
theorem sec_mul_left {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) {a b : X.functionField}
    (ha : ∀ x, RegAt x a) (hb : b ∈ Sec D k) : a * b ∈ Sec D k := fun x => by
  obtain ⟨g, hg, h⟩ := hb x
  exact ⟨g, hg, _root_.mul_assoc a b g ▸ (ha x).mul h⟩

/- English proof (translation)
Use `((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage (f := fun p : PrimeSpectrum R => p.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hfp⟩`. Use `Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hfp) ?_` and prove the remaining obligations. Rewrite using `[hp]`. Conclude with `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)`.
-/
theorem finite_height_one {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage
    (f := fun p : PrimeSpectrum R => p.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hfp⟩
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hfp) ?_
  rw [hp]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)

/- English proof (translation)
Establish `e : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))`. Establish `e2 : spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) = spMap (Desc.cst σ.A.hom) ≫ Desc.awayMap σ.f`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `e : spMap σ.c₀ = spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)))`.

Rewrite using `[e2, Setup.c₀, spMap_cst, spMap_cst, Category.assoc]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective e)`. Rewrite using `[e, RingHom.comp_apply]`. Conclude with `((IsLocalization.Away.algebraMap_isUnit σ.f).map _).ne_zero`.
-/
theorem c₀_f_ne_zero (σ : Setup) : σ.c₀ σ.f ≠ 0 := by
  have e : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    have e2 : spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) =
        spMap (Desc.cst σ.A.hom) ≫ Desc.awayMap σ.f := by
      rw [← Spec.map_comp]; rfl
    have e : spMap σ.c₀ = spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) := by
      rw [e2, Setup.c₀, spMap_cst, spMap_cst, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e, RingHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit σ.f).map _).ne_zero

/- English proof (translation)
Introduce `σ`. Use `⟨⟨⟨fun x => ?_, fun x => ?_⟩, fun k => ⟨fun x => ?_, fun x => ?_⟩, fun k a ha b hb => ⟨fun x => (ha.1 x).add (hb.1 x), fun x => W_add σ x (ha.2 x) (hb.2 x)⟩, fun k r a ha => ⟨sec_mul_left _ _ (fun x => regAt_cst _ x r) ha.1, fun x => W_mul σ x (c₀_mem_W σ x r) (ha.2 x)⟩, fun k l …` and prove the remaining obligations. Rewrite using `[zero_nsmul]`. Conclude with `⟨1, CartierDiv.isEqn_zero x, by simpa using (unitAt_one x).regAt⟩`. Simplify using `using c₀_mem_W σ x 1`.

Conclude with `(CartierDiv.vanishesAt_zero _ x).regularAt`. Simplify using `using c₀_mem_W σ x 0`. Rewrite using `[add_nsmul]`. Conclude with `(ha.1 x).mul (hb.1 x)`. Take `⟨k, hk, u, hu, U, -, hU, hx⟩` from `σ.amp (genericPoint _)`.

Establish `hu0 : u ≠ 0`. Establish `: genericPoint σ.A.left ∈ locus σ.D k u` using `hU ▸ hx`. Conclude with `CartierDiv.GeneratesAt.ne_zero this`. Use `choose m hm using fun x => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ x u`. Take `⟨M, hM⟩` from `((finite_height_one σ.hf).image m).bddAbove`.

Use `⟨k, hk, σ.c₀ σ.f ^ M * u, ⟨?_, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ _).2 fun p hp hfp => ?_⟩, mul_ne_zero (pow_ne_zero _ (c₀_f_ne_zero σ)) hu0⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `sec_mul_left _ _ (fun x => regAt_cst _ x _) hu`. Establish `hle : m p ≤ M` using `hM ⟨p, ⟨hp, hfp⟩, rfl⟩`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le' hle`.

Rewrite using `[pow_add, _root_.mul_assoc, ← map_pow]`. Conclude with `W_mul σ p (c₀_mem_W σ p _) (hm p)`.
-/
theorem gradedFam_and_ne_zero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  intro σ
  refine ⟨⟨⟨fun x => ?_, fun x => ?_⟩, fun k => ⟨fun x => ?_, fun x => ?_⟩,
    fun k a ha b hb => ⟨fun x => (ha.1 x).add (hb.1 x), fun x => W_add σ x (ha.2 x) (hb.2 x)⟩,
    fun k r a ha => ⟨sec_mul_left _ _ (fun x => regAt_cst _ x r) ha.1, fun x => W_mul σ x (c₀_mem_W σ x r) (ha.2 x)⟩,
    fun k l a ha b hb => ⟨fun x => ?_, fun x => W_mul σ x (ha.2 x) (hb.2 x)⟩⟩, ?_⟩
  · rw [zero_nsmul]
    exact ⟨1, CartierDiv.isEqn_zero x, by simpa using (unitAt_one x).regAt⟩
  · simpa using c₀_mem_W σ x 1
  · exact (CartierDiv.vanishesAt_zero _ x).regularAt
  · simpa using c₀_mem_W σ x 0
  · rw [add_nsmul]
    exact (ha.1 x).mul (hb.1 x)
  · obtain ⟨k, hk, u, hu, U, -, hU, hx⟩ := σ.amp (genericPoint _)
    have hu0 : u ≠ 0 := by
      have : genericPoint σ.A.left ∈ locus σ.D k u := hU ▸ hx
      exact CartierDiv.GeneratesAt.ne_zero this
    choose m hm using fun x => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ x u
    obtain ⟨M, hM⟩ := ((finite_height_one σ.hf).image m).bddAbove
    refine ⟨k, hk, σ.c₀ σ.f ^ M * u, ⟨?_, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ _).2 fun p hp hfp => ?_⟩,
      mul_ne_zero (pow_ne_zero _ (c₀_f_ne_zero σ)) hu0⟩
    · rw [← map_pow]
      exact sec_mul_left _ _ (fun x => regAt_cst _ x _) hu
    · have hle : m p ≤ M := hM ⟨p, ⟨hp, hfp⟩, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [pow_add, _root_.mul_assoc, ← map_pow]
      exact W_mul σ p (c₀_mem_W σ p _) (hm p)

end GlobalTheory.DescGraded
