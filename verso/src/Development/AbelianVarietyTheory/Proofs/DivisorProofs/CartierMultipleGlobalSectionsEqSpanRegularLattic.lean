import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescSpan

/- English proof (translation)
Simplify using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (g : S →+* T) (h : R →+* S) :
    spMap (g.comp h) = spMap g ≫ spMap h := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]`. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id]`.

Rewrite using `[Scheme.ΓSpecIso_naturality]`. Use extensionality with `r`. Simplify using `[Desc.cst, Cartier.fnOf]`.
-/
theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (Desc.cst p) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_naturality]
  ext r
  simp [Desc.cst, Cartier.fnOf]

/- English proof (translation)
Establish `h : spMap (Desc.cst (p ≫ spMap g)) = spMap ((Desc.cst p).comp g)`. Rewrite using `[spMap_comp', ← gp_comp, ← gp_comp, Category.assoc]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem cst_comp_spMap {X : Scheme.{0}} [IsIntegral X] {R S : Type} [CommRing R] [CommRing S] (p : X ⟶ Sp S)
    (g : R →+* S) : Desc.cst (p ≫ spMap g) = (Desc.cst p).comp g := by
  have h : spMap (Desc.cst (p ≫ spMap g)) = spMap ((Desc.cst p).comp g) := by
    rw [spMap_comp', ← gp_comp, ← gp_comp, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
The claim follows from `regAt_fnOf (U := ⊤) trivial trivial _`.
-/
theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (q : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst q r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

/- English proof (translation)
Take `⟨l, h1, h2⟩` from `σ.hθ x`. Establish `e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x))`. Rewrite using `[spMap_comp', spMap_comp', Setup.c₀, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, Category.assoc, (σ.cart x).w, ← Category.assoc, ← Category.assoc, h1, Category.assoc]`. Conclude with `congrArg (fun q : σ.R →+* _ => q r) (congrArg CommRingCat.Hom.hom (Spec.map_injective e))`.
-/
theorem theta_c₀ (σ : Setup) (x : Sp σ.R) (r : σ.R) :
    σ.θ x (σ.c₀ r) = Desc.cst (σ.C x).G.hom (σ.ρ x r) := by
  obtain ⟨l, h1, h2⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, Category.assoc,
      (σ.cart x).w, ← Category.assoc, ← Category.assoc, h1, Category.assoc]
  exact congrArg (fun q : σ.R →+* _ => q r) (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

/- English proof (translation)
Introduce `z hz` and use `by rw [map_mul, theta_c₀] exact (regAt_cst _ _ _).mul (hu z hz)`.
-/
theorem mem_W_mul (σ : Setup) (x : Sp σ.R) {u : σ.A.left.functionField} (hu : u ∈ σ.W x) (r : σ.R) :
    σ.c₀ r * u ∈ σ.W x := fun z hz => by
  rw [map_mul, theta_c₀]
  exact (regAt_cst _ _ _).mul (hu z hz)

section Sec

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {k : ℕ}

/- English proof (translation)
Introduce `x` and use `by obtain ⟨g, hg⟩ := (k • D).exists_isEqn x exact hg.regularAt_iff.2 (by rw [zero_mul]; exact regAt_zero x)`.
-/
theorem sec_zero : (0 : X.functionField) ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [zero_mul]; exact regAt_zero x)

/- English proof (translation)
Introduce `x` and use `by obtain ⟨g, hg⟩ := (k • D).exists_isEqn x exact hg.regularAt_iff.2 (by rw [add_mul]; exact (hg.regularAt_iff.1 (hu x)).add (hg.regularAt_iff.1 (hv x)))`.
-/
theorem sec_add {u v : X.functionField} (hu : u ∈ Sec D k) (hv : v ∈ Sec D k) : u + v ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [add_mul]; exact (hg.regularAt_iff.1 (hu x)).add (hg.regularAt_iff.1 (hv x)))

/- English proof (translation)
Introduce `x` and use `by obtain ⟨g, hg⟩ := (k • D).exists_isEqn x exact hg.regularAt_iff.2 (by rw [_root_.mul_assoc]; exact (hc x).mul (hg.regularAt_iff.1 (hu x)))`.
-/
theorem sec_mul {u c : X.functionField} (hu : u ∈ Sec D k) (hc : ∀ x, RegAt x c) : c * u ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [_root_.mul_assoc]; exact (hc x).mul (hg.regularAt_iff.1 (hu x)))

end Sec

/- English proof (translation)
Establish `hfin` using `(Ideal.span {σ.f}).finite_minimalPrimes_of_isNoetherianRing`. Use `(hfin.preimage fun a _ b _ h => PrimeSpectrum.ext h).subset fun p hp => ?_` and prove the remaining obligations. Take `⟨h1, hf⟩` from `hp`. Establish `: p.asIdeal.FiniteHeight` using `(Ideal.finiteHeight_iff _).2 (Or.inr (by rw [h1]; exact ENat.one_ne_top))`. Use `Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hf) ?_` and prove the remaining obligations.

Rewrite using `[h1]`. Conclude with `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero σ.hf)`.
-/
theorem finite_vert (σ : Setup) :
    {p : Sp σ.R | p.asIdeal.height = 1 ∧ σ.f ∈ p.asIdeal}.Finite := by
  have hfin := (Ideal.span {σ.f}).finite_minimalPrimes_of_isNoetherianRing
  refine (hfin.preimage fun a _ b _ h => PrimeSpectrum.ext h).subset fun p hp => ?_
  obtain ⟨h1, hf⟩ := hp
  have : p.asIdeal.FiniteHeight := (Ideal.finiteHeight_iff _).2 (Or.inr (by rw [h1]; exact ENat.one_ne_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hf) ?_
  rw [h1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero σ.hf)

end GlobalTheory.DescSpan

open GlobalTheory.DescSpan in

/- English proof (translation)
Introduce `σ k`. Establish `hc₀ : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))` using `cst_comp_spMap _ _`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce `hu choose m hm using fun p : Sp σ.R => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ p u`.

Set `M` to `∑ p ∈ (finite_vert σ).toFinset, m p`. Set `v` to `σ.c₀ (σ.f ^ M) * u`. Establish `hv : v ∈ σ.N k`. Use `⟨sec_mul hu fun x => by rw [hc₀]; exact regAt_cst _ _ _, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ v).2 fun p h1 hf => ?_⟩` and prove the remaining obligations. Establish `hle : m p ≤ M` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) ((finite_vert σ).mem_toFinset.2 ⟨h1, hf⟩)`.

Establish `e : v = σ.c₀ (σ.f ^ (M - m p)) * (σ.c₀ σ.f ^ m p * u)`. Simplify using `only [v, map_pow]`. Rewrite using `[← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Rewrite using `[e]`. Conclude with `mem_W_mul σ p (hm p) _`.

Use `⟨1, fun _ => IsLocalization.Away.invSelf σ.f ^ M, fun _ => v, fun _ => hv, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_one]`. Simplify using `only [v, hc₀, RingHom.comp_apply, map_pow]`. Rewrite using `[← _root_.mul_assoc, ← mul_pow, ← map_mul, mul_comm (IsLocalization.Away.invSelf σ.f), IsLocalization.Away.mul_invSelf, map_one, one_pow, _root_.one_mul]`. Introduce and unpack `⟨n, r, t, ht, rfl⟩`.

Conclude with `Finset.sum_induction _ (· ∈ Sec σ.D k) (fun _ _ => sec_add) sec_zero fun i _ => sec_mul (ht i).1 fun x => regAt_cst _ _ _`.
-/
theorem GlobalTheory.Desc.sec_eq_spanBy_N : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  intro σ k
  have hc₀ : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := cst_comp_spMap _ _
  ext u
  constructor
  · intro hu
    choose m hm using fun p : Sp σ.R => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ p u
    let M := ∑ p ∈ (finite_vert σ).toFinset, m p
    let v := σ.c₀ (σ.f ^ M) * u
    have hv : v ∈ σ.N k := by
      refine ⟨sec_mul hu fun x => by rw [hc₀]; exact regAt_cst _ _ _, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ v).2 fun p h1 hf => ?_⟩
      have hle : m p ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        ((finite_vert σ).mem_toFinset.2 ⟨h1, hf⟩)
      have e : v = σ.c₀ (σ.f ^ (M - m p)) * (σ.c₀ σ.f ^ m p * u) := by
        simp only [v, map_pow]
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact mem_W_mul σ p (hm p) _
    refine ⟨1, fun _ => IsLocalization.Away.invSelf σ.f ^ M, fun _ => v, fun _ => hv, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [v, hc₀, RingHom.comp_apply, map_pow]
    rw [← _root_.mul_assoc, ← mul_pow, ← map_mul, mul_comm (IsLocalization.Away.invSelf σ.f),
      IsLocalization.Away.mul_invSelf, map_one, one_pow, _root_.one_mul]
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Finset.sum_induction _ (· ∈ Sec σ.D k) (fun _ _ => sec_add) sec_zero
      fun i _ => sec_mul (ht i).1 fun x => regAt_cst _ _ _
