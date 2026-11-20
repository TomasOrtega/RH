import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCombinationOfMemHaO
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr

set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.ThetaLeast

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in

/- English proof (translation)
Use `set ψ := algebraMap S S' with hψ`. Establish `eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S'`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) = MvPowerSeries.map (algebraMap S S') (B.G.F i)`. Use extensionality with `e`.

Simplify using `[coeff_map, hψ]`. Establish `eA : mapP ψ (B.actK S w0) = B.actK S' w0`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) = MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)`. Use extensionality with `e`.

Simplify using `[coeff_map, hψ]`. Establish `gC : GP (comp1 (B.actK S w0) (pt S (n` using `1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)`. Establish `cL : constantCoeff (B.hL S h w0) = 0` using `gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc`. Establish `eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0`. Unfold `FB.hL`.

Rewrite using `[map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]`. Establish `g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j)`. Introduce `b j`. Use `fin_cases j`. Conclude with `gp_pt b`.

Establish `cb : ∀ b : Fin n, constantCoeff (ev (n` using `n) ![pt S d b] (B.hL S h w0)) = 0 := fun b => gt_const_ev _ (g1 b) _ cL`. Establish `eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n` using `n) ![pt S d b] (B.hL S h w0)) = ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by`. Introduce `b`. Rewrite using `[map_ev ψ _ (g1 b), eL]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Conclude with `baseChange_pt ψ b`. Unfold `nabValN`. Rewrite using `[← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul, map_expS _ _ (by`.

Rewrite using `[MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),`. Use the proof step `MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,`. Use the proof step `Finset.sum_congr rfl fun b _ => eb b]`.
-/
theorem nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t], fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩`.
-/
theorem smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

/- English proof (translation)
Establish `h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K)` using `fun x => IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))`. Use `choose g hg using h`. Establish `inj` using `IsFractionRing.injective V L`. Apply the tactic sequence `refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]`.
-/
theorem exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_lift_integers K T.V T.Fr io`. Set `p : Ideal (𝓞 K)` to `(IsLocalRing.maximalIdeal T.V).comap φ`. Use `haveI hp : p.IsPrime := Ideal.comap_isPrime _ _`. Establish `hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K)` using `p.primeCompl_le_nonZeroDivisors`. Set `V` to `Localization.subalgebra.ofField K p.primeCompl hS`.

Use `haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p`. Use `haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V`. Use `haveI : IsPrincipalIdealRing V := ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 2 0).1 ‹IsDedekindDomain V›`. Establish `hu : ∀ s : p.primeCompl, IsUnit (φ s)` using `fun s => by`. Assume the negation of the conclusion as `hn`.

Conclude with `s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)`. Establish `hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range`. Introduce and unpack `⟨x, a, s, hs, rfl⟩`. Take `⟨u, hu'⟩` from `hu ⟨s, hs⟩`. Use `⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)`. Rewrite using `[map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]`. Take `⟨s, c, Q, hc, hQ, hsum⟩` from `GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP`. Establish `hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring`. Introduce `j`.

Use `choose g hg using (hQ j).2`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g`. Use `⟨b, fun m => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hm : m ∈ (Q j).support`. Take `⟨z, hz⟩` from `hb m hm`.

Establish `: (((b : 𝓞 K) : K) • Q j).coeff m = (z : K)`. Rewrite using `[MvPolynomial.coeff_smul, ← hg m]`. Use `congrArg (algebraMap V K) hz` as an intermediate fact. Rewrite `this` using `[← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`. Conclude with `this.symm`.

Rewrite using `[this]`. Conclude with `z.isIntegral_coe`. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]`. Conclude with `Subring.zero_mem _`. Use `choose b hb using hden`.

Use `choose c' hc' using hc`. Use `choose u hu' using hu`. Use `⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j, fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h0 : io ((b j : 𝓞 K) : K) ≠ 0`. Rewrite using `[← hφ, ← hu']`. Conclude with `((u (b j)).isUnit.map _).ne_zero`. Use `beta_reduce`. Rewrite using `[MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc, ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]`.
-/
theorem exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift_integers K T.V T.Fr io
  let p : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal T.V).comap φ
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K) := p.primeCompl_le_nonZeroDivisors
  let V := Localization.subalgebra.ofField K p.primeCompl hS
  haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p
  haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V
  haveI : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 2 0).1 ‹IsDedekindDomain V›
  have hu : ∀ s : p.primeCompl, IsUnit (φ s) := fun s => by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range := by
    rintro ⟨x, a, s, hs, rfl⟩
    obtain ⟨u, hu'⟩ := hu ⟨s, hs⟩
    refine ⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩
    change _ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)
    rw [map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]
  obtain ⟨s, c, Q, hc, hQ, hsum⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP
  have hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring := by
    intro j
    choose g hg using (hQ j).2
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g
    refine ⟨b, fun m => ?_⟩
    by_cases hm : m ∈ (Q j).support
    · obtain ⟨z, hz⟩ := hb m hm
      have : (((b : 𝓞 K) : K) • Q j).coeff m = (z : K) := by
        rw [MvPolynomial.coeff_smul, ← hg m]
        have := congrArg (algebraMap V K) hz
        rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at this
        exact this.symm
      rw [this]
      exact z.isIntegral_coe
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]
      exact Subring.zero_mem _
  choose b hb using hden
  choose c' hc' using hc
  choose u hu' using hu
  refine ⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j,
    fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : io ((b j : 𝓞 K) : K) ≠ 0 := by
    rw [← hφ, ← hu']
    exact ((u (b j)).isUnit.map _).ne_zero
  beta_reduce
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc,
    ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]

/- English proof (translation)
Establish `key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a`. Introduce `m hm`. Rewrite using `[Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`.

Conclude with `Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i`. Conclude with `Finset.sup_le fun m' hm' => (key m' hm').le`.
-/
theorem totalDegree_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (T : CDVR) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) T.Fr} (hP : P ∈ FFV (Dw := Dw) T a n) :
    P.totalDegree ≤ DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  exact Finset.sup_le fun m' hm' => (key m' hm').le

/- English proof (translation)
Distinguish the cases in `hx : algebraMap T.V T.Fr x = 0`. Rewrite using `[hx, map_zero, AddValuation.map_zero]`. Conclude with `le_top`. Rewrite using `[hv _ hx]`. Conclude with `GlobalTheory.vV_algebraMap_nonneg_dvr T x` after adjusting the coercions.
-/
theorem val_algebraMap_nonneg (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x

/- English proof (translation)
Establish `hz : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hρ` using `[map_zero, mul_zero, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe hρ`. Rewrite `hρ` using `[AddValuation.map_mul, hv z hz]`.

Establish `h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ)` using `hρ ▸ le_add_of_nonneg_left hε`. Establish `h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ` using `WithTop.coe_le_coe.1 h1`. Establish `h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ)` using `by exact_mod_cast h2`. Rewrite using `[nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]`. Use `div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)` and prove the remaining obligations.

Rewrite `hle` using `[Rat.cast_intCast]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, AddValuation.map_zero] at hρ
    exact WithTop.top_ne_coe hρ
  rw [AddValuation.map_mul, hv z hz] at hρ
  have h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ) := hρ ▸ le_add_of_nonneg_left hε
  have h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ := WithTop.coe_le_coe.1 h1
  have h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h2
  rw [nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)
  rw [Rat.cast_intCast] at hle
  linarith

/- English proof (translation)
Rewrite using `[← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]`. Conclude with `le_iInf fun i => (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)`.
-/
theorem le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)

end GlobalTheory.ThetaLeast
