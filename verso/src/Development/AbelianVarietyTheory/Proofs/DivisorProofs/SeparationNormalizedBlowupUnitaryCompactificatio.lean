import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermCoefficientSqEqMonomialSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

noncomputable section
namespace GlobalTheory.USep.Alg

/- English proof (translation)
Establish `hn : ∃ n : ℕ, 0 < n ∧ x ^ n ∈ k₀`. Break down `lt_or_gt_of_ne hm with hm | hm` into its components or cases. Use `⟨m.natAbs, by omega, ?_⟩` and prove the remaining obligations. Establish `: x ^ m = (x ^ m.natAbs)⁻¹`. Rewrite using `[← zpow_natCast, ← zpow_neg]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[this]`. Simplify using `using k₀.inv_mem h`. Use `⟨m.natAbs, by omega, ?_⟩` and prove the remaining obligations.

Establish `: x ^ m = x ^ m.natAbs` using `by rw [← zpow_natCast]; congr 1; omega`. Rewrite `h` using `[this]`. Then use the resulting hypothesis. Take `⟨n, hn, h⟩` from `hn`. Use `letI : Algebra k₀ K := k₀.subtype.toAlgebra`. Establish `hi : IsIntegral k₀ x`.

Use `⟨Polynomial.X ^ n - Polynomial.C ⟨x ^ n, h⟩, Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]`. Conclude with `sub_eq_zero.2 rfl`. Establish `h1 : (minpoly k₀ x).natDegree = 1`. Use `IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hi)` as an intermediate fact.

Conclude with `Polynomial.natDegree_eq_of_degree_eq_some this`. Take `⟨y, hy⟩` from `(minpoly.natDegree_eq_one_iff).1 h1`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K} (hx : x ≠ 0) {m : ℤ}
    (hm : m ≠ 0) (h : x ^ m ∈ k₀) : x ∈ k₀ := by
  have hn : ∃ n : ℕ, 0 < n ∧ x ^ n ∈ k₀ := by
    rcases lt_or_gt_of_ne hm with hm | hm
    · refine ⟨m.natAbs, by omega, ?_⟩
      have : x ^ m = (x ^ m.natAbs)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg]; congr 1; omega
      rw [this] at h
      simpa using k₀.inv_mem h
    · refine ⟨m.natAbs, by omega, ?_⟩
      have : x ^ m = x ^ m.natAbs := by rw [← zpow_natCast]; congr 1; omega
      rwa [this] at h
  obtain ⟨n, hn, h⟩ := hn
  letI : Algebra k₀ K := k₀.subtype.toAlgebra
  have hi : IsIntegral k₀ x := by
    refine ⟨Polynomial.X ^ n - Polynomial.C ⟨x ^ n, h⟩, Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    exact sub_eq_zero.2 rfl
  have h1 : (minpoly k₀ x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

/- English proof (translation)
Take `⟨r, S⟩` from `N.smithNormalForm (Module.Free.chooseBasis ℤ L)`. Establish `ha : ∀ i, S.a i ≠ 0` using `fun i h0 => S.bN.ne_zero i (Subtype.ext (by rw [S.snf, h0, zero_smul]; rfl))`. Use `set P : ℤ := ∏ i, S.a i`. Establish `hdiv : ∀ i, S.a i ∣ P` using `fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Use `⟨P, Finset.prod_ne_zero_iff.2 fun i _ => ha i, ∑ i, (P / S.a i * F (S.bN i)) • S.bM.coord (S.f i), ?_⟩` and prove the remaining obligations.

Establish `key : ∀ i, (∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)) (S.bN i) = P * F (S.bN i)`. Introduce `i`. Rewrite using `[LinearMap.sum_apply, S.snf, Finset.sum_eq_single i]`. Simplify using `only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]`. Rewrite using `[← mul_assoc, mul_comm (S.a i), Int.ediv_mul_cancel (hdiv i)]`.

Introduce `k _ hk`. Simplify using `only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]`. Rewrite using `[Finsupp.single_eq_of_ne (S.f.injective.ne hk)]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce `x`. Establish `: ((∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)).comp N.subtype) = P • F` using `S.bN.ext fun i => by rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, key]; rfl`. Conclude with `LinearMap.congr_fun this x`.
-/
theorem exists_extend_smul {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (N : Submodule ℤ L)
    (F : N →ₗ[ℤ] ℤ) : ∃ n : ℤ, n ≠ 0 ∧ ∃ g : L →ₗ[ℤ] ℤ, ∀ x : N, g x = n * F x := by
  classical
  obtain ⟨r, S⟩ := N.smithNormalForm (Module.Free.chooseBasis ℤ L)
  have ha : ∀ i, S.a i ≠ 0 := fun i h0 => S.bN.ne_zero i (Subtype.ext (by rw [S.snf, h0, zero_smul]; rfl))
  set P : ℤ := ∏ i, S.a i
  have hdiv : ∀ i, S.a i ∣ P := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨P, Finset.prod_ne_zero_iff.2 fun i _ => ha i, ∑ i, (P / S.a i * F (S.bN i)) • S.bM.coord (S.f i), ?_⟩
  have key : ∀ i, (∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)) (S.bN i) = P * F (S.bN i) := by
    intro i
    rw [LinearMap.sum_apply, S.snf, Finset.sum_eq_single i]
    · simp only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [← mul_assoc, mul_comm (S.a i), Int.ediv_mul_cancel (hdiv i)]
    · intro k _ hk
      simp only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
      rw [Finsupp.single_eq_of_ne (S.f.injective.ne hk)]
      simp
    · simp
  intro x
  have : ((∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)).comp N.subtype) = P • F :=
    S.bN.ext fun i => by rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, key]; rfl
  exact LinearMap.congr_fun this x

end GlobalTheory.USep.Alg

namespace GlobalTheory.USep.Alg

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]`.
-/
theorem zpow_sum_units {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

end GlobalTheory.USep.Alg

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

open GlobalTheory.USep in

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq φ hpol hnsi l Xo c C d J hd hJ hval S π j hbl hprop hjπ hj hpre`. Introduce `V _ _ _ Cm hV ξ hξ N s ε τ₀ h1 h2 h3 hτ K _ _ ev k₀ hk hc hdef`. Establish `hξ' : Cm.y ≫ C.iF = jK V ≫ ξ ≫ π` using `by rw [← hjπ, ← Category.assoc, hξ, Category.assoc]`. Take `⟨j₀, hdesc⟩` from `GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios Cm.P.D.toPre.P.g 3 Nat.prime_three (by decide)`. Take `⟨jj, M, _, g, z₁, ζ, Φ, y, ρ, e, h, U, hUne, hjj, hcov, htr, hmem⟩` from `GlobalTheory.T.exists_unitary_fourier_system_traits_family E H Dw hpq l Xo c C φ V Cm hV (ξ ≫ π) hξ' 3 Nat.prime_three (by decide) (max j₀ 1)`.

Set `ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)` to `fun k => GlobalTheory.PolFan.pull e.toLinearMap (Cm.δ (h k))`. Take `⟨ev₁, hev₁, hEl⟩` from `GlobalTheory.T.exists_approximating_elements_normalCover_unitary E H Dw hpq l Xo c C φ hpol d J hJ hval S π hbl V Cm hV ξ hξ' _ M g z₁ ζ Φ y ρ e h U hUne hcov htr hmem K ev k₀ hk hc hdef ga (fun k a b => rfl)`. Take `⟨d₀, hd₀, hsup⟩ : ∃ d₀, 1 ≤ d₀ ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ d₀` from `exists_hasSupports (𝓞 E) H.bar (min Dw.p Dw.q) φ hpol fun X _ _ _ _ hX r γ hγ => GlobalTheory.T.exists_supportingTuple_smoothCone_cmField E H φ X (hpol X hX) r γ hγ`. Establish `hM' : 1 ≤ l.M'` using `Nat.one_le_iff_ne_zero.2 (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')`. Establish `hmem4` using `hmem.2.2.2.1`.

Establish `hδ : ∀ k, Φ.δ y k = (l.M' : ℤ) • ga k` using `fun k => LinearMap.ext₂ fun a b => by`. Rewrite using `[(hmem4 k).2 a b]`. Both sides reduce to the same expression. Establish `hN3 : 3 ≤ (3 ^ jj) ^ 2`. Establish `: 3 ≤ 3 ^ jj`.

Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Take `⟨V1, V2, V3⟩` from `GlobalTheory.T.poincareApprox_values_at_point_of_elements (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ hpol hnsi d₀ (2 * d) hd₀ (by omega) hsup 0 !![(1 : ℤ)] Φ.posW _ hN3 _ Φ y ga l.M' hM' ((Cm.cone.pull_equiv e).reindex h) hδ K ev₁ k₀ hEl`. Establish `hρinj : Function.Injective ρ` using `hmem.1`. Take `⟨-, -, -, -, D, p, hth⟩` from `hmem`.

Establish `hU : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Φ.V y)` using `fun m hm => by`. Use `(IsUnit.mk0 (m : c.F) (Nat.cast_ne_zero.2 hm)).map (ρ.comp Cm.b)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hmo : ∀ mu : Cm.P.D.toPre.X, mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) ≠ 0 ∧ ∃ cc, IsUnit (Φ.u y (fun _ => e.symm mu) cc)` using `fun mu => ⟨Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Φ.t_mem y i).2, Φ.u_unit y _⟩`. Take `⟨hg, htr'⟩` from `GlobalTheory.T.descendsAbelianPart_of_isPullDeg V (Φ.V y) ρ Cm.P.D.toPre D p`.

Use `(sepAtB_iff _ _ _ _ _).2 ⟨fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1 i, ← hev₁, RingHom.comp_apply]`. Use `(hmem4 (h.symm i)).1` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Rewrite using `[← this, map_pow, V1, zero_pow two_ne_zero]`.

Establish `hD` using `hdesc jj (le_of_max_le_left hjj) (Φ.V y) (Φ.cn y) hU D hg Cm.P.D.toPre.X Φ.Q p.xe.symm (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)) hmo hth K ev₁ k₀ hk (fun mu cc cc' hu => V2 _ cc cc' hu)`. Use `htr' K ev₁ k₀ hD` as an intermediate fact. Rewrite `this` using `[hev₁]`. Then use the resulting hypothesis. Introduce `W₀ _ ιb hFB hkb i`. Set `P : LinearMap.BilinForm ℤ Cm.P.D.toPre.X → LinearMap.BilinForm ℤ D.X` to `fun β => β.compl₁₂ p.xe.toAddMonoidHom.toIntLinearMap p.xe.toAddMonoidHom.toIntLinearMap`.

Set `ε₁ : Fin Cm.m ⊕ Fin N → LinearMap.BilinForm ℤ D.X` to `fun x => P ((l.M' : ℤ) • (ε x : LinearMap.BilinForm ℤ Cm.P.D.toPre.X))`. Take `⟨τ₁, hT1, hF1⟩` from `GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg V (Φ.V y) ρ hρinj Cm.P.D.toPre D p τ₀ (Cm.m + N) (fun k => s (finSumFinEquiv.symm k)) (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Cm.P.D.toPre.X)) (fun k => ε₁ (finSumFinEquiv.symm k)) (fun k a b = …`. Establish `hPE : D.PsiEven` using `GlobalTheory.PsiEvenPull.psiEven_pull GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.psi_even`. Establish `hTB : D.TauBimult` using `GlobalTheory.tauBimult_of_isPullDeg GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.tau_bimult`. Establish `hε₁ : ∀ x mu, ε₁ x (p.xe.symm mu) (p.xe.symm mu) = (l.M' : ℤ) * (ε x : LinearMap.BilinForm ℤ _) mu mu`.

Introduce `x mu`. Simplify using `[ε₁, P]`. Establish `hmo2 : ∀ mu, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)) ^ 2 = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (s (.inl k))) ^ ε₁ (.inl k) (p.xe.symm mu) (p.xe.symm mu)`. Introduce `mu`. Establish `hq : ∀ k', (qW !![(1 : ℤ)] (Φ.δ y k') fun _ => e.symm mu) = (l.M' : ℤ) * Cm.δ (h k') mu mu` using `fun k' => by`.

Simplify using `[qW, (hmem4 k').2]`. Establish `hnn : ∀ k, 0 ≤ (l.M' : ℤ) * Cm.δ k mu mu` using `fun k => mul_nonneg (by positivity) (Cm.cone.nonneg k mu)`. Simplify using `only [mono, hq, hε₁, h2, h1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_prod, ← Finset.prod_pow]`.

Use `Finset.prod_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[← (hmem4 k').1, map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k') 2]`. Rewrite using `[map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k')]`. Conclude with `pow_right_comm (M := FractionRing (Φ.V y)) _ _ _`. Use `_ = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (Cm.s k)) ^ ((l.M' : ℤ) * Cm.δ k mu mu).toNat := Fintype.prod_equiv h _ _ (fun _ => rfl)`.

Use `_ = _ := Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, Int.toNat_of_nonneg (hnn k)]`. Establish `hcoef` using `GlobalTheory.T.thetaTerm_coefficient_sq_eq_monomial_subfield ((3 ^ jj) ^ 2) (by omega) (Φ.V y) (Φ.cn y) hU D hPE hTB Cm.P.D.toPre.X Φ.Q p.xe.symm (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)) hmo hth K ev₁ k₀ hk τ₁ …`. Establish `hxne : ∀ k, ev (s (.inr k)) ≠ 0` using `fun k => ((h3 k).map ev).ne_zero`. Set `Uk : Fin N → Kˣ` to `fun k => Units.mk0 (ev (s (.inr k))) (hxne k)`. Establish `hc1 : ∀ (x : Φ.X y) cc, ∃ r ∈ k₀, ev₁ (Φ.u y (fun _ => x) cc) ^ 2 = r * ((∏ k, Uk k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ _) (e x) (e x)) : Kˣ) : K)`.

Introduce `x cc`. Take `⟨r, hr, hre⟩` from `hcoef (e x) cc`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.symm_apply_apply] at hre`. Rewrite using `[hre, Units.coe_prod]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hε₁, Units.val_zpow_eq_zpow_val, ← RingHom.comp_apply ev₁ ρ, hev₁]`. Both sides reduce to the same expression. Set `β' : Fin N → LinearMap.BilinForm ℤ (Φ.X y)` to `fun k => pull e.toLinearMap (ε (.inr k))`.

Establish `hβ' : ∀ k, β' k ∈ balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)` using `fun k => pull_mem _ (ε (.inr k)).2`. Establish `hlin1 : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (k : Fin N), lin !![(1 : ℤ)] a (β' k) = ∑ i', (ε (.inr k) : LinearMap.BilinForm ℤ _) (e (a (i', 0))) (e (a (i', 0)))`. Introduce `l₀ a k`. Simplify using `[lin, qW, β']`. Establish `hT : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (cs : Fin l₀ → Φ.Q), ∃ R ∈ k₀, ev₁ (Φ.coefT y a cs) ^ 2 = R * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K)`.

Introduce `l₀ a cs`. Use `choose r hr hre using fun i' => hc1 (a (i', 0)) (cs i')`. Use `⟨∏ i', r i', prod_mem fun i' _ => hr i', ?_⟩` and prove the remaining obligations. Establish `ha : ∀ i', (fun v => a (i', v)) = fun _ => a (i', 0)` using `fun i' => funext fun v => by`. Rewrite using `[Subsingleton.elim v 0]`.

Simplify using `only [VSys.coefT, map_prod, ← Finset.prod_pow, ha, hre, Finset.prod_mul_distrib, hlin1, Finset.mul_sum]`. Use `congr 1`. Rewrite using `[← Units.coe_prod, Finset.prod_comm]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun k _ => (GlobalTheory.USep.Alg.zpow_sum_units _ _ _).symm`.

Set `F : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y) →ₗ[ℤ] ℤ` to `(ε.coord (.inr i)).comp (pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e).symm.toLinearMap`. Take `⟨n, hn, lam, hlam⟩` from `GlobalTheory.USep.Alg.exists_extend_smul (balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) F`. Establish `hF : ∀ β : balForms (H.bar : 𝓞 E → 𝓞 E) Cm.P.D.toPre.X, F ⟨pull e.toLinearMap β, pull_mem _ β.2⟩ = ε.coord (.inr i) β`. Introduce `β`. Establish `: (⟨pull e.toLinearMap β, pull_mem _ β.2⟩ : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) = pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e β` using `rfl`.

Simplify using `only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply]`. Establish `hlam0 : ∀ k, lam (Φ.δ y k) = 0`. Introduce `k`. Establish `e1 : Φ.δ y k = pull e.toLinearMap (((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _) : LinearMap.BilinForm ℤ _)` using `LinearMap.ext₂ fun a b => by`. Rewrite using `[(hmem4 k).2 a b]`.

Simplify using `[h2]`. Establish `e2` using `hlam ⟨pull e.toLinearMap ((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _), pull_mem _ ((l.M' : ℤ) • ε (.inl (h k))).2⟩`. Rewrite `e2` using `[hF]`. Rewrite using `[e1, e2, map_zsmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (by simp)]`. Simplify using the standard rewrite rules.

Take `⟨l₁, l₂, MM, a, a', c₁, c₂, hMM, hu₁, hu₂, hlin, r, hr, hre⟩` from `V3 lam hlam0`. Take `⟨R₁, hR₁, hR₁e⟩` from `hT a c₁`. Take `⟨R₂, hR₂, hR₂e⟩` from `hT a' c₂`. Establish `hlam1 : ∀ k, lam (β' k) = n * if i = k then 1 else 0`. Introduce `k`.

Establish `e2` using `hlam ⟨β' k, hβ' k⟩`. Rewrite `e2` using `[hF (ε (.inr k))]`. Rewrite using `[e2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hik, Ne.symm hik]`. Establish `hG : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K) = ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)`. Rewrite using `[← Units.val_mul]`. Use `congr 1`.

Establish `: ∀ k, (l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k) = (l.M' : ℤ) * (MM * (n * if i = k then 1 else 0)) + (l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)` using `fun k => by`. Rewrite using `[← hlam1, ← hlin _ (hβ' k)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, zpow_add, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Finset.prod_eq_single i (fun k _ hk => by rw [if_neg (Ne.symm hk)]; simp) (by simp)]`. Simplify using the standard rewrite rules. Establish `hne : ev₁ (Φ.coefT y a c₁) ^ 2 ≠ 0` using `pow_ne_zero _ (hu₁.map ev₁).ne_zero`. Establish `hR₁ne : R₁ ≠ 0` using `fun h0 => hne (by rw [hR₁e, h0, zero_mul])`. Establish `key : ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) = r ^ 2 * R₂ / R₁`.

Establish `h5 : R₁ * (((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)) = r ^ 2 * (R₂ * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K))`. Rewrite using `[← hG, ← hR₁e, ← hR₂e, hre, mul_pow]`. Rewrite using `[eq_div_iff hR₁ne]`. Establish `hP : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K) ≠ 0` using `Units.ne_zero _`. Apply `mul_right_cancel₀ hP` to reduce the goal to its premises.

Take the linear combination `h5`. Establish `hmem' : ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) ∈ k₀`. Establish `: ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) = ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K)`. Rewrite using `[Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.

Rewrite using `[this, key]`. Conclude with `div_mem (mul_mem (pow_mem hr 2) hR₂) hR₁`. Use `GlobalTheory.USep.Alg.mem_of_zpow_mem k₀ hk (hxne i) ?_ hmem'` and prove the remaining obligations. Establish `: (l.M' : ℤ) ≠ 0` using `by exact_mod_cast (show l.M' ≠ 0 by omega)`. Conclude with `mul_ne_zero this (mul_ne_zero (by exact_mod_cast (show MM ≠ 0 by omega)) hn)`.
-/
theorem GlobalTheory.USep.sepB_of_normBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d → (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)) (j : Xo.XF c ⟶ S), GlobalTheory.Poinc.IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → IsProper π → j ≫ π = C.iF → IsOpenImmersion j → π ⁻¹' Set.range C.iF = Set.range j → GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hpol hnsi l Xo c C d J hd hJ hval S π j hbl hprop hjπ hj hpre
  intro V _ _ _ Cm hV ξ hξ N s ε τ₀ h1 h2 h3 hτ K _ _ ev k₀ hk hc hdef
  have hξ' : Cm.y ≫ C.iF = jK V ≫ ξ ≫ π := by rw [← hjπ, ← Category.assoc, hξ, Category.assoc]
  obtain ⟨j₀, hdesc⟩ := GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios Cm.P.D.toPre.P.g 3 Nat.prime_three (by decide)
  obtain ⟨jj, M, _, g, z₁, ζ, Φ, y, ρ, e, h, U, hUne, hjj, hcov, htr, hmem⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_family E H Dw hpq l Xo c C φ V Cm hV (ξ ≫ π) hξ' 3 Nat.prime_three (by decide) (max j₀ 1)
  let ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y) := fun k => GlobalTheory.PolFan.pull e.toLinearMap (Cm.δ (h k))
  obtain ⟨ev₁, hev₁, hEl⟩ := GlobalTheory.T.exists_approximating_elements_normalCover_unitary E H Dw hpq l Xo c C φ hpol d J hJ hval S π hbl V Cm hV ξ hξ' _ M g z₁ ζ Φ y ρ e h U hUne
    hcov htr hmem K ev k₀ hk hc hdef ga (fun k a b => rfl)
  obtain ⟨d₀, hd₀, hsup⟩ : ∃ d₀, 1 ≤ d₀ ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ d₀ :=
    exists_hasSupports (𝓞 E) H.bar (min Dw.p Dw.q) φ hpol fun X _ _ _ _ hX r γ hγ =>
      GlobalTheory.T.exists_supportingTuple_smoothCone_cmField E H φ X (hpol X hX) r γ hγ
  have hM' : 1 ≤ l.M' := Nat.one_le_iff_ne_zero.2 (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')
  have hmem4 := hmem.2.2.2.1
  have hδ : ∀ k, Φ.δ y k = (l.M' : ℤ) • ga k := fun k => LinearMap.ext₂ fun a b => by
    rw [(hmem4 k).2 a b]; rfl
  have hN3 : 3 ≤ (3 ^ jj) ^ 2 := by
    have : 3 ≤ 3 ^ jj := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ jj := Nat.pow_le_pow_right (by norm_num) (le_of_max_le_right hjj)
    nlinarith
  obtain ⟨V1, V2, V3⟩ := GlobalTheory.T.poincareApprox_values_at_point_of_elements (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ hpol hnsi d₀ (2 * d) hd₀ (by omega) hsup 0
    !![(1 : ℤ)] Φ.posW _ hN3 _ Φ y ga l.M' hM' ((Cm.cone.pull_equiv e).reindex h) hδ K ev₁ k₀ hEl
  have hρinj : Function.Injective ρ := hmem.1
  obtain ⟨-, -, -, -, D, p, hth⟩ := hmem
  have hU : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Φ.V y) := fun m hm => by
    have := (IsUnit.mk0 (m : c.F) (Nat.cast_ne_zero.2 hm)).map (ρ.comp Cm.b)
    rwa [map_natCast] at this
  have hmo : ∀ mu : Cm.P.D.toPre.X, mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) ≠ 0 ∧
      ∃ cc, IsUnit (Φ.u y (fun _ => e.symm mu) cc) := fun mu =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Φ.t_mem y i).2, Φ.u_unit y _⟩
  obtain ⟨hg, htr'⟩ := GlobalTheory.T.descendsAbelianPart_of_isPullDeg V (Φ.V y) ρ Cm.P.D.toPre D p
  refine (sepAtB_iff _ _ _ _ _).2 ⟨fun i => ?_, ?_, ?_⟩
  · rw [h1 i, ← hev₁, RingHom.comp_apply]
    have := (hmem4 (h.symm i)).1
    rw [Equiv.apply_symm_apply] at this
    rw [← this, map_pow, V1, zero_pow two_ne_zero]
  · have hD := hdesc jj (le_of_max_le_left hjj) (Φ.V y) (Φ.cn y) hU D hg Cm.P.D.toPre.X Φ.Q p.xe.symm
      (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu))
      hmo hth K ev₁ k₀ hk (fun mu cc cc' hu => V2 _ cc cc' hu)
    have := htr' K ev₁ k₀ hD
    rwa [hev₁] at this
  · intro W₀ _ ιb hFB hkb i
    let P : LinearMap.BilinForm ℤ Cm.P.D.toPre.X → LinearMap.BilinForm ℤ D.X :=
      fun β => β.compl₁₂ p.xe.toAddMonoidHom.toIntLinearMap p.xe.toAddMonoidHom.toIntLinearMap
    let ε₁ : Fin Cm.m ⊕ Fin N → LinearMap.BilinForm ℤ D.X :=
      fun x => P ((l.M' : ℤ) • (ε x : LinearMap.BilinForm ℤ Cm.P.D.toPre.X))
    obtain ⟨τ₁, hT1, hF1⟩ := GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg V (Φ.V y) ρ hρinj Cm.P.D.toPre D p τ₀ (Cm.m + N)
      (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Cm.P.D.toPre.X))
      (fun k => ε₁ (finSumFinEquiv.symm k)) (fun k a b => rfl) hτ W₀ ιb hFB
    have hPE : D.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.psi_even
    have hTB : D.TauBimult := GlobalTheory.tauBimult_of_isPullDeg GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.tau_bimult
    have hε₁ : ∀ x mu, ε₁ x (p.xe.symm mu) (p.xe.symm mu) = (l.M' : ℤ) * (ε x : LinearMap.BilinForm ℤ _) mu mu := by
      intro x mu; simp [ε₁, P]
    have hmo2 : ∀ mu, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)) ^ 2
        = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (s (.inl k))) ^ ε₁ (.inl k) (p.xe.symm mu) (p.xe.symm mu) := by
      intro mu
      have hq : ∀ k', (qW !![(1 : ℤ)] (Φ.δ y k') fun _ => e.symm mu) = (l.M' : ℤ) * Cm.δ (h k') mu mu := fun k' => by
        simp [qW, (hmem4 k').2]
      have hnn : ∀ k, 0 ≤ (l.M' : ℤ) * Cm.δ k mu mu := fun k => mul_nonneg (by positivity) (Cm.cone.nonneg k mu)
      simp only [mono, hq, hε₁, h2, h1]
      calc (algebraMap (Φ.V y) (FractionRing (Φ.V y)) (∏ k', Φ.t y k' ^ ((l.M' : ℤ) * Cm.δ (h k') mu mu).toNat)) ^ 2
          = ∏ k', algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (Cm.s (h k'))) ^ ((l.M' : ℤ) * Cm.δ (h k') mu mu).toNat := by
            rw [map_prod, ← Finset.prod_pow]
            refine Finset.prod_congr rfl fun k' _ => ?_
            rw [← (hmem4 k').1, map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k') 2]
            rw [map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k')]
            exact pow_right_comm (M := FractionRing (Φ.V y)) _ _ _
        _ = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (Cm.s k)) ^ ((l.M' : ℤ) * Cm.δ k mu mu).toNat :=
            Fintype.prod_equiv h _ _ (fun _ => rfl)
        _ = _ := Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, Int.toNat_of_nonneg (hnn k)]
    have hcoef := GlobalTheory.T.thetaTerm_coefficient_sq_eq_monomial_subfield ((3 ^ jj) ^ 2) (by omega) (Φ.V y) (Φ.cn y) hU D hPE hTB Cm.P.D.toPre.X Φ.Q p.xe.symm
      (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu))
      hmo hth K ev₁ k₀ hk τ₁ Cm.m N (fun x => ρ (s x)) ε₁ (fun k => (h3 k).map ρ) hT1 hmo2 W₀ (ρ.comp ιb) hF1
      (fun a => by rw [RingHom.comp_apply, ← RingHom.comp_apply ev₁, hev₁]; exact hkb a)
    have hxne : ∀ k, ev (s (.inr k)) ≠ 0 := fun k => ((h3 k).map ev).ne_zero
    let Uk : Fin N → Kˣ := fun k => Units.mk0 (ev (s (.inr k))) (hxne k)
    have hc1 : ∀ (x : Φ.X y) cc, ∃ r ∈ k₀, ev₁ (Φ.u y (fun _ => x) cc) ^ 2 =
        r * ((∏ k, Uk k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ _) (e x) (e x)) : Kˣ) : K) := by
      intro x cc
      obtain ⟨r, hr, hre⟩ := hcoef (e x) cc
      refine ⟨r, hr, ?_⟩
      simp only [LinearEquiv.symm_apply_apply] at hre
      rw [hre, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hε₁, Units.val_zpow_eq_zpow_val, ← RingHom.comp_apply ev₁ ρ, hev₁]
      rfl
    let β' : Fin N → LinearMap.BilinForm ℤ (Φ.X y) := fun k => pull e.toLinearMap (ε (.inr k))
    have hβ' : ∀ k, β' k ∈ balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y) := fun k => pull_mem _ (ε (.inr k)).2
    have hlin1 : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (k : Fin N),
        lin !![(1 : ℤ)] a (β' k) = ∑ i', (ε (.inr k) : LinearMap.BilinForm ℤ _) (e (a (i', 0))) (e (a (i', 0))) := by
      intro l₀ a k
      simp [lin, qW, β']
    have hT : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (cs : Fin l₀ → Φ.Q), ∃ R ∈ k₀,
        ev₁ (Φ.coefT y a cs) ^ 2 = R * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K) := by
      intro l₀ a cs
      choose r hr hre using fun i' => hc1 (a (i', 0)) (cs i')
      refine ⟨∏ i', r i', prod_mem fun i' _ => hr i', ?_⟩
      have ha : ∀ i', (fun v => a (i', v)) = fun _ => a (i', 0) := fun i' => funext fun v => by
        rw [Subsingleton.elim v 0]
      simp only [VSys.coefT, map_prod, ← Finset.prod_pow, ha, hre, Finset.prod_mul_distrib, hlin1, Finset.mul_sum]
      congr 1
      rw [← Units.coe_prod, Finset.prod_comm]
      congr 1
      exact Finset.prod_congr rfl fun k _ => (GlobalTheory.USep.Alg.zpow_sum_units _ _ _).symm
    let F : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y) →ₗ[ℤ] ℤ :=
      (ε.coord (.inr i)).comp (pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e).symm.toLinearMap
    obtain ⟨n, hn, lam, hlam⟩ := GlobalTheory.USep.Alg.exists_extend_smul (balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) F
    have hF : ∀ β : balForms (H.bar : 𝓞 E → 𝓞 E) Cm.P.D.toPre.X,
        F ⟨pull e.toLinearMap β, pull_mem _ β.2⟩ = ε.coord (.inr i) β := by
      intro β
      have : (⟨pull e.toLinearMap β, pull_mem _ β.2⟩ : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) =
        pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e β := rfl
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply]
    have hlam0 : ∀ k, lam (Φ.δ y k) = 0 := by
      intro k
      have e1 : Φ.δ y k = pull e.toLinearMap (((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _) :
          LinearMap.BilinForm ℤ _) := LinearMap.ext₂ fun a b => by
        rw [(hmem4 k).2 a b]
        simp [h2]
      have e2 := hlam ⟨pull e.toLinearMap ((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _),
        pull_mem _ ((l.M' : ℤ) • ε (.inl (h k))).2⟩
      rw [hF] at e2
      rw [e1, e2, map_zsmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (by simp)]
      simp
    obtain ⟨l₁, l₂, MM, a, a', c₁, c₂, hMM, hu₁, hu₂, hlin, r, hr, hre⟩ := V3 lam hlam0
    obtain ⟨R₁, hR₁, hR₁e⟩ := hT a c₁
    obtain ⟨R₂, hR₂, hR₂e⟩ := hT a' c₂
    have hlam1 : ∀ k, lam (β' k) = n * if i = k then 1 else 0 := by
      intro k
      have e2 := hlam ⟨β' k, hβ' k⟩
      rw [hF (ε (.inr k))] at e2
      rw [e2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, Ne.symm hik]
    have hG : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K) =
        ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K) := by
      rw [← Units.val_mul]
      congr 1
      have : ∀ k, (l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k) =
          (l.M' : ℤ) * (MM * (n * if i = k then 1 else 0)) + (l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k) := fun k => by
        rw [← hlam1, ← hlin _ (hβ' k)]; ring
      simp only [this, zpow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single i (fun k _ hk => by rw [if_neg (Ne.symm hk)]; simp) (by simp)]
      simp
    have hne : ev₁ (Φ.coefT y a c₁) ^ 2 ≠ 0 := pow_ne_zero _ (hu₁.map ev₁).ne_zero
    have hR₁ne : R₁ ≠ 0 := fun h0 => hne (by rw [hR₁e, h0, zero_mul])
    have key : ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) = r ^ 2 * R₂ / R₁ := by
      have h5 : R₁ * (((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) *
          ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)) =
          r ^ 2 * (R₂ * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)) := by
        rw [← hG, ← hR₁e, ← hR₂e, hre, mul_pow]
      rw [eq_div_iff hR₁ne]
      have hP : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K) ≠ 0 := Units.ne_zero _
      apply mul_right_cancel₀ hP
      linear_combination h5
    have hmem' : ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) ∈ k₀ := by
      have : ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) = ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) := by
        rw [Units.val_zpow_eq_zpow_val]; rfl
      rw [this, key]
      exact div_mem (mul_mem (pow_mem hr 2) hR₂) hR₁
    refine GlobalTheory.USep.Alg.mem_of_zpow_mem k₀ hk (hxne i) ?_ hmem'
    have : (l.M' : ℤ) ≠ 0 := by exact_mod_cast (show l.M' ≠ 0 by omega)
    exact mul_ne_zero this (mul_ne_zero (by exact_mod_cast (show MM ≠ 0 by omega)) hn)
