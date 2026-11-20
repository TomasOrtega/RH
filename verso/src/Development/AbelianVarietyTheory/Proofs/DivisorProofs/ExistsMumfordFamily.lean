import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbLocusIffOfMonomialTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriodsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.TChart

/- English proof (translation)
Introduce `K _ _ κ x hx`. Set `b₀ : o →+* K` to `(κ.comp (algebraMap R (FractionRing R))).comp b`. Establish `hb₀ : ((spMap κ ≫ jK R) ≫ f) ≫ s = spMap b₀`. Rewrite using `[Category.assoc, hf]`. Simplify using `only [b₀, spMap, jK, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`.

Take `⟨-, h2, -⟩` from `c.geom K ((spMap κ ≫ jK R) ≫ f) b₀ (hζ.map b₀).unit hb₀ rfl`. Take `⟨a, ha⟩` from `h2 (pushHom hβ (Over.mk (spMap κ ≫ jK R)) x) (by rw [← map_pow, hx, map_one])`. Establish `ha' : ((spMap κ ≫ jK R) ≫ f) ≫ (c.lev a).left = x.left ≫ β` using `congrArg (fun q => q.left) ha`. Establish `hl : (c.lev a).left ≫ c.A.hom = 𝟙 S` using `Over.w (c.lev a)`. Establish `w : (jK R ≫ f ≫ (c.lev a).left) ≫ c.A.hom = jK R ≫ f`.

Simplify using `only [Category.assoc]`. Use `erw [hl, Category.comp_id]`. Use `⟨Over.homMk (hβ.1.lift (jK R ≫ f ≫ (c.lev a).left) (jK R) w) (hβ.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Apply `hβ.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← ha'] show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ β`.

Rewrite using `[Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_fst]`. Simplify using `only [Category.assoc]`. Use `show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ B.hom`. Rewrite using `[Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_snd]`. Conclude with `Over.w x`.
-/
theorem torsRat_of_isGrpPullback_siegPre {S : Scheme.{0}} {h n : ℕ} {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ)
    {s : S ⟶ Sp o} (c : SiegPre h n ζ s) {R : Type} [CommRing R] [IsDomain R] (b : o →+* R) (B : Over (Sp R)) [GrpObj B]
    (f : Sp R ⟶ S) (hf : f ≫ s = spMap b) (β : B.left ⟶ c.A.left) (hβ : IsGrpPullback B c.A f β) : TorsRat B n := by
  intro K _ _ κ x hx
  let b₀ : o →+* K := (κ.comp (algebraMap R (FractionRing R))).comp b
  have hb₀ : ((spMap κ ≫ jK R) ≫ f) ≫ s = spMap b₀ := by
    rw [Category.assoc, hf]
    simp only [b₀, spMap, jK, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨-, h2, -⟩ := c.geom K ((spMap κ ≫ jK R) ≫ f) b₀ (hζ.map b₀).unit hb₀ rfl
  obtain ⟨a, ha⟩ := h2 (pushHom hβ (Over.mk (spMap κ ≫ jK R)) x) (by rw [← map_pow, hx, map_one])
  have ha' : ((spMap κ ≫ jK R) ≫ f) ≫ (c.lev a).left = x.left ≫ β := congrArg (fun q => q.left) ha
  have hl : (c.lev a).left ≫ c.A.hom = 𝟙 S := Over.w (c.lev a)
  have w : (jK R ≫ f ≫ (c.lev a).left) ≫ c.A.hom = jK R ≫ f := by
    simp only [Category.assoc]
    erw [hl, Category.comp_id]
  refine ⟨Over.homMk (hβ.1.lift (jK R ≫ f ≫ (c.lev a).left) (jK R) w) (hβ.1.lift_snd _ _ _), ?_⟩
  apply hβ.1.hom_ext
  · rw [← ha']
    show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ β
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_fst]
    simp only [Category.assoc]
  · show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ B.hom
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_snd]
    exact Over.w x

/- English proof (translation)
Take `⟨β, -, -, hβ, -⟩` from `C.data`. Use `torsRat_of_isGrpPullback_siegPre hζ C.F.univ C.b C.Q.B _ ?_ _ (IsGrpPullback.comp hβ C.cart)` and prove the remaining obligations. Use `C.u_base` as an intermediate fact. Rewrite `this` using `[LowChart.toO]`. Rewrite using `[Category.assoc, Category.assoc, this]`.

Simplify using `only [Taut.b, Taut.iw, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`.
-/
theorem Taut.torsRat_B {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ) {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) :
    TorsRat C.Q.B n := by
  obtain ⟨β, -, -, hβ, -⟩ := C.data
  refine torsRat_of_isGrpPullback_siegPre hζ C.F.univ C.b C.Q.B _ ?_ _ (IsGrpPullback.comp hβ C.cart)
  have := C.u_base
  rw [LowChart.toO] at this
  rw [Category.assoc, Category.assoc, this]
  simp only [Taut.b, Taut.iw, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/- English proof (translation)
Introduce `g n φ hn _ C`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `hn1 : (0 : ℤ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn0`. Take `⟨hreg, hchar, hinj, -⟩` from `Taut.isRegularLocalRing_and_isRelParam g n φ hn C`. Take `⟨hmono, -, hcone, hdef, ht⟩` from `Taut.monomial_chart g n φ (by omega) C`.

Establish `hCN : IsCN C.R` using `⟨C.compl.1, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R).2, C.compl.2.1, hchar⟩`. Establish `hsym : ∀ k a b, ((n : ℤ) • C.δ k) a b = ((n : ℤ) • C.δ k) b a` using `fun k a b => by`. Simplify using `only [LinearMap.smul_apply, (hcone.mem k).1 a b]`. Establish `hnn : ∀ k a, 0 ≤ ((n : ℤ) • C.δ k) a a` using `fun k a => by`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `mul_nonneg hn1.le (hcone.nonneg k a)`. Establish `hpos : ∀ a, a ≠ 0 → ∃ k, 0 < ((n : ℤ) • C.δ k) a a` using `fun a ha => by`. Take `⟨k, hk⟩` from `hdef a ha`. Conclude with `⟨k, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn1 hk⟩`. Establish `hne : ∀ k, (n : ℤ) • C.δ k ≠ 0` using `fun k hk => by`.

Apply `C.ε.ne_zero (.inl k)` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext fun a => LinearMap.ext fun b => ?_` and prove the remaining obligations. Establish `h1 : (n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e (C.e.symm a)) (C.e (C.e.symm b)) = 0` using `congrArg (fun B : LinearMap.BilinForm ℤ C.Q.X => B (C.e.symm a) (C.e.symm b)) hk`. Rewrite `h1` using `[C.e.apply_symm_apply, C.e.apply_symm_apply]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left hn1.ne'`. Establish `hQ : C.Q.IsPos (maximalIdeal C.R)` using `hmono.isPos (fun k => C.bd k) hnn hpos`. Take `⟨G, _, _, P, hM, hC⟩` from `GlobalTheory.T.exists_canonical_mumford_family_monomial_periods C.R hCN C.Q hQ C.m C.t _ hmono ht hsym hnn hpos`. Establish `hζ : IsPrimitiveRoot (zetaAway n) n` using `IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective`. Use `⟨G, inferInstance, inferInstance, P, hM, hC, GlobalTheory.Mum.abLocus_iff_of_monomialTau C.R hCN C.Q hQ G P hM C.m C.t _ (fun k => ⟨C.bd k, ht k⟩) hsym hnn hpos hne hmono, ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.T.nTorsion_rational_canonicalFamily_dividedData C.T C.R _ _ _ n hCN (by omega) (by simpa using (isUnit_natCast hn0).map C.b) (C.b (zetaAway n)) (hζ.map_of_injective hinj) C.Q C.e C.data (C.torsRat_B (hζ.isUnit hn0)) G P hC.canon`.
-/
theorem Taut.exists_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  intro g n φ hn _ C
  have hn0 : n ≠ 0 := by omega
  have hn1 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  obtain ⟨hreg, hchar, hinj, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  have hCN : IsCN C.R :=
    ⟨C.compl.1, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R).2, C.compl.2.1, hchar⟩
  have hsym : ∀ k a b, ((n : ℤ) • C.δ k) a b = ((n : ℤ) • C.δ k) b a := fun k a b => by
    simp only [LinearMap.smul_apply, (hcone.mem k).1 a b]
  have hnn : ∀ k a, 0 ≤ ((n : ℤ) • C.δ k) a a := fun k a => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hn1.le (hcone.nonneg k a)
  have hpos : ∀ a, a ≠ 0 → ∃ k, 0 < ((n : ℤ) • C.δ k) a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn1 hk⟩
  have hne : ∀ k, (n : ℤ) • C.δ k ≠ 0 := fun k hk => by
    apply C.ε.ne_zero (.inl k)
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have h1 : (n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e (C.e.symm a)) (C.e (C.e.symm b)) = 0 :=
      congrArg (fun B : LinearMap.BilinForm ℤ C.Q.X => B (C.e.symm a) (C.e.symm b)) hk
    rw [C.e.apply_symm_apply, C.e.apply_symm_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left hn1.ne'
  have hQ : C.Q.IsPos (maximalIdeal C.R) := hmono.isPos (fun k => C.bd k) hnn hpos
  obtain ⟨G, _, _, P, hM, hC⟩ := GlobalTheory.T.exists_canonical_mumford_family_monomial_periods C.R hCN C.Q hQ C.m C.t _ hmono ht hsym hnn hpos
  have hζ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  refine ⟨G, inferInstance, inferInstance, P, hM, hC,
    GlobalTheory.Mum.abLocus_iff_of_monomialTau C.R hCN C.Q hQ G P hM C.m C.t _ (fun k => ⟨C.bd k, ht k⟩) hsym hnn hpos hne hmono, ?_⟩
  exact GlobalTheory.T.nTorsion_rational_canonicalFamily_dividedData C.T C.R _ _ _ n hCN (by omega) (by simpa using (isUnit_natCast hn0).map C.b) (C.b (zetaAway n))
    (hζ.map_of_injective hinj) C.Q C.e C.data (C.torsRat_B (hζ.isUnit hn0)) G P hC.canon

end GlobalTheory.TChart
