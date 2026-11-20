import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

/- English proof (translation)
Use `show (toUnit X ≫ η[M]).left = _`. Rewrite using `[Over.comp_left]`. Use `congr 1`.
-/
theorem one_left'' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  congr 1

def anE (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) :
    (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left) :=
  fun z => (F.ex i P z).left

/- English proof (translation)
Establish `hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P)` using `⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩`. Establish `h2` using `(F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2`. Introduce `U f`. Take `⟨ho, hd⟩` from `h2 U f`. Establish `hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))` using `by fun_prop`.

Establish `hc` using `hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `ho.preimage hι.continuous using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `[anE]`.

Use `hc using 1 all_goals` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `[anE]`.
-/
theorem anHol (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : IsHolFam (anE F i P) := by
  have hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h2 := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  intro U f
  obtain ⟨ho, hd⟩ := h2 U f
  have hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  have hc := hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)
  refine ⟨?_, ?_⟩
  · convert ho.preimage hι.continuous using 1
    ext z
    simp [anE]
  · convert hc using 1
    all_goals
      ext z
      simp [anE]

variable [Algebra c.F ℂ]

def anX (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (m : ℕ) : jO y g m 1 ⟶ Xo.univ.t.G :=
  Over.homMk (jetPt (anE F i P) (anHol F i P hP) m) (by
    rw [jetPt_over (anE F i P) (anHol F i P hP) Xo.univ.t.G.hom (F.u i P) (fun z => Over.w (F.ex i P z)) m, ← hy]
    rfl)

variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem anX_left (m : ℕ) : (anX F i P hP y hy m).left = jetPt (anE F i P) (anHol F i P hP) m := rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, anX_left, anX_left]`. Conclude with `jetPt_trunc (e := anE F i P) (hol := anHol F i P hP) m`.
-/
theorem anX_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ anX F i P hP y hy (m + 1) =
      anX F i P hP y hy m := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, anX_left, anX_left]
  exact jetPt_trunc (e := anE F i P) (hol := anHol F i P hP) m

include hP in
/- English proof (translation)
Simplify using `using F.ex_add i P hP 0 0`.
-/
theorem ex_zero_eq_one : F.ex i P 0 = 1 := by
  simpa using F.ex_add i P hP 0 0

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, anX_left]`. Use `(jetPt_aug (anE F i P) (anHol F i P hP) m).trans ?_` and prove the remaining obligations. Use `show (F.ex i P 0).left = _`. Rewrite using `[ex_zero_eq_one F i P hP, one_left'', one_left'']`.

Use `congr 1`. Rewrite using `[← hy]`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 _` using `by first`. Consider the case `simp [spMap]`. Consider the case `(simp only [spMap]`.

Rewrite using `[show CommRingCat.ofHom (RingHom.id ℂ) = 𝟙 _ from rfl, Spec.map_id])`. Simplify using `[overAt, hid]`.
-/
theorem anX_zero (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ anX F i P hP y hy m = 1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, anX_left]
  refine (jetPt_aug (anE F i P) (anHol F i P hP) m).trans ?_
  show (F.ex i P 0).left = _
  rw [ex_zero_eq_one F i P hP, one_left'', one_left'']
  congr 1
  rw [← hy]
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by
    first
      | simp [spMap]
      | (simp only [spMap]
         rw [show CommRingCat.ofHom (RingHom.id ℂ) = 𝟙 _ from rfl, Spec.map_id])
  simp [overAt, hid]

/- English proof (translation)
Establish `key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j)`. Introduce `a j`. Rewrite using `[Fintype.sum_eq_single (e' j)]`. Simplify using the standard rewrite rules. Introduce `ℓ hℓ`.

Establish `hne : j ≠ e'.symm ℓ`. Introduce `h`. Apply `hℓ` to reduce the goal to its premises. Rewrite using `[h, Equiv.apply_symm_apply]`. Simplify using `[hne]`.

Use `⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `ℓ`. Establish `h1` using `ha (e'.symm ℓ)`.

Rewrite `h1` using `[key, Equiv.apply_symm_apply]`. Conclude with `h1`.
-/
theorem basis_single (e' : Fin g ≃ Lt1 Dw) (v : Fin g → ℂ) :
    ∃! a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = v j := by
  have key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j) := by
    intro a j
    rw [Fintype.sum_eq_single (e' j)]
    · simp
    · intro ℓ hℓ
      have hne : j ≠ e'.symm ℓ := by
        intro h
        apply hℓ
        rw [h, Equiv.apply_symm_apply]
      simp [hne]
  refine ⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp
  · funext ℓ
    have h1 := ha (e'.symm ℓ)
    rw [key, Equiv.apply_symm_apply] at h1
    exact h1

def anAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Fin g → MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun k => MvPowerSeries.C (ty k (a : E)) * MvPowerSeries.X ((0 : Fin 1), k)

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Unfold `jetSubstP jetScaleP`. Rewrite using `[Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]`. Establish `key : ∀ p : Fin 1 × Fin g, Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1)) (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) = Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1)) (MvPolynomial.C (ty p.2 (a : E)) * MvPoly …`. Introduce and unpack `⟨i, k⟩`.

Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Use `set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq`. Establish `hps : psTrunc m (anAct ty a k) = if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0`. Unfold `psTrunc anAct`.

Distinguish the cases in `hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))`. Rewrite using `[if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]`. Simplify using `[MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]`. Introduce `e _ he`. Simplify using `[MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]`.

Introduce `h`. Conclude with `absurd hmem h`. Rewrite using `[if_neg hmem]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `e he`.

Establish `hne : e ≠ Finsupp.single q 1` using `fun h => hmem (h ▸ he)`. Simplify using `[MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]`. Rewrite using `[hps]`. Distinguish the cases in `hm0 : m = 0`. Substitute `hm0` using the available equality.

Establish `hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ))`. Introduce `hmem`. Rewrite `hmem` using `[degLE, Finset.mem_filter]`. Use `hmem.2` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_single_index rfl]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hnot]`. Simplify using `only [map_zero, sub_zero]`. Use `symm`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)`. Establish `hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))`. Rewrite using `[degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]`. Use `⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩` and prove the remaining obligations. Use extensionality with `j`.

Distinguish the cases in `hj : j = q`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, Finsupp.single_apply, Ne.symm hj]`. Rewrite using `[if_pos hmem]`.

Simplify using `[MvPolynomial.constantCoeff_X, hq]`. Use `show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)`. Rewrite using `[← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]`. Use `congr 2`. Use function extensionality and compare the values at `p`.

Conclude with `key p`.
-/
theorem jetSubstP_anAct (m : ℕ) (a : 𝓞 E) (b : Jet ℂ (Fin 1 × Fin g) m) :
    jetSubstP m (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) b =
      jetScaleP m (fun k => ty k (a : E)) b := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  unfold jetSubstP jetScaleP
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]
  have key : ∀ p : Fin 1 × Fin g,
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) =
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (MvPolynomial.C (ty p.2 (a : E)) * MvPolynomial.X p) := by
    rintro ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq
    have hps : psTrunc m (anAct ty a k) =
        if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then
          MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0 := by
      unfold psTrunc anAct
      by_cases hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))
      · rw [if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]
        · simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]
        · intro e _ he
          simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]
        · intro h
          exact absurd hmem h
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ Finsupp.single q 1 := fun h => hmem (h ▸ he)
        simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]
    rw [hps]
    by_cases hm0 : m = 0
    · subst hm0
      have hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        intro hmem
        rw [degLE, Finset.mem_filter] at hmem
        have := hmem.2
        rw [Finsupp.sum_single_index rfl] at this
        omega
      rw [if_neg hnot]
      simp only [map_zero, sub_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · have hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        rw [degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]
        refine ⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩
        ext j
        by_cases hj : j = q
        · subst hj
          simp
        · simp [hj, Finsupp.single_apply, Ne.symm hj]
      rw [if_pos hmem]
      simp [MvPolynomial.constantCoeff_X, hq]
  show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext p
  exact key p

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, anX_left, homAt, Over.homMk_left]`. Establish `hol'` using `isHolFam_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left`. Establish `hc : ∀ z, anE F i P z ≫ (Xo.univ.t.act.act a).left = anE F i P (fun k => ty k (a : E) * z k)` using `fun z => by`. Unfold `anE`.

Rewrite using `[F.ex_lin i P hP a z, Over.comp_left]`. Establish `h0 : (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) 0 = anE F i P 0` using `by show anE F i P 0 ≫ (Xo.univ.t.act.act a).left = anE F i P 0`. Rewrite using `[hc]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Establish `hloc : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)`. Unfold `jetSubstP`. Conclude with `isLocalHom_jetMap _ _`. Rewrite using `[jetPt_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left _ hol' (fun z => rfl) m]`.

Use `(jetPt_precomp (anE F i P) (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) (anHol F i P hP) hol' h0 m ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) …` and prove the remaining obligations. Introduce `U hU f`. Repeatedly rewrite using `[hc]`. Rewrite using `[jetOf_scale m (fun k => ty k (a : E)) (contDiffAt_val (e := anE F i P) (hol := anHol F i P hP) hU f)]`. Conclude with `jetSubstP_anAct m a _`.
-/
theorem anX_act (m : ℕ) (a : 𝓞 E) :
    anX F i P hP y hy m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ anX F i P hP y hy m := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, anX_left, homAt, Over.homMk_left]
  have hol' := isHolFam_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left
  have hc : ∀ z, anE F i P z ≫ (Xo.univ.t.act.act a).left = anE F i P (fun k => ty k (a : E) * z k) := fun z => by
    unfold anE
    rw [F.ex_lin i P hP a z, Over.comp_left]
  have h0 : (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) 0 = anE F i P 0 := by
    show anE F i P 0 ≫ (Xo.univ.t.act.act a).left = anE F i P 0
    rw [hc]
    congr 1
    funext k
    simp
  have hloc : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) := by
    unfold jetSubstP
    exact isLocalHom_jetMap _ _
  rw [jetPt_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left _ hol' (fun z => rfl) m]
  refine (jetPt_precomp (anE F i P) (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) (anHol F i P hP) hol' h0 m
    ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)
    (hχl := hloc) ?_).symm
  intro U hU f
  simp_rw [hc]
  rw [jetOf_scale m (fun k => ty k (a : E)) (contDiffAt_val (e := anE F i P) (hol := anHol F i P hP) hU f)]
  exact jetSubstP_anAct m a _

/- English proof (translation)
Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Simplify using `only [jetTan, jetAug, liftJet]`. Apply the tactic sequence `try simp only [Ideal.Quotient.liftₐ_apply]`. Use `erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]`. Apply the tactic sequence `try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r => simp [TrivSqZeroExt.algebraMap_eq_inl]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p j hp`. Apply the tactic sequence `by_cases hj : j = ℓ <;> simp [hj, hp]`.
-/
theorem fst_jetTan (ℓ : Fin 1 × Fin g) (a : Jet ℂ (Fin 1 × Fin g) (0 + 1)) :
    ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) a).fst =
      (jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [jetTan, jetAug, liftJet]
  try simp only [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  induction p using MvPolynomial.induction_on with
  | C r => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = ℓ <;> simp [hj, hp]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [epsMul]`.
-/
theorem epsMul_algebraMap (cc : ℂ) (a : ℂ) : epsMul cc (algebraMap ℂ (DualNumber ℂ) a) = algebraMap ℂ _ a := by
  ext <;> simp [epsMul]

def epsHom (x : Sp ℂ ⟶ Xo.X) (cc : ℂ) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul cc)) (by
    show spMap (epsMul cc) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a => epsMul_algebraMap cc a)

/- English proof (translation)
Establish `h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ)`. Use `RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Simplify using `[epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `[epsMul, TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]`.
-/
theorem spMap_epsMul_zero_jetTan (ℓ : Fin 1 × Fin g) :
    spMap (epsMul (0 : ℂ)) ≫ spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
  have h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp
      ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · simp [epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [epsMul]`.
-/
theorem epsMul_one : epsMul (1 : ℂ) = RingHom.id (DualNumber ℂ) := by
  ext x <;> simp [epsMul]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro u j`. Conclude with `j.elim0`. Consider the case `succ n ih`.

Introduce `u j h`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Consider the cases of `j using Fin.cases with`. Consider the case `zero`. Establish `h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1`.

Apply `List.prod_eq_one` to reduce the goal to its premises. Introduce `x hx`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `h i.succ (Fin.succ_ne_zero i)`. Rewrite using `[h1, _root_.mul_one]`.

Consider the case `succ j'`. Rewrite using `[h 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]`. Conclude with `ih (fun i => u i.succ) j' (fun i hi => h i.succ (fun e => hi (Fin.succ_injective _ e)))`.
-/
private theorem prod_ofFn_single_lemma {M : Type*} [Monoid M] :
    ∀ (n : ℕ) (u : Fin n → M) (j : Fin n), (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j h
    rw [List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact h i.succ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    | succ j' =>
      rw [h 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' (fun i hi => h i.succ (fun e => hi (Fin.succ_injective _ e)))

/- English proof (translation)
Use `⟨fun k => if k = j0 then homAt y.x (jetTan ((0 : Fin 1), j0) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ anX F i P hP y hy (0 + 1) else 1, fun k => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = j0`. Substitute `hk` using the available equality. Simplify using `only [if_true, epsMul_one]`. Simplify using `[spMap]`.

Simplify using `only [if_neg hk]`. Rewrite using `[one_left'']`. Simplify using `only [Over.comp_left, homAt, Over.homMk_left, anX_left]`. Rewrite using `[← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug]`. Unfold `anE`.

Rewrite using `[ex_zero_eq_one F i P hP, one_left'']`. Simplify using `only [Over.mk_hom, Category.assoc, hy]`. Rewrite using `[prod_ofFn_single_lemma g _ j0 (fun k hk => if_neg hk), if_pos rfl]`. Simplify using `only [Over.comp_left, homAt, Over.homMk_left, anX_left]`. Conclude with `jetPt_tan (anE F i P) (anHol F i P hP) ((0 : Fin 1), j0) vt hd`.
-/
theorem anX_tan (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (anE F i P) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        anX F i P hP y hy (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  refine ⟨fun k => if k = j0 then homAt y.x (jetTan ((0 : Fin 1), j0) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ anX F i P hP y hy (0 + 1) else 1, fun k => ?_, ?_⟩
  · by_cases hk : k = j0
    · subst hk
      simp only [if_true, epsMul_one]
      simp [spMap]
    · simp only [if_neg hk]
      rw [one_left'']
      simp only [Over.comp_left, homAt, Over.homMk_left, anX_left]
      rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug]
      unfold anE
      rw [ex_zero_eq_one F i P hP, one_left'']
      simp only [Over.mk_hom, Category.assoc, hy]
  · rw [prod_ofFn_single_lemma g _ j0 (fun k hk => if_neg hk), if_pos rfl]
    simp only [Over.comp_left, homAt, Over.homMk_left, anX_left]
    exact jetPt_tan (anE F i P) (anHol F i P hP) ((0 : Fin 1), j0) vt hd

end ReciprocityTheory.ChartRestriction.G.PullbackSections
