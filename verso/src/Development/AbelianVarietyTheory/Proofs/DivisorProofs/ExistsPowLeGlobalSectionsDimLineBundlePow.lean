import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

namespace AmpleBig

/- English proof (translation)
Take `⟨e, g, hg, hf⟩` from `exists_finite_inj_algHom_of_fg k R`. Use `⟨e, fun i => g (MvPolynomial.X i), ?_, ?_⟩` and prove the remaining obligations. Establish `e : MvPolynomial.aeval (fun i => g (MvPolynomial.X i)) = g` using `(MvPolynomial.aeval_unique g).symm`. Rewrite using `[algebraicIndependent_iff_injective_aeval, e]`. Conclude with `hg`.

Use `letI := g.toRingHom.toAlgebra`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin e) k) R` using `⟨RingHom.Finite.to_isIntegral hf⟩`. Use `(Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin e) k) R)) fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ringKrullDim _ ≤ _`. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`.

Simplify using the standard rewrite rules.
-/
theorem exists_algebraicIndependent (k R : Type) [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (e : ℕ) (y : Fin e → R), AlgebraicIndependent k y ∧ ringKrullDim R ≤ e := by
  obtain ⟨e, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨e, fun i => g (MvPolynomial.X i), ?_, ?_⟩
  · have e : MvPolynomial.aeval (fun i => g (MvPolynomial.X i)) = g :=
      (MvPolynomial.aeval_unique g).symm
    rw [algebraicIndependent_iff_injective_aeval, e]
    exact hg
  · letI := g.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin e) k) R := ⟨RingHom.Finite.to_isIntegral hf⟩
    refine (Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin e) k) R))
      fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h).trans ?_
    change ringKrullDim _ ≤ _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp

/- English proof (translation)
Set `d : (Fin e → Fin (n + 1)) → (Fin e →₀ ℕ)` to `fun α => Finsupp.equivFunOnFinite.symm fun i => (α i : ℕ)`. Establish `hd : Function.Injective d` using `fun α β h =>`. Use function extensionality and compare the values at `fun i => Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)`. Establish `h₁` using `((MvPolynomial.basisMonomials (Fin e) k).linearIndependent.comp d hd).map' (LinearMap.mulLeft k σ ∘ₗ (MvPolynomial.aeval y).toLinearMap) (LinearMap.ker_eq_bot.2 ((mul_right_injective₀ hσ).comp hy))`. Establish `e : (fun α : Fin e → Fin (n + 1) => σ * ∏ i, y i ^ (α i : ℕ)) = (LinearMap.mulLeft k σ ∘ₗ (MvPolynomial.aeval y).toLinearMap) ∘ MvPolynomial.basisMonomials (Fin e) k ∘ d` using `funext fun α => by`.

Simplify using `[d, MvPolynomial.aeval_monomial, Finsupp.prod_fintype]`. Rewrite using `[e]`. Conclude with `h₁`.
-/
theorem linearIndependent_monomials {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {e : ℕ} {y : Fin e → R} (hy : AlgebraicIndependent k y) {σ : R} (hσ : σ ≠ 0) (n : ℕ) :
    LinearIndependent k fun α : Fin e → Fin (n + 1) => σ * ∏ i, y i ^ (α i : ℕ) := by
  let d : (Fin e → Fin (n + 1)) → (Fin e →₀ ℕ) := fun α =>
    Finsupp.equivFunOnFinite.symm fun i => (α i : ℕ)
  have hd : Function.Injective d := fun α β h =>
    funext fun i => Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)
  have h₁ := ((MvPolynomial.basisMonomials (Fin e) k).linearIndependent.comp d hd).map'
    (LinearMap.mulLeft k σ ∘ₗ (MvPolynomial.aeval y).toLinearMap)
    (LinearMap.ker_eq_bot.2 ((mul_right_injective₀ hσ).comp hy))
  have e : (fun α : Fin e → Fin (n + 1) => σ * ∏ i, y i ^ (α i : ℕ)) =
      (LinearMap.mulLeft k σ ∘ₗ (MvPolynomial.aeval y).toLinearMap) ∘
        MvPolynomial.basisMonomials (Fin e) k ∘ d := funext fun α => by
    simp [d, MvPolynomial.aeval_monomial, Finsupp.prod_fintype]
  rw [e]
  exact h₁

variable {X : Scheme.{0}} {L : LB X}

def IsLocalFn {J : PUnit → L.ι} {V : X.Opens} (h : V ≤ powChart L J) (n : ℕ) (r : Γ(X, V)) : Prop :=
  ∃ u : (lbPow L n).Sec, resG X h (powFn u J) = r

namespace IsLocalFn

variable {J : PUnit → L.ι} {V : X.Opens} {h : V ≤ powChart L J} {m n : ℕ} {r r' : Γ(X, V)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨secOfFn L 1, by rw [powFn_secOfFn, map_one, map_one]⟩`.
-/
theorem one : IsLocalFn h 0 1 :=
  ⟨secOfFn L 1, by rw [powFn_secOfFn, map_one, map_one]⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `a`. Take `⟨v, rfl⟩` from `b`. Conclude with `⟨secMul u v, by rw [powFn_secMul, map_mul]⟩`.
-/
theorem mul (a : IsLocalFn h m r) (b : IsLocalFn h n r') : IsLocalFn h (m + n) (r * r') := by
  obtain ⟨u, rfl⟩ := a
  obtain ⟨v, rfl⟩ := b
  exact ⟨secMul u v, by rw [powFn_secMul, map_mul]⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `a`. Conclude with `⟨secPow u n, by rw [powFn_secPow, map_pow]⟩`.
-/
theorem pow (a : IsLocalFn h m r) (n : ℕ) : IsLocalFn h (m * n) (r ^ n) := by
  obtain ⟨u, rfl⟩ := a
  exact ⟨secPow u n, by rw [powFn_secPow, map_pow]⟩

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using one`. Consider the case `insert i T hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.card_insert_of_notMem hi, mul_add, mul_one, add_comm]`. Conclude with `(a i).mul ih`.
-/
theorem prod {ι : Type} (T : Finset ι) {f : ι → Γ(X, V)} (a : ∀ i, IsLocalFn h m (f i)) :
    IsLocalFn h (m * T.card) (∏ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using one
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, mul_add, mul_one, add_comm]
    exact (a i).mul ih

/- English proof (translation)
Establish `h₁ : ∀ i, IsLocalFn h (m * n) (σ ^ n * y i ^ (α i : ℕ))` using `fun i => by`. Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (α i).2)`. Use `((hy i).pow (α i)).mul (hσ.pow c)` as an intermediate fact. Rewrite `this` using `[← mul_add, ← hc]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Generalize the expression as in `(α i : ℕ) = a at hc ⊢`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `h₂` using `(prod Finset.univ h₁).mul (hσ.pow n)`. Rewrite `h₂` using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Apply the tactic sequence `convert h₂ using 1 <;> ring`.
-/
theorem monomial {e : ℕ} {σ : Γ(X, V)} {y : Fin e → Γ(X, V)} (hσ : IsLocalFn h m σ)
    (hy : ∀ i, IsLocalFn h m (σ * y i)) (α : Fin e → Fin (n + 1)) :
    IsLocalFn h (m * (e + 1) * n) (σ ^ (n * (e + 1)) * ∏ i, y i ^ (α i : ℕ)) := by
  have h₁ : ∀ i, IsLocalFn h (m * n) (σ ^ n * y i ^ (α i : ℕ)) := fun i => by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (α i).2)
    have := ((hy i).pow (α i)).mul (hσ.pow c)
    rw [← mul_add, ← hc] at this
    convert this using 1
    generalize (α i : ℕ) = a at hc ⊢
    rw [hc]
    ring
  have h₂ := (prod Finset.univ h₁).mul (hσ.pow n)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
  convert h₂ using 1 <;> ring

/- English proof (translation)
Use `choose u hu using a`. Set `E` to `cohZeroTwistEquiv (lbPow L n)`. Set `φ : coh (twist (structureModule X) (lbPow L n)) 0 →ₗ[k] Γ(X, V)` to `{ toFun := fun w => resG X h (powFn (E w) J) map_add' := fun w w' => by`. Rewrite using `[map_add E]`. Conclude with `map_add (resG X h) (powFn (E w) J) (powFn (E w') J)`.

Use the proof step `map_smul' := fun c w => by`. Rewrite using `[← algebraMap_smul Γ(X, ⊤) c w, map_smul, RingHom.id_apply, Algebra.smul_def, hk]`. Use `(map_mul (resG X h) (resG X le_top (algebraMap k Γ(X, ⊤) c)) (powFn (E w) J)).trans ?_` and prove the remaining obligations. Rewrite using `[LB.resG_resG] }`. Establish `: LinearIndependent k fun i => E.symm (u i)`.

Use `LinearIndependent.of_comp φ ?_` and prove the remaining obligations. Use `hf using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `resG X h (powFn (E (E.symm (u i))) J) = _`. Rewrite using `[E.apply_symm_apply, hu]`.

Conclude with `this.fintype_card_le_finrank`.
-/
theorem card_le_globalSectionsDim_of_localFnOfPowerSection {k : Type} [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(X, V)]
    (hk : ∀ c, algebraMap k Γ(X, V) c = resG X le_top (algebraMap k Γ(X, ⊤) c))
    (hfin : Module.Finite k (coh (twist (structureModule X) (lbPow L n)) 0))
    {ι : Type} [Fintype ι] {f : ι → Γ(X, V)} (hf : LinearIndependent k f)
    (a : ∀ i, IsLocalFn h n (f i)) : Fintype.card ι ≤ lbH0 k (lbPow L n) := by
  choose u hu using a
  let E := cohZeroTwistEquiv (lbPow L n)
  let φ : coh (twist (structureModule X) (lbPow L n)) 0 →ₗ[k] Γ(X, V) :=
    { toFun := fun w => resG X h (powFn (E w) J)
      map_add' := fun w w' => by
        rw [map_add E]
        exact map_add (resG X h) (powFn (E w) J) (powFn (E w') J)
      map_smul' := fun c w => by
        rw [← algebraMap_smul Γ(X, ⊤) c w, map_smul, RingHom.id_apply, Algebra.smul_def, hk]
        refine (map_mul (resG X h) (resG X le_top (algebraMap k Γ(X, ⊤) c)) (powFn (E w) J)).trans ?_
        rw [LB.resG_resG] }
  have : LinearIndependent k fun i => E.symm (u i) := by
    refine LinearIndependent.of_comp φ ?_
    convert hf using 1
    funext i
    change resG X h (powFn (E (E.symm (u i))) J) = _
    rw [E.apply_symm_apply, hu]
  exact this.fintype_card_le_finrank

end IsLocalFn

/- English proof (translation)
Use `choose N hN using fun i => exists_sec_eq_pow_mul (m := 0) hL s (fun J => resG X inf_le_left (y i)) (LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun z J J' hs hJ hJ' => by`. Rewrite using `[gm_lbPow_g 0 (𝟙 X) z J J' hJ hJ', pow_zero, Units.val_one, one_mul]`. Conclude with `(gs_res (𝟙 X) z inf_le_left ⟨hs, hJ⟩ (y i)).trans (gs_res (𝟙 X) z inf_le_left ⟨hs, hJ'⟩ (y i)).symm)`. Use `⟨Finset.univ.sup N + 1, Nat.le_add_left _ _, fun i => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hN i (Finset.univ.sup N + 1) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))`.

Conclude with `⟨secCast (zero_add _) u, hu J⟩`.
-/
theorem exists_isLocalFn_mul [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {q : ℕ}
    (s : (lbPow L q).Sec) (J : PUnit → L.ι) {e : ℕ} (y : Fin e → Γ(X, nonzeroLocus s)) :
    ∃ a, 1 ≤ a ∧ ∀ i, IsLocalFn (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ powChart L J)
      (q * a) (resG X inf_le_right (powFn s J) ^ a * resG X inf_le_left (y i)) := by
  choose N hN using fun i => exists_sec_eq_pow_mul (m := 0) hL s
    (fun J => resG X inf_le_left (y i))
    (LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun z J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) z J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 X) z inf_le_left ⟨hs, hJ⟩ (y i)).trans
        (gs_res (𝟙 X) z inf_le_left ⟨hs, hJ'⟩ (y i)).symm)
  refine ⟨Finset.univ.sup N + 1, Nat.le_add_left _ _, fun i => ?_⟩
  obtain ⟨u, hu⟩ := hN i (Finset.univ.sup N + 1)
    ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
  exact ⟨secCast (zero_add _) u, hu J⟩

variable {k : Type} [Field k] [Algebra k Γ(X, ⊤)]

variable (k) in

abbrev algebraOpen (U : X.Opens) : Algebra k Γ(X, U) :=
  ((resG X le_top).comp (algebraMap k Γ(X, ⊤))).toAlgebra

/- English proof (translation)
Take `⟨J, hJ⟩ : ∃ J, x ∈ powChart L J` from `exists_chart_of_mem_nonzeroLocus hx`. Take `⟨a, ha, hya⟩` from `exists_isLocalFn_mul hL s J y`. Establish `hxV : x ∈ nonzeroLocus s ⊓ powChart L J` using `⟨hx, hJ⟩`. Establish `: Nonempty ((nonzeroLocus s ⊓ powChart L J : X.Opens))` using `⟨⟨x, hxV⟩⟩`. Use `letI := algebraOpen k (nonzeroLocus s)`.

Use `letI := algebraOpen k (nonzeroLocus s ⊓ powChart L J)`. Set `ρ : Γ(X, nonzeroLocus s) →ₐ[k] Γ(X, nonzeroLocus s ⊓ powChart L J)` to `{ resG X inf_le_left with commutes' := fun c => LB.resG_resG _ _ _ }`. Establish `hy' : AlgebraicIndependent k fun i => resG X (inf_le_left : nonzeroLocus s ⊓ powChart L J ≤ _) (y i)` using `hy.map' (f := ρ) (map_injective_of_isIntegral X (homOfLE inf_le_left))`. Establish `hσ : resG X (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ _) (powFn s J) ≠ 0`. Introduce `h0`.

Establish `hu` using `(mem_nonzeroLocus_iff_powFn s hJ).1 hx`. Rewrite `hu` using `[← gs_res (𝟙 X) x inf_le_right hxV, h0, LBGerm.gs_zero _ _ _ hxV]`. Conclude with `not_isUnit_zero hu`. Establish `hs : IsLocalFn (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ _) q _` using `⟨s, rfl⟩`. Use `⟨q * a * (e + 1), Nat.mul_pos (Nat.mul_pos hq ha) e.succ_pos, fun n => ?_⟩` and prove the remaining obligations.

Use `IsLocalFn.card_le_globalSectionsDim_of_localFnOfPowerSection (fun _ => rfl) (hfin _) (linearIndependent_monomials hy' (pow_ne_zero (n * (e + 1)) (pow_ne_zero a hσ)) n) (IsLocalFn.monomial (hs.pow a) hya)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_pow_le_globalSectionsDim_lineBundlePow [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB)
    (hfin : ∀ n, Module.Finite k (coh (twist (structureModule X) (lbPow L n)) 0))
    {q : ℕ} (hq : 1 ≤ q) (s : (lbPow L q).Sec) {x : X} (hx : x ∈ nonzeroLocus s) {e : ℕ}
    {y : Fin e → Γ(X, nonzeroLocus s)}
    (hy : letI := algebraOpen k (nonzeroLocus s); AlgebraicIndependent k y) :
    ∃ M, 1 ≤ M ∧ ∀ n, (n + 1) ^ e ≤ lbH0 k (lbPow L (M * n)) := by
  obtain ⟨J, hJ⟩ : ∃ J, x ∈ powChart L J := exists_chart_of_mem_nonzeroLocus hx
  obtain ⟨a, ha, hya⟩ := exists_isLocalFn_mul hL s J y
  have hxV : x ∈ nonzeroLocus s ⊓ powChart L J := ⟨hx, hJ⟩
  have : Nonempty ((nonzeroLocus s ⊓ powChart L J : X.Opens)) := ⟨⟨x, hxV⟩⟩
  letI := algebraOpen k (nonzeroLocus s)
  letI := algebraOpen k (nonzeroLocus s ⊓ powChart L J)
  let ρ : Γ(X, nonzeroLocus s) →ₐ[k] Γ(X, nonzeroLocus s ⊓ powChart L J) :=
    { resG X inf_le_left with commutes' := fun c => LB.resG_resG _ _ _ }
  have hy' : AlgebraicIndependent k fun i => resG X
      (inf_le_left : nonzeroLocus s ⊓ powChart L J ≤ _) (y i) :=
    hy.map' (f := ρ) (map_injective_of_isIntegral X (homOfLE inf_le_left))
  have hσ : resG X (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ _) (powFn s J) ≠ 0 := by
    intro h0
    have hu := (mem_nonzeroLocus_iff_powFn s hJ).1 hx
    rw [← gs_res (𝟙 X) x inf_le_right hxV, h0, LBGerm.gs_zero _ _ _ hxV] at hu
    exact not_isUnit_zero hu
  have hs : IsLocalFn (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ _) q _ := ⟨s, rfl⟩
  refine ⟨q * a * (e + 1), Nat.mul_pos (Nat.mul_pos hq ha) e.succ_pos, fun n => ?_⟩
  have := IsLocalFn.card_le_globalSectionsDim_of_localFnOfPowerSection (fun _ => rfl) (hfin _)
    (linearIndependent_monomials hy' (pow_ne_zero (n * (e + 1)) (pow_ne_zero a hσ)) n)
    (IsLocalFn.monomial (hs.pow a) hya)
  simpa using this

/- English proof (translation)
Establish `h` using `((strHom k X).finiteType_appLE (isAffineOpen_top _) hU le_top).comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)`. Establish `e : (resG X (le_top : U ≤ ⊤)).comp (algebraMap k Γ(X, ⊤)) = ((strHom k X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom` using `RingHom.ext fun c => by`. Rewrite using `[RingHom.comp_apply, algebraMap_eq_strHom k X c]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `RingHom.FiniteType _`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem finiteType_algebraOpen [LocallyOfFiniteType (strHom k X)] {U : X.Opens}
    (hU : IsAffineOpen U) : letI := algebraOpen k U; Algebra.FiniteType k Γ(X, U) := by
  have h := ((strHom k X).finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have e : (resG X (le_top : U ≤ ⊤)).comp (algebraMap k Γ(X, ⊤)) =
      ((strHom k X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, algebraMap_eq_strHom k X c]
      rfl
  change RingHom.FiniteType _
  rw [e]
  exact h

/- English proof (translation)
The claim follows from `(topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))`.
-/
theorem topologicalKrullDim_affineOpen {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) :=
  (topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
    hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))

end AmpleBig

open AmpleBig in

/- English proof (translation)
Introduce `k _ X _ _ hp A hA`. Use `hA.compactSpace` as an intermediate fact. Use `hA.quasiSeparatedSpace` as an intermediate fact. Establish `: IsProper (strHom k X)`. Take `⟨N, i, hi, e⟩` from `hp`.

Use `isProper_str k N` as an intermediate fact. Rewrite using `[← e]`. Use `infer_instance`. Establish `hfin` using `fun n => finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom k X) hp (isLB_lbPow hA.isLB n)`. Take `⟨q, hq, N, s, hs, ha⟩` from `hA.exists_cover`.

Establish `hc : ∀ x : X, ∃ i, x ∈ nonzeroLocus (s i)` using `fun x => Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))`. Establish `key : ∀ i : {i // ∃ x, x ∈ nonzeroLocus (s i)}, ∃ e : ℕ, topologicalKrullDim (nonzeroLocus (s i) : Set X) ≤ e ∧ ∃ M, 1 ≤ M ∧ ∀ n, (n + 1) ^ e ≤ lbH0 k (lbPow A (M * n))`. Introduce and unpack `⟨i, x, hx⟩`. Use `letI := algebraOpen k (nonzeroLocus (s i))`. Use `finiteType_algebraOpen (k := k) (ha i)` as an intermediate fact.

Establish `: Nonempty (nonzeroLocus (s i))` using `⟨⟨x, hx⟩⟩`. Take `⟨e, y, hy, hd⟩` from `exists_algebraicIndependent k Γ(X, nonzeroLocus (s i))`. Conclude with `⟨e, (topologicalKrullDim_affineOpen (ha i)).trans_le hd, exists_pow_le_globalSectionsDim_lineBundlePow hA.isLB hfin hq (s i) hx hy⟩`. Use `choose e he hM using key`. Establish `: Nonempty {i // ∃ x, x ∈ nonzeroLocus (s i)}`.

Establish `⟨i, hi⟩` using `hc (genericPoint X)`. Use the proof step `⟨⟨i, _, hi⟩⟩`. Take `⟨i₀, hi₀⟩` from `Finite.exists_max e`. Establish `hd : topologicalKrullDim X ≤ e i₀` using `topologicalKrullDim_le_of_forall_exists_isOpen fun x =>`. Establish `⟨i, hi⟩` using `hc x`.

Use the proof step `⟨_, (nonzeroLocus (s i)).isOpen, hi, (he ⟨i, x, hi⟩).trans (by exact_mod_cast hi₀ _)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨D, hD, hDe⟩ : ∃ D : ℕ, topologicalKrullDim X = D ∧ D ≤ e i₀ := by`. Establish `h0 : 0 ≤ topologicalKrullDim X`. Establish `: Nonempty (IrreducibleCloseds X)` using `⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩`. Conclude with `Order.krullDim_nonneg`.

Generalize the expression as in `topologicalKrullDim X = d at hd h0`. Use `lift d to ℕ∞ using (fun h => by simp [h] at h0)`. Establish `hd' : d ≤ e i₀` using `by exact_mod_cast hd`. Use `lift d to ℕ using ne_top_of_le_ne_top (ENat.coe_ne_top _) hd'`. Conclude with `⟨d, rfl, by exact_mod_cast hd'⟩`.

Take `⟨M, hM1, hM⟩` from `hM i₀`. Establish `hM' : (0 : ℝ) < M` using `Nat.cast_pos.2 hM1`. Use `⟨hA.isLB, hfin, D, hD, 1 / (M : ℝ) ^ D, by positivity, ?_⟩` and prove the remaining obligations. Establish `ht : Tendsto (fun n : ℕ => M * n) atTop atTop` using `tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hM1) tendsto_id`. Use `ht.frequently (Frequently.of_forall fun n => ?_)` and prove the remaining obligations.

Establish `h₁ : n ^ D ≤ lbH0 k (lbPow A (M * n))` using `((Nat.pow_le_pow_left (Nat.le_succ n) D).trans (Nat.pow_le_pow_right (Nat.succ_pos n) hDe)).trans (hM n)`. Use `le_of_eq_of_le ?_ (Nat.cast_le.2 h₁)` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_pow, Nat.cast_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem IsAmpleLB.isBig : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ A : LB X, IsAmpleLB A → IsBig k A := by
  intro k _ X _ _ hp A hA
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  have : IsProper (strHom k X) := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hfin := fun n => finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom k X) hp
    (isLB_lbPow hA.isLB n)
  obtain ⟨q, hq, N, s, hs, ha⟩ := hA.exists_cover
  have hc : ∀ x : X, ∃ i, x ∈ nonzeroLocus (s i) := fun x =>
    Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
  have key : ∀ i : {i // ∃ x, x ∈ nonzeroLocus (s i)}, ∃ e : ℕ,
      topologicalKrullDim (nonzeroLocus (s i) : Set X) ≤ e ∧
      ∃ M, 1 ≤ M ∧ ∀ n, (n + 1) ^ e ≤ lbH0 k (lbPow A (M * n)) := by
    rintro ⟨i, x, hx⟩
    letI := algebraOpen k (nonzeroLocus (s i))
    have := finiteType_algebraOpen (k := k) (ha i)
    have : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hx⟩⟩
    obtain ⟨e, y, hy, hd⟩ := exists_algebraicIndependent k Γ(X, nonzeroLocus (s i))
    exact ⟨e, (topologicalKrullDim_affineOpen (ha i)).trans_le hd,
      exists_pow_le_globalSectionsDim_lineBundlePow hA.isLB hfin hq (s i) hx hy⟩
  choose e he hM using key
  have : Nonempty {i // ∃ x, x ∈ nonzeroLocus (s i)} :=
    have ⟨i, hi⟩ := hc (genericPoint X)
    ⟨⟨i, _, hi⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max e
  have hd : topologicalKrullDim X ≤ e i₀ :=
    topologicalKrullDim_le_of_forall_exists_isOpen fun x =>
      have ⟨i, hi⟩ := hc x
      ⟨_, (nonzeroLocus (s i)).isOpen, hi, (he ⟨i, x, hi⟩).trans (by exact_mod_cast hi₀ _)⟩
  obtain ⟨D, hD, hDe⟩ : ∃ D : ℕ, topologicalKrullDim X = D ∧ D ≤ e i₀ := by
    have h0 : 0 ≤ topologicalKrullDim X := by
      have : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg
    generalize topologicalKrullDim X = d at hd h0
    lift d to ℕ∞ using (fun h => by simp [h] at h0)
    have hd' : d ≤ e i₀ := by exact_mod_cast hd
    lift d to ℕ using ne_top_of_le_ne_top (ENat.coe_ne_top _) hd'
    exact ⟨d, rfl, by exact_mod_cast hd'⟩
  obtain ⟨M, hM1, hM⟩ := hM i₀
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM1
  refine ⟨hA.isLB, hfin, D, hD, 1 / (M : ℝ) ^ D, by positivity, ?_⟩
  have ht : Tendsto (fun n : ℕ => M * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hM1) tendsto_id
  refine ht.frequently (Frequently.of_forall fun n => ?_)
  have h₁ : n ^ D ≤ lbH0 k (lbPow A (M * n)) :=
    ((Nat.pow_le_pow_left (Nat.le_succ n) D).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) hDe)).trans (hM n)
  refine le_of_eq_of_le ?_ (Nat.cast_le.2 h₁)
  rw [Nat.cast_mul, mul_pow, Nat.cast_pow]
  field_simp

end GlobalTheory
