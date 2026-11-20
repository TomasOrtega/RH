import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedCharStatement

open IsLocalRing

namespace GlobalTheory

namespace CompleteJoin

variable {C : Type} [NormedField C] [IsUltrametricDist C]

omit [IsUltrametricDist C] in

/- English proof (translation)
Introduce and unpack `⟨u, rfl⟩`. Establish `h1 : ‖f u‖ * ‖f (↑u⁻¹ : R)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]`. Use `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha (hf (↑u⁻¹ : R))` as an intermediate fact. Conclude with `this.ne h1`.
-/
theorem not_isUnit_of_norm_lt_one {R : Type*} [CommRing R] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1)
    {a : R} (ha : ‖f a‖ < 1) : ¬ IsUnit a := by
  rintro ⟨u, rfl⟩
  have h1 : ‖f u‖ * ‖f (↑u⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha (hf (↑u⁻¹ : R))
  exact this.ne h1

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `key : ∀ k : ℕ, ‖a x - b x‖ ≤ ‖(p : C)‖ ^ k` using `fun k => by`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)`. Establish `hx : x = y * (p : ℤ_[p]) ^ k + (x.appr k : ℤ_[p])` using `by rw [hy]; ring`. Establish `: a x - b x = (a y - b y) * (p : C) ^ k` using `by conv_lhs => rw [hx]`.

Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_mul, norm_pow]`. Use `mul_le_of_le_one_left (by positivity) ?_` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y) (by simpa using hb y))`. Use `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key` as an intermediate fact. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 this)`.
-/
theorem padicInt_ringHom_ext {p : ℕ} [Fact p.Prime] (hp : ‖(p : C)‖ < 1) (a b : ℤ_[p] →+* C)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1) : a = b := by
  refine RingHom.ext fun x => ?_
  have key : ∀ k : ℕ, ‖a x - b x‖ ≤ ‖(p : C)‖ ^ k := fun k => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = y * (p : ℤ_[p]) ^ k + (x.appr k : ℤ_[p]) := by rw [hy]; ring
    have : a x - b x = (a y - b y) * (p : C) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y) (by simpa using hb y))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite R S := hφ`. Use `haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S`. Establish `hle : ∀ z : S, ‖(z : C)‖ ≤ 1` using `fun z => by`. Set `v` to `NormedField.valuation (K := C)`.

Set `ψ : R →+* v.integer` to `(S.subtype.comp φ).codRestrict _ fun a => h1 a`. Establish `hz : IsIntegral R z` using `Algebra.IsIntegral.isIntegral z`. Establish `hz' : IsIntegral v.integer (z : C)` using `hz.map_of_comp_eq ψ S.subtype rfl`. Conclude with `(Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hz'`. Use `⟨inferInstance, IsNoetherianRing.of_finite R S, CompleteFiniteExtension.isAdicComplete_of_finite_local R S, hle, fun z => ⟨fun hz => ?_, fun hz => not_isUnit_of_norm_lt_one S.subtype hle hz⟩⟩` and prove the remaining obligations.

Set `P : Ideal S` to `{ carrier := {z | ‖(z : C)‖ < 1} add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt (max_lt ha hb) zero_mem' := by simp smul_mem' := fun c x hx => by`. Express the relevant statement in the definitionally equal form `‖(c : C) * x‖ < 1`. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }`. Establish `hP : ∀ z : S, z ∈ P ↔ ‖(z : C)‖ < 1` using `fun _ => Iff.rfl`.

Establish `hP1 : P ≠ ⊤`. Rewrite using `[Ideal.ne_top_iff_one, hP]`. Simplify using the standard rewrite rules. Use `haveI : P.IsPrime := ⟨hP1, fun {x y} hxy => by`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_or, hP, hP, not_lt, not_lt]`. Rewrite `hxy` using `[hP, Subring.coe_mul, norm_mul]`. Conclude with `hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)⟩`. Establish `hc : maximalIdeal R = P.comap (algebraMap R S)` using `(maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP1) fun a ha => h2 a ha`. Establish `hm : P.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (hc ▸ maximalIdeal.isMaximal R)`.

Rewrite `hz` using `[← eq_maximalIdeal hm]`. Conclude with `hz`.
-/
theorem subring_of_finite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Subring C) (φ : R →+* S) (hφ : φ.Finite)
    (h1 : ∀ a, ‖(φ a : C)‖ ≤ 1) (h2 : ∀ a ∈ maximalIdeal R, ‖(φ a : C)‖ < 1) :
    ∃ _ : IsLocalRing S, IsNoetherianRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  letI := φ.toAlgebra
  haveI : Module.Finite R S := hφ
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  have hle : ∀ z : S, ‖(z : C)‖ ≤ 1 := fun z => by
    let v := NormedField.valuation (K := C)
    let ψ : R →+* v.integer := (S.subtype.comp φ).codRestrict _ fun a => h1 a
    have hz : IsIntegral R z := Algebra.IsIntegral.isIntegral z
    have hz' : IsIntegral v.integer (z : C) := hz.map_of_comp_eq ψ S.subtype rfl
    exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hz'
  refine ⟨inferInstance, IsNoetherianRing.of_finite R S,
    CompleteFiniteExtension.isAdicComplete_of_finite_local R S, hle, fun z => ⟨fun hz => ?_,
      fun hz => not_isUnit_of_norm_lt_one S.subtype hle hz⟩⟩
  let P : Ideal S :=
    { carrier := {z | ‖(z : C)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖(c : C) * x‖ < 1
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hP : ∀ z : S, z ∈ P ↔ ‖(z : C)‖ < 1 := fun _ => Iff.rfl
  have hP1 : P ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hP]
    simp
  haveI : P.IsPrime := ⟨hP1, fun {x y} hxy => by
    by_contra h
    rw [not_or, hP, hP, not_lt, not_lt] at h
    rw [hP, Subring.coe_mul, norm_mul] at hxy
    exact hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)⟩
  have hc : maximalIdeal R = P.comap (algebraMap R S) :=
    (maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP1) fun a ha => h2 a ha
  have hm : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (hc ▸ maximalIdeal.isMaximal R)
  rw [← eq_maximalIdeal hm] at hz
  exact hz

omit [IsUltrametricDist C] in

/- English proof (translation)
Use `letI := f.toAlgebra`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ_[p]) (M := V)`. Establish `hint : ∀ x : V, IsIntegral R (g x)` using `fun x => (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x).map_of_comp_eq φ g h`. Establish `hfin : Module.Finite R (Algebra.adjoin R (g '' s))` using `Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g) (by rintro _ ⟨x, -, rfl⟩; exact hint x)`. Use `⟨(Algebra.adjoin R (g '' s)).toSubring, algebraMap R (Algebra.adjoin R (g '' s)), (RingHom.finite_algebraMap (B := Algebra.adjoin R (g '' s))).2 hfin, fun _ => rfl, fun a => ?_⟩` and prove the remaining obligations.

Establish `ha : a ∈ Submodule.span ℤ_[p] (s : Set V)` using `hs ▸ Submodule.mem_top`. Express the relevant statement in the definitionally equal form `g a ∈ Algebra.adjoin R (g '' s)`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[Algebra.smul_def, map_mul]`.

Use `mul_mem ?_ hx` and prove the remaining obligations. Establish `: g (algebraMap ℤ_[p] V c) = algebraMap R C (φ c)` using `(RingHom.congr_fun h c).symm`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`.
-/
theorem exists_subring_finite {R V : Type} [CommRing R] [CommRing V] {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] V] [Module.Finite ℤ_[p] V] (f : R →+* C) (g : V →+* C) (φ : ℤ_[p] →+* R)
    (h : f.comp φ = g.comp (algebraMap ℤ_[p] V)) :
    ∃ (S : Subring C) (ψ : R →+* S), ψ.Finite ∧ (∀ a, (ψ a : C) = f a) ∧ ∀ a, g a ∈ S := by
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := V)
  have hint : ∀ x : V, IsIntegral R (g x) := fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x).map_of_comp_eq φ g h
  have hfin : Module.Finite R (Algebra.adjoin R (g '' s)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g)
      (by rintro _ ⟨x, -, rfl⟩; exact hint x)
  refine ⟨(Algebra.adjoin R (g '' s)).toSubring, algebraMap R (Algebra.adjoin R (g '' s)),
    (RingHom.finite_algebraMap (B := Algebra.adjoin R (g '' s))).2 hfin, fun _ => rfl, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ_[p] (s : Set V) := hs ▸ Submodule.mem_top
  change g a ∈ Algebra.adjoin R (g '' s)
  induction ha using Submodule.span_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : g (algebraMap ℤ_[p] V c) = algebraMap R C (φ c) := (RingHom.congr_fun h c).symm
    rw [this]
    exact Subalgebra.algebraMap_mem _ _

omit [IsUltrametricDist C] in

/- English proof (translation)
Set `j : FractionRing S →ₐ[S] C` to `IsFractionRing.liftAlgHom (g := Algebra.ofId S C) Subtype.val_injective`. Set `e` to `(integralClosure S (FractionRing S)).equivMapOfInjective j j.injective`. Use `haveI : IsFractionRing (integralClosure S (FractionRing S)) (FractionRing S) := integralClosure.isFractionRing_of_finite_extension (FractionRing S) (FractionRing S)`. Use `haveI : IsIntegrallyClosed (integralClosure S (FractionRing S)) := (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).2 inferInstance`. Conclude with `⟨((integralClosure S (FractionRing S)).map j).toSubring, algebraMap S ((integralClosure S (FractionRing S)).map j), (RingHom.finite_algebraMap (B := (integralClosure S (FractionRing S)).map j)).2 (Module.Finite.equiv e.toLinearEquiv), fun _ => rfl, IsIntegrallyClosed.of_equiv e.t …`.
-/
theorem exists_normal_subring (S : Subring C)
    (h : Module.Finite S (integralClosure S (FractionRing S))) :
    ∃ (S' : Subring C) (ψ : S →+* S'), ψ.Finite ∧ (∀ a, (ψ a : C) = a) ∧ IsIntegrallyClosed S' := by
  let j : FractionRing S →ₐ[S] C :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId S C) Subtype.val_injective
  let e := (integralClosure S (FractionRing S)).equivMapOfInjective j j.injective
  haveI : IsFractionRing (integralClosure S (FractionRing S)) (FractionRing S) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing S) (FractionRing S)
  haveI : IsIntegrallyClosed (integralClosure S (FractionRing S)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).2 inferInstance
  exact ⟨((integralClosure S (FractionRing S)).map j).toSubring,
    algebraMap S ((integralClosure S (FractionRing S)).map j),
    (RingHom.finite_algebraMap (B := (integralClosure S (FractionRing S)).map j)).2
      (Module.Finite.equiv e.toLinearEquiv), fun _ => rfl,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end CompleteJoin

open CompleteJoin in

/- English proof (translation)
Introduce `R _ _ _ _ T C _ _ _ _ f g _ _ _ hT hN hR hf1 hf2 hg1 hg2`. Use `haveI : Finite (ResidueField T.V) := hT`. Take `⟨q, hq, _, hfin⟩` from `exists_padicInt_algebra_finite T.V`. Establish `hqV : (q : T.V) ∈ maximalIdeal T.V`. Use `ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[q]) T.V _ (maximalIdeal.isMaximal _) (Ideal.mem_map_of_mem _ (show (q : ℤ_[q]) ∈ maximalIdeal _ from PadicInt.irreducible_p.not_isUnit))` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hqC : ‖(q : C)‖ < 1` using `by simpa using hg2 _ hqV`. Establish `hqR : (q : R) ∈ maximalIdeal R` using `not_isUnit_of_norm_lt_one f hf1 (by simpa using hqC)`. Take `⟨φ⟩` from `nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal R) q hqR`. Take `⟨S₀, ψ₀, hψ₀, h₀, hg₀⟩` from `exists_subring_finite f g φ (padicInt_ringHom_ext hqC _ _ (fun x => hf1 _) fun x => hg1 _)`.

Take `⟨_, hN₀, hc₀, -, hm₀⟩` from `subring_of_finite S₀ ψ₀ hψ₀ (fun a => h₀ a ▸ hf1 a) fun a ha => h₀ a ▸ hf2 a ha`. Take `⟨S, ψ, hψ, h, hS⟩` from `exists_normal_subring S₀ (GlobalTheory.T.integralClosure_finite_local_complete_mixedChar S₀ q hq.out ((hm₀ _).2 (by simpa using hqC)) hN₀ hc₀).1`. Establish `h' : ∀ a, ((ψ.comp ψ₀ a : S) : C) = f a` using `fun a => (h _).trans (h₀ a)`. Take `⟨_, hN₁, hc₁, hle, hm₁⟩` from `subring_of_finite S (ψ.comp ψ₀) (hψ.comp hψ₀) (fun a => h' a ▸ hf1 a) fun a ha => h' a ▸ hf2 a ha`. Conclude with `⟨S, inferInstance, hN₁, hS, hc₁, fun a => h' a ▸ (ψ.comp ψ₀ a).2, fun a => (show ((ψ ⟨g a, hg₀ a⟩ : S) : C) = g a from h _) ▸ (ψ ⟨g a, hg₀ a⟩).2, hle, hm₁⟩`.
-/
theorem exists_complete_normal_subring_join : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (T : Formalism.L2.Pj.CDVR) (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (f : R →+* C) (g : T.V →+* C) (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → T.FinRes → IsNoetherianRing R → IsAdicComplete (maximalIdeal R) R → (∀ a, ‖f a‖ ≤ 1) → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖g a‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖g a‖ < 1) → ∃ (S : Subring C) (_ : IsLocalRing S), IsNoetherianRing S ∧ IsIntegrallyClosed S ∧ IsAdicComplete (maximalIdeal S) S ∧ (∀ a, f a ∈ S) ∧ (∀ a, g a ∈ S) ∧ (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  intro R _ _ _ _ T C _ _ _ _ f g _ _ _ hT hN hR hf1 hf2 hg1 hg2
  haveI : Finite (ResidueField T.V) := hT
  obtain ⟨q, hq, _, hfin⟩ := exists_padicInt_algebra_finite T.V
  have hqV : (q : T.V) ∈ maximalIdeal T.V := by
    have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[q]) T.V _ (maximalIdeal.isMaximal _)
      (Ideal.mem_map_of_mem _ (show (q : ℤ_[q]) ∈ maximalIdeal _ from
        PadicInt.irreducible_p.not_isUnit))
    rwa [map_natCast] at this
  have hqC : ‖(q : C)‖ < 1 := by simpa using hg2 _ hqV
  have hqR : (q : R) ∈ maximalIdeal R := not_isUnit_of_norm_lt_one f hf1 (by simpa using hqC)
  obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal R) q hqR
  obtain ⟨S₀, ψ₀, hψ₀, h₀, hg₀⟩ := exists_subring_finite f g φ
    (padicInt_ringHom_ext hqC _ _ (fun x => hf1 _) fun x => hg1 _)
  obtain ⟨_, hN₀, hc₀, -, hm₀⟩ := subring_of_finite S₀ ψ₀ hψ₀ (fun a => h₀ a ▸ hf1 a)
    fun a ha => h₀ a ▸ hf2 a ha
  obtain ⟨S, ψ, hψ, h, hS⟩ := exists_normal_subring S₀
    (GlobalTheory.T.integralClosure_finite_local_complete_mixedChar S₀ q hq.out ((hm₀ _).2 (by simpa using hqC)) hN₀ hc₀).1
  have h' : ∀ a, ((ψ.comp ψ₀ a : S) : C) = f a := fun a => (h _).trans (h₀ a)
  obtain ⟨_, hN₁, hc₁, hle, hm₁⟩ := subring_of_finite S (ψ.comp ψ₀) (hψ.comp hψ₀)
    (fun a => h' a ▸ hf1 a) fun a ha => h' a ▸ hf2 a ha
  exact ⟨S, inferInstance, hN₁, hS, hc₁, fun a => h' a ▸ (ψ.comp ψ₀ a).2,
    fun a => (show ((ψ ⟨g a, hg₀ a⟩ : S) : C) = g a from h _) ▸ (ψ ⟨g a, hg₀ a⟩).2, hle, hm₁⟩

end GlobalTheory
