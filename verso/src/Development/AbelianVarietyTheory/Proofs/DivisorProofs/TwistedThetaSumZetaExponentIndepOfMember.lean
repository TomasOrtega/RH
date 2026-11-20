import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistIndep

/- English proof (translation)
Establish `hη : (ζ ^ d) ^ M = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0`. Establish `h` using `mul_geom_sum (ζ ^ d) M`. Rewrite `h` using `[hη, sub_self]`. Conclude with `(mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hd)`.

Establish `hdiv : (1 - ζ ^ d) ∣ (M : o)`. Establish `h : (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k)`. Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Conclude with `Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k`. Conclude with `isUnit_of_dvd_unit hdiv hM`.
-/
theorem isUnit_one_sub_pow {o : Type} [CommRing o] [IsDomain o] {ζ : o} {M : ℕ} (hζ : IsPrimitiveRoot ζ M)
    (hM : IsUnit (M : o)) {d : ℕ} (hd : ζ ^ d ≠ 1) : IsUnit (1 - ζ ^ d) := by
  have hη : (ζ ^ d) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0 := by
    have h := mul_geom_sum (ζ ^ d) M
    rw [hη, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hd)
  have hdiv : (1 - ζ ^ d) ∣ (M : o) := by
    have h : (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [h]
    exact Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k
  exact isUnit_of_dvd_unit hdiv hM

/- English proof (translation)
Rewrite `h`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => h (hu.map ev)`.
-/
theorem mem_maximalIdeal_of_map {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ev : R →+* V) {x : R} (h : ev x ∈ maximalIdeal V) : x ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h (hu.map ev)

/- English proof (translation)
Take `⟨s, hs⟩` from `(X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩`. Conclude with `⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩`.
-/
theorem stalk_of_base (X₁ : GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

/- English proof (translation)
Take `⟨y, hy⟩` from `hx.exists_right_inv`. Take `⟨t, ht⟩` from `stalk_of_base X₁ z₁ y`. Use `IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hs, ht, ← map_mul, hy, map_one, map_one]`.
-/
theorem stalk_isUnit (X₁ : GSet) (z₁ : X₁.M.Z) {s : X₁.M.Z.presheaf.stalk z₁} {x : X₁.o₁}
    (hs : X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ x) (hx : IsUnit x) : IsUnit s := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨t, ht⟩ := stalk_of_base X₁ z₁ y
  refine IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ ?_)
  rw [map_mul, hs, ht, ← map_mul, hy, map_one, map_one]

/- English proof (translation)
Use `haveI : IsDomain X₁.o₁ := by haveI := X₁.ar.ded; infer_instance`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM⟩ : ∃ M, M = (X₁.S.r * X₁.S.N) ^ 2` from `⟨_, rfl⟩`. Establish `hζ : IsPrimitiveRoot X₁.S.ζ M` using `hM ▸ X₁.S.prim`. Establish `hM0 : M ≠ 0`.

Rewrite using `[hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))`. Establish `hMu : IsUnit (M : X₁.o₁)` using `by rw [hM, Nat.cast_pow]; exact X₁.S.unit.pow 2`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hM0`. Establish `hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁`. Establish `h1 : e₂ + (e₁ + k * e₂) = e₁ + M * e₂` using `by rw [hk, Nat.succ_eq_add_one]; ring`.

Rewrite using `[← pow_add, h1, pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]`. Establish `hd1 : X₁.S.ζ ^ (e₁ + k * e₂) ≠ 1` using `fun h => hne (by rw [← hd, h, _root_.mul_one])`. Establish `hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂)`. Establish `h3 : X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂)))`. Rewrite using `[← hd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `((((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ hMu hd1))).neg`. Establish `hs : IsUnit (s₁ - s₂)` using `stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu`. Rewrite `hm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `hm hs`.
-/
theorem pow_eq_of_sub_mem (X₁ : GSet) (z₁ : X₁.M.Z) {s₁ s₂ : X₁.M.Z.presheaf.stalk z₁} {e₁ e₂ : ℕ}
    (h₁ : X₁.M.stalkHom z₁ s₁ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₁))
    (h₂ : X₁.M.stalkHom z₁ s₂ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₂))
    (hm : s₁ - s₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)) : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ e₂ := by
  haveI : IsDomain X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  by_contra hne
  obtain ⟨M, hM⟩ : ∃ M, M = (X₁.S.r * X₁.S.N) ^ 2 := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot X₁.S.ζ M := hM ▸ X₁.S.prim
  have hM0 : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hMu : IsUnit (M : X₁.o₁) := by rw [hM, Nat.cast_pow]; exact X₁.S.unit.pow 2
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁ := by
    have h1 : e₂ + (e₁ + k * e₂) = e₁ + M * e₂ := by rw [hk, Nat.succ_eq_add_one]; ring
    rw [← pow_add, h1, pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]
  have hd1 : X₁.S.ζ ^ (e₁ + k * e₂) ≠ 1 := fun h => hne (by rw [← hd, h, _root_.mul_one])
  have hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂) := by
    have h3 : X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂))) := by
      rw [← hd]; ring
    rw [h3]
    exact ((((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ hMu hd1))).neg
  have hs : IsUnit (s₁ - s₂) := stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm hs

/- English proof (translation)
Establish `hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2` using `pow_pos (Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)) 2`. Establish `hord` using `X₁.S.prim.eq_orderOf`. Rewrite using `[ZMod.natCast_eq_natCast_iff']`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Apply `X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)` to reduce the goal to its premises. Rewrite using `[hord, pow_mod_orderOf, pow_mod_orderOf]`. Conclude with `h`. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_eq_iff_cast (X₁ : GSet) (a b : ℕ) :
    X₁.S.ζ ^ a = X₁.S.ζ ^ b ↔ (a : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = (b : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) := by
  have hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2 :=
    pow_pos (Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)) 2
  have hord := X₁.S.prim.eq_orderOf
  rw [ZMod.natCast_eq_natCast_iff']
  constructor
  · intro h
    apply X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
    rw [hord, pow_mod_orderOf, pow_mod_orderOf]
    exact h
  · intro h
    calc X₁.S.ζ ^ a = X₁.S.ζ ^ (a % orderOf X₁.S.ζ) := (pow_mod_orderOf _ _).symm
      _ = X₁.S.ζ ^ (b % orderOf X₁.S.ζ) := by rw [← hord, h]
      _ = X₁.S.ζ ^ b := pow_mod_orderOf _ _

/- English proof (translation)
Take `⟨s₀, hs₀⟩` from `hne`. Establish `h1` using `hz s₀ hs₀`. Establish `h2` using `hz (-s₀) (hS s₀ hs₀)`. Establish `hneg : (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) = -⟨s₀, AddSubgroup.subset_closure hs₀⟩` using `rfl`. Rewrite `h2` using `[hneg, map_neg]`.

Establish `h2κ : (2 : ZMod M) * κ = 0` using `by linear_combination h1 + h2`. Establish `hcop : Nat.Coprime 2 M` using `(Nat.coprime_two_left).2 hM`. Establish `hκ : κ = 0`. Establish `hu : IsUnit (2 : ZMod M)`. Use `(ZMod.unitOfCoprime 2 hcop).isUnit` as an intermediate fact.

Rewrite `this` using `[ZMod.coe_unitOfCoprime, Nat.cast_ofNat]`. Then use the resulting hypothesis. Conclude with `hu.mul_right_eq_zero.1 h2κ`. Substitute `hκ` using the available equality. Introduce `a ha`. Rewrite using `[zero_add]`.

Use `AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0) (fun x hx => ?_) ?_ (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => ?_) ha` and prove the remaining obligations. Simplify using `using hz x hx`. Conclude with `map_zero h`. Establish `: (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`. Rewrite using `[this, map_add, h1, h2, add_zero]`.

Establish `: (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩` using `rfl`. Rewrite using `[this, map_neg, h1, neg_zero]`.
-/
theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have h1 := hz s₀ hs₀
  have h2 := hz (-s₀) (hS s₀ hs₀)
  have hneg : (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) =
      -⟨s₀, AddSubgroup.subset_closure hs₀⟩ := rfl
  rw [hneg, map_neg] at h2
  have h2κ : (2 : ZMod M) * κ = 0 := by linear_combination h1 + h2
  have hcop : Nat.Coprime 2 M := (Nat.coprime_two_left).2 hM
  have hκ : κ = 0 := by
    have hu : IsUnit (2 : ZMod M) := by
      have := (ZMod.unitOfCoprime 2 hcop).isUnit
      rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
    exact hu.mul_right_eq_zero.1 h2κ
  subst hκ
  intro a ha
  rw [zero_add]
  refine AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0) (fun x hx => ?_) ?_
    (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => ?_) ha
  · simpa using hz x hx
  · exact map_zero h
  · have : (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, h1, h2, add_zero]
  · have : (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩ := rfl
    rw [this, map_neg, h1, neg_zero]

end GlobalTheory.GSep.TwistIndep

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TwistIndep

/- English proof (translation)
Introduce `I X₁ z₁ act x₀ hdiv sg hsg hW V₁ _ _ _ ev₁ Y₁ _ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁ V₂ _ _ _ ev₂ Y₂ _ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ hr'`. Take `⟨r, hr, hr0⟩` from `hr'`. Take `⟨ε₁, ε₂, h1, h2, haff⟩` from `GlobalTheory.T.twistedSum_exponents_differ_affine_two_members I X₁ z₁ act x₀ hdiv sg hsg hW V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂`. Establish `hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ`. Take `⟨κ, h, hκ⟩` from `haff τ hτ`.

Establish `hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0`. Introduce `s hs`. Establish `hsH : s ∈ X₁.S.HH X₁.M z₁` using `AddSubgroup.subset_closure hs`. Take `⟨U₁, hU₁⟩` from `GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ s hsH`. Take `⟨U₂, hU₂⟩` from `GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ s hsH`.

Establish `hw₁` using `h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ`. Establish `hw₂` using `h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ`. Take `⟨q₁, hq₁⟩` from `stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)`. Take `⟨q₂, hq₂⟩` from `stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)`. Take `⟨u, hu⟩` from `(X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩`.

Establish `hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s` using `by rw [← RatModel.coe_stalkEquiv, hu]`. Establish `r₁` using `GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () hs τ hτ sg _ hw₁ q₁ u hq₁ hu'`. Establish `r₂` using `GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () hs τ hτ sg _ hw₂ q₂ u hq₂ hu'`. Establish `m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)` using `mem_maximalIdeal_of_map ev₁ (by rwa [map_sub, map_one])`. Establish `m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)` using `mem_maximalIdeal_of_map ev₂ (by rwa [map_sub, map_one])`.

Establish `hunit : IsUnit u`. Establish `hqu : IsUnit (q₁ * u)`. Assume the negation of the conclusion as `hn`. Establish `hmem : q₁ * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)` using `(IsLocalRing.mem_maximalIdeal _).2 hn`. Establish `h1m : (1 : X₁.M.Z.presheaf.stalk z₁) ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)`.

Simplify using `using sub_mem hmem m₁'`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1m)`. Conclude with `isUnit_of_mul_isUnit_right hqu`. Establish `hdiff : (q₁ - q₂) * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)`. Establish `h3` using `sub_mem m₁' m₂'`.

Rewrite `h3` using `[show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring]`. Then use the resulting hypothesis. Establish `hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)`. Take `⟨v, hv⟩` from `hunit.exists_right_inv`. Establish `h4` using `Ideal.mul_mem_right v _ hdiff`. Rewrite `h4` using `[_root_.mul_assoc, hv, _root_.mul_one]`. Then use the resulting hypothesis.

Establish `heq` using `(pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq)`. Rewrite using `[← hκ s hsH, heq, sub_self]`. Establish `hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2)`. Establish `h5 : Odd (X₁.S.r * X₁.S.N)`. Take `⟨j, -, hj⟩` from `X₁.ρ.r_eq`.

Rewrite using `[hj, X₁.ρ.N_eq]`. Conclude with `X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow`. Conclude with `h5.pow`. Establish `hz` using `affine_zero hodd (X₁.S.supI X₁.M z₁) (GlobalTheory.T.neg_mem_dividingLabels_thetaSystem X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup`. Introduce `b hb`.

Rewrite using `[pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]`. Conclude with `hz b hb`. Take `⟨zt, hzt⟩` from `stalk_of_base X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))`. Take `⟨wt, hwt⟩` from `GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ sg τ hτ`. Take `⟨s₁, hs₁⟩` from `stalk_of_base X₁ z₁ (X₁.S.ζ ^ e₁)`.

Take `⟨s₀, hs₀⟩` from `stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)`. Establish `hA` using `hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt`. Establish `hB` using `h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt`. Use `haveI : IsNoetherianRing V₁ := 𝔪₁.cn.1`. Establish `hE` using `GlobalTheory.AdicSum.sumI_unique (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hA hB`.

Rewrite `hE` using `[map_mul, map_mul]`. Establish `hE' : ev₁ s₁ = ev₁ s₀` using `mul_right_cancel₀ hr0 hE`. Establish `hm : s₁ - s₀ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)` using `mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _)`. Establish `hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ` using `pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀ hm`. Establish `hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁`.

Rewrite using `[hpe, ← hlab]`. Conclude with `(hφ _ (hlab₁ c₁)).symm`. Establish `hF` using `h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ`. Introduce `zt' h' hzt' hh' wt' hwt'`. Conclude with `hF zt' h' hzt' (by rw [hpe2]; exact hh') wt' hwt'`.
-/
theorem twistSum_indep : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  intro I X₁ z₁ act x₀ hdiv sg hsg hW V₁ _ _ _ ev₁ Y₁ _ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
    V₂ _ _ _ ev₂ Y₂ _ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ hr'
  obtain ⟨r, hr, hr0⟩ := hr'
  obtain ⟨ε₁, ε₂, h1, h2, haff⟩ := GlobalTheory.T.twistedSum_exponents_differ_affine_two_members I X₁ z₁ act x₀ hdiv sg hsg hW V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂

  have hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ := by
    obtain ⟨κ, h, hκ⟩ := haff τ hτ
    have hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0 := by
      intro s hs
      have hsH : s ∈ X₁.S.HH X₁.M z₁ := AddSubgroup.subset_closure hs
      obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ s hsH
      obtain ⟨U₂, hU₂⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ s hsH
      have hw₁ := h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ
      have hw₂ := h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ
      obtain ⟨q₁, hq₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)
      obtain ⟨q₂, hq₂⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)
      obtain ⟨u, hu⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩
      have hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s := by rw [← RatModel.coe_stalkEquiv, hu]
      have r₁ := GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ ()
        hs τ hτ sg _ hw₁ q₁ u hq₁ hu'
      have r₂ := GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ ()
        hs τ hτ sg _ hw₂ q₂ u hq₂ hu'
      have m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₁ (by rwa [map_sub, map_one])
      have m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₂ (by rwa [map_sub, map_one])
      have hunit : IsUnit u := by
        have hqu : IsUnit (q₁ * u) := by
          by_contra hn
          have hmem : q₁ * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := (IsLocalRing.mem_maximalIdeal _).2 hn
          have h1m : (1 : X₁.M.Z.presheaf.stalk z₁) ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
            simpa using sub_mem hmem m₁'
          exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
        exact isUnit_of_mul_isUnit_right hqu
      have hdiff : (q₁ - q₂) * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        have h3 := sub_mem m₁' m₂'
        rwa [show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring] at h3
      have hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        obtain ⟨v, hv⟩ := hunit.exists_right_inv
        have h4 := Ideal.mul_mem_right v _ hdiff
        rwa [_root_.mul_assoc, hv, _root_.mul_one] at h4
      have heq := (pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq)
      rw [← hκ s hsH, heq, sub_self]
    have hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2) := by
      have h5 : Odd (X₁.S.r * X₁.S.N) := by
        obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
        rw [hj, X₁.ρ.N_eq]
        exact X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow
      exact h5.pow
    have hz := affine_zero hodd (X₁.S.supI X₁.M z₁) (GlobalTheory.T.neg_mem_dividingLabels_thetaSystem X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup
    intro b hb
    rw [pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]
    exact hz b hb

  obtain ⟨zt, hzt⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ sg τ hτ
  obtain ⟨s₁, hs₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ e₁)
  obtain ⟨s₀, hs₀⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)
  have hA := hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt
  have hB := h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt
  haveI : IsNoetherianRing V₁ := 𝔪₁.cn.1
  have hE := GlobalTheory.AdicSum.sumI_unique (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hA hB
  rw [map_mul, map_mul] at hE
  have hE' : ev₁ s₁ = ev₁ s₀ := mul_right_cancel₀ hr0 hE
  have hm : s₁ - s₀ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
    mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _)
  have hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ := pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀ hm

  have hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁ := by
    rw [hpe, ← hlab]
    exact (hφ _ (hlab₁ c₁)).symm
  have hF := h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ
  intro zt' h' hzt' hh' wt' hwt'
  exact hF zt' h' hzt' (by rw [hpe2]; exact hh') wt' hwt'

end GlobalTheory.GSep
