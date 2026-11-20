import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.SupISymm

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap o Ω)` using `ArithBase.inj`. Establish `hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2)` using `S.prim.map_of_injective hinj`. Establish `hpos : 0 < (S.r * S.N) ^ 2`. Use `S.N_ge` as an intermediate fact. Use `S.r_pos` as an intermediate fact.

Check the signs of the components of the expression. Take `⟨k, -, hk⟩` from `hp.eq_pow_of_pow_eq_one hε`. Establish `hζu : IsUnit S.ζ` using `S.prim.isUnit hpos.ne'`. Establish `hc' : c = 1 ∨ c = -1`. Establish `: c * c = 1` using `by rw [← sq]; exact hc`.

Conclude with `mul_self_eq_one_iff.1 this`. Break down `hc' with rfl | rfl` into its components or cases. Conclude with `⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩`. Conclude with `⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩`.
-/
theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

/- English proof (translation)
Take `⟨c, ε, hc, hε, h⟩` from `H a`. Take `⟨u, hu⟩` from `exists_unit_of_pow_eq_one S hc hε`. Conclude with `⟨u, by rw [h, hu]⟩`.
-/
theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

/- English proof (translation)
Take `⟨hne, hdiv⟩` from `ha`. Take `⟨u, hu⟩` from `exists_unit_th_neg S H a`. Establish `hu0 : algebraMap o Ω (u : o) ≠ 0`. Introduce `h0`. Establish `h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1` using `by simp`.

Rewrite `h1` using `[map_mul, h0, zero_mul]`. Conclude with `zero_ne_one h1`. Use `⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `exists_unit_th_neg S H (-j)`. Rewrite `hv` using `[neg_neg]`.

Establish `key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a)`. Establish `hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)`. Rewrite using `[hv, hu, map_mul, hi]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[key]`. Conclude with `(M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))`.
-/
theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.GSep.SupISymm

open GlobalTheory.GSep.SupISymm in

/- English proof (translation)
Introduce `X₁ z₁ a ha`. Conclude with `neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha`.
-/
theorem GlobalTheory.GSep.neg_mem_supI : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
