import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

noncomputable section
namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `o Ω _ _ _ M U hU z hz x hx`. Take `⟨W, f, hzW, rfl⟩` from `hx`. Establish `hne : (U : Set M.Z).Nonempty` using `⟨z, hz⟩`. Take `⟨g, hgW, hzg⟩` from `hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz`. Establish `hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty` using `⟨z, hzg⟩`.

Use `hU.isLocalization_basicOpen g` as an intermediate fact. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g (resG M.Z hgW f)`. Establish `h1` using `congrArg (M.res _ hg) ha`. Establish `h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t` using `fun t => M.res_resG (M.Z.basicOpen_le g) hg t`. Rewrite `h1` using `[map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply]`.

Establish `hu` using `(isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)`. Establish `hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n`. Rewrite using `[← M.res_apply U hne, map_pow, res_apply]`. Establish `h0 : valF M.pt U (g ^ n) ≠ 0`. Rewrite using `[hb]`.

Conclude with `pow_ne_zero _ hu.1`. Use `⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_, (eq_div_iff h0).2 h1⟩` and prove the remaining obligations. Rewrite using `[hb, ← inv_pow]`. Conclude with `pow_mem hu.2 n`.
-/
theorem exists_eq_div_of_mem_O_affine : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  intro o Ω _ _ _ M U hU z hz x hx
  obtain ⟨W, f, hzW, rfl⟩ := hx
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzg⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgW f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply] at h1
  have hu := (isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)
  have hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n := by
    rw [← M.res_apply U hne, map_pow, res_apply]
  have h0 : valF M.pt U (g ^ n) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ hu.1
  refine ⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_,
    (eq_div_iff h0).2 h1⟩
  rw [hb, ← inv_pow]
  exact pow_mem hu.2 n

end GlobalTheory.Poinc
