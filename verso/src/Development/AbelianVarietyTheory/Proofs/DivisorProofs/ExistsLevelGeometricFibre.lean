import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliWithSymplecticLevelRepresentab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLevelFamily
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `: Flat (Spec.map (CommRingCat.ofHom σ))` using `inferInstance`. Establish `: Surjective (Spec.map (CommRingCat.ofHom σ))` using `⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `(congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm`.
-/
theorem unitOn_pull_spMap {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

/- English proof (translation)
Establish `h` using `hP a (-a + b)`. Rewrite `h` using `[add_neg_cancel_left]`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Conclude with `mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)`. Introduce `e`. Rewrite using `[e, _root_.mul_one]`.
-/
theorem eq_iff_of_add {La G : Type} [AddGroup La] [Group G] (P : La → G)
    (hP : ∀ a b, P (a + b) = P a * P b) (a b : La) : P a = P b ↔ P (-a + b) = 1 := by
  have h := hP a (-a + b)
  rw [add_neg_cancel_left] at h
  rw [h]
  constructor
  · intro e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  · intro e
    rw [e, _root_.mul_one]

/- English proof (translation)
Set `m : La →+ La` to `AddMonoidHom.mk' (fun a : La => n • a) (fun a b => smul_add n a b)`. Set `K : AddSubgroup La` to `m.range`. Establish `hK : ∀ a, a ∈ K ↔ ∃ b, a = n • b` using `fun a => by`. Simplify using `only [K, AddMonoidHom.mem_range]`. Conclude with `⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩`.

Establish `: AddGroup.FG La` using `Module.Finite.iff_addGroup_fg.1 inferInstance`. Establish `: Finite (La ⧸ K)` using `AddCommGroup.finite_of_fg_torsion _ fun q => by`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H a`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK]`. Conclude with `⟨a, rfl⟩`. Establish `hmk : ∀ (R : La → G), (∀ a b, R (a + b) = R a * R b) → (∀ a, R a = 1 ↔ ∃ b, a = n • b) → ∀ a b, R a = R b ↔ (a : La ⧸ K) = b` using `fun R hRa hR a b => by`. Rewrite using `[eq_iff_of_add R hRa, QuotientAddGroup.eq, hK, hR]`. Use `choose f hf using hPQ`.

Set `g : La ⧸ K → La ⧸ K` to `fun q => (f q.out : La ⧸ K)`. Establish `hg : Function.Injective g` using `fun q q' e => by`. Establish `e'` using `(hmk Q hQa hQ _ _).2 e`. Rewrite `e'` using `[← hf, ← hf, hmk P hPa hP]`. Simplify using `using e'`.

Take `⟨q, hq⟩` from `(Finite.injective_iff_surjective.1 hg) (c : La ⧸ K)`. Use `⟨q.out, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hmk Q hQa hQ]`. Conclude with `hq`.
-/
theorem exists_eq_of_count {La G : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group G] (n : ℕ) (hn : 0 < n)
    (P Q : La → G) (hPa : ∀ a b, P (a + b) = P a * P b) (hQa : ∀ a b, Q (a + b) = Q a * Q b)
    (hP : ∀ a, P a = 1 ↔ ∃ b, a = n • b) (hQ : ∀ a, Q a = 1 ↔ ∃ b, a = n • b)
    (hPQ : ∀ a, ∃ c, P a = Q c) (c : La) : ∃ a, P a = Q c := by
  let m : La →+ La := AddMonoidHom.mk' (fun a : La => n • a) (fun a b => smul_add n a b)
  let K : AddSubgroup La := m.range
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = n • b := fun a => by
    simp only [K, AddMonoidHom.mem_range]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have : AddGroup.FG La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Finite (La ⧸ K) := AddCommGroup.finite_of_fg_torsion _ fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK]
      exact ⟨a, rfl⟩
  have hmk : ∀ (R : La → G), (∀ a b, R (a + b) = R a * R b) → (∀ a, R a = 1 ↔ ∃ b, a = n • b) →
      ∀ a b, R a = R b ↔ (a : La ⧸ K) = b := fun R hRa hR a b => by
    rw [eq_iff_of_add R hRa, QuotientAddGroup.eq, hK, hR]
  choose f hf using hPQ
  let g : La ⧸ K → La ⧸ K := fun q => (f q.out : La ⧸ K)
  have hg : Function.Injective g := fun q q' e => by
    have e' := (hmk Q hQa hQ _ _).2 e
    rw [← hf, ← hf, hmk P hPa hP] at e'
    simpa using e'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hg) (c : La ⧸ K)
  refine ⟨q.out, ?_⟩
  rw [hf, hmk Q hQa hQ]
  exact hq

end GlobalTheory.UPel.GeometricLevelExistence

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

end GlobalTheory.UPel.GeometricLevelExistence
