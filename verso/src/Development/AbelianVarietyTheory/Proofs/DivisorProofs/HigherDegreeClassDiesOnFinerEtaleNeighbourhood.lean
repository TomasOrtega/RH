import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyVanishesArtinian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.KillFiner

/- English proof (translation)
Establish `e : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ` using `by show sch.map (Spec.map (CommRingCat.ofHom (ψ.comp ρ))) = sch.map (Spec.map (CommRingCat.ofHom ψ)) ≫ sch.map (Spec.map (CommRingCat.ofHom ρ))`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]`. Rewrite using `[e, pull_comp]`.
-/
theorem pull_spMap_comp (q : ℕ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ρ : R →+* S) (ψ : S →+* T)
    (n i : ℤ) (z : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp ρ)) _ _ z = pull _ (spMap ψ) _ _ (pull _ (spMap ρ) _ _ z) := by
  have e : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
    show sch.map (Spec.map (CommRingCat.ofHom (ψ.comp ρ))) = sch.map (Spec.map (CommRingCat.ofHom ψ)) ≫ sch.map (Spec.map (CommRingCat.ofHom ρ))
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]
  rw [e, pull_comp]

/- English proof (translation)
Introduce `q _ k B _ _ _ _ _ _ hq f hf hfu A' _ _ _ hN`. Use `set f' : A' := algebraMap B A' f with hf'`. Introduce `m i hm z`. Use `set R := Localization.Away f'`. Establish `hBf : ¬ IsField B` using `fun hB => hfu (by`.

Use `letI := hB.toField`. Conclude with `isUnit_iff_ne_zero.mpr hf)`. Establish `hqR : IsUnit (q : R)`. Use `((hq.map (algebraMap k B)).map (algebraMap B A')).map (algebraMap A' R)` as an intermediate fact. Simplify `this` using `only [map_natCast]`.

Establish `hFR : Subsingleton (Ht q (sp (FractionRing R)) m i)`. Take `⟨hArt, hRed⟩` from `GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced B f A'`. Use `GlobalTheory.T.cohomology_vanishes_artinian q _ m i (fun M => ?_)` and prove the remaining obligations. Take `⟨alg, halg⟩` from `GlobalTheory.T.etale_maximal_quotient_algebraic k B hBf f hf A' M`. Establish `hqM : IsUnit (q : FractionRing R ⧸ M.asIdeal)`.

Use `(hqR.map (algebraMap R (FractionRing R))).map (Ideal.Quotient.mk M.asIdeal)` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Then use the resulting hypothesis. Use `haveI := M.isMaximal`. Use `letI : Field (FractionRing R ⧸ M.asIdeal) := Ideal.Quotient.field _`. Conclude with `GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing R ⧸ M.asIdeal) hqM m i hm`.

Take `⟨g, hg, hz⟩` from `GlobalTheory.T.class_vanishes_away_nonZeroDivisor q R hqR m i z (Subsingleton.elim _ _)`. Establish `hf'reg : IsSMulRegular A' f'`. Establish `h` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A') (mem_nonZeroDivisors_of_ne_zero hf)`. Introduce `x y hxy`. Apply `h` to reduce the goal to its premises.

Simplify `hxy` using `[Algebra.smul_def, hf']`. Establish `hpow : ∀ (N : ℕ) (y : A'), f' ^ N * y = 0 → y = 0`. Introduce `N y hy`. Proceed by induction on `N generalizing y with`. Consider the case `zero => simpa using hy`.

Consider the case `succ N ih`. Apply `ih` to reduce the goal to its premises. Apply `hf'reg` to reduce the goal to its premises. Simplify using `only [smul_eq_mul, mul_zero]`. Rewrite using `[← hy]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers f') g`. Simplify using `only at hs`. Establish `ha : a ∈ nonZeroDivisors A'`. It suffices to establish `key : ∀ y : A', y * a = 0 → y = 0 from mem_nonZeroDivisors_iff.mpr ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩`.

Introduce `y hy`. Establish `h1 : algebraMap A' R y * g = 0`. Establish `hsu : IsUnit (algebraMap A' R (s : A'))` using `IsLocalization.map_units R s`. Apply `hsu.mul_left_injective` to reduce the goal to its premises. Simplify using `only [zero_mul]`.

Rewrite using `[mul_assoc, hs, ← map_mul, hy, map_zero]`. Establish `h2 : algebraMap A' R y = 0` using `(mem_nonZeroDivisors_iff.mp hg).2 _ h1`. Rewrite `h2` using `[IsLocalization.map_eq_zero_iff (Submonoid.powers f')]`. Take `⟨⟨c, N, rfl⟩, hc⟩` from `h2`. Conclude with `hpow N y hc`.

Set `J : Ideal A'` to `{ carrier := {x | ∃ N : ℕ, a ∣ x * f' ^ N} add_mem' := by`. Introduce and unpack `x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩`. Use `⟨N₁ + N₂, ?_⟩` and prove the remaining obligations. Establish `e : (x + y) * f' ^ (N₁ + N₂) = (x * f' ^ N₁) * f' ^ N₂ + (y * f' ^ N₂) * f' ^ N₁` using `by ring`. Rewrite using `[e]`.

Conclude with `dvd_add (h₁.mul_right _) (h₂.mul_right _)`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨N, h⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, mul_assoc]`. Conclude with `h.mul_left c }`. Establish `hJ : J ⊔ Ideal.span {f'} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Establish `hfM : f' ∈ M` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Take `⟨t, htM, N, hN⟩` from `GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus B A' f hf hN a ha M hM hfM`. Conclude with `htM (hle (Ideal.mem_sup_left ⟨N, hN⟩))`. Establish `h1 : (1 : A') ∈ J ⊔ Ideal.span {f'}` using `by rw [hJ]; trivial`. Take `⟨h, ⟨N, hhN⟩, y, hy, hhy⟩` from `Submodule.mem_sup.mp h1`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Use `⟨Localization.Away h, inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom B A' (Localization.Away h), GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one B A' f h c hN (by rw [← hhy]; ring), ?_⟩` and prove the remaining obligations. Use `set φ := IsScalarTower.toAlgHom B A' (Localization.Away h)`. Use `set S := Localization.Away (algebraMap B (Localization.Away h) f)`. Establish `hcomp : ∀ x : A', awayHom φ f (algebraMap A' R x) = algebraMap _ S (φ x)` using `fun x => RingHom.congr_fun (awayHom_comp_algebraMap φ f) x`.

Establish `hfS : IsUnit (algebraMap _ S (φ f'))`. Rewrite using `[hf', AlgHom.commutes]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`. Establish `hhS : IsUnit (algebraMap _ S (φ h))` using `(IsLocalization.Away.algebraMap_isUnit h).map (algebraMap _ S)`. Establish `haS : IsUnit (algebraMap _ S (φ a))`.

Apply `isUnit_of_dvd_unit (y := algebraMap _ S (φ (h * f' ^ N)))` to reduce the goal to its premises. Conclude with `map_dvd _ (map_dvd _ hhN)`. Rewrite using `[map_mul, map_pow, map_mul, map_pow]`. Conclude with `hhS.mul (hfS.pow N)`. Establish `hgS : IsUnit (awayHom φ f g)`.

Establish `e : awayHom φ f g * awayHom φ f (algebraMap A' R s) = algebraMap _ S (φ a)`. Rewrite using `[← map_mul, hs, hcomp]`. Rewrite `haS` using `[← e]`. Conclude with `isUnit_of_mul_isUnit_left haS`. Establish `hfac : (IsLocalization.Away.lift g hgS).comp (algebraMap R (Localization.Away g)) = awayHom φ f` using `IsLocalization.Away.lift_comp g hgS`.

Rewrite using `[← hfac, pull_spMap_comp, hz, map_zero]`.
-/
theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu A' _ _ _ hN
  set f' : A' := algebraMap B A' f with hf'
  intro m i hm z
  set R := Localization.Away f'
  have hBf : ¬ IsField B := fun hB => hfu (by
    letI := hB.toField; exact isUnit_iff_ne_zero.mpr hf)
  have hqR : IsUnit (q : R) := by
    have := ((hq.map (algebraMap k B)).map (algebraMap B A')).map (algebraMap A' R)
    simpa only [map_natCast] using this

  have hFR : Subsingleton (Ht q (sp (FractionRing R)) m i) := by
    obtain ⟨hArt, hRed⟩ := GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced B f A'
    refine GlobalTheory.T.cohomology_vanishes_artinian q _ m i (fun M => ?_)
    obtain ⟨alg, halg⟩ := GlobalTheory.T.etale_maximal_quotient_algebraic k B hBf f hf A' M
    have hqM : IsUnit (q : FractionRing R ⧸ M.asIdeal) := by
      have := (hqR.map (algebraMap R (FractionRing R))).map (Ideal.Quotient.mk M.asIdeal)
      rwa [map_natCast, map_natCast] at this
    haveI := M.isMaximal
    letI : Field (FractionRing R ⧸ M.asIdeal) := Ideal.Quotient.field _
    exact GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing R ⧸ M.asIdeal) hqM m i hm

  obtain ⟨g, hg, hz⟩ := GlobalTheory.T.class_vanishes_away_nonZeroDivisor q R hqR m i z (Subsingleton.elim _ _)

  have hf'reg : IsSMulRegular A' f' := by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A') (mem_nonZeroDivisors_of_ne_zero hf)
    intro x y hxy
    apply h
    simpa [Algebra.smul_def, hf'] using hxy
  have hpow : ∀ (N : ℕ) (y : A'), f' ^ N * y = 0 → y = 0 := by
    intro N y hy
    induction N generalizing y with
    | zero => simpa using hy
    | succ N ih =>
      apply ih
      apply hf'reg
      simp only [smul_eq_mul, mul_zero]
      rw [← hy]; ring

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f') g
  simp only at hs
  have ha : a ∈ nonZeroDivisors A' := by
    suffices key : ∀ y : A', y * a = 0 → y = 0 from
      mem_nonZeroDivisors_iff.mpr ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩
    intro y hy
    have h1 : algebraMap A' R y * g = 0 := by
      have hsu : IsUnit (algebraMap A' R (s : A')) := IsLocalization.map_units R s
      apply hsu.mul_left_injective
      simp only [zero_mul]
      rw [mul_assoc, hs, ← map_mul, hy, map_zero]
    have h2 : algebraMap A' R y = 0 := (mem_nonZeroDivisors_iff.mp hg).2 _ h1
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f')] at h2
    obtain ⟨⟨c, N, rfl⟩, hc⟩ := h2
    exact hpow N y hc

  let J : Ideal A' :=
    { carrier := {x | ∃ N : ℕ, a ∣ x * f' ^ N}
      add_mem' := by
        rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨N₁ + N₂, ?_⟩
        have e : (x + y) * f' ^ (N₁ + N₂) = (x * f' ^ N₁) * f' ^ N₂ + (y * f' ^ N₂) * f' ^ N₁ := by ring
        rw [e]
        exact dvd_add (h₁.mul_right _) (h₂.mul_right _)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨N, h⟩
        refine ⟨N, ?_⟩
        rw [smul_eq_mul, mul_assoc]
        exact h.mul_left c }
  have hJ : J ⊔ Ideal.span {f'} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hfM : f' ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨t, htM, N, hN⟩ := GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus B A' f hf hN a ha M hM hfM
    exact htM (hle (Ideal.mem_sup_left ⟨N, hN⟩))
  have h1 : (1 : A') ∈ J ⊔ Ideal.span {f'} := by rw [hJ]; trivial
  obtain ⟨h, ⟨N, hhN⟩, y, hy, hhy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy

  refine ⟨Localization.Away h, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom B A' (Localization.Away h), GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one B A' f h c hN (by rw [← hhy]; ring), ?_⟩
  set φ := IsScalarTower.toAlgHom B A' (Localization.Away h)
  set S := Localization.Away (algebraMap B (Localization.Away h) f)
  have hcomp : ∀ x : A', awayHom φ f (algebraMap A' R x) = algebraMap _ S (φ x) := fun x =>
    RingHom.congr_fun (awayHom_comp_algebraMap φ f) x
  have hfS : IsUnit (algebraMap _ S (φ f')) := by
    rw [hf', AlgHom.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
  have hhS : IsUnit (algebraMap _ S (φ h)) :=
    (IsLocalization.Away.algebraMap_isUnit h).map (algebraMap _ S)
  have haS : IsUnit (algebraMap _ S (φ a)) := by
    apply isUnit_of_dvd_unit (y := algebraMap _ S (φ (h * f' ^ N)))
    · exact map_dvd _ (map_dvd _ hhN)
    · rw [map_mul, map_pow, map_mul, map_pow]; exact hhS.mul (hfS.pow N)
  have hgS : IsUnit (awayHom φ f g) := by
    have e : awayHom φ f g * awayHom φ f (algebraMap A' R s) = algebraMap _ S (φ a) := by
      rw [← map_mul, hs, hcomp]
    rw [← e] at haS
    exact isUnit_of_mul_isUnit_left haS
  have hfac : (IsLocalization.Away.lift g hgS).comp (algebraMap R (Localization.Away g)) = awayHom φ f :=
    IsLocalization.Away.lift_comp g hgS
  rw [← hfac, pull_spMap_comp, hz, map_zero]
end GlobalTheory.KillFiner
