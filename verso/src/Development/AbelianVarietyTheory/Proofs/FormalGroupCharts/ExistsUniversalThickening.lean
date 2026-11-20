import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IsolPt

/- English proof (translation)
Establish `hN : IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing k B`. Establish `hJ : IsJacobsonRing B` using `isJacobsonRing_of_finiteType (A := k)`. Establish `hsur : ∀ m : Ideal B, m.IsMaximal → ∃ f : B →ₐ[k] AlgebraicClosure k, RingHom.ker f = m`. Introduce `m hm`. Use `letI := Ideal.Quotient.field m`.

Establish `: Module.Finite k (B ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)`. Set `g : (B ⧸ m) →ₐ[k] AlgebraicClosure k` to `IsAlgClosed.lift`. Use `⟨g.comp (Ideal.Quotient.mkₐ k m), ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Simplify using `only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`.

Rewrite using `[map_eq_zero_iff g g.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hfin : {m : Ideal B | m.IsMaximal}.Finite` using `(Set.finite_range fun f : B →ₐ[k] AlgebraicClosure k => RingHom.ker f).subset hsur`. Rewrite using `[isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]`. Introduce `p hp`. Establish `h1 : p.jacobson = p` using `IsJacobsonRing.out hJ hp.isRadical`.

Establish `hf : {J : Ideal B | p ≤ J ∧ J.IsMaximal}.Finite` using `hfin.subset fun _ h => h.2`. Establish `h2 : hf.toFinset.inf id ≤ p`. Rewrite using `[Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]`. Conclude with `h1.le`. Take `⟨m, hm, hle⟩` from `hp.inf_le'.1 h2`.

Rewrite `hm` using `[Set.Finite.mem_toFinset]`. Establish `: m = p` using `le_antisymm hle hm.1`. Conclude with `this ▸ hm.2`.
-/
theorem isArtinianRing_of_finite_points (k B : Type) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Finite (B →ₐ[k] AlgebraicClosure k)] : IsArtinianRing B := by
  have hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hJ : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hsur : ∀ m : Ideal B, m.IsMaximal → ∃ f : B →ₐ[k] AlgebraicClosure k, RingHom.ker f = m := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
    let g : (B ⧸ m) →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
    refine ⟨g.comp (Ideal.Quotient.mkₐ k m), ?_⟩
    ext b
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff g g.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hfin : {m : Ideal B | m.IsMaximal}.Finite :=
    (Set.finite_range fun f : B →ₐ[k] AlgebraicClosure k => RingHom.ker f).subset hsur
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : p.jacobson = p := IsJacobsonRing.out hJ hp.isRadical
  have hf : {J : Ideal B | p ≤ J ∧ J.IsMaximal}.Finite := hfin.subset fun _ h => h.2
  have h2 : hf.toFinset.inf id ≤ p := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact h1.le
  obtain ⟨m, hm, hle⟩ := hp.inf_le'.1 h2
  rw [Set.Finite.mem_toFinset] at hm
  have : m = p := le_antisymm hle hm.1
  exact this ▸ hm.2

/- English proof (translation)
Take `⟨n, hn⟩` from `IsArtinian.monotone_stabilizes (R := B) (M := B) ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩`. Use `⟨n, fun j => ?_⟩` and prove the remaining obligations. Establish `h1 : I ^ n = I ^ (n + (j + 1))` using `hn (n + (j + 1)) (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_stable {B : Type} [CommRing B] [IsArtinianRing B] (I : Ideal B) :
    ∃ M : ℕ, ∀ j : ℕ, I ^ (M + 1) ≤ I ^ (j + 1) := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := B) (M := B)
    ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  refine ⟨n, fun j => ?_⟩
  have h1 : I ^ n = I ^ (n + (j + 1)) := hn (n + (j + 1)) (by omega)
  calc I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
    _ = I ^ (n + (j + 1)) := h1
    _ ≤ I ^ (j + 1) := Ideal.pow_le_pow_right (by omega)

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_pow_stable (RingHom.ker e)`. Use `set I : Ideal B := RingHom.ker e ^ (M + 1) with hI`. Establish `hIe : ∀ b ∈ I, e b = 0` using `fun b hb => Ideal.pow_le_self (Nat.succ_ne_zero M) hb`. Use `⟨B ⧸ I, inferInstance, inferInstance, Ideal.Quotient.liftₐ I e hIe, M, Ideal.Quotient.mkₐ k I, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : RingHom.ker (Ideal.Quotient.liftₐ I e hIe) ≤ (RingHom.ker e).map (Ideal.Quotient.mk I)`.

Introduce `x hx`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `Ideal.mem_map_of_mem _ hx`. Use `le_bot_iff.1 ((Ideal.pow_right_mono h _).trans ?_)` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow, ← hI, Ideal.map_quotient_self]`.

Use extensionality with `b`. Both sides reduce to the same expression. Introduce `Q _ _ augQ j hj z hz`. Establish `hzI : ∀ b ∈ I, z b = 0`. Introduce `b hb`.

Establish `h : (RingHom.ker e).map z ≤ RingHom.ker augQ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `c hc`. Express the relevant statement in the definitionally equal form `augQ (z c) = 0`. Rewrite using `[← AlgHom.comp_apply, hz]`.

Conclude with `hc`. Establish `h2` using `Ideal.mem_map_of_mem z (hM j hb)`. Rewrite `h2` using `[Ideal.map_pow]`. Establish `h3` using `Ideal.pow_right_mono h _ h2`. Rewrite `h3` using `[hj]`. Then use the resulting hypothesis.

Use `⟨Ideal.Quotient.liftₐ I z hzI, ?_, ?_⟩` and prove the remaining obligations. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Use extensionality with `b`. Conclude with `DFunLike.congr_fun hz b`. Use extensionality with `b`.

Both sides reduce to the same expression.
-/
theorem exists_thickening {k B : Type} [Field k] [CommRing B] [Algebra k B] [IsArtinianRing B]
    (e : B →ₐ[k] k) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ)
      (π : B →ₐ[k] A), RingHom.ker aug ^ (M + 1) = ⊥ ∧ aug.comp π = e ∧
      ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ),
        RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : B →ₐ[k] Q, augQ.comp z = e →
        ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = a.comp π := by
  obtain ⟨M, hM⟩ := exists_pow_stable (RingHom.ker e)
  set I : Ideal B := RingHom.ker e ^ (M + 1) with hI
  have hIe : ∀ b ∈ I, e b = 0 := fun b hb => Ideal.pow_le_self (Nat.succ_ne_zero M) hb
  refine ⟨B ⧸ I, inferInstance, inferInstance, Ideal.Quotient.liftₐ I e hIe, M, Ideal.Quotient.mkₐ k I,
    ?_, ?_, ?_⟩
  · have h : RingHom.ker (Ideal.Quotient.liftₐ I e hIe) ≤ (RingHom.ker e).map (Ideal.Quotient.mk I) := by
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    refine le_bot_iff.1 ((Ideal.pow_right_mono h _).trans ?_)
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  · ext b
    rfl
  · intro Q _ _ augQ j hj z hz
    have hzI : ∀ b ∈ I, z b = 0 := by
      intro b hb
      have h : (RingHom.ker e).map z ≤ RingHom.ker augQ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        change augQ (z c) = 0
        rw [← AlgHom.comp_apply, hz]
        exact hc
      have h2 := Ideal.mem_map_of_mem z (hM j hb)
      rw [Ideal.map_pow] at h2
      have h3 := Ideal.pow_right_mono h _ h2
      rwa [hj] at h3
    refine ⟨Ideal.Quotient.liftₐ I z hzI, ?_, ?_⟩
    · apply Ideal.Quotient.algHom_ext
      ext b
      exact DFunLike.congr_fun hz b
    · ext b
      rfl

/- English proof (translation)
Establish `hl` using `IsOpenImmersion.lift_fac v.left _ hsub`. Take `⟨ψ, hψ⟩` from `NatFun.spMap_surjective (k := k) (A := B) (B := A) (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by`. Rewrite using `[← Over.w v, ← Category.assoc, hl, Over.w]))`. Use `⟨ψ, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hψ]`.

Conclude with `hl.symm`.
-/
theorem exists_factor {k A B : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {X : Over (Spec (CommRingCat.of k))} (x : Chart.sp (R₀ := k) A ⟶ X) (v : Chart.sp (R₀ := k) B ⟶ X)
    [IsOpenImmersion v.left] (hsub : Set.range x.left ⊆ Set.range v.left) :
    ∃ ψ : B →ₐ[k] A, x = Chart.spMap ψ ≫ v := by
  have hl := IsOpenImmersion.lift_fac v.left _ hsub
  obtain ⟨ψ, hψ⟩ := NatFun.spMap_surjective (k := k) (A := B) (B := A)
    (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by
      rw [← Over.w v, ← Category.assoc, hl, Over.w]))
  refine ⟨ψ, Over.OverMorphism.ext ?_⟩
  rw [hψ]
  exact hl.symm

/- English proof (translation)
Introduce `p`. Establish `hq : Function.Surjective q.toRingHom` using `fun c => ⟨algebraMap k Q c, q.commutes c⟩`. Set `p' : PrimeSpectrum Q` to `p`. Use `haveI := p'.isPrime`. Establish `hker : RingHom.ker q.toRingHom ≤ p'.asIdeal` using `p'.isPrime.le_of_pow_le (n := j + 1) (le_of_eq_of_le hj bot_le)`.

Establish `hprime : (p'.asIdeal.map q.toRingHom).IsPrime` using `Ideal.map_isPrime_of_surjective hq hker`. Use `⟨(⟨p'.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum k), ?_⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap q.toRingHom (Ideal.map q.toRingHom p'.asIdeal) = p'.asIdeal`. Rewrite using `[Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]`.
-/
theorem surjective_spMap_aug {k Q : Type} [Field k] [CommRing Q] [Algebra k Q] (q : Q →ₐ[k] k) (j : ℕ)
    (hj : RingHom.ker q ^ (j + 1) = ⊥) : Function.Surjective (Chart.spMap q).left := by
  intro p
  have hq : Function.Surjective q.toRingHom := fun c => ⟨algebraMap k Q c, q.commutes c⟩
  let p' : PrimeSpectrum Q := p
  haveI := p'.isPrime
  have hker : RingHom.ker q.toRingHom ≤ p'.asIdeal :=
    p'.isPrime.le_of_pow_le (n := j + 1) (le_of_eq_of_le hj bot_le)
  have hprime : (p'.asIdeal.map q.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨(⟨p'.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum k), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q.toRingHom (Ideal.map q.toRingHom p'.asIdeal) = p'.asIdeal
  rw [Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]

open NatFun in

/- English proof (translation)
Introduce `k _ K _ hfin e`. Set `o : (Chart.sp (R₀` to `k) k).left := (⊥ : PrimeSpectrum k)`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `K.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e.left o)) isOpen_univ`. Express the relevant statement in the definitionally equal form `IsAffineOpen U at hU`. Set `v : Chart.sp (R₀` to `k) Γ(K.left, U) ⟶ K := affinePoint hU`.

Use `haveI : IsOpenImmersion v.left := hU.isOpenImmersion_fromSpec`. Use `haveI : Mono v := Over.mono_of_mono_left v`. Establish `hinj : ∀ (Q : Type) [CommRing Q] [Algebra k Q], Function.Injective fun f : Γ(K.left, U) →ₐ[k] Q => Chart.spMap f ≫ v`. Introduce `Q _ _ f g h`. Conclude with `spMap_injective ((cancel_mono v).1 h)`.

Establish `hft : Algebra.FiniteType k Γ(K.left, U)`. Establish `h : LocallyOfFiniteType (v.left ≫ K.hom)` using `inferInstance`. Rewrite `h` using `[Over.w v]`. Establish `h2` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h`. Conclude with `RingHom.finiteType_algebraMap.1 h2`.

Use `haveI : Finite (Chart.sp (R₀ := k) (AlgebraicClosure k) ⟶ K) := hfin _ _`. Use `haveI : Finite (Γ(K.left, U) →ₐ[k] AlgebraicClosure k) := Finite.of_injective _ (hinj _)`. Use `haveI := isArtinianRing_of_finite_points k Γ(K.left, U)`. Establish `he : Set.range e.left ⊆ Set.range v.left`. Introduce and unpack `_ ⟨y, rfl⟩`.

Establish `: y = o` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[this]`. Conclude with `hU.range_fromSpec.superset hxU`. Take `⟨e₀, he₀⟩` from `exists_factor e v he`. Take `⟨A, _, _, aug, M, π, h1, h2, h3⟩` from `exists_thickening e₀`.

Use `⟨A, _, _, aug, M, Chart.spMap π ≫ v, h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, Chart.spMap_comp, h2, he₀]`. Introduce `Q _ _ augQ j hj z hz`. Establish `hzr : Set.range z.left ⊆ Set.range v.left`. Introduce and unpack `_ ⟨y, rfl⟩`.

Take `⟨y', rfl⟩` from `surjective_spMap_aug augQ j hj y`. Apply `he` to reduce the goal to its premises. Conclude with `⟨y', by rw [← hz]; rfl⟩`. Take `⟨z₀, rfl⟩` from `exists_factor z v hzr`. Rewrite `hz` using `[← Category.assoc, Chart.spMap_comp, he₀]`.

Take `⟨a, ha, rfl⟩` from `h3 Q augQ j hj z₀ (hinj _ hz)`. Conclude with `⟨a, ha, by rw [← Category.assoc, Chart.spMap_comp]⟩`.
-/
theorem exists_universal_thickening : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  intro k _ K _ hfin e
  let o : (Chart.sp (R₀ := k) k).left := (⊥ : PrimeSpectrum k)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := K.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e.left o)) isOpen_univ
  change IsAffineOpen U at hU
  let v : Chart.sp (R₀ := k) Γ(K.left, U) ⟶ K := affinePoint hU
  haveI : IsOpenImmersion v.left := hU.isOpenImmersion_fromSpec
  haveI : Mono v := Over.mono_of_mono_left v
  have hinj : ∀ (Q : Type) [CommRing Q] [Algebra k Q],
      Function.Injective fun f : Γ(K.left, U) →ₐ[k] Q => Chart.spMap f ≫ v := by
    intro Q _ _ f g h
    exact spMap_injective ((cancel_mono v).1 h)
  have hft : Algebra.FiniteType k Γ(K.left, U) := by
    have h : LocallyOfFiniteType (v.left ≫ K.hom) := inferInstance
    rw [Over.w v] at h
    have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
    exact RingHom.finiteType_algebraMap.1 h2
  haveI : Finite (Chart.sp (R₀ := k) (AlgebraicClosure k) ⟶ K) := hfin _ _
  haveI : Finite (Γ(K.left, U) →ₐ[k] AlgebraicClosure k) := Finite.of_injective _ (hinj _)
  haveI := isArtinianRing_of_finite_points k Γ(K.left, U)
  have he : Set.range e.left ⊆ Set.range v.left := by
    rintro _ ⟨y, rfl⟩
    have : y = o := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hU.range_fromSpec.superset hxU
  obtain ⟨e₀, he₀⟩ := exists_factor e v he
  obtain ⟨A, _, _, aug, M, π, h1, h2, h3⟩ := exists_thickening e₀
  refine ⟨A, _, _, aug, M, Chart.spMap π ≫ v, h1, ?_, ?_⟩
  · rw [← Category.assoc, Chart.spMap_comp, h2, he₀]
  · intro Q _ _ augQ j hj z hz
    have hzr : Set.range z.left ⊆ Set.range v.left := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', rfl⟩ := surjective_spMap_aug augQ j hj y
      apply he
      exact ⟨y', by rw [← hz]; rfl⟩
    obtain ⟨z₀, rfl⟩ := exists_factor z v hzr
    rw [← Category.assoc, Chart.spMap_comp, he₀] at hz
    obtain ⟨a, ha, rfl⟩ := h3 Q augQ j hj z₀ (hinj _ hz)
    exact ⟨a, ha, by rw [← Category.assoc, Chart.spMap_comp]⟩

end GlobalTheory.IsolPt
