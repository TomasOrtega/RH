import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TensorProduct in

/- English proof (translation)
Introduce `R _ _ _ A _ _ _ A₀ x Sg hfg hdense hfib`. Use `haveI : Algebra.FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).1 hfg`. Use `haveI : Algebra.FiniteType A₀ A := Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A`. Take `⟨a, ha0, s, -, hli, hspan⟩` from `_root_.GlobalTheory.GenericFreeness.exists_hasBasisAway_quotient R A₀ A (M := A) (Submodule.span A₀ ({1} : Set A)) (Submodule.fg_span_singleton 1)`. Use `set P := (Submodule.span A₀ ({1} : Set A)).restrictScalars R with hPdef`.

Establish `hP : ∀ y, y ∈ P ↔ y ∈ A₀`. Introduce `y`. Rewrite using `[hPdef, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`.

Rewrite using `[Algebra.smul_def, _root_.mul_one]`. Conclude with `c.2`. Introduce `hy`. Conclude with `⟨⟨y, hy⟩, by rw [Algebra.smul_def, _root_.mul_one]; rfl⟩`. Take `⟨N, hN⟩` from `hspan x Submodule.mem_top`.

Take `⟨p, hp, v, hv, hpv⟩` from `Submodule.mem_sup.1 hN`. Take `⟨c, hcs, hcv⟩` from `Submodule.mem_span_set.1 hv`. Establish `hcoord : ∀ (K : Type) [Field K] [Algebra R K], algebraMap R K a ≠ 0 → ∀ j ∈ s, ∃ θ : A →ₗ[R] K, (∀ y ∈ P, θ y = 0) ∧ ∀ m ∈ s, θ m = if m = j then 1 else 0`. Introduce `K _ _ haK j hj`. Set `S` to `Submonoid.powers a`.

Set `f` to `LocalizedModule.mkLinearMap S (A ⧸ P)`. Establish `hli' : LinearIndependent R (fun i : s => P.mkQ (i : A))` using `hli`. Establish `hliₐ` using `hli'.of_isLocalizedModule (Localization S) S f`. Establish `hsp : ⊤ ≤ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A)))`. Introduce `z _`.

Take `⟨⟨q, t⟩, rfl⟩` from `IsLocalizedModule.mk'_surjective S f z`. Take `⟨y, rfl⟩` from `P.mkQ_surjective q`. Take `⟨n, hn⟩` from `hspan y Submodule.mem_top`. Take `⟨p', hp', w, hw, hpw⟩` from `Submodule.mem_sup.1 hn`. Establish `h1 : P.mkQ (a ^ n • y) ∈ Submodule.span R (Set.range fun i : s => P.mkQ (i : A))`.

Establish `hp0 : P.mkQ p' = 0` using `(Submodule.Quotient.mk_eq_zero P).2 hp'`. Rewrite using `[← hpw, map_add, hp0, zero_add]`. Use `Submodule.mem_map_of_mem (f := P.mkQ) hw` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, Set.image_eq_range]`. Then use the resulting hypothesis. Establish `h2 : f (P.mkQ (a ^ n • y)) ∈ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A)))`.

Use `Submodule.mem_map_of_mem (f := f) h1` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_le_restrictScalars R (Localization S) _ this`. Establish `hmemS : a ^ n * (t : R) ∈ S` using `S.mul_mem (Submonoid.pow_mem _ (Submonoid.mem_powers a) n) t.2`. Establish `hu : IsUnit (algebraMap R (Localization S) (a ^ n * t))` using `IsLocalization.map_units _ ⟨_, hmemS⟩`.

Establish `heq : (algebraMap R (Localization S) (a ^ n * t)) • IsLocalizedModule.mk' f (P.mkQ y) t = f (P.mkQ (a ^ n • y))`. Rewrite using `[algebraMap_smul, mul_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', map_smul, map_smul]`. Use `show IsLocalizedModule.mk' f (P.mkQ y) t ∈ _`. Rewrite using `[← inv_smul_smul hu.unit (IsLocalizedModule.mk' f (P.mkQ y) t)]`. Conclude with `Submodule.smul_of_tower_mem _ _ (by rw [Units.smul_def, IsUnit.unit_spec, heq]; exact h2)`.

Set `b` to `Module.Basis.mk hliₐ hsp`. Establish `hunit : ∀ y : S, IsUnit ((Algebra.ofId R K) y)`. Introduce and unpack `⟨y, k, rfl⟩`. Conclude with `IsUnit.mk0 _ (by rw [map_pow]; exact pow_ne_zero _ haK)`. Set `ψ : Localization S →ₐ[R] K` to `IsLocalization.liftAlgHom hunit`.

Use `⟨ψ.toLinearMap ∘ₗ ((b.coord ⟨j, hj⟩).restrictScalars R) ∘ₗ f ∘ₗ P.mkQ, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Simplify using `[(Submodule.Quotient.mk_eq_zero P).2 hy]`. Introduce `m hm`. Establish `hb : f (P.mkQ m) = b ⟨m, hm⟩` using `by simp [b]`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, hb, Module.Basis.coord_apply, Module.Basis.repr_self]`. Distinguish the cases in `hmj : m = j`. Substitute `hmj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, hmj, Ne.symm hmj]`.

Establish `hfibre : ∀ P' ∈ Sg, a ∉ P'.asIdeal → ∀ j ∈ s, c j ∈ P'.asIdeal`. Introduce `P' hP' haP j hj`. Take `⟨K, hK, hKa, hker, hmem⟩` from `hfib P' hP'`. Take `⟨z, hz⟩` from `(AlgHom.mem_range _).1 hmem`. Establish `haK : algebraMap R K a ≠ 0` using `fun h => haP (hker ▸ RingHom.mem_ker.2 h)`.

Take `⟨θ, hθP, hθs⟩` from `hcoord K haK j hj`. Set `Θ : K ⊗[R] A →ₗ[R] K` to `TensorProduct.lift ((LinearMap.mul R K).compl₂ θ)`. Establish `hΘ : ∀ k y, Θ (k ⊗ₜ y) = k * θ y` using `fun k y => rfl`. Establish `hΘ0' : ∀ w, Θ (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val w) = 0`. Introduce `w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k y`. Rewrite using `[Algebra.TensorProduct.map_tmul, hΘ, hθP (A₀.val y) ((hP _).2 y.2), mul_zero]`. Consider the case `add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]`.

Establish `hx : θ x = 0`. Establish `hΘ0` using `hΘ0' z`. Rewrite `hΘ0` using `[hz, hΘ, _root_.one_mul]`. Conclude with `hΘ0`. Distinguish the cases in `hjs : j ∈ c.support`.

Establish `hθv : θ v = c j • (1 : K)`. Rewrite using `[← hcv, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single j]`. Rewrite using `[map_smul, hθs j hj, if_pos rfl]`. Introduce `m hm hmj`. Rewrite using `[map_smul, hθs m (hcs hm), if_neg hmj, smul_zero]`.

Introduce `h`. Conclude with `absurd hjs h`. Establish `h0 : θ (a ^ N • x) = 0` using `by rw [map_smul, hx, smul_zero]`. Rewrite `h0` using `[← hpv, map_add, hθP p hp, zero_add, hθv, Algebra.smul_def, _root_.mul_one]`. Rewrite using `[← hker]`.

Conclude with `RingHom.mem_ker.2 h0`. Rewrite using `[Finsupp.notMem_support_iff.1 hjs]`. Conclude with `P'.asIdeal.zero_mem`. Establish `hc0 : c = 0`. Use extensionality with `j`.

Assume the negation of the conclusion as `hne`. Establish `hj : j ∈ s` using `hcs (Finsupp.mem_support_iff.2 hne)`. Establish `hsub : Sg ⊆ PrimeSpectrum.zeroLocus {c j * a}`. Introduce `P' hP'`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`.

Distinguish the cases in `haP : a ∈ P'.asIdeal`. Conclude with `P'.asIdeal.mul_mem_left _ haP`. Conclude with `P'.asIdeal.mul_mem_right _ (hfibre P' hP' haP j hj)`. Establish `huniv : PrimeSpectrum.zeroLocus {c j * a} = Set.univ` using `Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _))`. Rewrite `huniv` using `[PrimeSpectrum.zeroLocus_eq_univ_iff, Set.singleton_subset_iff]`.

Establish `hz : c j * a = 0` using `(mem_nilradical.1 huniv).eq_zero`. Conclude with `hne ((mul_eq_zero.1 hz).resolve_right ha0)`. Use `⟨a ^ N, pow_ne_zero _ ha0, (hP _).1 ?_⟩` and prove the remaining obligations. Establish `hv0 : v = 0` using `by rw [← hcv, hc0, Finsupp.sum_zero_index]`. Rewrite using `[← hpv, hv0, add_zero]`.

Conclude with `hp`.
-/
theorem _root_.GlobalTheory.exists_smul_mem_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : Type) [CommRing A]
      [Algebra R A] [Algebra.FiniteType R A] (A₀ : Subalgebra R A) (x : A)
      (Sg : Set (PrimeSpectrum R)), A₀.FG → Dense Sg →
      (∀ P ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
        RingHom.ker (algebraMap R K) = P.asIdeal ∧
        (1 ⊗ₜ[R] x : TensorProduct R K A) ∈
          (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val).range) →
      ∃ a : R, a ≠ 0 ∧ a • x ∈ A₀ := by
  intro R _ _ _ A _ _ _ A₀ x Sg hfg hdense hfib
  classical
  haveI : Algebra.FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).1 hfg
  haveI : Algebra.FiniteType A₀ A := Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A
  obtain ⟨a, ha0, s, -, hli, hspan⟩ := _root_.GlobalTheory.GenericFreeness.exists_hasBasisAway_quotient R A₀ A (M := A) (Submodule.span A₀ ({1} : Set A)) (Submodule.fg_span_singleton 1)
  set P := (Submodule.span A₀ ({1} : Set A)).restrictScalars R with hPdef
  have hP : ∀ y, y ∈ P ↔ y ∈ A₀ := by
    intro y
    rw [hPdef, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [Algebra.smul_def, _root_.mul_one]
      exact c.2
    · intro hy
      exact ⟨⟨y, hy⟩, by rw [Algebra.smul_def, _root_.mul_one]; rfl⟩
  obtain ⟨N, hN⟩ := hspan x Submodule.mem_top
  obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.1 hN
  obtain ⟨c, hcs, hcv⟩ := Submodule.mem_span_set.1 hv
  have hcoord : ∀ (K : Type) [Field K] [Algebra R K], algebraMap R K a ≠ 0 → ∀ j ∈ s,
      ∃ θ : A →ₗ[R] K, (∀ y ∈ P, θ y = 0) ∧ ∀ m ∈ s, θ m = if m = j then 1 else 0 := by
    intro K _ _ haK j hj
    let S := Submonoid.powers a
    let f := LocalizedModule.mkLinearMap S (A ⧸ P)
    have hli' : LinearIndependent R (fun i : s => P.mkQ (i : A)) := hli
    have hliₐ := hli'.of_isLocalizedModule (Localization S) S f
    have hsp : ⊤ ≤ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
      intro z _
      obtain ⟨⟨q, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective q
      obtain ⟨n, hn⟩ := hspan y Submodule.mem_top
      obtain ⟨p', hp', w, hw, hpw⟩ := Submodule.mem_sup.1 hn
      have h1 : P.mkQ (a ^ n • y) ∈ Submodule.span R (Set.range fun i : s => P.mkQ (i : A)) := by
        have hp0 : P.mkQ p' = 0 := (Submodule.Quotient.mk_eq_zero P).2 hp'
        rw [← hpw, map_add, hp0, zero_add]
        have := Submodule.mem_map_of_mem (f := P.mkQ) hw
        rwa [Submodule.map_span, Set.image_eq_range] at this
      have h2 : f (P.mkQ (a ^ n • y)) ∈ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
        have := Submodule.mem_map_of_mem (f := f) h1
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact Submodule.span_le_restrictScalars R (Localization S) _ this
      have hmemS : a ^ n * (t : R) ∈ S := S.mul_mem (Submonoid.pow_mem _ (Submonoid.mem_powers a) n) t.2
      have hu : IsUnit (algebraMap R (Localization S) (a ^ n * t)) := IsLocalization.map_units _ ⟨_, hmemS⟩
      have heq : (algebraMap R (Localization S) (a ^ n * t)) • IsLocalizedModule.mk' f (P.mkQ y) t = f (P.mkQ (a ^ n • y)) := by
        rw [algebraMap_smul, mul_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', map_smul, map_smul]
      show IsLocalizedModule.mk' f (P.mkQ y) t ∈ _
      rw [← inv_smul_smul hu.unit (IsLocalizedModule.mk' f (P.mkQ y) t)]
      exact Submodule.smul_of_tower_mem _ _ (by rw [Units.smul_def, IsUnit.unit_spec, heq]; exact h2)
    let b := Module.Basis.mk hliₐ hsp
    have hunit : ∀ y : S, IsUnit ((Algebra.ofId R K) y) := by
      rintro ⟨y, k, rfl⟩
      exact IsUnit.mk0 _ (by rw [map_pow]; exact pow_ne_zero _ haK)
    let ψ : Localization S →ₐ[R] K := IsLocalization.liftAlgHom hunit
    refine ⟨ψ.toLinearMap ∘ₗ ((b.coord ⟨j, hj⟩).restrictScalars R) ∘ₗ f ∘ₗ P.mkQ, ?_, ?_⟩
    · intro y hy
      simp [(Submodule.Quotient.mk_eq_zero P).2 hy]
    · intro m hm
      have hb : f (P.mkQ m) = b ⟨m, hm⟩ := by simp [b]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, hb, Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [Finsupp.single_apply, hmj, Ne.symm hmj]
  have hfibre : ∀ P' ∈ Sg, a ∉ P'.asIdeal → ∀ j ∈ s, c j ∈ P'.asIdeal := by
    intro P' hP' haP j hj
    obtain ⟨K, hK, hKa, hker, hmem⟩ := hfib P' hP'
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 hmem
    have haK : algebraMap R K a ≠ 0 := fun h => haP (hker ▸ RingHom.mem_ker.2 h)
    obtain ⟨θ, hθP, hθs⟩ := hcoord K haK j hj
    let Θ : K ⊗[R] A →ₗ[R] K := TensorProduct.lift ((LinearMap.mul R K).compl₂ θ)
    have hΘ : ∀ k y, Θ (k ⊗ₜ y) = k * θ y := fun k y => rfl
    have hΘ0' : ∀ w, Θ (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul k y =>
        rw [Algebra.TensorProduct.map_tmul, hΘ, hθP (A₀.val y) ((hP _).2 y.2), mul_zero]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]
    have hx : θ x = 0 := by
      have hΘ0 := hΘ0' z
      rw [hz, hΘ, _root_.one_mul] at hΘ0
      exact hΘ0
    by_cases hjs : j ∈ c.support
    · have hθv : θ v = c j • (1 : K) := by
        rw [← hcv, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single j]
        · rw [map_smul, hθs j hj, if_pos rfl]
        · intro m hm hmj
          rw [map_smul, hθs m (hcs hm), if_neg hmj, smul_zero]
        · intro h; exact absurd hjs h
      have h0 : θ (a ^ N • x) = 0 := by rw [map_smul, hx, smul_zero]
      rw [← hpv, map_add, hθP p hp, zero_add, hθv, Algebra.smul_def, _root_.mul_one] at h0
      rw [← hker]
      exact RingHom.mem_ker.2 h0
    · rw [Finsupp.notMem_support_iff.1 hjs]
      exact P'.asIdeal.zero_mem
  have hc0 : c = 0 := by
    ext j
    by_contra hne
    have hj : j ∈ s := hcs (Finsupp.mem_support_iff.2 hne)
    have hsub : Sg ⊆ PrimeSpectrum.zeroLocus {c j * a} := by
      intro P' hP'
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      by_cases haP : a ∈ P'.asIdeal
      · exact P'.asIdeal.mul_mem_left _ haP
      · exact P'.asIdeal.mul_mem_right _ (hfibre P' hP' haP j hj)
    have huniv : PrimeSpectrum.zeroLocus {c j * a} = Set.univ :=
      Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _))
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff, Set.singleton_subset_iff] at huniv
    have hz : c j * a = 0 := (mem_nilradical.1 huniv).eq_zero
    exact hne ((mul_eq_zero.1 hz).resolve_right ha0)
  refine ⟨a ^ N, pow_ne_zero _ ha0, (hP _).1 ?_⟩
  have hv0 : v = 0 := by rw [← hcv, hc0, Finsupp.sum_zero_index]
  rw [← hpv, hv0, add_zero]
  exact hp

end GlobalTheory
