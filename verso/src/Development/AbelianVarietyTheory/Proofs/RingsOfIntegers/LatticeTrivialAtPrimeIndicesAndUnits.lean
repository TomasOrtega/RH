import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemRangeOfIsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.LatticeIndex

namespace GlobalTheory.TrivLattice

/- English proof (translation)
Introduce `x`. Use `QuotientAddGroup.induction_on x (fun b => ?_)` and prove the remaining obligations. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, Nat.pos_of_ne_zero hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Simplify using `using h b b.2`.
-/
private theorem isAddTorsion_quotient_of_nsmul_mem {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : IsAddTorsion (B ⧸ A.addSubgroupOf B) := by
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using h b b.2

/- English proof (translation)
Use `haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (A.addSubgroupOf B))`. Use `haveI := AddCommGroup.finite_of_fg_isAddTorsion _ (isAddTorsion_quotient_of_nsmul_mem A B m hm h)`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_fg {G : Type} [AddCommGroup G] (A B : AddSubgroup G) [AddGroup.FG B] (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : A.relIndex B ≠ 0 := by
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (A.addSubgroupOf B))
  haveI := AddCommGroup.finite_of_fg_isAddTorsion _ (isAddTorsion_quotient_of_nsmul_mem A B m hm h)
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)`.
-/
theorem nsmul_mem_of_le {A B : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} (h : Ideal.span {(k : 𝓞 E)} • A ≤ B)
    {v : Fin n → E} (hv : v ∈ A) : k • v ∈ B := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)

/- English proof (translation)
Set `f : (Fin n → E) →ₗ[ℤ] (Fin n → E)` to `(k : ℤ) • LinearMap.id`. Establish `hf : Function.Injective f`. Introduce `x y hxy`. Establish `h0 : (k : ℤ) • (x - y) = 0`. Simplify using `only [f, LinearMap.smul_apply, LinearMap.id_apply] at hxy`.

Rewrite using `[smul_sub, hxy, sub_self]`. Break down `smul_eq_zero.1 h0 with h0 | h0` into its components or cases. Conclude with `absurd (by exact_mod_cast h0) hk`. Conclude with `sub_eq_zero.1 h0`. Set `T : Submodule ℤ (Fin n → E)` to `LinearMap.range ((GlobalTheory.LatticeIndex.incl E n).restrictScalars ℤ)`.

Establish `hT : T.FG`. Simplify using `only [T, LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Use `haveI := isNoetherian_of_fg_of_noetherian T hT`. Establish `hle : (A.restrictScalars ℤ).map f ≤ T`.

Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨u, hu⟩` from `GlobalTheory.LatticeIndex.mem_std.1 (h v hv)`. Use `⟨u, ?_⟩` and prove the remaining obligations. Simplify using `only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]`. Conclude with `hu`.

Establish `hA : (A.restrictScalars ℤ).FG` using `Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le_of_isNoetherian hle)`. Conclude with `(AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg _).1 hA)`.
-/
theorem fg_of_nsmul_mem (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : k ≠ 0) (h : ∀ v ∈ A, k • v ∈ stdLat E n) :
    AddGroup.FG A.toAddSubgroup := by
  let f : (Fin n → E) →ₗ[ℤ] (Fin n → E) := (k : ℤ) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h0 : (k : ℤ) • (x - y) = 0 := by
      simp only [f, LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [smul_sub, hxy, sub_self]
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact absurd (by exact_mod_cast h0) hk
    · exact sub_eq_zero.1 h0
  let T : Submodule ℤ (Fin n → E) := LinearMap.range ((GlobalTheory.LatticeIndex.incl E n).restrictScalars ℤ)
  have hT : T.FG := by
    simp only [T, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian T hT
  have hle : (A.restrictScalars ℤ).map f ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu⟩ := GlobalTheory.LatticeIndex.mem_std.1 (h v hv)
    refine ⟨u, ?_⟩
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]
    exact hu
  have hA : (A.restrictScalars ℤ).FG :=
    Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le_of_isNoetherian hle)
  exact (AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg _).1 hA)

/- English proof (translation)
Take `⟨hNodd, -, hNle⟩` from `hL`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hl.ne_one ((Nat.coprime_zero_left ℓ).1 hk)`. Establish `memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n` using `fun x => by`.

Unfold `GenLat.Ln`. Conclude with `Submodule.mem_inf`. Establish `hS : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup` using `fun x hx => hNle hx`. Establish `hLn : Λ.Ln.toAddSubgroup ≤ Λ.La.toAddSubgroup` using `fun x hx => ((memLn x).1 hx).1`. Use `haveI := fg_of_nsmul_mem Λ.La hk0 h1`.

Use `haveI := fg_of_nsmul_mem Λ.Ln one_ne_zero (fun v hv => by rw [one_smul]; exact ((memLn v).1 hv).2)`. Establish `hkLn : ∀ b ∈ Λ.La.toAddSubgroup, k • b ∈ Λ.Ln.toAddSubgroup` using `fun b hb => (memLn _).2 ⟨nsmul_mem hb k, h1 b hb⟩`. Establish `ha : Λ.Ln.toAddSubgroup.relIndex Λ.La.toAddSubgroup ≠ 0` using `relIndex_ne_zero_of_fg _ _ k hk0 hkLn`. Establish `hnd` using `GlobalTheory.LatticeIndex.not_dvd_relIndex _ _ k ℓ hl hk ha hkLn`. Establish `hb : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ≠ 0`.

Use `relIndex_ne_zero_of_fg _ _ N hNodd.pos.ne' (fun b hb => ?_)` and prove the remaining obligations. Use `show N • b ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ((memLn b).1 hb).2`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hS hLn`.

Express the relevant statement in the definitionally equal form `((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup ^ r).factorization ℓ = ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r).factorization ℓ ∧ (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddS …`. Use `⟨?_, pow_ne_zero _ hb⟩` and prove the remaining obligations. Rewrite using `[← hmul, mul_pow, Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ ha)]`. Simplify using `[Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]`.
-/
theorem index_part (Λ : GenLat E n) (N M ℓ k : ℕ) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (hk : Nat.Coprime k ℓ)
    (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n) (r : ℕ) :
    (Λ.zCard N r).factorization ℓ = (Λ.mIdx N r).factorization ℓ ∧ Λ.mIdx N r ≠ 0 := by
  obtain ⟨hNodd, -, hNle⟩ := hL
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hl.ne_one ((Nat.coprime_zero_left ℓ).1 hk)
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hS : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup := fun x hx => hNle hx
  have hLn : Λ.Ln.toAddSubgroup ≤ Λ.La.toAddSubgroup := fun x hx => ((memLn x).1 hx).1
  haveI := fg_of_nsmul_mem Λ.La hk0 h1
  haveI := fg_of_nsmul_mem Λ.Ln one_ne_zero (fun v hv => by rw [one_smul]; exact ((memLn v).1 hv).2)
  have hkLn : ∀ b ∈ Λ.La.toAddSubgroup, k • b ∈ Λ.Ln.toAddSubgroup := fun b hb =>
    (memLn _).2 ⟨nsmul_mem hb k, h1 b hb⟩
  have ha : Λ.Ln.toAddSubgroup.relIndex Λ.La.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero_of_fg _ _ k hk0 hkLn
  have hnd := GlobalTheory.LatticeIndex.not_dvd_relIndex _ _ k ℓ hl hk ha hkLn
  have hb : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ≠ 0 := by
    refine relIndex_ne_zero_of_fg _ _ N hNodd.pos.ne' (fun b hb => ?_)
    show N • b ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ((memLn b).1 hb).2
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hS hLn
  change ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup ^ r).factorization ℓ =
      ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r).factorization ℓ ∧
    (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r ≠ 0
  refine ⟨?_, pow_ne_zero _ hb⟩
  rw [← hmul, mul_pow, Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ ha)]
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `y ⟨v, hv, rfl⟩`. Establish `hc` using `GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := v) (u := fun i => k • v i) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])`. Take `⟨r, hr⟩` from `GlobalTheory.LatticeIndex.det_std (u := fun i => k • v i) (fun i => h1 _ (hv i))`. Rewrite `hc` using `[Matrix.det_one, _root_.one_mul, ← hr]`.

Establish `hwc` using `congrArg w hc`. Rewrite `hwc` using `[map_mul, map_pow, hk, one_pow, _root_.one_mul]`. Rewrite using `[hwc]`. Conclude with `hw r`. Use `⟨(k : E) ^ n, ⟨fun i => k • (Pi.single i 1 : Fin n → E), fun i => h2 _ (GlobalTheory.LatticeIndex.single_std i), ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hc` using `GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := fun i => (Pi.single i 1 : Fin n → E)) (u := fun i => k • (Pi.single i 1 : Fin n → E)) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]) beta_reduce at hc`. Rewrite `hc` using `[GlobalTheory.LatticeIndex.det_single, _root_.mul_one, Matrix.det_one, _root_.one_mul]`. Conclude with `hc`. Rewrite using `[map_pow, hk, one_pow]`.
-/
theorem detSet_max {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation E Γ)
    (hw : ∀ r : 𝓞 E, w (algebraMap (𝓞 E) E r) ≤ 1) (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : w (k : E) = 1)
    (h1 : ∀ v ∈ A, k • v ∈ stdLat E n) (h2 : ∀ v ∈ stdLat E n, k • v ∈ A) :
    (∀ y ∈ detSet A, w y ≤ 1) ∧ ∃ y ∈ detSet A, w y = 1 := by
  constructor
  · rintro y ⟨v, hv, rfl⟩
    have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := v)
      (u := fun i => k • v i) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
    obtain ⟨r, hr⟩ := GlobalTheory.LatticeIndex.det_std (u := fun i => k • v i) (fun i => h1 _ (hv i))
    rw [Matrix.det_one, _root_.one_mul, ← hr] at hc
    have hwc := congrArg w hc
    rw [map_mul, map_pow, hk, one_pow, _root_.one_mul] at hwc
    rw [hwc]
    exact hw r
  · refine ⟨(k : E) ^ n, ⟨fun i => k • (Pi.single i 1 : Fin n → E),
      fun i => h2 _ (GlobalTheory.LatticeIndex.single_std i), ?_⟩, ?_⟩
    · have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E))
        (v := fun i => (Pi.single i 1 : Fin n → E)) (u := fun i => k • (Pi.single i 1 : Fin n → E))
        (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
      beta_reduce at hc
      rw [GlobalTheory.LatticeIndex.det_single, _root_.mul_one, Matrix.det_one, _root_.one_mul] at hc
      exact hc
    · rw [map_pow, hk, one_pow]

/- English proof (translation)
Set `w : Valuation c.F (WithZero (Multiplicative ℤ))` to `v0.comap io`. Establish `hwR : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1` using `fun r => hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map io.toIntAlgHom)`. Establish `hA : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) → ∀ τ : E →+* ℂ, GlobalTheory.LatticeIndex.HasMax w (idealAt c A τ) 1`. Introduce `A hA1 hA2 τ`. Set `wτ : Valuation E (WithZero (Multiplicative ℤ))` to `w.comap (embF c τ)`.

Establish `hwE : ∀ r : 𝓞 E, wτ (algebraMap (𝓞 E) E r) ≤ 1` using `fun r => hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map (io.comp (embF c τ)).toIntAlgHom)`. Establish `hkE : wτ (k : E) = 1`. Simplify using `only [wτ, w, Valuation.comap_apply, map_natCast]`. Conclude with `hnat`. Establish `hm` using `detSet_max wτ hwE A hkE hA1 hA2`.

Unfold `idealAt`. Use `GlobalTheory.LatticeIndex.hasMax_span hwR ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Conclude with `hm.1 d hd`. Take `⟨d, hd, hd1⟩` from `hm.2`.

Conclude with `⟨_, ⟨d, hd, rfl⟩, hd1⟩`. Establish `hprod : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) → GlobalTheory.LatticeIndex.HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1`. Introduce `A hA1 hA2`. Use `GlobalTheory.LatticeIndex.hasMax_prod hwR Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) (fun τ => by simpa using (hA A hA1 hA2 τ).pow hwR (Dw.mult τ))` as an intermediate fact. Simplify using `using this`.

Establish `memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n` using `fun x => by`. Unfold `GenLat.Ln`. Conclude with `Submodule.mem_inf`. Establish `hLa` using `hprod Λ.La h1 h2`. Establish `hLn` using `hprod Λ.Ln (fun v hv => nsmul_mem ((memLn v).1 hv).2 k) (fun v hv => (memLn _).2 ⟨h2 v hv, nsmul_mem hv k⟩)`.

Establish `hβ : GlobalTheory.LatticeIndex.HasMax w (𝓞 c.F ∙ β) (w β)` using `GlobalTheory.LatticeIndex.hasMax_span hwR (by rintro y rfl; exact le_rfl) ⟨β, Set.mem_singleton β, rfl⟩`. Establish `hm` using `hβ.mul hLa`. Unfold `BetaIs at hB`. Rewrite `hm` using `[hB]`. Establish `hu` using `hm.unique hLn`.

Rewrite `hu` using `[_root_.mul_one]`. Conclude with `hu`.
-/
private theorem valuation_beta_of_lattice_commensurable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (k : ℕ) (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n)
    (h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La) {K : Type} [Field K] (io : c.F →+* K) (v0 : Valuation K (WithZero (Multiplicative ℤ)))
    (hint : ∀ x : K, IsIntegral ℤ x → v0 x ≤ 1) (hnat : v0 (k : K) = 1) (β : c.F)
    (hB : BetaIs (Dw := Dw) c Λ β) : v0 (io β) = 1 := by
  let w : Valuation c.F (WithZero (Multiplicative ℤ)) := v0.comap io
  have hwR : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r =>
    hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map io.toIntAlgHom)
  have hA : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      ∀ τ : E →+* ℂ, GlobalTheory.LatticeIndex.HasMax w (idealAt c A τ) 1 := by
    intro A hA1 hA2 τ
    let wτ : Valuation E (WithZero (Multiplicative ℤ)) := w.comap (embF c τ)
    have hwE : ∀ r : 𝓞 E, wτ (algebraMap (𝓞 E) E r) ≤ 1 := fun r =>
      hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map (io.comp (embF c τ)).toIntAlgHom)
    have hkE : wτ (k : E) = 1 := by
      simp only [wτ, w, Valuation.comap_apply, map_natCast]
      exact hnat
    have hm := detSet_max wτ hwE A hkE hA1 hA2
    unfold idealAt
    refine GlobalTheory.LatticeIndex.hasMax_span hwR ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hm.1 d hd
    · obtain ⟨d, hd, hd1⟩ := hm.2
      exact ⟨_, ⟨d, hd, rfl⟩, hd1⟩
  have hprod : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      GlobalTheory.LatticeIndex.HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := by
    intro A hA1 hA2
    have := GlobalTheory.LatticeIndex.hasMax_prod hwR Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1)
      (fun τ => by simpa using (hA A hA1 hA2 τ).pow hwR (Dw.mult τ))
    simpa using this
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hLa := hprod Λ.La h1 h2
  have hLn := hprod Λ.Ln (fun v hv => nsmul_mem ((memLn v).1 hv).2 k)
    (fun v hv => (memLn _).2 ⟨h2 v hv, nsmul_mem hv k⟩)
  have hβ : GlobalTheory.LatticeIndex.HasMax w (𝓞 c.F ∙ β) (w β) :=
    GlobalTheory.LatticeIndex.hasMax_span hwR (by rintro y rfl; exact le_rfl) ⟨β, Set.mem_singleton β, rfl⟩
  have hm := hβ.mul hLa
  unfold BetaIs at hB
  rw [hB] at hm
  have hu := hm.unique hLn
  rw [_root_.mul_one] at hu
  exact hu

end

/- English proof (translation)
Introduce `E _ _ _ H Dw l c n Λ N M ℓ _ hL hl hT`. Take `⟨k, hk, hk1, hk2⟩` from `hT`. Establish `h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n` using `fun v hv => nsmul_mem_of_le hk1 hv`. Establish `h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La` using `fun v hv => nsmul_mem_of_le hk2 hv`. Take `⟨hidx, hne⟩` from `index_part Λ N M ℓ k hL hl hk h1 (Dw.p + Dw.q)`.

Use `⟨hidx, hne, fun T io hlT => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `β _ hB`. Establish `key : valV T.V (io β) = 1`. Establish `hint : ∀ x : T.Fr, IsIntegral ℤ x → valV T.V x ≤ 1` using `fun x hx => GlobalTheory.LatticeIndex.valV_integral T hx`. Establish `hnat` using `GlobalTheory.LatticeIndex.valV_nat T hk hlT`.

Unfold `valV at hint hnat ⊢`. Use `valuation_beta_of_lattice_commensurable c Λ k h1 h2 io _ ?_ ?_ β hB` and prove the remaining obligations. Introduce `x hx`. Use `hint x ?_` and prove the remaining obligations. Use `hx` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `exact rfl`. Consider the case `exact Subsingleton.elim _ _`. Consider the case `(apply Algebra.algebra_ext; intro r; simp)`.

Use `first`. Consider the case `exact hnat`. Consider the case `convert hnat using 2`. Unfold `vV`. Rewrite using `[key]`.

Simplify using the standard rewrite rules. Introduce `w P hP`. Establish `hunit : IsUnit (k : T.V)`. Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 hk).map (Int.castRingHom T.V)`. Establish `hab' : a * (k : T.V) + b * (ℓ : T.V) = 1` using `by simpa using hab`.

Break down `IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h` into its components or cases. Conclude with `isUnit_of_mul_isUnit_right h`. Conclude with `absurd (isUnit_of_mul_isUnit_right h) hlT`. Establish `hunitary : ∀ i j : Fin n, ∑ b, IsCMField.complexConj E ((1 : Matrix (Fin n) (Fin n) E) b i) * (1 : Matrix (Fin n) (Fin n) E) b j = if i = j then 1 else 0`. Introduce `i j`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Matrix.one_apply]`. Introduce `b _ hb`. Simplify using `[Matrix.one_apply_ne hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Take `⟨hmem, hone, -⟩` from `GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io k 1 hunit hunitary (fun v hv => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]; exact h1 v hv)`. Rewrite `hmem` using `[hone]`. Then use the resulting hypothesis.
-/
theorem trivAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  intro E _ _ _ H Dw l c n Λ N M ℓ _ hL hl hT
  obtain ⟨k, hk, hk1, hk2⟩ := hT
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  obtain ⟨hidx, hne⟩ := index_part Λ N M ℓ k hL hl hk h1 (Dw.p + Dw.q)
  refine ⟨hidx, hne, fun T io hlT => ⟨?_, ?_⟩⟩
  · intro β _ hB
    have key : valV T.V (io β) = 1 := by
      have hint : ∀ x : T.Fr, IsIntegral ℤ x → valV T.V x ≤ 1 := fun x hx => GlobalTheory.LatticeIndex.valV_integral T hx
      have hnat := GlobalTheory.LatticeIndex.valV_nat T hk hlT
      unfold valV at hint hnat ⊢
      refine valuation_beta_of_lattice_commensurable c Λ k h1 h2 io _ ?_ ?_ β hB
      · intro x hx
        refine hint x ?_
        convert hx
        all_goals first
          | rfl
          | exact rfl
          | exact Subsingleton.elim _ _
          | (apply Algebra.algebra_ext; intro r; simp)
      · first
          | exact hnat
          | convert hnat using 2
    unfold vV
    rw [key]
    simp
  · intro w P hP
    have hunit : IsUnit (k : T.V) := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hk).map (Int.castRingHom T.V)
      have hab' : a * (k : T.V) + b * (ℓ : T.V) = 1 := by simpa using hab
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h
      · exact isUnit_of_mul_isUnit_right h
      · exact absurd (isUnit_of_mul_isUnit_right h) hlT
    have hunitary : ∀ i j : Fin n, ∑ b, IsCMField.complexConj E ((1 : Matrix (Fin n) (Fin n) E) b i) *
        (1 : Matrix (Fin n) (Fin n) E) b j = if i = j then 1 else 0 := by
      intro i j
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro b _ hb
        simp [Matrix.one_apply_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    obtain ⟨hmem, hone, -⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io k 1 hunit hunitary
      (fun v hv => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]; exact h1 v hv)
    rwa [hone] at hmem

end GlobalTheory.TrivLattice
