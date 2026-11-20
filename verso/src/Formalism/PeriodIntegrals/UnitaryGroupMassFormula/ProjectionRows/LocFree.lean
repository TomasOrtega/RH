import Mathlib
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LatticeFinitelyGenerated

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain

def LocFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (Y : Submodule (𝓞 K) V), Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      Submodule.span K (Set.range b) = Submodule.span K (Y : Set V) ∧ (∀ i, b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ Submodule.span (𝓞 K) (Set.range b)

section Den

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨S, rfl⟩` from `hY`. Establish `hs : ∀ g : S, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (g : V) ∈ X` using `fun g => by`. Take `⟨s, hs, hx⟩` from `(mem_locP' w.asIdeal).1 (hYX (Submodule.subset_span g.2))`. Conclude with `⟨s, hs, hx⟩`. Use `choose s hsw hsX using hs`.

Establish `hT : (∏ g, s g) ∈ w.asIdeal.primeCompl` using `Submonoid.prod_mem _ fun g _ => hsw g`. Use `⟨∏ g, s g, hT, ?_⟩` and prove the remaining obligations. Establish `key : Submodule.span (𝓞 K) (S : Set V) ≤ X.comap ((∏ g, s g) • LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hx' : x ∈ S` using `Finset.mem_coe.1 hx`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]`. Conclude with `X.smul_mem _ (hsX ⟨x, hx'⟩)`. Introduce `y hy`.

Conclude with `key hy`.
-/
lemma den_of_locP {V : Type*} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {X Y : Submodule (𝓞 K) V} (hY : Y.FG) (hYX : Y ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X) :
    ∃ T : 𝓞 K, T ∉ w.asIdeal ∧ ∀ y ∈ Y, T • y ∈ X := by
  classical
  obtain ⟨S, rfl⟩ := hY
  have hs : ∀ g : S, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (g : V) ∈ X := fun g => by
    obtain ⟨s, hs, hx⟩ := (mem_locP' w.asIdeal).1 (hYX (Submodule.subset_span g.2))
    exact ⟨s, hs, hx⟩
  choose s hsw hsX using hs
  have hT : (∏ g, s g) ∈ w.asIdeal.primeCompl := Submonoid.prod_mem _ fun g _ => hsw g
  refine ⟨∏ g, s g, hT, ?_⟩
  have key : Submodule.span (𝓞 K) (S : Set V) ≤
      X.comap ((∏ g, s g) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    have hx' : x ∈ S := Finset.mem_coe.1 hx
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact X.smul_mem _ (hsX ⟨x, hx'⟩)
  intro y hy
  exact key hy

end Den

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ w Y hY`. Set `_ : StarRing K` to `starRingOfComm`. Take `⟨T, hT⟩` from `hY`. Take `⟨B, hBT, hBsp, hBli⟩` from `exists_linearIndependent K (T : Set V)`. Establish `hBfin : B.Finite` using `(T.finite_toSet).subset hBT`.

Use `hBfin.fintype` as an intermediate fact. Use `set r := Fintype.card B with hr`. Use `set eB := Fintype.equivFin B with heB`. Use `set v : Fin r → V := fun i => ((eB.symm i : B) : V) with hv`. Establish `hvli : LinearIndependent K v` using `hBli.comp _ eB.symm.injective`.

Establish `hvY : ∀ i, v i ∈ Y` using `fun i => hT ▸ Submodule.subset_span (hBT (eB.symm i).2)`. Establish `hrv : Set.range v = B`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `(eB.symm i).2`. Introduce `hx`. Conclude with `⟨eB ⟨x, hx⟩, by simp [hv]⟩`. Establish `hvsp : Submodule.span K (Set.range v) = Submodule.span K (Y : Set V)`. Rewrite using `[hrv, hBsp, ← hT, Submodule.span_span_of_tower]`.

Use `set f : (Fin r → K) →ₗ[K] V := combo v with hf`. Use `set fO : (Fin r → K) →ₗ[𝓞 K] V := f.restrictScalars (𝓞 K) with hfO`. Establish `hfinj : Function.Injective f`. Introduce `a b hab`. Establish `h2 : combo v (a - b) = 0`.

Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.2 hab`. Rewrite `h2` using `[combo_apply]`. Use `(Fintype.linearIndependent_iff.1 hvli) _ h2` as an intermediate fact. Use function extensionality and compare the values at `i`.

Conclude with `sub_eq_zero.1 (this i)`. Establish `hfsingle : ∀ i, f (Pi.single i 1) = v i`. Introduce `i`. Rewrite using `[hf, combo_apply]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]`.

Establish `hfmem : ∀ x, f x ∈ Submodule.span K (Set.range v)`. Introduce `x`. Rewrite using `[hf, combo_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hrange : ∀ y ∈ Submodule.span K (Set.range v), ∃ x, f x = y`.

Introduce `y hy`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hy`. Conclude with `⟨c, by rw [hf, combo_apply, hc]⟩`. Use `set Y' : Submodule (𝓞 K) (Fin r → K) := Y.comap fO with hY'`. Establish `hmapY : Y'.map fO = Y`.

Apply `le_antisymm (Submodule.map_comap_le _ _)` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx⟩` from `hrange y (by rw [hvsp]; exact Submodule.subset_span hy)`. Use `⟨x, ?_, hx⟩` and prove the remaining obligations. Use `show f x ∈ Y`.

Rewrite using `[hx]`. Conclude with `hy`. Establish `hY'fg : Y'.FG` using `Submodule.fg_of_fg_map_injective fO hfinj (by rw [hmapY]; exact ⟨T, hT⟩)`. Establish `hstd : ∀ i, (Pi.single i 1 : Fin r → K) ∈ Y'`. Introduce `i`.

Rewrite using `[hY', Submodule.mem_comap]`. Use `show f (Pi.single i 1) ∈ Y`. Rewrite using `[hfsingle]`. Conclude with `hvY i`. Establish `hY'sp : Submodule.span K (Y' : Set (Fin r → K)) = ⊤`.

Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Pi.basisFun_apply]`. Conclude with `Submodule.subset_span (hstd i)`. Establish `hlat : Submodule.IsLattice K Y'` using `⟨hY'fg, hY'sp⟩`.

Take `⟨g, hgli, hgloc⟩` from `Formalism.DivisionValues.semilocal_basis_exists K r Y' hlat w`. Establish `hgtop : Submodule.span K (Set.range g) = ⊤` using `Formalism.DivisionValues.idxChange_span_top hgli`. Use `set b0 : Fin r → V := fun i => f (g i) with hb0`. Establish `hb0li : LinearIndependent K b0` using `hgli.map' f (LinearMap.ker_eq_bot.2 hfinj)`. Establish `hb0sp : Submodule.span K (Set.range b0) = Submodule.span K (Y : Set V)`.

Rewrite using `[← hvsp]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hfmem (g i)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h1 : (Pi.single i 1 : Fin r → K) ∈ Submodule.span K (Set.range g)`. Rewrite using `[hgtop]`. Conclude with `Submodule.mem_top`.

Establish `h2` using `Submodule.mem_map_of_mem (f := f) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp, hfsingle]`. Conclude with `h2`. Establish `hloc1 : ∀ x ∈ Submodule.span (𝓞 K) (Set.range g), ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y'`. Introduce `x hx`.

Establish `: x ∈ Formalism.HermitianLatticesTheory.loc (K` using `K) w.asIdeal Y' := by`. Rewrite using `[← hgloc]`. Conclude with `Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx`. Take `⟨s, hs, hsx⟩` from `this`. Conclude with `⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩`.

Establish `hloc2 : ∀ x ∈ Y', ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Submodule.span (𝓞 K) (Set.range g)`. Introduce `x hx`. Establish `: x ∈ Formalism.HermitianLatticesTheory.loc (K` using `K) w.asIdeal (Submodule.span (𝓞 K) (Set.range g)) := by`. Rewrite using `[hgloc]`. Conclude with `Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx`.

Take `⟨s, hs, hsx⟩` from `this`. Conclude with `⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩`. Establish `hb0loc : Submodule.span (𝓞 K) (Set.range b0) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal Y`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Take `⟨s, hs, hsx⟩` from `hloc1 (g i) (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `: fO (s • g i) ∈ Y` using `hsx`. Rewrite `this` using `[map_smul]`. Then use the resulting hypothesis. Take `⟨t, htw, htY⟩` from `den_of_locP w (Submodule.fg_span (Set.finite_range b0)) hb0loc`.

Establish `ht0 : algebraMap (𝓞 K) K t ≠ 0`. Introduce `h0`. Apply `htw` to reduce the goal to its premises. Establish `: t = 0` using `by simpa using h0`. Rewrite using `[this]`.

Conclude with `w.asIdeal.zero_mem`. Establish `e : (fun i => t • b0 i) = fun i => (algebraMap (𝓞 K) K t) • b0 i`. Use function extensionality and compare the values at `i`. Rewrite using `[algebraMap_smul]`. Use `⟨r, fun i => t • b0 i, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Fintype.linearIndependent_iff]`. Introduce `gg hgg i`. Establish `h3 : ∑ i, (gg i * algebraMap (𝓞 K) K t) • b0 i = 0`. Rewrite using `[← hgg]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [mul_smul]`.

Use `(Fintype.linearIndependent_iff.1 hb0li) _ h3 i` as an intermediate fact. Conclude with `(mul_eq_zero.1 this).resolve_right ht0`. Rewrite using `[e, ← hb0sp]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h4 : b0 i = (algebraMap (𝓞 K) K t)⁻¹ • ((algebraMap (𝓞 K) K t) • b0 i)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Rewrite using `[SetLike.mem_coe, h4]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `i`. Conclude with `htY _ (Submodule.subset_span ⟨i, rfl⟩)`.

Introduce `y hy`. Take `⟨x, hxY, rfl⟩` from `(by rw [hmapY]; exact hy : y ∈ Y'.map fO)`. Take `⟨s, hs, hsx⟩` from `hloc2 x hxY`. Use `⟨t * s, ?_, ?_⟩` and prove the remaining obligations. Introduce `hm`.

Break down `w.isPrime.mem_or_mem hm with h | h` into its components or cases. Conclude with `htw h`. Conclude with `hs h`. Establish `h1 : fO (s • x) ∈ (Submodule.span (𝓞 K) (Set.range g)).map fO` using `Submodule.mem_map_of_mem hsx`. Rewrite `h1` using `[Submodule.map_span, ← Set.range_comp]`.

Rewrite `h1` using `[map_smul]`. Rewrite using `[mul_smul]`. Establish `h2 : Submodule.span (𝓞 K) (Set.range (fO ∘ g)) ≤ (Submodule.span (𝓞 K) (Set.range fun i => t • b0 i)).comap (t • LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `h2 h1`.
-/
theorem lattice_locally_free : LocFree := by
  intro K _ _ V _ _ _ _ w Y hY
  let _ : StarRing K := starRingOfComm
  obtain ⟨T, hT⟩ := hY
  obtain ⟨B, hBT, hBsp, hBli⟩ := exists_linearIndependent K (T : Set V)
  have hBfin : B.Finite := (T.finite_toSet).subset hBT
  have := hBfin.fintype
  set r := Fintype.card B with hr
  set eB := Fintype.equivFin B with heB
  set v : Fin r → V := fun i => ((eB.symm i : B) : V) with hv
  have hvli : LinearIndependent K v := hBli.comp _ eB.symm.injective
  have hvY : ∀ i, v i ∈ Y := fun i => hT ▸ Submodule.subset_span (hBT (eB.symm i).2)
  have hrv : Set.range v = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eB.symm i).2
    · intro hx
      exact ⟨eB ⟨x, hx⟩, by simp [hv]⟩
  have hvsp : Submodule.span K (Set.range v) = Submodule.span K (Y : Set V) := by
    rw [hrv, hBsp, ← hT, Submodule.span_span_of_tower]
  set f : (Fin r → K) →ₗ[K] V := combo v with hf
  set fO : (Fin r → K) →ₗ[𝓞 K] V := f.restrictScalars (𝓞 K) with hfO
  have hfinj : Function.Injective f := by
    intro a b hab
    have h2 : combo v (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    rw [combo_apply] at h2
    have := (Fintype.linearIndependent_iff.1 hvli) _ h2
    funext i
    exact sub_eq_zero.1 (this i)
  have hfsingle : ∀ i, f (Pi.single i 1) = v i := by
    intro i
    rw [hf, combo_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  have hfmem : ∀ x, f x ∈ Submodule.span K (Set.range v) := by
    intro x
    rw [hf, combo_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : ∀ y ∈ Submodule.span K (Set.range v), ∃ x, f x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
    exact ⟨c, by rw [hf, combo_apply, hc]⟩
  set Y' : Submodule (𝓞 K) (Fin r → K) := Y.comap fO with hY'
  have hmapY : Y'.map fO = Y := by
    apply le_antisymm (Submodule.map_comap_le _ _)
    intro y hy
    obtain ⟨x, hx⟩ := hrange y (by rw [hvsp]; exact Submodule.subset_span hy)
    refine ⟨x, ?_, hx⟩
    show f x ∈ Y
    rw [hx]; exact hy
  have hY'fg : Y'.FG := Submodule.fg_of_fg_map_injective fO hfinj (by rw [hmapY]; exact ⟨T, hT⟩)
  have hstd : ∀ i, (Pi.single i 1 : Fin r → K) ∈ Y' := by
    intro i
    rw [hY', Submodule.mem_comap]
    show f (Pi.single i 1) ∈ Y
    rw [hfsingle]; exact hvY i
  have hY'sp : Submodule.span K (Y' : Set (Fin r → K)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hstd i)
  have hlat : Submodule.IsLattice K Y' := ⟨hY'fg, hY'sp⟩
  obtain ⟨g, hgli, hgloc⟩ := Formalism.DivisionValues.semilocal_basis_exists K r Y' hlat w
  have hgtop : Submodule.span K (Set.range g) = ⊤ := Formalism.DivisionValues.idxChange_span_top hgli

  set b0 : Fin r → V := fun i => f (g i) with hb0
  have hb0li : LinearIndependent K b0 := hgli.map' f (LinearMap.ker_eq_bot.2 hfinj)
  have hb0sp : Submodule.span K (Set.range b0) = Submodule.span K (Y : Set V) := by
    rw [← hvsp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hfmem (g i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : (Pi.single i 1 : Fin r → K) ∈ Submodule.span K (Set.range g) := by
        rw [hgtop]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := f) h1
      rw [Submodule.map_span, ← Set.range_comp, hfsingle] at h2
      exact h2
  have hloc1 : ∀ x ∈ Submodule.span (𝓞 K) (Set.range g),
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y' := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal Y' := by
      rw [← hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩
  have hloc2 : ∀ x ∈ Y', ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      s • x ∈ Submodule.span (𝓞 K) (Set.range g) := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range g)) := by
      rw [hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩

  have hb0loc : Submodule.span (𝓞 K) (Set.range b0) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal Y := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hloc1 (g i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨s, hs, ?_⟩
    have : fO (s • g i) ∈ Y := hsx
    rwa [map_smul] at this
  obtain ⟨t, htw, htY⟩ := den_of_locP w (Submodule.fg_span (Set.finite_range b0)) hb0loc
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    intro h0; apply htw
    have : t = 0 := by simpa using h0
    rw [this]; exact w.asIdeal.zero_mem
  have e : (fun i => t • b0 i) = fun i => (algebraMap (𝓞 K) K t) • b0 i := by
    funext i; rw [algebraMap_smul]
  refine ⟨r, fun i => t • b0 i, ?_, ?_, ?_, ?_⟩
  · rw [e, Fintype.linearIndependent_iff]
    intro gg hgg i
    have h3 : ∑ i, (gg i * algebraMap (𝓞 K) K t) • b0 i = 0 := by
      rw [← hgg]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]
    have := (Fintype.linearIndependent_iff.1 hb0li) _ h3 i
    exact (mul_eq_zero.1 this).resolve_right ht0
  · rw [e, ← hb0sp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h4 : b0 i = (algebraMap (𝓞 K) K t)⁻¹ • ((algebraMap (𝓞 K) K t) • b0 i) := by
        rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [SetLike.mem_coe, h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    exact htY _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro y hy
    obtain ⟨x, hxY, rfl⟩ := (by rw [hmapY]; exact hy : y ∈ Y'.map fO)
    obtain ⟨s, hs, hsx⟩ := hloc2 x hxY
    refine ⟨t * s, ?_, ?_⟩
    · intro hm
      rcases w.isPrime.mem_or_mem hm with h | h
      · exact htw h
      · exact hs h
    · have h1 : fO (s • x) ∈ (Submodule.span (𝓞 K) (Set.range g)).map fO :=
        Submodule.mem_map_of_mem hsx
      rw [Submodule.map_span, ← Set.range_comp] at h1
      rw [map_smul] at h1
      rw [mul_smul]
      have h2 : Submodule.span (𝓞 K) (Set.range (fO ∘ g)) ≤
          (Submodule.span (𝓞 K) (Set.range fun i => t • b0 i)).comap (t • LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact h2 h1

end PI.DvRows
