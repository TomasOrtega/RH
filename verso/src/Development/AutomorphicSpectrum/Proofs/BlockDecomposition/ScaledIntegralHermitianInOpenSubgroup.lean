import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

/- English proof (translation)
Establish `hal : IsAlgebraic ℤ y` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)`. Take `⟨z, hz, hint⟩` from `hal.exists_integral_multiple`. Use `⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩` and prove the remaining obligations. Establish `hint' : IsIntegral ℤ ((z.natAbs : F) * y)`. Break down `Int.natAbs_eq z with h | h` into its components or cases.

Establish `: ((z.natAbs : F) * y) = z • y`. Rewrite using `[zsmul_eq_mul]`. Use `congr 1`. Use `conv_rhs => rw [h]`. Simplify using the standard rewrite rules.

Rewrite using `[this]` and apply the resulting hypothesis. Establish `: ((z.natAbs : F) * y) = -(z • y)`. Rewrite using `[zsmul_eq_mul, ← neg_mul]`. Use `congr 1`. Use `conv_rhs => rw [h]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hint.neg`. Conclude with `⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩`.
-/
theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

/- English proof (translation)
Use `choose D hD r hr using fun i => exists_den (y i)`. Use `⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `Finset.dvd_prod_of_mem D (Finset.mem_univ i)`. Use `⟨(m : 𝓞 F) * r i, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, map_mul, hr, map_natCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

/- English proof (translation)
Set `e` to `RingOfIntegers.basis E`. Take `⟨D, hD, h⟩` from `exists_common_den (F := F) (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)`. Use `⟨D, hD, fun o k => ?_⟩` and prove the remaining obligations. Use `choose r hr using h`. Use `⟨∑ i, (e.repr o i) • r (i, k), ?_⟩` and prove the remaining obligations.

Establish `ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i)` using `by conv_lhs => rw [← e.sum_repr o]`. Simplify using `[map_sum]`. Rewrite using `[ho, map_sum, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]`.

Simplify using `only [zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]
    simp [map_sum]
  rw [ho, map_sum, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

/- English proof (translation)
Rewrite `hW` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, t, ht, hsub⟩` from `hW`. Use `⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩` and prove the remaining obligations. Introduce `i _`. Conclude with `Set.mem_iInter.mp (hy i) i`.
-/
theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n U hU t ht`. Take `⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Use `haveI : SecondCountableTopology (Af F) := hSC`. Use `haveI : T2Space (Af F) := hT2`. Use `haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1`.

Take `⟨-, -, -, -, -, -, hH, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)`. Set `b` to `Module.finBasis F E`. Establish `hh` using `hH _ b`. Use `set h := hh.homeomorph with hdef`. Establish `happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k` using `fun _ _ => rfl`.

Take `⟨U', hU'o, hU'⟩` from `isOpen_induced_iff.mp hU`. Set `G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E)` to `fun x a c => h.symm (fun k => x (a, c, k))`. Establish `hG : Continuous G`. Use `continuous_matrix fun a c => ?_` and prove the remaining obligations. Conclude with `h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)`.

Establish `hG0 : G (fun _ => 0) = 0`. Use extensionality with `a c`. Apply `h.injective` to reduce the goal to its premises. Use `show h (h.symm _) = h 0`. Rewrite using `[h.apply_symm_apply]`.

Use function extensionality and compare the values at `k`. Rewrite using `[happ]`. Simplify using the standard rewrite rules. Establish `h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U'`. Establish `h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n))` using `U.zero_mem`.

Rewrite `h1` using `[← hU']`. Conclude with `h1`. Establish `hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F))` using `(hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)`. Take `⟨V, hV, hVW⟩` from `nhds_unif _ _ hW`. Take `⟨N, hNpos, hNV⟩` from `hN V hV`.

Take `⟨D₁, hD₁, p, hp⟩` from `exists_den (t⁻¹)`. Take `⟨D₂, hD₂, hco⟩` from `coords_den b`. Use `⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩` and prove the remaining obligations. Set `y : Fin n × Fin n × Fin (Module.finrank F E) → Af F` to `fun q => algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)`. Establish `hy : ∀ q, y q ∈ V`.

Introduce and unpack `⟨a, a', k⟩`. Take `⟨o, ho⟩` from `hc a a'`. Take `⟨r, hr⟩` from `hco o k`. Establish `hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r)`. Establish `: (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o`.

Rewrite using `[ho]`. Both sides reduce to the same expression. Rewrite using `[this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F` using `(hF _).mpr ⟨p * r, by simp⟩`. Use `hNV _ hmem` as an intermediate fact. Use `show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V`. Rewrite using `[hval, map_mul, map_natCast]`. Conclude with `this`.

Establish `hGy : G y ∈ U'` using `hVW y hy`. Establish `heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1`. Use extensionality with `a a'`. Apply `h.injective` to reduce the goal to its premises. Use `show h (h.symm _) = _`.

Rewrite using `[h.apply_symm_apply]`. Use function extensionality and compare the values at `k`. Rewrite using `[happ]`. Use `show y (a, a', k) = _`. Apply the tactic sequence `have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' = (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl`.

Rewrite using `[hentry, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]`. Both sides reduce to the same expression. Establish `hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n))`. Rewrite using `[← hU']`.

Use `show _ ∈ U'`. Rewrite using `[← heq]`. Conclude with `hGy`. Conclude with `hfin`.
-/
theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
