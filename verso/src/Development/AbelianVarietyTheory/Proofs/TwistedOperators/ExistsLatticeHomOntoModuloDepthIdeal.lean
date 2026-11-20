import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg`. Use `haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ`. Use `haveI : IsAddTorsionFree Λ := ⟨fun k hk a b h => Subtype.ext (IsAddTorsionFree.nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩`. Take `⟨r, x, hli, c, hc0, hcop, hspan⟩` from `GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN`. Use `set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'`.

Establish `hli' : LinearIndependent (𝓞 K) x'` using `hli.map' Λ.subtype (Submodule.ker_subtype Λ)`. Establish `hliK : LinearIndependent K x'` using `(LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'`. Establish `hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x')`. Introduce `w hw`. Establish `h` using `Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)`.

Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Establish `e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w`. Simplify using `[Submodule.coe_smul, algebraMap_smul]`. Rewrite `h` using `[e]`. Conclude with `h`.

Establish `hcK : (c : K) ≠ 0` using `by exact_mod_cast hc0`. Establish `hspanK : ⊤ ≤ Submodule.span K (Set.range x')`. Rewrite using `[← hΛ.span_eq_top, Submodule.span_le]`. Introduce `w hw`. Establish `h1` using `Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)`.

Establish `h2` using `Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hcK, one_smul]`. Then use the resulting hypothesis. Set `b0 : Module.Basis (Fin r) K (Fin n → K)` to `Module.Basis.mk hliK hspanK`. Establish `hr : r = n`. Use `Module.finrank_eq_card_basis b0` as an intermediate fact.

Simplify using `using this.symm`. Substitute `hr` using the available equality. Use `⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.mk_apply]`. Conclude with `(x i).2`.

Establish `: Set.range b0 = Set.range x'` using `by rw [Module.Basis.coe_mk]`. Rewrite using `[this]`. Conclude with `hmem w hw`.
-/
theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : IsAddTorsionFree Λ := ⟨fun k hk a b h => Subtype.ext
    (IsAddTorsionFree.nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

open Matrix in

/- English proof (translation)
Use `set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef`. Establish `hN0 : Ideal.absNorm 𝔪 ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hN : 2 ≤ N` using `by omega`. Establish `hNm : (N : 𝓞 K) ∈ 𝔪`. Rewrite using `[hNdef, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)`. Take `⟨b, hb, c, hc, hcb⟩` from `exists_basis_in_lattice Λ N hN`. Take `⟨b', hb', c', hc', hcb'⟩` from `exists_basis_in_lattice Λ' N hN`. Take `⟨u, v, huv⟩` from `hc.mul_left hc'`. Set `φ : (Fin n' → K) →ₗ[K] (Fin n → K)` to `b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0`.

Set `ψ : (Fin n → K) →ₗ[K] (Fin n' → K)` to `b.constr K fun i => b' (Fin.castLE hnn i)`. Establish `hφψ : φ ∘ₗ ψ = LinearMap.id`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `show φ (ψ (b i)) = b i`. Simplify using `only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]`.

Rewrite using `[dif_pos i.isLt]`. Establish `hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show φ (b' j) ∈ Λ`.

Simplify using `only [φ, Module.Basis.constr_basis]`. Use `split_ifs`. Conclude with `hb _`. Conclude with `Λ.zero_mem`. Establish `hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show ψ (b i) ∈ Λ'`. Simplify using `only [ψ, Module.Basis.constr_basis]`. Conclude with `hb' _`.

Use `⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_, LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]`. Establish `h1 : φ ((c' : K) • w) ∈ Λ` using `hφ (hcb' w hw)`. Establish `h2` using `Λ.smul_mem u h1`. Rewrite `h2` using `[← algebraMap_smul K u, map_smul, smul_smul]`.

Use `h2 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]`. Conclude with `hψ (hcb w hw)`.

Establish `: u * c * c' - 1 = -(v * (N : 𝓞 K))` using `by linear_combination huv`. Rewrite using `[this]`. Conclude with `neg_mem (Ideal.mul_mem_left _ _ hNm)`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id`.

Rewrite using `[LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_smul, LinearMap.toMatrix'_id]`.

Use `push_cast`. Rewrite using `[sub_smul, one_smul]`.
-/
theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsLattice K] [Λ'.IsLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dif_pos i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

/- English proof (translation)
Introduce `D _ T L μ0 _ sc G W M _ i hi`. Establish `h0` using `G.sp.P_is i hi.le`. Establish `h1` using `G.sp.P_is (i + 1) hi`. Use `haveI : (G.Λ (.core i)).IsLattice D.host.E := h0.sd.1`. Use `haveI : (G.Λ (.core (i + 1))).IsLattice D.host.E := h1.sd.1`.

Establish `e0 : (G.V (.core i)).rank = rankP D i` using `h0.rank`. Establish `e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1)` using `h1.rank`. Establish `hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank`. Rewrite using `[e0, e1]`. Unfold `rankP`.

Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _`. Take `⟨x, hx, y, hy, a, ha, hxy⟩` from `exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)`. Use `⟨x, hx, y, hy, ?_⟩` and prove the remaining obligations. Establish `h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈ homLat (G.Λ (.core i)) (G.Λ (.core i))` using `fun v hv => by simpa using hv`. Establish `e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E)`.

Rewrite using `[hxy]`. Conclude with `algebraMap_smul D.host.E a _`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul ha h1m`.
-/
theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsLattice D.host.E := h0.sd.1
  haveI : (G.Λ (.core (i + 1))).IsLattice D.host.E := h1.sd.1
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
