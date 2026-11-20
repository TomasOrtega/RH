import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsOrthGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, z, hz, hzy⟩`. Establish `ht0 : t ≠ 0` using `fun h0 => ht (h0 ▸ 𝔭.zero_mem)`.

Establish `hne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0`. Establish `e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F)` using `rfl`. Rewrite using `[e, map_ne_zero]`. Conclude with `fun h => ht0 (by exact_mod_cast h)`. Establish `hmem : algebraMap (𝓞 F) (𝓞 K) t • y ∈ X`.

Rewrite using `[← hzy]`. Conclude with `z.2`. Rewrite `hmem` using `[← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y]`. Establish `hyX : y ∈ X` using `(X.smul_mem_iff hne).mp hmem`. Use `⟨⟨y, hyX⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Establish `e2 : algebraMap (𝓞 F) (𝓞 K) t • (⟨y, hyX⟩ : X) = z`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hzy.symm`.

Rewrite using `[e2]`. Conclude with `hz`. Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite `hz` using `[Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]`. Take `⟨t, ht, hz⟩` from `hz`.

Conclude with `⟨t, ht, _, hz, by simp⟩`.
-/
theorem locF_map_subtype (X : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) X) :
    locF 𝔭 (N.map (X.subtype.restrictScalars (𝓞 K))) =
      (locF 𝔭 N).map (X.subtype.restrictScalars (𝓞 K)) := by
  ext y
  rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF, Submodule.mem_map]
  constructor
  · rintro ⟨t, ht, z, hz, hzy⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
      rw [e, map_ne_zero]
      exact fun h => ht0 (by exact_mod_cast h)
    have hmem : algebraMap (𝓞 F) (𝓞 K) t • y ∈ X := by
      rw [← hzy]; exact z.2
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y] at hmem
    have hyX : y ∈ X := (X.smul_mem_iff hne).mp hmem
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
    refine ⟨t, ht, ?_⟩
    have e2 : algebraMap (𝓞 F) (𝓞 K) t • (⟨y, hyX⟩ : X) = z := by
      apply Subtype.ext
      simpa using hzy.symm
    rw [e2]; exact hz
  · rintro ⟨z, hz, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF] at hz
    obtain ⟨t, ht, hz⟩ := hz
    exact ⟨t, ht, _, hz, by simp⟩

variable [FiniteDimensional K V]

/- English proof (translation)
Use `haveI : 𝔭.IsPrime := h𝔭.isPrime`. Take `⟨hfg, hspan⟩` from `hL`. Establish `hLX : ∀ v ∈ L, v ∈ X` using `fun v hv => hspan ▸ Submodule.subset_span hv`. Establish `hmapN : (L.comap (X.subtype.restrictScalars (𝓞 K))).map (X.subtype.restrictScalars (𝓞 K)) = L`. Rewrite using `[Submodule.map_comap_eq]`.

Use `inf_eq_right.mpr ?_` and prove the remaining obligations. Introduce `v hv`. Conclude with `⟨⟨v, hLX v hv⟩, rfl⟩`. Establish `hinj : Function.Injective (X.subtype.restrictScalars (𝓞 K))` using `X.injective_subtype`. Establish `hfgN : (L.comap (X.subtype.restrictScalars (𝓞 K))).FG` using `Submodule.fg_of_fg_map_injective _ hinj (by rw [hmapN]; exact hfg)`.

Establish `himg : X.subtype '' ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X) = (L : Set V)`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `hw`.

Introduce `hv`. Conclude with `⟨⟨v, hLX v hv⟩, hv, rfl⟩`. Establish `hspanN : Submodule.span K ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X) = ⊤`. Apply `Submodule.map_injective_of_injective X.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, himg, hspan, Submodule.map_top, Submodule.range_subtype]`.

Establish `hNlat : Submodule.IsLattice K (L.comap (X.subtype.restrictScalars (𝓞 K)))` using `⟨hfgN, hspanN⟩`. Take `⟨b, hbN, hbloc⟩` from `Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hNlat h𝔭`. Use `⟨fun i => (b i : V), fun i => hbN i, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `b.linearIndependent.map' X.subtype X.ker_subtype`. Establish `hx : Set.range (fun i => (b i : V)) = X.subtype '' Set.range b` using `Set.range_comp _ _`.

Rewrite using `[hx, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hx : Set.range (fun i => (b i : V)) = (X.subtype.restrictScalars (𝓞 K)) '' Set.range b` using `Set.range_comp _ _`. Rewrite using `[hx, Submodule.span_image, locF_map_subtype, hbloc, ← locF_map_subtype, hmapN]`.
-/
theorem exists_basis_in {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : Cnt.IsLatIn X L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ x : Fin (finrank K X) → V, (∀ i, x i ∈ L) ∧ LinearIndependent K x ∧
      Submodule.span K (Set.range x) = X ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range x)) = locF 𝔭 L := by
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hfg, hspan⟩ := hL
  have hLX : ∀ v ∈ L, v ∈ X := fun v hv => hspan ▸ Submodule.subset_span hv
  have hmapN : (L.comap (X.subtype.restrictScalars (𝓞 K))).map
      (X.subtype.restrictScalars (𝓞 K)) = L := by
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.mpr ?_
    intro v hv
    exact ⟨⟨v, hLX v hv⟩, rfl⟩
  have hinj : Function.Injective (X.subtype.restrictScalars (𝓞 K)) := X.injective_subtype
  have hfgN : (L.comap (X.subtype.restrictScalars (𝓞 K))).FG :=
    Submodule.fg_of_fg_map_injective _ hinj (by rw [hmapN]; exact hfg)
  have himg : X.subtype '' ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X)
      = (L : Set V) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hLX v hv⟩, hv, rfl⟩
  have hspanN : Submodule.span K
      ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X) = ⊤ := by
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [Submodule.map_span, himg, hspan, Submodule.map_top, Submodule.range_subtype]
  have hNlat : Submodule.IsLattice K (L.comap (X.subtype.restrictScalars (𝓞 K))) :=
    ⟨hfgN, hspanN⟩
  obtain ⟨b, hbN, hbloc⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hNlat h𝔭
  refine ⟨fun i => (b i : V), fun i => hbN i, ?_, ?_, ?_⟩
  · exact b.linearIndependent.map' X.subtype X.ker_subtype
  · have hx : Set.range (fun i => (b i : V)) = X.subtype '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  · have hx : Set.range (fun i => (b i : V)) =
        (X.subtype.restrictScalars (𝓞 K)) '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, locF_map_subtype, hbloc, ← locF_map_subtype, hmapN]

/- English proof (translation)
Introduce `hdet`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hdet`. Establish `hyX : (∑ i, star (c i) • x i) ∈ X`. Rewrite using `[← hsp]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `key : ∀ j, h (∑ i, star (c i) • x i) (x j) = 0`. Introduce `j`. Establish `hj` using `congrFun hc j`. Simplify using `only [Matrix.vecMul, dotProduct, U0.gram, Matrix.of_apply, Pi.zero_apply] at hj`. Simplify using `only [map_sum, map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `hj`. Establish `hall : ∀ z ∈ X, h (∑ i, star (c i) • x i) z = 0`. Introduce `z hz`. Rewrite `hz` using `[← hsp]`. Establish `hle : Submodule.span K (Set.range x) ≤ LinearMap.ker (h (∑ i, star (c i) • x i))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `key j`. Conclude with `hle hz`. Establish `hy0` using `hnd _ hyX hall`.

Establish `hcoef` using `Fintype.linearIndependent_iff.mp hli (fun i => star (c i)) hy0`. Apply `hc0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `using hcoef i`.
-/
theorem det_gram_ne_zero [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    (hnd : Cnt.NondegOn h X) {n : ℕ} {x : Fin n → V} (hli : LinearIndependent K x)
    (hsp : Submodule.span K (Set.range x) = X) : (U0.gram h x).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hyX : (∑ i, star (c i) • x i) ∈ X := by
    rw [← hsp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ j, h (∑ i, star (c i) • x i) (x j) = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, U0.gram, Matrix.of_apply, Pi.zero_apply] at hj
    simp only [map_sum, map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact hj
  have hall : ∀ z ∈ X, h (∑ i, star (c i) • x i) z = 0 := by
    intro z hz
    rw [← hsp] at hz
    have hle : Submodule.span K (Set.range x) ≤ LinearMap.ker (h (∑ i, star (c i) • x i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact key j
    exact hle hz
  have hy0 := hnd _ hyX hall
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i => star (c i)) hy0
  apply hc0
  funext i
  simpa using hcoef i

end Formalism.L2.SG.Pf.G1
