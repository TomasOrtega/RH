import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor

noncomputable section

namespace PI.Dv.ProjBW

open NumberField Formalism.HN

section Real

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realize_apply (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    Formalism.HermitianLatticesTheory.realize b X x p = if p.2.2 = 0 then (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re
      else (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := rfl

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Simplify using `only [realize_apply]`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_realize (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) =
      ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp only [realize_apply]
  simp [Complex.mul_re]
  ring

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_zero]`.
-/
theorem majAt_zero_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : Formalism.HermitianLatticesTheory.majAt b X v x 0 = 0 := by
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_zero]

end Real

section Zl

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_zl (ρ : V →+ E) (N : Submodule R V) (u : E) : u ∈ zl ρ N ↔ ∃ z ∈ N, ρ z = u := Iff.rfl

end Zl

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[← Module.End.mul_apply, he]`. Introduce `h`. Conclude with `⟨x, h⟩`.
-/
theorem mem_range_iff {V : Type} [AddCommGroup V] [Module K V] (e : Module.End K V) (he : e * e = e) (x : V) :
    x ∈ LinearMap.range e ↔ e x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Module.End.mul_apply, he]
  · intro h
    exact ⟨x, h⟩

/- English proof (translation)
Take `⟨hlat, hrk, -⟩` from `plLat K A.V A.ι A.b A.X hX M hM`. Establish `hr : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hsat` using `satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) (Formalism.HermitianLatticesTheory.realize A.b A.X) M hlat`. Establish `hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) M = deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M / ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))`. Establish `h1 : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize A.b A.X) M) = Module.finrank ℚ K * rkK M` using `hrk`.

Unfold `Formalism.HN.slope Formalism.F.slope`. Rewrite using `[h1]`. Use `push_cast`. Both sides reduce to the same expression. Unfold `PI.Dv.degL muDef`.

Distinguish the cases in `h0 : rkK M = 0`. Establish `hb : M = ⊥` using `(hsat.2.2.2.1 M le_rfl).1 (by rw [hrk, h0, mul_zero])`. Establish `hd : deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M = 0` using `by rw [hb]; exact hsat.2.2.2.2.1`. Rewrite using `[hs, h0, hd]`. Simplify using the standard rewrite rules.

Establish `h0' : (rkK M : ℝ) ≠ 0` using `by exact_mod_cast h0`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degL_eq (A : Formalism.BasicNotions.HLat K) (hX : ∀ v, IsUnit (A.X v).det) (M : Submodule (𝓞 K) A.V) (hM : M.FG) :
    PI.Dv.degL A M = 2 * deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M / (Module.finrank ℚ K : ℝ) +
      (- Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)) * (rkK M : ℝ) := by
  obtain ⟨hlat, hrk, -⟩ := plLat K A.V A.ι A.b A.X hX M hM
  have hr : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hsat := satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))
    (Formalism.HermitianLatticesTheory.realize A.b A.X) M hlat
  have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) M =
      deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M / ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) := by
    have h1 : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize A.b A.X) M) = Module.finrank ℚ K * rkK M := hrk
    unfold Formalism.HN.slope Formalism.F.slope
    rw [h1]
    push_cast
    rfl
  unfold PI.Dv.degL muDef
  by_cases h0 : rkK M = 0
  · have hb : M = ⊥ := (hsat.2.2.2.1 M le_rfl).1 (by rw [hrk, h0, mul_zero])
    have hd : deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M = 0 := by rw [hb]; exact hsat.2.2.2.2.1
    rw [hs, h0, hd]
    simp
  · have h0' : (rkK M : ℝ) ≠ 0 := by exact_mod_cast h0
    rw [hs]
    field_simp
    ring

/- English proof (translation)
Introduce `K _ _ _ _ A e n hP`. Take `⟨hG, hn, hee, hnL, hsa⟩` from `hP`. Take `⟨hX, hFG, hspan⟩` from `hG`. Use `set ρ := Formalism.HermitianLatticesTheory.realize A.b A.X with hρ`. Use `set L0 := PI.Dv.cutE A e A.L with hL0def`.

Use `set I := PI.Dv.imgE A (1 - e) A.L with hIdef`. Establish `hee' : ∀ y, e (e y) = e y` using `fun y => by rw [← Module.End.mul_apply, hee]`. Establish `hr : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hrN : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hn`.

Establish `hnoeth : IsNoetherian (𝓞 K) A.L` using `isNoetherian_of_fg_of_noetherian _ hFG`. Establish `hL0le : L0 ≤ A.L` using `inf_le_left`. Establish `hfg0 : L0.FG`. Establish `h1` using `(IsNoetherian.noetherian (L0.comap A.L.subtype)).map A.L.subtype`. Rewrite `h1` using `[Submodule.map_comap_subtype, inf_eq_right.2 hL0le]`. Then use the resulting hypothesis.

Establish `hfgI : I.FG` using `hFG.map _`. Take `⟨hlatL, hrkL, -⟩` from `plLat K A.V A.ι A.b A.X hX A.L hFG`. Take `⟨hlat0, hrk0, -⟩` from `plLat K A.V A.ι A.b A.X hX L0 hfg0`. Take `⟨hlatI, hrkI, -⟩` from `plLat K A.V A.ι A.b A.X hX I hfgI`. Establish `hL0eq : L0 = A.L ⊓ (LinearMap.ker (1 - e)).restrictScalars (𝓞 K)`.

Use extensionality with `x`. Simplify using `only [hL0def, PI.Dv.cutE, Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker, mem_range_iff e hee, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Apply the tactic sequence `constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩`. Establish `hsat0 : IsSat ρ A.L L0`. Rewrite using `[hL0eq]`.

Conclude with `(htImage K A.V A.ι A.V A.ι A.b A.X A.b A.X hX hX (1 - e) A.L hFG).1`. Establish `hrkKI : rkK I = PI.Dv.dimE A (1 - e)`. Unfold `rkK PI.Dv.dimE`. Establish `hIset : (I : Set A.V) = ((1 - e : Module.End K A.V) : A.V → A.V) '' (A.L : Set A.V)`. Rewrite using `[hIdef, PI.Dv.imgE, Submodule.map_coe, LinearMap.coe_restrictScalars]`.

Rewrite using `[hIset, Submodule.span_image, hspan, Submodule.map_top]`. Use `set S : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) := Submodule.span ℝ ((zl ρ L0 : Submodule ℤ _) : Set (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))) with hSdef`. Establish `hA : ∀ x ∈ A.L, ρ (e x) ∈ S`. Introduce `x hx`. Establish `hm : ((n : 𝓞 K)) • e x ∈ L0`.

Use `⟨hnL x hx, ?_⟩` and prove the remaining obligations. Use `show ((n : 𝓞 K)) • e x ∈ LinearMap.range e`. Rewrite using `[mem_range_iff e hee, LinearMap.map_smul_of_tower, hee']`. Establish `h1 : ρ (((n : 𝓞 K)) • e x) ∈ S` using `Submodule.subset_span ⟨_, hm, rfl⟩`. Rewrite `h1` using `[Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]`.

Establish `h2` using `S.smul_mem ((n : ℝ)⁻¹) h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hnR.ne', one_smul]`. Then use the resulting hypothesis. Establish `hB : ∀ x : A.V, ρ ((1 - e) x) ∈ Sᗮ`. Introduce `x`. Establish `hle : S ≤ (ℝ ∙ ρ ((1 - e) x))ᗮ`.

Rewrite using `[hSdef, Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]`. Establish `hz' : e z = z` using `(mem_range_iff e hee z).1 hz.2`. Rewrite using `[real_inner_comm, inner_realize]`.

Use `Finset.sum_eq_zero fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← hz', hsa, LinearMap.sub_apply, Module.End.one_apply, map_sub, hee', sub_self, majAt_zero_right]`. Simplify using the standard rewrite rules. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Use `hle hu` as an intermediate fact. Rewrite `this` using `[Submodule.mem_orthogonal_singleton_iff_inner_right]`. Rewrite using `[real_inner_comm]` and apply the resulting hypothesis. Establish `hproj : ∀ x ∈ A.L, Sᗮ.starProjection (ρ x) = ρ ((1 - e) x)`. Introduce `x hx`.

Establish `hsplit : ρ x = ρ (e x) + ρ ((1 - e) x)`. Rewrite using `[← map_add]`. Use `congr 1`. Simplify using `[LinearMap.sub_apply]`. Rewrite using `[hsplit, map_add, (Submodule.starProjection_apply_eq_zero_iff _).2 (Submodule.le_orthogonal_orthogonal S (hA x hx)), zero_add, Submodule.starProjection_eq_self_iff.2 (hB x)]`.

Establish `hq : Formalism.F.quot (zl ρ A.L) (zl ρ L0) = zl ρ I`. Use extensionality with `w`. Simplify using `only [Formalism.F.quot, Submodule.mem_map, mem_zl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`.

Use `⟨(1 - e) x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hproj x hx).symm`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨ρ x, ⟨x, hx, rfl⟩, hproj x hx⟩`. Establish `hsatL` using `satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ A.L hlatL`.

Establish `hq3` using `hsatL.2.2.2.2.2.2.2 L0 hsat0`. Rewrite `hq3` using `[hq]`. Take `⟨hrkq, hrkle, hdegq⟩` from `hq3`. Establish `hdeg : deg ρ I = deg ρ A.L - deg ρ L0` using `hdegq`. Establish `hrkq' : rk ρ I = rk ρ A.L - rk ρ L0` using `hrkq`.

Establish `hrkle' : rk ρ L0 ≤ rk ρ A.L` using `hrkle`. Establish `hsumZ : rk ρ I + rk ρ L0 = rk ρ A.L` using `by omega`. Establish `hsum : rkK I + rkK L0 = rkK A.L`. Rewrite `hsumZ` using `[hrkI, hrk0, hrkL, ← mul_add]`. Conclude with `Nat.eq_of_mul_eq_mul_left hrN hsumZ`.

Establish `hbound : deg ρ I ≤ (muMax ρ A.L + Real.log n) * ((Module.finrank ℚ K : ℝ) * (rkK I : ℝ))`. Distinguish the cases in `hI : I = ⊥`. Establish `h0 : rk ρ I = 0` using `(hsatL.2.2.2.1 I (by rw [hI]; exact bot_le)).2 hI`. Rewrite `h0` using `[hrkI]`. Establish `h0' : rkK I = 0`.

Break down `Nat.mul_eq_zero.1 h0 with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hd : deg ρ I = 0` using `by rw [hI]; exact hsatL.2.2.2.2.1`. Rewrite using `[hd, h0']`.

Simplify using the standard rewrite rules. Establish `hmem : ∀ x ∈ I, ((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)) x ∈ A.L`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_restrictScalars, LinearMap.sub_apply, Module.End.one_apply, smul_sub]`. Conclude with `A.L.sub_mem (A.L.smul_mem _ hy) (hnL y hy)`.

Set `φ : I →ₗ[𝓞 K] A.L` to `((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)).restrict hmem`. Establish `hφ : ∀ x : I, ((φ x : A.L) : A.V) = ((n : 𝓞 K)) • (x : A.V)` using `fun x => rfl`. Establish `hnorm : ∀ x : I, ‖ρ ((φ x : A.L) : A.V)‖ ≤ (n : ℝ) * ‖ρ (x : A.V)‖`. Introduce `x`. Use `le_of_eq ?_` and prove the remaining obligations.

Rewrite using `[hφ, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]`. Establish `hinj : Function.Injective φ`. Introduce `x y hxy`. Establish `h1` using `congrArg (fun z : A.L => (z : A.V)) hxy`. Simplify using `only [hφ] at h1`.

Rewrite `h1` using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]`. Conclude with `Subtype.ext ((smul_right_inj (Nat.cast_ne_zero.2 hn.ne')).1 h1)`. Establish `hmu` using `(slopeIneq (𝓞 K) A.V A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ ρ I A.L hlatI hlatL φ (n : ℝ) hnR hnorm).2 hinj hI`. Establish `hdI` using `((muChar (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ I hlatI hI).1 (muMax ρ I)).1 le_rfl I le_rfl`. Establish `hrkIR : (rk ρ I : ℝ) = (Module.finrank ℚ K : ℝ) * (rkK I : ℝ)`.

Rewrite using `[hrkI]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hdI` using `[hrkIR]`. Establish `hpos : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * (rkK I : ℝ)` using `by positivity`.

Conclude with `hdI.trans (mul_le_mul_of_nonneg_right hmu hpos)`. Unfold `PI.Dv.DegreeKernelLowerBound`. Rewrite using `[degL_eq A hX A.L hFG, degL_eq A hX L0 hfg0, ← hrkKI]`. Establish `hsumR : (rkK A.L : ℝ) = (rkK I : ℝ) + (rkK L0 : ℝ)` using `by exact_mod_cast hsum.symm`. Establish `key : 2 * deg ρ A.L / (Module.finrank ℚ K : ℝ) - 2 * deg ρ L0 / (Module.finrank ℚ K : ℝ) ≤ 2 * (rkK I : ℝ) * (muMax ρ A.L + Real.log n)`.

Rewrite using `[← sub_div, div_le_iff₀ hr]`. Use polynomial arithmetic with `[hbound, hdeg]`. Unfold `PI.Dv.muMaxL muMaxDef`. Rewrite using `[hsumR]`. Use polynomial arithmetic with `[key]`.
-/
theorem projB : PI.Dv.ProjB := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, hn, hee, hnL, hsa⟩ := hP
  obtain ⟨hX, hFG, hspan⟩ := hG

  set ρ := Formalism.HermitianLatticesTheory.realize A.b A.X with hρ
  set L0 := PI.Dv.cutE A e A.L with hL0def
  set I := PI.Dv.imgE A (1 - e) A.L with hIdef
  have hee' : ∀ y, e (e y) = e y := fun y => by rw [← Module.End.mul_apply, hee]
  have hr : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hrN : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn

  have hnoeth : IsNoetherian (𝓞 K) A.L := isNoetherian_of_fg_of_noetherian _ hFG
  have hL0le : L0 ≤ A.L := inf_le_left
  have hfg0 : L0.FG := by
    have h1 := (IsNoetherian.noetherian (L0.comap A.L.subtype)).map A.L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hL0le] at h1
  have hfgI : I.FG := hFG.map _
  obtain ⟨hlatL, hrkL, -⟩ := plLat K A.V A.ι A.b A.X hX A.L hFG
  obtain ⟨hlat0, hrk0, -⟩ := plLat K A.V A.ι A.b A.X hX L0 hfg0
  obtain ⟨hlatI, hrkI, -⟩ := plLat K A.V A.ι A.b A.X hX I hfgI

  have hL0eq : L0 = A.L ⊓ (LinearMap.ker (1 - e)).restrictScalars (𝓞 K) := by
    ext x
    simp only [hL0def, PI.Dv.cutE, Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker,
      mem_range_iff e hee, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
  have hsat0 : IsSat ρ A.L L0 := by
    rw [hL0eq]
    exact (htImage K A.V A.ι A.V A.ι A.b A.X A.b A.X hX hX (1 - e) A.L hFG).1

  have hrkKI : rkK I = PI.Dv.dimE A (1 - e) := by
    unfold rkK PI.Dv.dimE
    have hIset : (I : Set A.V) = ((1 - e : Module.End K A.V) : A.V → A.V) '' (A.L : Set A.V) := by
      rw [hIdef, PI.Dv.imgE, Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [hIset, Submodule.span_image, hspan, Submodule.map_top]

  set S : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :=
    Submodule.span ℝ ((zl ρ L0 : Submodule ℤ _) : Set (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)))
    with hSdef
  have hA : ∀ x ∈ A.L, ρ (e x) ∈ S := by
    intro x hx
    have hm : ((n : 𝓞 K)) • e x ∈ L0 := by
      refine ⟨hnL x hx, ?_⟩
      show ((n : 𝓞 K)) • e x ∈ LinearMap.range e
      rw [mem_range_iff e hee, LinearMap.map_smul_of_tower, hee']
    have h1 : ρ (((n : 𝓞 K)) • e x) ∈ S := Submodule.subset_span ⟨_, hm, rfl⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h1
    have h2 := S.smul_mem ((n : ℝ)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ hnR.ne', one_smul] at h2
  have hB : ∀ x : A.V, ρ ((1 - e) x) ∈ Sᗮ := by
    intro x
    have hle : S ≤ (ℝ ∙ ρ ((1 - e) x))ᗮ := by
      rw [hSdef, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      have hz' : e z = z := (mem_range_iff e hee z).1 hz.2
      rw [real_inner_comm, inner_realize]
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [← hz', hsa, LinearMap.sub_apply, Module.End.one_apply, map_sub, hee', sub_self, majAt_zero_right]
      simp
    rw [Submodule.mem_orthogonal]
    intro u hu
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    rwa [real_inner_comm]
  have hproj : ∀ x ∈ A.L, Sᗮ.starProjection (ρ x) = ρ ((1 - e) x) := by
    intro x hx
    have hsplit : ρ x = ρ (e x) + ρ ((1 - e) x) := by
      rw [← map_add]
      congr 1
      simp [LinearMap.sub_apply]
    rw [hsplit, map_add, (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.le_orthogonal_orthogonal S (hA x hx)), zero_add,
      Submodule.starProjection_eq_self_iff.2 (hB x)]
  have hq : Formalism.F.quot (zl ρ A.L) (zl ρ L0) = zl ρ I := by
    ext w
    simp only [Formalism.F.quot, Submodule.mem_map, mem_zl]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(1 - e) x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hproj x hx).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, hproj x hx⟩

  have hsatL := satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ A.L hlatL
  have hq3 := hsatL.2.2.2.2.2.2.2 L0 hsat0
  rw [hq] at hq3
  obtain ⟨hrkq, hrkle, hdegq⟩ := hq3
  have hdeg : deg ρ I = deg ρ A.L - deg ρ L0 := hdegq
  have hrkq' : rk ρ I = rk ρ A.L - rk ρ L0 := hrkq
  have hrkle' : rk ρ L0 ≤ rk ρ A.L := hrkle
  have hsumZ : rk ρ I + rk ρ L0 = rk ρ A.L := by omega
  have hsum : rkK I + rkK L0 = rkK A.L := by
    rw [hrkI, hrk0, hrkL, ← mul_add] at hsumZ
    exact Nat.eq_of_mul_eq_mul_left hrN hsumZ

  have hbound : deg ρ I ≤ (muMax ρ A.L + Real.log n) * ((Module.finrank ℚ K : ℝ) * (rkK I : ℝ)) := by
    by_cases hI : I = ⊥
    · have h0 : rk ρ I = 0 := (hsatL.2.2.2.1 I (by rw [hI]; exact bot_le)).2 hI
      rw [hrkI] at h0
      have h0' : rkK I = 0 := by
        rcases Nat.mul_eq_zero.1 h0 with h | h
        · omega
        · exact h
      have hd : deg ρ I = 0 := by rw [hI]; exact hsatL.2.2.2.2.1
      rw [hd, h0']
      simp
    · have hmem : ∀ x ∈ I, ((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)) x ∈ A.L := by
        rintro _ ⟨y, hy, rfl⟩
        simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_restrictScalars,
          LinearMap.sub_apply, Module.End.one_apply, smul_sub]
        exact A.L.sub_mem (A.L.smul_mem _ hy) (hnL y hy)
      let φ : I →ₗ[𝓞 K] A.L := ((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)).restrict hmem
      have hφ : ∀ x : I, ((φ x : A.L) : A.V) = ((n : 𝓞 K)) • (x : A.V) := fun x => rfl
      have hnorm : ∀ x : I, ‖ρ ((φ x : A.L) : A.V)‖ ≤ (n : ℝ) * ‖ρ (x : A.V)‖ := by
        intro x
        refine le_of_eq ?_
        rw [hφ, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
      have hinj : Function.Injective φ := by
        intro x y hxy
        have h1 := congrArg (fun z : A.L => (z : A.V)) hxy
        simp only [hφ] at h1
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K,
          ← Nat.cast_smul_eq_nsmul K] at h1
        exact Subtype.ext ((smul_right_inj (Nat.cast_ne_zero.2 hn.ne')).1 h1)
      have hmu := (slopeIneq (𝓞 K) A.V A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))
        (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ ρ I A.L hlatI hlatL φ (n : ℝ) hnR hnorm).2 hinj hI
      have hdI := ((muChar (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ I hlatI hI).1
        (muMax ρ I)).1 le_rfl I le_rfl
      have hrkIR : (rk ρ I : ℝ) = (Module.finrank ℚ K : ℝ) * (rkK I : ℝ) := by
        rw [hrkI]; push_cast; ring
      rw [hrkIR] at hdI
      have hpos : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * (rkK I : ℝ) := by positivity
      exact hdI.trans (mul_le_mul_of_nonneg_right hmu hpos)

  unfold PI.Dv.DegreeKernelLowerBound
  rw [degL_eq A hX A.L hFG, degL_eq A hX L0 hfg0, ← hrkKI]
  have hsumR : (rkK A.L : ℝ) = (rkK I : ℝ) + (rkK L0 : ℝ) := by exact_mod_cast hsum.symm
  have key : 2 * deg ρ A.L / (Module.finrank ℚ K : ℝ) - 2 * deg ρ L0 / (Module.finrank ℚ K : ℝ) ≤
      2 * (rkK I : ℝ) * (muMax ρ A.L + Real.log n) := by
    rw [← sub_div, div_le_iff₀ hr]
    nlinarith [hbound, hdeg]
  unfold PI.Dv.muMaxL muMaxDef
  rw [hsumR]
  nlinarith [key]

end Main

end PI.Dv.ProjBW
