import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl

open Module NumberField IsDedekindDomain Pointwise

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.HN

section Scale

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `haveI : FiniteDimensional K V := Module.Finite.of_basis b`. Unfold `Formalism.HN.rkK`. Rewrite using `[Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]`. Introduce `h`. Apply `hM0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span K (M : Set V)` using `Submodule.subset_span hx`. Rewrite `hx'` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `hx'`.
-/
theorem rkK_pos (b : Basis ι K V) (M : Submodule (𝓞 K) V) (hM0 : M ≠ ⊥) : 0 < rkK M := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  unfold Formalism.HN.rkK
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  apply hM0
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (M : Set V) := Submodule.subset_span hx
  rw [h, Submodule.mem_bot] at hx'
  rw [Submodule.mem_bot]
  exact hx'

/- English proof (translation)
Establish `: FiniteDimensional K V` using `Module.Finite.of_basis b`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Establish `hfg : (𝔟 • M).FG` using `Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM`. Take `⟨hlatM, hrkM, -⟩` from `place_lattice_structure K V ι b X hX M hM`. Take `⟨hlatB, hrkB, -⟩` from `place_lattice_structure K V ι b X hX (𝔟 • M) hfg`.

Establish `hrkK : rkK (𝔟 • M) = rkK M`. Unfold `rkK`. Rewrite using `[DualPolygon.twist_span_smul M 𝔟 h𝔟]`. Establish `: DiscreteTopology (zl ρ M)` using `hlatM.2`. Establish `hle : zl ρ (𝔟 • M) ≤ zl ρ M` using `shiftInv_zl_mono ρ Submodule.smul_le_right`.

Establish `hrkeq : Formalism.F.rk (zl ρ (𝔟 • M)) = Formalism.F.rk (zl ρ M)`. Establish `h1 : Formalism.HN.rk ρ (𝔟 • M) = Formalism.HN.rk ρ M` using `by rw [hrkM, hrkB, hrkK]`. Conclude with `h1`. Establish `hcov` using `Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (zl ρ (𝔟 • M)) (zl ρ M) hle hrkeq`. Establish `hinj` using `Formalism.HN.PlaceLattice.realize_injective b X hX`.

Establish `hidx : (zl ρ (𝔟 • M)).toAddSubgroup.relIndex (zl ρ M).toAddSubgroup = (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup`. Simplify using `only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`. Establish `htw` using `DualPolygon.twist_index M hM 𝔟 h𝔟`. Establish `hcM` using `Formalism.F.covolPos _ (zl ρ M) hlatM.2`.

Establish `hr : 0 < rkK M` using `rkK_pos b M hM0`. Establish `hn : 0 < finrank ℚ K` using `Module.finrank_pos`. Establish `hN : 0 < Ideal.absNorm 𝔟` using `Nat.pos_of_ne_zero (fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h))`. Establish `hrk' : Formalism.F.rk (zl ρ M) = finrank ℚ K * rkK M` using `hrkM`. Establish `hsl : Formalism.HN.slope ρ (𝔟 • M) = Formalism.HN.slope ρ M - Real.log (Ideal.absNorm 𝔟 : ℝ) / (finrank ℚ K : ℝ)`.

Unfold `Formalism.HN.slope Formalism.F.slope Formalism.F.deg`. Rewrite using `[hrkeq, hcov, hidx, htw, hrk']`. Establish `hN' : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ)` using `by exact_mod_cast hN`. Establish `hr' : (0 : ℝ) < (rkK M : ℝ)` using `by exact_mod_cast hr`. Establish `hn' : (0 : ℝ) < (finrank ℚ K : ℝ)` using `by exact_mod_cast hn`.

Express the relevant statement in the definitionally equal form `-Real.log (((Ideal.absNorm 𝔟 ^ rkK M : ℕ) : ℝ) * _) / _ = _`. Use `push_cast`. Rewrite using `[Real.log_mul (pow_pos hN' _).ne' hcM.ne', Real.log_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Unfold `muDef`. Rewrite using `[← hρ, hsl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mu_smul_ideal (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    muDef b X (𝔟 • M) = muDef b X M - 2 * Real.log (Ideal.absNorm 𝔟 : ℝ) / (finrank ℚ K : ℝ) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  have hfg : (𝔟 • M).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM
  obtain ⟨hlatM, hrkM, -⟩ := place_lattice_structure K V ι b X hX M hM
  obtain ⟨hlatB, hrkB, -⟩ := place_lattice_structure K V ι b X hX (𝔟 • M) hfg
  have hrkK : rkK (𝔟 • M) = rkK M := by
    unfold rkK; rw [DualPolygon.twist_span_smul M 𝔟 h𝔟]
  have : DiscreteTopology (zl ρ M) := hlatM.2
  have hle : zl ρ (𝔟 • M) ≤ zl ρ M := shiftInv_zl_mono ρ Submodule.smul_le_right
  have hrkeq : Formalism.F.rk (zl ρ (𝔟 • M)) = Formalism.F.rk (zl ρ M) := by
    have h1 : Formalism.HN.rk ρ (𝔟 • M) = Formalism.HN.rk ρ M := by rw [hrkM, hrkB, hrkK]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (zl ρ (𝔟 • M)) (zl ρ M) hle hrkeq
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : (zl ρ (𝔟 • M)).toAddSubgroup.relIndex (zl ρ M).toAddSubgroup =
      (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup := by
    simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have htw := DualPolygon.twist_index M hM 𝔟 h𝔟
  have hcM := Formalism.F.covolPos _ (zl ρ M) hlatM.2
  have hr : 0 < rkK M := rkK_pos b M hM0
  have hn : 0 < finrank ℚ K := Module.finrank_pos
  have hN : 0 < Ideal.absNorm 𝔟 := Nat.pos_of_ne_zero (fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h))
  have hrk' : Formalism.F.rk (zl ρ M) = finrank ℚ K * rkK M := hrkM
  have hsl : Formalism.HN.slope ρ (𝔟 • M) = Formalism.HN.slope ρ M - Real.log (Ideal.absNorm 𝔟 : ℝ) / (finrank ℚ K : ℝ) := by
    unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
    rw [hrkeq, hcov, hidx, htw, hrk']
    have hN' : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hN
    have hr' : (0 : ℝ) < (rkK M : ℝ) := by exact_mod_cast hr
    have hn' : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast hn
    change -Real.log (((Ideal.absNorm 𝔟 ^ rkK M : ℕ) : ℝ) * _) / _ = _
    push_cast
    rw [Real.log_mul (pow_pos hN' _).ne' hcM.ne', Real.log_pow]
    field_simp
    ring
  unfold muDef
  rw [← hρ, hsl]
  ring

/- English proof (translation)
Establish `: FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hM0 : M ≠ ⊥`. Introduce and unpack `rfl`. Apply `hN0` to reduce the goal to its premises. Rewrite using `[hN, Submodule.span_eq_bot]`.

Introduce and unpack `x ⟨a, -, y, hy, rfl⟩`. Rewrite using `[(Submodule.mem_bot _).1 hy, smul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hI (FractionalIdeal.eq_zero_iff.2 hcon)`. Establish `hMfg : M.FG`. Set `ψ : V →ₗ[𝓞 K] V` to `(a • (LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K)`. Establish `hψ : Function.Injective ψ`. Introduce `x y hxy`.

Establish `: a • x = a • y` using `hxy`. Conclude with `smul_right_injective V ha0 this`. Establish `hle : M.map ψ ≤ N`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite using `[hN]`.

Conclude with `Submodule.subset_span ⟨a, ha, y, hy, rfl⟩`. Establish `h1 : (M.map ψ).FG` using `Submodule.FG.of_le hfg hle`. Conclude with `Submodule.fg_of_fg_map_injective ψ hψ h1`. Use `set d : 𝓞 K := (I.den : 𝓞 K) with hd`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.coe_ne_zero I.den`.

Use `set J : Ideal (𝓞 K) := I.num with hJ`. Establish `hJ0 : J ≠ ⊥`. Introduce `h`. Conclude with `hI (FractionalIdeal.num_eq_zero_iff.1 h)`. Establish `hden` using `FractionalIdeal.den_mul_self_eq_num I`.

Establish `hkey : (Ideal.span {d}) • N = J • M`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.smul_le]`. Introduce `r hr n hn`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`.

Rewrite using `[mul_smul]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Rewrite `hn` using `[hN]`. Proceed by induction on `hn using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, y, hy, rfl⟩` from `hx`. Establish `h1 : d • a ∈ I.den • (I : Submodule (𝓞 K) K)` using `Submodule.smul_mem_pointwise_smul a I.den _ ha`. Rewrite `h1` using `[hden]`. Take `⟨j, hj, hja⟩` from `h1`. Establish `h2 : d • a • y = j • y`.

Rewrite using `[← algebraMap_smul K j y, ← smul_assoc]`. Use `congr 1`. Conclude with `hja.symm`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem_smul hj hy`.

Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[Submodule.smul_le]`. Introduce `j hj y hy`. Establish `h1 : algebraMap (𝓞 K) K j ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num` using `⟨j, hj, rfl⟩`. Rewrite `h1` using `[← hden]`.

Take `⟨a, ha, hja⟩` from `h1`. Establish `h2 : j • y = d • a • y`. Rewrite using `[← algebraMap_smul K j y, ← smul_assoc]`. Use `congr 1`. Conclude with `hja.symm`.

Rewrite using `[h2]`. Use `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self d) ?_` and prove the remaining obligations. Rewrite using `[hN]`. Conclude with `Submodule.subset_span ⟨a, ha, y, hy, rfl⟩`. Establish `hsp0 : Ideal.span {d} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hd0`. Establish `e1` using `mu_smul_ideal b X hX N hfg hN0 (Ideal.span {d}) hsp0`. Establish `e2` using `mu_smul_ideal b X hX M hMfg hM0 J hJ0`. Rewrite `e1` using `[hkey]`.

Establish `hNd : (0 : ℝ) < (Ideal.absNorm (Ideal.span {d}) : ℝ)`. Conclude with `Nat.pos_of_ne_zero (fun h => hsp0 (Ideal.absNorm_eq_zero_iff.1 h))` after adjusting the coercions. Establish `hNJ : (0 : ℝ) < (Ideal.absNorm J : ℝ)`. Conclude with `Nat.pos_of_ne_zero (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h))` after adjusting the coercions. Establish `habs : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (Ideal.absNorm J : ℝ) / (Ideal.absNorm (Ideal.span {d}) : ℝ)`.

Rewrite using `[FractionalIdeal.absNorm_eq, Ideal.absNorm_span_singleton]`. Use `push_cast`. Rewrite using `[Nat.cast_natAbs]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[habs, Real.log_div hNJ.ne' hNd.ne']`. Establish `: muDef b X N = muDef b X M - 2 * Real.log (Ideal.absNorm J : ℝ) / (finrank ℚ K : ℝ) + 2 * Real.log (Ideal.absNorm (Ideal.span {d}) : ℝ) / (finrank ℚ K : ℝ)` using `by linarith`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mu_frac (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0)
    (M N : Submodule (𝓞 K) V)
    (hN : N = Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ M, x = (a : K) • y})
    (hfg : N.FG) (hN0 : N ≠ ⊥) :
    muDef b X N = muDef b X M -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (finrank ℚ K : ℝ) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b

  have hM0 : M ≠ ⊥ := by
    rintro rfl
    apply hN0
    rw [hN, Submodule.span_eq_bot]
    rintro x ⟨a, -, y, hy, rfl⟩
    rw [(Submodule.mem_bot _).1 hy, smul_zero]

  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hI (FractionalIdeal.eq_zero_iff.2 hcon)
  have hMfg : M.FG := by
    let ψ : V →ₗ[𝓞 K] V := (a • (LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K)
    have hψ : Function.Injective ψ := by
      intro x y hxy
      have : a • x = a • y := hxy
      exact smul_right_injective V ha0 this
    have hle : M.map ψ ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hN]
      exact Submodule.subset_span ⟨a, ha, y, hy, rfl⟩
    have h1 : (M.map ψ).FG := Submodule.FG.of_le hfg hle
    exact Submodule.fg_of_fg_map_injective ψ hψ h1
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero I.den
  set J : Ideal (𝓞 K) := I.num with hJ
  have hJ0 : J ≠ ⊥ := by
    intro h
    exact hI (FractionalIdeal.num_eq_zero_iff.1 h)
  have hden := FractionalIdeal.den_mul_self_eq_num I
  have hkey : (Ideal.span {d}) • N = J • M := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro r hr n hn
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      apply Submodule.smul_mem
      rw [hN] at hn
      induction hn using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, y, hy, rfl⟩ := hx
        have h1 : d • a ∈ I.den • (I : Submodule (𝓞 K) K) :=
          Submodule.smul_mem_pointwise_smul a I.den _ ha
        rw [hden] at h1
        obtain ⟨j, hj, hja⟩ := h1
        have h2 : d • a • y = j • y := by
          rw [← algebraMap_smul K j y, ← smul_assoc]
          congr 1
          exact hja.symm
        rw [h2]
        exact Submodule.smul_mem_smul hj hy
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    · rw [Submodule.smul_le]
      intro j hj y hy
      have h1 : algebraMap (𝓞 K) K j ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
        ⟨j, hj, rfl⟩
      rw [← hden] at h1
      obtain ⟨a, ha, hja⟩ := h1
      have h2 : j • y = d • a • y := by
        rw [← algebraMap_smul K j y, ← smul_assoc]
        congr 1
        exact hja.symm
      rw [h2]
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self d) ?_
      rw [hN]
      exact Submodule.subset_span ⟨a, ha, y, hy, rfl⟩
  have hsp0 : Ideal.span {d} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd0
  have e1 := mu_smul_ideal b X hX N hfg hN0 (Ideal.span {d}) hsp0
  have e2 := mu_smul_ideal b X hX M hMfg hM0 J hJ0
  rw [hkey] at e1
  have hNd : (0 : ℝ) < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hsp0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hNJ : (0 : ℝ) < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h))
  have habs : ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      (Ideal.absNorm J : ℝ) / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    rw [FractionalIdeal.absNorm_eq, Ideal.absNorm_span_singleton]
    push_cast
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [habs, Real.log_div hNJ.ne' hNd.ne']
  have : muDef b X N = muDef b X M - 2 * Real.log (Ideal.absNorm J : ℝ) / (finrank ℚ K : ℝ) +
      2 * Real.log (Ideal.absNorm (Ideal.span {d}) : ℝ) / (finrank ℚ K : ℝ) := by linarith
  rw [this]
  ring

end Scale

section places

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `haveI := Fact.mk hp`. Conclude with `Int.ideal_span_isMaximal_of_prime p`.
-/
theorem span_prime_isMaximal (p : ℕ) (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  haveI := Fact.mk hp
  exact Int.ideal_span_isMaximal_of_prime p

/- English proof (translation)
Use `haveI := w.isPrime`. Establish `hne : Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal ≠ ⊤` using `(inferInstance : (Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal).IsPrime).ne_top`. Establish `hle : Ideal.span {((p : ℕ) : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]`. Simplify using `using hmem`.

Conclude with `⟨(span_prime_isMaximal p hp).eq_of_le hne hle⟩`.
-/
theorem liesOver_of_mem (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K))
    (hmem : (p : 𝓞 K) ∈ w.asIdeal) : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI := w.isPrime
  have hne : Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal ≠ ⊤ :=
    (inferInstance : (Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal).IsPrime).ne_top
  have hle : Ideal.span {((p : ℕ) : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hmem
  exact ⟨(span_prime_isMaximal p hp).eq_of_le hne hle⟩

/- English proof (translation)
Establish `h : ((p : ℕ) : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) q`. Establish `h0` using `(‹q.LiesOver (Ideal.span {((p : ℕ) : ℤ)})›).over`. Express the relevant statement in the definitionally equal form `Ideal.span {((p : ℕ) : ℤ)} = Ideal.comap (algebraMap ℤ (𝓞 K)) q at h0`. Rewrite using `[← h0]`. Conclude with `Ideal.subset_span rfl`.

Rewrite `h` using `[Ideal.mem_comap]`. Simplify using `using h`.
-/
theorem mem_of_liesOver (p : ℕ) (q : Ideal (𝓞 K)) [q.LiesOver (Ideal.span {(p : ℤ)})] :
    (p : 𝓞 K) ∈ q := by
  have h : ((p : ℕ) : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) q := by
    have h0 := (‹q.LiesOver (Ideal.span {((p : ℕ) : ℤ)})›).over
    change Ideal.span {((p : ℕ) : ℤ)} = Ideal.comap (algebraMap ℤ (𝓞 K)) q at h0
    rw [← h0]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap] at h
  simpa using h

/- English proof (translation)
Use `span_prime_isMaximal p hp` as an intermediate fact. Establish `hP0 : Ideal.span {(p : ℤ)} ≠ ⊥` using `by simp [hp.ne_zero]`. Establish `h` using `Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)`. Rewrite `h` using `[NumberField.RingOfIntegers.rank]`. Rewrite using `[← h]`.

Use `Finset.sum_bij' (fun w hw => ⟨w.asIdeal, w.isPrime, liesOver_of_mem p hp w ((hS w).mp hw)⟩) (fun q _ => ⟨q.1, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hP0 q.1⟩) (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)` and prove the remaining obligations. Rewrite using `[hS]`. Use `q.2.2` as an intermediate fact. Conclude with `mem_of_liesOver p q.1`.
-/
theorem sum_e_f (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal) :
    ∑ w ∈ S, eWL K w * w.asIdeal.inertiaDeg ℤ = Module.finrank ℚ K := by
  have := span_prime_isMaximal p hp
  have hP0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at h
  rw [← h]
  refine Finset.sum_bij' (fun w hw => ⟨w.asIdeal, w.isPrime, liesOver_of_mem p hp w ((hS w).mp hw)⟩)
    (fun q _ => ⟨q.1, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hP0 q.1⟩)
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
  rw [hS]
  have := q.2.2
  exact mem_of_liesOver p q.1

/- English proof (translation)
Establish `hn : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hterm : ∀ w ∈ S, lw K w * (eWL K w : ℝ) = Real.log p / Module.finrank ℚ K * ((eWL K w * w.asIdeal.inertiaDeg ℤ : ℕ) : ℝ)`. Introduce `w hw`. Use `liesOver_of_mem p hp w ((hS w).mp hw)` as an intermediate fact. Establish `hN` using `Ideal.pow_inertiaDeg p w.asIdeal`.

Unfold `lw`. Rewrite using `[← hN]`. Use `push_cast`. Rewrite using `[Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum]`. Use `sum_e_f p hp S hS` as an intermediate fact. Rewrite using `[← Nat.cast_sum, this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_lw_e (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal) :
    ∑ w ∈ S, lw K w * (eWL K w : ℝ) = Real.log p := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hterm : ∀ w ∈ S, lw K w * (eWL K w : ℝ) =
      Real.log p / Module.finrank ℚ K * ((eWL K w * w.asIdeal.inertiaDeg ℤ : ℕ) : ℝ) := by
    intro w hw
    have := liesOver_of_mem p hp w ((hS w).mp hw)
    have hN := Ideal.pow_inertiaDeg p w.asIdeal
    unfold lw
    rw [← hN]
    push_cast
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have := sum_e_f p hp S hS
  rw [← Nat.cast_sum, this]
  field_simp

/- English proof (translation)
Establish `hI : (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Use `⟨(Ideal.finite_factors hI).toFinset, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]`.
-/
theorem finite_places_over (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal := by
  have hI : (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  refine ⟨(Ideal.finite_factors hI).toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

/- English proof (translation)
Unfold `lw`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`.
-/
theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K w := by
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

end places

/- English proof (translation)
Establish `hv` using `D.what₂.places.val_resChar w`. Establish `hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0`. Conclude with `(D.what₂.places.resChar_prime w).ne_zero` after adjusting the coercions. Rewrite `hv` using `[D.val_eq w _ hne]`. Establish `hv' : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = ((D.what₂.places.ramIdx w : ℕ) : ℤ)` using `by exact_mod_cast hv`.

Establish `hpos` using `D.what₂.places.ramIdx_pos w`. Establish `h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) < 1`. Establish `hx : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)` using `by simp`. Rewrite using `[← hx]`. Establish `hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hne`.

Unfold `vAdd at hv'`. Rewrite using `[← WithZero.exp_log hv0, show WithZero.log ((D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) = -((D.what₂.places.ramIdx w : ℕ) : ℤ) by omega]`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Conclude with `((D.plEq w).valuation_lt_one_iff_mem _).mp h1`.
-/
theorem resChar_mem (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hv := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := by
    exact_mod_cast (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne] at hv
  have hv' : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      ((D.what₂.places.ramIdx w : ℕ) : ℤ) := by exact_mod_cast hv
  have hpos := D.what₂.places.ramIdx_pos w
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL
      ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) < 1 := by
    have hx : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL
        ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) := by simp
    rw [← hx]
    have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hne
    unfold vAdd at hv'
    rw [← WithZero.exp_log hv0, show WithZero.log ((D.plEq w).valuation D.what₂.LL
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) = -((D.what₂.places.ramIdx w : ℕ) : ℤ) by omega]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  exact ((D.plEq w).valuation_lt_one_iff_mem _).mp h1

/- English proof (translation)
The claim follows from `lw_nonneg _`.
-/
theorem logWeight_nonneg {D : D7} (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := lw_nonneg _

/- English proof (translation)
Take `⟨T, hT⟩` from `finite_places_over (K := D.what₂.LL) p hp`. Establish `h1 : ∑ w ∈ S, SizeData₂.lwP w = ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Establish `hsub : S.map D.plEq.toEmbedding ⊆ T`.

Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `Finset.mem_map.1 hv`. Rewrite using `[hT]`. Use `resChar_mem D w` as an intermediate fact. Rewrite `this` using `[hS w hw]`.

Conclude with `this`. Establish `h2 : ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v ≤ ∑ v ∈ T, lw D.what₂.LL v` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => lw_nonneg v)`. Establish `h3 : ∑ v ∈ T, lw D.what₂.LL v ≤ ∑ v ∈ T, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ)`. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations. Establish `he : 1 ≤ eWL D.what₂.LL v`.

Establish `h` using `D.ram_eq (D.plEq.symm v)`. Rewrite `h` using `[Equiv.apply_symm_apply]`. Rewrite using `[← h]`. Conclude with `D.what₂.places.ramIdx_pos _`. Establish `he' : (1 : ℝ) ≤ (eWL D.what₂.LL v : ℝ)` using `by exact_mod_cast he`.

Conclude with `le_mul_of_one_le_right (lw_nonneg v) he'`. Rewrite `h3` using `[sum_lw_e p hp T hT]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_lwP_le (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w ∈ S, D.what₂.places.resChar w = p) : ∑ w ∈ S, SizeData₂.lwP w ≤ Real.log p := by
  classical
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w = ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v := by
    rw [Finset.sum_map]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  have h2 : ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v ≤ ∑ v ∈ T, lw D.what₂.LL v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => lw_nonneg v)
  have h3 : ∑ v ∈ T, lw D.what₂.LL v ≤ ∑ v ∈ T, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    refine Finset.sum_le_sum fun v _ => ?_
    have he : 1 ≤ eWL D.what₂.LL v := by
      have h := D.ram_eq (D.plEq.symm v)
      rw [Equiv.apply_symm_apply] at h
      rw [← h]
      exact D.what₂.places.ramIdx_pos _
    have he' : (1 : ℝ) ≤ (eWL D.what₂.LL v : ℝ) := by exact_mod_cast he
    exact le_mul_of_one_le_right (lw_nonneg v) he'
  rw [sum_lw_e p hp T hT] at h3
  linarith

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to h]`. Use `Finset.sum_le_sum fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp : p.Prime`. Conclude with `sum_lwP_le D p hp _ (fun w hw => (Finset.mem_filter.1 hw).2)`. Establish `: S.filter (fun w => D.what₂.places.resChar w = p) = ∅` using `Finset.filter_eq_empty_iff.2 (fun w _ hw => hp (hw ▸ D.what₂.places.resChar_prime w))`.

Rewrite using `[this, Finset.sum_empty]`. Conclude with `Real.log_natCast_nonneg _`.
-/
theorem sum_lwP_le_primes (D : D7) (S : Finset D.what₂.places.Pl) (P : Finset ℕ)
    (h : ∀ w ∈ S, D.what₂.places.resChar w ∈ P) :
    ∑ w ∈ S, SizeData₂.lwP w ≤ ∑ p ∈ P, Real.log p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to h]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p.Prime
  · exact sum_lwP_le D p hp _ (fun w hw => (Finset.mem_filter.1 hw).2)
  · have : S.filter (fun w => D.what₂.places.resChar w = p) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun w _ hw => hp (hw ▸ D.what₂.places.resChar_prime w))
    rw [this, Finset.sum_empty]
    exact Real.log_natCast_nonneg _

/- English proof (translation)
Establish `h : ∑ p ∈ A ∪ B, Real.log (p : ℝ) + ∑ p ∈ A ∩ B, Real.log (p : ℝ) = ∑ p ∈ A, Real.log (p : ℝ) + ∑ p ∈ B, Real.log (p : ℝ)` using `Finset.sum_union_inter`. Establish `h2 : 0 ≤ ∑ p ∈ A ∩ B, Real.log (p : ℝ)` using `Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_union_le (A B : Finset ℕ) :
    ∑ p ∈ A ∪ B, Real.log (p : ℝ) ≤ ∑ p ∈ A, Real.log (p : ℝ) + ∑ p ∈ B, Real.log (p : ℝ) := by
  have h : ∑ p ∈ A ∪ B, Real.log (p : ℝ) + ∑ p ∈ A ∩ B, Real.log (p : ℝ) =
      ∑ p ∈ A, Real.log (p : ℝ) + ∑ p ∈ B, Real.log (p : ℝ) := Finset.sum_union_inter
  have h2 : 0 ≤ ∑ p ∈ A ∩ B, Real.log (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  linarith

/- English proof (translation)
Establish `hpr : ((primorial N : ℕ) : ℝ) = ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℝ)`. Rewrite using `[primorial, Nat.cast_prod]`. Establish `h1 : Real.log ((primorial N : ℕ) : ℝ) = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)`. Rewrite using `[hpr, Real.log_prod]`. Introduce `p hp`.

Conclude with `Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero`. Rewrite using `[← h1]`. Establish `h2 : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N` using `by exact_mod_cast primorial_le_4_pow N`. Establish `h3 : (0 : ℝ) < ((primorial N : ℕ) : ℝ)` using `by exact_mod_cast primorial_pos N`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_log_primes_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤ N * Real.log 4 := by
  have hpr : ((primorial N : ℕ) : ℝ) = ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℝ) := by
    rw [primorial, Nat.cast_prod]
  have h1 : Real.log ((primorial N : ℕ) : ℝ) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [hpr, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
  rw [← h1]
  have h2 : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by exact_mod_cast primorial_le_4_pow N
  have h3 : (0 : ℝ) < ((primorial N : ℕ) : ℝ) := by exact_mod_cast primorial_pos N
  calc Real.log ((primorial N : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ N) := Real.log_le_log h3 h2
    _ = N * Real.log 4 := by rw [Real.log_pow]

/- English proof (translation)
Establish `hpos : 0 < ∏ p ∈ n.primeFactors, p` using `Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)`. Establish `hle : ∏ p ∈ n.primeFactors, p ≤ n` using `Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)`. Establish `h1 : Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) = ∑ p ∈ n.primeFactors, Real.log (p : ℝ)`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Introduce `p hp`.

Conclude with `Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero`. Rewrite using `[← h1]`. Conclude with `Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)`.
-/
theorem sum_log_primeFactors_le (n : ℕ) (hn : 0 < n) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log n := by
  have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hle : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have h1 : Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
      ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← h1]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/- English proof (translation)
Unfold `DV.Iu`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `w _`. Conclude with `zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)`.
-/
theorem Iu_ne_zero (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) : DV.Iu D L u ≠ 0 := by
  unfold DV.Iu
  rw [Finset.prod_ne_zero_iff]
  intro w _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)

/- English proof (translation)
Unfold `DV.Iu`. Rewrite using `[map_prod]`. Use `push_cast`. Rewrite using `[Real.log_prod]`. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, FractionalIdeal.coeIdeal_absNorm]`. Use `push_cast`. Rewrite using `[Real.log_zpow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `w _`. Rewrite using `[map_zpow₀, FractionalIdeal.coeIdeal_absNorm]`. Use `push_cast`. Apply `zpow_ne_zero` to reduce the goal to its premises.

Establish `: Ideal.absNorm (D.plEq w).asIdeal ≠ 0` using `fun h => (D.plEq w).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `this` after adjusting the coercions.
-/
theorem log_absNorm_Iu (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) :
    Real.log ((FractionalIdeal.absNorm (DV.Iu D L u) : ℚ) : ℝ) =
      -∑ w ∈ L.supp, (⌊DV.ur D w (L.sg u w)⌋ : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ) := by
  unfold DV.Iu
  rw [map_prod]
  push_cast
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [Real.log_zpow]
    push_cast
    ring
  · intro w _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    apply zpow_ne_zero
    have : Ideal.absNorm (D.plEq w).asIdeal ≠ 0 :=
      fun h => (D.plEq w).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this

/- English proof (translation)
Establish `h` using `mu_frac (D.div.Nu u).b (D.div.Nu u).X hX (DV.Iu D L u) (Iu_ne_zero D L u) (L.NuLat u) (D.div.Nu u).L (hdef u) hfg hne`. Establish `h' : (D.div.Nu u).mu = (L.NuH u).mu - 2 * Real.log ((FractionalIdeal.absNorm (DV.Iu D L u) : ℚ) : ℝ) / (finrank ℚ D.what₂.LL : ℝ)` using `h`. Rewrite using `[h', log_absNorm_Iu]`. Establish `: ∀ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) = 2 * ((⌊DV.ur D w (L.sg u w)⌋ : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ)) / (finrank ℚ D.what₂.LL : ℝ)`. Introduce `w _`.

Unfold `SizeData₂.lwP lw`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl this, ← Finset.sum_div, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mu_diff (D : D7) (L : SizeData₂ D) (hdef : DV.NprimeDef D L) (u : D.what₂.Word)
    (hX : ∀ v, IsUnit ((D.div.Nu u).X v).det)
    (hfg : (D.div.Nu u).L.FG) (hne : (D.div.Nu u).L ≠ ⊥) :
    (D.div.Nu u).mu - (L.NuH u).mu =
      ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) := by
  have h := mu_frac (D.div.Nu u).b (D.div.Nu u).X hX (DV.Iu D L u) (Iu_ne_zero D L u)
    (L.NuLat u) (D.div.Nu u).L (hdef u) hfg hne
  have h' : (D.div.Nu u).mu = (L.NuH u).mu -
      2 * Real.log ((FractionalIdeal.absNorm (DV.Iu D L u) : ℚ) : ℝ) / (finrank ℚ D.what₂.LL : ℝ) := h
  rw [h', log_absNorm_Iu]
  have : ∀ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) =
      2 * ((⌊DV.ur D w (L.sg u w)⌋ : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ)) /
        (finrank ℚ D.what₂.LL : ℝ) := by
    intro w _
    unfold SizeData₂.lwP lw
    ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Finset.mul_sum]
  ring

open Classical in

/- English proof (translation)
The claim follows from `|(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤ 2 * ∑ w ∈ L.supp.filter (fun w => L.sg u w ≠ 0), SizeData₂.lwP w := by rw [mu_diff D L hdef u hX hfg hne, ← Finset.sum_sub_distrib] have hsum : ∑ w ∈ L.supp.filter (fun w => L.sg u w ≠ 0), SizeData₂.lwP …`.
-/
theorem round_le (D : D7) (L : SizeData₂ D) (hdef : DV.NprimeDef D L) (u : D.what₂.Word)
    (hX : ∀ v, IsUnit ((D.div.Nu u).X v).det)
    (hfg : (D.div.Nu u).L.FG) (hne : (D.div.Nu u).L ≠ ⊥) :
    |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤
      2 * ∑ w ∈ L.supp.filter (fun w => L.sg u w ≠ 0), SizeData₂.lwP w := by
  rw [mu_diff D L hdef u hX hfg hne, ← Finset.sum_sub_distrib]
  have hsum : ∑ w ∈ L.supp.filter (fun w => L.sg u w ≠ 0), SizeData₂.lwP w =
      ∑ w ∈ L.supp, if L.sg u w ≠ 0 then SizeData₂.lwP w else 0 := Finset.sum_filter _ _
  rw [hsum, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun w _ => ?_)
  have hl : 0 ≤ SizeData₂.lwP w := logWeight_nonneg w
  unfold SizeData₂.sz DV.ur
  have e : 2 * SizeData₂.lwP w * (⌊(D.what₂.places.ramIdx w : ℝ) * L.sg u w⌋ : ℝ) -
      2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * L.sg u w) =
      2 * SizeData₂.lwP w * ((⌊(D.what₂.places.ramIdx w : ℝ) * L.sg u w⌋ : ℝ) -
        (D.what₂.places.ramIdx w : ℝ) * L.sg u w) := by ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * SizeData₂.lwP w)]
  split_ifs with hs
  · have h1 := Int.floor_le ((D.what₂.places.ramIdx w : ℝ) * L.sg u w)
    have h2 := Int.lt_floor_add_one ((D.what₂.places.ramIdx w : ℝ) * L.sg u w)
    have h3 : |(⌊(D.what₂.places.ramIdx w : ℝ) * L.sg u w⌋ : ℝ) -
        (D.what₂.places.ramIdx w : ℝ) * L.sg u w| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * SizeData₂.lwP w)
    linarith
  · push_neg at hs
    rw [hs]
    simp

/- English proof (translation)
Unfold `SizeData₂.ZeroAbove at hZ`. Unfold `SizeData₂.sg`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j hj`. Take `⟨hg, hE⟩` from `hZ u j hj w h1 h2 h3 h4 h5`.

Establish `hF` using `L.F_above j w h1 h3 h4`. Establish `hgD : L.gainD j w = 0`. Unfold `SizeData₂.gainD`. Simplify using `[hg]`. Simplify using `[hgD, hF, hE]`.
-/
theorem sg_eq_zero (D : D7) (L : SizeData₂ D) (hZ : L.ZeroAbove) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h1 : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
    (h2 : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (h3 : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (h4 : D.what₂.places.resChar w ≠ D.host.d)
    (h5 : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) : L.sg u w = 0 := by
  unfold SizeData₂.ZeroAbove at hZ
  unfold SizeData₂.sg
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hg, hE⟩ := hZ u j hj w h1 h2 h3 h4 h5
  have hF := L.F_above j w h1 h3 h4
  have hgD : L.gainD j w = 0 := by
    unfold SizeData₂.gainD
    simp [hg]
  simp [hgD, hF, hE]

/- English proof (translation)
The claim follows from `|(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤ 2 * (L.sc.X'' D.R.n * Real.log 4 + (Real.log ((D.mem u).A.T : ℝ) + (Real.log (D.host.g 0 : ℝ) + (Real.log (D.host.g 1 : ℝ) + (Real.log (D.host.d : ℝ) + Real.log ((D.mem u).C.DGam : ℝ)))))) := by classica …`.
-/
theorem nprimeMu_at (D : D7) (L : SizeData₂ D) (hdef : DV.NprimeDef D L) (hZ : L.ZeroAbove)
    (hXpp : 0 ≤ L.sc.X'' D.R.n) (u : D.what₂.Word)
    (hX : ∀ v, IsUnit ((D.div.Nu u).X v).det)
    (hfg : (D.div.Nu u).L.FG) (hne : (D.div.Nu u).L ≠ ⊥) :
    |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤
      2 * (L.sc.X'' D.R.n * Real.log 4 + (Real.log ((D.mem u).A.T : ℝ) + (Real.log (D.host.g 0 : ℝ) +
        (Real.log (D.host.g 1 : ℝ) + (Real.log (D.host.d : ℝ) +
          Real.log ((D.mem u).C.DGam : ℝ)))))) := by
  classical
  refine (round_le D L hdef u hX hfg hne).trans ?_
  set N : ℕ := ⌊L.sc.X'' D.R.n⌋₊ with hN
  set P : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime ∪ ({(D.mem u).A.T} ∪ ({D.host.g 0} ∪
    ({D.host.g 1} ∪ ({D.host.d} ∪ (D.mem u).C.DGam.primeFactors)))) with hP
  have hmem : ∀ w ∈ L.supp.filter (fun w => L.sg u w ≠ 0), D.what₂.places.resChar w ∈ P := by
    intro w hw
    have hsg := (Finset.mem_filter.1 hw).2
    by_contra hcon
    simp only [hP, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
      not_or, not_and] at hcon
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcon
    apply hsg
    refine sg_eq_zero D L hZ u w ?_ c2 ?_ c5 ?_
    · have : ¬ D.what₂.places.resChar w < N + 1 := fun h => c1 h (D.what₂.places.resChar_prime w)
      have h' : N < D.what₂.places.resChar w := by omega
      exact Nat.lt_of_floor_lt h'
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨c3, c4⟩
    · intro hd
      exact c6 (Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, hd, (D.mem u).C.DGam_pos.ne'⟩)
  have h1 := sum_lwP_le_primes D _ P hmem
  have hNle : (N : ℝ) ≤ L.sc.X'' D.R.n := Nat.floor_le hXpp
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : ∑ p ∈ P, Real.log (p : ℝ) ≤ L.sc.X'' D.R.n * Real.log 4 +
      (Real.log ((D.mem u).A.T : ℝ) + (Real.log (D.host.g 0 : ℝ) +
        (Real.log (D.host.g 1 : ℝ) + (Real.log (D.host.d : ℝ) +
          Real.log ((D.mem u).C.DGam : ℝ))))) := by
    rw [hP]
    refine (sum_log_union_le _ _).trans (add_le_add ((sum_log_primes_le N).trans
      (mul_le_mul_of_nonneg_right hNle hlog4)) ?_)
    refine (sum_log_union_le _ _).trans (add_le_add (by rw [Finset.sum_singleton]) ?_)
    refine (sum_log_union_le _ _).trans (add_le_add (by rw [Finset.sum_singleton]) ?_)
    refine (sum_log_union_le _ _).trans (add_le_add (by rw [Finset.sum_singleton]) ?_)
    refine (sum_log_union_le _ _).trans (add_le_add (by rw [Finset.sum_singleton]) ?_)
    exact sum_log_primeFactors_le _ (D.mem u).C.DGam_pos
  linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem scale_rpow_le_self_of_le_one (s : Scale) {c : ℝ} (hc : c ≤ 1) : s.x ^ c ≤ s.x := by
  calc s.x ^ c ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hc
    _ = s.x := Real.rpow_one _

/- English proof (translation)
Establish `hx : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `ha : 0 < s.a`. Unfold `Scale.a Scale.b`. Conclude with `mul_pos hx (Real.exp_pos _)`. Establish `hX : 0 < s.X'`.

Unfold `Scale.X'`. Conclude with `Real.exp_pos _`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Simplify using `only [Scale.X'', Scale.w'', Scale.b']`. Clear denominators, using `[ha.ne', hX.ne', hx.ne', hn'.ne']` for the nonvanishing conditions.

Apply the tactic sequence `try ring`.
-/
theorem Xpp_eq (s : Scale) (n : ℕ) (hn : 0 < n) : s.X'' n = s.X' * s.x * n := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have ha : 0 < s.a := by
    unfold Scale.a Scale.b
    exact mul_pos hx (Real.exp_pos _)
  have hX : 0 < s.X' := by
    unfold Scale.X'
    exact Real.exp_pos _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Scale.X'', Scale.w'', Scale.b']
  field_simp [ha.ne', hX.ne', hx.ne', hn'.ne']
  try ring

/- English proof (translation)
Unfold `Scale.X'`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)`.
-/
theorem one_le_Xp (s : Scale) : 1 ≤ s.X' := by
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

/- English proof (translation)
Establish `h1` using `R.m_le_f`. Establish `h2` using `R.two_le_m`. Use `show 0 < R.ord`. Use linear arithmetic over natural numbers and integers.
-/
theorem n_pos (R : Ranks) : 0 < R.n := by
  have h1 := R.m_le_f
  have h2 := R.two_le_m
  show 0 < R.ord
  omega

/- English proof (translation)
Establish `hn` using `n_pos R`. Rewrite using `[Xpp_eq s R.n hn]`. Establish `h1` using `one_le_Xp s`. Establish `hx : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `h0 : (0 : ℝ) ≤ s.x * R.n` using `mul_nonneg hx.le (Nat.cast_nonneg _)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 h0]`.
-/
theorem xn_le_Xpp (s : Scale) (R : Ranks) : s.x * R.n ≤ s.X'' R.n := by
  have hn := n_pos R
  rw [Xpp_eq s R.n hn]
  have h1 := one_le_Xp s
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have h0 : (0 : ℝ) ≤ s.x * R.n := mul_nonneg hx.le (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h1 h0]

/- English proof (translation)
Establish `hn : (1 : ℝ) ≤ R.n` using `by exact_mod_cast n_pos R`. Establish `hx : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `h` using `xn_le_Xpp s R`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem x_le_Xpp (s : Scale) (R : Ranks) : s.x ≤ s.X'' R.n := by
  have hn : (1 : ℝ) ≤ R.n := by exact_mod_cast n_pos R
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have h := xn_le_Xpp s R
  nlinarith

variable {D : D7} (L : SizeData₂ D)

/- English proof (translation)
Establish `h1` using `L.sc.eps_pos`. Establish `h2` using `L.sc.eps_lt`. Unfold `szTh`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith`.
-/
theorem th_bounds : 0 < szTh L ∧ szTh L + L.sc.eps ≤ 1 ∧ L.sc.eps / 5 + szTh L ≤ 1 ∧
    2 + 8 * L.sc.eps + szTh L ≤ 3 ∧ L.sc.eps / 4 ≤ 1 ∧ L.sc.eps / 4 ≤ L.sc.eps / 3 := by
  have h1 := L.sc.eps_pos
  have h2 := L.sc.eps_lt
  unfold szTh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/- English proof (translation)
Establish `hx : 0 < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Unfold `SizeG at hG`. Establish `h` using `(hG i i).2.2`. Establish `hb` using `th_bounds L`. Establish `e1 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (szTh L + L.sc.eps)`.

Unfold `Scale.L`. Rewrite using `[Real.rpow_add hx]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_g_le (hG : SizeG L) (i : Fin 2) : Real.log (D.host.g i : ℝ) ≤ L.sc.X'' D.R.n := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  unfold SizeG at hG
  have h := (hG i i).2.2
  have hb := th_bounds L
  have e1 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (szTh L + L.sc.eps) := by
    unfold Scale.L
    rw [Real.rpow_add hx]
  calc Real.log (D.host.g i : ℝ) ≤ L.sc.x ^ szTh L * L.sc.L := h
    _ = L.sc.x ^ (szTh L + L.sc.eps) := e1
    _ ≤ L.sc.x := scale_rpow_le_self_of_le_one L.sc hb.2.1
    _ ≤ L.sc.X'' D.R.n := x_le_Xpp L.sc D.R

/- English proof (translation)
Unfold `SizeQD at hQD`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_d_le (hQD : SizeQD L) : Real.log (D.host.d : ℝ) ≤ L.sc.X'' D.R.n := by
  unfold SizeQD at hQD
  calc Real.log (D.host.d : ℝ) ≤ L.sc.x ^ (L.sc.eps / 5 + szTh L) := hQD.2.2.2.2.1
    _ ≤ L.sc.x := scale_rpow_le_self_of_le_one L.sc (th_bounds L).2.2.1
    _ ≤ L.sc.X'' D.R.n := x_le_Xpp L.sc D.R

/- English proof (translation)
Unfold `SizeTu at hT`. Establish `hx : 0 < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Establish `e1 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (szTh L + L.sc.eps)`. Unfold `Scale.L`. Rewrite using `[Real.rpow_add hx]`.

Establish `h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x`. Rewrite using `[e1]`. Conclude with `scale_rpow_le_self_of_le_one L.sc (th_bounds L).2.1`. Establish `hm : (D.R.m : ℝ) ≤ 2 * D.R.n`. Establish `h' : D.R.m ≤ 2 * D.R.n` using `D.R.m_le_f`.

Conclude with `h'` after adjusting the coercions. Establish `hxn` using `xn_le_Xpp L.sc D.R`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_T_le (hT : SizeTu L) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) ≤ 2 * L.sc.X'' D.R.n := by
  unfold SizeTu at hT
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have e1 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (szTh L + L.sc.eps) := by
    unfold Scale.L
    rw [Real.rpow_add hx]
  have h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x := by
    rw [e1]
    exact scale_rpow_le_self_of_le_one L.sc (th_bounds L).2.1
  have hm : (D.R.m : ℝ) ≤ 2 * D.R.n := by
    have h' : D.R.m ≤ 2 * D.R.n := D.R.m_le_f
    exact_mod_cast h'
  have hxn := xn_le_Xpp L.sc D.R
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  calc Real.log ((D.mem u).A.T : ℝ) ≤ L.sc.x ^ szTh L * D.R.m * L.sc.L := hT u
    _ = D.R.m * (L.sc.x ^ szTh L * L.sc.L) := by ring
    _ ≤ D.R.m * L.sc.x := mul_le_mul_of_nonneg_left h2 hm0
    _ ≤ 2 * D.R.n * L.sc.x := mul_le_mul_of_nonneg_right hm hx.le
    _ ≤ 2 * L.sc.X'' D.R.n := by linarith

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx : 0 < L.sc.x` using `by linarith`. Establish `hb` using `th_bounds L`. Unfold `SizeN at hN`. Unfold `SizeEta at hEta`.

Unfold `SizeNodes at hNodes`. Establish `hn1 : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast n_pos D.R`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hN2n : 2 ≤ D.R.N D.R.m`. Establish `h2` using `D.R.two_le_m`.

Use `show 2 ≤ D.R.k + D.R.m * (D.R.t + 1)`. Establish `h3 : D.R.m ≤ D.R.m * (D.R.t + 1)` using `le_trans (le_of_eq (mul_one D.R.m).symm) (Nat.mul_le_mul_left _ (by omega))`. Conclude with `le_trans h2 (le_trans h3 (Nat.le_add_left _ _))`. Establish `hN1 : (1 : ℝ) ≤ D.R.N D.R.m`. Establish `: (2 : ℝ) ≤ D.R.N D.R.m` using `by exact_mod_cast hN2n`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Take `⟨j, hj⟩` from `D.R.t_odd`. Establish `: 1 ≤ D.R.t` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `heta1 : 1 ≤ L.etaSz` using `le_trans ht1 hEta.1`. Establish `heta0 : 0 < L.etaSz` using `by linarith`. Establish `hNeta : (D.R.N D.R.m : ℝ) ≤ L.etaSz`. Establish `h1` using `hNodes.2.2.2.2.2.2`. Establish `hp : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ (by linarith)`.

Establish `h2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10` using `le_mul_of_one_le_right (by linarith) hp`. Establish `h3 : L.etaSz / D.R.m ≤ L.etaSz` using `div_le_self heta0.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogeta : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4))` using `(Real.log_le_iff_le_exp heta0).mp hEta.2.2.1`. Establish `hq : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3)` using `Real.rpow_le_rpow_of_exponent_le hx1.le hb.2.2.2.2.2`.

Establish `hNX : (D.R.N D.R.m : ℝ) ≤ L.sc.X'`. Unfold `Scale.X'`. Combine the equalities or inequalities in the displayed calculation. Establish `hlogn : Real.log (D.R.n : ℝ) ≤ 3 * Real.log L.sc.x`. Establish `h1 : Real.log (D.R.n : ℝ) ≤ Real.log (L.sc.x ^ (2 + 8 * L.sc.eps + szTh L))` using `Real.log_le_log (by linarith) hN.2`.

Rewrite `h1` using `[Real.log_rpow hx]`. Establish `h2 : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg hx1.le`. Establish `h3` using `mul_le_mul_of_nonneg_right hb.2.2.2.1 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.x`.

Combine the equalities or inequalities in the displayed calculation. Establish `hf : (D.R.f : ℝ) = 2 * D.R.n`. Simplify using `only [Ranks.f, Nat.cast_mul, Nat.cast_ofNat]`. Establish `hlx : Real.log L.sc.x ≤ L.sc.x - 1` using `Real.log_le_sub_one_of_pos hx`. Establish `hl2 : Real.log 2 < 1`.

Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (D.R.n : ℝ) ≠ 0` using `ne_of_gt (by linarith)`. Establish `h2n0 : 2 * (D.R.n : ℝ) ≠ 0` using `ne_of_gt (by linarith)`. Establish `hN0 : (D.R.N D.R.m : ℝ) ≠ 0` using `ne_of_gt (by linarith)`.

Establish `hlog : Real.log (2 * (D.R.n : ℝ) * D.R.N D.R.m) ≤ 4 * L.sc.x`. Rewrite using `[Real.log_mul h2n0 hN0, Real.log_mul two_ne_zero hn0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod1 : (1 : ℝ) ≤ 2 * D.R.n * D.R.N D.R.m` using `one_le_mul_of_one_le_of_one_le (by linarith) hN1`. Establish `hlog0 : 0 ≤ Real.log (2 * (D.R.n : ℝ) * D.R.N D.R.m)` using `Real.log_nonneg hprod1`.

Establish `hXpp` using `Xpp_eq L.sc D.R.n (n_pos D.R)`. Establish `hX1` using `one_le_Xp L.sc`. Rewrite using `[hf]`. Use `⟨?_, mul_nonneg (by positivity) hlog0⟩` and prove the remaining obligations. Rewrite using `[hXpp]`.

Establish `hA : 2 * (D.R.n : ℝ) * D.R.N D.R.m ≤ 2 * D.R.n * L.sc.X'` using `mul_le_mul_of_nonneg_left hNX (by positivity)`. Establish `hB` using `mul_le_mul hA hlog hlog0 (mul_nonneg (by positivity) (by linarith : (0 : ℝ) ≤ L.sc.X'))`. Establish `hpos : 0 ≤ L.sc.X' * L.sc.x * D.R.n` using `mul_nonneg (mul_nonneg (by linarith) hx.le) (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fN_le (hN : SizeN L) (hEta : SizeEta L) (hNodes : SizeNodes L) :
    (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ 10 * L.sc.X'' D.R.n ∧
    0 ≤ (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := by linarith
  have hb := th_bounds L
  unfold SizeN at hN
  unfold SizeEta at hEta
  unfold SizeNodes at hNodes
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n_pos D.R
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hN2n : 2 ≤ D.R.N D.R.m := by
    have h2 := D.R.two_le_m
    show 2 ≤ D.R.k + D.R.m * (D.R.t + 1)
    have h3 : D.R.m ≤ D.R.m * (D.R.t + 1) :=
      le_trans (le_of_eq (mul_one D.R.m).symm) (Nat.mul_le_mul_left _ (by omega))
    exact le_trans h2 (le_trans h3 (Nat.le_add_left _ _))
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
    have : (2 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hN2n
    linarith
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    obtain ⟨j, hj⟩ := D.R.t_odd
    have : 1 ≤ D.R.t := by omega
    exact_mod_cast this
  have heta1 : 1 ≤ L.etaSz := le_trans ht1 hEta.1
  have heta0 : 0 < L.etaSz := by linarith
  have hNeta : (D.R.N D.R.m : ℝ) ≤ L.etaSz := by
    have h1 := hNodes.2.2.2.2.2.2
    have hp : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
      le_mul_of_one_le_right (by linarith) hp
    have h3 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self heta0.le (by linarith)
    linarith
  have hlogeta : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) :=
    (Real.log_le_iff_le_exp heta0).mp hEta.2.2.1
  have hq : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le hb.2.2.2.2.2
  have hNX : (D.R.N D.R.m : ℝ) ≤ L.sc.X' := by
    unfold Scale.X'
    calc (D.R.N D.R.m : ℝ) ≤ L.etaSz := hNeta
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := hlogeta
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := Real.exp_le_exp.mpr hq
  have hlogn : Real.log (D.R.n : ℝ) ≤ 3 * Real.log L.sc.x := by
    have h1 : Real.log (D.R.n : ℝ) ≤ Real.log (L.sc.x ^ (2 + 8 * L.sc.eps + szTh L)) :=
      Real.log_le_log (by linarith) hN.2
    rw [Real.log_rpow hx] at h1
    have h2 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
    have h3 := mul_le_mul_of_nonneg_right hb.2.2.2.1 h2
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.x := by
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log L.etaSz := Real.log_le_log (by linarith) hNeta
      _ ≤ L.sc.x ^ (L.sc.eps / 4) := hEta.2.2.1
      _ ≤ L.sc.x := scale_rpow_le_self_of_le_one L.sc hb.2.2.2.2.1
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by
    simp only [Ranks.f, Nat.cast_mul, Nat.cast_ofNat]
  have hlx : Real.log L.sc.x ≤ L.sc.x - 1 := Real.log_le_sub_one_of_pos hx
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hn0 : (D.R.n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h2n0 : 2 * (D.R.n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN0 : (D.R.N D.R.m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log (2 * (D.R.n : ℝ) * D.R.N D.R.m) ≤ 4 * L.sc.x := by
    rw [Real.log_mul h2n0 hN0, Real.log_mul two_ne_zero hn0]
    linarith
  have hprod1 : (1 : ℝ) ≤ 2 * D.R.n * D.R.N D.R.m :=
    one_le_mul_of_one_le_of_one_le (by linarith) hN1
  have hlog0 : 0 ≤ Real.log (2 * (D.R.n : ℝ) * D.R.N D.R.m) := Real.log_nonneg hprod1
  have hXpp := Xpp_eq L.sc D.R.n (n_pos D.R)
  have hX1 := one_le_Xp L.sc
  rw [hf]
  refine ⟨?_, mul_nonneg (by positivity) hlog0⟩
  rw [hXpp]
  have hA : 2 * (D.R.n : ℝ) * D.R.N D.R.m ≤ 2 * D.R.n * L.sc.X' :=
    mul_le_mul_of_nonneg_left hNX (by positivity)
  have hB := mul_le_mul hA hlog hlog0 (mul_nonneg (by positivity) (by linarith : (0 : ℝ) ≤ L.sc.X'))
  have hpos : 0 ≤ L.sc.X' * L.sc.x * D.R.n :=
    mul_nonneg (mul_nonneg (by linarith) hx.le) (by linarith)
  calc 2 * (D.R.n : ℝ) * D.R.N D.R.m * Real.log (2 * (D.R.n : ℝ) * D.R.N D.R.m)
      ≤ 2 * D.R.n * L.sc.X' * (4 * L.sc.x) := hB
    _ = 8 * (L.sc.X' * L.sc.x * D.R.n) := by ring
    _ ≤ 10 * (L.sc.X' * L.sc.x * D.R.n) := by linarith

/- English proof (translation)
Unfold `FactDGam at hC`. Take `⟨h1, h2⟩` from `fN_le L hN hEta hNodes`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_DGam_le (hN : SizeN L) (hEta : SizeEta L) (hNodes : SizeNodes L) (C : ℝ)
    (hC : FactDGam D C) (u : D.what₂.Word) :
    Real.log ((D.mem u).C.DGam : ℝ) ≤ |C| * 10 * L.sc.X'' D.R.n := by
  unfold FactDGam at hC
  obtain ⟨h1, h2⟩ := fN_le L hN hEta hNodes
  calc Real.log ((D.mem u).C.DGam : ℝ)
      ≤ C * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := hC u
    _ = C * ((D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := by ring
    _ ≤ |C| * ((D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ ≤ |C| * (10 * L.sc.X'' D.R.n) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 10 * L.sc.X'' D.R.n := by ring

/- English proof (translation)
Introduce `hL`. Unfold `HLat.rank Formalism.HN.rkK at h`. Establish `h0 : Submodule.span K (A.L : Set A.V) = ⊥`. Rewrite using `[hL]`. Simplify using the standard rewrite rules.

Establish `h1` using `(LinearEquiv.ofEq _ _ h0).finrank_eq`. Rewrite `h1` using `[finrank_bot]`. Rewrite `h` using `[h1]`. Conclude with `lt_irrefl 0 h`.
-/
theorem ne_bot_of_rank_pos {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (h : 0 < A.rank) : A.L ≠ ⊥ := by
  intro hL
  unfold HLat.rank Formalism.HN.rkK at h
  have h0 : Submodule.span K (A.L : Set A.V) = ⊥ := by
    rw [hL]
    simp
  have h1 := (LinearEquiv.ofEq _ _ h0).finrank_eq
  rw [finrank_bot] at h1
  rw [h1] at h
  exact lt_irrefl 0 h

/- English proof (translation)
The claim follows from `|(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤ (2 * (Real.log 4 + 3 + CT + CG)) * L.sc.X'' D.R.n := by have hXpp : 0 ≤ L.sc.X'' D.R.n := (lt_trans one_pos L.sc.one_lt_alt).le.trans (x_le_Xpp L.sc D.R) have h := nprimeMu_at D L hdef hZ hXpp u (D.div_g …`.
-/
theorem nprimeMuR_at (hQD : SizeQD L) (hG : SizeG L) (hdef : DV.NprimeDef D L) (hZ : L.ZeroAbove)
    (hlat : ∀ u, (D.div.Nu u).L.FG ∧ 0 < (D.div.Nu u).rank) (CT CG : ℝ)
    (hT : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CT * L.sc.X'' D.R.n)
    (hC : ∀ u, Real.log ((D.mem u).C.DGam : ℝ) ≤ CG * L.sc.X'' D.R.n) (u : D.what₂.Word) :
    |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤
      (2 * (Real.log 4 + 3 + CT + CG)) * L.sc.X'' D.R.n := by
  have hXpp : 0 ≤ L.sc.X'' D.R.n :=
    (lt_trans one_pos L.sc.one_lt_alt).le.trans (x_le_Xpp L.sc D.R)
  have h := nprimeMu_at D L hdef hZ hXpp u (D.div_good.2 u) (hlat u).1
    (ne_bot_of_rank_pos _ (hlat u).2)
  have h1 := hT u
  have h2 := log_g_le L hG 0
  have h3 := log_g_le L hG 1
  have h4 := log_d_le L hQD
  have h5 := hC u
  linarith

def MuZero {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.L x i).ZeroAbove

def MuFG {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, ((Fm.D x i).div.Nu u).L.FG

def MuRank {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, 0 < ((Fm.D x i).div.Nu u).rank

def MuTu {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
    Real.log (((Fm.D x i).mem u).A.T : ℝ) ≤ C * (Fm.L x i).sc.X'' (Fm.D x i).R.n

def MuDGam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
    Real.log (((Fm.D x i).mem u).C.DGam : ℝ) ≤ C * (Fm.L x i).sc.X'' (Fm.D x i).R.n

/- English proof (translation)
Take `⟨a1, hZ⟩` from `hZ`. Take `⟨a2, hF⟩` from `hF`. Take `⟨a3, hR⟩` from `hR`. Take `⟨CT, a4, hT⟩` from `hT`. Take `⟨CG, a5, hG⟩` from `hG`.

Use `⟨2 * (Real.log 4 + 3 + CT + CG), max (Fm.x1 + 1) (max a1 (max a2 (max a3 (max a4 a5)))), fun x hx i u => ?_⟩` and prove the remaining obligations. Establish `b0 : Fm.x1 < x` using `lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hx)`. Establish `c1` using `(le_max_right _ _).trans hx`. Establish `b1 : x ≥ a1` using `(le_max_left _ _).trans c1`. Establish `c2` using `(le_max_right _ _).trans c1`.

Establish `b2 : x ≥ a2` using `(le_max_left _ _).trans c2`. Establish `c3` using `(le_max_right _ _).trans c2`. Establish `b3 : x ≥ a3` using `(le_max_left _ _).trans c3`. Establish `c4` using `(le_max_right _ _).trans c3`. Establish `b4 : x ≥ a4` using `(le_max_left _ _).trans c4`.

Establish `b5 : x ≥ a5` using `(le_max_right _ _).trans c4`. Take `⟨-, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -, -⟩` from `Fm.sizes x b0 i`. Conclude with `nprimeMuR_at (Fm.L x i) sQD sG (Fm.nprimeDef x b0 i) (hZ x b1 i) (fun u => ⟨hF x b2 i u, hR x b3 i u⟩) CT CG (hT x b4 i) (hG x b5 i) u`.
-/
theorem linkMu {eps : ℝ} (Fm : FamP eps) (hZ : MuZero Fm) (hF : MuFG Fm) (hR : MuRank Fm)
    (hT : MuTu Fm) (hG : MuDGam Fm) : LinkMu Fm := by
  obtain ⟨a1, hZ⟩ := hZ
  obtain ⟨a2, hF⟩ := hF
  obtain ⟨a3, hR⟩ := hR
  obtain ⟨CT, a4, hT⟩ := hT
  obtain ⟨CG, a5, hG⟩ := hG
  refine ⟨2 * (Real.log 4 + 3 + CT + CG),
    max (Fm.x1 + 1) (max a1 (max a2 (max a3 (max a4 a5)))), fun x hx i u => ?_⟩
  have b0 : Fm.x1 < x := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hx)
  have c1 := (le_max_right _ _).trans hx
  have b1 : x ≥ a1 := (le_max_left _ _).trans c1
  have c2 := (le_max_right _ _).trans c1
  have b2 : x ≥ a2 := (le_max_left _ _).trans c2
  have c3 := (le_max_right _ _).trans c2
  have b3 : x ≥ a3 := (le_max_left _ _).trans c3
  have c4 := (le_max_right _ _).trans c3
  have b4 : x ≥ a4 := (le_max_left _ _).trans c4
  have b5 : x ≥ a5 := (le_max_right _ _).trans c4
  obtain ⟨-, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -, -⟩ := Fm.sizes x b0 i
  exact nprimeMuR_at (Fm.L x i) sQD sG (Fm.nprimeDef x b0 i) (hZ x b1 i)
    (fun u => ⟨hF x b2 i u, hR x b3 i u⟩) CT CG (hT x b4 i) (hG x b5 i) u

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Conclude with `⟨2, x0, fun x hx i u => log_T_le (Fm.L x i) (hx0 x hx i) u⟩`.
-/
theorem muTu_of_sizeTu {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SizeTu (Fm.L x i)) : MuTu Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨2, x0, fun x hx i u => log_T_le (Fm.L x i) (hx0 x hx i) u⟩

/- English proof (translation)
Take `⟨C, x0, hC⟩` from `h`. Use `⟨|C| * 10, max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩` and prove the remaining obligations. Establish `hx0 : x0 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx1 : Fm.x1 < x`. Use `le_trans (le_max_right _ _) hx` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, hEta, hNodes, -⟩` from `Fm.sizes x hx1 i`. Conclude with `log_DGam_le (Fm.L x i) hN hEta hNodes C (hC x hx0 i) u`.
-/
theorem muDGam_of_fact {eps : ℝ} (Fm : FamP eps)
    (h : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, FactDGam (Fm.D x i) C) : MuDGam Fm := by
  obtain ⟨C, x0, hC⟩ := h
  refine ⟨|C| * 10, max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  obtain ⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, hEta, hNodes, -⟩ := Fm.sizes x hx1 i
  exact log_DGam_le (Fm.L x i) hN hEta hNodes C (hC x hx0 i) u

/- English proof (translation)
Unfold `LinkDIV at h`. Take `⟨C, x0, hx0⟩` from `h`. Use `⟨x0, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx0 x hx i`. Unfold `LinkDIV_at at h1`.

Conclude with `h1.2.2.1`.
-/
theorem muZero_of_linkDIV {eps : ℝ} (Fm : FamP eps) {Cabs CH : ℝ} (h : LinkDIV Fm Cabs CH) : MuZero Fm := by
  unfold LinkDIV at h
  obtain ⟨C, x0, hx0⟩ := h
  refine ⟨x0, fun x hx i => ?_⟩
  have h1 := hx0 x hx i
  unfold LinkDIV_at at h1
  exact h1.2.2.1

/- English proof (translation)
Establish `hF : MuFG Fm`. Take `⟨x0, hx0⟩` from `hN`. Use `⟨x0, fun x hx i u => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx0 x hx i`. Unfold `D7.NuFull at h1`.

Conclude with `(h1 u).1`. Conclude with `linkMu Fm (muZero_of_linkDIV Fm h) hF hR hT hG`.
-/
theorem linkMu_of_linkDIV {eps : ℝ} (Fm : FamP eps) {Cabs CH : ℝ} (h : LinkDIV Fm Cabs CH) (hN : NuFullF Fm)
    (hR : MuRank Fm) (hT : MuTu Fm) (hG : MuDGam Fm) : LinkMu Fm := by
  have hF : MuFG Fm := by
    obtain ⟨x0, hx0⟩ := hN
    refine ⟨x0, fun x hx i u => ?_⟩
    have h1 := hx0 x hx i
    unfold D7.NuFull at h1
    exact (h1 u).1
  exact linkMu Fm (muZero_of_linkDIV Fm h) hF hR hT hG

end Formalism.MainNotions.J

end
