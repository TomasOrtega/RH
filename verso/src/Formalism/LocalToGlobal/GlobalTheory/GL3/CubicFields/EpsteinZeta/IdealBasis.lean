import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Simplify using `[Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ib_im_conj_mul (u v : ℂ) : ((starRingEnd ℂ) u * v).im = u.re * v.im - u.im * v.re := by
  simp [Complex.mul_im]; ring

/- English proof (translation)
Rewrite `hw` using `[← h₀]`. Establish `hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range`. Unfold `latI`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨c, -, rfl⟩`.

Conclude with `⟨c, by simp⟩`. Take `⟨c, hc⟩` from `hle hw`. Conclude with `⟨c, hc⟩`.
-/
theorem ib_mem_range {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by
  rw [← h₀] at hw
  have hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range := by
    unfold latI
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, by simp⟩
  obtain ⟨c, hc⟩ := hle hw
  exact ⟨c, hc⟩

/- English proof (translation)
Take `⟨e, he⟩` from `ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))`. Take `⟨f, hf⟩` from `ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))`. Use `set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ`. Establish `hinj : Function.Injective ψ` using `φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)`. Establish `hli : LinearIndependent ℤ ![e, f]`.

Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0`. Use `congrArg ψ hst` as an intermediate fact. Simplify `this` using `[map_add, map_zsmul, he, hf, zsmul_eq_mul]`.

Rewrite `hab₀` using `[ib_im_conj_mul]`. Establish `hre` using `congrArg Complex.re h1`. Establish `him` using `congrArg Complex.im h1`. Simplify using `at hre him`. Prove the components needed by the constructor for the conclusion.

Establish `: (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0`. Take the linear combination `b₀.im * hre - b₀.re * him`. Conclude with `(mul_eq_zero.mp this).resolve_right hab₀.ne'` after adjusting the coercions. Establish `: (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0`. Take the linear combination `a₀.re * him - a₀.im * hre`.

Conclude with `(mul_eq_zero.mp this).resolve_right hab₀.ne'` after adjusting the coercions. Establish `hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f])`. Introduce `c _`. Establish `hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)`. Rewrite using `[← h₀]`.

Conclude with `AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩`. Take `⟨m, n, hmn⟩` from `AddSubgroup.mem_closure_pair.mp hc`. Establish `: c = m • e + n • f` using `hinj (by rw [← hmn]; simp [map_add, he, hf, zsmul_eq_mul])`. Rewrite using `[this]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))`.

Apply the tactic sequence `refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]`.
-/
theorem ib_exists_basis {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by
  obtain ⟨e, he⟩ := ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))
  obtain ⟨f, hf⟩ := ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  have hinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hli : LinearIndependent ℤ ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0 := by
      have := congrArg ψ hst
      simpa [map_add, map_zsmul, he, hf, zsmul_eq_mul] using this
    rw [ib_im_conj_mul] at hab₀
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    constructor
    · have : (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination b₀.im * hre - b₀.re * him
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
    · have : (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination a₀.re * him - a₀.im * hre
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f]) := by
    intro c _
    have hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ) := by
      rw [← h₀]
      exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hc
    have : c = m • e + n • f := hinj (by rw [← hmn]; simp [map_add, he, hf, zsmul_eq_mul])
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]

/- English proof (translation)
Establish `hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀`. Introduce `j`. Use `conv_lhs => rw [← B.sum_repr (v j)]`. Simplify using `[Fin.sum_univ_two, map_add, hB0, hB1, zsmul_eq_mul]`. Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]`.

Simplify using `only [Module.Basis.toMatrix_apply, ib_im_conj_mul]`. Use `push_cast`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ib_im_det {K : Type} [Field K] [NumberField K] (ψ : 𝓞 K →+* ℂ) (a₀ b₀ : ℂ)
    (B : Module.Basis (Fin 2) ℤ (𝓞 K)) (hB0 : ψ (B 0) = a₀) (hB1 : ψ (B 1) = b₀)
    (v : Fin 2 → 𝓞 K) :
    ((starRingEnd ℂ) (ψ (v 0)) * ψ (v 1)).im = (B.det v : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  have hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀ := by
    intro j
    conv_lhs => rw [← B.sum_repr (v j)]
    simp [Fin.sum_univ_two, map_add, hB0, hB1, zsmul_eq_mul]
  rw [Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]
  simp only [Module.Basis.toMatrix_apply, ib_im_conj_mul]
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring

/- English proof (translation)
Use `set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ`. Take `⟨B, hB0, hB1⟩` from `ib_exists_basis φ a₀ b₀ hab₀ h₀`. Use `set bI := Ideal.selfBasis B 𝔞 h𝔞`. Establish `hdet` using `Ideal.natAbs_det_basis_change B 𝔞 bI`. Use `set D := B.det ((↑) ∘ bI) with hD`.

Establish `hD0 : D ≠ 0`. Introduce `h`. Rewrite `hdet` using `[h, Int.natAbs_zero]`. Conclude with `h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)`. Establish `hcross` using `ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)`.

Rewrite `hcross` using `[← hD]`. Simplify using `only [Function.comp_apply] at hcross`. Establish `hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)|`. Rewrite using `[← hdet, Nat.cast_natAbs, Int.cast_abs]`. Establish `hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)}`.

Apply `le_antisymm` to reduce the goal to its premises. Unfold `latI`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]`.

Establish `hs` using `bI.sum_repr ⟨c, hc⟩`. Establish `hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K)`. Establish `h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c` using `by rw [hs]`. Rewrite `h2` using `[Fin.sum_univ_two]`. Conclude with `h2.symm`.

Use `⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩` and prove the remaining obligations. Use `show _ = ψ c`. Use `conv_rhs => rw [hc']`. Simplify using `[map_add]`. Rewrite using `[AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]`.

Conclude with `⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩, AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩`. Break down `lt_or_gt_of_ne hD0 with hneg | hpos` into its components or cases. Establish `hneg' : (D : ℝ) < 0` using `by exact_mod_cast hneg`. Establish `hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im = -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im`. Rewrite using `[ib_im_conj_mul, ib_im_conj_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩` and prove the remaining obligations. Rewrite using `[hsw, hcross]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hsw, hcross, hN, abs_of_neg hneg']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpos' : (0 : ℝ) < D` using `by exact_mod_cast hpos`. Use `⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩` and prove the remaining obligations. Rewrite using `[hcross]`. Check the signs of the components of the expression.

Rewrite using `[hcross, hN, abs_of_pos hpos']`.
-/
theorem latI_basis (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  obtain ⟨B, hB0, hB1⟩ := ib_exists_basis φ a₀ b₀ hab₀ h₀
  set bI := Ideal.selfBasis B 𝔞 h𝔞
  have hdet := Ideal.natAbs_det_basis_change B 𝔞 bI
  set D := B.det ((↑) ∘ bI) with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)
  have hcross := ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)
  rw [← hD] at hcross
  simp only [Function.comp_apply] at hcross
  have hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)| := by
    rw [← hdet, Nat.cast_natAbs, Int.cast_abs]
  have hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)} := by
    apply le_antisymm
    · unfold latI
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
      have hs := bI.sum_repr ⟨c, hc⟩
      have hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K) := by
        have h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c := by rw [hs]
        rw [Fin.sum_univ_two] at h2
        exact h2.symm
      refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
      show _ = ψ c
      conv_rhs => rw [hc']
      simp [map_add]
    · rw [AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩,
        AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · have hneg' : (D : ℝ) < 0 := by exact_mod_cast hneg
    have hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im =
        -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im := by
      rw [ib_im_conj_mul, ib_im_conj_mul]; ring
    refine ⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩
    · rw [hsw, hcross]; nlinarith
    · rw [hsw, hcross, hN, abs_of_neg hneg']; ring
  · have hpos' : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩
    · rw [hcross]; positivity
    · rw [hcross, hN, abs_of_pos hpos']

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
