import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeKernelAddImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRankAdditiveExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeStdSublatticeNonposStatement
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.TorusSlope

open scoped Matrix

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right, Finset.sum_mul, Complex.star_def]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem gram_comb_rect {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) {r n : ℕ} (e : Fin r → V) (c : Matrix (Fin r) (Fin n) K) :
    h.gram σ (fun j => ∑ i, c i j • e i) = (c.map σ)ᴴ * h.gram σ e * c.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `K _ _ m r h ε C hC hε hG W hW`. Set `b` to `Module.Basis.span hε`. Take `⟨φ, hφ⟩` from `LinearMap.exists_extend (b.equivFun.toLinearMap)`. Establish `hφb : ∀ y : Submodule.span K (Set.range ε), φ y = b.equivFun y` using `fun y => LinearMap.congr_fun hφ y`. Establish `hb : ∀ i, (b i : Fin m → K) = ε i` using `fun i => by`.

Simplify using `[b, Module.Basis.span_apply]`. Establish `hφε : ∀ i, φ (ε i) = Pi.single i 1`. Introduce `i`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `j`.

Rewrite using `[b.equivFun_self i j, Pi.single_apply]`. Simplify using `[eq_comm]`. Establish `hrec : ∀ x ∈ Submodule.span K (Set.range ε), x = ∑ k, φ x k • ε k`. Introduce `x hx`. Establish `h3` using `congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hb] at h3`. Establish `h2` using `hφb ⟨x, hx⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hWK : ∀ x ∈ W, x ∈ Submodule.span K (Set.range ε)` using `fun x hx => Submodule.span_le_restrictScalars (𝓞 K) K _ (hW hx)`. Establish `hWfg : W.FG`.

Establish `hS : (Submodule.span (𝓞 K) (Set.range ε)).FG` using `Submodule.fg_span (Set.finite_range _)`. Use `haveI : IsNoetherian (𝓞 K) (Submodule.span (𝓞 K) (Set.range ε)) := isNoetherian_of_fg_of_noetherian _ hS`. Establish `h2` using `(IsNoetherian.noetherian (W.comap (Submodule.span (𝓞 K) (Set.range ε)).subtype)).map (Submodule.span (𝓞 K) (Set.range ε)).subtype`. Rewrite `h2` using `[Submodule.map_comap_eq_of_le (by simpa using hW)]`. Then use the resulting hypothesis. Establish `hpsd : ∀ (σ : K →+* ℂ) (n : ℕ) (v : Fin n → Fin m → K), (∀ i, v i ∈ W) → ((C : ℂ) • h.gram σ v - (stdHerm K r).gram σ (φ ∘ v)).PosSemidef`.

Introduce `σ n v hv`. Set `c : Matrix (Fin r) (Fin n) K` to `Matrix.of fun k j => φ (v j) k`. Establish `hv' : v = fun j => ∑ k, c k j • ε k`. Use function extensionality and compare the values at `j`. Conclude with `hrec (v j) (hWK _ (hv j))`.

Establish `h1 : h.gram σ v = (c.map σ)ᴴ * h.gram σ ε * c.map σ` using `(congrArg (h.gram σ) hv').trans (gram_comb_rect h σ ε c)`. Establish `h2 : (stdHerm K r).gram σ (φ ∘ v) = (c.map σ)ᴴ * c.map σ`. Use extensionality with `i j`. Simplify using `[HermFam.gram, stdHerm, Matrix.mul_apply, Matrix.conjTranspose_apply, c]`. Rewrite using `[h1, h2]`.

Establish `h4 : (C : ℂ) • ((c.map σ)ᴴ * h.gram σ ε * c.map σ) - (c.map σ)ᴴ * c.map σ = (c.map σ)ᴴ * ((C : ℂ) • h.gram σ ε - 1) * c.map σ`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Rewrite using `[h4]`. Conclude with `(hG σ).conjTranspose_mul_mul_same _`. Establish `hker : W ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨hxW, hxk⟩` from `Submodule.mem_inf.mp hx`. Establish `hx0 : φ x = 0` using `by simpa using hxk`. Rewrite using `[Submodule.mem_bot, hrec x (hWK _ hxW), hx0]`.

Simplify using the standard rewrite rules. Establish `himg : W.map (φ.restrictScalars (𝓞 K)) ≤ stdLat K r`. Use `(Submodule.map_mono hW).trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`.

Use `show (φ.restrictScalars (𝓞 K)) (ε i) ∈ Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i 1 : Fin r → K))`. Conclude with `Submodule.subset_span ⟨i, by simp [hφε]⟩`. Establish `hext` using `GlobalTheory.T.degree_le_kernel_add_image K m r h (stdHerm K r) φ C hC W hWfg hpsd`. Establish `hrk` using `GlobalTheory.T.lattice_rank_additive_exact K m r φ W`. Establish `hstd` using `GlobalTheory.T.degree_std_sublattice_nonpos K r _ himg`.

Rewrite `hext` using `[hker, HadamardFrameExtension.deg_bot]`. Rewrite `hrk` using `[hker]`. Simplify using `only [HadamardFrameExtension.latRank_bot, zero_add] at hrk`. Rewrite using `[hrk]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_le_half_log : ∀ (K : Type) [Field K] [NumberField K] (m r : ℕ) (h : HermFam K (Fin m → K)) (ε : Fin r → Fin m → K) (C : ℝ), 0 < C → LinearIndependent K ε → (∀ σ : K →+* ℂ, ((C : ℂ) • h.gram σ ε - 1).PosSemidef) → ∀ W : Submodule (𝓞 K) (Fin m → K), W ≤ Submodule.span (𝓞 K) (Set.range ε) → deg h W ≤ (latRank K W : ℝ) / 2 * Real.log C := by
  intro K _ _ m r h ε C hC hε hG W hW
  classical
  let b := Module.Basis.span hε
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.equivFun.toLinearMap)
  have hφb : ∀ y : Submodule.span K (Set.range ε), φ y = b.equivFun y := fun y =>
    LinearMap.congr_fun hφ y
  have hb : ∀ i, (b i : Fin m → K) = ε i := fun i => by
    simp [b, Module.Basis.span_apply]
  have hφε : ∀ i, φ (ε i) = Pi.single i 1 := by
    intro i
    calc φ (ε i) = φ (b i) := by rw [hb]
      _ = b.equivFun (b i) := hφb _
      _ = Pi.single i 1 := by
        funext j
        rw [b.equivFun_self i j, Pi.single_apply]
        simp [eq_comm]
  have hrec : ∀ x ∈ Submodule.span K (Set.range ε), x = ∑ k, φ x k • ε k := by
    intro x hx
    have h3 := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hb] at h3
    have h2 := hφb ⟨x, hx⟩
    calc x = ∑ i, b.equivFun ⟨x, hx⟩ i • ε i := h3.symm
      _ = ∑ k, φ x k • ε k := by rw [← h2]
  have hWK : ∀ x ∈ W, x ∈ Submodule.span K (Set.range ε) := fun x hx =>
    Submodule.span_le_restrictScalars (𝓞 K) K _ (hW hx)
  have hWfg : W.FG := by
    have hS : (Submodule.span (𝓞 K) (Set.range ε)).FG := Submodule.fg_span (Set.finite_range _)
    haveI : IsNoetherian (𝓞 K) (Submodule.span (𝓞 K) (Set.range ε)) :=
      isNoetherian_of_fg_of_noetherian _ hS
    have h2 := (IsNoetherian.noetherian
      (W.comap (Submodule.span (𝓞 K) (Set.range ε)).subtype)).map
      (Submodule.span (𝓞 K) (Set.range ε)).subtype
    rwa [Submodule.map_comap_eq_of_le (by simpa using hW)] at h2
  have hpsd : ∀ (σ : K →+* ℂ) (n : ℕ) (v : Fin n → Fin m → K), (∀ i, v i ∈ W) →
      ((C : ℂ) • h.gram σ v - (stdHerm K r).gram σ (φ ∘ v)).PosSemidef := by
    intro σ n v hv
    let c : Matrix (Fin r) (Fin n) K := Matrix.of fun k j => φ (v j) k
    have hv' : v = fun j => ∑ k, c k j • ε k := by
      funext j
      exact hrec (v j) (hWK _ (hv j))
    have h1 : h.gram σ v = (c.map σ)ᴴ * h.gram σ ε * c.map σ :=
      (congrArg (h.gram σ) hv').trans (gram_comb_rect h σ ε c)
    have h2 : (stdHerm K r).gram σ (φ ∘ v) = (c.map σ)ᴴ * c.map σ := by
      ext i j
      simp [HermFam.gram, stdHerm, Matrix.mul_apply, Matrix.conjTranspose_apply, c]
    rw [h1, h2]
    have h4 : (C : ℂ) • ((c.map σ)ᴴ * h.gram σ ε * c.map σ) - (c.map σ)ᴴ * c.map σ =
        (c.map σ)ᴴ * ((C : ℂ) • h.gram σ ε - 1) * c.map σ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [h4]
    exact (hG σ).conjTranspose_mul_mul_same _
  have hker : W ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxk⟩ := Submodule.mem_inf.mp hx
    have hx0 : φ x = 0 := by simpa using hxk
    rw [Submodule.mem_bot, hrec x (hWK _ hxW), hx0]
    simp
  have himg : W.map (φ.restrictScalars (𝓞 K)) ≤ stdLat K r := by
    refine (Submodule.map_mono hW).trans ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show (φ.restrictScalars (𝓞 K)) (ε i) ∈
      Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i 1 : Fin r → K))
    exact Submodule.subset_span ⟨i, by simp [hφε]⟩
  have hext := GlobalTheory.T.degree_le_kernel_add_image K m r h (stdHerm K r) φ C hC W hWfg hpsd
  have hrk := GlobalTheory.T.lattice_rank_additive_exact K m r φ W
  have hstd := GlobalTheory.T.degree_std_sublattice_nonpos K r _ himg
  rw [hker, HadamardFrameExtension.deg_bot] at hext
  rw [hker] at hrk
  simp only [HadamardFrameExtension.latRank_bot, zero_add] at hrk
  rw [hrk]
  linarith

end GlobalTheory.TorusSlope
