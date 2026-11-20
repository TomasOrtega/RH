import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNegStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitActionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

/- English proof (translation)
Simplify using `[eig, sub_eq_zero]`.
-/
theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] {ρ : O → V →ₗ[K] V} {χ : O → K} {x : V} :
    x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eig, sub_eq_zero]

/- English proof (translation)
Introduce `K _ p _ _ d O ρ χ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[mem_eig]`. Use `set K0 := (frobenius K p).fieldRange with hK0`.

Set `β` to `Module.Basis.ofVectorSpace K0 K`. Establish `hpow : ∀ c : K, c ^ p ∈ K0` using `fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩`. Establish `hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι`. Introduce `c u ι`. Establish `h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u` using `rfl`.

Rewrite using `[h0, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K)`. Introduce `ι f`. Simplify using `[map_sum, Finsupp.finset_sum_apply]`.

Set `z : _ → Fin d → K` to `fun ι j => (β.repr (y j) ι : K)`. Establish `hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r`. Introduce `ι a r`. Establish `h1` using `congrFun (hy a) r`. Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1`.

Establish `h2` using `congrArg (fun u => (β.repr u ι : K)) h1`. Simplify using `only [hsum, hrepr] at h2`. Conclude with `h2`. Establish `hex : ∀ ι j, ∃ x : K, x ^ p = z ι j`. Introduce `ι j`.

Take `⟨x, hx⟩` from `RingHom.mem_fieldRange.1 (β.repr (y j) ι).2`. Conclude with `⟨x, by rw [← frobenius_def]; exact hx⟩`. Use `choose x hx using hex`. Establish `hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ`. Introduce `ι`.

Rewrite using `[mem_eig]`. Introduce `a`. Use function extensionality and compare the values at `r`. Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]`. Apply `frobenius_inj K p` to reduce the goal to its premises.

Rewrite using `[frobenius_def, frobenius_def, sum_pow_char, mul_pow]`. Simplify using `only [mul_pow, hx]`. Conclude with `hz ι a r`. Set `T` to `Finset.univ.biUnion fun j => (β.repr (y j)).support`. Establish `hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι)`.

Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply]`. Use `conv_lhs => rw [← β.linearCombination_repr (y j)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]`. Use `Finset.sum_congr rfl fun ι _ => ?_` and prove the remaining obligations.

Use `show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p`. Rewrite using `[hx ι j, mul_comm]`. Rewrite using `[hT, frobSub]`. Conclude with `Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)`. Rewrite using `[frobSub, Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_eig]`. Rewrite `hx` using `[SetLike.mem_coe, mem_eig]`. Introduce `a`. Establish `hxa` using `hx a`.

Simplify using `only [Matrix.toLin'_apply] at hxa ⊢`. Use function extensionality and compare the values at `r`. Establish `h1` using `congrFun hxa r`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢`. Rewrite using `[← mul_pow, ← h1, sum_pow_char]`.

Simplify using `only [mul_pow]`.
-/
theorem eig_frob : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  intro K _ p _ _ d O ρ χ
  apply le_antisymm
  · classical
    intro y hy
    rw [mem_eig] at hy
    set K0 := (frobenius K p).fieldRange with hK0
    let β := Module.Basis.ofVectorSpace K0 K
    have hpow : ∀ c : K, c ^ p ∈ K0 := fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩
    have hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι := by
      intro c u ι
      have h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u := rfl
      rw [h0, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K) := by
      intro ι f
      simp [map_sum, Finsupp.finset_sum_apply]
    let z : _ → Fin d → K := fun ι j => (β.repr (y j) ι : K)
    have hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r := by
      intro ι a r
      have h1 := congrFun (hy a) r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := congrArg (fun u => (β.repr u ι : K)) h1
      simp only [hsum, hrepr] at h2
      exact h2
    have hex : ∀ ι j, ∃ x : K, x ^ p = z ι j := by
      intro ι j
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (β.repr (y j) ι).2
      exact ⟨x, by rw [← frobenius_def]; exact hx⟩
    choose x hx using hex
    have hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ := by
      intro ι
      rw [mem_eig]
      intro a
      funext r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      apply frobenius_inj K p
      rw [frobenius_def, frobenius_def, sum_pow_char, mul_pow]
      simp only [mul_pow, hx]
      exact hz ι a r
    let T := Finset.univ.biUnion fun j => (β.repr (y j)).support
    have hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι) := by
      funext j
      rw [Finset.sum_apply]
      conv_lhs => rw [← β.linearCombination_repr (y j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p
      rw [hx ι j, mul_comm]
    rw [hT, frobSub]
    exact Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)
  · rw [frobSub, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eig]
    rw [SetLike.mem_coe, mem_eig] at hx
    intro a
    have hxa := hx a
    simp only [Matrix.toLin'_apply] at hxa ⊢
    funext r
    have h1 := congrFun hxa r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢
    rw [← mul_pow, ← h1, sum_pow_char]
    simp only [mul_pow]

/- English proof (translation)
Introduce `K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s`. Set `ρL : O →+* Module.End K (Fin d → K)` to `(Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ`. Take `⟨e, he_hom, he_mem, he_id, -, he_comb⟩` from `GlobalTheory.T.eigen_projectors_split_action K C (Fin d → K) L O k S χ hχ hv ρL hL hρ`. Take `⟨m, c, b, hc, hes⟩` from `he_comb s`. Use `set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW`.

Use `set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'`. Use `set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE`. Establish `hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j))`. Rewrite using `[hE, map_sum]`. Simplify using `only [map_smul]`.

Establish `hlinT : Matrix.toLin' E.transpose = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose`. Rewrite using `[hE, Matrix.transpose_sum, map_sum]`. Simplify using `only [Matrix.transpose_smul, map_smul]`. Establish `heE : ∀ x, e s x = E.mulVec x`. Introduce `x`.

Rewrite using `[← Matrix.toLin'_apply, hlin, hes]`. Both sides reduce to the same expression. Establish `hEW : ∀ x, E.mulVec x ∈ W` using `fun x => heE x ▸ he_mem s x`. Establish `hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i` using `fun i x hx => heE x ▸ he_hom s i x hx`. Establish `hEid : ∀ x ∈ W, E.mulVec x = x` using `fun x hx => (heE x).symm.trans (he_id s x hx)`.

Establish `hETid : ∀ y ∈ W', E.transpose.mulVec y = y`. Introduce `y hy`. Simplify using `only [hW', mem_eig, Matrix.toLin'_apply] at hy`. Rewrite using `[← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum]`.

Rewrite using `[hc s, if_pos rfl, map_one, one_smul]`. Establish `hETW : ∀ z, E.transpose.mulVec z ∈ W'`. Introduce `z`. Rewrite using `[hW', mem_eig]`. Introduce `a`.

Establish `hmat : ρ a * E = algebraMap k K (χ s a) • E`. Use `Matrix.toLin'.injective (LinearMap.ext fun w => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`. Establish `h1` using `(mem_eig.1 (hEW w)) a`. Simplify `h1` using `only [Matrix.toLin'_apply]`.

Establish `h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose`. Establish `hcm : E * ρ a = ρ a * E`. Rewrite using `[hE, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]`.

Rewrite using `[← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]`. Use `show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) = algebraMap k K (χ s a) • E.transpose.mulVec z`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]`. Establish `hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y`. Introduce `x y`.

Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`. Set `B : W →ₗ[K] W' →ₗ[K] K` to `(dotProductBilin K K).compl₁₂ W.subtype W'.subtype`. Establish `hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K)` using `fun x y => rfl`. Establish `hinj : Function.Injective B`. Use `(injective_iff_map_eq_zero B).2 fun x hx => ?_` and prove the remaining obligations.

Establish `h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0`. Introduce `z`. Establish `h1 : B x ⟨_, hETW z⟩ = 0` using `by rw [hx]; rfl`. Rewrite `h1` using `[hB]`. Express the relevant statement in the definitionally equal form `(x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1`.

Rewrite `h1` using `[hadj, hEid _ x.2]`. Then use the resulting hypothesis. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `using h0 (Pi.single j 1)`. Establish `hinj2 : Function.Injective B.flip`.

Use `(injective_iff_map_eq_zero B.flip).2 fun y hy => ?_` and prove the remaining obligations. Establish `h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0`. Introduce `z`. Establish `h1 : B.flip y ⟨_, hEW z⟩ = 0` using `by rw [hy]; rfl`. Rewrite `h1` using `[LinearMap.flip_apply, hB]`.

Express the relevant statement in the definitionally equal form `E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1`. Rewrite `h1` using `[← hadj, hETid _ y.2]`. Then use the resulting hypothesis. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `using h0 (Pi.single j 1)`.

Establish `hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W'` using `Subspace.dual_finrank_eq`. Establish `hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W` using `Subspace.dual_finrank_eq`. Establish `hle1` using `LinearMap.finrank_le_finrank_of_injective hinj`. Establish `hle2` using `LinearMap.finrank_le_finrank_of_injective hinj2`. Establish `hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K)` using `by omega`.

Establish `hbij : Function.Bijective B` using `⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩`. Take `⟨-, hdeg, -⟩` from `GlobalTheory.T.dual_lattice_degree_neg K C W W' (sub C L W) B (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1 hbij`. Establish `hident : dualLat C (sub C L W) B = sub C (dotDual C L) W'`. Use function extensionality and compare the values at `i`. Use extensionality with `y`.

Use `show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y`. Rewrite using `[hB]`.

Use `show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)`. Rewrite using `[← hadj, hETid _ y.2]`. Rewrite using `[hxy]`. Conclude with `h _ (hEL i x hx)`. Introduce `h x hx`.

Conclude with `h x hx`. Use `show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)`. Rewrite using `[← hident]`. Conclude with `hdeg`.
-/
theorem eig_dual : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s
  let ρL : O →+* Module.End K (Fin d → K) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ
  obtain ⟨e, he_hom, he_mem, he_id, -, he_comb⟩ :=
    GlobalTheory.T.eigen_projectors_split_action K C (Fin d → K) L O k S χ hχ hv ρL hL hρ
  obtain ⟨m, c, b, hc, hes⟩ := he_comb s
  set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW
  set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'
  set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE
  have hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)) := by
    rw [hE, map_sum]
    simp only [map_smul]
  have hlinT : Matrix.toLin' E.transpose =
      ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose := by
    rw [hE, Matrix.transpose_sum, map_sum]
    simp only [Matrix.transpose_smul, map_smul]
  have heE : ∀ x, e s x = E.mulVec x := by
    intro x
    rw [← Matrix.toLin'_apply, hlin, hes]
    rfl
  have hEW : ∀ x, E.mulVec x ∈ W := fun x => heE x ▸ he_mem s x
  have hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i := fun i x hx => heE x ▸ he_hom s i x hx
  have hEid : ∀ x ∈ W, E.mulVec x = x := fun x hx => (heE x).symm.trans (he_id s x hx)
  have hETid : ∀ y ∈ W', E.transpose.mulVec y = y := by
    intro y hy
    simp only [hW', mem_eig, Matrix.toLin'_apply] at hy
    rw [← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul,
      ← Finset.sum_smul, ← map_sum]
    rw [hc s, if_pos rfl, map_one, one_smul]
  have hETW : ∀ z, E.transpose.mulVec z ∈ W' := by
    intro z
    rw [hW', mem_eig]
    intro a
    have hmat : ρ a * E = algebraMap k K (χ s a) • E := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec]
      have h1 := (mem_eig.1 (hEW w)) a
      simpa only [Matrix.toLin'_apply] using h1
    have h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose := by
      have hcm : E * ρ a = ρ a * E := by
        rw [hE, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]
      rw [← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]
    show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) =
      algebraMap k K (χ s a) • E.transpose.mulVec z
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul,
      LinearMap.smul_apply, Matrix.toLin'_apply]
  have hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  let B : W →ₗ[K] W' →ₗ[K] K := (dotProductBilin K K).compl₁₂ W.subtype W'.subtype
  have hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K) := fun x y => rfl
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun x hx => ?_
    have h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0 := by
      intro z
      have h1 : B x ⟨_, hETW z⟩ = 0 := by rw [hx]; rfl
      rw [hB] at h1
      change (x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1
      rwa [hadj, hEid _ x.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hinj2 : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    have h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0 := by
      intro z
      have h1 : B.flip y ⟨_, hEW z⟩ = 0 := by rw [hy]; rfl
      rw [LinearMap.flip_apply, hB] at h1
      change E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1
      rwa [← hadj, hETid _ y.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W' := Subspace.dual_finrank_eq
  have hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  have hle1 := LinearMap.finrank_le_finrank_of_injective hinj
  have hle2 := LinearMap.finrank_le_finrank_of_injective hinj2
  have hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K) := by omega
  have hbij : Function.Bijective B :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩
  obtain ⟨-, hdeg, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C W W' (sub C L W) B (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1 hbij
  have hident : dualLat C (sub C L W) B = sub C (dotDual C L) W' := by
    funext i
    ext y
    show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1
    constructor
    · intro h x hx
      have hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y := by
        rw [hB]
        show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)
        rw [← hadj, hETid _ y.2]
      rw [hxy]
      exact h _ (hEL i x hx)
    · intro h x hx
      exact h x hx
  show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)
  rw [← hident]
  exact hdeg

end PositivityTheory.HtPt.Ci
