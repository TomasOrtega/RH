import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDual

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann

section Core

open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.SelfDual Topology

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨hlc, hsc, ht2, hOc, hOo, hden, hint, hnb, hcp, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hall : ∀ z : A F, ψf (z * y) = 1`. Introduce `z`. Establish `hcl : IsClosed {z : A F | ψf (z * y) = 1}` using `isClosed_eq (hψ.1.comp (continuous_id.mul continuous_const)) continuous_const`. Conclude with `hden.induction_on (p := fun z => ψf (z * y) = 1) z hcl hy`.

Establish `hMc : IsCompact (MG ψf : Set (A F))`. Use `isCompact_of_relIndex (ohG_le_MG hψ) ?_ hOc` and prove the remaining obligations. Rewrite using `[relIndex_MG hψ]`. Conclude with `Int.natAbs_ne_zero.2 (discr_ne_zero F)`. Take `⟨N, hN, hNK⟩` from `hcp _ hMc`.

Establish `hinv : ∀ m : ℕ, 0 < m → (m : A F) * algebraMap F (A F) (m : F)⁻¹ = 1`. Introduce `m hm`. Establish `hm' : (m : F) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Rewrite using `[← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hm', map_one]`. Establish `hmul : ∀ m : ℕ, 0 < m → algebraMap F (A F) (m : F)⁻¹ * ((N : A F) * y) ∈ Oh F`.

Introduce `m hm`. Establish `h1 : algebraMap F (A F) (m : F)⁻¹ * y ∈ MG ψf`. Introduce `z _`. Use `show ψf (z * _) = 1`. Rewrite using `[← mul_assoc]`.

Conclude with `hall _`. Establish `h2` using `hNK _ h1`. Rewrite `h2` using `[mul_left_comm]`. Then use the resulting hypothesis. Establish `hw : (N : A F) * y = 0`. Assume the negation of the conclusion as `hne`.

Establish `hU : ({(N : A F) * y}ᶜ : Set (A F)) ∈ 𝓝 (0 : A F)` using `isOpen_compl_singleton.mem_nhds (fun h => hne (Eq.symm h))`. Take `⟨m, hm, hmU⟩` from `hnb _ hU`. Apply `hmU _ (hmul m hm)` to reduce the goal to its premises. Rewrite using `[← mul_assoc, hinv m hm, one_mul]`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, mul_comm (algebraMap F (A F) _), hinv N hN, one_mul]`. Use `_ = 0 := by rw [hw, mul_zero]`.
-/
theorem fin_eq_zero (ψf : AddChar (A F) ℂ) (hψ : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {y : A F}
    (hy : ∀ t : F, ψf (algebraMap F (A F) t * y) = 1) : y = 0 := by
  obtain ⟨hlc, hsc, ht2, hOc, hOo, hden, hint, hnb, hcp, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hall : ∀ z : A F, ψf (z * y) = 1 := by
    intro z
    have hcl : IsClosed {z : A F | ψf (z * y) = 1} :=
      isClosed_eq (hψ.1.comp (continuous_id.mul continuous_const)) continuous_const
    exact hden.induction_on (p := fun z => ψf (z * y) = 1) z hcl hy
  have hMc : IsCompact (MG ψf : Set (A F)) := by
    refine isCompact_of_relIndex (ohG_le_MG hψ) ?_ hOc
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  obtain ⟨N, hN, hNK⟩ := hcp _ hMc
  have hinv : ∀ m : ℕ, 0 < m → (m : A F) * algebraMap F (A F) (m : F)⁻¹ = 1 := by
    intro m hm
    have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hm', map_one]
  have hmul : ∀ m : ℕ, 0 < m → algebraMap F (A F) (m : F)⁻¹ * ((N : A F) * y) ∈ Oh F := by
    intro m hm
    have h1 : algebraMap F (A F) (m : F)⁻¹ * y ∈ MG ψf := by
      intro z _
      show ψf (z * _) = 1
      rw [← mul_assoc]
      exact hall _
    have h2 := hNK _ h1
    rwa [mul_left_comm] at h2
  have hw : (N : A F) * y = 0 := by
    by_contra hne
    have hU : ({(N : A F) * y}ᶜ : Set (A F)) ∈ 𝓝 (0 : A F) :=
      isOpen_compl_singleton.mem_nhds (fun h => hne (Eq.symm h))
    obtain ⟨m, hm, hmU⟩ := hnb _ hU
    apply hmU _ (hmul m hm)
    rw [← mul_assoc, hinv m hm, one_mul]
    rfl
  calc y = algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * y) := by
        rw [← mul_assoc, mul_comm (algebraMap F (A F) _), hinv N hN, one_mul]
    _ = 0 := by rw [hw, mul_zero]

/- English proof (translation)
Establish `hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ))`. Introduce `w w' hww`. Establish `h1 : w.embedding = w'.embedding`. Use extensionality with `x`. Rewrite using `[← hρ, ← hρ]`.

Establish `: ρ w x = ρ w' x` using `DFunLike.congr_fun hww x`. Rewrite using `[this]`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1]`. Establish `hli` using `(linearIndependent_monoidHom F ℝ).comp _ hinj`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`.

Use `hli D ?_` and prove the remaining obligations. Use extensionality with `t`. Simplify `h t` using `[mul_comm]`.
-/
theorem coeff_eq_zero (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (D : InfinitePlace F → ℝ)
    (h : ∀ t : F, ∑ w, ρ w t * D w = 0) : ∀ w, D w = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      have : ρ w x = ρ w' x := DFunLike.congr_fun hww x
      rw [this]
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine hli D ?_
  ext t
  simpa [mul_comm] using h t

/- English proof (translation)
Use `set e := integralBasis F with he`. Establish `hXe : ∀ i, ∃ n : ℤ, ∑ w, ρ w (e i) * X w = n`. Introduce `i`. Take `⟨n, hn⟩` from `hX (RingOfIntegers.basis F i)`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hn, he, integralBasis_apply]`. Use `choose n hn using hXe`. Use `set c : F := e.traceDual.equivFun.symm (fun i => (n i : ℚ)) with hc`. Establish `hrepr : ∀ i, Algebra.trace ℚ F (c * e i) = n i`. Introduce `i`.

Establish `h1` using `Module.Basis.traceDual_repr_apply e c i`. Rewrite `h1` using `[Algebra.traceForm_apply]`. Rewrite using `[← h1, ← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]`. Use `⟨c, fun w => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ t : F, ∑ w, ρ w t * (ρ w c - X w) = 0`.

Set `Lf : F →ₗ[ℚ] ℝ` to `∑ w, (ρ w c - X w) • (ρ w).toRatAlgHom.toLinearMap`. Establish `hL : Lf = 0`. Use `e.ext fun i => ?_` and prove the remaining obligations. Establish `h2` using `GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ (c * e i)`. Rewrite `h2` using `[hrepr]`.

Simplify using `only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply]`. Simplify using `only [map_mul] at h2`. Establish `h3 : ∑ w, (ρ w c - X w) * ρ w (e i) = ∑ w, ρ w c * ρ w (e i) - ∑ w, ρ w (e i) * X w`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`.

Rewrite using `[h3, h2, hn]`. Simplify using the standard rewrite rules. Introduce `t`. Use `LinearMap.congr_fun hL t` as an intermediate fact. Simplify using `only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply] at this`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun w _ => mul_comm _ _`. Use `coeff_eq_zero ρ hρ _ hz w` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem real_eq_of_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (X : InfinitePlace F → ℝ)
    (hX : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * X w = n) : ∃ c : F, ∀ w, X w = ρ w c := by
  classical
  set e := integralBasis F with he
  have hXe : ∀ i, ∃ n : ℤ, ∑ w, ρ w (e i) * X w = n := by
    intro i
    obtain ⟨n, hn⟩ := hX (RingOfIntegers.basis F i)
    refine ⟨n, ?_⟩
    rw [← hn, he, integralBasis_apply]
  choose n hn using hXe
  set c : F := e.traceDual.equivFun.symm (fun i => (n i : ℚ)) with hc
  have hrepr : ∀ i, Algebra.trace ℚ F (c * e i) = n i := by
    intro i
    have h1 := Module.Basis.traceDual_repr_apply e c i
    rw [Algebra.traceForm_apply] at h1
    rw [← h1, ← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]
  refine ⟨c, fun w => ?_⟩
  have hz : ∀ t : F, ∑ w, ρ w t * (ρ w c - X w) = 0 := by
    let Lf : F →ₗ[ℚ] ℝ := ∑ w, (ρ w c - X w) • (ρ w).toRatAlgHom.toLinearMap
    have hL : Lf = 0 := by
      refine e.ext fun i => ?_
      have h2 := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ (c * e i)
      rw [hrepr] at h2
      simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
        AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply]
      simp only [map_mul] at h2
      have h3 : ∑ w, (ρ w c - X w) * ρ w (e i) = ∑ w, ρ w c * ρ w (e i) - ∑ w, ρ w (e i) * X w := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h3, h2, hn]
      simp
    intro t
    have := LinearMap.congr_fun hL t
    simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have := coeff_eq_zero ρ hρ _ hz w
  linarith

def eR (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

/- English proof (translation)
Simplify using `only [eR, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eR_add (s u : ℝ) : eR (s + u) = eR s * eR u := by
  simp only [eR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `[eR]`.
-/
theorem eR_zero : eR 0 = 1 := by simp [eR]

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : (s : ℂ) = n`. Use `mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_` and prove the remaining obligations. Rewrite using `[hn]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h1` after adjusting the coercions.
-/
theorem eR_int {s : ℝ} (h : eR s = 1) : ∃ n : ℤ, s = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h1 : (s : ℂ) = n := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [hn]
    ring
  exact_mod_cast h1

/- English proof (translation)
Establish `hT : eR (∑ w, ρ w (t * c)) * ψf (algebraMap F (A F) (t * c)) = 1`. Rewrite using `[GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ, hstd.2, eR, ← Complex.exp_add]`. Establish `h0 : 2 * (Real.pi : ℂ) * Complex.I * (((Algebra.trace ℚ F (t * c) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℚ F (t * c) : ℚ) : ℂ) = 0`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h0, Complex.exp_zero]`. Establish `e1 : ∑ w, ρ w t * X w = ∑ w, ρ w t * (X w - ρ w c) + ∑ w, ρ w (t * c)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [map_mul]; ring`. Establish `e2 : algebraMap F (A F) t * y = algebraMap F (A F) t * (y - algebraMap F (A F) c) + algebraMap F (A F) (t * c)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `H t`. Rewrite `h` using `[e1, e2, eR_add, AddChar.map_add_eq_mul]`. Establish `key : ∀ p q r s : ℂ, (p * q) * (r * s) = 1 → q * s = 1 → p * r = 1` using `fun p q r s h1 h2 => by linear_combination h1 - p * r * h2`.

Conclude with `key _ _ _ _ h hT`.
-/
theorem sub_field (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {X : InfinitePlace F → ℝ} {y : A F}
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) (c : F) (t : F) :
    eR (∑ w, ρ w t * (X w - ρ w c)) * ψf (algebraMap F (A F) t * (y - algebraMap F (A F) c)) = 1 := by
  have hT : eR (∑ w, ρ w (t * c)) * ψf (algebraMap F (A F) (t * c)) = 1 := by
    rw [GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ, hstd.2, eR, ← Complex.exp_add]
    have h0 : 2 * (Real.pi : ℂ) * Complex.I * (((Algebra.trace ℚ F (t * c) : ℚ) : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℚ F (t * c) : ℚ) : ℂ) = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero]
  have e1 : ∑ w, ρ w t * X w = ∑ w, ρ w t * (X w - ρ w c) + ∑ w, ρ w (t * c) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [map_mul]; ring
  have e2 : algebraMap F (A F) t * y =
      algebraMap F (A F) t * (y - algebraMap F (A F) c) + algebraMap F (A F) (t * c) := by
    rw [map_mul]
    ring
  have h := H t
  rw [e1, e2, eR_add, AddChar.map_add_eq_mul] at h
  have key : ∀ p q r s : ℂ, (p * q) * (r * s) = 1 → q * s = 1 → p * r = 1 :=
    fun p q r s h1 h2 => by linear_combination h1 - p * r * h2
  exact key _ _ _ _ h hT

/- English proof (translation)
Take `⟨-, -, -, -, hOo, hden, hint, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hopen : IsOpen {z : A F | y - z ∈ Oh F}` using `hOo.preimage (continuous_const.sub continuous_id)`. Take `⟨c1, hc1⟩` from `hden.exists_mem_open hopen ⟨y, by show y - y ∈ Oh F`. Rewrite using `[sub_self]`. Conclude with `(ohG F).zero_mem⟩`.

Establish `hc1' : y - algebraMap F (A F) c1 ∈ Oh F` using `hc1`. Establish `H1` using `sub_field hF ρ hρ ψf hstd H c1`. Establish `hXint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * (X w - ρ w c1) = n`. Introduce `r`. Establish `h1` using `H1 r`.

Rewrite `h1` using `[((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.1 _ (oh_mul ((hint _).2 ⟨r, rfl⟩) hc1'), mul_one]`. Conclude with `eR_int h1`. Take `⟨c2, hc2⟩` from `real_eq_of_int hF ρ hρ _ hXint`. Establish `H2` using `sub_field hF ρ hρ ψf hstd H1 c2`. Establish `hy0 : y - algebraMap F (A F) c1 - algebraMap F (A F) c2 = 0` using `fin_eq_zero ψf hstd fun t => by`.

Establish `h1` using `H2 t`. Establish `h0 : ∑ w, ρ w t * ((X w - ρ w c1) - ρ w c2) = 0` using `Finset.sum_eq_zero fun w _ => by rw [← hc2 w, sub_self, mul_zero]`. Rewrite `h1` using `[h0, eR_zero, one_mul]`. Then use the resulting hypothesis. Use `⟨c1 + c2, fun w => ?_, ?_⟩` and prove the remaining obligations. Use `hc2 w` as an intermediate fact.

Rewrite using `[map_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[map_add]`. Take the linear combination `hy0`.
-/
theorem core (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) (X : InfinitePlace F → ℝ) (y : A F)
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) :
    ∃ c : F, (∀ w, X w = ρ w c) ∧ y = algebraMap F (A F) c := by
  obtain ⟨-, -, -, -, hOo, hden, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hopen : IsOpen {z : A F | y - z ∈ Oh F} := hOo.preimage (continuous_const.sub continuous_id)
  obtain ⟨c1, hc1⟩ := hden.exists_mem_open hopen ⟨y, by
    show y - y ∈ Oh F
    rw [sub_self]
    exact (ohG F).zero_mem⟩
  have hc1' : y - algebraMap F (A F) c1 ∈ Oh F := hc1
  have H1 := sub_field hF ρ hρ ψf hstd H c1
  have hXint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * (X w - ρ w c1) = n := by
    intro r
    have h1 := H1 r
    rw [((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.1 _ (oh_mul ((hint _).2 ⟨r, rfl⟩) hc1'), mul_one] at h1
    exact eR_int h1
  obtain ⟨c2, hc2⟩ := real_eq_of_int hF ρ hρ _ hXint
  have H2 := sub_field hF ρ hρ ψf hstd H1 c2
  have hy0 : y - algebraMap F (A F) c1 - algebraMap F (A F) c2 = 0 := fin_eq_zero ψf hstd fun t => by
    have h1 := H2 t
    have h0 : ∑ w, ρ w t * ((X w - ρ w c1) - ρ w c2) = 0 :=
      Finset.sum_eq_zero fun w _ => by rw [← hc2 w, sub_self, mul_zero]
    rwa [h0, eR_zero, one_mul] at h1
  refine ⟨c1 + c2, fun w => ?_, ?_⟩
  · have := hc2 w
    rw [map_add]
    linarith
  · rw [map_add]
    linear_combination hy0

end Core

/- English proof (translation)
Introduce `F _ _ hF ψ hψ x hx`. Take `⟨ρ, e, hρ, he, heρ, -, -⟩` from `GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF`. Take `⟨a, ha, hinf, ψf, hstd, hfin⟩` from `GlobalTheory.T.adelic_character_archimedean_form F hF ρ e hρ he heρ ψ hψ`. Establish `hsplit : ∀ (u : Ainf F) (v : Af F), ψ (u, v) = eR (∑ w, ρ w a * e u w) * ψf (algebraMap F (Af F) a * v)`. Introduce `u v`.

Establish `h : ((u, v) : AF F) = pairA F u 0 + pairA F 0 v` using `by show ((u, v) : Ainf F × Af F) = ((u, 0) : Ainf F × Af F) + ((0, v) : Ainf F × Af F)`. Rewrite using `[Prod.mk_add_mk, add_zero, zero_add]`. Rewrite using `[h, AddChar.map_add_eq_mul, hinf, hfin]`. Both sides reduce to the same expression. Establish `H : ∀ t : F, eR (∑ w, ρ w t * (ρ w a * e x.1 w)) * ψf (algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)) = 1`.

Introduce `t`. Establish `h` using `hx t`. Establish `hm : algebraMap F (AF F) t * x = (algebraMap F (Ainf F) t * x.1, algebraMap F (Af F) t * x.2)` using `rfl`. Rewrite `h` using `[hm, hsplit]`. Establish `e1 : ∑ w, ρ w a * e (algebraMap F (Ainf F) t * x.1) w = ∑ w, ρ w t * (ρ w a * e x.1 w)` using `Finset.sum_congr rfl fun w _ => by rw [map_mul, Pi.mul_apply, heρ]; ring`.

Establish `e2 : algebraMap F (Af F) a * (algebraMap F (Af F) t * x.2) = algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)` using `mul_left_comm _ _ _`. Rewrite `h` using `[e1, e2]`. Conclude with `h`. Take `⟨c, hc1, hc2⟩` from `core hF ρ hρ ψf hstd _ _ H`. Use `⟨a⁻¹ * c, ?_⟩` and prove the remaining obligations.

Establish `hx1 : x.1 = algebraMap F (Ainf F) (a⁻¹ * c)`. Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Rewrite using `[heρ, map_mul, map_inv₀]`. Establish `hne : ρ w a ≠ 0` using `(map_ne_zero _).2 ha`.

Establish `h1` using `hc1 w`. Rewrite using `[← h1]`. Clear the denominators using the available nonvanishing facts. Establish `hx2 : x.2 = algebraMap F (Af F) (a⁻¹ * c)`. Rewrite using `[map_mul, ← hc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]`.

Conclude with `Prod.ext hx1 hx2`.
-/
theorem annihilator_eq : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  intro F _ _ hF ψ hψ x hx
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, hinf, ψf, hstd, hfin⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e hρ he heρ ψ hψ
  have hsplit : ∀ (u : Ainf F) (v : Af F),
      ψ (u, v) = eR (∑ w, ρ w a * e u w) * ψf (algebraMap F (Af F) a * v) := by
    intro u v
    have h : ((u, v) : AF F) = pairA F u 0 + pairA F 0 v := by
      show ((u, v) : Ainf F × Af F) = ((u, 0) : Ainf F × Af F) + ((0, v) : Ainf F × Af F)
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [h, AddChar.map_add_eq_mul, hinf, hfin]
    rfl
  have H : ∀ t : F, eR (∑ w, ρ w t * (ρ w a * e x.1 w)) *
      ψf (algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)) = 1 := by
    intro t
    have h := hx t
    have hm : algebraMap F (AF F) t * x =
        (algebraMap F (Ainf F) t * x.1, algebraMap F (Af F) t * x.2) := rfl
    rw [hm, hsplit] at h
    have e1 : ∑ w, ρ w a * e (algebraMap F (Ainf F) t * x.1) w = ∑ w, ρ w t * (ρ w a * e x.1 w) :=
      Finset.sum_congr rfl fun w _ => by rw [map_mul, Pi.mul_apply, heρ]; ring
    have e2 : algebraMap F (Af F) a * (algebraMap F (Af F) t * x.2) =
        algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2) := mul_left_comm _ _ _
    rw [e1, e2] at h
    exact h
  obtain ⟨c, hc1, hc2⟩ := core hF ρ hρ ψf hstd _ _ H
  refine ⟨a⁻¹ * c, ?_⟩
  have hx1 : x.1 = algebraMap F (Ainf F) (a⁻¹ * c) := by
    apply e.injective
    funext w
    rw [heρ, map_mul, map_inv₀]
    have hne : ρ w a ≠ 0 := (map_ne_zero _).2 ha
    have h1 := hc1 w
    rw [← h1]
    field_simp
  have hx2 : x.2 = algebraMap F (Af F) (a⁻¹ * c) := by
    rw [map_mul, ← hc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  exact Prod.ext hx1 hx2

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann
