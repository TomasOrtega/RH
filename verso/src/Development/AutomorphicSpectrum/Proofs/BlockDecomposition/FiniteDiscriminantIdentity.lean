import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGLStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniformStatement

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscP

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Use `⟨T.symm, fun o φ ψ e => ?_⟩` and prove the remaining obligations. Establish `hm : act o (T.symm φ).1 ∈ V` using `hV o _ (T.symm φ).2`. Establish `h1` using `hT o (T.symm φ) ⟨_, hm⟩ rfl`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply, ← e]`.

Establish `h2 : T ⟨_, hm⟩ = ψ` using `Subtype.ext h1`. Rewrite using `[← h2, LinearEquiv.symm_apply_apply]`.
-/
theorem isoV_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {V V' : Submodule ℂ (Sm E N)}
    (hV : IsStable V) (h : IsoV V V') : IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ).1 ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `E _ _ _ N _ _ μ _ K W R ε hK hW hε hRep`. Use `set D : Submodule ℂ (Sm E N) → Prop := fun V => IsDiscrete V ∧ HasType K W V ∧ InfBdd R V ∧ ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r)) with hD`. Distinguish the cases in `hne : ∃ V, D V`. Use `swap`. Conclude with `⟨∅, fun V h1 h2 h3 h4 => (hne ⟨V, h1, h2, h3, h4⟩).elim⟩`.

Take `⟨V₁, h₁⟩` from `hne`. Take `⟨F, hF⟩` from `GlobalTheory.T.exists_fundamental_domain_GL E N μ _ (h₁.1.sqInt 0 (zero_mem _))`. Take `⟨α, δ, hαc, hαs, hδ, hα⟩` from `hRep`. Take `⟨Ω, hΩ, hconc⟩` from `GlobalTheory.T.typed_space_approximation E N μ K W R ε δ α F hK hW hε hαc hαs hδ hF`. Take `⟨B, hB, hbes⟩` from `GlobalTheory.T.kernel_sum_bound_uniform E N μ δ α F Ω hαc hαs hδ hF hΩ`.

Establish `key : ∀ (n : ℕ) (Vs : Fin n → Submodule ℂ (Sm E N)), (∀ i, D (Vs i)) → (∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j)) → (n : ENNReal) ≤ 2 * B`. Introduce `n Vs hVs hne`. Establish `hsel : ∀ i, ∃ ψ : Sm E N, ψ ∈ Vs i ∧ TypeB K W ψ ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1`. Introduce `i`. Take `⟨hd, ⟨φ, hφ, h0, hty⟩, -, -⟩` from `hVs i`.

Take `⟨hT, hZ⟩` from `GlobalTheory.T.automorphic_norm_finite_nonzero E N μ F hF φ (hd.aut φ hφ) (hd.sqInt φ hφ) h0`. Use `set L := ∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ with hL`. Establish `hLr : 0 < L.toReal` using `ENNReal.toReal_pos hZ hT`. Use `set c : ℝ := (Real.sqrt L.toReal)⁻¹ with hc`. Establish `hc0 : 0 < c` using `inv_pos.2 (Real.sqrt_pos.2 hLr)`.

Use `⟨(c : ℂ) • φ, (Vs i).smul_mem _ hφ, ⟨fun u hu g => ?_, fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Use `hty.1 u hu g` as an intermediate fact. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, this]`. Conclude with `W.smul_mem (c : ℂ) (hty.2 g)`. Establish `e : ∀ x, ‖(((c : ℂ) • φ : Sm E N)).1 x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖φ.1 x‖ₑ ^ 2`.

Introduce `x`. Establish `h2 : ((((c : ℂ) • φ : Sm E N)).1 x) = (c : ℂ) * φ.1 x` using `rfl`. Rewrite using `[h2, enorm_mul, mul_pow]`. Use `congr 1`. Rewrite using `[← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, ENNReal.ofReal_pow hc0.le]`.

Simplify using `only [e]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL]`. Establish `: c ^ 2 = (L.toReal)⁻¹`. Rewrite using `[hc, inv_pow, Real.sq_sqrt hLr.le]`. Rewrite using `[this, ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_toReal hT]`.

Conclude with `ENNReal.inv_mul_cancel hZ hT`. Use `choose ψ hψV hψT hψ1 using hsel`. Establish `hcont : ∀ i, Continuous (ψ i).1` using `fun i => ContAut.continuous_of_isOpen_stab E N (ψ i) ((hVs i).1.aut _ (hψV i)).level`. Establish `hleft : ∀ i, ∀ γ ∈ latticeGL E N, ∀ x, (ψ i).1 (γ * x) = (ψ i).1 x`. Introduce `i γ hγ x`.

Take `⟨ρ, m, rfl⟩` from `GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ`. Establish `h1` using `((hVs i).1.sqInt _ (hψV i)).1`. Rewrite using `[mul_assoc, ((hVs i).1.aut _ (hψV i)).left, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast, h1]`. Establish `hs : ∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * (ψ i).1 (x * y) ∂μ = s * (ψ i).1 x`. Introduce `i`.

Use `hα (ψ i) ((hVs i).1.aut _ (hψV i)) (hψT i) fun τ => ?_` and prove the remaining obligations. Take `⟨m, hm, hb⟩` from `(hVs i).2.2.1 τ`. Use `⟨m, ⟨hm.1, fun u φ hφ => ?_⟩, hb⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Rewrite using `[map_smul, hm.2 u _ (hψV i), smul_comm]`.

Establish `hcB` using `hbes n (fun i => (ψ i).1) hcont hleft hs hψ1 (fun i j hij => GlobalTheory.T.orthogonal_of_non_isomorphic E N μ F hF (Vs i) (Vs j) (hVs i).1 (hVs j).1 (hne i j hij) _ (hψV i) _ (hψV j))`. Establish `h1 : ∀ i, 1 ≤ 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ` using `fun i => hconc (Vs i) (ψ i) (hVs i).1 (hψV i) (hψT i) (hVs i).2.2.1 (hVs i).2.2.2 (hs i) (hψ1 i)`. Combine the equalities or inequalities in the displayed calculation. Choose the witnesses or unpack the hypotheses as in `⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * B ≤ (n₀ : ENNReal) := by`. Establish `h2B : 2 * B ≠ ⊤` using `ENNReal.mul_ne_top (by simp) hB`.

Conclude with `ENNReal.exists_nat_gt h2B |>.imp fun _ h => h.le`. Use `set P : ℕ → Prop := fun n => ∃ Vs : Fin n → Submodule ℂ (Sm E N), (∀ i, D (Vs i)) ∧ ∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j) with hP`. Establish `hbd : ∀ n, P n → n ≤ n₀`. Introduce and unpack `n ⟨Vs, h1, h2⟩`. Conclude with `(key n Vs h1 h2).trans hn₀` after adjusting the coercions.

Establish `hP0 : P 0` using `⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Use `set n := Nat.findGreatest P n₀ with hn`. Take `⟨Vs, hVs, hpw⟩ : P n` from `Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0`. Use `⟨Finset.univ.image Vs, fun V h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hno`.

Establish `hDV : D V` using `⟨h1, h2, h3, h4⟩`. Establish `hno' : ∀ i, ¬ IsoV V (Vs i)` using `fun i hi => hno ⟨Vs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩`. Establish `hnext : P (n + 1)`. Use `⟨Fin.cons V Vs, fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hDV`. Simplify using `using hVs i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => exact (hij rfl).elim`. Consider the case `succ j => simpa using hno' j`. Consider the case `succ i`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `fun h => hno' i (isoV_symm (hVs i).1.stable h)`. Consider the case `succ j`. Simplify using `using hpw i j fun e => hij (by rw [e])`. Use `Nat.le_findGreatest (hbd _ hnext) hnext` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem main : FinDisc := by
  intro E _ _ _ N _ _ μ _ K W R ε hK hW hε hRep
  set D : Submodule ℂ (Sm E N) → Prop := fun V => IsDiscrete V ∧ HasType K W V ∧ InfBdd R V ∧
    ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r)) with hD
  by_cases hne : ∃ V, D V
  swap
  · exact ⟨∅, fun V h1 h2 h3 h4 => (hne ⟨V, h1, h2, h3, h4⟩).elim⟩
  obtain ⟨V₁, h₁⟩ := hne
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_fundamental_domain_GL E N μ _ (h₁.1.sqInt 0 (zero_mem _))
  obtain ⟨α, δ, hαc, hαs, hδ, hα⟩ := hRep
  obtain ⟨Ω, hΩ, hconc⟩ := GlobalTheory.T.typed_space_approximation E N μ K W R ε δ α F hK hW hε hαc hαs hδ hF
  obtain ⟨B, hB, hbes⟩ := GlobalTheory.T.kernel_sum_bound_uniform E N μ δ α F Ω hαc hαs hδ hF hΩ

  have key : ∀ (n : ℕ) (Vs : Fin n → Submodule ℂ (Sm E N)), (∀ i, D (Vs i)) →
      (∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j)) → (n : ENNReal) ≤ 2 * B := by
    intro n Vs hVs hne
    have hsel : ∀ i, ∃ ψ : Sm E N, ψ ∈ Vs i ∧ TypeB K W ψ ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 := by
      intro i
      obtain ⟨hd, ⟨φ, hφ, h0, hty⟩, -, -⟩ := hVs i
      obtain ⟨hT, hZ⟩ := GlobalTheory.T.automorphic_norm_finite_nonzero E N μ F hF φ (hd.aut φ hφ) (hd.sqInt φ hφ) h0
      set L := ∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ with hL
      have hLr : 0 < L.toReal := ENNReal.toReal_pos hZ hT
      set c : ℝ := (Real.sqrt L.toReal)⁻¹ with hc
      have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hLr)
      refine ⟨(c : ℂ) • φ, (Vs i).smul_mem _ hφ, ⟨fun u hu g => ?_, fun g => ?_⟩, ?_⟩
      · have := hty.1 u hu g
        simp only [Submodule.coe_smul, Pi.smul_apply, this]
      · exact W.smul_mem (c : ℂ) (hty.2 g)
      · have e : ∀ x, ‖(((c : ℂ) • φ : Sm E N)).1 x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖φ.1 x‖ₑ ^ 2 := by
          intro x
          have h2 : ((((c : ℂ) • φ : Sm E N)).1 x) = (c : ℂ) * φ.1 x := rfl
          rw [h2, enorm_mul, mul_pow]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
            ENNReal.ofReal_pow hc0.le]
        simp only [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL]
        have : c ^ 2 = (L.toReal)⁻¹ := by
          rw [hc, inv_pow, Real.sq_sqrt hLr.le]
        rw [this, ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_toReal hT]
        exact ENNReal.inv_mul_cancel hZ hT
    choose ψ hψV hψT hψ1 using hsel
    have hcont : ∀ i, Continuous (ψ i).1 := fun i =>
      ContAut.continuous_of_isOpen_stab E N (ψ i) ((hVs i).1.aut _ (hψV i)).level
    have hleft : ∀ i, ∀ γ ∈ latticeGL E N, ∀ x, (ψ i).1 (γ * x) = (ψ i).1 x := by
      intro i γ hγ x
      obtain ⟨ρ, m, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
      have h1 := ((hVs i).1.sqInt _ (hψV i)).1
      rw [mul_assoc, ((hVs i).1.aut _ (hψV i)).left, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast, h1]
    have hs : ∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * (ψ i).1 (x * y) ∂μ = s * (ψ i).1 x := by
      intro i
      refine hα (ψ i) ((hVs i).1.aut _ (hψV i)) (hψT i) fun τ => ?_
      obtain ⟨m, hm, hb⟩ := (hVs i).2.2.1 τ
      refine ⟨m, ⟨hm.1, fun u φ hφ => ?_⟩, hb⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      rw [map_smul, hm.2 u _ (hψV i), smul_comm]
    have hcB := hbes n (fun i => (ψ i).1) hcont hleft hs hψ1 (fun i j hij =>
      GlobalTheory.T.orthogonal_of_non_isomorphic E N μ F hF (Vs i) (Vs j) (hVs i).1 (hVs j).1 (hne i j hij) _ (hψV i) _ (hψV j))
    have h1 : ∀ i, 1 ≤ 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := fun i =>
      hconc (Vs i) (ψ i) (hVs i).1 (hψV i) (hψT i) (hVs i).2.2.1 (hVs i).2.2.2 (hs i) (hψ1 i)
    calc (n : ENNReal) = ∑ _i : Fin n, (1 : ENNReal) := by simp
      _ ≤ ∑ i : Fin n, 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * ∑ i : Fin n, ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := by rw [Finset.mul_sum]
      _ ≤ 2 * B := by gcongr
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * B ≤ (n₀ : ENNReal) := by
    have h2B : 2 * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
    exact ENNReal.exists_nat_gt h2B |>.imp fun _ h => h.le
  set P : ℕ → Prop := fun n => ∃ Vs : Fin n → Submodule ℂ (Sm E N), (∀ i, D (Vs i)) ∧
    ∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j) with hP
  have hbd : ∀ n, P n → n ≤ n₀ := by
    rintro n ⟨Vs, h1, h2⟩
    exact_mod_cast (key n Vs h1 h2).trans hn₀
  have hP0 : P 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  set n := Nat.findGreatest P n₀ with hn
  obtain ⟨Vs, hVs, hpw⟩ : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨Finset.univ.image Vs, fun V h1 h2 h3 h4 => ?_⟩
  by_contra hno
  have hDV : D V := ⟨h1, h2, h3, h4⟩
  have hno' : ∀ i, ¬ IsoV V (Vs i) := fun i hi => hno ⟨Vs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩
  have hnext : P (n + 1) := by
    refine ⟨Fin.cons V Vs, fun i => ?_, fun i j hij => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hDV
      · simpa using hVs i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hno' j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i (isoV_symm (hVs i).1.stable h)
        | succ j =>
          simpa using hpw i j fun e => hij (by rw [e])
  have := Nat.le_findGreatest (hbd _ hnext) hnext
  omega

end GlobalTheory.CompanionTheory.FinDiscP

end
