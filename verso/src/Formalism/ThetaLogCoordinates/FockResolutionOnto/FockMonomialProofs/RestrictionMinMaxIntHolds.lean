import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersHolds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section EProj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def LowIm (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c), Submodule.map (glAct p LL j c d) ⊤

def IsEProj (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  PE ∘ₗ PE = PE ∧ LinearMap.range PE = HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w ∧
    LinearMap.ker PE ⊓ WtSpC p LL j univ w = LowIm p LL j ρ ⊓ WtSpC p LL j univ w

/- English proof (translation)
Take `⟨PE, h1, h2, h3, h4, h5⟩` from `hE j hj w`. Conclude with `⟨PE, ⟨h1, h2, h3⟩, h4, h5⟩`.
-/
theorem hypE_eproj (LL : Letters N) (ρ : Fin r) (e1 : ℕ) (hE : HypE p LL ρ e1) (j : ℕ) (hj : j ≤ N) (w : Fin r → ℤ) :
    ∃ PE, IsEProj p LL j ρ w PE ∧
      (∀ F G, F ∈ WtSpC p LL j univ w → G ∈ WtSpC p LL j univ w → fock p (PE F) G = fock p F (PE G)) ∧
      ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ w → ((p : ℚ_[p]) ^ e1) • PE F ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨PE, h1, h2, h3, h4, h5⟩ := hE j hj w
  exact ⟨PE, ⟨h1, h2, h3⟩, h4, h5⟩

/- English proof (translation)
Introduce `x hx`. Simplify using `only [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx ⊢`. Introduce `m hm`. Establish `hm'` using `hx hm`. Simplify using `only [Set.mem_setOf_eq] at hm' ⊢`.

Introduce `c _`. Conclude with `hm' c (Finset.mem_univ c)`.
-/
theorem wtsp_mono (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ) :
    WtSpC p LL j univ w ≤ WtSpC p LL j Cs w := by
  intro x hx
  simp only [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  intro m hm
  have hm' := hx hm
  simp only [Set.mem_setOf_eq] at hm' ⊢
  intro c _
  exact hm' c (Finset.mem_univ c)

/- English proof (translation)
Take `⟨_, hr, _⟩` from `hPE`. Rewrite using `[← hr]`. Conclude with `LinearMap.mem_range_self PE x`.
-/
theorem eproj_mem (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    PE x ∈ HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w := by
  obtain ⟨_, hr, _⟩ := hPE
  rw [← hr]
  exact LinearMap.mem_range_self PE x

/- English proof (translation)
Introduce `x hx`. Take `⟨hi, hr, _⟩` from `hPE`. Rewrite `hx` using `[← hr]`. Take `⟨y, rfl⟩` from `hx`. Conclude with `LinearMap.congr_fun hi y`.
-/
theorem eproj_fix (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ x ∈ HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w, PE x = x := by
  intro x hx
  obtain ⟨hi, hr, _⟩ := hPE
  rw [← hr] at hx
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun hi y

/- English proof (translation)
Introduce `x hx`. Establish `key : LowIm p LL j ρ ≤ (LowIm p LL j ρ).comap Q`. Unfold `LowIm`. Use `iSup_le fun c => iSup_le fun d => iSup_le fun h => ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨z, -, rfl⟩` from `Submodule.mem_map.mp hy`. Rewrite using `[Submodule.mem_comap, hQ c h.1 d h.2.1 z]`. Conclude with `Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem Submodule.mem_top)))`. Conclude with `key hx`.
-/
theorem lowIm_keep (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ LowIm p LL j ρ, Q x ∈ LowIm p LL j ρ := by
  intro x hx
  have key : LowIm p LL j ρ ≤ (LowIm p LL j ρ).comap Q := by
    unfold LowIm
    refine iSup_le fun c => iSup_le fun d => iSup_le fun h => ?_
    intro y hy
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.mem_comap, hQ c h.1 d h.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem Submodule.mem_top)))
  exact key hx

/- English proof (translation)
Introduce `F hF`. Take `⟨i1, r1, k1⟩` from `h1`. Take `⟨i2, r2, k2⟩` from `h2`. Establish `hP1 : HeightBoundSetup F ∈ HWC p LL j (univ.erase ρ) w1 ⊓ WtSpC p LL j univ w1`. Rewrite using `[← r1]`.

Conclude with `LinearMap.mem_range_self HeightBoundSetup F`. Establish `hfix1 : HeightBoundSetup (HeightBoundSetup F) = HeightBoundSetup F` using `LinearMap.congr_fun i1 F`. Establish `hK : F - HeightBoundSetup F ∈ LinearMap.ker HeightBoundSetup ⊓ WtSpC p LL j univ w1`. Use `Submodule.mem_inf.mpr ⟨?_, Submodule.sub_mem _ hF (Submodule.mem_inf.mp hP1).2⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hfix1, sub_self]`.

Rewrite `hK` using `[k1]`. Take `⟨hKL, hKW⟩` from `Submodule.mem_inf.mp hK`. Establish `hQK : Q (F - HeightBoundSetup F) ∈ LinearMap.ker LogBallEstimates ⊓ WtSpC p LL j univ w2`. Rewrite using `[k2]`. Conclude with `Submodule.mem_inf.mpr ⟨lowIm_keep LL j ρ Q hQ _ hKL, hW _ hKW⟩`.

Establish `hQH : Q (HeightBoundSetup F) ∈ HWC p LL j (univ.erase ρ) w2 ⊓ WtSpC p LL j univ w2`. Take `⟨hH, hWW⟩` from `Submodule.mem_inf.mp hP1`. Establish `hQW` using `hW _ hWW`. Use `Submodule.mem_inf.mpr ⟨?_, hQW⟩` and prove the remaining obligations. Simplify using `only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢`.

Use `⟨wtsp_mono LL j _ w2 hQW, fun c d hcd => ?_⟩` and prove the remaining obligations. Rewrite using `[← hQ c hcd.1 d hcd.2.1, hH.2 c d hcd, map_zero]`. Establish `e2 : LogBallEstimates (Q (HeightBoundSetup F)) = Q (HeightBoundSetup F)` using `eproj_fix LL j ρ w2 LogBallEstimates ⟨i2, r2, k2⟩ _ hQH`. Establish `e3 : LogBallEstimates (Q (F - HeightBoundSetup F)) = 0` using `(Submodule.mem_inf.mp hQK).1`. Establish `hsplit : Q F = Q (HeightBoundSetup F) + Q (F - HeightBoundSetup F)`.

Rewrite using `[← map_add]`. Simplify using the standard rewrite rules. Rewrite using `[hsplit, map_add, e2, e3, add_zero]`.
-/
theorem eproj_comm (LL : Letters N) (j : ℕ) (ρ : Fin r) (w1 w2 : Fin r → ℤ)
    (HeightBoundSetup LogBallEstimates : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : IsEProj p LL j ρ w1 HeightBoundSetup) (h2 : IsEProj p LL j ρ w2 LogBallEstimates)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hW : ∀ x ∈ WtSpC p LL j univ w1, Q x ∈ WtSpC p LL j univ w2) :
    ∀ F ∈ WtSpC p LL j univ w1, LogBallEstimates (Q F) = Q (HeightBoundSetup F) := by
  intro F hF
  obtain ⟨i1, r1, k1⟩ := h1
  obtain ⟨i2, r2, k2⟩ := h2
  have hP1 : HeightBoundSetup F ∈ HWC p LL j (univ.erase ρ) w1 ⊓ WtSpC p LL j univ w1 := by
    rw [← r1]; exact LinearMap.mem_range_self HeightBoundSetup F
  have hfix1 : HeightBoundSetup (HeightBoundSetup F) = HeightBoundSetup F := LinearMap.congr_fun i1 F
  have hK : F - HeightBoundSetup F ∈ LinearMap.ker HeightBoundSetup ⊓ WtSpC p LL j univ w1 := by
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.sub_mem _ hF (Submodule.mem_inf.mp hP1).2⟩
    rw [LinearMap.mem_ker, map_sub, hfix1, sub_self]
  rw [k1] at hK
  obtain ⟨hKL, hKW⟩ := Submodule.mem_inf.mp hK
  have hQK : Q (F - HeightBoundSetup F) ∈ LinearMap.ker LogBallEstimates ⊓ WtSpC p LL j univ w2 := by
    rw [k2]
    exact Submodule.mem_inf.mpr ⟨lowIm_keep LL j ρ Q hQ _ hKL, hW _ hKW⟩
  have hQH : Q (HeightBoundSetup F) ∈ HWC p LL j (univ.erase ρ) w2 ⊓ WtSpC p LL j univ w2 := by
    obtain ⟨hH, hWW⟩ := Submodule.mem_inf.mp hP1
    have hQW := hW _ hWW
    refine Submodule.mem_inf.mpr ⟨?_, hQW⟩
    simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    refine ⟨wtsp_mono LL j _ w2 hQW, fun c d hcd => ?_⟩
    rw [← hQ c hcd.1 d hcd.2.1, hH.2 c d hcd, map_zero]
  have e2 : LogBallEstimates (Q (HeightBoundSetup F)) = Q (HeightBoundSetup F) := eproj_fix LL j ρ w2 LogBallEstimates ⟨i2, r2, k2⟩ _ hQH
  have e3 : LogBallEstimates (Q (F - HeightBoundSetup F)) = 0 := (Submodule.mem_inf.mp hQK).1
  have hsplit : Q F = Q (HeightBoundSetup F) + Q (F - HeightBoundSetup F) := by
    rw [← map_add]; simp
  rw [hsplit, map_add, e2, e3, add_zero]

/- English proof (translation)
Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [apply_ite (coeff n), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]`. Distinguish the cases in `hn : n ∈ x.support`. Rewrite using `[Finset.sum_eq_single n]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`. Conclude with `absurd hn h`. Establish `h0 : coeff n x = 0` using `by simpa using hn`.

Rewrite using `[h0, ite_self]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`. Establish `hbn : b ≠ n` using `fun h => hn (h ▸ hb)`. Simplify using `[hbn]`.
-/
private theorem coeff_filt_lemma {σ R : Type*} [CommSemiring R] [DecidableEq σ] (P : (σ →₀ ℕ) → Prop)
    (dec : ∀ m, Decidable (P m)) (x : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (∑ m ∈ x.support, @ite _ (P m) (dec m) (monomial m (coeff m x)) 0) =
      @ite _ (P n) (dec n) (coeff n x) 0 := by
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (coeff n), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  by_cases hn : n ∈ x.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hn h
  · have h0 : coeff n x = 0 := by simpa using hn
    rw [h0, ite_self]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := fun h => hn (h ▸ hb)
    simp [hbn]

/- English proof (translation)
Establish `hmono : ∀ (a b : Fin r), a ≠ ρ → b ≠ ρ → ∀ (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N), n (i, ρ) ∈ Q → X (i', a) * pderiv (i', b) (monomial n t) ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q}`. Introduce `a b ha hb n t i' hn`. Rewrite using `[MvPolynomial.pderiv_monomial]`. Establish `hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1` using `rfl`. Rewrite using `[hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]`.

Introduce `m hm`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]`. Establish `h1 : (i', a) ≠ (i, ρ)` using `fun h => ha (Prod.mk.inj h).2`. Establish `h2 : (i', b) ≠ (i, ρ)` using `fun h => hb (Prod.mk.inj h).2`. Simplify `hn` using `[Finsupp.single_apply, h1, h2]`.

Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[← MvPolynomial.support_sum_monomial_coeff y, map_sum]`. Use `Submodule.sum_mem _ fun n hn => ?_` and prove the remaining obligations. Establish `hnQ : n (i, ρ) ∈ Q` using `hy (Finset.mem_coe.mpr hn)`. Simplify using `only [glAct, LinearMap.sum_apply]`.

Use `Submodule.sum_mem _ fun i' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hmono c d hc hd n _ i' hnQ`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `Submodule.neg_mem _ (hmono d c hd hc n _ i' hnQ)`.

Conclude with `Submodule.zero_mem _`.
-/
private theorem glAct_slice_lemma_2 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (Q : Set ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
  have hmono : ∀ (a b : Fin r), a ≠ ρ → b ≠ ρ → ∀ (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N),
      n (i, ρ) ∈ Q →
      X (i', a) * pderiv (i', b) (monomial n t) ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
    intro a b ha hb n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
    rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have h1 : (i', a) ≠ (i, ρ) := fun h => ha (Prod.mk.inj h).2
    have h2 : (i', b) ≠ (i, ρ) := fun h => hb (Prod.mk.inj h).2
    simpa [Finsupp.single_apply, h1, h2] using hn
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnQ : n (i, ρ) ∈ Q := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d hc hd n _ i' hnQ
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c hd hc n _ i' hnQ)
  · exact Submodule.zero_mem _

/- English proof (translation)
Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`. Simplify using `only [resL, LinearMap.coe_mk, AddHom.coe_mk]`. Unfold `initPart`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]`. Conclude with `hy (Finset.mem_coe.mpr hm)`. Conclude with `Submodule.zero_mem _`.
-/
private theorem resL_keep_lemma_4 (v : Fin N × Fin r) (e : ℕ) (S : Set (Fin N × Fin r →₀ ℕ))
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] S) :
    resL p v e y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hy (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _

/- English proof (translation)
Establish `hres : ∀ (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (n : Fin N × Fin r →₀ ℕ), coeff n (resL p (i, ρ) e y) = if n (i, ρ) = e then coeff n y else 0`. Introduce `y n`. Simplify using `only [resL, LinearMap.coe_mk, AddHom.coe_mk]`. Unfold `initPart`. Conclude with `coeff_filt_lemma (fun m => m (i, ρ) = e) _ y n`.

Establish `hmem : resL p (i, ρ) e x ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)}`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, hres]`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`.

Assume the negation of the conclusion as `h`. Conclude with `hn (if_neg h)`. Establish `hrest : x - resL p (i, ρ) e x ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)}`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`.

Rewrite `hn` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hres]`. Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]`. Introduce `h`. Conclude with `hn (by rw [if_pos h, sub_self])`. Establish `hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)}, resL p (i, ρ) e y = y`.

Introduce `y hy`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`. Use extensionality with `n`. Rewrite using `[hres]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Establish `hn : n ∉ y.support` using `fun hn => h (hy (Finset.mem_coe.mpr hn))`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, not_not]`. Conclude with `hn.symm`. Establish `hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)}, resL p (i, ρ) e y = 0`.

Introduce `y hy`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`. Use extensionality with `n`. Rewrite using `[hres, MvPolynomial.coeff_zero]`. Use `split_ifs with h`.

Establish `hn : n ∉ y.support` using `fun hn => hy (Finset.mem_coe.mpr hn) h`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, not_not]`. Conclude with `hn`. Both sides reduce to the same expression. Establish `hsplit : x = resL p (i, ρ) e x + (x - resL p (i, ρ) e x)` using `by abel`.

Use `conv_lhs => rw [hsplit]`. Rewrite using `[map_add, map_add, hid _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hmem), hzero _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hrest), add_zero]`.
-/
private theorem resL_glAct_lemma_3 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (e : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p (i, ρ) e (glAct p LL j c d x) = glAct p LL j c d (resL p (i, ρ) e x) := by
  have hres : ∀ (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (n : Fin N × Fin r →₀ ℕ),
      coeff n (resL p (i, ρ) e y) = if n (i, ρ) = e then coeff n y else 0 := by
    intro y n
    simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
    unfold initPart
    exact coeff_filt_lemma (fun m => m (i, ρ) = e) _ y n
  have hmem : resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_contra h
    exact hn (if_neg h)
  have hrest : x - resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)},
      resL p (i, ρ) e y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h (hy (Finset.mem_coe.mpr hn))
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)},
      resL p (i, ρ) e y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => hy (Finset.mem_coe.mpr hn) h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hsplit : x = resL p (i, ρ) e x + (x - resL p (i, ρ) e x) := by abel
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, hid _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hmem),
    hzero _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hrest), add_zero]

/- English proof (translation)
Introduce `F hF`. Conclude with `eproj_comm LL j ρ w w PE PE hPE hPE (resL p (i, ρ) e) (fun c hc d hd x => resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hc) (Finset.ne_of_mem_erase hd) i e x) (fun x hx => resL_keep_lemma_4 (i, ρ) e _ x hx) F hF`.
-/
theorem eproj_res (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (i : Fin N) (e : ℕ) :
    ∀ F ∈ WtSpC p LL j univ w, PE (resL p (i, ρ) e F) = resL p (i, ρ) e (PE F) := by
  intro F hF
  exact eproj_comm LL j ρ w w PE PE hPE hPE (resL p (i, ρ) e)
    (fun c hc d hd x => resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hc) (Finset.ne_of_mem_erase hd) i e x)
    (fun x hx => resL_keep_lemma_4 (i, ρ) e _ x hx) F hF

/- English proof (translation)
Establish `hs : ∀ (i' : Fin N) (a' : Fin r) (i'' : Fin N), ∑ c', (Finsupp.single (i', a') 1 : Fin N × Fin r →₀ ℕ) (i'', c') = if i'' = i' then 1 else 0`. Introduce `i' a' i''`. Distinguish the cases in `h : i'' = i'`. Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`.

Simplify using `[Finsupp.single_apply, Ne.symm h, h]`. Establish `hmono : ∀ (a b : Fin r) (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N), (MultiDeg LL n ↔ B) → X (i', a) * pderiv (i', b) (monomial n t) ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)}`. Introduce `a b n t i' hn`. Rewrite using `[MvPolynomial.pderiv_monomial]`. Distinguish the cases in `h0 : n (i', b) = 0`.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hle : Finsupp.single (i', b) 1 ≤ n` using `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)`. Establish `hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1` using `rfl`. Rewrite using `[hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]`.

Introduce `m hm`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]`. Establish `hsum : ∀ i'', ∑ c', ((Finsupp.single (i', a) 1 + (n - Finsupp.single (i', b) 1) : Fin N × Fin r →₀ ℕ)) (i'', c') = ∑ c', n (i'', c')`. Introduce `i''`. Establish `hn' : n = (n - Finsupp.single (i', b) 1) + Finsupp.single (i', b) 1` using `(tsub_add_cancel_of_le hle).symm`.

Use `conv_rhs => rw [hn']`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hs]`. Expand and normalize the polynomial expressions, which then agree. Use `show MultiDeg LL _ ↔ B`. Rewrite using `[← hn]`.

Unfold `MultiDeg`. Simplify using `only [hsum]`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[← MvPolynomial.support_sum_monomial_coeff y, map_sum]`. Use `Submodule.sum_mem _ fun n hn => ?_` and prove the remaining obligations.

Establish `hnB : (MultiDeg LL n ↔ B)` using `hy (Finset.mem_coe.mpr hn)`. Simplify using `only [glAct, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun i' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hmono c d n _ i' hnB`.

Rewrite using `[LinearMap.neg_apply]`. Conclude with `Submodule.neg_mem _ (hmono d c n _ i' hnB)`. Conclude with `Submodule.zero_mem _`.
-/
private theorem glAct_md_lemma_5 (LL : Letters N) (j : ℕ) (c d : Fin r) (B : Prop)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
  have hs : ∀ (i' : Fin N) (a' : Fin r) (i'' : Fin N),
      ∑ c', (Finsupp.single (i', a') 1 : Fin N × Fin r →₀ ℕ) (i'', c') = if i'' = i' then 1 else 0 := by
    intro i' a' i''
    by_cases h : i'' = i'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hmono : ∀ (a b : Fin r) (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N), (MultiDeg LL n ↔ B) →
      X (i', a) * pderiv (i', b) (monomial n t) ∈
        MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
    intro a b n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : n (i', b) = 0
    · rw [h0]
      simp
    · have hle : Finsupp.single (i', b) 1 ≤ n := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
      rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
      have hsum : ∀ i'', ∑ c', ((Finsupp.single (i', a) 1 + (n - Finsupp.single (i', b) 1) : Fin N × Fin r →₀ ℕ)) (i'', c') =
          ∑ c', n (i'', c') := by
        intro i''
        have hn' : n = (n - Finsupp.single (i', b) 1) + Finsupp.single (i', b) 1 :=
          (tsub_add_cancel_of_le hle).symm
        conv_rhs => rw [hn']
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hs]
        ring
      show MultiDeg LL _ ↔ B
      rw [← hn]
      unfold MultiDeg
      simp only [hsum]
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnB : (MultiDeg LL n ↔ B) := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d n _ i' hnB
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c n _ i' hnB)
  · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `F hFP hFW`. Set `Pm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]` to `{ toFun := fun x => ∑ m ∈ x.support, if MultiDeg LL m then monomial m (coeff m x) else 0 map_add' := fun x y => by`. Use extensionality with `n`. Use `beta_reduce`. Rewrite using `[MvPolynomial.coeff_add, coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _]`.

Apply the tactic sequence `split_ifs <;> simp`. Use the proof step `map_smul' := fun t x => by`. Use extensionality with `n`. Use `beta_reduce`. Rewrite using `[MvPolynomial.coeff_smul, coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _]`.

Apply the tactic sequence `split_ifs <;> simp }`. Establish `hπ : ∀ y n, coeff n (Pm y) = if MultiDeg LL n then coeff n y else 0` using `fun y n => coeff_filt_lemma (fun m => MultiDeg LL m) _ y n`. Establish `hsupp : ∀ (S : Set (Fin N × Fin r →₀ ℕ)) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]), y ∈ MvPolynomial.restrictSupport ℚ_[p] S → Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] S`. Introduce `S y hy`. Rewrite `hy`, the goal using `[MvPolynomial.mem_restrictSupport_iff]`.

Introduce `n hn`. Rewrite `hn` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, hπ]`. Apply `hy` to reduce the goal to its premises. Rewrite using `[Finset.mem_coe, MvPolynomial.mem_support_iff]`. Introduce `h0`.

Conclude with `hn (by rw [h0, ite_self])`. Establish `hmemT : ∀ y, Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)}`. Introduce `y`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`.

Rewrite `hn` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, hπ]`. Simplify using `only [Set.mem_setOf_eq, iff_true]`. Assume the negation of the conclusion as `h`. Conclude with `hn (if_neg h)`. Establish `hrest : ∀ y, y - Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)}`.

Introduce `y`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hπ]`. Simplify using `only [Set.mem_setOf_eq, iff_false]`.

Introduce `h`. Conclude with `hn (by rw [if_pos h, sub_self])`. Establish `hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)}, Pm y = y`. Introduce `y hy`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`.

Use extensionality with `n`. Rewrite using `[hπ]`. Use `split_ifs with h`. Both sides reduce to the same expression. Establish `hn : n ∉ y.support` using `fun hn => h ((hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ True).mpr trivial)`.

Rewrite `hn` using `[MvPolynomial.mem_support_iff, not_not]`. Conclude with `hn.symm`. Establish `hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)}, Pm y = 0`. Introduce `y hy`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`.

Use extensionality with `n`. Rewrite using `[hπ, MvPolynomial.coeff_zero]`. Use `split_ifs with h`. Establish `hn : n ∉ y.support` using `fun hn => (hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ False).mp h`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, not_not]`.

Conclude with `hn`. Both sides reduce to the same expression. Establish `hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Pm (glAct p LL j c d x) = glAct p LL j c d (Pm x)`. Introduce `c _ d _ x`. Establish `hsplit : x = Pm x + (x - Pm x)` using `by abel`.

Use `conv_lhs => rw [hsplit]`. Rewrite using `[map_add, map_add, hid _ (glAct_md_lemma_5 LL j c d True _ (hmemT x)), hzero _ (glAct_md_lemma_5 LL j c d False _ (hrest x)), add_zero]`. Establish `key` using `eproj_comm LL j ρ w w PE PE hPE hPE Pm hQ (fun x hx => hsupp _ x hx) F hFW`. Establish `hF : Pm F = F` using `hid F (by`. Rewrite `hFP` using `[Pol, MvPolynomial.mem_restrictSupport_iff]`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`. Simplify using `using hFP hn)`. Rewrite `key` using `[hF]`. Rewrite using `[key]`.

Establish `hT` using `hmemT (PE F)`. Rewrite using `[Pol, MvPolynomial.mem_restrictSupport_iff]`. Rewrite `hT` using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`. Simplify using `using hT hn`.
-/
theorem eproj_pol (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ F ∈ Pol p r LL, F ∈ WtSpC p LL j univ w → PE F ∈ Pol p r LL := by
  classical
  intro F hFP hFW
  let Pm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    { toFun := fun x => ∑ m ∈ x.support, if MultiDeg LL m then monomial m (coeff m x) else 0
      map_add' := fun x y => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_add, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp
      map_smul' := fun t x => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_smul, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp }
  have hπ : ∀ y n, coeff n (Pm y) = if MultiDeg LL n then coeff n y else 0 :=
    fun y n => coeff_filt_lemma (fun m => MultiDeg LL m) _ y n
  have hsupp : ∀ (S : Set (Fin N × Fin r →₀ ℕ)) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      y ∈ MvPolynomial.restrictSupport ℚ_[p] S → Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
    intro S y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    apply hy
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
    intro h0
    exact hn (by rw [h0, ite_self])
  have hmemT : ∀ y, Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_true]
    by_contra h
    exact hn (if_neg h)
  have hrest : ∀ y, y - Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_false]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)}, Pm y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h ((hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ True).mpr trivial)
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)}, Pm y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => (hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ False).mp h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      Pm (glAct p LL j c d x) = glAct p LL j c d (Pm x) := by
    intro c _ d _ x
    have hsplit : x = Pm x + (x - Pm x) := by abel
    conv_lhs => rw [hsplit]
    rw [map_add, map_add, hid _ (glAct_md_lemma_5 LL j c d True _ (hmemT x)),
      hzero _ (glAct_md_lemma_5 LL j c d False _ (hrest x)), add_zero]
  have key := eproj_comm LL j ρ w w PE PE hPE hPE Pm hQ (fun x hx => hsupp _ x hx) F hFW
  have hF : Pm F = F := hid F (by
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hFP
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    simpa using hFP hn)
  rw [hF] at key
  rw [key]
  have hT := hmemT (PE F)
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  rw [MvPolynomial.mem_restrictSupport_iff] at hT
  intro n hn
  simpa using hT hn

/- English proof (translation)
The claim follows from `comm_wtsp LL j P (fun c x => typeProj_comm_later LL j' j hjj T P hP c c x) w`.
-/
theorem typeProj_wtsp_later (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, P x ∈ WtSpC p LL j univ w :=
  comm_wtsp LL j P (fun c x => typeProj_comm_later LL j' j hjj T P hP c c x) w

/- English proof (translation)
The claim follows from `eproj_comm LL j ρ w w PE PE hPE hPE P (fun c _ d _ x => typeProj_comm_later LL j' j hjj T P hP c d x) (typeProj_wtsp_later LL j' j hjj T P hP w)`.
-/
theorem eproj_typeProj (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) :
    ∀ F ∈ WtSpC p LL j univ w, PE (P F) = P (PE F) :=
  eproj_comm LL j ρ w w PE PE hPE hPE P
    (fun c _ d _ x => typeProj_comm_later LL j' j hjj T P hP c d x) (typeProj_wtsp_later LL j' j hjj T P hP w)

/- English proof (translation)
Introduce `h hh hW`. Establish `h1 : P h = h` using `ycond_fix LL j' _ Mt P hP (fun la hla => hla) h hh`. Establish `h2` using `eproj_typeProj LL j' j hjj ρ w PE hPE _ P hP h hW`. Rewrite `h2` using `[h1]`. Rewrite using `[h2]`.

Conclude with `typeProj_range_le_ycond LL j' _ Mt P hP (fun la hla => hla) _`.
-/
theorem eproj_ycond [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ h ∈ YCond p LL j' Mt ⊓ Pol p r LL, h ∈ WtSpC p LL j univ w → PE h ∈ YCond p LL j' Mt := by
  intro h hh hW
  have h1 : P h = h := ycond_fix LL j' _ Mt P hP (fun la hla => hla) h hh
  have h2 := eproj_typeProj LL j' j hjj ρ w PE hPE _ P hP h hW
  rw [h1] at h2
  rw [h2]
  exact typeProj_range_le_ycond LL j' _ Mt P hP (fun la hla => hla) _

/- English proof (translation)
Introduce `h hh hW`. Take `⟨hhP, hhY⟩` from `Submodule.mem_inf.mp hh`. Rewrite `hhY` using `[Submodule.mem_iInf]`. Take `⟨hA, hB⟩` from `Submodule.mem_inf.mp (eproj_mem LL N ρ w PE hPE h)`. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨eproj_pol LL N ρ w PE hPE h hhP hW, ?_⟩, hA⟩, hB⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_iInf]`. Introduce `k`. Take `⟨P, hP, -, -⟩` from `hHP.1 (min (J k) N) (min_le_right _ _) univ (Or.inl rfl) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)`. Rewrite using `[hl 0 (Finset.mem_univ 0)])`. Establish `hk` using `hhY k`.

Rewrite `hk`, the goal using `[ycond_min]`. Conclude with `eproj_ycond LL _ N (min_le_right _ _) ρ w PE hPE (M k) P hP h (Submodule.mem_inf.mpr ⟨hk, hhP⟩) hW`.
-/
theorem eproj_Y [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 : ℕ) (hHP : HypP p LL ρ e1)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL N ρ w PE) :
    ∀ h ∈ Y p LL J M, h ∈ WtSpC p LL N univ w → PE h ∈ MMw p LL J M ρ w := by
  intro h hh hW
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp (eproj_mem LL N ρ w PE hPE h)
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
    ⟨eproj_pol LL N ρ w PE hPE h hhP hW, ?_⟩, hA⟩, hB⟩
  rw [Submodule.mem_iInf]
  intro k
  obtain ⟨P, hP, -, -⟩ := hHP.1 (min (J k) N) (min_le_right _ _) univ (Or.inl rfl)
    {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)
      rw [hl 0 (Finset.mem_univ 0)])
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact eproj_ycond LL _ N (min_le_right _ _) ρ w PE hPE (M k) P hP h (Submodule.mem_inf.mpr ⟨hk, hhP⟩) hW

end EProj

section WtComp
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def wtComp (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (w : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  compP (fun m => ∀ c, wt LL j c m = w c) x

/- English proof (translation)
Unfold `wtComp compP`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[WtSpC, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`.

Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]`. Simplify using `only [Set.mem_setOf_eq]`. Introduce `c _`. Conclude with `h c`. Conclude with `Submodule.zero_mem _`.
-/
theorem wtComp_mem (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wtComp p LL j w x ∈ WtSpC p LL j univ w := by
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m _ => ?_
  split_ifs with h
  · rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    simp only [Set.mem_setOf_eq]
    intro c _
    exact h c
  · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[WtSpC, MvPolynomial.mem_restrictSupport_iff]`. Unfold `wtComp compP`. Use `conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hm' : ∀ c ∈ univ, wt LL j c m = w c` using `hx (Finset.mem_coe.mpr hm)`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `absurd (fun c => hm' c (Finset.mem_univ c)) h`.
-/
theorem wtComp_fix (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, wtComp p LL j w x = x := by
  intro x hx
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : ∀ c ∈ univ, wt LL j c m = w c := hx (Finset.mem_coe.mpr hm)
  split_ifs with h
  · rfl
  · exact absurd (fun c => hm' c (Finset.mem_univ c)) h

/- English proof (translation)
Introduce `x hx`. Take `⟨y, rfl⟩` from `hx`. Unfold `wtComp compP`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `⟨monomial m (coeff m y), by simp [MvPolynomial.coeff_map]⟩`. Conclude with `Submodule.zero_mem _`.
-/
theorem wtComp_int (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ IntPol p (Fin N × Fin r), wtComp p LL j w x ∈ IntPol p (Fin N × Fin r) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m _ => ?_
  split_ifs
  · exact ⟨monomial m (coeff m y), by simp [MvPolynomial.coeff_map]⟩
  · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[MvPolynomial.mem_restrictSupport_iff]`. Unfold `wtComp compP`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]`. Conclude with `hx (Finset.mem_coe.mpr hm)`. Conclude with `Submodule.zero_mem _`.
-/
theorem wtComp_keep_supp (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (Q : Set (Fin N × Fin r →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, wtComp p LL j w x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hx (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [resL, LinearMap.coe_mk, AddHom.coe_mk]`. Unfold `initPart wtComp compP`. Use `beta_reduce`. Rewrite using `[coeff_filt_lemma (fun m => m v = e) _]`.

Use `erw [coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _, coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _]`. Rewrite using `[coeff_filt_lemma (fun m => m v = e) _]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem wtComp_res (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (v : Fin N × Fin r) (e : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (wtComp p LL j w x) = wtComp p LL j w (resL p v e x) := by
  ext n
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart wtComp compP
  beta_reduce
  rw [coeff_filt_lemma (fun m => m v = e) _]
  erw [coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _, coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _]
  rw [coeff_filt_lemma (fun m => m v = e) _]
  split_ifs <;> rfl

/- English proof (translation)
Introduce `x hx`. Rewrite using `[glAct_split LL j' j c c, LinearMap.add_apply]`. Use `Submodule.add_mem _ (ycond_glStable LL j' Mt c c x hx) ?_` and prove the remaining obligations. Use `ycond_keep LL j' Mt (glRest p LL j' j c c) (fun a b y => glRest_comm LL j' j hjj c c a b y) (fun y hy => ops_keep_supp {v : Fin N × Fin r | j' ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_) (glRest_mem LL j' j hjj c c) y hy) x hx` and prove the remaining obligations. Establish `: wt LL j' 0 m = wt LL j' 0 m'` using `wt_congr LL j' 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))`.

Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[← this]`. Conclude with `hm`.
-/
theorem cartan_ycond [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j' Mt, glAct p LL j c c x ∈ YCond p LL j' Mt := by
  intro x hx
  rw [glAct_split LL j' j c c, LinearMap.add_apply]
  refine Submodule.add_mem _ (ycond_glStable LL j' Mt c c x hx) ?_
  refine ycond_keep LL j' Mt (glRest p LL j' j c c) (fun a b y => glRest_comm LL j' j hjj c c a b y)
    (fun y hy => ops_keep_supp {v : Fin N × Fin r | j' ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_)
      (glRest_mem LL j' j hjj c c) y hy) x hx
  have : wt LL j' 0 m = wt LL j' 0 m' :=
    wt_congr LL j' 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [← this]; exact hm

/- English proof (translation)
Introduce `h hh`. Take `⟨hhP, hhY⟩` from `Submodule.mem_inf.mp hh`. Rewrite `hhY` using `[Submodule.mem_iInf]`. Use `Submodule.mem_inf.mpr ⟨wtComp_keep_supp LL N w _ h hhP, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_iInf]`.

Introduce `k`. Establish `hk` using `hhY k`. Rewrite `hk`, the goal using `[ycond_min]`. Conclude with `wcomp_mem LL N _ (fun c x hx => cartan_ycond LL _ N (min_le_right _ _) (M k) c x hx) w h hk`.
-/
theorem wtComp_Y [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (w : Fin r → ℤ) :
    ∀ h ∈ Y p LL J M, wtComp p LL N w h ∈ Y p LL J M := by
  intro h hh
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  refine Submodule.mem_inf.mpr ⟨wtComp_keep_supp LL N w _ h hhP, ?_⟩
  rw [Submodule.mem_iInf]
  intro k
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact wcomp_mem LL N _ (fun c x hx => cartan_ycond LL _ N (min_le_right _ _) (M k) c x hx) w h hk

end WtComp

section MulX
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

end MulX

/- English proof (translation)
Introduce `x hx`. Simplify using `only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢`. Use `⟨resL_keep_lemma_4 (i, ρ) e _ x hx.1, fun c d hcd => ?_⟩` and prove the remaining obligations. Rewrite using `[← resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hcd.1) (Finset.ne_of_mem_erase hcd.2.1) i e x, hx.2 c d hcd, map_zero]`.
-/
theorem res_hw {p : ℕ} [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ) (i : Fin N)
    (e : ℕ) : ∀ x ∈ HWC p LL j (univ.erase ρ) w, resL p (i, ρ) e x ∈ HWC p LL j (univ.erase ρ) w := by
  intro x hx
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  refine ⟨resL_keep_lemma_4 (i, ρ) e _ x hx.1, fun c d hcd => ?_⟩
  rw [← resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hcd.1) (Finset.ne_of_mem_erase hcd.2.1) i e x,
    hx.2 c d hcd, map_zero]

/- English proof (translation)
Introduce `p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hOnto x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨hx1, hxW⟩` from `Submodule.mem_inf.mp hx`. Take `⟨hxX, hxH⟩` from `Submodule.mem_inf.mp hx1`.

Take `⟨h0, hh0, hres⟩` from `hOnto x hxX`. Take `⟨PE, hPE, -, -⟩` from `hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w`. Use `⟨PE (wtComp p LL (K + 1) w h0), eproj_Y LL J M ρ w e1 hHP PE hPE _ (wtComp_Y LL J M w h0 hh0) (wtComp_mem LL (K + 1) w h0), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resL p (Fin.last K, ρ) 0 (PE (wtComp p LL (K + 1) w h0)) = x`. Express the relevant statement in the definitionally equal form `resL p (Fin.last K, ρ) 0 h0 = x at hres`.

Rewrite using `[← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ (wtComp_mem LL (K + 1) w h0), wtComp_res, hres, wtComp_fix LL (K + 1) w x hxW]`. Conclude with `eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)`. Introduce and unpack `⟨h, hh, rfl⟩`. Take `⟨hh1, hhW⟩` from `Submodule.mem_inf.mp hh`. Take `⟨hhY, hhH⟩` from `Submodule.mem_inf.mp hh1`.

Conclude with `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨restriction_into_holds p K r LL J M ρ e1 hr hρ hv hHP h hhY, res_hw LL (K + 1) ρ w (Fin.last K) 0 h hhH⟩, resL_keep_supp (Fin.last K, ρ) 0 _ h hhW⟩`.
-/
theorem restriction_min_max_holds : ResMM := by
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hOnto x
  constructor
  · intro hx
    obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
    obtain ⟨h0, hh0, hres⟩ := hOnto x hxX
    obtain ⟨PE, hPE, -, -⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
    refine ⟨PE (wtComp p LL (K + 1) w h0), eproj_Y LL J M ρ w e1 hHP PE hPE _ (wtComp_Y LL J M w h0 hh0)
      (wtComp_mem LL (K + 1) w h0), ?_⟩
    change resL p (Fin.last K, ρ) 0 (PE (wtComp p LL (K + 1) w h0)) = x
    change resL p (Fin.last K, ρ) 0 h0 = x at hres
    rw [← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ (wtComp_mem LL (K + 1) w h0), wtComp_res, hres,
      wtComp_fix LL (K + 1) w x hxW]
    exact eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh1, hhW⟩ := Submodule.mem_inf.mp hh
    obtain ⟨hhY, hhH⟩ := Submodule.mem_inf.mp hh1
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨restriction_into_holds p K r LL J M ρ e1 hr hρ hv hHP h hhY,
      res_hw LL (K + 1) ρ w (Fin.last K) 0 h hhH⟩, resL_keep_supp (Fin.last K, ρ) 0 _ h hhW⟩

/- English proof (translation)
Introduce `p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hSat x hx hxI`. Take `⟨hx1, hxW⟩` from `Submodule.mem_inf.mp hx`. Take `⟨hxX, hxH⟩` from `Submodule.mem_inf.mp hx1`. Take `⟨h0, hh0, hh0I, hres⟩` from `hSat x hxX hxI`. Take `⟨PE, hPE, -, hInt⟩` from `hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w`.

Establish `hY` using `wtComp_Y LL J M w h0 hh0`. Establish `hW` using `wtComp_mem (p := p) LL (K + 1) w h0`. Use `⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW), hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _`. Express the relevant statement in the definitionally equal form `resL p (Fin.last K, ρ) 0 h0 = x at hres`.

Rewrite using `[map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres, wtComp_fix LL (K + 1) w x hxW, eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)]`.
-/
theorem restriction_min_max_int_holds : ResMMZ := by
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hSat x hx hxI
  obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
  obtain ⟨h0, hh0, hh0I, hres⟩ := hSat x hxX hxI
  obtain ⟨PE, hPE, -, hInt⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
  have hY := wtComp_Y LL J M w h0 hh0
  have hW := wtComp_mem (p := p) LL (K + 1) w h0
  refine ⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr
    ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW),
      hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩
  change resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _
  change resL p (Fin.last K, ρ) 0 h0 = x at hres
  rw [map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres,
    wtComp_fix LL (K + 1) w x hxW, eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)]

end Formalism.InvariantFactorPaths.L4
