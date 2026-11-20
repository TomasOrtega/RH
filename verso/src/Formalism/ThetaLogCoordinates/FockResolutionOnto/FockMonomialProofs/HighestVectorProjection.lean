import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Abs
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/- English proof (translation)
Introduce `x hx`. Establish `hfix : ∀ y ∈ LinearMap.range PE, PE y = y`. Introduce and unpack `y ⟨z, rfl⟩`. Rewrite using `[← LinearMap.comp_apply, h1]`. Establish `hPx : PE x ∈ R ⊓ W`.

Rewrite using `[← h2]`. Conclude with `LinearMap.mem_range_self PE x`. Establish `hA1 : A (PE x) ∈ R ⊓ W` using `⟨hR _ hPx.1, hW _ hPx.2⟩`. Establish `hA1' : PE (A (PE x)) = A (PE x)` using `hfix _ (by rw [h2]; exact hA1)`. Establish `hker : x - PE x ∈ LinearMap.ker PE ⊓ W`.

Use `⟨LinearMap.mem_ker.mpr ?_, W.sub_mem hx hPx.2⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← LinearMap.comp_apply, h1, sub_self]`. Rewrite `hker` using `[h3]`. Establish `hA2 : A (x - PE x) ∈ LinearMap.ker PE ⊓ W`. Rewrite using `[h3]`.

Conclude with `⟨hL _ hker.1, hW _ hker.2⟩`. Establish `h0 : PE (A (x - PE x)) = 0` using `hA2.1`. Rewrite `h0` using `[map_sub, map_sub, hA1', sub_eq_zero]`. Conclude with `h0`.
-/
theorem proj_comm_abs' (PE A : V →ₗ[k] V) (R W L : Submodule k V) (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = R ⊓ W) (h3 : LinearMap.ker PE ⊓ W = L ⊓ W)
    (hR : ∀ x ∈ R, A x ∈ R) (hW : ∀ x ∈ W, A x ∈ W) (hL : ∀ x ∈ L, A x ∈ L) :
    ∀ x ∈ W, PE (A x) = A (PE x) := by
  intro x hx
  have hfix : ∀ y ∈ LinearMap.range PE, PE y = y := by
    rintro y ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, h1]
  have hPx : PE x ∈ R ⊓ W := by
    rw [← h2]
    exact LinearMap.mem_range_self PE x
  have hA1 : A (PE x) ∈ R ⊓ W := ⟨hR _ hPx.1, hW _ hPx.2⟩
  have hA1' : PE (A (PE x)) = A (PE x) := hfix _ (by rw [h2]; exact hA1)
  have hker : x - PE x ∈ LinearMap.ker PE ⊓ W := by
    refine ⟨LinearMap.mem_ker.mpr ?_, W.sub_mem hx hPx.2⟩
    rw [map_sub, ← LinearMap.comp_apply, h1, sub_self]
  rw [h3] at hker
  have hA2 : A (x - PE x) ∈ LinearMap.ker PE ⊓ W := by
    rw [h3]
    exact ⟨hL _ hker.1, hW _ hker.2⟩
  have h0 : PE (A (x - PE x)) = 0 := hA2.1
  rw [map_sub, map_sub, hA1', sub_eq_zero] at h0
  exact h0

end Abs

section EC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def lowIm' (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
    Submodule.map (glAct p LL j c d) ⊤

/- English proof (translation)
Establish `key : lowIm' p LL j ρ ≤ (lowIm' p LL j ρ).comap A`. Unfold `lowIm'`. Use `iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_` and prove the remaining obligations. Introduce and unpack `y ⟨z, -, rfl⟩`. Rewrite using `[Submodule.mem_comap, hA c hcd.1 d hcd.2.1 z]`.

Conclude with `Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hcd ⟨A z, Submodule.mem_top, rfl⟩))`. Introduce `x hx`. Conclude with `key hx`.
-/
theorem lowIm_keep' (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) :
    ∀ x ∈ lowIm' p LL j ρ, A x ∈ lowIm' p LL j ρ := by
  have key : lowIm' p LL j ρ ≤ (lowIm' p LL j ρ).comap A := by
    unfold lowIm'
    refine iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_
    rintro y ⟨z, -, rfl⟩
    rw [Submodule.mem_comap, hA c hcd.1 d hcd.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hcd ⟨A z, Submodule.mem_top, rfl⟩))
  intro x hx
  exact key hx

/- English proof (translation)
Establish `hsub : WtSpC p LL j univ la ≤ WtSpC p LL j (univ.erase ρ) la`. Introduce `x hx`. Simplify using `only [WtSpC, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx ⊢`. Introduce `m hm c _`. Conclude with `hx (show m ∈ (↑x.support : Set _) from hm) c (Finset.mem_univ c)`.

Establish `hR : ∀ x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la, A x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la`. Introduce `x hx`. Establish `hAx` using `hW x hx.2`. Use `⟨?_, hAx⟩` and prove the remaining obligations. Establish `hx1 : x ∈ WtSpC p LL j (univ.erase ρ) la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)` using `hx.1`.

Use `show A x ∈ WtSpC p LL j (univ.erase ρ) la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)`. Rewrite `hx1`, the goal using `[Submodule.mem_inf]`. Use `⟨hsub hAx, ?_⟩` and prove the remaining obligations. Establish `hx2` using `hx1.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢`.

Introduce `c d hcd`. Rewrite using `[← hA c hcd.1 d hcd.2.1, hx2 c d hcd, map_zero]`. Establish `h2' : LinearMap.range PE = (HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la) ⊓ WtSpC p LL j univ la`. Rewrite using `[h2, inf_assoc, inf_idem]`. Conclude with `proj_comm_abs' PE A _ _ _ h1 h2' h3 hR hW (lowIm_keep' LL j ρ A hA)`.
-/
theorem hwProj_comm' (LL : Letters N) (j : ℕ) (ρ : Fin r) (la : Fin r → ℤ)
    (PE A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la)
    (h3 : LinearMap.ker PE ⊓ WtSpC p LL j univ la = lowIm' p LL j ρ ⊓ WtSpC p LL j univ la)
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x))
    (hW : ∀ x ∈ WtSpC p LL j univ la, A x ∈ WtSpC p LL j univ la) :
    ∀ x ∈ WtSpC p LL j univ la, PE (A x) = A (PE x) := by
  have hsub : WtSpC p LL j univ la ≤ WtSpC p LL j (univ.erase ρ) la := by
    intro x hx
    simp only [WtSpC, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx ⊢
    intro m hm c _
    exact hx (show m ∈ (↑x.support : Set _) from hm) c (Finset.mem_univ c)
  have hR : ∀ x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la,
      A x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la := by
    intro x hx
    have hAx := hW x hx.2
    refine ⟨?_, hAx⟩
    have hx1 : x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d) := hx.1
    show A x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)
    rw [Submodule.mem_inf] at hx1 ⊢
    refine ⟨hsub hAx, ?_⟩
    have hx2 := hx1.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, hx2 c d hcd, map_zero]
  have h2' : LinearMap.range PE
      = (HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la) ⊓ WtSpC p LL j univ la := by
    rw [h2, inf_assoc, inf_idem]
  exact proj_comm_abs' PE A _ _ _ h1 h2' h3 hR hW (lowIm_keep' LL j ρ A hA)

/- English proof (translation)
Establish `hx' : ↑x.support ⊆ {m : σ →₀ ℕ | m v = 0}`. Establish `h'` using `hx`. Simplify using `only [FreeOf, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'`. Conclude with `h'`. Express the relevant statement in the definitionally equal form `initPart v 0 x = x`.

Unfold `initPart`. Use `conv_rhs => rw [x.as_sum]`. Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[if_pos (show m v = 0 from hx' (Finset.mem_coe.mpr hm))]`.
-/
theorem resL_fix' {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by
  have hx' : ↑x.support ⊆ {m : σ →₀ ℕ | m v = 0} := by
    have h' := hx
    simp only [FreeOf, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'
    exact h'
  change initPart v 0 x = x
  unfold initPart
  conv_rhs => rw [x.as_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [if_pos (show m v = 0 from hx' (Finset.mem_coe.mpr hm))]

/- English proof (translation)
Unfold `fock`. Use `Finset.sum_eq_zero (fun n hn => ?_)` and prove the remaining obligations. Establish `hne : m ≠ n` using `fun h => hm (by rw [h]; exact hn)`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg hne, mul_zero, zero_mul]`.
-/
theorem fock_monomial_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (hm : m ∉ g.support) :
    fock p g (monomial m 1) = 0 := by
  classical
  unfold fock
  refine Finset.sum_eq_zero (fun n hn => ?_)
  have hne : m ≠ n := fun h => hm (by rw [h]; exact hn)
  rw [MvPolynomial.coeff_monomial, if_neg hne, mul_zero, zero_mul]

/- English proof (translation)
Unfold `fock`. Simplify using the standard rewrite rules.
-/
theorem fock_right_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) : fock p g 0 = 0 := by
  unfold fock
  simp

/- English proof (translation)
Simplify using `only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply]`. Introduce `n hn`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (show n ∈ (monomial m (1 : ℚ_[p])).support from hn))]`. Conclude with `hm`.
-/
theorem monomial_mem_supp' {σ : Type} (Q : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ Q) :
    monomial m (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] Q := by
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply]
  intro n hn
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (show n ∈ (monomial m (1 : ℚ_[p])).support from hn))]
  exact hm

/- English proof (translation)
Establish `h` using `glAct_comm (p := p) LL j ρ ρ a b x`. Establish `hda : ¬ (ρ = a)` using `fun h => (Finset.mem_erase.mp ha).1 h.symm`. Establish `hbc : ¬ (b = ρ)` using `(Finset.mem_erase.mp hb).1`. Rewrite `h` using `[if_neg hda, if_neg hbc, sub_zero, sub_eq_zero]`. Conclude with `h`.
-/
theorem cartan_comm_erase' (LL : Letters N) (j : ℕ) (ρ : Fin r) (a : Fin r) (ha : a ∈ univ.erase ρ) (b : Fin r)
    (hb : b ∈ univ.erase ρ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j ρ ρ (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j ρ ρ x) := by
  have h := glAct_comm (p := p) LL j ρ ρ a b x
  have hda : ¬ (ρ = a) := fun h => (Finset.mem_erase.mp ha).1 h.symm
  have hbc : ¬ (b = ρ) := (Finset.mem_erase.mp hb).1
  rw [if_neg hda, if_neg hbc, sub_zero, sub_eq_zero] at h
  exact h

end EC

/- English proof (translation)
Establish `h'` using `hx`. Simplify using `only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'`. Conclude with `h' hm`.
-/
private lemma mem_of_mem_support_restrictSupport {p : ℕ} [Fact p.Prime] {σ : Type} {Q : Set (σ →₀ ℕ)}
    {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ MvPolynomial.restrictSupport ℚ_[p] Q) {m : σ →₀ ℕ}
    (hm : m ∈ x.support) : m ∈ Q := by
  have h' := hx
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported,
    Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'
  exact h' hm

/- English proof (translation)
Introduce and unpack `x ⟨y, rfl⟩`. Rewrite using `[← LinearMap.comp_apply, hQ]`.
-/
private lemma idempotent_apply_eq_self_of_mem_range {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : V →ₗ[k] V)
    (hQ : Q ∘ₗ Q = Q) : ∀ x ∈ LinearMap.range Q, Q x = x := by
  rintro x ⟨y, rfl⟩
  rw [← LinearMap.comp_apply, hQ]

/- English proof (translation)
Introduce `x`. Establish `h : x - Q x ∈ LinearMap.ker Q`. Rewrite using `[LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hQ, sub_self]`. Rewrite `h` using `[hk, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h.symm`.
-/
private lemma idempotent_apply_eq_self_of_ker_eq_bot {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : V →ₗ[k] V)
    (hQ : Q ∘ₗ Q = Q) (hk : LinearMap.ker Q = ⊥) : ∀ x, Q x = x := by
  intro x
  have h : x - Q x ∈ LinearMap.ker Q := by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hQ, sub_self]
  rw [hk, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/- English proof (translation)
Introduce `p _ K r _ LL q J M ρ w e1 hr hρ hv hP hE`. Establish `h0ρ : (0 : Fin r) ≠ ρ`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Rewrite `h'` using `[Fin.val_zero]`.

Use linear arithmetic over natural numbers and integers. Establish `h0e : (0 : Fin r) ∈ univ.erase ρ` using `Finset.mem_erase.mpr ⟨h0ρ, Finset.mem_univ _⟩`. Take `⟨Tu, hTu⟩ : ∃ Tu : ℕ → Set (Fin r → ℤ), Tu = fun j => {la | ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}` from `⟨_, rfl⟩`. Take `⟨Te, hTe⟩ : ∃ Te : Set (Fin r → ℤ), Te = {la | ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}` from `⟨_, rfl⟩`. Establish `hTu' : ∀ j la, la ∈ Tu j ↔ ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k`.

Introduce `j la`. Rewrite using `[hTu]`. Both sides reduce to the same expression. Establish `hTe' : ∀ la, la ∈ Te ↔ ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k`. Introduce `la`.

Rewrite using `[hTe]`. Both sides reduce to the same expression. Establish `hsatU : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T`. Introduce `T la la' h`. Establish `: la = la'` using `funext fun c => h c (Finset.mem_univ c)`.

Rewrite using `[this]`. Establish `hsatE : CsSaturated (univ.erase ρ) Te`. Introduce `la la' h`. Establish `h0 : la 0 = la' 0` using `h 0 h0e`. Rewrite using `[hTe', hTe', h0]`.

Take `⟨hPex, hPcomm⟩` from `hP`. Use `choose Pu hPu using fun (j : ℕ) (hj : j ≤ K) => hPex j (by omega) univ (Or.inl rfl) (Tu j) (hsatU _)`. Take `⟨Pe, hPe1, hPe2, hPe3⟩` from `hPex (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl) Te hsatE`. Take `⟨P, hPdef⟩ : ∃ P : ℕ → (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), P = fun j => if h : j ≤ K then Pu j h else Pe` from `⟨_, rfl⟩`. Establish `hPu_eq : ∀ j (hj : j ≤ K), P j = Pu j hj` using `by intro j hj; rw [hPdef]; simp [hj]`.

Establish `hPe_eq : ∀ j, ¬ j ≤ K → P j = Pe` using `by intro j hj; rw [hPdef]; simp [hj]`. Establish `hTPu : ∀ j (hj : j ≤ K), IsTypeProj p LL j univ (Tu j) (P j)`. Introduce `j hj`. Rewrite using `[hPu_eq j hj]`. Conclude with `(hPu j hj).1`.

Establish `hTPe : ∀ j, ¬ j ≤ K → IsTypeProj p LL (K + 1) (univ.erase ρ) Te (P j)`. Introduce `j hj`. Rewrite using `[hPe_eq j hj]`. Conclude with `hPe1`. Establish `hPP : ∀ j x, P j (P j x) = P j x`.

Introduce `j x`. Distinguish the cases in `hj : j ≤ K`. Conclude with `LinearMap.congr_fun (hTPu j hj).1 x`. Conclude with `LinearMap.congr_fun (hTPe j hj).1 x`. Establish `hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)`.

Introduce `j j' x`. Apply the tactic sequence `by_cases hj : j ≤ K <;> by_cases hj' : j' ≤ K`. Break down `le_total j j' with h | h` into its components or cases. Conclude with `LinearMap.congr_fun (hPcomm j j' univ univ (Tu j) (Tu j') (P j) (P j') h subset_rfl (Or.inl rfl) (Or.inl rfl) (hTPu j hj) (hTPu j' hj')) x`. Conclude with `(LinearMap.congr_fun (hPcomm j' j univ univ (Tu j') (Tu j) (P j') (P j) h subset_rfl (Or.inl rfl) (Or.inl rfl) (hTPu j' hj') (hTPu j hj)) x).symm`.

Conclude with `LinearMap.congr_fun (hPcomm j (K + 1) univ (univ.erase ρ) (Tu j) Te (P j) (P j') (by omega) (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j hj) (hTPe j' hj')) x`. Conclude with `(LinearMap.congr_fun (hPcomm j' (K + 1) univ (univ.erase ρ) (Tu j') Te (P j') (P j) (by omega) (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j' hj') (hTPe j hj)) x).symm`. Rewrite using `[hPe_eq j hj, hPe_eq j' hj']`. Establish `hPsa : ∀ j F G, fock p (P j F) G = fock p F (P j G)`. Introduce `j F G`.

Distinguish the cases in `hj : j ≤ K`. Rewrite using `[hPu_eq j hj]`. Conclude with `(hPu j hj).2.1 F G`. Rewrite using `[hPe_eq j hj]`. Conclude with `hPe2 F G`.

Establish `hPint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin (K + 1) × Fin r)`. Introduce `j F hF`. Distinguish the cases in `hj : j ≤ K`. Rewrite using `[hPu_eq j hj]`. Conclude with `(hPu j hj).2.2 F hF`.

Rewrite using `[hPe_eq j hj]`. Conclude with `hPe3 F hF`. Establish `hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL`. Introduce `j x hx`. Distinguish the cases in `hj : j ≤ K`.

Conclude with `typeProj_polC LL j univ (Tu j) (P j) (hTPu j hj) x hx`. Conclude with `typeProj_polC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) x hx`. Establish `hPgl : ∀ j, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, P j (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P j x)`. Introduce `j c hc d hd x`. Distinguish the cases in `hj : j ≤ K`.

Conclude with `typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c d x`. Conclude with `typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc d hd x`. Establish `hPdiag : ∀ j c x, P j (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P j x)`. Introduce `j c x`. Distinguish the cases in `hj : j ≤ K`.

Conclude with `typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c c x`. Distinguish the cases in `hc : c = ρ`. Rewrite using `[hc]`. Conclude with `typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (glAct p LL (K + 1) ρ ρ) (fun a ha b hb y => cartan_comm_erase' LL (K + 1) ρ a ha b hb y) x`. Establish `hc' : c ∈ univ.erase ρ` using `Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩`.

Conclude with `typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc' c hc' x`. Establish `hPws : ∀ j, ∀ x ∈ WtSpC p LL (K + 1) univ w, P j x ∈ WtSpC p LL (K + 1) univ w` using `fun j => comm_wtsp LL (K + 1) (P j) (hPdiag j) w`. Establish `hPres : ∀ j x, P j (resL p (Fin.last K, ρ) 0 x) = resL p (Fin.last K, ρ) 0 (P j x)`. Introduce `j x`. Distinguish the cases in `hj : j ≤ K`.

Use `typeProj_commC LL j univ (Tu j) (P j) (hTPu j hj) (resL p (Fin.last K, ρ) 0) (fun c _ d _ y => resL_glAct LL j c d (Fin.last K, ρ) 0 ?_ y) x` and prove the remaining obligations. Introduce `i hi`. Establish `hne : i ≠ Fin.last K`. Introduce `h`. Rewrite `hi` using `[h, Fin.val_last]`.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨fun h => hne (Prod.ext_iff.mp h).1, fun h => hne (Prod.ext_iff.mp h).1⟩`. Use `typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (resL p (Fin.last K, ρ) 0) (fun c hc d hd y => resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 ?_ y) x` and prove the remaining obligations. Introduce `i _`. Conclude with `⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2, fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩`.

Take `⟨PE, hE1, hE2, hE3, hE4, hE5⟩` from `hE (K + 1) le_rfl w`. Establish `hPEc : ∀ A : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p], (∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (A x)) → (∀ x ∈ WtSpC p LL (K + 1) univ w, A x ∈ WtSpC p LL (K + 1) univ w …` using `fun A hA hW => hwProj_comm' LL (K + 1) ρ w PE A hE1 hE2 hE3 hA hW`. Establish `hPEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w, PE g = g`. Introduce `g hg`. Conclude with `idempotent_apply_eq_self_of_mem_range PE hE1 g (by rw [hE2]; exact hg)`.

Establish `hPEpol : ∀ y ∈ Pol p r LL ⊓ WtSpC p LL (K + 1) univ w, PE y ∈ Pol p r LL`. Introduce `y hy`. Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.mp hy`. Rewrite `hy1`, the goal using `[pol_iff_eul]`. Introduce `i`.

Establish `hc` using `hPEc (ProjS.eulL (fun c : Fin r => (i, c))) (fun c _ d _ x => eul_glAct LL (K + 1) i c d x) (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i c c x) w) y hy2`. Rewrite using `[← hc, hy1 i, map_smul]`. Establish `hXH : ∀ g ∈ XH p LL J M ρ w, g ∈ Pol p r LL ∧ g ∈ FreeOf p (Fin.last K, ρ) ∧ (∀ k, K + 1 ≤ J k → g ∈ YCond p LL K (M k) ∧ g ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧ (∀ k, ¬ K + 1 ≤ J k → g ∈ YCond p LL (J k) (M k)) ∧ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ∧ g ∈ WtSpC p LL (K …`. Introduce `g hg`. Establish `hg' : g ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓ ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k) else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w` using `hg`.

Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf] at hg'`. Take `⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩` from `hg'`. Use `⟨h1, h2, fun k hk => ?_, fun k hk => ?_, h4, h5⟩` and prove the remaining obligations. Use `h3 k` as an intermediate fact. Rewrite `this` using `[if_pos hk]`.

Conclude with `Submodule.mem_inf.mp this`. Use `h3 k` as an intermediate fact. Rewrite `this` using `[if_neg hk]`. Conclude with `this`. Establish `hYmin : ∀ g ∈ XH p LL J M ρ w, ∀ k, g ∈ YCond p LL (min (J k) K) (M k)`.

Introduce `g hg k`. Take `⟨-, -, h3, h4, -⟩` from `hXH g hg`. Distinguish the cases in `hk : K + 1 ≤ J k`. Rewrite using `[show min (J k) K = K by omega]; exact (h3 k hk).1`. Rewrite using `[show min (J k) K = J k by omega]; exact h4 k hk`.

Establish `hPg : ∀ g ∈ XH p LL J M ρ w, ∀ j, P j g = g`. Introduce `g hg j`. Take `⟨hgP, -, hgT, -, -, -⟩` from `hXH g hg`. Distinguish the cases in `hj : j ≤ K`. Distinguish the cases in `hex : ∃ k, min (J k) K = j`.

Take `⟨k, hk⟩` from `hex`. Take `⟨k0, hk0, hmin⟩` from `Finset.exists_min_image (univ.filter fun k => min (J k) K = j) M ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩`. Establish `hk0' : min (J k0) K = j` using `(Finset.mem_filter.mp hk0).2`. Use `ycond_fix LL j (Tu j) (M k0) (P j) (hTPu j hj) (fun la hla => ?_) g ⟨?_, hgP⟩` and prove the remaining obligations. Rewrite using `[hTu']`.

Introduce `k' hk'`. Conclude with `hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))`. Use `hYmin g hg k0` as an intermediate fact. Rewrite `this` using `[hk0']`. Then use the resulting hypothesis. Use `idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPu j hj).1 ?_ g` and prove the remaining obligations.

Rewrite using `[(hTPu j hj).2.2]`. Use `le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le` and prove the remaining obligations. Rewrite using `[hTu']`. Introduce `k hk`. Conclude with `absurd ⟨k, hk⟩ hex`.

Distinguish the cases in `hex : ∃ k, K + 1 ≤ J k`. Take `⟨k, hk⟩` from `hex`. Take `⟨k0, hk0, hmin⟩` from `Finset.exists_min_image (univ.filter fun k => K + 1 ≤ J k) M ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩`. Establish `hk0' : K + 1 ≤ J k0` using `(Finset.mem_filter.mp hk0).2`. Use `idempotent_apply_eq_self_of_mem_range (P j) (hTPe j hj).1 g ?_` and prove the remaining obligations.

Rewrite using `[(hTPe j hj).2.1]`. Establish `hgt` using `(hgT k0 hk0').2`. Unfold `TypesLE at hgt`. Use `SetLike.le_def.mp (iSup_le fun la => iSup_le fun hla => ?_) hgt` and prove the remaining obligations. Use `le_iSup₂_of_le (f := fun la (_ : la ∈ Te) => IsoC p LL (K + 1) (univ.erase ρ) la) la ?_ le_rfl` and prove the remaining obligations.

Rewrite using `[hTe']`. Introduce `k' hk'`. Conclude with `hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))`. Use `idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPe j hj).1 ?_ g` and prove the remaining obligations. Rewrite using `[(hTPe j hj).2.2]`.

Use `le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le` and prove the remaining obligations. Rewrite using `[hTe']`. Introduce `k hk`. Conclude with `absurd ⟨k, hk⟩ hex`. Take `⟨G, hG⟩ : ∃ G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p], G = fun u => resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) u))` from `⟨_, rfl⟩`.

Take `⟨f, hf⟩ : ∃ f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p], f = fun m => if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then G (monomial m 1) else 0` from `⟨_, rfl⟩`. Use `⟨(MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, ?_⟩` and prove the remaining obligations. Introduce `m hm hm0`. Establish `hPr : (MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m`. Establish `h` using `(MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m`.

Rewrite `h` using `[MvPolynomial.coe_basisMonomials]`. Then use the resulting hypothesis. Rewrite using `[hPr]`. Distinguish the cases in `hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c`. Use `swap`. Establish `h0 : f m = 0` using `by rw [hf]; exact if_neg hw`.

Rewrite using `[h0, smul_zero]`. Use `⟨zero_mem _, zero_mem _, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[fock_right_zero', fock_monomial_zero']`. Introduce `hmg`. Take `⟨-, -, -, -, -, hgw⟩` from `hXH g hg`.

Conclude with `hw (mem_of_mem_support_restrictSupport hgw hmg)`. Establish `hfm : f m = resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) (monomial m 1)))`. Rewrite using `[hf, hG]`. Conclude with `if_pos hw`. Rewrite using `[hfm]`.

Establish `hu_pol : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ Pol p r LL` using `monomial_mem_supp' {m | MultiDeg LL m} m hm`. Establish `hu_ws : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ WtSpC p LL (K + 1) univ w` using `monomial_mem_supp' _ m hw`. Establish `hu_int : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ IntPol p (Fin (K + 1) × Fin r)`. Rewrite using `[intPol_iff_norm]`. Introduce `n`.

Rewrite using `[MvPolynomial.coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`. Use `set y := lcomp P (List.range (K + 2)) (monomial m 1) with hy`. Establish `hy_ws : y ∈ WtSpC p LL (K + 1) univ w` using `lcomp_keep P (WtSpC p LL (K + 1) univ w : Set _) _ (fun j _ u hu => hPws j u hu) _ hu_ws`. Establish `hy_pol : y ∈ Pol p r LL` using `lcomp_keep P (Pol p r LL : Set _) _ (fun j _ u hu => hPpol j u hu) _ hu_pol`.

Establish `hy_fix : ∀ j, j ≤ K + 1 → P j y = y` using `fun j hj => lcomp_fix P hPP hcomm _ j (List.mem_range.mpr (by omega)) _`. Use `set z := PE y with hz`. Establish `hz_rng : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w`. Rewrite using `[← hE2]`. Conclude with `LinearMap.mem_range_self PE y`.

Establish `hz_pol : z ∈ Pol p r LL` using `hPEpol y ⟨hy_pol, hy_ws⟩`. Establish `hz_fix : ∀ j, j ≤ K + 1 → P j z = z`. Introduce `j hj`. Rewrite using `[hz, ← hPEc (P j) (hPgl j) (hPws j) y hy_ws, hy_fix j hj]`. Use `set x := resL p (Fin.last K, ρ) 0 z with hx`.

Establish `hx_fix : ∀ j, j ≤ K + 1 → P j x = x`. Introduce `j hj`. Rewrite using `[hx, hPres, hz_fix j hj]`. Establish `hx_pol : x ∈ Pol p r LL` using `resL_keep_supp (Fin.last K, ρ) 0 {m | MultiDeg LL m} z hz_pol`. Establish `hx_free : x ∈ FreeOf p (Fin.last K, ρ)` using `resL_free _ z`.

Establish `hx_ws : x ∈ WtSpC p LL (K + 1) univ w` using `resL_keep_supp _ 0 _ z hz_rng.2`. Establish `hres : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ u, resL p (Fin.last K, ρ) 0 (glAct p LL (K + 1) c d u) = glAct p LL (K + 1) c d (resL p (Fin.last K, ρ) 0 u)`. Introduce `c hc d hd u`. Use `resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ => ?_) u` and prove the remaining obligations. Conclude with `⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2, fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩`.

Establish `hx_hwc : x ∈ HWC p LL (K + 1) (univ.erase ρ) w`. Establish `hzh : z ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL (K + 1) c d)` using `hz_rng.1`. Use `show x ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL (K + 1) c d)`. Rewrite `hzh`, the goal using `[Submodule.mem_inf]`. Use `⟨resL_keep_supp _ 0 _ z hzh.1, ?_⟩` and prove the remaining obligations.

Establish `h2` using `hzh.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢`. Introduce `c d hcd`. Rewrite using `[hx, ← hres c hcd.1 d hcd.2.1 z, h2 c d hcd, map_zero]`. Establish `hxY : ∀ k, x ∈ YCond p LL (min (J k) K) (M k)`.

Introduce `k`. Rewrite using `[← hx_fix (min (J k) K) (by omega)]`. Conclude with `typeProj_range_le_ycond LL _ (Tu _) (M k) (P _) (hTPu _ (by omega)) (fun la hla => (hTu' _ la).mp hla k rfl) x`. Establish `hxT : ∀ k, K + 1 ≤ J k → x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)`. Introduce `k hk`.

Establish `h1 : x ∈ ⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la`. Rewrite using `[← (hTPe (K + 1) (by omega)).2.1, ← hx_fix (K + 1) le_rfl]`. Conclude with `LinearMap.mem_range_self _ x`. Establish `hle : (⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la) ≤ TypesLE p LL (K + 1) (univ.erase ρ) (M k)`. Unfold `TypesLE`.

Conclude with `iSup₂_le fun la hla => le_iSup₂_of_le la ((hTe' la).mp hla k hk) le_rfl`. Conclude with `hle h1`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show x ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓ ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k) else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w`. Use `⟨⟨⟨⟨hx_pol, hx_free⟩, ?_⟩, hx_hwc⟩, hx_ws⟩` and prove the remaining obligations.

Apply `(Submodule.mem_iInf _).mpr` to reduce the goal to its premises. Introduce `k`. Use `split_ifs with hk`. Establish `h1` using `hxY k`. Rewrite `h1` using `[show min (J k) K = K by omega]`.

Conclude with `⟨h1, hxT k hk⟩`. Establish `h1` using `hxY k`. Rewrite `h1` using `[show min (J k) K = J k by omega]`. Then use the resulting hypothesis. Establish `hyZ` using `lcomp_int LL e1 P hPpol hPint (List.range (K + 2)) (monomial m 1) ⟨hu_pol, hu_int⟩`. Rewrite `hyZ` using `[List.length_range]`.

Establish `hzI` using `hE5 _ hyZ (Submodule.smul_mem _ _ hy_ws)`. Rewrite `hzI` using `[map_smul, smul_smul, ← pow_add]`. Establish `hxI` using `initPart_int (Fin.last K, ρ) 0 _ hzI`. Establish `he : ((p : ℚ_[p]) ^ ((K + 3) * e1)) • x = resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (e1 + e1 * (K + 2))) • z)`. Rewrite using `[map_smul, hx, show (K + 3) * e1 = e1 + e1 * (K + 2) by ring]`.

Rewrite using `[he]`. Conclude with `hxI`. Introduce `g hg`. Take `⟨-, hgF, -, -, hgH, hgW⟩` from `hXH g hg`. Establish `f1 : fock p g x = fock p g z`.

Rewrite using `[hx]`. Unfold `fock`. Use `Finset.sum_congr rfl (fun n hn => ?_)` and prove the remaining obligations. Establish `h1 : (resL p (Fin.last K, ρ) 0 z).coeff n = z.coeff n` using `by show (initPart (Fin.last K, ρ) 0 z).coeff n = _`. Rewrite using `[coeff_initPart, if_pos (show n (Fin.last K, ρ) = 0 from mem_of_mem_support_restrictSupport hgF hn)]`.

Rewrite using `[h1]`. Establish `f2 : fock p g z = fock p g y`. Rewrite using `[hz, ← hE4 g y hgW hy_ws, hPEfix g ⟨hgH, hgW⟩]`. Establish `f3 : fock p g y = fock p g (monomial m 1)` using `lcomp_fock P hPsa g (hPg g hg) _ _`. Rewrite using `[f1, f2, f3]`.
-/
theorem highest_vector_projection : ProjX := by
  classical
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hP hE
  have h0ρ : (0 : Fin r) ≠ ρ := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero] at h'
    omega
  have h0e : (0 : Fin r) ∈ univ.erase ρ := Finset.mem_erase.mpr ⟨h0ρ, Finset.mem_univ _⟩
  obtain ⟨Tu, hTu⟩ : ∃ Tu : ℕ → Set (Fin r → ℤ),
      Tu = fun j => {la | ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := ⟨_, rfl⟩
  obtain ⟨Te, hTe⟩ : ∃ Te : Set (Fin r → ℤ),
      Te = {la | ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := ⟨_, rfl⟩
  have hTu' : ∀ j la, la ∈ Tu j ↔ ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k := by
    intro j la; rw [hTu]; rfl
  have hTe' : ∀ la, la ∈ Te ↔ ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k := by
    intro la; rw [hTe]; rfl
  have hsatU : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := by
    intro T la la' h
    have : la = la' := funext fun c => h c (Finset.mem_univ c)
    rw [this]
  have hsatE : CsSaturated (univ.erase ρ) Te := by
    intro la la' h
    have h0 : la 0 = la' 0 := h 0 h0e
    rw [hTe', hTe', h0]
  obtain ⟨hPex, hPcomm⟩ := hP
  choose Pu hPu using fun (j : ℕ) (hj : j ≤ K) => hPex j (by omega) univ (Or.inl rfl) (Tu j) (hsatU _)
  obtain ⟨Pe, hPe1, hPe2, hPe3⟩ := hPex (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl) Te hsatE
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), P = fun j => if h : j ≤ K then Pu j h else Pe := ⟨_, rfl⟩
  have hPu_eq : ∀ j (hj : j ≤ K), P j = Pu j hj := by intro j hj; rw [hPdef]; simp [hj]
  have hPe_eq : ∀ j, ¬ j ≤ K → P j = Pe := by intro j hj; rw [hPdef]; simp [hj]
  have hTPu : ∀ j (hj : j ≤ K), IsTypeProj p LL j univ (Tu j) (P j) := by
    intro j hj; rw [hPu_eq j hj]; exact (hPu j hj).1
  have hTPe : ∀ j, ¬ j ≤ K → IsTypeProj p LL (K + 1) (univ.erase ρ) Te (P j) := by
    intro j hj; rw [hPe_eq j hj]; exact hPe1
  have hPP : ∀ j x, P j (P j x) = P j x := by
    intro j x
    by_cases hj : j ≤ K
    · exact LinearMap.congr_fun (hTPu j hj).1 x
    · exact LinearMap.congr_fun (hTPe j hj).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    by_cases hj : j ≤ K <;> by_cases hj' : j' ≤ K
    · rcases le_total j j' with h | h
      · exact LinearMap.congr_fun (hPcomm j j' univ univ (Tu j) (Tu j') (P j) (P j') h subset_rfl
          (Or.inl rfl) (Or.inl rfl) (hTPu j hj) (hTPu j' hj')) x
      · exact (LinearMap.congr_fun (hPcomm j' j univ univ (Tu j') (Tu j) (P j') (P j) h subset_rfl
          (Or.inl rfl) (Or.inl rfl) (hTPu j' hj') (hTPu j hj)) x).symm
    · exact LinearMap.congr_fun (hPcomm j (K + 1) univ (univ.erase ρ) (Tu j) Te (P j) (P j') (by omega)
          (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j hj) (hTPe j' hj')) x
    · exact (LinearMap.congr_fun (hPcomm j' (K + 1) univ (univ.erase ρ) (Tu j') Te (P j') (P j) (by omega)
          (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j' hj') (hTPe j hj)) x).symm
    · rw [hPe_eq j hj, hPe_eq j' hj']
  have hPsa : ∀ j F G, fock p (P j F) G = fock p F (P j G) := by
    intro j F G
    by_cases hj : j ≤ K
    · rw [hPu_eq j hj]; exact (hPu j hj).2.1 F G
    · rw [hPe_eq j hj]; exact hPe2 F G
  have hPint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin (K + 1) × Fin r) := by
    intro j F hF
    by_cases hj : j ≤ K
    · rw [hPu_eq j hj]; exact (hPu j hj).2.2 F hF
    · rw [hPe_eq j hj]; exact hPe3 F hF
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := by
    intro j x hx
    by_cases hj : j ≤ K
    · exact typeProj_polC LL j univ (Tu j) (P j) (hTPu j hj) x hx
    · exact typeProj_polC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) x hx
  have hPgl : ∀ j, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      P j (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P j x) := by
    intro j c hc d hd x
    by_cases hj : j ≤ K
    · exact typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c d x
    · exact typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc d hd x
  have hPdiag : ∀ j c x, P j (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P j x) := by
    intro j c x
    by_cases hj : j ≤ K
    · exact typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c c x
    · by_cases hc : c = ρ
      · rw [hc]
        exact typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (glAct p LL (K + 1) ρ ρ)
          (fun a ha b hb y => cartan_comm_erase' LL (K + 1) ρ a ha b hb y) x
      · have hc' : c ∈ univ.erase ρ := Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩
        exact typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc' c hc' x
  have hPws : ∀ j, ∀ x ∈ WtSpC p LL (K + 1) univ w, P j x ∈ WtSpC p LL (K + 1) univ w :=
    fun j => comm_wtsp LL (K + 1) (P j) (hPdiag j) w
  have hPres : ∀ j x, P j (resL p (Fin.last K, ρ) 0 x) = resL p (Fin.last K, ρ) 0 (P j x) := by
    intro j x
    by_cases hj : j ≤ K
    · refine typeProj_commC LL j univ (Tu j) (P j) (hTPu j hj) (resL p (Fin.last K, ρ) 0)
        (fun c _ d _ y => resL_glAct LL j c d (Fin.last K, ρ) 0 ?_ y) x
      intro i hi
      have hne : i ≠ Fin.last K := by
        intro h
        rw [h, Fin.val_last] at hi
        omega
      exact ⟨fun h => hne (Prod.ext_iff.mp h).1, fun h => hne (Prod.ext_iff.mp h).1⟩
    · refine typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (resL p (Fin.last K, ρ) 0)
        (fun c hc d hd y => resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 ?_ y) x
      intro i _
      exact ⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2,
        fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩
  obtain ⟨PE, hE1, hE2, hE3, hE4, hE5⟩ := hE (K + 1) le_rfl w
  have hPEc : ∀ A : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
        A (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (A x)) →
      (∀ x ∈ WtSpC p LL (K + 1) univ w, A x ∈ WtSpC p LL (K + 1) univ w) →
      ∀ x ∈ WtSpC p LL (K + 1) univ w, PE (A x) = A (PE x) :=
    fun A hA hW => hwProj_comm' LL (K + 1) ρ w PE A hE1 hE2 hE3 hA hW
  have hPEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w, PE g = g := by
    intro g hg
    exact idempotent_apply_eq_self_of_mem_range PE hE1 g (by rw [hE2]; exact hg)
  have hPEpol : ∀ y ∈ Pol p r LL ⊓ WtSpC p LL (K + 1) univ w, PE y ∈ Pol p r LL := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [pol_iff_eul] at hy1 ⊢
    intro i
    have hc := hPEc (ProjS.eulL (fun c : Fin r => (i, c)))
      (fun c _ d _ x => eul_glAct LL (K + 1) i c d x)
      (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i c c x) w) y hy2
    rw [← hc, hy1 i, map_smul]

  have hXH : ∀ g ∈ XH p LL J M ρ w, g ∈ Pol p r LL ∧ g ∈ FreeOf p (Fin.last K, ρ) ∧
      (∀ k, K + 1 ≤ J k → g ∈ YCond p LL K (M k) ∧ g ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧
      (∀ k, ¬ K + 1 ≤ J k → g ∈ YCond p LL (J k) (M k)) ∧
      g ∈ HWC p LL (K + 1) (univ.erase ρ) w ∧ g ∈ WtSpC p LL (K + 1) univ w := by
    intro g hg
    have hg' : g ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
        ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
          else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w := hg
    simp only [Submodule.mem_inf, Submodule.mem_iInf] at hg'
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hg'
    refine ⟨h1, h2, fun k hk => ?_, fun k hk => ?_, h4, h5⟩
    · have := h3 k
      rw [if_pos hk] at this
      exact Submodule.mem_inf.mp this
    · have := h3 k
      rw [if_neg hk] at this
      exact this
  have hYmin : ∀ g ∈ XH p LL J M ρ w, ∀ k, g ∈ YCond p LL (min (J k) K) (M k) := by
    intro g hg k
    obtain ⟨-, -, h3, h4, -⟩ := hXH g hg
    by_cases hk : K + 1 ≤ J k
    · rw [show min (J k) K = K by omega]; exact (h3 k hk).1
    · rw [show min (J k) K = J k by omega]; exact h4 k hk

  have hPg : ∀ g ∈ XH p LL J M ρ w, ∀ j, P j g = g := by
    intro g hg j
    obtain ⟨hgP, -, hgT, -, -, -⟩ := hXH g hg
    by_cases hj : j ≤ K
    · by_cases hex : ∃ k, min (J k) K = j
      · obtain ⟨k, hk⟩ := hex
        obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image (univ.filter fun k => min (J k) K = j) M
          ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
        have hk0' : min (J k0) K = j := (Finset.mem_filter.mp hk0).2
        refine ycond_fix LL j (Tu j) (M k0) (P j) (hTPu j hj) (fun la hla => ?_) g ⟨?_, hgP⟩
        · rw [hTu']
          intro k' hk'
          exact hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))
        · have := hYmin g hg k0
          rwa [hk0'] at this
      · refine idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPu j hj).1 ?_ g
        rw [(hTPu j hj).2.2]
        refine le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le
        rw [hTu']
        intro k hk
        exact absurd ⟨k, hk⟩ hex
    · by_cases hex : ∃ k, K + 1 ≤ J k
      · obtain ⟨k, hk⟩ := hex
        obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image (univ.filter fun k => K + 1 ≤ J k) M
          ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
        have hk0' : K + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
        refine idempotent_apply_eq_self_of_mem_range (P j) (hTPe j hj).1 g ?_
        rw [(hTPe j hj).2.1]
        have hgt := (hgT k0 hk0').2
        unfold TypesLE at hgt
        refine SetLike.le_def.mp (iSup_le fun la => iSup_le fun hla => ?_) hgt
        refine le_iSup₂_of_le (f := fun la (_ : la ∈ Te) => IsoC p LL (K + 1) (univ.erase ρ) la) la ?_ le_rfl
        rw [hTe']
        intro k' hk'
        exact hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))
      · refine idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPe j hj).1 ?_ g
        rw [(hTPe j hj).2.2]
        refine le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le
        rw [hTe']
        intro k hk
        exact absurd ⟨k, hk⟩ hex

  obtain ⟨G, hG⟩ : ∃ G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      G = fun u => resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) u)) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      f = fun m => if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then G (monomial m 1) else 0 :=
    ⟨_, rfl⟩
  refine ⟨(MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, ?_⟩
  intro m hm hm0
  have hPr : (MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m := by
    have h := (MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m
    rwa [MvPolynomial.coe_basisMonomials] at h
  rw [hPr]
  by_cases hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c
  swap
  · have h0 : f m = 0 := by rw [hf]; exact if_neg hw
    rw [h0, smul_zero]
    refine ⟨zero_mem _, zero_mem _, fun g hg => ?_⟩
    rw [fock_right_zero', fock_monomial_zero']
    intro hmg
    obtain ⟨-, -, -, -, -, hgw⟩ := hXH g hg
    exact hw (mem_of_mem_support_restrictSupport hgw hmg)
  have hfm : f m = resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) (monomial m 1))) := by
    rw [hf, hG]; exact if_pos hw
  rw [hfm]

  have hu_pol : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ Pol p r LL :=
    monomial_mem_supp' {m | MultiDeg LL m} m hm
  have hu_ws : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ WtSpC p LL (K + 1) univ w :=
    monomial_mem_supp' _ m hw
  have hu_int : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ IntPol p (Fin (K + 1) × Fin r) := by
    rw [intPol_iff_norm]
    intro n
    rw [MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  set y := lcomp P (List.range (K + 2)) (monomial m 1) with hy
  have hy_ws : y ∈ WtSpC p LL (K + 1) univ w :=
    lcomp_keep P (WtSpC p LL (K + 1) univ w : Set _) _ (fun j _ u hu => hPws j u hu) _ hu_ws
  have hy_pol : y ∈ Pol p r LL :=
    lcomp_keep P (Pol p r LL : Set _) _ (fun j _ u hu => hPpol j u hu) _ hu_pol
  have hy_fix : ∀ j, j ≤ K + 1 → P j y = y := fun j hj =>
    lcomp_fix P hPP hcomm _ j (List.mem_range.mpr (by omega)) _
  set z := PE y with hz
  have hz_rng : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w := by
    rw [← hE2]; exact LinearMap.mem_range_self PE y
  have hz_pol : z ∈ Pol p r LL := hPEpol y ⟨hy_pol, hy_ws⟩
  have hz_fix : ∀ j, j ≤ K + 1 → P j z = z := by
    intro j hj
    rw [hz, ← hPEc (P j) (hPgl j) (hPws j) y hy_ws, hy_fix j hj]
  set x := resL p (Fin.last K, ρ) 0 z with hx
  have hx_fix : ∀ j, j ≤ K + 1 → P j x = x := by
    intro j hj
    rw [hx, hPres, hz_fix j hj]

  have hx_pol : x ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 {m | MultiDeg LL m} z hz_pol
  have hx_free : x ∈ FreeOf p (Fin.last K, ρ) := resL_free _ z
  have hx_ws : x ∈ WtSpC p LL (K + 1) univ w := resL_keep_supp _ 0 _ z hz_rng.2
  have hres : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ u,
      resL p (Fin.last K, ρ) 0 (glAct p LL (K + 1) c d u) = glAct p LL (K + 1) c d (resL p (Fin.last K, ρ) 0 u) := by
    intro c hc d hd u
    refine resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ => ?_) u
    exact ⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2,
      fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩
  have hx_hwc : x ∈ HWC p LL (K + 1) (univ.erase ρ) w := by
    have hzh : z ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d),
          LinearMap.ker (glAct p LL (K + 1) c d) := hz_rng.1
    show x ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d),
          LinearMap.ker (glAct p LL (K + 1) c d)
    rw [Submodule.mem_inf] at hzh ⊢
    refine ⟨resL_keep_supp _ 0 _ z hzh.1, ?_⟩
    have h2 := hzh.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro c d hcd
    rw [hx, ← hres c hcd.1 d hcd.2.1 z, h2 c d hcd, map_zero]
  have hxY : ∀ k, x ∈ YCond p LL (min (J k) K) (M k) := by
    intro k
    rw [← hx_fix (min (J k) K) (by omega)]
    exact typeProj_range_le_ycond LL _ (Tu _) (M k) (P _) (hTPu _ (by omega))
      (fun la hla => (hTu' _ la).mp hla k rfl) x
  have hxT : ∀ k, K + 1 ≤ J k → x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k) := by
    intro k hk
    have h1 : x ∈ ⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la := by
      rw [← (hTPe (K + 1) (by omega)).2.1, ← hx_fix (K + 1) le_rfl]
      exact LinearMap.mem_range_self _ x
    have hle : (⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la)
        ≤ TypesLE p LL (K + 1) (univ.erase ρ) (M k) := by
      unfold TypesLE
      exact iSup₂_le fun la hla => le_iSup₂_of_le la ((hTe' la).mp hla k hk) le_rfl
    exact hle h1
  refine ⟨?_, ?_, ?_⟩
  · show x ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
        ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
          else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w
    refine ⟨⟨⟨⟨hx_pol, hx_free⟩, ?_⟩, hx_hwc⟩, hx_ws⟩
    apply (Submodule.mem_iInf _).mpr
    intro k
    split_ifs with hk
    · have h1 := hxY k
      rw [show min (J k) K = K by omega] at h1
      exact ⟨h1, hxT k hk⟩
    · have h1 := hxY k
      rwa [show min (J k) K = J k by omega] at h1
  · have hyZ := lcomp_int LL e1 P hPpol hPint (List.range (K + 2)) (monomial m 1) ⟨hu_pol, hu_int⟩
    rw [List.length_range] at hyZ
    have hzI := hE5 _ hyZ (Submodule.smul_mem _ _ hy_ws)
    rw [map_smul, smul_smul, ← pow_add] at hzI
    have hxI := initPart_int (Fin.last K, ρ) 0 _ hzI
    have he : ((p : ℚ_[p]) ^ ((K + 3) * e1)) • x
        = resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (e1 + e1 * (K + 2))) • z) := by
      rw [map_smul, hx, show (K + 3) * e1 = e1 + e1 * (K + 2) by ring]
    rw [he]
    exact hxI
  · intro g hg
    obtain ⟨-, hgF, -, -, hgH, hgW⟩ := hXH g hg
    have f1 : fock p g x = fock p g z := by
      rw [hx]
      unfold fock
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have h1 : (resL p (Fin.last K, ρ) 0 z).coeff n = z.coeff n := by
        show (initPart (Fin.last K, ρ) 0 z).coeff n = _
        rw [coeff_initPart, if_pos (show n (Fin.last K, ρ) = 0 from mem_of_mem_support_restrictSupport hgF hn)]
      rw [h1]
    have f2 : fock p g z = fock p g y := by
      rw [hz, ← hE4 g y hgW hy_ws, hPEfix g ⟨hgH, hgW⟩]
    have f3 : fock p g y = fock p g (monomial m 1) := lcomp_fock P hPsa g (hPg g hg) _ _
    rw [f1, f2, f3]

end Formalism.InvariantFactorPaths.L4
