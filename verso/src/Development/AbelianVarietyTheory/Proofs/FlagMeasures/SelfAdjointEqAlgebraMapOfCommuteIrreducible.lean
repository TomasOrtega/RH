import Mathlib

open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Break down `subsingleton_or_nontrivial H with hH | hH` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Simplify using `[Subsingleton.elim u 0]`. Take `⟨r, hr⟩` from `ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA`.

Establish `hsub : ∀ s ∈ spectrum ℝ A, s = r`. Introduce `s hs`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b, hb, hab⟩ : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ A, a < b := by`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases.

Conclude with `⟨s, hs, r, hr, h⟩`. Conclude with `⟨r, hr, s, hs, h⟩`. Use `set c : ℝ := (a + b) / 2 with hc_def`. Use `set f : ℝ → ℝ := fun x => max (c - x) 0 with hf_def`. Use `set k : ℝ → ℝ := fun x => max (x - c) 0 with hk_def`.

Establish `hfk : (fun x => k x * f x) = (0 : ℝ → ℝ)`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.zero_apply, hf_def, hk_def]`. Break down `le_total x c with h | h` into its components or cases. Rewrite using `[max_eq_right (by linarith : x - c ≤ 0), zero_mul]`.

Rewrite using `[max_eq_right (by linarith : c - x ≤ 0), mul_zero]`. Establish `hprod : cfc k A * cfc f A = 0`. Rewrite using `[← cfc_mul k f A, hfk, cfc_zero]`. Establish `hF : cfc f A ≠ 0`. Introduce `h0`.

Use `(eqOn_of_cfc_eq_cfc (f := f) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) ha` as an intermediate fact. Simplify using `only [Pi.zero_apply, hf_def] at this`. Establish `: c - a ≤ 0`. Rewrite using `[← this]`. Conclude with `le_max_left _ _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : cfc k A ≠ 0`. Introduce `h0`. Use `(eqOn_of_cfc_eq_cfc (f := k) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) hb` as an intermediate fact. Simplify using `only [Pi.zero_apply, hk_def] at this`.

Establish `: b - c ≤ 0`. Rewrite using `[← this]`. Conclude with `le_max_left _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcomm : ∀ g, Commute (cfc k A) (π g)` using `fun g => (hc g).cfc_real k`.

Set `S : Submodule ℂ H` to `LinearMap.ker (cfc k A).toLinearMap`. Establish `hS : S = ⊥ ∨ S = ⊤`. Use `hirr S ?_ ?_` and prove the remaining obligations. Conclude with `(cfc k A).isClosed_ker`. Introduce `g u hu`.

Establish `hu' : cfc k A u = 0` using `hu`. Use `show cfc k A (π g u) = 0`. Use `congrArg (fun T : H →L[ℂ] H => T u) (hcomm g).eq` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`. Rewrite using `[this, hu', map_zero]`.

Break down `hS with hS | hS` into its components or cases. Apply `hF` to reduce the goal to its premises. Use extensionality with `v`. Establish `hv : cfc f A v ∈ S` using `by show cfc k A (cfc f A v) = 0`. Rewrite using `[← ContinuousLinearMap.mul_apply, hprod, ContinuousLinearMap.zero_apply]`.

Rewrite `hv` using `[hS, Submodule.mem_bot]`. Simplify using `using hv`. Apply `hK` to reduce the goal to its premises. Use extensionality with `v`. Establish `hv : v ∈ S` using `hS ▸ Submodule.mem_top`.

Establish `hv' : cfc k A v = 0` using `hv`. Rewrite using `[ContinuousLinearMap.zero_apply]`. Conclude with `hv'`. Use `⟨r, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem selfAdjoint_eq_algebraMap_of_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (π g)) :
    ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · refine ⟨0, ?_⟩
    ext u
    simp [Subsingleton.elim u 0]
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hsub : ∀ s ∈ spectrum ℝ A, s = r := by
    intro s hs
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ A, a < b := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨s, hs, r, hr, h⟩
      · exact ⟨r, hr, s, hs, h⟩
    set c : ℝ := (a + b) / 2 with hc_def
    set f : ℝ → ℝ := fun x => max (c - x) 0 with hf_def
    set k : ℝ → ℝ := fun x => max (x - c) 0 with hk_def
    have hfk : (fun x => k x * f x) = (0 : ℝ → ℝ) := by
      funext x
      simp only [Pi.zero_apply, hf_def, hk_def]
      rcases le_total x c with h | h
      · rw [max_eq_right (by linarith : x - c ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : c - x ≤ 0), mul_zero]
    have hprod : cfc k A * cfc f A = 0 := by
      rw [← cfc_mul k f A, hfk, cfc_zero]
    have hF : cfc f A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := f) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) ha
      simp only [Pi.zero_apply, hf_def] at this
      have : c - a ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hK : cfc k A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := k) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) hb
      simp only [Pi.zero_apply, hk_def] at this
      have : b - c ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hcomm : ∀ g, Commute (cfc k A) (π g) := fun g => (hc g).cfc_real k
    let S : Submodule ℂ H := LinearMap.ker (cfc k A).toLinearMap
    have hS : S = ⊥ ∨ S = ⊤ := by
      refine hirr S ?_ ?_
      · exact (cfc k A).isClosed_ker
      · intro g u hu
        have hu' : cfc k A u = 0 := hu
        show cfc k A (π g u) = 0
        have := congrArg (fun T : H →L[ℂ] H => T u) (hcomm g).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hu', map_zero]
    rcases hS with hS | hS
    · apply hF
      ext v
      have hv : cfc f A v ∈ S := by
        show cfc k A (cfc f A v) = 0
        rw [← ContinuousLinearMap.mul_apply, hprod, ContinuousLinearMap.zero_apply]
      rw [hS, Submodule.mem_bot] at hv
      simpa using hv
    · apply hK
      ext v
      have hv : v ∈ S := hS ▸ Submodule.mem_top
      have hv' : cfc k A v = 0 := hv
      rw [ContinuousLinearMap.zero_apply]
      exact hv'
  refine ⟨r, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A).symm
    _ = cfc (fun _ : ℝ => r) A := cfc_congr (fun s hs => hsub s hs)
    _ = algebraMap ℝ (H →L[ℂ] H) r := cfc_const r A

/- English proof (translation)
Establish `hinner : ∀ g (u v : H), ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ`. Introduce `g u v`. Set `L : H →ₗᵢ[ℂ] H` to `⟨(π g).toLinearMap, hπ g⟩`. Conclude with `L.inner_map_map u v`. Establish `hinv : ∀ g (v : H), π g (π g⁻¹ v) = v`.

Introduce `g v`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `hadj : ∀ g, ContinuousLinearMap.adjoint (π g) = π g⁻¹`. Introduce `g`. Use `symm`.

Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `u v`. Rewrite using `[← hinner g (π g⁻¹ u) v, hinv]`. Establish `hstar : ∀ g, star (π g) = π g⁻¹` using `hadj`. Establish `hcT : ∀ g, Commute T (π g)` using `fun g => hT g`.

Establish `hcS : ∀ g, Commute (star T) (π g)`. Introduce `g`. Establish `h1` using `(hcT g⁻¹).star_star`. Rewrite `h1` using `[hstar, inv_inv]`. Conclude with `h1`.

Establish `hre : ∀ g, Commute (realPart T : H →L[ℂ] H) (π g)`. Introduce `g`. Rewrite using `[realPart_apply_coe]`. Conclude with `((hcT g).add_left (hcS g)).smul_left _`. Establish `him : ∀ g, Commute (imaginaryPart T : H →L[ℂ] H) (π g)`.

Introduce `g`. Rewrite using `[imaginaryPart_apply_coe]`. Conclude with `(((hcT g).sub_left (hcS g)).smul_left _).smul_left _`. Take `⟨a, ha⟩` from `selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (realPart T).2 hre`. Take `⟨b, hb⟩` from `selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (imaginaryPart T).2 him`.

Use `⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩` and prove the remaining obligations. Rewrite using `[← realPart_add_I_smul_imaginaryPart T, ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]`.
-/
theorem schur_unitary_irreducible (G H : Type) [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H))
    (hπ : ∀ g u, ‖π g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ g, T * π g = π g * T) : ∃ c : ℂ, T = c • 1 := by
  classical
  have hinner : ∀ g (u v : H), ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g u v
    let L : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hπ g⟩
    exact L.inner_map_map u v
  have hinv : ∀ g (v : H), π g (π g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hadj : ∀ g, ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
    intro g
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [← hinner g (π g⁻¹ u) v, hinv]
  have hstar : ∀ g, star (π g) = π g⁻¹ := hadj
  have hcT : ∀ g, Commute T (π g) := fun g => hT g
  have hcS : ∀ g, Commute (star T) (π g) := by
    intro g
    have h1 := (hcT g⁻¹).star_star
    rw [hstar, inv_inv] at h1
    exact h1
  have hre : ∀ g, Commute (realPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [realPart_apply_coe]
    exact ((hcT g).add_left (hcS g)).smul_left _
  have him : ∀ g, Commute (imaginaryPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [imaginaryPart_apply_coe]
    exact (((hcT g).sub_left (hcS g)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (realPart T).2 hre
  obtain ⟨b, hb⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (imaginaryPart T).2 him
  refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, ha, hb, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
