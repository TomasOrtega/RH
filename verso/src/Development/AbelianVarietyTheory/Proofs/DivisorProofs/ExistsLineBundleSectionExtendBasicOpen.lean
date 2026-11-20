import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecAff

/- English proof (translation)
The claim follows from `GlobalTheory.KS.rsT_of_le h s`.
-/
theorem rsT_eq_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) : rsT s V = rs h s :=
  GlobalTheory.KS.rsT_of_le h s

/- English proof (translation)
Introduce `X _ _ M hM f t ht`. Set `φ` to `(X.basicOpen f).ι`. Establish `hφ : φ.opensRange = X.basicOpen f` using `Scheme.Opens.opensRange_ι _`. Establish `hr : ∀ x, φ x ∈ X.basicOpen f`. Introduce `x`.

Establish `hx : φ x ∈ φ.opensRange` using `⟨x, rfl⟩`. Rewrite `hx` using `[hφ]`. Then use the resulting hypothesis. Establish `hc : ∀ c, φ ⁻¹ᵁ M.U c ≤ φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f)` using `fun c x hx => ⟨hx, hr x⟩`. Set `t' : ∀ c, Γ(↑(X.basicOpen f), φ ⁻¹ᵁ M.U c)` to `fun c => pa φ (hc c) (t c)`. Establish `ht' : ∀ i j, rs (inf_le_left : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U i) (t' i) = pa φ (le_pre_inf (inf_le_left.trans (le_refl (φ ⁻¹ᵁ M.U i))) (inf_le_right.trans (le_refl (φ ⁻¹ᵁ M.U j)))) (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs (inf_le_right : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U j …`.

Introduce `i j`. Establish `e : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ (M.U i ⊓ M.U j ⊓ X.basicOpen f)` using `fun x hx => ⟨⟨hx.1, hx.2⟩, hr x⟩`. Establish `h1 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ X.basicOpen f` using `inf_le_inf_right _ inf_le_left`. Establish `h2 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ M.U j` using `inf_le_left`. Establish `h3 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U j ⊓ X.basicOpen f` using `inf_le_inf_right _ inf_le_right`.

Use `ht i j` as an intermediate fact. Rewrite `this` using `[rsT_eq_rs h1, rsT_eq_rs h2, rsT_eq_rs h3]`. Use `congrArg (pa φ e) this` as an intermediate fact. Rewrite `this` using `[map_mul, pa_rs, pa_rs, pa_rs]`. Simplify using `only [t']`.

Rewrite using `[rs_pa, rs_pa]`. Conclude with `this`. Take `⟨N, s, hs⟩` from `sec_extend φ f hφ M hM (fun c => φ ⁻¹ᵁ M.U c) (fun c => le_rfl) (fun c => le_rfl) t' ht'`. Use `⟨N, s, fun c => ?_⟩` and prove the remaining obligations. Establish `hU : M.U c ⊓ X.basicOpen f ≤ φ.opensRange` using `by rw [hφ]; exact inf_le_right`.

Apply `(pa_bijective φ (le_refl (φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f))) le_rfl hU).1` to reduce the goal to its premises. Establish `hV : φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) ≤ φ ⁻¹ᵁ M.U c` using `fun x hx => hx.1`. Use `congrArg (rs hV) (hs c)` as an intermediate fact. Rewrite `this` using `[rs_pa, map_mul, map_pow, rs_pa]`. Simplify using `only [t'] at this`.

Rewrite `this` using `[rs_pa]`. Rewrite using `[rsT_eq_rs inf_le_left, rsT_eq_rs le_top, map_mul, map_pow, pa_rs, pa_rs, this]`.
-/
theorem sec_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  intro X _ _ M hM f t ht
  let φ := (X.basicOpen f).ι
  have hφ : φ.opensRange = X.basicOpen f := Scheme.Opens.opensRange_ι _
  have hr : ∀ x, φ x ∈ X.basicOpen f := by
    intro x
    have hx : φ x ∈ φ.opensRange := ⟨x, rfl⟩
    rwa [hφ] at hx
  have hc : ∀ c, φ ⁻¹ᵁ M.U c ≤ φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) := fun c x hx => ⟨hx, hr x⟩
  let t' : ∀ c, Γ(↑(X.basicOpen f), φ ⁻¹ᵁ M.U c) := fun c => pa φ (hc c) (t c)
  have ht' : ∀ i j, rs (inf_le_left : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U i) (t' i) =
      pa φ (le_pre_inf (inf_le_left.trans (le_refl (φ ⁻¹ᵁ M.U i)))
        (inf_le_right.trans (le_refl (φ ⁻¹ᵁ M.U j))))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U j) (t' j) := by
    intro i j
    have e : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ (M.U i ⊓ M.U j ⊓ X.basicOpen f) :=
      fun x hx => ⟨⟨hx.1, hx.2⟩, hr x⟩
    have h1 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have h2 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ M.U j := inf_le_left
    have h3 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U j ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    have := ht i j
    rw [rsT_eq_rs h1, rsT_eq_rs h2, rsT_eq_rs h3] at this
    have := congrArg (pa φ e) this
    rw [map_mul, pa_rs, pa_rs, pa_rs] at this
    simp only [t']
    rw [rs_pa, rs_pa]
    exact this
  obtain ⟨N, s, hs⟩ := sec_extend φ f hφ M hM (fun c => φ ⁻¹ᵁ M.U c) (fun c => le_rfl)
    (fun c => le_rfl) t' ht'
  refine ⟨N, s, fun c => ?_⟩
  have hU : M.U c ⊓ X.basicOpen f ≤ φ.opensRange := by rw [hφ]; exact inf_le_right
  apply (pa_bijective φ (le_refl (φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f))) le_rfl hU).1
  have hV : φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) ≤ φ ⁻¹ᵁ M.U c := fun x hx => hx.1
  have := congrArg (rs hV) (hs c)
  rw [rs_pa, map_mul, map_pow, rs_pa] at this
  simp only [t'] at this
  rw [rs_pa] at this
  rw [rsT_eq_rs inf_le_left, rsT_eq_rs le_top, map_mul, map_pow, pa_rs, pa_rs, this]

end GlobalTheory.SecAff
