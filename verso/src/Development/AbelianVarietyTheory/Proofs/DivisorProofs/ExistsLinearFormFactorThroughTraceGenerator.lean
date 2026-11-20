import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

/- English proof (translation)
Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))`. Use `⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩` and prove the remaining obligations. Establish `: Ideal.absNorm (Ideal.span {t}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `ht`.

Conclude with `this` after adjusting the coercions. Rewrite using `[Int.cast_natCast, ← hc, mul_comm]`.
-/
theorem exists_int_eq_mul_of_ne_zero {E : Type} [Field E] [NumberField E] (t : 𝓞 E) (ht : t ≠ 0) :
    ∃ (N : ℤ) (c : 𝓞 E), N ≠ 0 ∧ (N : 𝓞 E) = t * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))
  refine ⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
    exact_mod_cast this
  · rw [Int.cast_natCast, ← hc, mul_comm]

/- English proof (translation)
Assume the negation of the conclusion as `ht`. Take `⟨N, c, hN, hc⟩` from `exists_int_eq_mul_of_ne_zero t ht`. Apply `hθ` to reduce the goal to its premises. Use extensionality with `v`. Use `h (c * v)` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul]`. Simplify `this` using `[hN]`.
-/
theorem eq_zero_of_forall_theta_mul {E : Type} [Field E] [NumberField E] {θ : 𝓞 E →+ ℤ} (hθ : θ ≠ 0)
    {t : 𝓞 E} (h : ∀ u, θ (t * u) = 0) : t = 0 := by
  by_contra ht
  obtain ⟨N, c, hN, hc⟩ := exists_int_eq_mul_of_ne_zero t ht
  apply hθ
  ext v
  have := h (c * v)
  rw [← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul] at this
  simpa [hN] using this

/- English proof (translation)
Introduce `E _ _ _ H D Z' θ s hs hgen w`. Establish `hθ : θ ≠ 0`. Introduce `h0`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Conclude with `hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))`. Take `⟨t, ht⟩` from `hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom`. Use `ht 1` as an intermediate fact. Simplify using `[h0] at this`.

Conclude with `hi this`. Establish `uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t'` using `fun t t' h => sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])`. Set `ψ : D.La → 𝓞 E →+ ℤ` to `fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])`. Use `choose T hT using fun x : Z' => hgen (ψ x)`. Use `⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩` and prove the remaining obligations.

Introduce `x y`. Apply `uniq` to reduce the goal to its premises. Introduce `u`. Rewrite using `[← hT (x + y) u, add_mul, map_add, ← hT x u, ← hT y u]`. Simplify using `[ψ, smul_add]`.

Introduce `c x show T (c • x) = c * T x`. Apply `uniq` to reduce the goal to its premises. Introduce `u`. Rewrite using `[← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]`. Simplify using `only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]`.

Rewrite using `[show s * u * c = s * (c * u) by ring]`. Use `show θ (T x) = _`. Use `hT x 1` as an intermediate fact. Rewrite `this` using `[mul_one, mul_one]`. Rewrite using `[← this]`.

Simplify using `only [ψ, AddMonoidHom.mk'_apply]`. Conclude with `D.adj s x w`.
-/
theorem exists_linear_theta_factor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  intro E _ _ _ H D Z' θ s hs hgen w
  have hθ : θ ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))
    obtain ⟨t, ht⟩ := hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom
    have := ht 1
    simp [h0] at this
    exact hi this
  have uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])
  let ψ : D.La → 𝓞 E →+ ℤ := fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])
  choose T hT using fun x : Z' => hgen (ψ x)
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩
  · intro x y
    apply uniq
    intro u
    rw [← hT (x + y) u, add_mul, map_add, ← hT x u, ← hT y u]
    simp [ψ, smul_add]
  · intro c x
    show T (c • x) = c * T x
    apply uniq
    intro u
    rw [← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]
    simp only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]
    rw [show s * u * c = s * (c * u) by ring]
  · show θ (T x) = _
    have := hT x 1
    rw [mul_one, mul_one] at this
    rw [← this]
    simp only [ψ, AddMonoidHom.mk'_apply]
    exact D.adj s x w

end GlobalTheory.LowFilt
