import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
open CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OntoDLog

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

/- English proof (translation)
Simplify using `only [form, mul_smul]`.
-/
theorem form_mul_left {a : ℕ} (c g₀ : A) (g : Fin a → A) :
    form K (c * g₀) g = c • form K g₀ g := by
  simp only [form, mul_smul]

/- English proof (translation)
Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨h, Fin.cons f g, Or.inr ⟨0, by rw [Fin.cons_zero]; exact Ideal.mem_span_singleton_self f⟩, rfl⟩`.
-/
theorem form_cons_mem {a : ℕ} (f h : A) (g : Fin a → A) :
    form K h (Fin.cons f g : Fin (a + 1) → A) ∈ relOm K (Ideal.span {f}) (a + 1) := by
  apply Submodule.subset_span
  exact ⟨h, Fin.cons f g, Or.inr ⟨0, by rw [Fin.cons_zero]; exact Ideal.mem_span_singleton_self f⟩, rfl⟩

/- English proof (translation)
Use `set v : Fin (a + 1) → Ω[A⁄K] := fun i => KaehlerDifferential.D K A ((Fin.cons f (Function.update g k h) : Fin (a + 1) → A) i) with hv`. Establish `hcons : (fun i => KaehlerDifferential.D K A ((Fin.cons f g : Fin (a + 1) → A) i)) = Function.update v k.succ (f • KaehlerDifferential.D K A h + h • KaehlerDifferential.D K A f)`. Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]`.

Consider the case `succ j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `[hk, Derivation.leibniz]`. Simplify using `[v, hj, Function.update_apply]`.

Establish `hv1 : Function.update v k.succ (KaehlerDifferential.D K A h) = v`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = k.succ`. Substitute `hi` using the available equality. Simplify using `[v]`.

Simplify using `[Function.update_apply, hi]`. Establish `hv2 : exteriorPower.ιMulti A (a + 1) (Function.update v k.succ (KaehlerDifferential.D K A f)) = 0`. Apply `AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := k.succ)` to reduce the goal to its premises. Simplify using `[v, Function.update_apply, (Fin.succ_ne_zero k).symm]`. Conclude with `(Fin.succ_ne_zero k).symm`.

Simplify using `only [form]`. Rewrite using `[hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul, AlternatingMap.map_update_smul, hv1, hv2, smul_zero, add_zero, smul_comm]`.
-/
theorem form_cons_eq_smul {a : ℕ} (f h g₀ : A) (g : Fin a → A) (k : Fin a)
    (hk : g k = f * h) :
    form K g₀ (Fin.cons f g : Fin (a + 1) → A) =
      f • form K g₀ (Fin.cons f (Function.update g k h) : Fin (a + 1) → A) := by
  set v : Fin (a + 1) → Ω[A⁄K] := fun i =>
    KaehlerDifferential.D K A ((Fin.cons f (Function.update g k h) : Fin (a + 1) → A) i) with hv
  have hcons : (fun i => KaehlerDifferential.D K A ((Fin.cons f g : Fin (a + 1) → A) i)) =
      Function.update v k.succ (f • KaehlerDifferential.D K A h + h • KaehlerDifferential.D K A f) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    | succ j =>
      by_cases hj : j = k
      · subst hj
        simp [hk, Derivation.leibniz]
      · simp [v, hj, Function.update_apply]
  have hv1 : Function.update v k.succ (KaehlerDifferential.D K A h) = v := by
    funext i
    by_cases hi : i = k.succ
    · subst hi
      simp [v]
    · simp [Function.update_apply, hi]
  have hv2 : exteriorPower.ιMulti A (a + 1) (Function.update v k.succ (KaehlerDifferential.D K A f)) = 0 := by
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := k.succ)
    · simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    · exact (Fin.succ_ne_zero k).symm
  simp only [form]
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, hv1, hv2, smul_zero, add_zero, smul_comm]

/- English proof (translation)
Unfold `DLog`. Introduce `K A _ _ _ a f hf w hw ω hω`. Establish `hex : ∀ ω ∈ relOm K (Ideal.span {f}) a, ∃ η ∈ relOm K (Ideal.span {f}) (a + 1), f • η = w ω`. Introduce `ω hω`. Proceed by induction on `hω using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g₀, g, hg, rfl⟩` from `hx`. Break down `hg with hg₀ | ⟨k, hk⟩` into its components or cases. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.mp hg₀`. Use `⟨form K c (Fin.cons f g), form_cons_mem f c g, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw, ← form_mul_left]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp hk`. Use `⟨form K g₀ (Fin.cons f (Function.update g k c)), form_cons_mem f g₀ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, form_cons_eq_smul f c g₀ g k hc]`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨η₁, h₁, e₁⟩` from `hx`. Take `⟨η₂, h₂, e₂⟩` from `hy`. Conclude with `⟨η₁ + η₂, Submodule.add_mem _ h₁ h₂, by rw [smul_add, e₁, e₂, map_add]⟩`. Consider the case `smul c x _ hx`.

Take `⟨η, h₁, e₁⟩` from `hx`. Conclude with `⟨c • η, Submodule.smul_mem _ c h₁, by rw [smul_comm, e₁, map_smul]⟩`. Take `⟨η, hη, e⟩` from `hex ω hω`. Use `⟨η, ⟨hη, e⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `η' ⟨_, e'⟩`.

Establish `hz : f • (η' - η) = 0` using `by rw [smul_sub, e, e', sub_self]`. Conclude with `sub_eq_zero.mp (hf _ hz)`.
-/
theorem dLog : DLog := by
  unfold DLog
  intro K A _ _ _ a f hf w hw ω hω
  have hex : ∀ ω ∈ relOm K (Ideal.span {f}) a,
      ∃ η ∈ relOm K (Ideal.span {f}) (a + 1), f • η = w ω := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, hg, rfl⟩ := hx
      rcases hg with hg₀ | ⟨k, hk⟩
      · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg₀
        refine ⟨form K c (Fin.cons f g), form_cons_mem f c g, ?_⟩
        rw [hw, ← form_mul_left]
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
        refine ⟨form K g₀ (Fin.cons f (Function.update g k c)), form_cons_mem f g₀ _, ?_⟩
        rw [hw, form_cons_eq_smul f c g₀ g k hc]
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨η₁, h₁, e₁⟩ := hx
      obtain ⟨η₂, h₂, e₂⟩ := hy
      exact ⟨η₁ + η₂, Submodule.add_mem _ h₁ h₂, by rw [smul_add, e₁, e₂, map_add]⟩
    | smul c x _ hx =>
      obtain ⟨η, h₁, e₁⟩ := hx
      exact ⟨c • η, Submodule.smul_mem _ c h₁, by rw [smul_comm, e₁, map_smul]⟩
  obtain ⟨η, hη, e⟩ := hex ω hω
  refine ⟨η, ⟨hη, e⟩, ?_⟩
  rintro η' ⟨_, e'⟩
  have hz : f • (η' - η) = 0 := by rw [smul_sub, e, e', sub_self]
  exact sub_eq_zero.mp (hf _ hz)

end GlobalTheory.CompanionTheory.OntoDLog
