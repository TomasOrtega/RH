import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType

open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section SlopeTestRemainingChoices

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem box_apply (ρ : Representation ℂ G W) (τ : Representation ℂ H W') (g : G) (h : H) :
    box ρ τ (g, h) = TensorProduct.map (ρ g) (τ h) := rfl

/- English proof (translation)
Use `haveI := h`. Break down `eq_bot_or_eq_top (⟨S, fun g _ hx => hS g _ hx⟩ : Subrepresentation ρ) with h1 | h1` into its components or cases. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises. Establish `h2 : S = ⊥` using `congrArg Subrepresentation.toSubmodule h1`.

Rewrite `hv` using `[h2]`. Simplify using `using hv`. Conclude with `congrArg Subrepresentation.toSubmodule h1`.
-/
private theorem irr_eq {ρ : Representation ℂ G W} (h : ρ.IsIrreducible) (S : Submodule ℂ W)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) {v : W} (hv : v ∈ S) (h0 : v ≠ 0) : S = ⊤ := by
  haveI := h
  rcases eq_bot_or_eq_top (⟨S, fun g _ hx => hS g _ hx⟩ : Subrepresentation ρ) with h1 | h1
  · exfalso
    apply h0
    have h2 : S = ⊥ := congrArg Subrepresentation.toSubmodule h1
    rw [h2] at hv
    simpa using hv
  · exact congrArg Subrepresentation.toSubmodule h1

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `haveI := h`. Apply `bot_ne_top (α := Subrepresentation ρ)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Use extensionality with `x`. Establish `hx` using `hc x`. Substitute `hx` using the available equality. Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩`.
-/
private theorem exists_ne {ρ : Representation ℂ G W} (h : ρ.IsIrreducible) : ∃ v : W, v ≠ 0 := by
  by_contra hc
  push Not at hc
  haveI := h
  apply bot_ne_top (α := Subrepresentation ρ)
  apply Subrepresentation.toSubmodule_injective
  ext x
  have hx := hc x
  subst hx
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/- English proof (translation)
Use `irr_eq h _ (fun g x hx => ?_) (Submodule.subset_span ⟨1, by simp⟩) hv` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g', rfl⟩` from `hx`. Use `Submodule.subset_span ⟨g * g', ?_⟩` and prove the remaining obligations.

Use `show ρ (g * g') v = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
private theorem span_orbit {ρ : Representation ℂ G W} (h : ρ.IsIrreducible) {v : W} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ := by
  refine irr_eq h _ (fun g x hx => ?_) (Submodule.subset_span ⟨1, by simp⟩) hv
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', ?_⟩
    show ρ (g * g') v = _
    rw [map_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Set `e : W → (MonoidAlgebra ℂ G →ₗ[ℂ] W)` to `fun v => (LinearMap.applyₗ v).comp ρ.asAlgebraHom.toLinearMap`. Establish `he : ∀ v a, e v a = ρ.asAlgebraHom a v` using `fun _ _ => rfl`. Establish `hs : Function.Surjective (e v₁)`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← span_orbit h.1 h1, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨MonoidAlgebra.single g 1, by simp [he]⟩`. Take `⟨s, hsr⟩` from `(e v₁).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)`. Establish `hsr' : ∀ w, e v₁ (s w) = w` using `fun w => LinearMap.congr_fun hsr w`.

Set `φ : W →ₗ[ℂ] W` to `(e v₂).comp s`. Establish `hφ : ∀ a, φ (e v₁ a) = e v₂ a` using `fun a => by`. Establish `h0 : e v₁ (s (e v₁ a) - a) = 0` using `by rw [map_sub, hsr', sub_self]`. Establish `h2` using `hc _ h0`. Rewrite `h2` using `[← he, map_sub, sub_eq_zero]`.

Conclude with `h2`. Establish `key : ∀ g u a, e u (MonoidAlgebra.single g 1 * a) = ρ g (e u a)` using `fun g u a => by`. Simplify using `[he, map_mul]`. Establish `hI : Intw ρ ρ φ` using `fun g v => by`. Take `⟨a, rfl⟩` from `hs v`.

Rewrite using `[← key, hφ, hφ, key]`. Take `⟨c, hc'⟩` from `h.2 φ hI`. Apply `hn c` to reduce the goal to its premises. Establish `h3` using `hφ 1`. Rewrite `h3` using `[hc']`.

Simplify `h3.symm` using `[he]`.
-/
private theorem sep {ρ : Representation ℂ G W} (h : AbsIrr ρ) {v₁ v₂ : W} (h1 : v₁ ≠ 0)
    (hn : ∀ c : ℂ, v₂ ≠ c • v₁) :
    ∃ a : MonoidAlgebra ℂ G, ρ.asAlgebraHom a v₁ = 0 ∧ ρ.asAlgebraHom a v₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  let e : W → (MonoidAlgebra ℂ G →ₗ[ℂ] W) := fun v => (LinearMap.applyₗ v).comp ρ.asAlgebraHom.toLinearMap
  have he : ∀ v a, e v a = ρ.asAlgebraHom a v := fun _ _ => rfl
  have hs : Function.Surjective (e v₁) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_orbit h.1 h1, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by simp [he]⟩
  obtain ⟨s, hsr⟩ := (e v₁).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hsr' : ∀ w, e v₁ (s w) = w := fun w => LinearMap.congr_fun hsr w
  let φ : W →ₗ[ℂ] W := (e v₂).comp s
  have hφ : ∀ a, φ (e v₁ a) = e v₂ a := fun a => by
    have h0 : e v₁ (s (e v₁ a) - a) = 0 := by rw [map_sub, hsr', sub_self]
    have h2 := hc _ h0
    rw [← he, map_sub, sub_eq_zero] at h2
    exact h2
  have key : ∀ g u a, e u (MonoidAlgebra.single g 1 * a) = ρ g (e u a) := fun g u a => by
    simp [he, map_mul]
  have hI : Intw ρ ρ φ := fun g v => by
    obtain ⟨a, rfl⟩ := hs v
    rw [← key, hφ, hφ, key]
  obtain ⟨c, hc'⟩ := h.2 φ hI
  apply hn c
  have h3 := hφ 1
  rw [hc'] at h3
  simpa [he] using h3.symm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem E_tmul {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ W') (v : W) (cf : ι →₀ ℂ) (j : ι) :
    TensorProduct.equivFinsuppOfBasisRight (M := W) b (v ⊗ₜ[ℂ] b.repr.symm cf) j = cf j • v := by
  simp

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v u => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
private theorem E_map {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ W') (T : Module.End ℂ W) (x : W ⊗[ℂ] W') (j : ι) :
    TensorProduct.equivFinsuppOfBasisRight (M := W) b (TensorProduct.map T LinearMap.id x) j =
      T (TensorProduct.equivFinsuppOfBasisRight (M := W) b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v u => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ W'`. Set `E` to `TensorProduct.equivFinsuppOfBasisRight (M := W) b`. Establish `hE : ∀ (T : Module.End ℂ W) x j, E (TensorProduct.map T LinearMap.id x) j = T (E x j)` using `fun T x j => E_map b T x j`. Take `⟨x₀, hx₀, hx₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Set `P : ℕ → Prop` to `fun n => ∃ x ∈ U, x ≠ 0 ∧ (E x).support.card = n`.

Establish `hP : ∃ n, P n` using `⟨_, x₀, hx₀, hx₀0, rfl⟩`. Take `⟨x, hxU, hx0, hxc⟩` from `Nat.find_spec hP`. Establish `hmin : ∀ y ∈ U, y ≠ 0 → (E x).support.card ≤ (E y).support.card` using `fun y hy hy0 => by`. Rewrite using `[hxc]`. Conclude with `Nat.find_min' hP ⟨y, hy, hy0, rfl⟩`.

Establish `hEx : E x ≠ 0` using `fun h0 => hx0 (E.map_eq_zero_iff.1 h0)`. Take `⟨j₀, hj₀⟩` from `Finsupp.support_nonempty_iff.2 hEx`. Establish `hv : E x j₀ ≠ 0` using `Finsupp.mem_support_iff.1 hj₀`. Establish `hline : ∀ j, ∃ c : ℂ, E x j = c • E x j₀`. Introduce `j`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨a, ha1, ha2⟩` from `sep h hv hc`. Establish `hyU` using `hU a x hxU`. Establish `hy0 : TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x ≠ 0` using `fun h0 => ha2 (by`.

Rewrite using `[← hE, h0]`. Use the proof step `simp)`. Establish `hsub : (E (TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x)).support ⊂ (E x).support`. Use `(Finset.ssubset_iff_of_subset ?_).2 ⟨j₀, hj₀, ?_⟩` and prove the remaining obligations. Introduce `i hi`.

Rewrite `hi`, the goal using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[hE, h0, map_zero]`. Rewrite using `[Finsupp.mem_support_iff, not_not, hE]`.

Conclude with `ha1`. Conclude with `absurd (hmin _ hyU hy0) (not_le.2 (Finset.card_lt_card hsub))`. Use `choose c hc using hline`. Set `cf : _ →₀ ℂ` to `Finsupp.onFinset (E x).support c (fun j hj => by`. Rewrite using `[Finsupp.mem_support_iff, hc j]`.

Conclude with `smul_ne_zero hj hv)`. Establish `hx : E x j₀ ⊗ₜ[ℂ] b.repr.symm cf = x`. Apply `E.injective` to reduce the goal to its premises. Use `ext1 j`. Rewrite using `[show E (E x j₀ ⊗ₜ[ℂ] b.repr.symm cf) j = cf j • E x j₀ from E_tmul b _ cf j]`.

Conclude with `(hc j).symm`. Use `⟨E x j₀, b.repr.symm cf, hv, fun h0 => hx0 ?_, by rw [hx]; exact hxU⟩` and prove the remaining obligations. Rewrite using `[← hx, h0, TensorProduct.tmul_zero]`.
-/
private theorem exists_pure {ρ : Representation ℂ G W} (h : AbsIrr ρ) (U : Submodule ℂ (W ⊗[ℂ] W'))
    (hU : ∀ a : MonoidAlgebra ℂ G, ∀ x ∈ U, TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x ∈ U)
    (hne : U ≠ ⊥) : ∃ (v : W) (u : W'), v ≠ 0 ∧ u ≠ 0 ∧ v ⊗ₜ[ℂ] u ∈ U := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W'
  let E := TensorProduct.equivFinsuppOfBasisRight (M := W) b
  have hE : ∀ (T : Module.End ℂ W) x j, E (TensorProduct.map T LinearMap.id x) j = T (E x j) :=
    fun T x j => E_map b T x j
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let P : ℕ → Prop := fun n => ∃ x ∈ U, x ≠ 0 ∧ (E x).support.card = n
  have hP : ∃ n, P n := ⟨_, x₀, hx₀, hx₀0, rfl⟩
  obtain ⟨x, hxU, hx0, hxc⟩ := Nat.find_spec hP
  have hmin : ∀ y ∈ U, y ≠ 0 → (E x).support.card ≤ (E y).support.card := fun y hy hy0 => by
    rw [hxc]
    exact Nat.find_min' hP ⟨y, hy, hy0, rfl⟩
  have hEx : E x ≠ 0 := fun h0 => hx0 (E.map_eq_zero_iff.1 h0)
  obtain ⟨j₀, hj₀⟩ := Finsupp.support_nonempty_iff.2 hEx
  have hv : E x j₀ ≠ 0 := Finsupp.mem_support_iff.1 hj₀
  have hline : ∀ j, ∃ c : ℂ, E x j = c • E x j₀ := by
    intro j
    by_contra hc
    push Not at hc
    obtain ⟨a, ha1, ha2⟩ := sep h hv hc
    have hyU := hU a x hxU
    have hy0 : TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x ≠ 0 := fun h0 => ha2 (by
      rw [← hE, h0]
      simp)
    have hsub : (E (TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x)).support ⊂ (E x).support := by
      refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j₀, hj₀, ?_⟩
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [hE, h0, map_zero]
      · rw [Finsupp.mem_support_iff, not_not, hE]
        exact ha1
    exact absurd (hmin _ hyU hy0) (not_le.2 (Finset.card_lt_card hsub))
  choose c hc using hline
  let cf : _ →₀ ℂ := Finsupp.onFinset (E x).support c (fun j hj => by
    rw [Finsupp.mem_support_iff, hc j]
    exact smul_ne_zero hj hv)
  have hx : E x j₀ ⊗ₜ[ℂ] b.repr.symm cf = x := by
    apply E.injective
    ext1 j
    rw [show E (E x j₀ ⊗ₜ[ℂ] b.repr.symm cf) j = cf j • E x j₀ from E_tmul b _ cf j]
    exact (hc j).symm
  refine ⟨E x j₀, b.repr.symm cf, hv, fun h0 => hx0 ?_, by rw [hx]; exact hxU⟩
  rw [← hx, h0, TensorProduct.tmul_zero]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ W'`. Set `E` to `TensorProduct.equivFinsuppOfBasisRight (M := W) b`. Establish `hE : ∀ (T : Module.End ℂ W) x j, E (TensorProduct.map T LinearMap.id x) j = T (E x j)` using `fun T x j => E_map b T x j`. Establish `hc : ∀ j, ∃ c : ℂ, ∀ w, E (Φ w) j = c • w`. Introduce `j`.

Take `⟨c, hc⟩` from `h.2 ((Finsupp.lapply j).comp (E.toLinearMap.comp Φ)) (fun g v => by show E (Φ (ρ g v)) j = ρ g (E (Φ v) j)`. Rewrite using `[hΦ, hE])`. Conclude with `⟨c, fun w => LinearMap.congr_fun hc w⟩`. Use `choose c hc using hc`. Take `⟨w₀, hw₀⟩` from `exists_ne h.1`.

Set `cf : _ →₀ ℂ` to `Finsupp.onFinset (E (Φ w₀)).support c (fun j hj => by`. Rewrite using `[Finsupp.mem_support_iff, hc j]`. Conclude with `smul_ne_zero hj hw₀)`. Use `⟨b.repr.symm cf, fun w => E.injective ?_⟩` and prove the remaining obligations. Use `ext1 j`.

Rewrite using `[show E (w ⊗ₜ[ℂ] b.repr.symm cf) j = cf j • w from E_tmul b _ cf j]`. Conclude with `hc j w`.
-/
private theorem line_of {ρ : Representation ℂ G W} (h : AbsIrr ρ) (Φ : W →ₗ[ℂ] W ⊗[ℂ] W')
    (hΦ : ∀ g w, Φ (ρ g w) = TensorProduct.map (ρ g) LinearMap.id (Φ w)) :
    ∃ u : W', ∀ w, Φ w = w ⊗ₜ[ℂ] u := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W'
  let E := TensorProduct.equivFinsuppOfBasisRight (M := W) b
  have hE : ∀ (T : Module.End ℂ W) x j, E (TensorProduct.map T LinearMap.id x) j = T (E x j) :=
    fun T x j => E_map b T x j
  have hc : ∀ j, ∃ c : ℂ, ∀ w, E (Φ w) j = c • w := by
    intro j
    obtain ⟨c, hc⟩ := h.2 ((Finsupp.lapply j).comp (E.toLinearMap.comp Φ)) (fun g v => by
      show E (Φ (ρ g v)) j = ρ g (E (Φ v) j)
      rw [hΦ, hE])
    exact ⟨c, fun w => LinearMap.congr_fun hc w⟩
  choose c hc using hc
  obtain ⟨w₀, hw₀⟩ := exists_ne h.1
  let cf : _ →₀ ℂ := Finsupp.onFinset (E (Φ w₀)).support c (fun j hj => by
    rw [Finsupp.mem_support_iff, hc j]
    exact smul_ne_zero hj hw₀)
  refine ⟨b.repr.symm cf, fun w => E.injective ?_⟩
  ext1 j
  rw [show E (w ⊗ₜ[ℂ] b.repr.symm cf) j = cf j • w from E_tmul b _ cf j]
  exact hc j w

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `G H W W' _ _ _ _ _ _ ρ τ hρ hτ`. Take `⟨w₀, hw₀⟩` from `exists_ne hρ.1`. Take `⟨u₀, hu₀⟩` from `exists_ne hτ.1`. Choose the witnesses or unpack the hypotheses as in `⟨φ₀, hφ₀⟩ : ∃ φ₀ : W →ₗ[ℂ] ℂ, φ₀ w₀ = 1 := by`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w₀ ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 hc)`. Conclude with `⟨(φ w₀)⁻¹ • φ, by simp [hφ]⟩`. Set `ct : W ⊗[ℂ] W' →ₗ[ℂ] W'` to `(TensorProduct.lid ℂ W').toLinearMap.comp (TensorProduct.map φ₀ LinearMap.id)`.

Establish `hct : ∀ v u, ct (v ⊗ₜ[ℂ] u) = φ₀ v • u` using `fun v u => by simp [ct]`. Establish `hct₀ : ∀ u, ct (w₀ ⊗ₜ[ℂ] u) = u` using `fun u => by rw [hct, hφ₀, one_smul]`. Establish `hne : w₀ ⊗ₜ[ℂ] u₀ ≠ 0` using `fun h0 => hu₀ (by rw [← hct₀ u₀, h0, map_zero])`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI : Nontrivial (Subrepresentation (box ρ τ)) := ⟨⊥, ⊤, fun h => hne (by`.

Establish `h1 : (⊥ : Submodule ℂ (W ⊗[ℂ] W')) = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Establish `h2 : w₀ ⊗ₜ[ℂ] u₀ ∈ (⊥ : Submodule ℂ (W ⊗[ℂ] W'))`. Rewrite using `[h1]`. Conclude with `Submodule.mem_top`. Conclude with `(Submodule.mem_bot ℂ).1 h2)⟩`.

Use `{ eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Distinguish the cases in `hS : S.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hS)`. Use `Or.inr (Subrepresentation.toSubmodule_injective ?_)` and prove the remaining obligations. Establish `hU : ∀ a : MonoidAlgebra ℂ G, ∀ x ∈ S.toSubmodule, TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x ∈ S.toSubmodule`.

Introduce `a`. Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero`. Introduce `x _`. Simplify using the standard rewrite rules.

Consider the case `add p q hp hq`. Introduce `x hx`. Rewrite using `[map_add, TensorProduct.map_add_left]`. Conclude with `add_mem (hp x hx) (hq x hx)`. Consider the case `single g c`.

Introduce `x hx`. Establish `h1` using `S.apply_mem_toSubmodule (g, 1) hx`. Rewrite `h1` using `[box_apply, map_one]`. Rewrite using `[Representation.asAlgebraHom_single, TensorProduct.map_smul_left]`. Conclude with `S.toSubmodule.smul_mem c h1`.

Take `⟨v, u, hv, hu, hm⟩` from `exists_pure hρ S.toSubmodule hU hS`. Establish `h1 : ∀ w, w ⊗ₜ[ℂ] u ∈ S.toSubmodule` using `fun w => by`. Establish `h2 : (⊤ : Submodule ℂ W) ≤ S.toSubmodule.comap ((TensorProduct.mk ℂ W W').flip u)`. Rewrite using `[← span_orbit hρ.1 hv, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Establish `h3` using `S.apply_mem_toSubmodule (g, 1) hm`. Simplify `h3` using `[box_apply]`. Conclude with `h2 Submodule.mem_top`. Establish `h4 : ∀ w u', w ⊗ₜ[ℂ] u' ∈ S.toSubmodule` using `fun w u' => by`. Establish `h2 : (⊤ : Submodule ℂ W') ≤ S.toSubmodule.comap (TensorProduct.mk ℂ W W' w)`.

Rewrite using `[← span_orbit hτ.1 hu, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Establish `h3` using `S.apply_mem_toSubmodule (1, g) (h1 w)`. Simplify `h3` using `[box_apply]`. Conclude with `h2 Submodule.mem_top`.

Use `eq_top_iff.2 ?_` and prove the remaining obligations. Rewrite using `[← TensorProduct.span_tmul_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨w, u', rfl⟩`. Conclude with `h4 w u'`. Introduce `f hf`.

Establish `hf₁ : ∀ u, ∃ u' : W', ∀ w, f (w ⊗ₜ[ℂ] u) = w ⊗ₜ[ℂ] u'` using `fun u => by`. Use `line_of hρ (f.comp ((TensorProduct.mk ℂ W W').flip u)) fun g w => ?_` and prove the remaining obligations. Establish `h1` using `hf (g, 1) (w ⊗ₜ[ℂ] u)`. Simplify using `only [box_apply, map_one, TensorProduct.map_tmul, Module.End.one_apply] at h1`. Conclude with `h1`.

Use `choose k hk using hf₁`. Set `γ : W' →ₗ[ℂ] W'` to `ct.comp (f.comp (TensorProduct.mk ℂ W W' w₀))`. Establish `hγ : ∀ u, γ u = k u` using `fun u => by show ct (f (w₀ ⊗ₜ[ℂ] u)) = k u`. Rewrite using `[hk, hct₀]`. Establish `hI : Intw τ τ γ` using `fun h u => by`.

Establish `h1` using `hf (1, h) (w₀ ⊗ₜ[ℂ] u)`. Simplify using `only [box_apply, map_one, TensorProduct.map_tmul, Module.End.one_apply, hk] at h1`. Rewrite using `[hγ, hγ]`. Establish `h2` using `congrArg ct h1`. Simplify `h2` using `[hct₀]`.

Take `⟨a, ha⟩` from `hτ.2 γ hI`. Use `⟨a, TensorProduct.ext' fun w u => ?_⟩` and prove the remaining obligations. Rewrite using `[hk, ← hγ, ha]`. Simplify using `[TensorProduct.tmul_smul]`.
-/
theorem boxIrr : BoxIrr := by
  intro G H W W' _ _ _ _ _ _ ρ τ hρ hτ
  obtain ⟨w₀, hw₀⟩ := exists_ne hρ.1
  obtain ⟨u₀, hu₀⟩ := exists_ne hτ.1
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : W →ₗ[ℂ] ℂ, φ₀ w₀ = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 hc)
    exact ⟨(φ w₀)⁻¹ • φ, by simp [hφ]⟩
  let ct : W ⊗[ℂ] W' →ₗ[ℂ] W' := (TensorProduct.lid ℂ W').toLinearMap.comp (TensorProduct.map φ₀ LinearMap.id)
  have hct : ∀ v u, ct (v ⊗ₜ[ℂ] u) = φ₀ v • u := fun v u => by simp [ct]
  have hct₀ : ∀ u, ct (w₀ ⊗ₜ[ℂ] u) = u := fun u => by rw [hct, hφ₀, one_smul]
  have hne : w₀ ⊗ₜ[ℂ] u₀ ≠ 0 := fun h0 => hu₀ (by rw [← hct₀ u₀, h0, map_zero])
  refine ⟨?_, ?_⟩
  · haveI : Nontrivial (Subrepresentation (box ρ τ)) := ⟨⊥, ⊤, fun h => hne (by
      have h1 : (⊥ : Submodule ℂ (W ⊗[ℂ] W')) = ⊤ := congrArg Subrepresentation.toSubmodule h
      have h2 : w₀ ⊗ₜ[ℂ] u₀ ∈ (⊥ : Submodule ℂ (W ⊗[ℂ] W')) := by
        rw [h1]
        exact Submodule.mem_top
      exact (Submodule.mem_bot ℂ).1 h2)⟩
    refine { eq_bot_or_eq_top := fun S => ?_ }
    by_cases hS : S.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
    refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have hU : ∀ a : MonoidAlgebra ℂ G, ∀ x ∈ S.toSubmodule,
        TensorProduct.map (ρ.asAlgebraHom a) LinearMap.id x ∈ S.toSubmodule := by
      intro a
      induction a using MonoidAlgebra.induction_linear with
      | zero =>
        intro x _
        simp
      | add p q hp hq =>
        intro x hx
        rw [map_add, TensorProduct.map_add_left]
        exact add_mem (hp x hx) (hq x hx)
      | single g c =>
        intro x hx
        have h1 := S.apply_mem_toSubmodule (g, 1) hx
        rw [box_apply, map_one] at h1
        rw [Representation.asAlgebraHom_single, TensorProduct.map_smul_left]
        exact S.toSubmodule.smul_mem c h1
    obtain ⟨v, u, hv, hu, hm⟩ := exists_pure hρ S.toSubmodule hU hS
    have h1 : ∀ w, w ⊗ₜ[ℂ] u ∈ S.toSubmodule := fun w => by
      have h2 : (⊤ : Submodule ℂ W) ≤ S.toSubmodule.comap ((TensorProduct.mk ℂ W W').flip u) := by
        rw [← span_orbit hρ.1 hv, Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        have h3 := S.apply_mem_toSubmodule (g, 1) hm
        simpa [box_apply] using h3
      exact h2 Submodule.mem_top
    have h4 : ∀ w u', w ⊗ₜ[ℂ] u' ∈ S.toSubmodule := fun w u' => by
      have h2 : (⊤ : Submodule ℂ W') ≤ S.toSubmodule.comap (TensorProduct.mk ℂ W W' w) := by
        rw [← span_orbit hτ.1 hu, Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        have h3 := S.apply_mem_toSubmodule (1, g) (h1 w)
        simpa [box_apply] using h3
      exact h2 Submodule.mem_top
    refine eq_top_iff.2 ?_
    rw [← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨w, u', rfl⟩
    exact h4 w u'
  · intro f hf
    have hf₁ : ∀ u, ∃ u' : W', ∀ w, f (w ⊗ₜ[ℂ] u) = w ⊗ₜ[ℂ] u' := fun u => by
      refine line_of hρ (f.comp ((TensorProduct.mk ℂ W W').flip u)) fun g w => ?_
      have h1 := hf (g, 1) (w ⊗ₜ[ℂ] u)
      simp only [box_apply, map_one, TensorProduct.map_tmul, Module.End.one_apply] at h1
      exact h1
    choose k hk using hf₁
    let γ : W' →ₗ[ℂ] W' := ct.comp (f.comp (TensorProduct.mk ℂ W W' w₀))
    have hγ : ∀ u, γ u = k u := fun u => by
      show ct (f (w₀ ⊗ₜ[ℂ] u)) = k u
      rw [hk, hct₀]
    have hI : Intw τ τ γ := fun h u => by
      have h1 := hf (1, h) (w₀ ⊗ₜ[ℂ] u)
      simp only [box_apply, map_one, TensorProduct.map_tmul, Module.End.one_apply, hk] at h1
      rw [hγ, hγ]
      have h2 := congrArg ct h1
      simpa [hct₀] using h2
    obtain ⟨a, ha⟩ := hτ.2 γ hI
    refine ⟨a, TensorProduct.ext' fun w u => ?_⟩
    rw [hk, ← hγ, ha]
    simp [TensorProduct.tmul_smul]

end UpperTheory.V.Z.J.D
