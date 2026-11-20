import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CompP

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem supp_congr {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) {f g : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (hg : g ∈ supportedIn (Set.univ : Set (Sp k n))) (e : ∀ p ∈ Bz Z ×ˢ Set.univ, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

/- English proof (translation)
Introduce `n Z hZ`. Take `⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩` from `hΦ n Z hZ`. Take `⟨hCs, hCa, -, -⟩` from `hC n Z hZ`. Establish `hUU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), f ∈ supportedIn (Set.univ : Set (Sp k n))` using `fun f hf => ⟨hf.1, Set.subset_univ _⟩`. Set `F : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] (Sp k n → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun ξ => ξ ∘ₗ Φ map_add' := fun a b => by ext; simp map_smul' := fun a b => by ext; simp }`.

Establish `hF : ∀ ξ f, F ξ f = ξ (Φ f)` using `fun _ _ => rfl`. Use `⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ξ hξ f hf hz`. Rewrite using `[hF]`. Use `hξ _ (h1 f hf) fun p hp => ?_` and prove the remaining obligations.

Establish `hpF : p ∈ Fib Z (qZ Z p.1)` using `⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩`. Conclude with `h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p hpF`. Introduce `ξ y hξ f hf hz`. Rewrite using `[hF]`. Conclude with `hξ _ (h1 f hf) (h3 f hf y hz)`.

Introduce `ξ hξ hinv g hg f hf`. Rewrite using `[hF, hF]`. Establish `hfg : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n))` using `hCa g f hf`. Rewrite using `[supp_congr hξ (h1 _ hfg) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]`. Conclude with `hinv g hg _ (h1 f hf)`.

Introduce `ξ hξ`. Prove the components needed by the constructor for the conclusion. Introduce `hk f hf`. Rewrite using `[hF]`. Conclude with `hk _ (h5 f hf)`.

Introduce `hk f hf`. Establish `hfu` using `hUU f hf`. Rewrite using `[← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]`. Conclude with `hk _ (h6 f hf)`. Introduce `ξ hξ f hf`.

Rewrite using `[hF]`. Conclude with `hξ _ (h1 f hf)`. Introduce `t ξ hξ f hf`. Rewrite using `[hF]`. Use `show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))`.

Establish `hsf : (fun q => f (sig Z t⁻¹ q)) ∈ supportedIn (Set.univ : Set (Sp k n))` using `hCs t⁻¹ f hf`. Rewrite using `[← smul_eq_mul, ← map_smul]`. Conclude with `supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ hsf)) (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)`.
-/
theorem fourP_of (hΦ : PhiP (k := k)) (hC : CompP (k := k)) : FourP (k := k) := by
  intro n Z hZ
  obtain ⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ n Z hZ
  obtain ⟨hCs, hCa, -, -⟩ := hC n Z hZ
  have hUU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => ⟨hf.1, Set.subset_univ _⟩
  let F : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] (Sp k n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun a b => by ext; simp
      map_smul' := fun a b => by ext; simp }
  have hF : ∀ ξ f, F ξ f = ξ (Φ f) := fun _ _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf hz
    rw [hF]
    refine hξ _ (h1 f hf) fun p hp => ?_
    have hpF : p ∈ Fib Z (qZ Z p.1) := ⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩
    exact h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p hpF
  · intro ξ y hξ f hf hz
    rw [hF]
    exact hξ _ (h1 f hf) (h3 f hf y hz)
  · intro ξ hξ hinv g hg f hf
    rw [hF, hF]
    have hfg : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCa g f hf
    rw [supp_congr hξ (h1 _ hfg) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]
    exact hinv g hg _ (h1 f hf)
  · intro ξ hξ
    constructor
    · intro hk f hf
      rw [hF]
      exact hk _ (h5 f hf)
    · intro hk f hf
      have hfu := hUU f hf
      rw [← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]
      exact hk _ (h6 f hf)
  · intro ξ hξ f hf
    rw [hF]
    exact hξ _ (h1 f hf)
  · intro t ξ hξ f hf
    rw [hF]
    show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))
    have hsf : (fun q => f (sig Z t⁻¹ q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCs t⁻¹ f hf
    rw [← smul_eq_mul, ← map_smul]
    exact supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ hsf))
      (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)

end PositivityTheory.RgUd.T.Nil.Four
