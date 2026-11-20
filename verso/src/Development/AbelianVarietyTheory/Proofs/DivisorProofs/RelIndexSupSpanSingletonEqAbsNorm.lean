import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

/- English proof (translation)
Use `set M := N₀ ⊔ Submodule.span (𝓞 F) {u} with hM`. Use `set K : Submodule (𝓞 F) M := N₀.comap M.subtype with hK`. Establish `huM : u ∈ M` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)`. Set `g : 𝓞 F →ₗ[𝓞 F] M` to `LinearMap.toSpanSingleton (𝓞 F) M ⟨u, huM⟩`. Set `f : 𝓞 F →ₗ[𝓞 F] M ⧸ K` to `K.mkQ ∘ₗ g`.

Establish `hf : Function.Surjective f`. Introduce `y`. Take `⟨⟨x, hx⟩, rfl⟩` from `K.mkQ_surjective y`. Take `⟨n, hn, w, hw, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hw`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Use `show K.mkQ (g a) = K.mkQ ⟨n + a • u, hx⟩`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `show (g a - ⟨n + a • u, hx⟩ : M).1 ∈ N₀`. Simplify using `[g, LinearMap.toSpanSingleton_apply]`.

Conclude with `hn`. Establish `hker : LinearMap.ker f = p`. Establish `hmem : ∀ a, a ∈ LinearMap.ker f ↔ a • u ∈ N₀`. Introduce `a`. Simplify using `only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap, Submodule.subtype_apply, g, LinearMap.toSpanSingleton_apply, SetLike.val_smul]`.

Use `symm`. Apply `hp.eq_of_le` to reduce the goal to its premises. Introduce `htop`. Apply `hu` to reduce the goal to its premises. Establish `: (1 : 𝓞 F) ∈ LinearMap.ker f`.

Express the relevant statement in the definitionally equal form `(1 : 𝓞 F) ∈ (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F))`. Rewrite using `[show (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F)) = ⊤ from htop]`. Discharge the goal by the elementary cases of `trivial`. Simplify using `using (hmem 1).mp this`. Introduce `a ha`.

Conclude with `(hmem a).mpr (hpu a ha)`. Establish `e : (𝓞 F ⧸ p) ≃ₗ[𝓞 F] M ⧸ K`. Use `f.quotKerEquivOfSurjective hf` as an intermediate fact. Rewrite `this` using `[hker]`. Conclude with `this`.

Establish `hidx : N₀.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ K)`. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.index_eq_card]`. Both sides reduce to the same expression. Rewrite using `[hidx, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr e.toEquiv).symm`.
-/
theorem relIndex_sup_span_singleton_eq_absNorm
    (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F))
    (hp : p.IsMaximal) (hu : u ∉ N₀) (hpu : ∀ π ∈ p, π • u ∈ N₀) :
    N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup
      = Ideal.absNorm p := by
  set M := N₀ ⊔ Submodule.span (𝓞 F) {u} with hM
  set K : Submodule (𝓞 F) M := N₀.comap M.subtype with hK
  have huM : u ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)

  let g : 𝓞 F →ₗ[𝓞 F] M := LinearMap.toSpanSingleton (𝓞 F) M ⟨u, huM⟩
  let f : 𝓞 F →ₗ[𝓞 F] M ⧸ K := K.mkQ ∘ₗ g
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨a, ?_⟩
    show K.mkQ (g a) = K.mkQ ⟨n + a • u, hx⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show (g a - ⟨n + a • u, hx⟩ : M).1 ∈ N₀
    simp [g, LinearMap.toSpanSingleton_apply]
    exact hn
  have hker : LinearMap.ker f = p := by
    have hmem : ∀ a, a ∈ LinearMap.ker f ↔ a • u ∈ N₀ := by
      intro a
      simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap, Submodule.subtype_apply, g,
        LinearMap.toSpanSingleton_apply, SetLike.val_smul]
    symm
    apply hp.eq_of_le
    · intro htop
      apply hu
      have : (1 : 𝓞 F) ∈ LinearMap.ker f := by
        change (1 : 𝓞 F) ∈ (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F))
        rw [show (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F)) = ⊤ from htop]
        trivial
      simpa using (hmem 1).mp this
    · intro a ha
      exact (hmem a).mpr (hpu a ha)
  have e : (𝓞 F ⧸ p) ≃ₗ[𝓞 F] M ⧸ K := by
    have := f.quotKerEquivOfSurjective hf
    rw [hker] at this
    exact this
  have hidx : N₀.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ K) := by
    rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  rw [hidx, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

end GlobalTheory
