import Mathlib

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' → u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k'`. Introduce `u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h`. Establish `e : k = m⁻¹ * u⁻¹ * (u' * m' * k')` using `by rw [← h]; group`. Establish `e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹` using `by rw [e]; group`. Establish `hkk : k * k'⁻¹ ∈ K` using `K.mul_mem hk (K.inv_mem hk')`.

Establish `hmm : m⁻¹ * m' ∈ M` using `M.mul_mem (M.inv_mem hm) hm'`. Establish `e2` using `h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)`. Establish `huu : u = u'`. Establish `: u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹)` using `by group`. Rewrite using `[this, e2]`.

Use `group`. Rewrite `e1` using `[e2, one_mul]`. Establish `e3` using `h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'`. Rewrite `e3` using `[inv_mul_cancel_right, hs, hs']`. Substitute `huu e3` using the available equality.

Conclude with `⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩`. Set `X : Set (G × G × G)` to `(DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))`. Establish `hX : MeasurableSet X` using `(hDN.inter hN).prod ((hDM.inter hM).prod (hK.inter (measurableSet_eq_fun hσ measurable_id)))`. Set `f : G × G × G → G` to `fun p => p.1 * p.2.1 * p.2.2`. Establish `hf : Continuous f` using `by fun_prop`.

Establish `hinj : Set.InjOn f X`. Introduce and unpack `⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h`. Take `⟨a, b, c⟩` from `uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h`. Rewrite using `[a, b, c]`. Use `⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩` and prove the remaining obligations.

Introduce `u hu m hm k hk`. Establish `hl` using `h1 k`. Establish `hl' : k * (σ k)⁻¹ ∈ K ⊓ M`. Use `(K ⊓ M).inv_mem hl` as an intermediate fact. Simplify using `using this`.

Establish `hσK : σ k ∈ K`. Use `K.mul_mem hl.1 hk` as an intermediate fact. Simplify using `using this`. Establish `hσσ : σ (σ k) = σ k`. Use `h2 _ hl k` as an intermediate fact.

Simplify using `using this`. Establish `hm2 : m * (k * (σ k)⁻¹) ∈ M` using `M.mul_mem hm hl'.2`. Establish `e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k` using `by group`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩`.

Take `⟨a, b, _⟩` from `uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)`. Rewrite using `[b, a]`. Conclude with `⟨hdu, hdm⟩`. Introduce and unpack `⟨hdu, hdm⟩`. Conclude with `⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩`.
-/
theorem exists_measurableSet_slice_of_transversal
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G)
    (hN : MeasurableSet (N : Set G)) (hM : MeasurableSet (M : Set G))
    (hK : MeasurableSet (K : Set G)) (hσ : Measurable σ)
    (h1 : ∀ x, σ x * x⁻¹ ∈ K ⊓ M) (h2 : ∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x)
    (h3 : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (h4 : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1)
    (DN DM : Set G) (hDN : MeasurableSet DN) (hDM : MeasurableSet DM) :
    ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K,
      (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  have uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' →
      u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k' := by
    intro u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    have e : k = m⁻¹ * u⁻¹ * (u' * m' * k') := by rw [← h]; group
    have e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹ := by rw [e]; group
    have hkk : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
    have hmm : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
    have e2 := h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)
    have huu : u = u' := by
      have : u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹) := by group
      rw [this, e2]; group
    rw [e2, one_mul] at e1
    have e3 := h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'
    rw [inv_mul_cancel_right, hs, hs'] at e3
    subst huu e3
    exact ⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩
  let X : Set (G × G × G) := (DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))
  have hX : MeasurableSet X :=
    (hDN.inter hN).prod ((hDM.inter hM).prod
      (hK.inter (measurableSet_eq_fun hσ measurable_id)))
  let f : G × G × G → G := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f := by fun_prop
  have hinj : Set.InjOn f X := by
    rintro ⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h
    obtain ⟨a, b, c⟩ := uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    rw [a, b, c]
  refine ⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩
  intro u hu m hm k hk
  have hl := h1 k
  have hl' : k * (σ k)⁻¹ ∈ K ⊓ M := by
    have := (K ⊓ M).inv_mem hl
    simpa using this
  have hσK : σ k ∈ K := by
    have := K.mul_mem hl.1 hk
    simpa using this
  have hσσ : σ (σ k) = σ k := by
    have := h2 _ hl k
    simpa using this
  have hm2 : m * (k * (σ k)⁻¹) ∈ M := M.mul_mem hm hl'.2
  have e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k := by group
  constructor
  · rintro ⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩
    obtain ⟨a, b, _⟩ := uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)
    rw [b, a]
    exact ⟨hdu, hdm⟩
  · rintro ⟨hdu, hdm⟩
    exact ⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩

end GlobalTheory
