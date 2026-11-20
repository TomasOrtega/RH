import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

/- English proof (translation)
Use `set q := h.symm.proj with hq`. Establish `hr : ∀ a, a - (q a : D.La) ∈ perp D Z'` using `fun a => h.symm.sub_proj_mem a`. Establish `hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z'` using `fun z => by`. Take `⟨e, he, hz⟩` from `ht z`. Rewrite using `[hz, add_sub_cancel_left]`.

Conclude with `nsmul_mem he N`. Use `choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a)) fun z z' => by simp only [map_add, map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)`. Simplify using `only [AddMonoidHom.mk'_apply] at hc hu`. Set `α : D.La →ₗ[𝓞 E] Z'` to `{ toFun := c map_add' := fun a a' => (hu _ _ fun z => by`. Simplify using `only [Submodule.coe_add, map_add, hc, map_sub, LinearMap.sub_apply, map_add]`.

Use the proof step `abel).symm`. Use the proof step `map_smul' := fun x a => (hu _ _ fun z => by`. Establish `key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w` using `fun u w => by rw [D.adj, bar_bar]`. Simplify using `only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]`. Rewrite using `[key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }`.

Establish `hα : ∀ a, α a = c a` using `fun _ => rfl`. Set `g : D.La →ₗ[𝓞 E] D.La` to `LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α`. Establish `hg : ∀ a, g a = a + (t (q a) - q a) - c a` using `fun _ => rfl`. Use `⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `hZ : ∀ (x y : Z), D.EF x y = 0` using `fun x y => h.1 x.2 _ y.2`.

Establish `hZ' : ∀ (x y : Z'), D.EF x y = 0` using `fun x y => h.2.1 x.2 _ y.2`. Establish `f1` using `hZ' (c a) (c a')`. Establish `f2 : D.EF (t (q a) - q a) (c a') = 0` using `hδ (q a) _ (c a').2`. Establish `f3 : D.EF (c a) (t (q a') - q a') = 0`. Rewrite using `[ef_swap, hδ (q a') _ (c a).2, neg_zero]`.

Establish `f4` using `hiso (q a) (q a')`. Establish `f5` using `hZ (q a) (q a')`. Establish `f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a')`. Use `hr a _ (c a').2` as an intermediate fact. Rewrite using `[← hc a' (q a)]`.

Simplify using `only [map_sub, LinearMap.sub_apply] at this`. Take the linear combination `this`. Establish `f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a')`. Use `hr a' _ (c a).2` as an intermediate fact. Establish `h2` using `hc a (q a')`.

Rewrite using `[ef_swap D (c a) a', ef_swap D (a - q a)]`. Simplify using `only [map_sub, LinearMap.sub_apply] at this h2 ⊢`. Take the linear combination `-this - h2`. Rewrite using `[hg, hg]`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢`.

Take the linear combination `f1 - f2 - f3 + f4 - f5 - f7 - f8`. Take `⟨e, -, he⟩` from `ht (q a)`. Take `⟨e', he'⟩` from `GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by`. Take `⟨e₁, -, he₁⟩` from `ht (q b)`. Establish `h1 : D.EF (c a) (b - q b) = 0` using `by rw [ef_swap, hr b _ (c a).2, neg_zero]`.

Establish `h2` using `hc a (q b)`. Rewrite `h2` using `[he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply]`. Use `⟨-D.EF e₁ (a - q a), ?_⟩` and prove the remaining obligations. Establish `h3 : D.EF (c a) b = D.EF (c a) (q b)`. Rewrite `h1` using `[map_sub]`.

Take the linear combination `h1`. Rewrite using `[h3, ef_swap, h2, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨e - e', ?_⟩` and prove the remaining obligations. Rewrite using `[hg, he, he', smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `hqz : q z = z` using `Subtype.ext (h.symm.proj_of_mem z.2)`. Establish `hcz : c z = 0` using `(hu z 0 fun z' => by simp [hqz]).symm`. Rewrite using `[hg, hqz, hcz]`. Simplify using the standard rewrite rules.
-/
theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add, map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add, hc, map_sub, LinearMap.sub_apply, map_add]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
