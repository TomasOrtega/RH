import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd
open MeasureTheory

namespace GlobalTheory.Cusp.Shear

/- English proof (translation)
Introduce `G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ A B hAm hBm hA hB ν`. Use `set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he`. Establish `himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B)`. Use extensionality with `n`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Simplify using `using hz`. Introduce `h; exact ⟨e.symm n, h, by simp⟩`. Establish `efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹` using `fun n => rfl`. Establish `esnd : ∀ n : N, (e.symm n).2 = π n` using `fun n => rfl`.

Use `IsFundamentalDomain.mk' ?_ ?_` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `(e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet`. Introduce `x`. Establish `hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B`.

Introduce `n`. Rewrite using `[himg]`. Both sides reduce to the same expression. Establish `hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) = (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹)`. Introduce `g`.

Rewrite using `[efst, hπmul, hsadd]`. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Establish `hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x` using `fun g => by rw [esnd, hπmul]`. Set `c : V → N'` to `fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹, hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩`.

Take `⟨w, hwB, hwu⟩` from `hB (π x)`. Take `⟨δ, hδA, hδu⟩` from `hA (c w)`. Establish `hδΓ : ((δ : N') : G) ∈ Γ` using `Subgroup.mem_subgroupOf.1 δ.2`. Set `γ0 : Γ.subgroupOf N` to `⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩`. Establish `hπγ0 : π (γ0 : N) = w`.

Establish `h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩` using `rfl`. Rewrite using `[h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]`. Use `⟨γ0, ?_, ?_⟩` and prove the remaining obligations. Use `show (γ0 : N) * x ∈ _`. Rewrite using `[hmemS, hsnd, hπγ0]`.

Use `⟨?_, hwB⟩` and prove the remaining obligations. Establish `h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hfst, hπγ0]`. Use `show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)`.

Use `group`. Rewrite using `[h]`. Conclude with `hδA`. Introduce `γ hγ`. Establish `hγ' : (γ : N) * x ∈ e '' (A ×ˢ B)` using `hγ`.

Rewrite `hγ'` using `[hmemS, hsnd]`. Take `⟨hγA, hγB⟩` from `hγ'`. Establish `hγΓ : ((γ : N) : G) ∈ Γ` using `Subgroup.mem_subgroupOf.1 γ.2`. Establish `hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w` using `hwu _ hγB`. Establish `hwv : π (γ : N) = w` using `congrArg Subtype.val hw`.

Establish `hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N'` using `hwv ▸ mul_inv_mem hs hπmul hπs hker γ`. Set `δγ : Γ.subgroupOf N'` to `⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩`. Establish `h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hfst, hwv]`.

Both sides reduce to the same expression. Establish `hδe : δγ = δ` using `hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)`. Establish `hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G)`. Rewrite using `[← hδe]`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((γ : N) : G) = ((δ : N') : G) * s w`. Rewrite using `[← hv]`. Use `group`.
-/
theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
