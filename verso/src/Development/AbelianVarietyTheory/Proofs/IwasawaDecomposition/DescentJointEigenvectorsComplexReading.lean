import Mathlib

namespace GlobalTheory

open Module

/- English proof (translation)
Introduce `K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv`. Use `set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM`. Establish `mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ`. Introduce `S hS`. Conclude with `iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl`.

Establish `key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K, (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ`. Introduce `S S'' hS k hk c hc v hv`. Establish `hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v)`. Simplify using `[map_sub, hT k hk, LinearMap.map_smulₛₗ]`. Rewrite using `[hrw]`.

It suffices to establish `h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv`. Use `iSup₂_le fun σ hσ w hw => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hPart σ (hS hσ) k hk w hw, ← sub_smul]`. Distinguish the cases in `h : σ ∈ S''`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))`.

Rewrite using `[hc σ hσ h, sub_self, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `S hS hSs v hv`. Establish `hS0 : S = ∅` using `Finset.card_eq_zero.mp (by omega)`. Substitute `hS0` using the available equality. Simplify using `only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv`.

Establish `hvG : v ∈ G` using `hG v (by rw [hv]; exact Submodule.zero_mem _)`. Rewrite using `[hinj v hvG hv]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ n ih`. Introduce `S hS hSs v hv`.

Break down `S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩` into its components or cases. Conclude with `ih S (by simp [hS0]) hSs v hv`. Distinguish the cases in `hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k`. Establish `hvG : v ∈ G` using `hG v (mono S hSs hv)`. Establish `heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k)`.

Use `Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_` and prove the remaining obligations. Establish `h0` using `key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv`. Simplify using `only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0`. Establish `hmG : T k v - lam a k • v ∈ G` using `hG _ (by rw [h0]; exact Submodule.zero_mem _)`. Use `hinj _ hmG h0` as an intermediate fact.

Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `sub_eq_zero.mp this`. Conclude with `Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))`. Use `push_neg at hall`. Take `⟨b, hb, k, hk, hne⟩` from `hall`.

Establish `hcb` using `Finset.card_erase_of_mem hb`. Establish `hca` using `Finset.card_erase_of_mem ha`. Establish `hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s` using `fun x y hy => hSs (Finset.mem_of_mem_erase hy)`. Establish `h1` using `ih (S.erase b) (by omega) (hsub b) _ (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by`. Assume the negation of the conclusion as `hc`.

Conclude with `hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)`. Establish `h2` using `ih (S.erase a) (by omega) (hsub a) _ (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by`. Assume the negation of the conclusion as `hc`. Conclude with `hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)`. Establish `hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v))`.

Rewrite using `[sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]`. Rewrite using `[hv']`. Conclude with `M.smul_mem _ (M.sub_mem h1 h2)`. Establish `hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ` using `hv`. Take `⟨S, hS⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hv2`.

Establish `hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ` using `iSup₂_le fun σ hσ => iSup_le fun hs => le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl`. Conclude with `main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)`.
-/
theorem descent_joint_eigen : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  classical
  intro K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv
  set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM
  have mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ := by
    intro S hS
    exact iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl
  have key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K,
      (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ →
      e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ := by
    intro S S'' hS k hk c hc v hv
    have hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v) := by
      simp [map_sub, hT k hk, LinearMap.map_smulₛₗ]
    rw [hrw]
    suffices h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv
    refine iSup₂_le fun σ hσ w hw => ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hPart σ (hS hσ) k hk w hw, ← sub_smul]
    by_cases h : σ ∈ S''
    · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))
    · rw [hc σ hσ h, sub_self, zero_smul]; exact Submodule.zero_mem _
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M := by
    intro n
    induction n with
    | zero =>
      intro S hS hSs v hv
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv
      have hvG : v ∈ G := hG v (by rw [hv]; exact Submodule.zero_mem _)
      rw [hinj v hvG hv]; exact Submodule.zero_mem _
    | succ n ih =>
      intro S hS hSs v hv
      rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
      · exact ih S (by simp [hS0]) hSs v hv
      by_cases hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k
      · have hvG : v ∈ G := hG v (mono S hSs hv)
        have heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k) := by
          refine Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_
          have h0 := key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv
          simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0
          have hmG : T k v - lam a k • v ∈ G := hG _ (by rw [h0]; exact Submodule.zero_mem _)
          have := hinj _ hmG h0
          rw [Module.End.mem_eigenspace_iff]
          exact sub_eq_zero.mp this
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))
      · push_neg at hall
        obtain ⟨b, hb, k, hk, hne⟩ := hall
        have hcb := Finset.card_erase_of_mem hb
        have hca := Finset.card_erase_of_mem ha
        have hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s := fun x y hy => hSs (Finset.mem_of_mem_erase hy)
        have h1 := ih (S.erase b) (by omega) (hsub b) _
          (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have h2 := ih (S.erase a) (by omega) (hsub a) _
          (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v)) := by
          rw [sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]
        rw [hv']; exact M.smul_mem _ (M.sub_mem h1 h2)

  have hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ := hv
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv2
  have hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ :=
    iSup₂_le fun σ hσ => iSup_le fun hs =>
      le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl
  exact main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)

end GlobalTheory
