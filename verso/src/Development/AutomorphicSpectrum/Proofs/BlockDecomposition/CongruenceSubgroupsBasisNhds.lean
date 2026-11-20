import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

/- English proof (translation)
Establish `hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B` using `continuous_const.add continuous_id`. Establish `hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k)`. Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using ht`. Establish `e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a)` using `nhds_pi`.

Establish `hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈ Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a)`. Rewrite using `[← e]`. Conclude with `hs`. Take `⟨I, -, t₁, ht₁, hsub⟩` from `Filter.mem_pi.1 hs'`. Establish `h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a`.

Introduce `a`. Establish `e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b)` using `nhds_pi`. Establish `h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b)`. Rewrite using `[← e']`. Conclude with `ht₁ a`.

Take `⟨J, -, t₂, ht₂, hJ⟩` from `Filter.mem_pi.1 h`. Conclude with `⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩`. Use `choose t₂ ht₂ hsub₂ using h2`. Use `⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b, fun A hA => ?_⟩` and prove the remaining obligations. Establish `hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t` using `hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b`.

Simplify using `using hmem`.
-/
theorem exists_entry_nhds {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (m : ℕ)
    {t : Set (Matrix (Fin m) (Fin m) k)} (ht : t ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) k)) :
    ∃ U ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin m) (Fin m) k,
      (∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ U) → A ∈ t := by
  have hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B := continuous_const.add continuous_id
  have hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using ht
  have e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := nhds_pi
  have hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈
      Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := by
    rw [← e]
    exact hs
  obtain ⟨I, -, t₁, ht₁, hsub⟩ := Filter.mem_pi.1 hs'
  have h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a := by
    intro a
    have e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := nhds_pi
    have h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := by
      rw [← e']
      exact ht₁ a
    obtain ⟨J, -, t₂, ht₂, hJ⟩ := Filter.mem_pi.1 h
    exact ⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩
  choose t₂ ht₂ hsub₂ using h2
  refine ⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b,
    fun A hA => ?_⟩
  have hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t :=
    hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b
  simpa using hmem

/- English proof (translation)
Take `⟨u, hu, huO⟩` from `(mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO`. Establish `hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k)` using `by simpa using hu`. Rewrite `hu1` using `[Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨w, hw, hwu⟩` from `hu1`. Rewrite `hw` using `[Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff]`.

Take `⟨t₁, ht₁, t₂, ht₂, hsub⟩` from `hw`. Establish `ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `by simpa using ht₁`. Establish `ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k)`. Establish `h` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂`. Simplify using `using h`.

Take `⟨U₁, hU₁, h₁⟩` from `GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'`. Take `⟨U₂, hU₂, h₂⟩` from `GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'`. Take `⟨s₀, hs₀⟩` from `GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)`. Use `⟨s₀, fun s hs hss₀ g hg => ?_⟩` and prove the remaining obligations. Establish `hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀`.

Introduce `x hx`. Simplify using `only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢`. Conclude with `le_trans hx hss₀`. Use `huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))` and prove the remaining obligations. Establish `hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `hg.1 show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁`.

Conclude with `h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1`. Establish `hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `hg.2 show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂`. Conclude with `h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2`.
-/
theorem congM_subset_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
      ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
        (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ :=
    (mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO
  have hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k) := by simpa using hu
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hu1
  obtain ⟨w, hw, hwu⟩ := hu1
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at hw
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hw
  have ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by simpa using ht₁
  have ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have h := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂
    simpa using h
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)
  refine ⟨s₀, fun s hs hss₀ g hg => ?_⟩
  have hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀ := by
    intro x hx
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx hss₀
  refine huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.1
    show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁
    exact h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s
        (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.2
    show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂
    exact h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
