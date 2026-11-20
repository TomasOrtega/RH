import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLocFEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `(mem_locF_lemma 𝔭 _ x).mp hx`. Use `Submodule.mem_inf.mpr ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Formalism.L2.SG.Pf.G7.locF_subspace X hp]`.

Conclude with `(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.2⟩`. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`. Take `⟨s, hs, hsx⟩` from `(mem_locF_lemma 𝔭 _ x).mp hx1`. Conclude with `(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_inf.mpr ⟨hsx, (X.restrictScalars (𝓞 K)).smul_mem s hx2⟩⟩`.
-/
private lemma locF_inf_restrictScalars (X : Submodule K V) (Λ : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) :
    locF 𝔭 (Λ ⊓ X.restrictScalars (𝓞 K)) = locF 𝔭 Λ ⊓ X.restrictScalars (𝓞 K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine Submodule.mem_inf.mpr ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.1⟩, ?_⟩
    rw [← Formalism.L2.SG.Pf.G7.locF_subspace X hp]
    exact (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.2⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    exact (mem_locF_lemma 𝔭 _ x).mpr
      ⟨s, hs, Submodule.mem_inf.mpr ⟨hsx, (X.restrictScalars (𝓞 K)).smul_mem s hx2⟩⟩

/- English proof (translation)
Establish `hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ` using `hu`. Simplify using `only [fibS, Set.mem_setOf_eq]`. Use `⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']`. Rewrite using `[← hM, locF_inf_restrictScalars U Λ h𝔭.isPrime]`.

Rewrite using `[← hT, locF_inf_restrictScalars (orthK h U) Λ h𝔭.isPrime]`.
-/
theorem locF_mem_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {M T Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ)
    (hM : Λ ⊓ U.restrictScalars (𝓞 K) = M) (hT : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibS h U 𝔭 M T := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ := hu
  simp only [fibS, Set.mem_setOf_eq]
  refine ⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']
  · rw [← hM, locF_inf_restrictScalars U Λ h𝔭.isPrime]
  · rw [← hT, locF_inf_restrictScalars (orthK h U) Λ h𝔭.isPrime]

/- English proof (translation)
Establish `hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀` using `hu`. Establish `hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T)`. Rewrite using `[he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']`. Establish `hMU : ∀ x ∈ M, x ∈ U` using `fun x hx => hM.2 ▸ Submodule.subset_span hx`. Establish `hTW : ∀ x ∈ T, x ∈ orthK h U` using `fun x hx => hT.2 ▸ Submodule.subset_span hx`.

Establish `hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M` using `locF_sup_inf hUc hMU hTW h𝔭.isPrime`. Establish `hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T`. Rewrite using `[sup_comm]`. Conclude with `locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime`. Use extensionality with `Λ`.

Simplify using `only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩`. Establish `hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁`. Introduce `x hx`.

Take `⟨s, hs, hsx⟩` from `(mem_locF_lemma 𝔭 _ x).mp hx`. Take `⟨m, hm, t, ht, hmt⟩` from `Submodule.mem_sup.mp hsx`. Establish `hm' : m ∈ locF 𝔭 Λ₁`. Establish `hm1 : m ∈ locF 𝔭 M` using `(mem_locF_lemma 𝔭 _ m).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩`. Rewrite `hm1` using `[← hcU]`.

Conclude with `(Submodule.mem_inf.mp hm1).1`. Establish `ht' : t ∈ locF 𝔭 Λ₁`. Establish `ht1 : t ∈ locF 𝔭 T` using `(mem_locF_lemma 𝔭 _ t).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩`. Rewrite `ht1` using `[← hcW]`. Conclude with `(Submodule.mem_inf.mp ht1).1`.

Establish `hsx' : s • x ∈ locF 𝔭 Λ₁` using `by rw [← hmt]; exact add_mem hm' ht'`. Take `⟨s', hs', h'⟩` from `(mem_locF_lemma 𝔭 _ _).mp hsx'`. Conclude with `(mem_locF_lemma 𝔭 _ x).mpr ⟨s' * s, Submonoid.mul_mem _ hs' hs, by rw [mul_smul]; exact h'⟩`. Use `le_antisymm ?_ hle` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `rfl`. Conclude with `⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩`.
-/
theorem fibS_eq_singleton (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {M T Λ₀ : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hΛ₀ : Submodule.IsLattice K Λ₀) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (he : locF 𝔭 (M ⊔ T) = locF 𝔭 Λ₀) :
    fibS h U 𝔭 M T = {locF 𝔭 (M ⊔ T)} := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀ := hu
  have hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T) := by
    rw [he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']
  have hMU : ∀ x ∈ M, x ∈ U := fun x hx => hM.2 ▸ Submodule.subset_span hx
  have hTW : ∀ x ∈ T, x ∈ orthK h U := fun x hx => hT.2 ▸ Submodule.subset_span hx
  have hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M :=
    locF_sup_inf hUc hMU hTW h𝔭.isPrime
  have hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
    rw [sup_comm]; exact locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime
  ext Λ
  simp only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁ := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
      obtain ⟨m, hm, t, ht, hmt⟩ := Submodule.mem_sup.mp hsx
      have hm' : m ∈ locF 𝔭 Λ₁ := by
        have hm1 : m ∈ locF 𝔭 M :=
          (mem_locF_lemma 𝔭 _ m).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcU] at hm1
        exact (Submodule.mem_inf.mp hm1).1
      have ht' : t ∈ locF 𝔭 Λ₁ := by
        have ht1 : t ∈ locF 𝔭 T :=
          (mem_locF_lemma 𝔭 _ t).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcW] at ht1
        exact (Submodule.mem_inf.mp ht1).1
      have hsx' : s • x ∈ locF 𝔭 Λ₁ := by rw [← hmt]; exact add_mem hm' ht'
      obtain ⟨s', hs', h'⟩ := (mem_locF_lemma 𝔭 _ _).mp hsx'
      exact (mem_locF_lemma 𝔭 _ x).mpr
        ⟨s' * s, Submonoid.mul_mem _ hs' hs, by rw [mul_smul]; exact h'⟩
    refine le_antisymm ?_ hle
    calc locF 𝔭 Λ₁ = dualF h 𝔭 (locF 𝔭 Λ₁) := hd.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
      _ = locF 𝔭 (M ⊔ T) := hN
  · rintro rfl
    exact ⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩

/- English proof (translation)
Establish `hN` using `isLattice_sup hUc hM hT`. Take `⟨s, hs⟩` from `exists_locF_eq (F := F) hN hΛ₀.1`. Establish `hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)}` using `fun 𝔭 h𝔭 => fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)`. Establish `hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1`. Introduce `𝔭 h𝔭`.

Rewrite using `[fibP_eq, hsing 𝔭 h𝔭]`. Simplify using the standard rewrite rules. Rewrite using `[tprod_eq_prod hone, ← Finset.prod_coe_sort s]`. Simplify using `only [fibP_eq]`. Rewrite using `[← Nat.card_pi]`.

Use `Nat.card_congr (Equiv.ofBijective (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Λ₁ = Λ₂`. Use `G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_` and prove the remaining obligations.

Distinguish the cases in `hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s`. Conclude with `congrArg Subtype.val (congrFun he ⟨_, hps⟩)`. Establish `a1` using `locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭`. Establish `a2` using `locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭`. Rewrite `a1`, `a2` using `[hsing _ hps, Set.mem_singleton_iff]`.

Conclude with `a1.trans a2.symm`. Introduce `τ`. Take `⟨Λ, ⟨hΛ, hin, hout⟩, -⟩` from `exists_unique_patch hK hF hN s (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by`. Introduce `𝔭 hp`. Simplify using `only [dif_pos hp]`.

Take `⟨⟨A, hA, e⟩, -, -, -⟩` from `(τ ⟨𝔭, hp⟩).2`. Conclude with `⟨by rw [← e, LocF.locF_idem], A, hA, e⟩)`. Establish `hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T`. Introduce `𝔭`. Distinguish the cases in `hp : 𝔭 ∈ s`.

Rewrite using `[hin 𝔭 hp, dif_pos hp]`. Conclude with `(τ ⟨𝔭, hp⟩).2`. Rewrite using `[hout 𝔭 hp, hsing 𝔭 hp]`. Conclude with `Set.mem_singleton _`. Establish `hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T`.

Use `⟨⟨hΛ, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show Formalism.HermitianLatticesTheory.dual h Λ = Λ`. Use `G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_` and prove the remaining obligations. Rewrite using `[G7.locF_dual hF h hΛ.fg h𝔭.isPrime]`. Conclude with `(hfib ⟨𝔭, h𝔭⟩).2.1`.

Use `G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_` and prove the remaining obligations. Rewrite using `[LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]`. Conclude with `(hfib ⟨𝔭, h𝔭⟩).2.2.1`. Use `G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_` and prove the remaining obligations. Rewrite using `[LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]`.

Conclude with `(hfib ⟨𝔭, h𝔭⟩).2.2.2`. Use `⟨⟨Λ, hmem⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `𝔭`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show locF 𝔭.1.1 Λ = (τ 𝔭).1`.

Rewrite using `[hin 𝔭.1 𝔭.2, dif_pos 𝔭.2]`.
-/
theorem card_glue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hT : IsLatIn (orthK h U) T) :
    Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T := by
  classical
  have hN := isLattice_sup hUc hM hT
  obtain ⟨s, hs⟩ := exists_locF_eq (F := F) hN hΛ₀.1
  have hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)} := fun 𝔭 h𝔭 =>
    fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)
  have hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1 := by
    intro 𝔭 h𝔭
    rw [fibP_eq, hsing 𝔭 h𝔭]
    simp
  rw [tprod_eq_prod hone, ← Finset.prod_coe_sort s]
  simp only [fibP_eq]
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)
  · rintro ⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he
    apply Subtype.ext
    show Λ₁ = Λ₂
    refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
    by_cases hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s
    · exact congrArg Subtype.val (congrFun he ⟨_, hps⟩)
    · have a1 := locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭
      have a2 := locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭
      rw [hsing _ hps, Set.mem_singleton_iff] at a1 a2
      exact a1.trans a2.symm
  · intro τ
    obtain ⟨Λ, ⟨hΛ, hin, hout⟩, -⟩ := exists_unique_patch hK hF hN s
      (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by
        intro 𝔭 hp
        simp only [dif_pos hp]
        obtain ⟨⟨A, hA, e⟩, -, -, -⟩ := (τ ⟨𝔭, hp⟩).2
        exact ⟨by rw [← e, LocF.locF_idem], A, hA, e⟩)
    have hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T := by
      intro 𝔭
      by_cases hp : 𝔭 ∈ s
      · rw [hin 𝔭 hp, dif_pos hp]
        exact (τ ⟨𝔭, hp⟩).2
      · rw [hout 𝔭 hp, hsing 𝔭 hp]
        exact Set.mem_singleton _
    have hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T := by
      refine ⟨⟨hΛ, ?_, ?_⟩, ?_⟩
      · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
        refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [G7.locF_dual hF h hΛ.fg h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.2
    refine ⟨⟨Λ, hmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 Λ = (τ 𝔭).1
    rw [hin 𝔭.1 𝔭.2, dif_pos 𝔭.2]

end Formalism.L2.SG.Pf.G8
