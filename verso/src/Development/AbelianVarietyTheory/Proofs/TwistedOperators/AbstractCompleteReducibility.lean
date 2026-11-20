import Mathlib

open Module

namespace GlobalTheory

/- English proof (translation)
Set `bs` to `Module.finBasis ℂ T`. Set `F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ)` to `LinearMap.pi fun i => b (bs i : E)`. Establish `key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0`. Introduce `x hx t ht`. Establish `h1 : (b.flip x) ∘ₛₗ T.subtype = 0` using `bs.ext fun i => by simpa [F] using congrFun hx i`.

Conclude with `LinearMap.congr_fun h1 ⟨t, ht⟩`. Establish `hinj : Function.Injective (F ∘ₗ T.subtype)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Conclude with `Subtype.ext (hT z z.2 (key z hz z z.2))`.

Establish `hsurj : Function.Surjective (F ∘ₗ T.subtype)` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj`. Take `⟨z, hz⟩` from `hsurj (F ψ)`. Use `⟨z, z.2, key (ψ - z) ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← hz]`. Simplify using the standard rewrite rules.
-/
theorem exists_mem_sub_orth_of_finiteDimensional {E : Type} [AddCommGroup E] [Module ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : Submodule ℂ E) [FiniteDimensional ℂ T]
    (hT : ∀ t ∈ T, b t t = 0 → t = 0) (ψ : E) : ∃ s ∈ T, ∀ t ∈ T, b t (ψ - s) = 0 := by
  let bs := Module.finBasis ℂ T
  let F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ) := LinearMap.pi fun i => b (bs i : E)
  have key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0 := by
    intro x hx t ht
    have h1 : (b.flip x) ∘ₛₗ T.subtype = 0 :=
      bs.ext fun i => by simpa [F] using congrFun hx i
    exact LinearMap.congr_fun h1 ⟨t, ht⟩
  have hinj : Function.Injective (F ∘ₗ T.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext (hT z z.2 (key z hz z z.2))
  have hsurj : Function.Surjective (F ∘ₗ T.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨z, hz⟩ := hsurj (F ψ)
  refine ⟨z, z.2, key (ψ - z) ?_⟩
  rw [map_sub, ← hz]
  simp

/- English proof (translation)
Introduce `E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe`. Set `S` to `⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A`. Use `show ψ ∈ S`. Set `V` to `N.map e`. Establish `hVN : V ≤ N` using `by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx`.

Establish `heV : ∀ v ∈ V, e v = v` using `by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx`. Establish `hψV : ψ ∈ V` using `⟨ψ, hψN, hψe⟩`. Establish `hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S` using `fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl`. Establish `hpos0 : ∀ x ∈ N, b x x = 0 → x = 0`. Introduce `x hx h0`.

Assume the negation of the conclusion as `hne`. Use `hpos x hx hne` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A` using `fun x => ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2, fun A hx hA => sInf_le ⟨hx, hA⟩⟩`.

Set `C : Submodule ℂ E` to `sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})`. Establish `hCP : P C`. Apply `hInf` to reduce the goal to its premises. Introduce and unpack `X (rfl | ⟨A, hA, rfl⟩)`. Conclude with `hN`.

Conclude with `hperp A hA.1 hA.2.1`. Establish `hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0`. Introduce `x hx A hA a ha`. Establish `: x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)` using `Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this`.

Conclude with `this.2 a ha`. Establish `hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C`. Introduce `x hx h`. Use `Submodule.mem_sInf.2 ?_` and prove the remaining obligations. Introduce and unpack `X (rfl | ⟨A, hA, rfl⟩)`.

Conclude with `hx`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`. Conclude with `⟨hx, fun a ha => h A hA a ha⟩`. Establish `hfinT : FiniteDimensional ℂ ↥(S ⊓ V)` using `Submodule.finiteDimensional_of_le inf_le_right`. Take `⟨s, hsT, hsorth⟩` from `exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V) (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ`.

Establish `hcV : ψ - s ∈ V` using `V.sub_mem hψV hsT.2`. Establish `hcC : ψ - s ∈ C`. Use `hCmem _ (hVN hcV) fun A hA a ha => ?_` and prove the remaining obligations. Establish `haN : a ∈ N` using `hA.1 ha`. Establish `heaT : e a ∈ S ⊓ V` using `⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩`.

Rewrite using `[← heV _ hcV, ← hsa a haN _ (hVN hcV)]`. Conclude with `hsorth _ heaT`. It suffices to establish `hc0 : ψ - s = 0 by`. Rewrite `hc0` using `[sub_eq_zero]`. Rewrite using `[hc0]`.

Conclude with `hsT.1`. Assume the negation of the conclusion as `hc0`. Take `⟨D, hcD, hDP, hDmin⟩` from `hGen (ψ - s)`. Establish `hDC : D ≤ C` using `hDmin C hcC hCP`. Establish `hDN : D ≤ N` using `hDmin N (hVN hcV) hN`.

Establish `hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n` using `⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩`. Take `⟨B, hBD, hBP, hBV, hBn⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ → Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V)` using `fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩`. Take `⟨β, hβBV, hβ0⟩` from `(Submodule.ne_bot_iff _).1 hBV`. Take `⟨G, hβG, hGP, hGmin⟩` from `hGen β`.

Establish `hGB : G ≤ B` using `hGmin B hβBV.1 hBP`. Establish `hGN : G ≤ N` using `hGB.trans (hBD.trans hDN)`. Establish `hβV : β ∈ V` using `hβBV.2`. Establish `hβe : e β = β` using `heV β hβV`. Establish `hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G`.

Use `⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩` and prove the remaining obligations. Establish `hB''N : B'' ≤ N` using `hle.trans hGN`. Distinguish the cases in `hV'' : B'' ⊓ V = ⊥`. Use `left`. Establish `hey : ∀ y ∈ B'', e y = 0`.

Introduce `y hy`. Establish `: e y ∈ B'' ⊓ V` using `⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩`. Rewrite `this` using `[hV'']`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Establish `hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a)`.

Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`. Use `⟨hVN hβV, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]`. Establish `hGperp` using `hGmin _ hβperp (hperp B'' hB''N hP)`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Establish `hyp` using `hGperp (hle hy)`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp`. Conclude with `(Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))`. Use `right`.

Establish `hle' : B'' ⊓ V ≤ B ⊓ V` using `inf_le_inf_right _ (hle.trans hGB)`. Establish `hfinBV : FiniteDimensional ℂ ↥(B ⊓ V)` using `Submodule.finiteDimensional_of_le inf_le_right`. Establish `heq : B'' ⊓ V = B ⊓ V` using `Submodule.eq_of_le_of_finrank_le hle' (by`. Rewrite using `[hBn]`. Conclude with `hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')`.

Establish `hβB'' : β ∈ B''`. Establish `h2` using `hβBV`. Rewrite `h2` using `[← heq]`. Conclude with `h2.1`. Conclude with `le_antisymm hle (hGmin B'' hβB'' hP)`.

Conclude with `hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))`.
-/
theorem abstract_complete_reducibility :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  classical
  intro E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe
  let S := ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A
  show ψ ∈ S
  let V := N.map e
  have hVN : V ≤ N := by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx
  have heV : ∀ v ∈ V, e v = v := by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx
  have hψV : ψ ∈ V := ⟨ψ, hψN, hψe⟩
  have hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S :=
    fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl
  have hpos0 : ∀ x ∈ N, b x x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have := hpos x hx hne
    rw [h0] at this
    simp at this
  have hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A := fun x =>
    ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2,
      fun A hx hA => sInf_le ⟨hx, hA⟩⟩
  let C : Submodule ℂ E := sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})
  have hCP : P C := by
    apply hInf
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hN
    · exact hperp A hA.1 hA.2.1
  have hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0 := by
    intro x hx A hA a ha
    have : x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
      Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a ha
  have hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C := by
    intro x hx h
    refine Submodule.mem_sInf.2 ?_
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hx
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      exact ⟨hx, fun a ha => h A hA a ha⟩
  have hfinT : FiniteDimensional ℂ ↥(S ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hsT, hsorth⟩ := exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V)
    (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ
  have hcV : ψ - s ∈ V := V.sub_mem hψV hsT.2
  have hcC : ψ - s ∈ C := by
    refine hCmem _ (hVN hcV) fun A hA a ha => ?_
    have haN : a ∈ N := hA.1 ha
    have heaT : e a ∈ S ⊓ V := ⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩
    rw [← heV _ hcV, ← hsa a haN _ (hVN hcV)]
    exact hsorth _ heaT
  suffices hc0 : ψ - s = 0 by
    rw [sub_eq_zero] at hc0
    rw [hc0]
    exact hsT.1
  by_contra hc0
  obtain ⟨D, hcD, hDP, hDmin⟩ := hGen (ψ - s)
  have hDC : D ≤ C := hDmin C hcC hCP
  have hDN : D ≤ N := hDmin N (hVN hcV) hN
  have hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n :=
    ⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩
  obtain ⟨B, hBD, hBP, hBV, hBn⟩ := Nat.find_spec hex
  have hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ →
      Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V) :=
    fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩
  obtain ⟨β, hβBV, hβ0⟩ := (Submodule.ne_bot_iff _).1 hBV
  obtain ⟨G, hβG, hGP, hGmin⟩ := hGen β
  have hGB : G ≤ B := hGmin B hβBV.1 hBP
  have hGN : G ≤ N := hGB.trans (hBD.trans hDN)
  have hβV : β ∈ V := hβBV.2
  have hβe : e β = β := heV β hβV
  have hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G := by
    refine ⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩
    have hB''N : B'' ≤ N := hle.trans hGN
    by_cases hV'' : B'' ⊓ V = ⊥
    · left
      have hey : ∀ y ∈ B'', e y = 0 := by
        intro y hy
        have : e y ∈ B'' ⊓ V := ⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩
        rw [hV''] at this
        exact (Submodule.mem_bot ℂ).1 this
      have hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a) := by
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
        refine ⟨hVN hβV, fun y hy => ?_⟩
        rw [← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]
      have hGperp := hGmin _ hβperp (hperp B'' hB''N hP)
      rw [eq_bot_iff]
      intro y hy
      have hyp := hGperp (hle hy)
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp
      exact (Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))
    · right
      have hle' : B'' ⊓ V ≤ B ⊓ V := inf_le_inf_right _ (hle.trans hGB)
      have hfinBV : FiniteDimensional ℂ ↥(B ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
      have heq : B'' ⊓ V = B ⊓ V := Submodule.eq_of_le_of_finrank_le hle' (by
        rw [hBn]; exact hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')
      have hβB'' : β ∈ B'' := by
        have h2 := hβBV
        rw [← heq] at h2
        exact h2.1
      exact le_antisymm hle (hGmin B'' hβB'' hP)
  exact hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))

end GlobalTheory
