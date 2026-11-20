import Mathlib

/- English proof (translation)
Rewrite using `[Subgroup.mem_map_equiv]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.Reformulated.B.Yt3.mem_conj {G : Type} [Group G] {K : Subgroup G} {g y : G} :
    y ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

/- English proof (translation)
Introduce `G _ K g h`. Use `set H : Subgroup K := (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).subgroupOf K with hH`. Establish `hfin : Finite (K ⧸ H)` using `Nat.finite_of_card_ne_zero h`. Use `letI : Fintype (K ⧸ H) := Fintype.ofFinite _`. Establish `key : ∀ (a b : K) (k : G), k ∈ K → ((((a : G) * g)⁻¹ * ((b : G) * g * k) ∈ K) ↔ (a : K ⧸ H) = (b : K ⧸ H))`.

Introduce `a b k hk`. Rewrite using `[QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, UpperTheory.Reformulated.B.Yt3.mem_conj, ← mul_assoc, K.mul_mem_cancel_right hk]`. Simplify using `[mul_assoc]`. Use `⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `⟨_, (q.out).2, 1, K.one_mem, (mul_one _).symm⟩`. Introduce and unpack `x ⟨k₁, hk₁, k₂, hk₂, rfl⟩`. Use `⟨(((((⟨k₁, hk₁⟩ : K) : K ⧸ H)).out : K) : G) * g, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(key _ ⟨k₁, hk₁⟩ k₂ hk₂).2 (QuotientGroup.out_eq' _)`.

Introduce and unpack `γ ⟨hγ, hx⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hγ`. Use `(key _ ⟨k₁, hk₁⟩ k₂ hk₂).1 hx` as an intermediate fact. Rewrite `this` using `[QuotientGroup.out_eq']`. Rewrite using `[this]`.
-/
theorem UpperTheory.Reformulated.B.Yt3.exists_reps :
    ∀ {G : Type} [inst : Group G] {K : Subgroup G} {g : G},
      (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).relIndex K ≠ (0 : ℕ) →
        ∃ (R : Finset G),
          (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
            ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K g h
  classical
  set H : Subgroup K :=
    (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).subgroupOf K with hH
  have hfin : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero h
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (a b : K) (k : G), k ∈ K →
      ((((a : G) * g)⁻¹ * ((b : G) * g * k) ∈ K) ↔ (a : K ⧸ H) = (b : K ⧸ H)) := by
    intro a b k hk
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, UpperTheory.Reformulated.B.Yt3.mem_conj,
      ← mul_assoc, K.mul_mem_cancel_right hk]
    simp [mul_assoc]
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, (mul_one _).symm⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨(((((⟨k₁, hk₁⟩ : K) : K ⧸ H)).out : K) : G) * g,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨k₁, hk₁⟩ k₂ hk₂).2 (QuotientGroup.out_eq' _)
    · rintro γ ⟨hγ, hx⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      have := (key _ ⟨k₁, hk₁⟩ k₂ hk₂).1 hx
      rw [QuotientGroup.out_eq'] at this
      rw [this]
