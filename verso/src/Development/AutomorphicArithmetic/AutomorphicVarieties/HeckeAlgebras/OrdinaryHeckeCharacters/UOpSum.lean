import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Introduce `G _ I A M _ _ _ π a ha`. Establish `hfin : Finite (I.N ⧸ (I.Nconj a).subgroupOf I.N)` using `Nat.finite_of_card_ne_zero (I.fin_N a ha)`. Use `letI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _`. Establish `key : ∀ x y : I.N, (QuotientGroup.mk x : I.N ⧸ (I.Nconj a).subgroupOf I.N) = QuotientGroup.mk y ↔ (x : G)⁻¹ * y ∈ I.Nconj a`. Introduce `x y`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using the standard rewrite rules. Use `⟨⟨Finset.univ.image (fun q : I.N ⧸ (I.Nconj a).subgroupOf I.N => ((q.out : I.N) : G)), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`.

Conclude with `q.out.2`. Introduce `x hx`. Use `⟨((QuotientGroup.mk (⟨x, hx⟩ : I.N) : I.N ⧸ (I.Nconj a).subgroupOf I.N).out : I.N), ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(key _ ⟨x, hx⟩).1 (QuotientGroup.out_eq' _)`. Introduce and unpack `u ⟨hu, hux⟩`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Establish `h` using `(key q.out ⟨x, hx⟩).2 hux`. Rewrite `h` using `[QuotientGroup.out_eq']`. Rewrite using `[h]`. Introduce `s hs hu`.

Set `i : ∀ u ∈ s, I.N ⧸ (I.Nconj a).subgroupOf I.N` to `fun u h => QuotientGroup.mk ⟨u, hs u h⟩`. Establish `inj : ∀ u₁ (h₁ : u₁ ∈ s) u₂ (h₂ : u₂ ∈ s), i u₁ h₁ = i u₂ h₂ → u₁ = u₂`. Introduce `u₁ h₁ u₂ h₂ h`. Establish `h'` using `(key ⟨u₁, hs _ h₁⟩ ⟨u₂, hs _ h₂⟩).1 h`. Conclude with `(hu u₂ (hs _ h₂)).unique ⟨h₁, h'⟩ ⟨h₂, by simp⟩`.

Establish `surj : ∀ q ∈ (Finset.univ : Finset (I.N ⧸ (I.Nconj a).subgroupOf I.N)), ∃ u h, i u h = q`. Introduce `q _`. Take `⟨u, ⟨h, h'⟩, -⟩` from `hu q.out q.out.2`. Conclude with `⟨u, h, ((key ⟨u, hs u h⟩ q.out).2 h').trans (QuotientGroup.out_eq' q)⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.card_bij i (fun _ _ => Finset.mem_univ _) inj surj, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]`. Introduce `v hv`. Rewrite using `[Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]`. Use `(Finset.sum_bij i (fun _ _ => Finset.mem_univ _) inj surj ?_).symm` and prove the remaining obligations. Introduce `u h`.

Establish `h'` using `(key ⟨u, hs u h⟩ (i u h).out).1 (QuotientGroup.out_eq' _).symm`. Take `⟨n, hn, e⟩` from `Subgroup.mem_map.1 h'`. Establish `e' : (((i u h).out : I.N) : G) * a = u * a * n`. Establish `e2 : a * n * a⁻¹ = u⁻¹ * (((i u h).out : I.N) : G)` using `e`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e', map_mul π (u * a) n, Module.End.mul_apply, hv n hn]`.
-/
theorem UpperTheory.V.Hi.uOpSum :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → (∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) ∧ ∀ s : Finset G, (∀ u ∈ s, u ∈ I.N) → (∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) → s.card = (I.Nconj a).relIndex I.N ∧ ∀ v ∈ fixd π I.N, I.uOp π a v = ∑ u ∈ s, π (u * a) v := by
  intro G _ I A M _ _ _ π a ha
  classical
  have hfin : Finite (I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Nat.finite_of_card_ne_zero (I.fin_N a ha)
  letI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have key : ∀ x y : I.N, (QuotientGroup.mk x : I.N ⧸ (I.Nconj a).subgroupOf I.N) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ I.Nconj a := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  refine ⟨⟨Finset.univ.image (fun q : I.N ⧸ (I.Nconj a).subgroupOf I.N => ((q.out : I.N) : G)), ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · intro x hx
    refine ⟨((QuotientGroup.mk (⟨x, hx⟩ : I.N) : I.N ⧸ (I.Nconj a).subgroupOf I.N).out : I.N),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨x, hx⟩).1 (QuotientGroup.out_eq' _)
    · rintro u ⟨hu, hux⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have h := (key q.out ⟨x, hx⟩).2 hux
      rw [QuotientGroup.out_eq'] at h
      rw [h]
  · intro s hs hu
    let i : ∀ u ∈ s, I.N ⧸ (I.Nconj a).subgroupOf I.N := fun u h => QuotientGroup.mk ⟨u, hs u h⟩
    have inj : ∀ u₁ (h₁ : u₁ ∈ s) u₂ (h₂ : u₂ ∈ s), i u₁ h₁ = i u₂ h₂ → u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂ h
      have h' := (key ⟨u₁, hs _ h₁⟩ ⟨u₂, hs _ h₂⟩).1 h
      exact (hu u₂ (hs _ h₂)).unique ⟨h₁, h'⟩ ⟨h₂, by simp⟩
    have surj : ∀ q ∈ (Finset.univ : Finset (I.N ⧸ (I.Nconj a).subgroupOf I.N)), ∃ u h, i u h = q := by
      intro q _
      obtain ⟨u, ⟨h, h'⟩, -⟩ := hu q.out q.out.2
      exact ⟨u, h, ((key ⟨u, hs u h⟩ q.out).2 h').trans (QuotientGroup.out_eq' q)⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.card_bij i (fun _ _ => Finset.mem_univ _) inj surj, Subgroup.relIndex, Subgroup.index,
        Nat.card_eq_fintype_card, Finset.card_univ]
    · intro v hv
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine (Finset.sum_bij i (fun _ _ => Finset.mem_univ _) inj surj ?_).symm
      intro u h
      have h' := (key ⟨u, hs u h⟩ (i u h).out).1 (QuotientGroup.out_eq' _).symm
      obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h'
      have e' : (((i u h).out : I.N) : G) * a = u * a * n := by
        have e2 : a * n * a⁻¹ = u⁻¹ * (((i u h).out : I.N) : G) := e
        calc (((i u h).out : I.N) : G) * a = u * (u⁻¹ * (((i u h).out : I.N) : G)) * a := by group
          _ = u * a * n := by rw [← e2]; group
      rw [e', map_mul π (u * a) n, Module.End.mul_apply, hv n hn]
