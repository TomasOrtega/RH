import Mathlib

namespace GlobalTheory.RelIndexOfMap

/- English proof (translation)
Rewrite using `[← hA, ← Subgroup.relIndex_comap]`. Unfold `Subgroup.relIndex`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]`.

Conclude with `hB a a.2`.
-/
theorem relIndex_eq_of_map {X P : Type} [Group X] [Group P] (φ : X →* P) (A B : Subgroup X)
    (U V : Subgroup P) (hA : A.map φ = U) (hB : ∀ a ∈ A, a ∈ B ↔ φ a ∈ V) :
    B.relIndex A = V.relIndex U := by
  rw [← hA, ← Subgroup.relIndex_comap]
  unfold Subgroup.relIndex
  congr 1
  ext a
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  exact hB a a.2

/- English proof (translation)
Simplify using `only [Subgroup.index_eq_card]`. Rewrite using `[← Nat.card_pi]`. Set `f : ((∀ i, H i) ⧸ Subgroup.pi Set.univ V) → ∀ i, H i ⧸ V i` to `Quotient.lift (fun g i => (QuotientGroup.mk (g i) : H i ⧸ V i)) (by`. Introduce `a b hab`. Establish `hab'` using `QuotientGroup.leftRel_apply.1 hab`.

Use function extensionality and compare the values at `i`. Conclude with `QuotientGroup.eq.2 (hab' i trivial))`. Use `Nat.card_eq_of_bijective f ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Use `Quotient.inductionOn₂ a b fun a b hab => ?_` and prove the remaining obligations.

Use `QuotientGroup.eq.2 fun i _ => ?_` and prove the remaining obligations. Conclude with `QuotientGroup.eq.1 (congrFun hab i)`. Introduce `q`. Use `⟨QuotientGroup.mk fun i => (q i).out, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Conclude with `Quotient.out_eq (q i)`.
-/
theorem index_pi_dep {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).index = ∏ i, (V i).index := by
  simp only [Subgroup.index_eq_card]
  rw [← Nat.card_pi]
  let f : ((∀ i, H i) ⧸ Subgroup.pi Set.univ V) → ∀ i, H i ⧸ V i :=
    Quotient.lift (fun g i => (QuotientGroup.mk (g i) : H i ⧸ V i)) (by
      intro a b hab
      have hab' := QuotientGroup.leftRel_apply.1 hab
      funext i
      exact QuotientGroup.eq.2 (hab' i trivial))
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b fun a b hab => ?_
    refine QuotientGroup.eq.2 fun i _ => ?_
    exact QuotientGroup.eq.1 (congrFun hab i)
  · intro q
    refine ⟨QuotientGroup.mk fun i => (q i).out, ?_⟩
    funext i
    exact Quotient.out_eq (q i)

/- English proof (translation)
Set `f : (∀ i, U i) →* (∀ i, H i)` to `{ toFun := fun x i => (x i : H i) map_one' := rfl map_mul' := fun _ _ => rfl }`. Establish `h` using `relIndex_eq_of_map f ⊤ (Subgroup.pi Set.univ fun i => (V i).subgroupOf (U i)) (Subgroup.pi Set.univ U) (Subgroup.pi Set.univ V) (by`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, -, rfl⟩ i _`.

Conclude with `(x i).2`. Introduce `hu`. Conclude with `⟨fun i => ⟨u i, hu i trivial⟩, trivial, rfl⟩) (by`. Introduce `a _`. Conclude with `Iff.rfl)`.

Rewrite using `[← h, Subgroup.relIndex_top_right]`. Conclude with `index_pi_dep (fun i => (V i).subgroupOf (U i))`.
-/
theorem relIndex_pi {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (U V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).relIndex (Subgroup.pi Set.univ U) = ∏ i, (V i).relIndex (U i) := by
  let f : (∀ i, U i) →* (∀ i, H i) :=
    { toFun := fun x i => (x i : H i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have h := relIndex_eq_of_map f ⊤ (Subgroup.pi Set.univ fun i => (V i).subgroupOf (U i))
    (Subgroup.pi Set.univ U) (Subgroup.pi Set.univ V) (by
      ext u
      constructor
      · rintro ⟨x, -, rfl⟩ i _
        exact (x i).2
      · intro hu
        exact ⟨fun i => ⟨u i, hu i trivial⟩, trivial, rfl⟩) (by
      intro a _
      exact Iff.rfl)
  rw [← h, Subgroup.relIndex_top_right]
  exact index_pi_dep (fun i => (V i).subgroupOf (U i))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[mul_assoc]`. Introduce `hx`. Conclude with `⟨_, hx, by simp [mul_assoc]⟩`.
-/
theorem mem_map_conj {H : Type} [Group H] (J : Subgroup H) (h x : H) :
    x ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H → MulAut H) h)) J ↔
      h⁻¹ * x * h ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

/- English proof (translation)
Introduce `d1 G _ M N K ι _ H _ S hS L J Nn hKJ hSK hSM hNN hSN hsurj δ r hr c h hrc hc hδ`. Establish `hd : ∀ (x : G) (n : N.subgroupOf M), n ∈ d1 M N K x ↔ x⁻¹ * ((n : M) : G) * x ∈ K`. Introduce `x n`. Simplify using `[d1, Subgroup.mem_comap]`. Establish `key : ∀ a b : G, a * b⁻¹ ∈ S → b ∈ K → (∀ i, L i a ∈ J i) → a ∈ K`.

Introduce `a b hab hb ha`. Establish `: a * b⁻¹ ∈ K` using `hSK _ hab fun i => by`. Rewrite using `[map_mul, map_inv]`. Conclude with `mul_mem (ha i) (inv_mem (hKJ b hb i))`. Simplify using `using mul_mem this hb`.

Set `φ : (N.subgroupOf M) →* (∀ i, H i)` to `{ toFun := fun n i => (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i) map_one' := by ext i; simp map_mul' := by intro a b; ext i; simp [mul_assoc] }`. Establish `hφ : ∀ n i, φ n i = (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i)` using `fun _ _ => rfl`. Establish `hφN : ∀ n i, φ n i ∈ Nn i` using `fun n i => (hδ i _).2 (hNN _ n.2 i)`. Establish `h1 : ∀ n i, φ n i ∈ J i ↔ L i (δ⁻¹ * ((n : M) : G) * δ) ∈ J i`. Introduce `n i`.

Establish `e : φ n i = (c i)⁻¹ * L i (δ⁻¹ * ((n : M) : G) * δ) * c i`. Simplify using `[hφ, mul_assoc]`. Rewrite using `[e, Subgroup.mul_mem_cancel_right _ (hc i), Subgroup.mul_mem_cancel_left _ (inv_mem (hc i))]`. Establish `h2 : ∀ n i, φ n i ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i) ↔ L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) ∈ J i`. Introduce `n i`.

Rewrite using `[mem_map_conj]`. Establish `e : (h i)⁻¹ * φ n i * h i = L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r))`. Simplify using `[hφ, hrc, mul_assoc]`. Rewrite using `[e]`. Establish `hs : ∀ u : ∀ i, H i, (∀ i, u i ∈ Nn i) → ∃ n : N.subgroupOf M, ((n : M) : G) ∈ S ∧ φ n = u`.

Introduce `u hu`. Take `⟨y, hy, hyu⟩` from `hsurj fun i => (L i δ * c i) * u i * (L i δ * c i)⁻¹`. Establish `hyN : y ∈ N` using `hSN y hy fun i => by`. Rewrite using `[← hδ i, hyu i]`. Simplify `hu i` using `[mul_assoc]`.

Use `⟨⟨⟨y, hSM hy⟩, hyN⟩, hy, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[hφ]`. Simplify using `[hyu, mul_assoc]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← relIndex_pi]`. Use `relIndex_eq_of_map φ _ _ _ _ ?_ ?_` and prove the remaining obligations. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, rfl⟩ i _`.

Conclude with `⟨hφN n i, (h1 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩`. Introduce `hu`. Take `⟨n, hn, rfl⟩` from `hs u fun i => (hu i trivial).1`. Use `⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h1 n i).1 (hu i trivial).2), rfl⟩` and prove the remaining obligations. Conclude with `hS.conj_mem' _ hn _`.

Introduce `a ha`. Rewrite `ha`, the goal using `[hd]`. Prove the components needed by the constructor for the conclusion. Introduce `hb i _`. Conclude with `(h2 a i).2 (hKJ _ hb i)`.

Introduce `hb`. Use `key _ _ ?_ ha fun i => (h2 a i).1 (hb i trivial)` and prove the remaining obligations. Use `mul_mem (inv_mem hr) (hS.conj_mem _ hr (δ⁻¹ * ((a : M) : G) * δ))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.

Rewrite using `[← relIndex_pi]`. Use `relIndex_eq_of_map φ _ _ _ _ ?_ ?_` and prove the remaining obligations. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, rfl⟩ i _`.

Conclude with `⟨hφN n i, (h2 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩`. Introduce `hu`. Take `⟨n, hn, rfl⟩` from `hs u fun i => (hu i trivial).1`. Use `⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h2 n i).1 (hu i trivial).2), rfl⟩` and prove the remaining obligations. Conclude with `hS.conj_mem' _ hn _`.

Introduce `a ha`. Rewrite `ha`, the goal using `[hd]`. Prove the components needed by the constructor for the conclusion. Introduce `hb i _`. Conclude with `(h1 a i).2 (hKJ _ hb i)`.

Introduce `hb`. Use `key _ _ ?_ ha fun i => (h1 a i).1 (hb i trivial)` and prove the remaining obligations. Use `mul_mem (hS.conj_mem _ (inv_mem hr) (δ⁻¹ * ((a : M) : G) * δ)) hr` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem main : (let d1 : {G : Type} → [inst : Group G] → (M N : Subgroup G) → Subgroup G → G → Subgroup ↥(Subgroup.subgroupOf N M) := @(fun {G : Type} [Group G] (M N K : Subgroup G) (x : G) ↦ Subgroup.comap (MonoidHom.comp (Subgroup.subtype M) (Subgroup.subtype (Subgroup.subgroupOf N M))) (Subgroup.comap (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) x⁻¹)) K)); ∀ {G : Type} [inst : Group G] {M N K : Subgroup G} {ι : Type} [inst_1 : Fintype ι] {H : ι → Type} [inst_2 : (i : ι) → Group (H i)] (S : Subgroup G) [Subgroup.Normal S] (L : (i : ι) → G →* H i) (J Nn : (i : ι) → Subgroup (H i)), (∀ k ∈ K, ∀ (i : ι), (L i : G → H i) k ∈ J i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ J i) → y ∈ K) → S ≤ M → (∀ n ∈ N, ∀ (i : ι), (L i : G → H i) n ∈ Nn i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ Nn i) → y ∈ N) → (∀ (u : (i : ι) → H i), ∃ y ∈ S, ∀ (i : ι), (L i : G → H i) y = u i) → ∀ {δ r : G}, r ∈ S → ∀ (c h : (i : ι) → H i), (∀ (i : ι), (L i : G → H i) r = c i * h i) → (∀ (i : ι), c i ∈ J i) → (∀ (i : ι) (x : H i), ((L i : G → H i) δ * c i)⁻¹ * x * ((L i : G → H i) δ * c i) ∈ Nn i ↔ x ∈ Nn i) → Subgroup.relIndex (d1 M N K (δ * r)) (d1 M N K δ) = ∏ i : ι, Subgroup.relIndex (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i)) (Nn i ⊓ J i) ∧ Subgroup.relIndex (d1 M N K δ) (d1 M N K (δ * r)) = ∏ i : ι, Subgroup.relIndex (J i) (Nn i ⊓ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i))) := by
  intro d1 G _ M N K ι _ H _ S hS L J Nn hKJ hSK hSM hNN hSN hsurj δ r hr c h hrc hc hδ
  have hd : ∀ (x : G) (n : N.subgroupOf M), n ∈ d1 M N K x ↔ x⁻¹ * ((n : M) : G) * x ∈ K := by
    intro x n
    simp [d1, Subgroup.mem_comap]
  have key : ∀ a b : G, a * b⁻¹ ∈ S → b ∈ K → (∀ i, L i a ∈ J i) → a ∈ K := by
    intro a b hab hb ha
    have : a * b⁻¹ ∈ K := hSK _ hab fun i => by
      rw [map_mul, map_inv]
      exact mul_mem (ha i) (inv_mem (hKJ b hb i))
    simpa using mul_mem this hb
  let φ : (N.subgroupOf M) →* (∀ i, H i) :=
    { toFun := fun n i => (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i)
      map_one' := by ext i; simp
      map_mul' := by intro a b; ext i; simp [mul_assoc] }
  have hφ : ∀ n i, φ n i = (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i) := fun _ _ => rfl
  have hφN : ∀ n i, φ n i ∈ Nn i := fun n i => (hδ i _).2 (hNN _ n.2 i)
  have h1 : ∀ n i, φ n i ∈ J i ↔ L i (δ⁻¹ * ((n : M) : G) * δ) ∈ J i := by
    intro n i
    have e : φ n i = (c i)⁻¹ * L i (δ⁻¹ * ((n : M) : G) * δ) * c i := by
      simp [hφ, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ (hc i), Subgroup.mul_mem_cancel_left _ (inv_mem (hc i))]
  have h2 : ∀ n i, φ n i ∈
      Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i) ↔
      L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) ∈ J i := by
    intro n i
    rw [mem_map_conj]
    have e : (h i)⁻¹ * φ n i * h i = L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) := by
      simp [hφ, hrc, mul_assoc]
    rw [e]
  have hs : ∀ u : ∀ i, H i, (∀ i, u i ∈ Nn i) →
      ∃ n : N.subgroupOf M, ((n : M) : G) ∈ S ∧ φ n = u := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := hsurj fun i => (L i δ * c i) * u i * (L i δ * c i)⁻¹
    have hyN : y ∈ N := hSN y hy fun i => by
      rw [← hδ i, hyu i]
      simpa [mul_assoc] using hu i
    refine ⟨⟨⟨y, hSM hy⟩, hyN⟩, hy, ?_⟩
    ext i
    rw [hφ]
    simp [hyu, mul_assoc]
  constructor
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h1 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h1 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h2 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h2 a i).1 (hb i trivial)
        have := mul_mem (inv_mem hr) (hS.conj_mem _ hr (δ⁻¹ * ((a : M) : G) * δ))
        convert this using 1
        group
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h2 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h2 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h1 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h1 a i).1 (hb i trivial)
        have := mul_mem (hS.conj_mem _ (inv_mem hr) (δ⁻¹ * ((a : M) : G) * δ)) hr
        convert this using 1
        group

end GlobalTheory.RelIndexOfMap
