import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSignStatement

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `empty => exact .empty`. Consider the case `cone s hli hP hQs => exact .cone s hli hP (hQ _ hQs)`. Consider the case `union _ _ hAB ihA ihB => exact .union ihA ihB hAB`.
-/
theorem tile_mono {P : Set V} {Q Q' : Set V → Prop} (hQ : ∀ A, Q A → Q' A) {C : Set V} (h : Tile P Q C) :
    Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP (hQ _ hQs)
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `empty => exact .empty`. Consider the case `cone s hli hP hQs => exact hc s hli hP hQs`. Consider the case `union _ _ hAB ihA ihB => exact .union ihA ihB hAB`.
-/
theorem tile_refine {P : Set V} {Q Q' : Set V → Prop}
    (hc : ∀ s : Finset V, LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P → Q (coneOn s) → Tile P Q' (coneOn s))
    {C : Set V} (h : Tile P Q C) : Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact hc s hli hP hQs
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `empty => exact .empty`. Consider the case `cone s hli hP hQs => exact .cone s hli hP ⟨hQs, subset_rfl⟩`. Consider the case `@union A B _ _ hAB ihA ihB`. Conclude with `.union (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_left⟩) ihA) (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_right⟩) ihB) hAB`.
-/
theorem tile_inside {P : Set V} {Q : Set V → Prop} {C : Set V} (h : Tile P Q C) :
    Tile P (fun A => Q A ∧ A ⊆ C) C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP ⟨hQs, subset_rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    exact .union (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_left⟩) ihA)
      (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_right⟩) ihB) hAB

/- English proof (translation)
Break down `h with h | h | h` into its components or cases. Conclude with `Or.inl fun x hx => h x (hAC hx)`. Conclude with `Or.inr (Or.inl fun x hx => h x (hAC hx))`. Conclude with `Or.inr (Or.inr fun x hx => h x (hAC hx))`.
-/
theorem signConst_mono {l : V →ₗ[ℚ] ℚ} {A C : Set V} (h : SignConst l C) (hAC : A ⊆ C) : SignConst l A := by
  rcases h with h | h | h
  · exact Or.inl fun x hx => h x (hAC hx)
  · exact Or.inr (Or.inl fun x hx => h x (hAC hx))
  · exact Or.inr (Or.inr fun x hx => h x (hAC hx))

/- English proof (translation)
Break down `h with h | h | h` into its components or cases. Rewrite using `[h x hx, h y hy]`. Rewrite using `[sign_pos (h x hx), sign_pos (h y hy)]`. Rewrite using `[sign_neg (h x hx), sign_neg (h y hy)]`.
-/
theorem sign_eq_of_signConst {l : V →ₗ[ℚ] ℚ} {A : Set V} (h : SignConst l A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    SignType.sign (l x) = SignType.sign (l y) := by
  rcases h with h | h | h
  · rw [h x hx, h y hy]
  · rw [sign_pos (h x hx), sign_pos (h y hy)]
  · rw [sign_neg (h x hx), sign_neg (h y hy)]

/- English proof (translation)
Take `⟨t, rfl⟩` from `hΛ.exists_finset_coe`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Conclude with `.cone s hli hP ⟨subset_rfl, fun l hl => by simp at hl⟩`. Introduce `l t _ ih`. Use `tile_refine (fun u hu huP hQu => ?_) ih` and prove the remaining obligations.

Use `tile_mono (fun A hA => ⟨hA.2.trans hQu.1, fun l' hl' => ?_⟩) (tile_inside (GlobalTheory.T.simplicial_cone_tiles_sign P l u hu huP))` and prove the remaining obligations. Break down `Finset.mem_insert.1 (Finset.mem_coe.1 hl') with rfl | h'` into its components or cases. Conclude with `hA.1`. Conclude with `signConst_mono (hQu.2 l' (Finset.mem_coe.2 h')) hA.2`.
-/
theorem tile_signs (P : ConvexCone ℚ V) (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V))
    (hP : (s : Set V) ⊆ (P : Set V)) (Λ : Set (V →ₗ[ℚ] ℚ)) (hΛ : Λ.Finite) :
    Tile (P : Set V) (fun A => A ⊆ coneOn s ∧ ∀ l ∈ Λ, SignConst l A) (coneOn s) := by
  classical
  obtain ⟨t, rfl⟩ := hΛ.exists_finset_coe
  refine Finset.induction_on t ?_ ?_
  · exact .cone s hli hP ⟨subset_rfl, fun l hl => by simp at hl⟩
  · intro l t _ ih
    refine tile_refine (fun u hu huP hQu => ?_) ih
    refine tile_mono (fun A hA => ⟨hA.2.trans hQu.1, fun l' hl' => ?_⟩)
      (tile_inside (GlobalTheory.T.simplicial_cone_tiles_sign P l u hu huP))
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hl') with rfl | h'
    · exact hA.1
    · exact signConst_mono (hQu.2 l' (Finset.mem_coe.2 h')) hA.2

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `empty`. Rewrite using `[Set.empty_inter]`. Conclude with `.empty`. Consider the case `cone s hli hP hQs`.

Break down `hQs with hs | hs` into its components or cases. Rewrite using `[Set.inter_eq_left.2 hs]`. Conclude with `.cone s hli hP trivial`. Rewrite using `[Set.disjoint_iff_inter_eq_empty.1 hs]`. Conclude with `.empty`.

Consider the case `union _ _ hAB ihA ihB`. Rewrite using `[Set.union_inter_distrib_right]`. Conclude with `.union ihA ihB (hAB.mono Set.inter_subset_left Set.inter_subset_left)`.
-/
theorem tile_inter {P E C : Set V} (h : Tile P (fun A => A ⊆ E ∨ Disjoint A E) C) :
    Tile P (fun _ => True) (C ∩ E) := by
  induction h with
  | empty =>
    rw [Set.empty_inter]
    exact .empty
  | cone s hli hP hQs =>
    rcases hQs with hs | hs
    · rw [Set.inter_eq_left.2 hs]
      exact .cone s hli hP trivial
    · rw [Set.disjoint_iff_inter_eq_empty.1 hs]
      exact .empty
  | union _ _ hAB ihA ihB =>
    rw [Set.union_inter_distrib_right]
    exact .union ihA ihB (hAB.mono Set.inter_subset_left Set.inter_subset_left)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩ i`. Rewrite using `[Finset.sum_image (fun a _ c _ hac => b.injective hac)]`. Establish `hrep : b.repr (∑ j, t (b j) • b j) i = t (b i)`. Simplify using `only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.finsetSum_apply]`.

Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Finsupp.single_apply, if_pos rfl]`. Introduce `j _ hji`. Rewrite using `[Finsupp.single_apply, if_neg hji]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[hrep]`. Conclude with `ht _ (Finset.mem_image_of_mem b (Finset.mem_univ i))`. Introduce `hx`. Establish `key : ∀ i, ∑ j, b.repr (b i) j * b.repr x j = b.repr x i`.

Introduce `i`. Rewrite using `[Module.Basis.repr_self, Finset.sum_eq_single i]`. Rewrite using `[Finsupp.single_apply, if_pos rfl, one_mul]`. Introduce `j _ hji`. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hji), zero_mul]`.

Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Use `⟨fun v => ∑ j, b.repr v j * b.repr x j, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`.

Use `show 0 < ∑ j, b.repr (b i) j * b.repr x j`. Rewrite using `[key]`. Conclude with `hx i`. Rewrite using `[Finset.sum_image (fun a _ c _ hac => b.injective hac)] conv_lhs => rw [← b.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `show b.repr x i • b i = (∑ j, b.repr (b i) j * b.repr x j) • b i`. Rewrite using `[key]`.
-/
theorem mem_coneOn_basis [DecidableEq V] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ V) (x : V) :
    x ∈ coneOn (Finset.univ.image b) ↔ ∀ i, 0 < b.repr x i := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
    have hrep : b.repr (∑ j, t (b j) • b j) i = t (b i) := by
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hrep]
    exact ht _ (Finset.mem_image_of_mem b (Finset.mem_univ i))
  · intro hx
    have key : ∀ i, ∑ j, b.repr (b i) j * b.repr x j = b.repr x i := by
      intro i
      rw [Module.Basis.repr_self, Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl, one_mul]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg (Ne.symm hji), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    refine ⟨fun v => ∑ j, b.repr v j * b.repr x j, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      show 0 < ∑ j, b.repr (b i) j * b.repr x j
      rw [key]
      exact hx i
    · rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      show b.repr x i • b i = (∑ j, b.repr (b i) j * b.repr x j) • b i
      rw [key]

/- English proof (translation)
Introduce `V _ _ κ _ P b hb Λ hΛ E hE hdec`. Establish `hcoe : ((Finset.univ.image b : Finset V) : Set V) = Set.range b`. Simplify using `[Set.image_univ]`. Establish `hli : LinearIndepOn ℚ id ((Finset.univ.image b : Finset V) : Set V)`. Rewrite using `[hcoe]`.

Conclude with `(linearIndepOn_id_range_iff b.injective).2 b.linearIndependent`. Establish `hP' : ((Finset.univ.image b : Finset V) : Set V) ⊆ (P : Set V)`. Rewrite using `[hcoe]`. Introduce and unpack `v ⟨i, rfl⟩`. Conclude with `hb i`.

Establish `hT` using `tile_inter (tile_mono (Q' := fun A => A ⊆ E ∨ Disjoint A E) (fun A hA => ?_) (tile_signs P _ hli hP' Λ hΛ))`. Establish `hEs : coneOn (Finset.univ.image b) ∩ E = E` using `Set.inter_eq_right.2 fun x hx => (mem_coneOn_basis b x).2 (hE x hx)`. Rewrite `hT` using `[hEs]`. Conclude with `hT`. Take `⟨hAs, hAl⟩` from `hA`.

Distinguish the cases in `hex : ∃ x ∈ A, x ∈ E`. Use `left`. Take `⟨x, hxA, hxE⟩` from `hex`. Introduce `y hyA`. Conclude with `hdec x y ((mem_coneOn_basis b x).1 (hAs hxA)) ((mem_coneOn_basis b y).1 (hAs hyA)) (fun l hl => sign_eq_of_signConst (hAl l hl) hxA hyA) hxE`.

Use `right`. Conclude with `Set.disjoint_left.2 fun x hxA hxE => hex ⟨x, hxA, hxE⟩`.
-/
theorem tile_of_signs : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  classical
  intro V _ _ κ _ P b hb Λ hΛ E hE hdec
  have hcoe : ((Finset.univ.image b : Finset V) : Set V) = Set.range b := by
    simp [Set.image_univ]
  have hli : LinearIndepOn ℚ id ((Finset.univ.image b : Finset V) : Set V) := by
    rw [hcoe]
    exact (linearIndepOn_id_range_iff b.injective).2 b.linearIndependent
  have hP' : ((Finset.univ.image b : Finset V) : Set V) ⊆ (P : Set V) := by
    rw [hcoe]
    rintro v ⟨i, rfl⟩
    exact hb i
  have hT := tile_inter (tile_mono (Q' := fun A => A ⊆ E ∨ Disjoint A E) (fun A hA => ?_)
    (tile_signs P _ hli hP' Λ hΛ))
  · have hEs : coneOn (Finset.univ.image b) ∩ E = E :=
      Set.inter_eq_right.2 fun x hx => (mem_coneOn_basis b x).2 (hE x hx)
    rw [hEs] at hT
    exact hT
  · obtain ⟨hAs, hAl⟩ := hA
    by_cases hex : ∃ x ∈ A, x ∈ E
    · left
      obtain ⟨x, hxA, hxE⟩ := hex
      intro y hyA
      exact hdec x y ((mem_coneOn_basis b x).1 (hAs hxA)) ((mem_coneOn_basis b y).1 (hAs hyA))
        (fun l hl => sign_eq_of_signConst (hAl l hl) hxA hyA) hxE
    · right
      exact Set.disjoint_left.2 fun x hxA hxE => hex ⟨x, hxA, hxE⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles
