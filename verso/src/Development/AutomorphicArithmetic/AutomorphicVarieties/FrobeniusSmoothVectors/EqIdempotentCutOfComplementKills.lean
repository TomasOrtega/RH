import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Introduce `x hx`. Simplify using `only [List.sum_cons] at hs`.

Establish `ha : a ≤ 0` using `h a (by simp)`. Establish `hL : ∀ x ∈ L, x ≤ 0` using `fun x hx => h x (by simp [hx])`. Establish `hsL : L.sum ≤ 0` using `by clear ih hs hx`. Proceed by induction on `L with`. Consider the case `nil => simp`.

Consider the case `cons b L ih2`. Simplify using `only [List.sum_cons]`. Establish `hb : b ≤ 0` using `hL b (by simp)`. Apply the tactic sequence `have := ih2 (fun x hx => h x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [hx])) (fun x hx => hL x (by simp [hx]))`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `ih hL (by linarith) x hx`.
-/
private theorem list_forall_eq_zero_of_nonpos_of_sum_eq_zero (L : List ℤ) (h : ∀ x ∈ L, x ≤ 0) (hs : L.sum = 0) : ∀ x ∈ L, x = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro x hx
    simp only [List.sum_cons] at hs
    have ha : a ≤ 0 := h a (by simp)
    have hL : ∀ x ∈ L, x ≤ 0 := fun x hx => h x (by simp [hx])
    have hsL : L.sum ≤ 0 := by
      clear ih hs hx
      induction L with
      | nil => simp
      | cons b L ih2 =>
        simp only [List.sum_cons]
        have hb : b ≤ 0 := hL b (by simp)
        have := ih2 (fun x hx => h x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [hx])) (fun x hx => hL x (by simp [hx]))
        linarith
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih hL (by linarith) x hx

/- English proof (translation)
Rewrite `hji` using `[Fin.le_def]`. Unfold `w`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem w_sub_w_nonpos_of_le (n : ℕ) (i j : Fin n) (hji : j ≤ i) : w n i - w n j ≤ 0 := by
  rw [Fin.le_def] at hji
  unfold w
  split_ifs <;> omega

/- English proof (translation)
Unfold `w at h`. Apply `Fin.ext` to reduce the goal to its premises. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
private theorem eq_of_w_sub_w_eq_zero (n : ℕ) (i j : Fin n) (h : w n i - w n j = 0) : i = j := by
  unfold w at h
  apply Fin.ext
  split_ifs at h <;> omega

/- English proof (translation)
Introduce `l _ O _ _ F n S Q _ f φ hφ htri hbar z hz`. Establish `hrA : ∀ g i j, S.ρ.r g i j ∈ S.A` using `fun g i j => Algebra.subset_adjoin (Or.inr ⟨g, i, j, rfl⟩)`. Establish `hψA : ∀ v i g, ((S.ρ.ψ v i g : S.Rˣ) : S.R) ∈ S.A`. Introduce `v i g`. Apply `Algebra.subset_adjoin` to reduce the goal to its premises.

Use `left`. Use `show _ ∈ adicClosure _`. Introduce `N`. Conclude with `⟨_, Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩), by simp⟩`. Establish `hr' : ∀ g i j, (S.u.map φ).r g i j = φ ⟨S.ρ.r g i j, hrA g i j⟩` using `fun g i j => rfl`.

Establish `hψ' : ∀ v i g, (((S.u.map φ).ψ v i g : Qˣ) : Q) = φ ⟨_, hψA v i g⟩` using `fun v i g => rfl`. Establish `hzero : ∀ g i j, i < j → φ ⟨S.ρ.r g i j, hrA g i j⟩ = 0`. Introduce `g i j hij`. Establish `hm : (S.u.map φ).r g i j ∈ (S.u.map φ).triM` using `Ideal.subset_span ⟨g, i, j, hij, rfl⟩`. Rewrite `hm` using `[htri, Ideal.mem_bot]`.

Rewrite using `[← hr']`. Conclude with `hm`. Establish `hdiag : ∀ g i j, i = j → φ ⟨S.ρ.r g i j, hrA g i j⟩ ∈ f.range`. Introduce and unpack `g i j rfl`. Rewrite using `[← hr', hbar.1 g i]`.

Conclude with `⟨_, rfl⟩`. Establish `hψr : ∀ v i g, φ ⟨_, hψA v i g⟩ ∈ f.range`. Introduce `v i g`. Rewrite using `[← hψ', hbar.2 v i g]`. Conclude with `⟨_, rfl⟩`.

Establish `hDA : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ S.A`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)`. Apply `list_prod_mem` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨s, -, rfl⟩` from `List.mem_map.mp hy`. Conclude with `hrA _ _ _`. Conclude with `hψA v i g`. Establish `key : ∀ x (hx : x ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})), φ ⟨x, hDA hx⟩ ∈ f.range`. Introduce `x hx`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨L, hsum, rfl⟩ | ⟨v, i, g, rfl⟩` into its components or cases. Establish `e : (⟨(L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod, hDA (Algebra.subset_adjoin (Or.inl ⟨L, hsum, rfl⟩))⟩ : S.A) = (L.map fun s => (⟨S.ρ.r s.1 s.2.1 s.2.2, hrA _ _ _⟩ : S.A)).prod`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[List.map_map, Function.comp_def]`. Rewrite using `[e, map_list_prod, List.map_map]`. Distinguish the cases in `hex : ∃ s ∈ L, s.2.1 < s.2.2`. Take `⟨s, hs, hlt⟩` from `hex`. Rewrite using `[List.prod_eq_zero]`.

Conclude with `zero_mem _`. Conclude with `List.mem_map.mpr ⟨s, hs, hzero _ _ _ hlt⟩`. Use `push_neg at hex`. Establish `hterm` using `list_forall_eq_zero_of_nonpos_of_sum_eq_zero _ (fun x hx => by`. Take `⟨s, hs, rfl⟩` from `List.mem_map.mp hx`.

Conclude with `w_sub_w_nonpos_of_le n _ _ (hex s hs)) hsum`. Apply `list_prod_mem` to reduce the goal to its premises. Introduce `y hy`. Take `⟨s, hs, rfl⟩` from `List.mem_map.mp hy`. Conclude with `hdiag _ _ _ (eq_of_w_sub_w_eq_zero n _ _ (hterm _ (List.mem_map_of_mem hs)))`.

Conclude with `hψr v i g`. Consider the case `algebraMap r => show φ (algebraMap O S.A r) ∈ f.range`. Rewrite using `[hφ]`. Conclude with `⟨_, rfl⟩`. Consider the case `add x y hx hy ihx ihy => show φ (⟨x, hDA hx⟩ + ⟨y, hDA hy⟩) ∈ f.range`.

Rewrite using `[map_add]`. Conclude with `add_mem ihx ihy`. Consider the case `mul x y hx hy ihx ihy => show φ (⟨x, hDA hx⟩ * ⟨y, hDA hy⟩) ∈ f.range`. Rewrite using `[map_mul]`. Conclude with `mul_mem ihx ihy`.

Conclude with `key z hz`.
-/
theorem UpperTheory.V.Fr.adjoin_image_in_residue_range :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) {Q : Type} [CommRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ z : S.A, (z : S.R) ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) → φ z ∈ f.range := by
  intro l _ O _ _ F n S Q _ f φ hφ htri hbar z hz
  have hrA : ∀ g i j, S.ρ.r g i j ∈ S.A := fun g i j =>
    Algebra.subset_adjoin (Or.inr ⟨g, i, j, rfl⟩)
  have hψA : ∀ v i g, ((S.ρ.ψ v i g : S.Rˣ) : S.R) ∈ S.A := by
    intro v i g
    apply Algebra.subset_adjoin
    left
    show _ ∈ adicClosure _
    intro N
    exact ⟨_, Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩), by simp⟩
  have hr' : ∀ g i j, (S.u.map φ).r g i j = φ ⟨S.ρ.r g i j, hrA g i j⟩ := fun g i j => rfl
  have hψ' : ∀ v i g, (((S.u.map φ).ψ v i g : Qˣ) : Q) = φ ⟨_, hψA v i g⟩ := fun v i g => rfl
  have hzero : ∀ g i j, i < j → φ ⟨S.ρ.r g i j, hrA g i j⟩ = 0 := by
    intro g i j hij
    have hm : (S.u.map φ).r g i j ∈ (S.u.map φ).triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at hm
    rw [← hr']
    exact hm
  have hdiag : ∀ g i j, i = j → φ ⟨S.ρ.r g i j, hrA g i j⟩ ∈ f.range := by
    rintro g i j rfl
    rw [← hr', hbar.1 g i]
    exact ⟨_, rfl⟩
  have hψr : ∀ v i g, φ ⟨_, hψA v i g⟩ ∈ f.range := by
    intro v i g
    rw [← hψ', hbar.2 v i g]
    exact ⟨_, rfl⟩
  have hDA : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ S.A := by
    apply Algebra.adjoin_le
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · apply list_prod_mem
      intro y hy
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
      exact hrA _ _ _
    · exact hψA v i g
  have key : ∀ x (hx : x ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})),
      φ ⟨x, hDA hx⟩ ∈ f.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨L, hsum, rfl⟩ | ⟨v, i, g, rfl⟩
      · have e : (⟨(L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod, hDA (Algebra.subset_adjoin (Or.inl ⟨L, hsum, rfl⟩))⟩ : S.A) =
            (L.map fun s => (⟨S.ρ.r s.1 s.2.1 s.2.2, hrA _ _ _⟩ : S.A)).prod := by
          apply Subtype.ext
          simp [List.map_map, Function.comp_def]
        rw [e, map_list_prod, List.map_map]
        by_cases hex : ∃ s ∈ L, s.2.1 < s.2.2
        · obtain ⟨s, hs, hlt⟩ := hex
          rw [List.prod_eq_zero]
          · exact zero_mem _
          · exact List.mem_map.mpr ⟨s, hs, hzero _ _ _ hlt⟩
        · push_neg at hex
          have hterm := list_forall_eq_zero_of_nonpos_of_sum_eq_zero _ (fun x hx => by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
            exact w_sub_w_nonpos_of_le n _ _ (hex s hs)) hsum
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
          exact hdiag _ _ _ (eq_of_w_sub_w_eq_zero n _ _ (hterm _ (List.mem_map_of_mem hs)))
      · exact hψr v i g
    | algebraMap r =>
      show φ (algebraMap O S.A r) ∈ f.range
      rw [hφ]
      exact ⟨_, rfl⟩
    | add x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ + ⟨y, hDA hy⟩) ∈ f.range
      rw [map_add]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ * ⟨y, hDA hy⟩) ∈ f.range
      rw [map_mul]
      exact mul_mem ihx ihy
  exact key z hz
