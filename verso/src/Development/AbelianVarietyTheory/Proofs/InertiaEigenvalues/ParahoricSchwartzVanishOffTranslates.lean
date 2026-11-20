import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubsetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHyperplaneResidueOutsideTranslatesStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r t ϖ hϖ Φ N hsupp h2 h3 x hx`. Assume the negation of the conclusion as `hnot`. Take `⟨z, hz⟩` from `hsupp x hx`. Establish `hc0 : algebraMap O K (ϖ ^ N) ≠ 0`. Rewrite using `[Ne, (IsFractionRing.injective O K).eq_iff' (map_zero _)]`.

Conclude with `pow_ne_zero _ hϖ.ne_zero`. Establish `hzn : ¬ ∃ (g : GL (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), z.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K)`. Introduce and unpack `⟨g, w, hw⟩`. Apply `hnot` to reduce the goal to its premises. Use `⟨Units.mk0 _ hc0 • g, w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hw, ← hz]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`. Take `⟨a, ha, hcore⟩` from `GlobalTheory.T.exists_hyperplane_residue_outside_translates O K r t ϖ hϖ z hzn`. Establish `hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))`. Introduce `g`.

Establish `hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) i j` using `fun i j => IsLocalRing.residue_surjective _`. Use `choose L hL using hs'`. Conclude with `⟨Matrix.of L, by ext i j; exact hL i j⟩`. Use `choose lift hlift using hsurj`. Establish `hs` using `h3 a ha lift hlift x`.

Use `set G := {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v} with hG`. Establish `hfix : ∀ g ∈ G, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = Φ x`. Introduce `g hg`. Take `⟨h, hh1, hh2, hh3⟩` from `hcore g hg (lift g) (hlift g)`. Rewrite using `[← h2 h hh1 hh2]`.

Use `congr 1`. Establish `e1` using `congrArg (fun m : Matrix (Fin r ⊕ Fin t) (Fin r) O => m.map (algebraMap O K)) hh3`. Simplify using `only [Matrix.map_mul] at e1`. Rewrite `e1` using `[← hz]`. Rewrite `e1` using `[Matrix.mul_smul, Matrix.mul_smul]`.

Conclude with `smul_right_injective _ hc0 e1`. Rewrite `hs` using `[finsum_mem_congr rfl hfix]`. Establish `hGfin : G.Finite` using `Set.toFinite G`. Rewrite `hs` using `[finsum_mem_eq_finite_toFinset_sum _ hGfin, Finset.sum_const]`. Establish `h1 : (1 : GL (Fin r) (IsLocalRing.ResidueField O)) ∈ hGfin.toFinset`.

Rewrite using `[Set.Finite.mem_toFinset]`. Introduce `v _`. Simplify using the standard rewrite rules. Establish `hcard : hGfin.toFinset.card ≠ 0` using `Finset.card_ne_zero.2 ⟨_, h1⟩`. Rewrite `hs` using `[nsmul_eq_mul]`.

Conclude with `hx ((mul_eq_zero.1 hs).resolve_left (by exact_mod_cast hcard))`.
-/
theorem parahoric_schwartz_vanish_off_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) (N : ℕ), (∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ x ≠ 0 → ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ N hsupp h2 h3 x hx
  classical
  by_contra hnot
  obtain ⟨z, hz⟩ := hsupp x hx
  have hc0 : algebraMap O K (ϖ ^ N) ≠ 0 := by
    rw [Ne, (IsFractionRing.injective O K).eq_iff' (map_zero _)]
    exact pow_ne_zero _ hϖ.ne_zero
  have hzn : ¬ ∃ (g : GL (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), z.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) := by
    rintro ⟨g, w, hw⟩
    apply hnot
    refine ⟨Units.mk0 _ hc0 • g, w, ?_⟩
    rw [← hw, ← hz]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨a, ha, hcore⟩ := GlobalTheory.T.exists_hyperplane_residue_outside_translates O K r t ϖ hϖ z hzn
  have hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) := by
    intro g
    have hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) i j :=
      fun i j => IsLocalRing.residue_surjective _
    choose L hL using hs'
    exact ⟨Matrix.of L, by ext i j; exact hL i j⟩
  choose lift hlift using hsurj
  have hs := h3 a ha lift hlift x
  set G := {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v} with hG
  have hfix : ∀ g ∈ G, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = Φ x := by
    intro g hg
    obtain ⟨h, hh1, hh2, hh3⟩ := hcore g hg (lift g) (hlift g)
    rw [← h2 h hh1 hh2]
    congr 1
    have e1 := congrArg (fun m : Matrix (Fin r ⊕ Fin t) (Fin r) O => m.map (algebraMap O K)) hh3
    simp only [Matrix.map_mul] at e1
    rw [← hz] at e1
    rw [Matrix.mul_smul, Matrix.mul_smul] at e1
    exact smul_right_injective _ hc0 e1
  rw [finsum_mem_congr rfl hfix] at hs
  have hGfin : G.Finite := Set.toFinite G
  rw [finsum_mem_eq_finite_toFinset_sum _ hGfin, Finset.sum_const] at hs
  have h1 : (1 : GL (Fin r) (IsLocalRing.ResidueField O)) ∈ hGfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; intro v _; simp
  have hcard : hGfin.toFinset.card ≠ 0 := Finset.card_ne_zero.2 ⟨_, h1⟩
  rw [nsmul_eq_mul] at hs
  exact hx ((mul_eq_zero.1 hs).resolve_left (by exact_mod_cast hcard))

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r t ϖ hϖ Φ ⟨N, hinv, hsupp⟩ h2 h3`. Take `⟨T, hT⟩` from `GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N`. Establish `hΩ` using `GlobalTheory.parahoric_schwartz_vanish_off_translates O K r t ϖ hϖ Φ N hsupp h2 h3`. Use `set S : GL (Fin r) K → Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) := fun g => {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)} with hS`. Establish `hconst : ∀ g x x', x ∈ S g → x' ∈ S g → Φ x = Φ x'`.

Introduce and unpack `g x x' ⟨z, hz⟩ ⟨z', hz'⟩`. Rewrite using `[GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x g z hz, GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x' g z' hz']`. Establish `huniq : ∀ g g' x, x ∈ S g → x ∈ S g' → S g = S g'`. Introduce and unpack `g g' x ⟨z, hz⟩ ⟨z', hz'⟩`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Conclude with `GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw`. Introduce and unpack `⟨w, hw⟩`. Conclude with `GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw`.

Set `gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K` to `fun y => if h : Φ y ≠ 0 then (hΩ y h).choose else 1`. Establish `hgs : ∀ y, Φ y ≠ 0 → y ∈ S (gs y)`. Introduce `y hy`. Simplify using `only [gs, dif_pos hy]`. Conclude with `(hΩ y hy).choose_spec`.

Set `F : Finset (Set (Matrix (Fin r ⊕ Fin t) (Fin r) K))` to `(T.filter (fun y => Φ y ≠ 0)).image (fun y => S (gs y))`. Establish `hcover : ∀ x, Φ x ≠ 0 → ∃ A ∈ F, x ∈ A`. Introduce `x hx`. Take `⟨z, hz⟩` from `hsupp x hx`. Take `⟨y, hyT, z', rfl⟩` from `hT x z hz`.

Establish `hy : Φ y ≠ 0` using `by rwa [hinv] at hx`. Use `⟨S (gs y), Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hyT, hy⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨z₀, hz₀⟩` from `hgs y hy`. Conclude with `GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ _ (by rwa [hinv])) z'`. Establish `hF : ∀ A ∈ F, ∃ g, A = S g`.

Introduce `A hA`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hA`. Conclude with `⟨_, rfl⟩`. Set `c : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → ℂ` to `fun A => if h : A.Nonempty then Φ h.some else 0`. Establish `hc : ∀ A ∈ F, ∀ x ∈ A, c A = Φ x`.

Introduce `A hA x hx`. Take `⟨g, rfl⟩` from `hF A hA`. Establish `hne : (S g).Nonempty` using `⟨x, hx⟩`. Simplify using `only [c, dif_pos hne]`. Conclude with `hconst g _ _ hne.some_mem hx`.

Establish `heq : Φ = ∑ A ∈ F, c A • A.indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hx : Φ x = 0`.

Rewrite using `[hx]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `A hA`. Use `split_ifs with h`.

Rewrite using `[hc A hA x h, hx]`. Both sides reduce to the same expression. Take `⟨A, hA, hxA⟩` from `hcover x hx`. Rewrite using `[Finset.sum_eq_single A]`. Rewrite using `[if_pos hxA, hc A hA x hxA]`.

Introduce `B hB hBA`. Rewrite using `[if_neg]`. Introduce `hxB`. Take `⟨g, rfl⟩` from `hF A hA`. Take `⟨g', rfl⟩` from `hF B hB`.

Conclude with `hBA (huniq g' g x hxB hxA)`. Introduce `h`. Conclude with `absurd hA h`. Rewrite using `[heq]`. Use `Submodule.sum_mem _ fun A hA => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `hF A hA`. Conclude with `⟨g, rfl⟩`.
-/
theorem parahoric_schwartz_mem_span_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ, (∃ N : ℕ, (∀ x (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ (x + (ϖ ^ N • z).map (algebraMap O K)) = Φ x) ∧ ∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → Φ ∈ Submodule.span ℂ {Ψ | ∃ g : GL (Fin r) K, Ψ = Set.indicator {x : Matrix (Fin r ⊕ Fin t) (Fin r) K | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)} (fun _ => (1 : ℂ))} := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ ⟨N, hinv, hsupp⟩ h2 h3
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N
  have hΩ := GlobalTheory.parahoric_schwartz_vanish_off_translates O K r t ϖ hϖ Φ N hsupp h2 h3
  set S : GL (Fin r) K → Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) := fun g =>
    {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)} with hS
  have hconst : ∀ g x x', x ∈ S g → x' ∈ S g → Φ x = Φ x' := by
    rintro g x x' ⟨z, hz⟩ ⟨z', hz'⟩
    rw [GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x g z hz, GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x' g z' hz']
  have huniq : ∀ g g' x, x ∈ S g → x ∈ S g' → S g = S g' := by
    rintro g g' x ⟨z, hz⟩ ⟨z', hz'⟩
    ext y; constructor
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw
  let gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K := fun y =>
    if h : Φ y ≠ 0 then (hΩ y h).choose else 1
  have hgs : ∀ y, Φ y ≠ 0 → y ∈ S (gs y) := by
    intro y hy
    simp only [gs, dif_pos hy]
    exact (hΩ y hy).choose_spec
  let F : Finset (Set (Matrix (Fin r ⊕ Fin t) (Fin r) K)) :=
    (T.filter (fun y => Φ y ≠ 0)).image (fun y => S (gs y))
  have hcover : ∀ x, Φ x ≠ 0 → ∃ A ∈ F, x ∈ A := by
    intro x hx
    obtain ⟨z, hz⟩ := hsupp x hx
    obtain ⟨y, hyT, z', rfl⟩ := hT x z hz
    have hy : Φ y ≠ 0 := by rwa [hinv] at hx
    refine ⟨S (gs y), Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hyT, hy⟩, rfl⟩, ?_⟩
    obtain ⟨z₀, hz₀⟩ := hgs y hy
    exact GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ _ (by rwa [hinv])) z'
  have hF : ∀ A ∈ F, ∃ g, A = S g := by
    intro A hA
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hA
    exact ⟨_, rfl⟩
  let c : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → ℂ := fun A => if h : A.Nonempty then Φ h.some else 0
  have hc : ∀ A ∈ F, ∀ x ∈ A, c A = Φ x := by
    intro A hA x hx
    obtain ⟨g, rfl⟩ := hF A hA
    have hne : (S g).Nonempty := ⟨x, hx⟩
    simp only [c, dif_pos hne]
    exact hconst g _ _ hne.some_mem hx
  have heq : Φ = ∑ A ∈ F, c A • A.indicator (fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hx : Φ x = 0
    · rw [hx]; symm
      apply Finset.sum_eq_zero
      intro A hA
      split_ifs with h
      · rw [hc A hA x h, hx]
      · rfl
    · obtain ⟨A, hA, hxA⟩ := hcover x hx
      rw [Finset.sum_eq_single A]
      · rw [if_pos hxA, hc A hA x hxA]
      · intro B hB hBA
        rw [if_neg]
        intro hxB
        obtain ⟨g, rfl⟩ := hF A hA
        obtain ⟨g', rfl⟩ := hF B hB
        exact hBA (huniq g' g x hxB hxA)
      · intro h; exact absurd hA h
  rw [heq]
  refine Submodule.sum_mem _ fun A hA => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨g, rfl⟩ := hF A hA
  exact ⟨g, rfl⟩

end GlobalTheory
