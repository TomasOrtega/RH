import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.ClassFiniteOf

noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Simplify using `only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem herm_add_left (x x' y : Fin M → E) : herm σ J (x + x') y = herm σ J x y + herm σ J x' y := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem herm_add_right (x y y' : Fin M → E) : herm σ J x (y + y') = herm σ J x y + herm σ J x y' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul_left (a : E) (x y : Fin M → E) : herm σ J (a • x) y = σ a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul_right (a : E) (x y : Fin M → E) : herm σ J x (a • y) = a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_left (y : Fin M → E) : herm σ J 0 y = 0 := by
  simp [herm]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_right (x : Fin M → E) : herm σ J x 0 = 0 := by
  simp [herm]

/- English proof (translation)
Simplify using `only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_scale (D : E) (x y : Fin M → E) : herm σ (D • J) x y = D * herm σ J x y := by
  simp only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [herm]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Introduce `k _ hk`. Simplify using `[Pi.single_eq_of_ne hk]`.

Simplify using the standard rewrite rules.
-/
theorem herm_single_left (i : Fin M) (k : ℕ) (y : Fin M → E) :
    herm σ J (Pi.single i (k : E)) y = (k : E) * (J.mulVec y) i := by
  classical
  simp only [herm]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

variable [NumberField E]

/- English proof (translation)
Set `f : (Fin M → 𝓞 E) →ₗ[𝓞 E] (Fin M → E)` to `LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)`. Set `sc : (Fin M → E) →ₗ[𝓞 E] (Fin M → E)` to `(d : 𝓞 E) • LinearMap.id`. Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hsc : ∀ y : Fin M → E, ∀ j, sc y j = (d : E) * y j`. Introduce `y j`.

Simplify using `[sc, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`. Establish `hinj : Function.Injective sc`. Introduce `x y hxy`. Use function extensionality and compare the values at `j`. Use `congrFun hxy j` as an intermediate fact.

Rewrite `this` using `[hsc, hsc]`. Conclude with `mul_left_cancel₀ hd' this`. Establish `hle : N.map sc ≤ LinearMap.range f`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨fun j => ⟨(d : E) * y j, h y hy j⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Rewrite using `[hsc]`. Both sides reduce to the same expression. Establish `hfg : (N.map sc).FG`. Rewrite using `[← Submodule.map_comap_eq_of_le hle]`.

Conclude with `(IsNoetherian.noetherian _).map f`. Conclude with `Submodule.fg_of_fg_map_injective sc hinj hfg`.
-/
theorem fg_of_den (N : Submodule (𝓞 E) (Fin M → E)) (d : ℕ) (hd : 0 < d)
    (h : ∀ y ∈ N, ∀ j, IsIntegral ℤ ((d : E) * y j)) : N.FG := by
  classical

  let f : (Fin M → 𝓞 E) →ₗ[𝓞 E] (Fin M → E) :=
    LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  let sc : (Fin M → E) →ₗ[𝓞 E] (Fin M → E) := (d : 𝓞 E) • LinearMap.id
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hsc : ∀ y : Fin M → E, ∀ j, sc y j = (d : E) * y j := by
    intro y j
    simp [sc, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hinj : Function.Injective sc := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    rw [hsc, hsc] at this
    exact mul_left_cancel₀ hd' this
  have hle : N.map sc ≤ LinearMap.range f := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun j => ⟨(d : E) * y j, h y hy j⟩, ?_⟩
    funext j
    rw [hsc]
    rfl
  have hfg : (N.map sc).FG := by
    rw [← Submodule.map_comap_eq_of_le hle]
    exact (IsNoetherian.noetherian _).map f
  exact Submodule.fg_of_fg_map_injective sc hinj hfg

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN`. Use `haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N`. Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := ℤ) (M := N)`. Set `rep : (S → Fin n) → (Fin M → E)` to `fun c => ∑ g : S, ((c g : ℕ) : ℤ) • ((g : N) : Fin M → E)`. Set `T : Set (Fin M → E)` to `Set.range rep`.

Establish `hT : T.Finite` using `Set.finite_range rep`. Establish `hnZ : (0 : ℤ) < n` using `by exact_mod_cast hn`. Establish `hdec : ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x = t + (n : E) • z`. Introduce `x hx`. Establish `hmem : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (S : Set N)` using `by rw [hS]; trivial`.

Take `⟨a, -, ha⟩` from `Submodule.mem_span_finset.1 hmem`. Establish `hx' : x = ∑ g ∈ S, a g • ((g : N) : Fin M → E)`. Use `congrArg Subtype.val ha` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `using this.symm`.

Set `c : S → Fin n` to `fun g => ⟨(a g % n).toNat, by`. Establish `h1` using `Int.emod_nonneg (a g) hnZ.ne'`. Establish `h2` using `Int.emod_lt_of_pos (a g) hnZ`. Use the proof step `omega⟩`. Use `⟨rep c, ⟨c, rfl⟩, ∑ g ∈ S, (a g / n) • ((g : N) : Fin M → E), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ g.2`. Establish `hc : ∀ g : S, (((c g : ℕ) : ℤ)) = a g % n` using `fun g => by`. Simplify using `only [c]`. Conclude with `Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')`. Simplify using `only [rep, hc]`.

Rewrite using `[Finset.sum_coe_sort S (fun g => (a g % (n : ℤ)) • ((g : N) : Fin M → E)), hx', Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul E, smul_comm ((n : E)) _ _, ← Int.cast_smul_eq_zsmul E (a g / n), smul_smul, ← Int.cast_smul_eq_zsmul E (a g % n), ← add_smul]`. Use `congr 1`. Establish `h2 : ((a g : ℤ) : E) = ((a g % n : ℤ) : E) + (n : E) * ((a g / n : ℤ) : E)`.

Establish `hdm : a g % (n : ℤ) + (n : ℤ) * (a g / n) = a g` using `by first`. Consider the case `exact Int.emod_add_ediv _ _`. Consider the case `exact Int.emod_add_ediv' _ _`. Consider the case `(rw [Int.emod_def]; ring)`. Consider the case `exact EuclideanDomain.mod_add_div _ _`.

Use `congrArg (fun q : ℤ => (q : E)) hdm` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ s s' : Set (Fin M → E), s ∈ {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s' ∈ {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ …`. Introduce and unpack `s s' ⟨⟨G, hG⟩, hns, hsN⟩ ⟨⟨G', hG'⟩, hns', -⟩ heq x hx`. Take `⟨t, ht, z, hz, rfl⟩` from `hdec x (hsN hx)`. Rewrite `hx`, `hns` using `[← hG]`. Rewrite `hns'`, the goal using `[← hG']`.

Establish `hts : t ∈ G`. Use `G.sub_mem hx (hns z hz)` as an intermediate fact. Simplify using `using this`. Establish `hts' : t ∈ s' ∩ T` using `heq ▸ ⟨(show t ∈ s by rw [← hG]; exact hts), ht⟩`. Rewrite `hts'` using `[← hG']`.

Conclude with `G'.add_mem hts'.1 (hns' z hz)`. Use `Set.Finite.of_finite_image (f := fun s => s ∩ T) ?_ ?_` and prove the remaining obligations. Use `(hT.finite_subsets).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, -, rfl⟩`. Conclude with `Set.inter_subset_right`.

Introduce `s hs s' hs' heq`. Conclude with `Set.Subset.antisymm (key s s' hs hs' heq) (key s' s hs' hs heq.symm)`.
-/
theorem sub_finite (N : Submodule (𝓞 E) (Fin M → E)) (hN : N.FG) (n : ℕ) (hn : 0 < n) :
    {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
      (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N}.Finite := by
  classical
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := N)

  let rep : (S → Fin n) → (Fin M → E) := fun c => ∑ g : S, ((c g : ℕ) : ℤ) • ((g : N) : Fin M → E)
  let T : Set (Fin M → E) := Set.range rep
  have hT : T.Finite := Set.finite_range rep
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hdec : ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x = t + (n : E) • z := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (S : Set N) := by rw [hS]; trivial
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hmem
    have hx' : x = ∑ g ∈ S, a g • ((g : N) : Fin M → E) := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    let c : S → Fin n := fun g => ⟨(a g % n).toNat, by
      have h1 := Int.emod_nonneg (a g) hnZ.ne'
      have h2 := Int.emod_lt_of_pos (a g) hnZ
      omega⟩
    refine ⟨rep c, ⟨c, rfl⟩, ∑ g ∈ S, (a g / n) • ((g : N) : Fin M → E), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ g.2
    · have hc : ∀ g : S, (((c g : ℕ) : ℤ)) = a g % n := fun g => by
        simp only [c]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')
      simp only [rep, hc]
      rw [Finset.sum_coe_sort S (fun g => (a g % (n : ℤ)) • ((g : N) : Fin M → E)), hx',
        Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Int.cast_smul_eq_zsmul E, smul_comm ((n : E)) _ _, ← Int.cast_smul_eq_zsmul E (a g / n),
        smul_smul, ← Int.cast_smul_eq_zsmul E (a g % n), ← add_smul]
      congr 1
      have h2 : ((a g : ℤ) : E) = ((a g % n : ℤ) : E) + (n : E) * ((a g / n : ℤ) : E) := by
        have hdm : a g % (n : ℤ) + (n : ℤ) * (a g / n) = a g := by
          first
            | exact Int.emod_add_ediv _ _
            | exact Int.emod_add_ediv' _ _
            | (rw [Int.emod_def]; ring)
            | exact EuclideanDomain.mod_add_div _ _
        have := congrArg (fun q : ℤ => (q : E)) hdm
        push_cast at this
        rw [this]
      rw [h2]
      ring

  have key : ∀ s s' : Set (Fin M → E), s ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s' ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s ∩ T = s' ∩ T → s ⊆ s' := by
    rintro s s' ⟨⟨G, hG⟩, hns, hsN⟩ ⟨⟨G', hG'⟩, hns', -⟩ heq x hx
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x (hsN hx)
    rw [← hG] at hx hns
    rw [← hG'] at hns' ⊢
    have hts : t ∈ G := by
      have := G.sub_mem hx (hns z hz)
      simpa using this
    have hts' : t ∈ s' ∩ T := heq ▸ ⟨(show t ∈ s by rw [← hG]; exact hts), ht⟩
    rw [← hG'] at hts'
    exact G'.add_mem hts'.1 (hns' z hz)
  refine Set.Finite.of_finite_image (f := fun s => s ∩ T) ?_ ?_
  · refine (hT.finite_subsets).subset ?_
    rintro _ ⟨s, -, rfl⟩
    exact Set.inter_subset_right
  · intro s hs s' hs' heq
    exact Set.Subset.antisymm (key s s' hs hs' heq) (key s' s hs' hs heq.symm)

end PI.UnitaryGroupMassFormula.UJClassFin
