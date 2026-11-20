import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N`. Set `P : Til O O' B → Prop` to `fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N`. Establish `Pmem : ∀ x ∈ Algebra.adjoin O' S', P x` using `fun x hx => ⟨x, hx, by simp⟩`. Establish `Padd : ∀ x y, P x → P y → P (x + y)`. Introduce and unpack `x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩`.

Use `⟨a + b, add_mem ha hb, ?_⟩` and prove the remaining obligations. Establish `: x + y - (a + b) = (x - a) + (y - b)` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem hx hy`. Establish `Pmul : ∀ x y, P x → P y → P (x * y)`.

Introduce and unpack `x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩`. Use `⟨a * b, mul_mem ha hb, ?_⟩` and prove the remaining obligations. Establish `: x * y - a * b = x * (y - b) + (x - a) * b` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)`.

Establish `hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S'`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin (hS x hx)`. Consider the case `algebraMap r => rw [Til.ι_algebraMap]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`.

Establish `hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N`. Rewrite using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ N` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Conclude with `map_nonunit (Til.ι O O' B) x hx`. Establish `Pι : ∀ b, P (Til.ι O O' B b)`. Introduce `b`. Take `⟨a, ha, hb⟩` from `hgen N b`. Use `⟨_, hadj a ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_sub]`. Conclude with `hmap (Ideal.mem_map_of_mem _ hb)`. Establish `PC : ∀ t, P (Til.C O O' B t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => rw [map_zero]`. Conclude with `Pmem _ (zero_mem _)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Padd _ _ hx hy`. Consider the case `tmul o b`.

Establish `h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o)` using `PowerSeries.algebraMap_apply`. Establish `e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b`. Rewrite using `[h]`. Use `show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)`. Rewrite using `[← map_mul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)`. Establish `hsA : Til.s O O' B ∈ Algebra.adjoin O' S'` using `Algebra.subset_adjoin hsS`.

Establish `hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c` using `fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩`. Establish `key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h`. Introduce `k f`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩`.

Consider the case `succ k ih`. Take `⟨g, h, hg, e⟩` from `ih`. Take `⟨h', c, e'⟩` from `hdec h`. Use `⟨g + Til.s O O' B ^ k * Til.C O O' B c, h', Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩` and prove the remaining obligations. Rewrite using `[e, e']`.

Expand and normalize the polynomial expressions, which then agree. Introduce `f`. Take `⟨g, h, hg, e⟩` from `key N f`. Rewrite using `[e]`. Use `Padd _ _ hg ⟨0, zero_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_zero]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)`.
-/
theorem UpperTheory.V.Pa.BC.gen_bc :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (S : Set B) (S' : Set (Til O O' B)), IsLocalHom (Til.ι O O' B) → Til.s O O' B ∈ maximalIdeal (Til O O' B) → (∀ a ∈ S, Til.ι O O' B a ∈ S') → Til.s O O' B ∈ S' → GenBy O S → GenBy O' S' := by
  intro O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N
  let P : Til O O' B → Prop := fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N
  have Pmem : ∀ x ∈ Algebra.adjoin O' S', P x := fun x hx => ⟨x, hx, by simp⟩
  have Padd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [this]
    exact add_mem hx hy
  have Pmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : x * y - a * b = x * (y - b) + (x - a) * b := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)
  have hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hS x hx)
    | algebraMap r => rw [Til.ι_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (Til.ι O O' B) x hx
  have Pι : ∀ b, P (Til.ι O O' B b) := by
    intro b
    obtain ⟨a, ha, hb⟩ := hgen N b
    refine ⟨_, hadj a ha, ?_⟩
    rw [← map_sub]
    exact hmap (Ideal.mem_map_of_mem _ hb)
  have PC : ∀ t, P (Til.C O O' B t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Pmem _ (zero_mem _)
    | add x y hx hy => rw [map_add]; exact Padd _ _ hx hy
    | tmul o b =>
      have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
        PowerSeries.algebraMap_apply
      have e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b := by
        rw [h]
        show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)
        rw [← map_mul]
        congr 1
        simp
      rw [e]
      exact Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)
  have hsA : Til.s O O' B ∈ Algebra.adjoin O' S' := Algebra.subset_adjoin hsS
  have hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c :=
    fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩
  have key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h := by
    intro k f
    induction k with
    | zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩
    | succ k ih =>
      obtain ⟨g, h, hg, e⟩ := ih
      obtain ⟨h', c, e'⟩ := hdec h
      refine ⟨g + Til.s O O' B ^ k * Til.C O O' B c, h',
        Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩
      rw [e, e']
      ring
  intro f
  obtain ⟨g, h, hg, e⟩ := key N f
  rw [e]
  refine Padd _ _ hg ⟨0, zero_mem _, ?_⟩
  rw [sub_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)
