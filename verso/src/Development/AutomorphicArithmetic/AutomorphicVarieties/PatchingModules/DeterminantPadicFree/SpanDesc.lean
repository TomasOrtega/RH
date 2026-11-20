import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `i j`. Use `⟨fun _ => trivial, fun e => ?_⟩` and prove the remaining obligations. Establish `h0 : Z i j = 0` using `(hZ i j).2 e`. Rewrite using `[Submodule.mem_bot, Matrix.map_apply, h0, map_zero]`.
-/
private theorem sd_map_ev {F F' : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) F} (hZ : Z ∈ Ev F F n a) : Z.map f ∈ Ev F' F' n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

/- English proof (translation)
Proceed by induction on `hY using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero`.

Establish `: (0 : Matrix (Fin n) (Fin n) F).map f = 0` using `by ext i j; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `: (y + z).map f = y.map f + z.map f` using `by ext i j; simp`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy`. Establish `: (c • y).map f = f c • y.map f` using `by ext i j; simp`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hy`.
-/
private theorem sd_up {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F)
    (hY : Y ∈ Submodule.span F (Set.range r)) :
    Y.map f ∈ Submodule.span F' (Set.range fun i => (r i).map f) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin n) (Fin n) F).map f = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (y + z).map f = y.map f + z.map f := by ext i j; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map f = f c • y.map f := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `hY using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Introduce `c`. Establish `: (c • (r i).map f).map p = p c • r i`.

Use extensionality with `s t`. Simplify using `[hp]`. Use `show (c • (r i).map f).map p ∈ _`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Consider the case `zero`. Introduce `c`. Establish `: (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0` using `by ext i j; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y z _ _ hy hz`. Introduce `c`. Establish `: (c • (y + z)).map p = (c • y).map p + (c • z).map p` using `by ext i j; simp [mul_add]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (hy c) (hz c)`.

Consider the case `smul d y _ hy`. Introduce `c`. Rewrite using `[smul_smul]`. Conclude with `hy _`.
-/
private theorem sd_down {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (p : F' →+ F) (hp : ∀ (c : F') (x : F), p (c * f x) = p c * x)
    (Y : Matrix (Fin n) (Fin n) F')
    (hY : Y ∈ Submodule.span F' (Set.range fun i => (r i).map f)) :
    ∀ c : F', (c • Y).map p ∈ Submodule.span F (Set.range r) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro c
    have : (c • (r i).map f).map p = p c • r i := by
      ext s t; simp [hp]
    show (c • (r i).map f).map p ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero =>
    intro c
    have : (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    intro c
    have : (c • (y + z)).map p = (c • y).map p + (c • z).map p := by ext i j; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ (hy c) (hz c)
  | smul d y _ hy =>
    intro c
    rw [smul_smul]; exact hy _

/- English proof (translation)
Introduce `F F' ι _ _ f n a r hr`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `sd_map_ev f (hr i)`. Introduce `Z hZ`. Establish `hZ' : Z = ∑ i, ∑ j, single i j (Z i j)` using `matrix_eq_sum_single Z`. Rewrite using `[hZ']`.

Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)`. Establish `h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a` using `fun p q => ⟨fun _ => trivial, fun e' => by`. Rewrite using `[Submodule.mem_bot, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `e' e⟩`. Rewrite `h1` using `[← h]`. Establish `h2` using `Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `p q`.

Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `: Z i j = 0` using `(hZ i j).2 e`. Simplify using `[this]`. Introduce `h`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hr i`. Introduce `Z hZ`.

Use `letI : Algebra F F' := f.toAlgebra`. Take `⟨p, hp⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F') (LinearMap.ker_eq_bot.2 f.injective)`. Establish `hp1 : ∀ x : F, p (f x) = x` using `fun x => LinearMap.congr_fun hp x`. Establish `hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x`. Introduce `c x`.

Establish `h3 : c * f x = x • c` using `by rw [mul_comm]; rfl`. Use `show p (c * f x) = p c * x`. Rewrite using `[h3, map_smul, smul_eq_mul, mul_comm]`. Establish `h1` using `sd_map_ev f hZ`. Rewrite `h1` using `[← h]`.

Establish `h2` using `sd_down f r p.toAddMonoidHom hp2 _ h1 1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `s t`. Simplify using `[hp1]`.
-/
theorem UpperTheory.V.Pa.Det.spanDesc :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) F), (∀ i, r i ∈ Ev F F n a) → (Submodule.span F (Set.range r) = Ev F F n a ↔ Submodule.span F' (Set.range fun i => (r i).map f) = Ev F' F' n a) := by
  intro F F' ι _ _ f n a r hr
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact sd_map_ev f (hr i)
    · intro Z hZ
      have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
      rw [hZ']
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a :=
          fun p q => ⟨fun _ => trivial, fun e' => by
            rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
            rintro ⟨rfl, rfl⟩
            exact e' e⟩
        rw [← h] at h1
        have h2 := Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)
        convert h2 using 1
        ext p q
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs <;> simp
      · have : Z i j = 0 := (hZ i j).2 e
        simp [this]
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hr i
    · intro Z hZ
      letI : Algebra F F' := f.toAlgebra
      obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
        (LinearMap.ker_eq_bot.2 f.injective)
      have hp1 : ∀ x : F, p (f x) = x := fun x => LinearMap.congr_fun hp x
      have hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x := by
        intro c x
        have h3 : c * f x = x • c := by rw [mul_comm]; rfl
        show p (c * f x) = p c * x
        rw [h3, map_smul, smul_eq_mul, mul_comm]
      have h1 := sd_map_ev f hZ
      rw [← h] at h1
      have h2 := sd_down f r p.toAddMonoidHom hp2 _ h1 1
      convert h2 using 1
      ext s t
      simp [hp1]
