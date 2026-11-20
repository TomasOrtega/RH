import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

/- English proof (translation)
Introduce `W u hu`. Rewrite using `[Submodule.mem_orthogonal']`. Introduce `v hv`. Establish `hu'` using `(Submodule.mem_orthogonal' K u).1 hu`. Rewrite using `[Matrix.matrix_eq_sum_single W]`.

Simplify using `only [map_sum, LinearMap.sum_apply, sum_inner]`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Establish `hs : Matrix.single a b (W a b) = W a b • Eab a b`. Simplify using `[Eab, Matrix.smul_single]`. Rewrite using `[hs, map_smul, LinearMap.smul_apply, inner_smul_left, aA, hu' _ (hK _ _ hv), mul_zero, mul_zero]`.
-/
theorem graph_orth_stable {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (ρ : Mat p q →ₗ[ℂ] Module.End ℂ A) (aA : AdjG ρ) (K : Submodule ℂ A) (hK : ∀ W, ∀ v ∈ K, ρ W v ∈ K) :
    ∀ W, ∀ u ∈ Kᗮ, ρ W u ∈ Kᗮ := by
  intro W u hu
  rw [Submodule.mem_orthogonal']
  intro v hv
  have hu' := (Submodule.mem_orthogonal' K u).1 hu
  rw [Matrix.matrix_eq_sum_single W]
  simp only [map_sum, LinearMap.sum_apply, sum_inner]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have hs : Matrix.single a b (W a b) = W a b • Eab a b := by
    simp [Eab, Matrix.smul_single]
  rw [hs, map_smul, LinearMap.smul_apply, inner_smul_left, aA, hu' _ (hK _ _ hv), mul_zero, mul_zero]

def prodAct {p q : ℕ} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B) :
    Mat p q →ₗ[ℂ] Module.End ℂ (A × B) where
  toFun Z := (ρA Z).prodMap (ρB Z)
  map_add' Z Z' := by
    refine LinearMap.ext fun n => ?_
    simp
  map_smul' a Z := by
    refine LinearMap.ext fun n => ?_
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodAct_apply {p q : ℕ} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B) (Z : Mat p q) (n : A × B) :
    prodAct ρA ρB Z n = (ρA Z n.1, ρB Z n.2) := rfl

/- English proof (translation)
Use `set P := prodAct ρA ρB with hPdef`. Establish `hP : ∀ Z (n : A × B), P Z n = (ρA Z n.1, ρB Z n.2)` using `fun Z n => prodAct_apply ρA ρB Z n`. Establish `hLie : ∀ (X Y : Mat p q) (n : A × B), P X (P Y n) = P Y (P X n) + P (X * Y - Y * X) n`. Introduce `X Y n`. Establish `h1` using `congrArg (fun f => f n.1) (hA X Y)`.

Establish `h2` using `congrArg (fun f => f n.2) (hB X Y)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only [hP, Prod.fst_add]`. Rewrite using `[← h1]`.

Normalize the expressions using the abelian group laws. Simplify using `only [hP, Prod.snd_add]`. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws. Establish `hbr : ∀ a b c d : Ix p q, Eab a b * Eab c d - Eab c d * Eab a b = (if b = c then Eab a d else 0) - (if d = a then Eab c b else 0)`.

Introduce `a b c d`. Simplify using `only [Eab]`. Use `split_ifs with h1 h2 h2`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Simplify using the standard rewrite rules. Substitute `h1` using the available equality. Rewrite using `[Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h2]`. Simplify using the standard rewrite rules. Substitute `h2` using the available equality.

Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_same]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_of_ne _ _ _ _ h2]`. Set `Rs : Set (Submodule ℂ (A × B))` to `{M | (x, y) ∈ M ∧ ∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M}`. Set `R` to `sInf Rs`.

Establish `hR_xy : (x, y) ∈ R` using `Submodule.mem_sInf.2 fun M hM => hM.1`. Establish `hR_raise : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inl i) (.inr j)) n ∈ R` using `fun i j n hn => Submodule.mem_sInf.2 fun M hM => hM.2 i j n (Submodule.mem_sInf.1 hn M hM)`. Establish `hR_ind : ∀ M : Submodule ℂ (A × B), (x, y) ∈ M → (∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M) → R ≤ M` using `fun M h1 h2 => sInf_le ⟨h1, h2⟩`. Establish `hK : ∀ a b : Ix p q, sameBlock a b → ∀ n ∈ R, P (Eab a b) n ∈ R`. Set `T : Submodule ℂ (A × B)` to `R ⊓ ⨅ a : Ix p q, ⨅ b : Ix p q, ⨅ (_ : sameBlock a b), R.comap (P (Eab a b))`.

Establish `hT : R ≤ T`. Apply `hR_ind` to reduce the goal to its premises. Use `Submodule.mem_inf.2 ⟨hR_xy, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `a b hab`.

Rewrite using `[hP]`. Simplify using `only [hxK a b hab, hyK a b hab]`. Rewrite using `[← Prod.smul_mk]`. Conclude with `R.smul_mem _ hR_xy`. Introduce `i j n hn`.

Take `⟨hnR, hn2⟩` from `Submodule.mem_inf.1 hn`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hn2`. Use `Submodule.mem_inf.2 ⟨hR_raise i j n hnR, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `a b hab`.

Rewrite using `[hLie, hbr]`. Use `R.add_mem (hR_raise i j _ (hn2 a b hab)) ?_` and prove the remaining obligations. Rewrite using `[map_sub, LinearMap.sub_apply]`. Use `R.sub_mem ?_ ?_` and prove the remaining obligations. Use `split_ifs with h`.

Substitute `h` using the available equality. Break down `a with a | a` into its components or cases. Conclude with `hR_raise a j n hnR`. Simplify using `[sameBlock] at hab`. Simplify using the standard rewrite rules.

Use `split_ifs with h`. Substitute `h` using the available equality. Break down `b with b | b` into its components or cases. Simplify using `[sameBlock] at hab`. Conclude with `hR_raise i b n hnR`.

Simplify using the standard rewrite rules. Introduce `a b hab n hn`. Establish `h` using `(Submodule.mem_inf.1 (hT hn)).2`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at h`. Conclude with `h a b hab`.

Establish `hL : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inr j) (.inl i)) n ∈ R`. Set `T : Submodule ℂ (A × B)` to `R ⊓ ⨅ i : Fin p, ⨅ j : Fin q, R.comap (P (Eab (.inr j) (.inl i)))`. Establish `hT : R ≤ T`. Apply `hR_ind` to reduce the goal to its premises. Use `Submodule.mem_inf.2 ⟨hR_xy, ?_⟩` and prove the remaining obligations.

Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `i j`. Rewrite using `[hP, hxP, hyP, Prod.mk_zero_zero]`. Conclude with `R.zero_mem`. Introduce `i' j' n hn`.

Take `⟨hnR, hn2⟩` from `Submodule.mem_inf.1 hn`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hn2`. Use `Submodule.mem_inf.2 ⟨hR_raise i' j' n hnR, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `i j`.

Rewrite using `[hLie, hbr]`. Use `R.add_mem (hR_raise i' j' _ (hn2 i j)) ?_` and prove the remaining obligations. Rewrite using `[map_sub, LinearMap.sub_apply]`. Use `R.sub_mem ?_ ?_` and prove the remaining obligations. Use `split_ifs with h`.

Conclude with `hK _ _ (by simp [sameBlock]) n hnR`. Simplify using the standard rewrite rules. Use `split_ifs with h`. Conclude with `hK _ _ (by simp [sameBlock]) n hnR`. Simplify using the standard rewrite rules.

Introduce `i j n hn`. Establish `h` using `(Submodule.mem_inf.1 (hT hn)).2`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at h`. Conclude with `h i j`. Establish `hall : ∀ W, ∀ n ∈ R, P W n ∈ R`.

Introduce `W n hn`. Rewrite using `[Matrix.matrix_eq_sum_single W]`. Simplify using `only [map_sum, LinearMap.sum_apply]`. Use `R.sum_mem fun a _ => R.sum_mem fun b _ => ?_` and prove the remaining obligations. Establish `hs : Matrix.single a b (W a b) = W a b • Eab a b`.

Simplify using `[Eab, Matrix.smul_single]`. Rewrite using `[hs, map_smul, LinearMap.smul_apply]`. Use `R.smul_mem _ ?_` and prove the remaining obligations. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `hK _ _ (by simp [sameBlock]) n hn`.

Conclude with `hR_raise a b n hn`. Conclude with `hL b a n hn`. Conclude with `hK _ _ (by simp [sameBlock]) n hn`. Set `Q : Submodule ℂ (A × B)` to `{ carrier := {m | ⟪x, x⟫_ℂ * ⟪m.2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, x⟫_ℂ} add_mem' := by`. Introduce `m m' hm hm'`.

Simplify using `only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, inner_add_left] at hm hm' ⊢`. Take the linear combination `hm + hm'`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `c m hm`.

Simplify using `only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, inner_smul_left] at hm ⊢`. Take the linear combination `(starRingEnd ℂ c) * hm }`. Establish `hRQ : R ≤ Q`. Apply `hR_ind` to reduce the goal to its premises. Use `show ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪x, x⟫_ℂ`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i j n _ show ⟪x, x⟫_ℂ * ⟪(P _ n).2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪(P _ n).1, x⟫_ℂ`. Rewrite using `[hP]`. Simplify using `only`. Rewrite using `[aB, hyP, aA, hxP, inner_zero_right, inner_zero_right]`.

Expand and normalize the polynomial expressions, which then agree. Set `S : Submodule ℂ (A × B)` to `{ carrier := {n | ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, n.2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, n.1⟫_ℂ} add_mem' := by`. Introduce `n n' hn hn' m hm`. Simplify using `only [Prod.fst_add, Prod.snd_add, inner_add_right]`. Take the linear combination `hn m hm + hn' m hm`.

Use the proof step `zero_mem' := by`. Introduce `m _`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c n hn m hm`.

Simplify using `only [Prod.smul_fst, Prod.smul_snd, inner_smul_right]`. Take the linear combination `c * hn m hm }`. Establish `hRS : R ≤ S`. Apply `hR_ind` to reduce the goal to its premises. Introduce `m hm`.

Conclude with `hRQ hm`. Introduce `i j n hn m hm`. Establish `key` using `hn (P (Eab (.inr j) (.inl i)) m) (hall _ m hm)`. Rewrite `key` using `[hP]`. Simplify using `only at key`.

Rewrite `key` using `[aB, aA]`. Establish `he : epsB (Sum.inr j : Ix p q) (Sum.inl i) = -1`. Simplify using `[epsB, sameBlock]`. Rewrite `key` using `[he]`. Use `show ⟪x, x⟫_ℂ * ⟪m.2, (P _ n).2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (P _ n).1⟫_ℂ`.

Rewrite using `[hP]`. Take the linear combination `-key`. Use `⟨R, hR_xy, hall, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Establish `h : ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, v⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (0 : A)⟫_ℂ` using `hRS hv`.

Establish `h0` using `h (0, v) hv`. Simplify using `only [inner_zero_right, mul_zero] at h0`. Establish `hxx : ⟪x, x⟫_ℂ ≠ 0` using `inner_self_ne_zero.2 hx0`. Establish `hvv : ⟪v, v⟫_ℂ = 0` using `(mul_eq_zero.1 h0).resolve_left hxx`. Conclude with `inner_self_eq_zero.1 hvv`.
-/
theorem graph_sub {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B)
    (hA : IsLie ρA) (hB : IsLie ρB) (aA : AdjG ρA) (aB : AdjG ρB) (lam : Ix p q → ℂ) (x : A) (y : B)
    (hx0 : x ≠ 0)
    (hxK : ∀ a b, sameBlock a b → ρA (Eab a b) x = (if a = b then lam a else 0) • x)
    (hyK : ∀ a b, sameBlock a b → ρB (Eab a b) y = (if a = b then lam a else 0) • y)
    (hxP : ∀ i j, ρA (Eab (.inr j) (.inl i)) x = 0) (hyP : ∀ i j, ρB (Eab (.inr j) (.inl i)) y = 0) :
    ∃ N : Submodule ℂ (A × B), (x, y) ∈ N ∧ (∀ W, ∀ n ∈ N, prodAct ρA ρB W n ∈ N) ∧
      ∀ v, ((0 : A), v) ∈ N → v = 0 := by
  classical
  set P := prodAct ρA ρB with hPdef
  have hP : ∀ Z (n : A × B), P Z n = (ρA Z n.1, ρB Z n.2) := fun Z n => prodAct_apply ρA ρB Z n
  have hLie : ∀ (X Y : Mat p q) (n : A × B), P X (P Y n) = P Y (P X n) + P (X * Y - Y * X) n := by
    intro X Y n
    have h1 := congrArg (fun f => f n.1) (hA X Y)
    have h2 := congrArg (fun f => f n.2) (hB X Y)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
    refine Prod.ext ?_ ?_
    · simp only [hP, Prod.fst_add]
      rw [← h1]
      abel
    · simp only [hP, Prod.snd_add]
      rw [← h2]
      abel
  have hbr : ∀ a b c d : Ix p q, Eab a b * Eab c d - Eab c d * Eab a b =
      (if b = c then Eab a d else 0) - (if d = a then Eab c b else 0) := by
    intro a b c d
    simp only [Eab]
    split_ifs with h1 h2 h2
    · subst h1
      subst h2
      simp
    · subst h1
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h2]
      simp
    · subst h2
      rw [Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_same]
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_of_ne _ _ _ _ h2]
  let Rs : Set (Submodule ℂ (A × B)) :=
    {M | (x, y) ∈ M ∧ ∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M}
  let R := sInf Rs
  have hR_xy : (x, y) ∈ R := Submodule.mem_sInf.2 fun M hM => hM.1
  have hR_raise : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inl i) (.inr j)) n ∈ R :=
    fun i j n hn => Submodule.mem_sInf.2 fun M hM => hM.2 i j n (Submodule.mem_sInf.1 hn M hM)
  have hR_ind : ∀ M : Submodule ℂ (A × B), (x, y) ∈ M →
      (∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M) → R ≤ M :=
    fun M h1 h2 => sInf_le ⟨h1, h2⟩
  have hK : ∀ a b : Ix p q, sameBlock a b → ∀ n ∈ R, P (Eab a b) n ∈ R := by
    let T : Submodule ℂ (A × B) :=
      R ⊓ ⨅ a : Ix p q, ⨅ b : Ix p q, ⨅ (_ : sameBlock a b), R.comap (P (Eab a b))
    have hT : R ≤ T := by
      apply hR_ind
      · refine Submodule.mem_inf.2 ⟨hR_xy, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro a b hab
        rw [hP]
        simp only [hxK a b hab, hyK a b hab]
        rw [← Prod.smul_mk]
        exact R.smul_mem _ hR_xy
      · intro i j n hn
        obtain ⟨hnR, hn2⟩ := Submodule.mem_inf.1 hn
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hn2
        refine Submodule.mem_inf.2 ⟨hR_raise i j n hnR, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro a b hab
        rw [hLie, hbr]
        refine R.add_mem (hR_raise i j _ (hn2 a b hab)) ?_
        rw [map_sub, LinearMap.sub_apply]
        refine R.sub_mem ?_ ?_
        · split_ifs with h
          · subst h
            rcases a with a | a
            · exact hR_raise a j n hnR
            · simp [sameBlock] at hab
          · simp
        · split_ifs with h
          · subst h
            rcases b with b | b
            · simp [sameBlock] at hab
            · exact hR_raise i b n hnR
          · simp
    intro a b hab n hn
    have h := (Submodule.mem_inf.1 (hT hn)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h
    exact h a b hab
  have hL : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inr j) (.inl i)) n ∈ R := by
    let T : Submodule ℂ (A × B) :=
      R ⊓ ⨅ i : Fin p, ⨅ j : Fin q, R.comap (P (Eab (.inr j) (.inl i)))
    have hT : R ≤ T := by
      apply hR_ind
      · refine Submodule.mem_inf.2 ⟨hR_xy, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro i j
        rw [hP, hxP, hyP, Prod.mk_zero_zero]
        exact R.zero_mem
      · intro i' j' n hn
        obtain ⟨hnR, hn2⟩ := Submodule.mem_inf.1 hn
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hn2
        refine Submodule.mem_inf.2 ⟨hR_raise i' j' n hnR, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro i j
        rw [hLie, hbr]
        refine R.add_mem (hR_raise i' j' _ (hn2 i j)) ?_
        rw [map_sub, LinearMap.sub_apply]
        refine R.sub_mem ?_ ?_
        · split_ifs with h
          · exact hK _ _ (by simp [sameBlock]) n hnR
          · simp
        · split_ifs with h
          · exact hK _ _ (by simp [sameBlock]) n hnR
          · simp
    intro i j n hn
    have h := (Submodule.mem_inf.1 (hT hn)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h
    exact h i j
  have hall : ∀ W, ∀ n ∈ R, P W n ∈ R := by
    intro W n hn
    rw [Matrix.matrix_eq_sum_single W]
    simp only [map_sum, LinearMap.sum_apply]
    refine R.sum_mem fun a _ => R.sum_mem fun b _ => ?_
    have hs : Matrix.single a b (W a b) = W a b • Eab a b := by
      simp [Eab, Matrix.smul_single]
    rw [hs, map_smul, LinearMap.smul_apply]
    refine R.smul_mem _ ?_
    rcases a with a | a <;> rcases b with b | b
    · exact hK _ _ (by simp [sameBlock]) n hn
    · exact hR_raise a b n hn
    · exact hL b a n hn
    · exact hK _ _ (by simp [sameBlock]) n hn
  let Q : Submodule ℂ (A × B) :=
    { carrier := {m | ⟪x, x⟫_ℂ * ⟪m.2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, x⟫_ℂ}
      add_mem' := by
        intro m m' hm hm'
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, inner_add_left] at hm hm' ⊢
        linear_combination hm + hm'
      zero_mem' := by simp
      smul_mem' := by
        intro c m hm
        simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, inner_smul_left] at hm ⊢
        linear_combination (starRingEnd ℂ c) * hm }
  have hRQ : R ≤ Q := by
    apply hR_ind
    · show ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪x, x⟫_ℂ
      ring
    · intro i j n _
      show ⟪x, x⟫_ℂ * ⟪(P _ n).2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪(P _ n).1, x⟫_ℂ
      rw [hP]
      simp only
      rw [aB, hyP, aA, hxP, inner_zero_right, inner_zero_right]
      ring
  let S : Submodule ℂ (A × B) :=
    { carrier := {n | ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, n.2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, n.1⟫_ℂ}
      add_mem' := by
        intro n n' hn hn' m hm
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
        linear_combination hn m hm + hn' m hm
      zero_mem' := by
        intro m _
        simp
      smul_mem' := by
        intro c n hn m hm
        simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right]
        linear_combination c * hn m hm }
  have hRS : R ≤ S := by
    apply hR_ind
    · intro m hm
      exact hRQ hm
    · intro i j n hn m hm
      have key := hn (P (Eab (.inr j) (.inl i)) m) (hall _ m hm)
      rw [hP] at key
      simp only at key
      rw [aB, aA] at key
      have he : epsB (Sum.inr j : Ix p q) (Sum.inl i) = -1 := by
        simp [epsB, sameBlock]
      rw [he] at key
      show ⟪x, x⟫_ℂ * ⟪m.2, (P _ n).2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (P _ n).1⟫_ℂ
      rw [hP]
      linear_combination -key
  refine ⟨R, hR_xy, hall, ?_⟩
  intro v hv
  have h : ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, v⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (0 : A)⟫_ℂ := hRS hv
  have h0 := h (0, v) hv
  simp only [inner_zero_right, mul_zero] at h0
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
  have hvv : ⟪v, v⟫_ℂ = 0 := (mul_eq_zero.1 h0).resolve_left hxx
  exact inner_self_eq_zero.1 hvv

/- English proof (translation)
Take `⟨N, hxyN, hNinv, hN0⟩` from `graph_sub ρA ρB hA hB aA aB lam x y hx0 hxK hyK hxP hyP`. Establish `hg : ∀ (z : A × B), z ∈ N → z.1 = 0 → z.2 = 0`. Introduce and unpack `⟨a, b⟩ hz h0`. Simplify using `only at h0 ⊢`. Substitute `h0` using the available equality.

Conclude with `hN0 b hz`. Establish `huniq : ∀ (u : A) (b b' : B), (u, b) ∈ N → (u, b') ∈ N → b = b'`. Introduce `u b b' h h'`. Establish `hd : ((0 : A), b - b') ∈ N`. Establish `h2` using `N.sub_mem h h'`.

Simplify using `using h2`. Conclude with `sub_eq_zero.1 (hN0 _ hd)`. Establish `hGinv : ∀ W, ∀ u ∈ genG ρA (Submodule.span ℂ {x}), ρA W u ∈ genG ρA (Submodule.span ℂ {x})`. Introduce `W u hu`. Conclude with `Submodule.mem_sInf.2 fun M hM => hM.2 W u (Submodule.mem_sInf.1 hu M hM)`.

Establish `hxG : x ∈ genG ρA (Submodule.span ℂ {x})` using `Submodule.mem_sInf.2 fun M hM => hM.1 (Submodule.mem_span_singleton_self x)`. Establish `hGdom : genG ρA (Submodule.span ℂ {x}) ≤ N.map (LinearMap.fst ℂ A B)`. Use `sInf_le (show N.map (LinearMap.fst ℂ A B) ∈ {M : Submodule ℂ A | Submodule.span ℂ {x} ≤ M ∧ ∀ W, ∀ u ∈ M, ρA W u ∈ M} from ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `⟨(x, y), hxyN, rfl⟩`.

Introduce and unpack `W u ⟨n, hn, rfl⟩`. Use `⟨prodAct ρA ρB W n, hNinv W n hn, ?_⟩` and prove the remaining obligations. Simplify using `[prodAct_apply]`. Use `set G := genG ρA (Submodule.span ℂ {x}) with hGdef`. Establish `hcompl : IsCompl G Gᗮ` using `⟨Submodule.orthogonal_disjoint G, codisjoint_iff.2 hproj⟩`.

Set `Φ : A →ₗ[ℂ] B` to `N.toLinearPMap.toFun ∘ₗ Submodule.inclusion hGdom ∘ₗ Submodule.linearProjOfIsCompl G Gᗮ hcompl`. Establish `hΦG : ∀ u (hu : u ∈ G), (u, Φ u) ∈ N`. Introduce `u hu`. Establish `h` using `Submodule.mem_graph_toLinearPMap hg (Submodule.inclusion hGdom ⟨u, hu⟩)`. Establish `hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = ⟨u, hu⟩` using `Submodule.linearProjOfIsCompl_apply_left hcompl ⟨u, hu⟩`.

Simplify using `only [Φ, LinearMap.comp_apply, hp]`. Conclude with `h`. Establish `hΦO : ∀ u ∈ Gᗮ, Φ u = 0`. Introduce `u hu`. Establish `hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = 0` using `Submodule.linearProjOfIsCompl_apply_right hcompl ⟨u, hu⟩`.

Simplify using `only [Φ, LinearMap.comp_apply, hp, map_zero]`. Establish `hOinv` using `graph_orth_stable ρA aA G hGinv`. Use `⟨Φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z u`. Establish `hu : u ∈ G ⊔ Gᗮ`.

Rewrite using `[hproj]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨g, hgG, g', hgO, rfl⟩` from `Submodule.mem_sup.1 hu`. Rewrite using `[map_add, map_add, map_add, hΦO g' hgO, hΦO _ (hOinv Z g' hgO), add_zero, add_zero]`. Use `huniq (ρA Z g) _ _ (hΦG _ (hGinv Z g hgG)) ?_` and prove the remaining obligations.

Establish `h3` using `hNinv Z _ (hΦG g hgG)`. Rewrite `h3` using `[prodAct_apply]`. Then use the resulting hypothesis. Conclude with `huniq x _ _ (hΦG x hxG) hxyN`.
-/
theorem graph_map {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B)
    (hA : IsLie ρA) (hB : IsLie ρB) (aA : AdjG ρA) (aB : AdjG ρB) (lam : Ix p q → ℂ) (x : A) (y : B)
    (hx0 : x ≠ 0)
    (hxK : ∀ a b, sameBlock a b → ρA (Eab a b) x = (if a = b then lam a else 0) • x)
    (hyK : ∀ a b, sameBlock a b → ρB (Eab a b) y = (if a = b then lam a else 0) • y)
    (hxP : ∀ i j, ρA (Eab (.inr j) (.inl i)) x = 0) (hyP : ∀ i j, ρB (Eab (.inr j) (.inl i)) y = 0)
    (hproj : genG ρA (Submodule.span ℂ {x}) ⊔ (genG ρA (Submodule.span ℂ {x}))ᗮ = ⊤) :
    ∃ Φ : A →ₗ[ℂ] B, (∀ Z u, Φ (ρA Z u) = ρB Z (Φ u)) ∧ Φ x = y := by
  classical
  obtain ⟨N, hxyN, hNinv, hN0⟩ := graph_sub ρA ρB hA hB aA aB lam x y hx0 hxK hyK hxP hyP
  have hg : ∀ (z : A × B), z ∈ N → z.1 = 0 → z.2 = 0 := by
    rintro ⟨a, b⟩ hz h0
    simp only at h0 ⊢
    subst h0
    exact hN0 b hz
  have huniq : ∀ (u : A) (b b' : B), (u, b) ∈ N → (u, b') ∈ N → b = b' := by
    intro u b b' h h'
    have hd : ((0 : A), b - b') ∈ N := by
      have h2 := N.sub_mem h h'
      simpa using h2
    exact sub_eq_zero.1 (hN0 _ hd)
  have hGinv : ∀ W, ∀ u ∈ genG ρA (Submodule.span ℂ {x}), ρA W u ∈ genG ρA (Submodule.span ℂ {x}) := by
    intro W u hu
    exact Submodule.mem_sInf.2 fun M hM => hM.2 W u (Submodule.mem_sInf.1 hu M hM)
  have hxG : x ∈ genG ρA (Submodule.span ℂ {x}) :=
    Submodule.mem_sInf.2 fun M hM => hM.1 (Submodule.mem_span_singleton_self x)
  have hGdom : genG ρA (Submodule.span ℂ {x}) ≤ N.map (LinearMap.fst ℂ A B) := by
    refine sInf_le (show N.map (LinearMap.fst ℂ A B) ∈ {M : Submodule ℂ A | Submodule.span ℂ {x} ≤ M ∧ ∀ W, ∀ u ∈ M, ρA W u ∈ M} from ⟨?_, ?_⟩)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨(x, y), hxyN, rfl⟩
    · rintro W u ⟨n, hn, rfl⟩
      refine ⟨prodAct ρA ρB W n, hNinv W n hn, ?_⟩
      simp [prodAct_apply]
  set G := genG ρA (Submodule.span ℂ {x}) with hGdef
  have hcompl : IsCompl G Gᗮ := ⟨Submodule.orthogonal_disjoint G, codisjoint_iff.2 hproj⟩
  let Φ : A →ₗ[ℂ] B := N.toLinearPMap.toFun ∘ₗ Submodule.inclusion hGdom ∘ₗ Submodule.linearProjOfIsCompl G Gᗮ hcompl
  have hΦG : ∀ u (hu : u ∈ G), (u, Φ u) ∈ N := by
    intro u hu
    have h := Submodule.mem_graph_toLinearPMap hg (Submodule.inclusion hGdom ⟨u, hu⟩)
    have hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = ⟨u, hu⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hcompl ⟨u, hu⟩
    simp only [Φ, LinearMap.comp_apply, hp]
    exact h
  have hΦO : ∀ u ∈ Gᗮ, Φ u = 0 := by
    intro u hu
    have hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨u, hu⟩
    simp only [Φ, LinearMap.comp_apply, hp, map_zero]
  have hOinv := graph_orth_stable ρA aA G hGinv
  refine ⟨Φ, ?_, ?_⟩
  · intro Z u
    have hu : u ∈ G ⊔ Gᗮ := by
      rw [hproj]
      trivial
    obtain ⟨g, hgG, g', hgO, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add, map_add, map_add, hΦO g' hgO, hΦO _ (hOinv Z g' hgO), add_zero, add_zero]
    refine huniq (ρA Z g) _ _ (hΦG _ (hGinv Z g hgG)) ?_
    have h3 := hNinv Z _ (hΦG g hgG)
    rwa [prodAct_apply] at h3
  · exact huniq x _ _ (hΦG x hxG) hxyN

end PositivityTheory.KReal

end
