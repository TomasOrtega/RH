import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PairsModuloNormFixedQuadruple

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

/- English proof (translation)
Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem c3eqv_mem_orth (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ v ∈ U, S.hT v x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`.

Conclude with `⟨y, hy, rfl⟩`. Rewrite `hy` using `[← h]`. Take `⟨z, hz, rfl⟩` from `hy`. Simplify using `using hz`. Introduce and unpack `⟨h1, h2⟩`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `h1 z hz`. Introduce `y hy`. Conclude with `⟨n.symm y, h2 y hy, by simp⟩`.
-/
theorem c3eqv_gmap_iff (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ y ∈ Λ, n y ∈ Λ) ∧ ∀ y ∈ Λ, n.symm y ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro y hy
      exact ⟨n.symm y, h2 y hy, by simp⟩

/- English proof (translation)
Establish `hle : U.map (n : S.V →ₗ[E] S.V) ≤ U`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h y hy`. Establish `heq : U.map (n : S.V →ₗ[E] S.V) = U` using `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)`. Introduce `x hx`.

Establish `hx' : x ∈ U.map (n : S.V →ₗ[E] S.V)` using `heq.symm ▸ hx`. Take `⟨y, hy, rfl⟩` from `hx'`. Simplify using `using hy`.
-/
theorem c3eqv_symm_mem (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (h : ∀ x ∈ U, n x ∈ U) :
    ∀ x ∈ U, n.symm x ∈ U := by
  have hle : U.map (n : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : U.map (n : S.V →ₗ[E] S.V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)
  intro x hx
  have hx' : x ∈ U.map (n : S.V →ₗ[E] S.V) := heq.symm ▸ hx
  obtain ⟨y, hy, rfl⟩ := hx'
  simpa using hy

/- English proof (translation)
Establish `hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y` using `h`. Use `show ∀ x y, S.hT (n.symm x) (n.symm y) = S.hT x y`. Introduce `x y`. Use `hiso (n.symm x) (n.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`.

Conclude with `this.symm`.
-/
theorem c3eqv_isom_symm {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) : n.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  show ∀ x y, S.hT (n.symm x) (n.symm y) = S.hT x y
  intro x y
  have := hiso (n.symm x) (n.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

/- English proof (translation)
Establish `hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y` using `h`. Establish `hiso' : ∀ x y, S.hT (m x) (m y) = S.hT x y` using `h'`. Use `show ∀ x y, S.hT ((n.trans m) x) ((n.trans m) y) = S.hT x y`. Introduce `x y`. Simplify using `only [LinearEquiv.trans_apply, hiso', hiso]`.
-/
theorem c3eqv_isom_trans {n m : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h' : m ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    n.trans m ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have hiso' : ∀ x y, S.hT (m x) (m y) = S.hT x y := h'
  show ∀ x y, S.hT ((n.trans m) x) ((n.trans m) y) = S.hT x y
  intro x y
  simp only [LinearEquiv.trans_apply, hiso', hiso]

/- English proof (translation)
Rewrite `hx`, the goal using `[c3eqv_mem_orth]`. Introduce `v hv`. Establish `hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y` using `h`. Use `hiso (n.symm v) x` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`.

Rewrite using `[this]`. Conclude with `hx _ (hU v hv)`.
-/
theorem c3eqv_orth_map {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U₁ U₂ : Submodule E S.V)
    (hU : ∀ v ∈ U₂, n.symm v ∈ U₁) {x : S.V} (hx : x ∈ orth S U₁) : n x ∈ orth S U₂ := by
  rw [c3eqv_mem_orth] at hx ⊢
  intro v hv
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have := hiso (n.symm v) x
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact hx _ (hU v hv)

variable {T : E} (F : LFlag S r T)

/- English proof (translation)
Unfold `Xflag Formalism.MainNotions.S.FlagG.Xa`. Conclude with `Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => Nat.lt_succ_of_lt hi)`.
-/
theorem c3eqv_Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => Nat.lt_succ_of_lt hi)

/- English proof (translation)
Unfold `Xflag Formalism.MainNotions.S.FlagG.Xa`. Simplify using the standard rewrite rules.
-/
theorem c3eqv_Xflag_zero : Xflag F 0 = ⊥ := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  simp

/- English proof (translation)
Unfold `Xsp Xflag Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa`. Use `congr 1`. Use extensionality with `v`. Simplify using `only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Fin.is_lt, true_and]`.
-/
theorem c3eqv_Xsp_eq : Xsp F = Xflag F r := by
  unfold Xsp Xflag Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Fin.is_lt, true_and]

variable {F} {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Unfold `NLam at hn`. Simplify using `only [Set.mem_setOf_eq] at hn`. Take `⟨_, h1, _⟩` from `hn`. Introduce `x hx`. Consider the cases of `j with`.

Consider the case `zero`. Rewrite `hx`, the goal using `[c3eqv_Xflag_zero]`. Rewrite using `[(Submodule.mem_bot E).1 hx, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ j`.

Establish `h2` using `c3eqv_Xflag_mono F j (h1 j x hx)`. Establish `e : n x = (n x - x) + x` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ h2 hx`.
-/
theorem c3eqv_N_flag {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  unfold NLam at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨_, h1, _⟩ := hn
  intro x hx
  cases j with
  | zero =>
    rw [c3eqv_Xflag_zero] at hx ⊢
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h2 := c3eqv_Xflag_mono F j (h1 j x hx)
    have e : n x = (n x - x) + x := by abel
    rw [e]
    exact Submodule.add_mem _ h2 hx

/- English proof (translation)
Rewrite using `[c3eqv_Xsp_eq]`. Conclude with `c3eqv_N_flag hn r`.
-/
theorem c3eqv_N_X {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  rw [c3eqv_Xsp_eq]
  exact c3eqv_N_flag hn r

/- English proof (translation)
Establish `hX` using `c3eqv_N_X hn`. Establish `h'` using `hn`. Unfold `NLam at h'`. Simplify using `only [Set.mem_setOf_eq] at h'`. Unfold `IsAutLam at h'`.

Conclude with `fun x hx => c3eqv_orth_map h'.1.1 _ _ (c3eqv_symm_mem n _ hX) hx`.
-/
theorem c3eqv_N_orth {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  have hX := c3eqv_N_X hn
  have h' := hn
  unfold NLam at h'
  simp only [Set.mem_setOf_eq] at h'
  unfold IsAutLam at h'
  exact fun x hx => c3eqv_orth_map h'.1.1 _ _ (c3eqv_symm_mem n _ hX) hx

/- English proof (translation)
Establish `hnf` using `c3eqv_N_flag hn`. Establish `hno` using `c3eqv_N_orth hn`. Establish `hn'` using `hn`. Establish `hm'` using `hm`. Unfold `NLam at hn' hm' ⊢`.

Simplify using `only [Set.mem_setOf_eq] at hn' hm' ⊢`. Unfold `IsAutLam at hn' hm' ⊢`. Take `⟨⟨hni, hng⟩, hn1, hn2⟩` from `hn'`. Take `⟨⟨hmi, hmg⟩, hm1, hm2⟩` from `hm'`. Use `⟨⟨c3eqv_isom_trans hni hmi, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hng`, `hmg`, the goal using `[c3eqv_gmap_iff]`. Use `⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply]`. Conclude with `hmg.1 _ (hng.1 _ hy)`. Simplify using `only [LinearEquiv.symm_trans_apply]`.

Conclude with `hng.2 _ (hmg.2 _ hy)`. Introduce `j x hx`. Establish `e : (n.trans m) x - x = (m (n x) - n x) + (n x - x)`. Simplify using `only [LinearEquiv.trans_apply]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hm1 j _ (hnf (j + 1) x hx)) (hn1 j x hx)`. Introduce `x hx`. Establish `e : (n.trans m) x - x = (m (n x) - n x) + (n x - x)`. Simplify using `only [LinearEquiv.trans_apply]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hm2 _ (hno x hx)) (hn2 x hx)`.
-/
theorem c3eqv_NLam_trans {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : n.trans m ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  have hm' := hm
  unfold NLam at hn' hm' ⊢
  simp only [Set.mem_setOf_eq] at hn' hm' ⊢
  unfold IsAutLam at hn' hm' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  obtain ⟨⟨hmi, hmg⟩, hm1, hm2⟩ := hm'
  refine ⟨⟨c3eqv_isom_trans hni hmi, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng hmg ⊢
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      exact hmg.1 _ (hng.1 _ hy)
    · simp only [LinearEquiv.symm_trans_apply]
      exact hng.2 _ (hmg.2 _ hy)
  · intro j x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm1 j _ (hnf (j + 1) x hx)) (hn1 j x hx)
  · intro x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm2 _ (hno x hx)) (hn2 x hx)

/- English proof (translation)
Establish `hnf` using `c3eqv_N_flag hn`. Establish `hno` using `c3eqv_N_orth hn`. Establish `hn'` using `hn`. Unfold `NLam at hn' ⊢`. Simplify using `only [Set.mem_setOf_eq] at hn' ⊢`.

Unfold `IsAutLam at hn' ⊢`. Take `⟨⟨hni, hng⟩, hn1, hn2⟩` from `hn'`. Use `⟨⟨c3eqv_isom_symm hni, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hng`, the goal using `[c3eqv_gmap_iff]`. Rewrite using `[LinearEquiv.symm_symm]`.

Conclude with `⟨hng.2, hng.1⟩`. Introduce `j x hx`. Establish `hy` using `c3eqv_symm_mem n _ (hnf (j + 1)) x hx`. Establish `e : n.symm x - x = -(n (n.symm x) - n.symm x)`. Rewrite using `[LinearEquiv.apply_symm_apply]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (hn1 j _ hy)`. Introduce `x hx`. Establish `hy` using `c3eqv_symm_mem n _ hno x hx`.

Establish `e : n.symm x - x = -(n (n.symm x) - n.symm x)`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (hn2 _ hy)`.
-/
theorem c3eqv_NLam_symm {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  unfold NLam at hn' ⊢
  simp only [Set.mem_setOf_eq] at hn' ⊢
  unfold IsAutLam at hn' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  refine ⟨⟨c3eqv_isom_symm hni, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng ⊢
    rw [LinearEquiv.symm_symm]
    exact ⟨hng.2, hng.1⟩
  · intro j x hx
    have hy := c3eqv_symm_mem n _ (hnf (j + 1)) x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn1 j _ hy)
  · intro x hx
    have hy := c3eqv_symm_mem n _ hno x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn2 _ hy)

def isUnitriangularIntegral {N : ℕ} (ξ : Matrix (Fin N) (Fin N) (𝓞 E)) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1

end Gen

section D7

variable (D : D7)

variable (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)

end D7

end Formalism.MainNotions.BridgeLemma₂

end
