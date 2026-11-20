import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `: x = 1` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Conclude with `T.one_mem`. Consider the case `succ n`. Rewrite using `[eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `h _ _ (by simp)`.
-/
theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

/- English proof (translation)
Set `S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))` to `{ carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q} one_mem' := by`. Introduce `Q`. Establish `: (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.

Rewrite using `[this, rename_id]`. Simplify using the standard rewrite rules. Use the proof step `mul_mem' := by`. Introduce `v w hv hw Q`. Establish `: (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) = (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))`.

Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Simplify using `only [Set.mem_setOf_eq] at hv hw ⊢`. Rewrite using `[this, ← rename_rename, hv, hw]`. Simplify using `only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]`.

Use `ring }`. Establish `hS : S = ⊤`. Establish `htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) = Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ)))))`. Use extensionality with `x`. Simplify using `[Submonoid.mem_pi]`.

Rewrite using `[eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]`. Introduce `τ`. Rewrite using `[Submonoid.map_le_iff_le_comap]`. Rewrite using `[perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]`. Introduce `a b hab Q`.

Establish `hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩`. Use function extensionality and compare the values at `⟨σ, c⟩`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]`.

Rewrite using `[Equiv.swap_apply_def, Equiv.swap_apply_def]`. Distinguish the cases in `h1 : c = a`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : c = b`.

Substitute `h2` using the available equality. Simplify using `[h1]`. Simplify using `[h1, h2]`. Simplify using `only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne]`.

Introduce `e`. Conclude with `h (congrArg Sigma.fst e)`. Introduce `e`. Conclude with `h (congrArg Sigma.fst e)`. Establish `hab' : a ≠ b`.

Introduce `e`. Substitute `e` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ (Equiv.swap a b)) σ)) = -1`. Establish `: ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ`.

Introduce `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.mulSingle_eq_of_ne h]`.

Simplify using `only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]`. Conclude with `Equiv.Perm.sign_swap hab'`. Use `show L _ = _`. Rewrite using `[hf, hs, hL τ a b hab Q]`. Simplify using the standard rewrite rules.

Establish `hw : w ∈ S` using `by rw [hS]; trivial`. Conclude with `hw Q`.
-/
theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
