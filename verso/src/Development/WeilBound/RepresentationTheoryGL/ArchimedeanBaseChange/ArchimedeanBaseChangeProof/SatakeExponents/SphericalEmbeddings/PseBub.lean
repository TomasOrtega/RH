import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseBub

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse PositivityTheory.Rg.BcB.N3.PseSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `set g := T.comp f with hg`. Establish `hg' : ∀ v, g v = T (f v)` using `fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v`. Break down `hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h` into its components or cases. Introduce `x y hxy`. Establish `hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g`.

Rewrite using `[Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]`. Rewrite `hx` using `[h]`. Establish `hx' : x - y ∈ (⊥ : Submodule ℂ V)` using `hx`. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')`. It suffices to derive a contradiction.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hsph`. Establish `hfv : f v ∈ fixed ρ (KO k (Fin n))`. Introduce `h'`. Use `hv h'` as an intermediate fact. Rewrite using `[← Representation.IntertwiningMap.isIntertwining, this]`.

Simplify using the standard rewrite rules. Establish `hker : v ∈ Representation.IntertwiningMap.ker _ _ g`. Rewrite using `[h]`. Conclude with `(Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))`. Rewrite `hker` using `[Representation.IntertwiningMap.mem_ker, hg']`.

Use `hT (f v) hfv hker` as an intermediate fact. Conclude with `hv0 (hf (by rw [this, map_zero]))`.
-/
theorem comp_injective {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {π : Representation ℂ (GL (Fin n) k) V} {ρ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) U} (hi : π.IsIrreducible) (hsph : IsSpherical π)
    (f : π.IntertwiningMap ρ) (hf : Function.Injective f) (T : ρ.IntertwiningMap τ) (hT : KInj k T) :
    Function.Injective (T.comp f) := by
  classical
  set g := T.comp f with hg
  have hg' : ∀ v, g v = T (f v) := fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v
  rcases hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h
  · intro x y hxy
    have hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]
    rw [h] at hx
    have hx' : x - y ∈ (⊥ : Submodule ℂ V) := hx
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hfv : f v ∈ fixed ρ (KO k (Fin n)) := by
      intro h'
      have := hv h'
      rw [← Representation.IntertwiningMap.isIntertwining, this]
      simp
    have hker : v ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [h]
      exact (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))
    rw [Representation.IntertwiningMap.mem_ker, hg'] at hker
    have := hT (f v) hfv hker
    exact hv0 (hf (by rw [this, map_zero]))

def wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, (i : ℕ) * (σ i : ℕ)

/- English proof (translation)
Unfold `wt`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : wt σ ≤ n * (n * n) := by
  unfold wt
  calc ∑ i : Fin n, (i : ℕ) * (σ i : ℕ) ≤ ∑ _i : Fin n, n * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul i.2.le (σ i).2.le
    _ = n * (n * n) := by simp

/- English proof (translation)
Establish `hne : i ≠ j`. Introduce `h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Unfold `wt`.

Establish `key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) = (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) + ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ))`. Introduce `τ`. Rewrite using `[Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]`. Rewrite using `[Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]`. Rewrite using `[key σ, key (σ * Equiv.swap i j)]`.

Establish `hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) = ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ)`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k hk`. Establish `hkj` using `Finset.ne_of_mem_erase hk`. Establish `hki` using `Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)`.

Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]`. Rewrite using `[hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Establish `hd' : (σ j : ℕ) < σ i` using `hd`. Rewrite using `[hij]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wt_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1) (hd : σ j < σ i) :
    wt σ < wt (σ * Equiv.swap i j) := by
  classical
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  unfold wt
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) =
      (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) +
        ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ)) := by
    intro τ
    rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ))
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]
    rw [Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]
  rw [key σ, key (σ * Equiv.swap i j)]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd' : (σ j : ℕ) < σ i := hd
  rw [hij]
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `h1` to reduce the goal to its premises. Consider the cases of `n with`. Consider the case `zero => exact Subsingleton.elim _ _`.

Consider the case `succ m`. Establish `hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1))`. Rewrite using `[Fin.strictMono_iff_lt_succ]`. Introduce `i`. Establish `hle` using `hne i.castSucc i.succ (by simp)`.

Conclude with `lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))`. Use extensionality with `x`. Establish `hx` using `congrFun hs.eq_id x`. Simplify using `[hx]`.
-/
theorem exists_descent {n : ℕ} (σ : Equiv.Perm (Fin n)) (h1 : σ ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i := by
  by_contra hne
  push_neg at hne
  apply h1
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := hne i.castSucc i.succ (by simp)
      exact lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))
    ext x
    have hx := congrFun hs.eq_id x
    simp [hx]

/- English proof (translation)
Introduce `hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀`. Establish `key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m → (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) → ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Introduce `σ hm hσ`. Distinguish the cases in `h1 : σ = 1`. Substitute `h1` using the available equality. Conclude with `hσ`. Take `⟨i, j, hij, hd⟩` from `exists_descent σ h1`.

Take `⟨f, hf⟩` from `hσ`. Establish `hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖` using `hξ _ _ hd.le`. Take `⟨T0, hT0⟩` from `hG2 _ _ hle`. Take `⟨T, hT⟩` from `hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩`. Establish `hinj` using `comp_injective hi hsph f hf T hT`.

Establish `hw` using `wt_swap σ i j hij hd`. Establish `hwle` using `wt_le (σ * Equiv.swap i j)`. Establish `hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m`. Generalize the expression as in `n * (n * n) = N at *`. Use linear arithmetic over natural numbers and integers.

Conclude with `ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩`. Conclude with `key _ σ₀ rfl hf₀`.
-/
theorem bubble : Bubble k := by
  intro hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀
  have key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m →
      (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) →
        ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hm hσ
      by_cases h1 : σ = 1
      · subst h1
        exact hσ
      · obtain ⟨i, j, hij, hd⟩ := exists_descent σ h1
        obtain ⟨f, hf⟩ := hσ
        have hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖ := hξ _ _ hd.le
        obtain ⟨T0, hT0⟩ := hG2 _ _ hle
        obtain ⟨T, hT⟩ := hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩
        have hinj := comp_injective hi hsph f hf T hT
        have hw := wt_swap σ i j hij hd
        have hwle := wt_le (σ * Equiv.swap i j)
        have hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m := by
          generalize n * (n * n) = N at *
          omega
        exact ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩
  exact key _ σ₀ rfl hf₀

end PositivityTheory.Rg.BcB.N3.PseBub
