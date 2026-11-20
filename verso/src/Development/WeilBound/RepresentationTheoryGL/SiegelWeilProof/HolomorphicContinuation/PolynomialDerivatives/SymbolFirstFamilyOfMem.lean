import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.EquivLift
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ZeroRight

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} (ε : Fin m → Bool)

def U (N : ℕ) : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) :=
  {t | (t.sum fun _ e => e) ≤ N ∧ ∀ v ∈ t.support, inF1 ε (Sum.elim id id v)}

def S (N : ℕ) : Submodule ℂ (Sym m n) := restrictSupport ℂ (U ε N)

variable {ε}

/- English proof (translation)
Unfold `S`. Rewrite using `[mem_restrictSupport_iff]`. Conclude with `⟨fun h t ht => h ht, fun h t ht => h t ht⟩`.
-/
theorem mem_S {N : ℕ} {s : Sym m n} : s ∈ S ε N ↔ ∀ t ∈ s.support, t ∈ U ε N := by
  unfold S
  rw [mem_restrictSupport_iff]
  exact ⟨fun h t ht => h ht, fun h t ht => h t ht⟩

/- English proof (translation)
Introduce `t ht k hk`. Establish `hU` using `(mem_S.1 h t ht).2`. Break down `hk with hk | hk` into its components or cases. Conclude with `hU (Sum.inl k) (Finsupp.mem_support_iff.2 hk)`. Conclude with `hU (Sum.inr k) (Finsupp.mem_support_iff.2 hk)`.
-/
theorem symbol_first_family_of_mem {N : ℕ} {s : Sym m n} (h : s ∈ S ε N) : SymbolInFirstFamily ε s := by
  intro t ht k hk
  have hU := (mem_S.1 h t ht).2
  rcases hk with hk | hk
  · exact hU (Sum.inl k) (Finsupp.mem_support_iff.2 hk)
  · exact hU (Sum.inr k) (Finsupp.mem_support_iff.2 hk)

/- English proof (translation)
Use `mem_S.2 fun t ht => ⟨le_totalDegree ht, fun v hv => ?_⟩` and prove the remaining obligations. Break down `v with k | k` into its components or cases. Conclude with `h t ht k (Or.inl (Finsupp.mem_support_iff.1 hv))`. Conclude with `h t ht k (Or.inr (Finsupp.mem_support_iff.1 hv))`.
-/
theorem mem_S_of {s : Sym m n} (h : SymbolInFirstFamily ε s) : s ∈ S ε s.totalDegree := by
  refine mem_S.2 fun t ht => ⟨le_totalDegree ht, fun v hv => ?_⟩
  rcases v with k | k
  · exact h t ht k (Or.inl (Finsupp.mem_support_iff.1 hv))
  · exact h t ht k (Or.inr (Finsupp.mem_support_iff.1 hv))

/- English proof (translation)
Introduce `s hs`. Rewrite using `[mem_restrictTotalDegree, totalDegree, Finset.sup_le_iff]`. Conclude with `fun t ht => (mem_S.1 hs t ht).1`.
-/
theorem S_le (N : ℕ) : S (n := n) ε N ≤ restrictTotalDegree ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) ℂ N := by
  intro s hs
  rw [mem_restrictTotalDegree, totalDegree, Finset.sup_le_iff]
  exact fun t ht => (mem_S.1 hs t ht).1

instance (N : ℕ) : FiniteDimensional ℂ (S (n := n) ε N) :=
  Submodule.finiteDimensional_of_le (S_le N)

/- English proof (translation)
Unfold `symK`. Rewrite using `[mkDerivation_X]`. Apply the tactic sequence `rcases v with ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr]`. Distinguish the cases in `ha : ε a = true`. Rewrite using `[if_pos ha]`.

Use `split_ifs with h`. Conclude with `Or.inr ⟨Sum.inl (a, i, false), 1, by simp, by simp [inF1, ha]⟩`. Conclude with `Or.inl rfl`. Rewrite using `[if_neg ha]`. Use `split_ifs with h`.

Conclude with `Or.inr ⟨Sum.inl (a, j, true), -1, by simp, by simp [inF1]; simpa using ha⟩`. Conclude with `Or.inl rfl`. Distinguish the cases in `ha : ε a = true`. Rewrite using `[if_pos ha]`. Use `split_ifs with h`.

Conclude with `Or.inr ⟨Sum.inr (a, j, false), -1, by simp, by simp [inF1, ha]⟩`. Conclude with `Or.inl rfl`. Rewrite using `[if_neg ha]`. Use `split_ifs with h`. Conclude with `Or.inr ⟨Sum.inr (a, i, true), 1, by simp, by simp [inF1]; simpa using ha⟩`.

Conclude with `Or.inl rfl`.
-/
theorem symK_X (i j : Fin n) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) :
    symK ε i j (X v) = 0 ∨ ∃ v', ∃ c : ℂ, symK ε i j (X v) = c • (X v' : Sym m n) ∧ inF1 ε (Sum.elim id id v') := by
  unfold symK
  rw [mkDerivation_X]
  rcases v with ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, i, false), 1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, j, true), -1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, j, false), -1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, i, true), 1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl

/- English proof (translation)
Use `mem_S.2 fun t ht => ?_` and prove the remaining obligations. Use `support_monomial_subset ht` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Conclude with `this ▸ hu`.
-/
theorem monomial_mem_S {N : ℕ} {u} (hu : u ∈ U ε N) (r : ℂ) : monomial u r ∈ S (n := n) ε N := by
  refine mem_S.2 fun t ht => ?_
  have := support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  exact this ▸ hu

/- English proof (translation)
The claim follows from `Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)`.
-/
theorem deg_add (a b : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) :
    ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/- English proof (translation)
Unfold `symK`. Rewrite using `[mkDerivation_monomial]`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v hv => ?_)` and prove the remaining obligations. Simplify using `only`. Establish `hsymk` using `symK_X (ε := ε) i j v`.

Unfold `symK at hsymk`. Rewrite `hsymk` using `[mkDerivation_X]`. Break down `hsymk with h0 | ⟨v', c, hc, hv'⟩` into its components or cases. Rewrite using `[h0, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[hc, smul_eq_mul, mul_smul_comm, X, monomial_mul]`. Use `Submodule.smul_mem _ _ (monomial_mem_S ⟨?_, ?_⟩ _)` and prove the remaining obligations. Establish `hle : Finsupp.single v 1 ≤ t`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)`.

Establish `e1` using `deg_add (t - Finsupp.single v 1) (Finsupp.single v 1)`. Rewrite `e1` using `[tsub_add_cancel_of_le hle]`. Rewrite using `[deg_add]`. Establish `: ((Finsupp.single v' 1 : _ →₀ ℕ).sum fun _ e => e) = ((Finsupp.single v 1 : _ →₀ ℕ).sum fun _ e => e)`. Simplify using `[Finsupp.sum_single_index]`.

Rewrite using `[this, ← e1]`. Conclude with `ht.1`. Introduce `w hw`. Break down `Finset.mem_union.1 (Finsupp.support_add hw) with hw | hw` into its components or cases. Conclude with `ht.2 w (Finsupp.support_tsub hw)`.

Rewrite `hw` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`. Conclude with `hw ▸ hv'`.
-/
theorem symK_monomial_mem {N : ℕ} (i j : Fin n) {t} (ht : t ∈ U ε N) (r : ℂ) :
    symK ε i j (monomial t r) ∈ S (n := n) ε N := by
  unfold symK
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v hv => ?_)
  dsimp only
  have hsymk := symK_X (ε := ε) i j v
  unfold symK at hsymk
  rw [mkDerivation_X] at hsymk
  rcases hsymk with h0 | ⟨v', c, hc, hv'⟩
  · rw [h0, smul_zero]; exact Submodule.zero_mem _
  · rw [hc, smul_eq_mul, mul_smul_comm, X, monomial_mul]
    refine Submodule.smul_mem _ _ (monomial_mem_S ⟨?_, ?_⟩ _)
    · have hle : Finsupp.single v 1 ≤ t := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
      have e1 := deg_add (t - Finsupp.single v 1) (Finsupp.single v 1)
      rw [tsub_add_cancel_of_le hle] at e1
      rw [deg_add]
      have : ((Finsupp.single v' 1 : _ →₀ ℕ).sum fun _ e => e) = ((Finsupp.single v 1 : _ →₀ ℕ).sum fun _ e => e) := by
        simp [Finsupp.sum_single_index]
      rw [this, ← e1]; exact ht.1
    · intro w hw
      rcases Finset.mem_union.1 (Finsupp.support_add hw) with hw | hw
      · exact ht.2 w (Finsupp.support_tsub hw)
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hw
        exact hw ▸ hv'

/- English proof (translation)
Rewrite using `[as_sum s, map_sum]`. Conclude with `Submodule.sum_mem _ fun t ht => symK_monomial_mem i j (mem_S.1 hs t ht) _`.
-/
theorem symK_mem {N : ℕ} (i j : Fin n) {s : Sym m n} (hs : s ∈ S ε N) : symK ε i j s ∈ S ε N := by
  rw [as_sum s, map_sum]
  exact Submodule.sum_mem _ fun t ht => symK_monomial_mem i j (mem_S.1 hs t ht) _

end CoreD

end PositivityTheory.Rg.Sw.LC
