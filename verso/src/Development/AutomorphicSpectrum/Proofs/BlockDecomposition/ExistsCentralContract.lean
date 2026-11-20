import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac ValuativeRel Matrix Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp` and prove the remaining obligations. Establish `hd : A.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero`. Conclude with `(continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt`.
-/
theorem isEmbedding_val_GL (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) k → Matrix (Fin n) (Fin n) k) := by
  refine Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  exact (continuousAt_matrix_inv _
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt

/- English proof (translation)
Establish `hS : (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) k)` using `(continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)`. Establish `e : 𝓝 (0 : Matrix (Fin n) (Fin n) k) = Filter.pi fun _ : Fin n => Filter.pi fun _ : Fin n => 𝓝 (0 : k)` using `by show 𝓝 (0 : Fin n → Fin n → k) = _`. Rewrite using `[nhds_pi]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[nhds_pi]`. Both sides reduce to the same expression. Rewrite `hS` using `[e]`. Take `⟨I, t, ht, hsub⟩` from `Filter.mem_pi'.1 hS`. Establish `ht' : ∀ i, ∃ (I' : Finset (Fin n)) (t' : Fin n → Set k), (∀ j, t' j ∈ 𝓝 (0 : k)) ∧ (I' : Set (Fin n)).pi t' ⊆ t i` using `fun i => Filter.mem_pi'.1 (ht i)`.

Use `choose I' t' h1 h2 using ht'`. Use `⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => h1 i j, fun A hA => ?_⟩` and prove the remaining obligations. Establish `h3 : A - 1 ∈ (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V` using `hsub fun i _ => h2 i fun j _ => by`. Use `hA i j` as an intermediate fact. Simplify using `only [Set.mem_iInter] at this`.

Conclude with `this i j`. Simplify using `using h3`.
-/
theorem exists_entry_nhds {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)}
    (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ W ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, (A - 1) i j ∈ W) → A ∈ V := by
  have hS : (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) k) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  have e : 𝓝 (0 : Matrix (Fin n) (Fin n) k) =
      Filter.pi fun _ : Fin n => Filter.pi fun _ : Fin n => 𝓝 (0 : k) := by
    show 𝓝 (0 : Fin n → Fin n → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [e] at hS
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hS
  have ht' : ∀ i, ∃ (I' : Finset (Fin n)) (t' : Fin n → Set k), (∀ j, t' j ∈ 𝓝 (0 : k)) ∧
      (I' : Set (Fin n)).pi t' ⊆ t i := fun i => Filter.mem_pi'.1 (ht i)
  choose I' t' h1 h2 using ht'
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => h1 i j,
    fun A hA => ?_⟩
  have h3 : A - 1 ∈ (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V :=
    hsub fun i _ => h2 i fun j _ => by
      have := hA i j
      simp only [Set.mem_iInter] at this
      exact this i j
  simpa using h3

variable {s : ℕ} {d : Fin s → ℕ}

def blockScalar {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) : Levi k (fun a => Fin (d a)) := fun a =>
  ⟨(c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k), (c ^ C a)⁻¹ • (1 : Matrix (Fin (d a)) (Fin (d a)) k),
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul]⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `Units.ext ?_` and prove the remaining obligations. Use `show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) * (m a).val = (m a).val * ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k))`. Simplify using the standard rewrite rules.
-/
theorem blockScalar_central {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) (m : Levi k (fun a => Fin (d a))) :
    blockScalar hc C * m = m * blockScalar hc C := by
  funext a
  refine Units.ext ?_
  show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) * (m a).val =
    (m a).val * ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k))
  simp

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[dia_val]`. Use extensionality with `i j`. Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[leviEmb_apply_same]`. Use `show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _`. Distinguish the cases in `h2 : i' = j'`.

Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.smul_apply, one_apply_ne h2, smul_zero, diagonal_apply_ne]`. Simplify using `using h2`. Rewrite using `[leviEmb_apply_ne k e _ h, diagonal_apply_ne]`.

Conclude with `fun h' => h (congrArg Sigma.fst (e.injective h'))`.
-/
theorem leviEmb_blockScalar {n : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {c : k} (hc : c ≠ 0)
    (C : Fin s → ℕ) : leviEmb k e (blockScalar hc C) = dia e hc C := by
  refine Units.ext ?_
  rw [dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
    by_cases h2 : i' = j'
    · subst h2
      simp
    · rw [Matrix.smul_apply, one_apply_ne h2, smul_zero, diagonal_apply_ne]
      simpa using h2
  · rw [leviEmb_apply_ne k e _ h, diagonal_apply_ne]
    exact fun h' => h (congrArg Sigma.fst (e.injective h'))

/- English proof (translation)
Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le h`. Establish `e1 : (c ^ A)⁻¹ * x * c ^ (A + N + r) = c ^ N * (x * c ^ r)`. Rewrite using `[pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_mul, map_mul, map_pow, map_pow]`.

Conclude with `mul_le_of_le_one_right' (mul_le_one' hx (pow_le_one' hv r))`.
-/
theorem valuation_conj_le {c x : k} (hc : c ≠ 0) (hv : valuation k c ≤ 1) (hx : valuation k x ≤ 1)
    {A B N : ℕ} (h : A + N ≤ B) : valuation k ((c ^ A)⁻¹ * x * c ^ B) ≤ valuation k c ^ N := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : (c ^ A)⁻¹ * x * c ^ (A + N + r) = c ^ N * (x * c ^ r) := by
    rw [pow_add, pow_add]
    field_simp
  rw [e1, map_mul, map_mul, map_pow, map_pow]
  exact mul_le_of_le_one_right' (mul_le_one' hx (pow_le_one' hv r))

/- English proof (translation)
Establish `h1 : (b : ℕ) < a` using `h`. Establish `h2 : (a : ℕ) < s` using `a.2`. Simplify using `only [expo]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem expo_gap {s : ℕ} (N : ℕ) {a b : Fin s} (h : b < a) : expo s N a + N ≤ expo s N b := by
  have h1 : (b : ℕ) < a := h
  have h2 : (a : ℕ) < s := a.2
  simp only [expo]
  calc (N + 1) * (s - 1 - (a : ℕ)) + N ≤ (N + 1) * (s - 1 - (a : ℕ)) + (N + 1) := by omega
    _ = (N + 1) * (s - 1 - (a : ℕ) + 1) := by ring
    _ ≤ (N + 1) * (s - 1 - (b : ℕ)) := Nat.mul_le_mul_left _ (by omega)

end GlobalTheory.CompanionTheory.MoyPrasad
