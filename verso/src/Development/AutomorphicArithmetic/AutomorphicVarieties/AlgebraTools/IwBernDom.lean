import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Establish `h : ∀ s : Fin n → kˣ, (diagT k (Fin n) s : Matrix (Fin n) (Fin n) k) = diagonal (fun a => (s a : k))` using `fun _ => val_diagT ..`. Rewrite using `[Units.val_mul, Units.val_mul, h, h, diagonal_mul, mul_diagonal, pm_apply]`. Use `split_ifs with hab`.

Rewrite using `[hab, mul_comm]`. Simplify using the standard rewrite rules.
-/
private theorem pm_diagT {k : Type} [Field k] {n : ℕ} (w : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    diagT k (Fin n) t * pm k n w = pm k n w * diagT k (Fin n) (fun a => t (w a)) := by
  apply Units.ext
  ext a b
  have h : ∀ s : Fin n → kˣ, (diagT k (Fin n) s : Matrix (Fin n) (Fin n) k) = diagonal (fun a => (s a : k)) :=
    fun _ => val_diagT ..
  rw [Units.val_mul, Units.val_mul, h, h, diagonal_mul, mul_diagonal, pm_apply]
  split_ifs with hab
  · rw [hab, mul_comm]
  · simp

/- English proof (translation)
Take `⟨p, -, hp⟩` from `hx`. Establish `h1 : valuation k (x : k) ≤ 1` using `by rw [← hp]; exact p.2`. Introduce `a b hab`. Establish `: (a : ℕ) ≤ b` using `hab`. Simplify using `only [fund]`.

Use `split_ifs with ha hb hb`. Conclude with `le_rfl`. Simplify using `using h1`. Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`.
-/
private theorem dom_fund {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {x : kˣ} (hx : IsUnif x) (m : ℕ) : Dom (fun a : Fin n => x ^ fund n m a) := by
  obtain ⟨p, -, hp⟩ := hx
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  intro a b hab
  have : (a : ℕ) ≤ b := hab
  simp only [fund]
  split_ifs with ha hb hb
  · exact le_rfl
  · simpa using h1
  · omega
  · exact le_rfl

/- English proof (translation)
Introduce `k _ _ _ _ n A M _ _ _ ρ x hx i j hij`. Take `⟨F, -, hs, hd, hy⟩` from `factBlock k n ⊤ i j hij`. Take `⟨hyP, hyN⟩` from `hy x hx`. Establish `hH` using `(heckePairIwC k n ⊤).1`. Establish `hss : pm k n (Equiv.swap i j) * pm k n (Equiv.swap i j) = 1`.

Rewrite using `[← map_mul, Equiv.swap_mul_self, map_one]`. Use `⟨fun t ht hv => ?_, hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j) * pw x (fund n j)), ?_, ?_⟩` and prove the remaining obligations. Take `⟨hP, hN⟩` from `hd t ht`. Establish `h1` using `(leviMul A _ M ρ _ F _ _ hH hs hP (Or.inr (hN hv))).2`. Establish `h2` using `(leviMul A _ M ρ _ F _ _ hH hP hs (Or.inl (hN hv))).2`.

Unfold `Commute SemiconjBy`. Rewrite using `[h1, h2, pm_diagT]`. Establish `hmem : diagT k (Fin n) (fun a => (t a)⁻¹ * t (Equiv.swap i j a)) ∈ iwC k n ⊤`. Use `Subgroup.mem_sup_right ⟨_, fun a _ => ?_, rfl⟩` and prove the remaining obligations. Use `((memIwC k n ⊤).2.2.2 _).2 ?_` and prove the remaining obligations.

Establish `hne : valuation k (t a : k) ≠ 0` using `by simp`. Establish `: valuation k (t (Equiv.swap i j a) : k) = valuation k (t a : k)`. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with ha hb`. Rewrite using `[ha, hv]`.

Rewrite using `[hb, hv]`. Both sides reduce to the same expression. Simplify using `[this, hne]`. Establish `h3` using `(hkApply A _ M ρ (iwC k n ⊤) (iwC k n ⊤) _ (hH (pm k n (Equiv.swap i j) * diagT k (Fin n) t))).2.2 1 (one_mem _) _ hmem`. Unfold `hk`.

Rewrite using `[← h3, one_mul, mul_assoc, ← map_mul]`. Use `congr 3`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Rewrite using `[(leviMul A _ M ρ _ F _ _ hH hs hyP (Or.inr hyN)).2, ← mul_assoc, hss, one_mul]`.

Rewrite using `[(leviMul A _ M ρ _ F _ _ hH hyP hyP (Or.inr hyN)).2]`. Unfold `pw`. Rewrite using `[(domMul k n ⊤ A M ρ).1 _ _ (dom_fund hx _) (dom_fund hx _), mul_assoc, ← mul_assoc (diagT k (Fin n) _), pm_diagT, mul_assoc, ← mul_assoc, hss, one_mul, ← map_mul]`. Use `congr 2`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.mul_apply, ← _root_.zpow_add]`. Use `congr 1`. Simplify using `only [fund, Equiv.swap_apply_def, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem UpperTheory.V.AlgebraTools.bernDom :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → ∀ (i j : Fin n), (j : ℕ) = i + 1 → (∀ t : Fin n → kˣ, Dom t → valuation k (t i : k) = valuation k (t j : k) → Commute (hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j))) (hk ρ (iwC k n ⊤) (diagT k (Fin n) t))) ∧ ∃ y : Module.End A (fixd ρ (iwC k n ⊤)), hk ρ (iwC k n ⊤) (pw x (fund n j)) = hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) * y ∧ y * y = hk ρ (iwC k n ⊤) (pw x (fund n i)) * hk ρ (iwC k n ⊤) (pw x (fund n ((j : ℕ) + 1))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx i j hij
  obtain ⟨F, -, hs, hd, hy⟩ := factBlock k n ⊤ i j hij
  obtain ⟨hyP, hyN⟩ := hy x hx
  have hH := (heckePairIwC k n ⊤).1
  have hss : pm k n (Equiv.swap i j) * pm k n (Equiv.swap i j) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  refine ⟨fun t ht hv => ?_, hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j) * pw x (fund n j)), ?_, ?_⟩
  · obtain ⟨hP, hN⟩ := hd t ht
    have h1 := (leviMul A _ M ρ _ F _ _ hH hs hP (Or.inr (hN hv))).2
    have h2 := (leviMul A _ M ρ _ F _ _ hH hP hs (Or.inl (hN hv))).2
    unfold Commute SemiconjBy
    rw [h1, h2, pm_diagT]
    have hmem : diagT k (Fin n) (fun a => (t a)⁻¹ * t (Equiv.swap i j a)) ∈ iwC k n ⊤ := by
      refine Subgroup.mem_sup_right ⟨_, fun a _ => ?_, rfl⟩
      refine ((memIwC k n ⊤).2.2.2 _).2 ?_
      have hne : valuation k (t a : k) ≠ 0 := by simp
      have : valuation k (t (Equiv.swap i j a) : k) = valuation k (t a : k) := by
        rw [Equiv.swap_apply_def]
        split_ifs with ha hb
        · rw [ha, hv]
        · rw [hb, hv]
        · rfl
      simp [this, hne]
    have h3 := (hkApply A _ M ρ (iwC k n ⊤) (iwC k n ⊤) _
      (hH (pm k n (Equiv.swap i j) * diagT k (Fin n) t))).2.2 1 (one_mem _) _ hmem
    unfold hk
    rw [← h3, one_mul, mul_assoc, ← map_mul]
    congr 3
    funext a
    simp
  · rw [(leviMul A _ M ρ _ F _ _ hH hs hyP (Or.inr hyN)).2, ← mul_assoc, hss, one_mul]
  · rw [(leviMul A _ M ρ _ F _ _ hH hyP hyP (Or.inr hyN)).2]
    unfold pw
    rw [(domMul k n ⊤ A M ρ).1 _ _ (dom_fund hx _) (dom_fund hx _), mul_assoc, ← mul_assoc (diagT k (Fin n) _),
      pm_diagT, mul_assoc, ← mul_assoc, hss, one_mul, ← map_mul]
    congr 2
    funext a
    simp only [Pi.mul_apply, ← _root_.zpow_add]
    congr 1
    simp only [fund, Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> omega
