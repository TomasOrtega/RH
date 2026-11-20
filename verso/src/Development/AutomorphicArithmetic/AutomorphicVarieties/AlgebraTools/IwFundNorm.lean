import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨p, hp, e⟩` from `hx`. Establish `hI` using `Valuation.integer.integers (valuation k)`. Establish `h1 : valuation k (x : k) < 1`. Rewrite using `[← e]`. Use `lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)` and prove the remaining obligations.

Use `⟨fun h => ?_, fun h => h.trans_lt h1⟩` and prove the remaining obligations. Set `z : 𝒪[k]` to `⟨y, h.le⟩`. Establish `hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k]` using `fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)`. Rewrite `hz` using `[hp.maximalIdeal_eq, Ideal.mem_span_singleton]`. Rewrite using `[← e]`.

Conclude with `hI.le_of_dvd hz`.
-/
private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

/- English proof (translation)
Establish `h1 : valuation k (x : k) ≤ 1` using `((unif_lt hx x).2 le_rfl).le`. Establish `A : ∀ g ∈ iwahori k (Fin n), Bd x g`. Introduce `g hg i j`. Establish `hg'` using `mem_iwahori.1 hg`. Use `split_ifs with h`.

Simplify using `using (unif_lt hx _).1 (hg'.2 i j h)`. Rewrite using `[zpow_zero]`. Conclude with `((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j`. Establish `B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1`. Introduce `g hg i j`.

Use `hg i j` as an intermediate fact. Use `split_ifs at this with h`. Conclude with `le_trans (by simpa using this) h1`. Simplify using `using this`. Use `⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩` and prove the remaining obligations.

Simplify `ha i j` using `[h]`.
-/
private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

/- English proof (translation)
Establish `e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ = pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹`. Rewrite using `[map_inv, map_inv, pw]`. Use `group`. Rewrite using `[e]`. Simplify using `only [Units.val_mul, pw, val_diagT]`.

Generalize the expression as in `hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) * diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M`. Establish `hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j`. Rewrite using `[← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]`. Simplify using `only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hM']`. Simplify using `only [Matrix.mul_apply, pm_apply]`. Simplify using the standard rewrite rules.
-/
private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

/- English proof (translation)
Establish `h0 : 0 < valuation k (x : k)` using `zero_lt_iff.2 (by simp)`. Unfold `Bd`. Rewrite using `[w.surjective.forall₂]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Rewrite using `[conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]`.
-/
private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

/- English proof (translation)
Set `f : Fin n → Fin n` to `fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by`. Apply the tactic sequence `have := i.2; split_ifs <;> omega⟩`. Establish `hf : Function.Injective f`. Introduce `i j h`. Establish `h'` using `congrArg Fin.val h`.

Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [f] at h'`. Use `ext`. Apply the tactic sequence `split_ifs at h' <;> omega`.

Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩` and prove the remaining obligations. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `k _ _ _ _ n C x hx m hm`. Take `⟨w, hw⟩` from `exists_rot n m hm`. Use `⟨w, Subgroup.mem_normalizer_iff.2 fun g => ?_⟩` and prove the remaining obligations. Establish `e : (pm k n w * pw x (fund n m) * g * (pm k n w * pw x (fund n m))⁻¹)⁻¹ = pm k n w * pw x (fund n m) * g⁻¹ * (pm k n w * pw x (fund n m))⁻¹` using `by group`. Rewrite using `[(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]`.

Use `and_congr Iff.rfl ?_` and prove the remaining obligations. Use `conv_rhs => rw [w.surjective.forall]`. Simplify using `only [conj_entry, sub_self, zpow_zero, one_mul]`.
-/
theorem UpperTheory.V.AlgebraTools.fundNorm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ m ≤ n, ∃ w : Equiv.Perm (Fin n), pm k n w * pw x (fund n m) ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n C x hx m hm
  obtain ⟨w, hw⟩ := exists_rot n m hm
  refine ⟨w, Subgroup.mem_normalizer_iff.2 fun g => ?_⟩
  have e : (pm k n w * pw x (fund n m) * g * (pm k n w * pw x (fund n m))⁻¹)⁻¹ =
      pm k n w * pw x (fund n m) * g⁻¹ * (pm k n w * pw x (fund n m))⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]
