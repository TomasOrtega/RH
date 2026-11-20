import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

def vG {σ : Type} (F : MvPolynomial σ K) : WithTop ℚ := F.support.inf fun α => v (F.coeff α)

variable {v}
variable {σ τ : Type}

/- English proof (translation)
Unfold `vG`. Rewrite using `[Finset.le_inf_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h α`. Distinguish the cases in `hα : α ∈ F.support`.

Conclude with `h α hα`. Rewrite using `[notMem_support_iff.mp hα, AddValuation.map_zero]`. Conclude with `le_top`. Introduce `h α _`. Conclude with `h α`.
-/
theorem le_vG_iff (F : MvPolynomial σ K) (n : WithTop ℚ) :
    n ≤ vG v F ↔ ∀ α, n ≤ v (F.coeff α) := by
  unfold vG
  rw [Finset.le_inf_iff]
  constructor
  · intro h α
    by_cases hα : α ∈ F.support
    · exact h α hα
    · rw [notMem_support_iff.mp hα, AddValuation.map_zero]; exact le_top
  · intro h α _; exact h α

/- English proof (translation)
The claim follows from `(le_vG_iff F _).mp le_rfl α`.
-/
theorem vG_le_coeff (F : MvPolynomial σ K) (α : σ →₀ ℕ) : vG v F ≤ v (F.coeff α) :=
  (le_vG_iff F _).mp le_rfl α

/- English proof (translation)
The claim follows from `(le_vG_iff F 0).symm`.
-/
theorem integral_iff (F : MvPolynomial σ K) : Integral v F ↔ 0 ≤ vG v F :=
  (le_vG_iff F 0).symm

/- English proof (translation)
Simplify using `[vG]`.
-/
theorem vG_zero : vG v (0 : MvPolynomial σ K) = ⊤ := by
  simp [vG]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `vG_le_coeff (v := v) (1 : MvPolynomial σ K) 0`. Simplify using `using h`. Rewrite using `[le_vG_iff]`. Introduce `α`.

Rewrite using `[coeff_one]`. Use `split_ifs`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem vG_one : vG v (1 : MvPolynomial σ K) = 0 := by
  classical
  apply le_antisymm
  · have h := vG_le_coeff (v := v) (1 : MvPolynomial σ K) 0
    simpa using h
  · rw [le_vG_iff]
    intro α
    rw [coeff_one]
    split_ifs
    · simp
    · simp

/- English proof (translation)
Establish `hne : F.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hF (support_eq_empty.mp h)`. Take `⟨α, hα, h⟩` from `Finset.exists_mem_eq_inf F.support hne fun α => v (F.coeff α)`.

Conclude with `⟨α, hα, h.symm⟩`.
-/
theorem exists_coeff_eq_vG (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ α ∈ F.support, v (F.coeff α) = vG v F := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hF (support_eq_empty.mp h)
  obtain ⟨α, hα, h⟩ := Finset.exists_mem_eq_inf F.support hne fun α => v (F.coeff α)
  exact ⟨α, hα, h.symm⟩

/- English proof (translation)
Take `⟨α, hα, h⟩` from `exists_coeff_eq_vG (v := v) F hF`. Rewrite using `[← h]`. Introduce `ht`. Conclude with `(mem_support_iff.mp hα) ((AddValuation.top_iff v).mp ht)`.
-/
theorem vG_ne_top (F : MvPolynomial σ K) (hF : F ≠ 0) : vG v F ≠ ⊤ := by
  obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
  rw [← h]
  intro ht
  exact (mem_support_iff.mp hα) ((AddValuation.top_iff v).mp ht)

/- English proof (translation)
Rewrite using `[le_vG_iff]`. Introduce `γ`. Rewrite using `[coeff_mul]`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `x _`.

Rewrite using `[AddValuation.map_mul]`. Conclude with `add_le_add (vG_le_coeff F _) (vG_le_coeff G _)`.
-/
theorem vG_add_vG_le_vG_mul (F G : MvPolynomial σ K) : vG v F + vG v G ≤ vG v (F * G) := by
  classical
  rw [le_vG_iff]
  intro γ
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_le_add (vG_le_coeff F _) (vG_le_coeff G _)

/- English proof (translation)
Take `⟨lo, wf⟩` from `exists_wellFoundedLT σ`. Set `_ : LinearOrder σ` to `@OrderDual.instLinearOrder σ lo`. Establish `: WellFoundedGT σ` using `⟨wf.wf⟩`. Conclude with `⟨MonomialOrder.lex⟩`.
-/
theorem exists_monomialOrder (σ : Type) : Nonempty (MonomialOrder.{0, 0} σ) := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT σ
  let _ : LinearOrder σ := @OrderDual.instLinearOrder σ lo
  have : WellFoundedGT σ := ⟨wf.wf⟩
  exact ⟨MonomialOrder.lex⟩

/- English proof (translation)
Distinguish the cases in `hF : F = 0`. Simplify using `[hF, vG_zero]`. Distinguish the cases in `hG : G = 0`. Simplify using `[hG, vG_zero]`. Use `le_antisymm ?_ (vG_add_vG_le_vG_mul F G)` and prove the remaining obligations.

Take `⟨m⟩` from `exists_monomialOrder σ`. Establish `haT` using `vG_ne_top (v := v) F hF`. Establish `hbT` using `vG_ne_top (v := v) G hG`. Use `set SF := F.support.filter fun α => v (F.coeff α) = vG v F with hSF`. Use `set SG := G.support.filter fun α => v (G.coeff α) = vG v G with hSG`.

Establish `hSFne : SF.Nonempty`. Take `⟨α, hα, h⟩` from `exists_coeff_eq_vG (v := v) F hF`. Conclude with `⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩`. Establish `hSGne : SG.Nonempty`. Take `⟨α, hα, h⟩` from `exists_coeff_eq_vG (v := v) G hG`.

Conclude with `⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩`. Take `⟨α0, hα0, hαmin⟩` from `Finset.exists_min_image SF m.toSyn hSFne`. Take `⟨β0, hβ0, hβmin⟩` from `Finset.exists_min_image SG m.toSyn hSGne`. Establish `hα0v : v (F.coeff α0) = vG v F` using `(Finset.mem_filter.mp hα0).2`. Establish `hβ0v : v (G.coeff β0) = vG v G` using `(Finset.mem_filter.mp hβ0).2`.

Establish `hmem : (α0, β0) ∈ antidiagonal (α0 + β0)` using `by simp`. Establish `hrest : vG v F + vG v G < v (∑ x ∈ (antidiagonal (α0 + β0)).erase (α0, β0), F.coeff x.1 * G.coeff x.2)`. Apply `AddValuation.map_lt_sum` to reduce the goal to its premises. Conclude with `WithTop.add_ne_top.mpr ⟨haT, hbT⟩`. Introduce `x hx`.

Take `⟨hxne, hxa⟩` from `Finset.mem_erase.mp hx`. Establish `hsum : x.1 + x.2 = α0 + β0` using `by simpa using hxa`. Rewrite using `[AddValuation.map_mul]`. Break down `lt_or_eq_of_le (vG_le_coeff (v := v) F x.1) with h1 | h1` into its components or cases. Conclude with `WithTop.add_lt_add_of_lt_of_le hbT h1 (vG_le_coeff G x.2)`.

Break down `lt_or_eq_of_le (vG_le_coeff (v := v) G x.2) with h2 | h2` into its components or cases. Conclude with `WithTop.add_lt_add_of_le_of_lt haT (vG_le_coeff F x.1) h2`. It suffices to derive a contradiction. Establish `hx1 : x.1 ∈ SF`. Use `Finset.mem_filter.mpr ⟨?_, h1.symm⟩` and prove the remaining obligations.

Rewrite using `[mem_support_iff]`. Introduce `h0`. Rewrite `h1` using `[h0, AddValuation.map_zero]`. Conclude with `haT h1`. Establish `hx2 : x.2 ∈ SG`.

Use `Finset.mem_filter.mpr ⟨?_, h2.symm⟩` and prove the remaining obligations. Rewrite using `[mem_support_iff]`. Introduce `h0`. Rewrite `h2` using `[h0, AddValuation.map_zero]`. Conclude with `hbT h2`.

Establish `l1` using `hαmin x.1 hx1`. Establish `l2` using `hβmin x.2 hx2`. Establish `hs : m.toSyn x.1 + m.toSyn x.2 = m.toSyn α0 + m.toSyn β0`. Rewrite using `[← map_add, ← map_add, hsum]`. Establish `e1 : m.toSyn x.1 = m.toSyn α0`.

Break down `lt_or_eq_of_le l1 with h | h` into its components or cases. Conclude with `absurd hs (ne_of_gt (add_lt_add_of_lt_of_le h l2))`. Conclude with `h.symm`. Establish `e2 : m.toSyn x.2 = m.toSyn β0`. Rewrite `hs` using `[e1]`.

Conclude with `add_left_cancel hs`. Conclude with `hxne (Prod.ext (m.toSyn.injective e1) (m.toSyn.injective e2))`. Establish `hc : v ((F * G).coeff (α0 + β0)) = vG v F + vG v G`. Rewrite using `[coeff_mul, ← Finset.add_sum_erase _ _ hmem]`. Establish `h0 : v (F.coeff α0 * G.coeff β0) = vG v F + vG v G`.

Rewrite using `[AddValuation.map_mul, hα0v, hβ0v]`. Rewrite `hrest`, the goal using `[← h0]`. Conclude with `AddValuation.map_add_eq_of_lt_left v hrest`. Rewrite using `[← hc]`. Conclude with `vG_le_coeff _ _`.
-/
theorem vG_mul (F G : MvPolynomial σ K) : vG v (F * G) = vG v F + vG v G := by
  classical
  by_cases hF : F = 0
  · simp [hF, vG_zero]
  by_cases hG : G = 0
  · simp [hG, vG_zero]
  refine le_antisymm ?_ (vG_add_vG_le_vG_mul F G)
  obtain ⟨m⟩ := exists_monomialOrder σ
  have haT := vG_ne_top (v := v) F hF
  have hbT := vG_ne_top (v := v) G hG
  set SF := F.support.filter fun α => v (F.coeff α) = vG v F with hSF
  set SG := G.support.filter fun α => v (G.coeff α) = vG v G with hSG
  have hSFne : SF.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  have hSGne : SG.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) G hG
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  obtain ⟨α0, hα0, hαmin⟩ := Finset.exists_min_image SF m.toSyn hSFne
  obtain ⟨β0, hβ0, hβmin⟩ := Finset.exists_min_image SG m.toSyn hSGne
  have hα0v : v (F.coeff α0) = vG v F := (Finset.mem_filter.mp hα0).2
  have hβ0v : v (G.coeff β0) = vG v G := (Finset.mem_filter.mp hβ0).2
  have hmem : (α0, β0) ∈ antidiagonal (α0 + β0) := by simp
  have hrest : vG v F + vG v G <
      v (∑ x ∈ (antidiagonal (α0 + β0)).erase (α0, β0), F.coeff x.1 * G.coeff x.2) := by
    apply AddValuation.map_lt_sum
    · exact WithTop.add_ne_top.mpr ⟨haT, hbT⟩
    intro x hx
    obtain ⟨hxne, hxa⟩ := Finset.mem_erase.mp hx
    have hsum : x.1 + x.2 = α0 + β0 := by simpa using hxa
    rw [AddValuation.map_mul]
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) F x.1) with h1 | h1
    · exact WithTop.add_lt_add_of_lt_of_le hbT h1 (vG_le_coeff G x.2)
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) G x.2) with h2 | h2
    · exact WithTop.add_lt_add_of_le_of_lt haT (vG_le_coeff F x.1) h2
    exfalso
    have hx1 : x.1 ∈ SF := by
      refine Finset.mem_filter.mpr ⟨?_, h1.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h1; exact haT h1
    have hx2 : x.2 ∈ SG := by
      refine Finset.mem_filter.mpr ⟨?_, h2.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h2; exact hbT h2
    have l1 := hαmin x.1 hx1
    have l2 := hβmin x.2 hx2
    have hs : m.toSyn x.1 + m.toSyn x.2 = m.toSyn α0 + m.toSyn β0 := by
      rw [← map_add, ← map_add, hsum]
    have e1 : m.toSyn x.1 = m.toSyn α0 := by
      rcases lt_or_eq_of_le l1 with h | h
      · exact absurd hs (ne_of_gt (add_lt_add_of_lt_of_le h l2))
      · exact h.symm
    have e2 : m.toSyn x.2 = m.toSyn β0 := by
      rw [e1] at hs; exact add_left_cancel hs
    exact hxne (Prod.ext (m.toSyn.injective e1) (m.toSyn.injective e2))
  have hc : v ((F * G).coeff (α0 + β0)) = vG v F + vG v G := by
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have h0 : v (F.coeff α0 * G.coeff β0) = vG v F + vG v G := by
      rw [AddValuation.map_mul, hα0v, hβ0v]
    rw [← h0] at hrest ⊢
    exact AddValuation.map_add_eq_of_lt_left v hrest
  rw [← hc]
  exact vG_le_coeff _ _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [vG_one]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vG_mul, ih]`.
-/
theorem vG_prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    vG v (∏ k ∈ s, f k) = ∑ k ∈ s, vG v (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vG_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vG_mul, ih]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_vG_iff]`. Introduce `α`. Rewrite using `[← coeff_rename_mapDomain f hf F α]`. Conclude with `vG_le_coeff _ _`.

Rewrite using `[le_vG_iff]`. Introduce `β`. Distinguish the cases in `h : ∃ u : σ →₀ ℕ, u.mapDomain f = β`. Take `⟨u, rfl⟩` from `h`. Rewrite using `[coeff_rename_mapDomain f hf]`.

Conclude with `vG_le_coeff _ _`. Rewrite using `[coeff_rename_eq_zero f F β (fun u hu => absurd ⟨u, hu⟩ h), AddValuation.map_zero]`. Conclude with `le_top`.
-/
theorem vG_rename (f : σ → τ) (hf : Function.Injective f) (F : MvPolynomial σ K) :
    vG v (rename f F) = vG v F := by
  classical
  apply le_antisymm
  · rw [le_vG_iff]
    intro α
    rw [← coeff_rename_mapDomain f hf F α]
    exact vG_le_coeff _ _
  · rw [le_vG_iff]
    intro β
    by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
    · obtain ⟨u, rfl⟩ := h
      rw [coeff_rename_mapDomain f hf]
      exact vG_le_coeff _ _
    · rw [coeff_rename_eq_zero f F β (fun u hu => absurd ⟨u, hu⟩ h), AddValuation.map_zero]
      exact le_top

/- English proof (translation)
Rewrite `h`, the goal using `[integral_iff]`. Rewrite `h`, the goal using `[vG_prod]`. Simplify `h` using `only [vG_rename _ (hf _)]`.
-/
theorem integral_prod_rename {ι : Type} [Fintype ι] (col : ι → MvPolynomial σ K) (f : ι → σ → τ)
    (hf : ∀ k, Function.Injective (f k)) (h : Integral v (∏ k, col k)) :
    Integral v (∏ k, rename (f k) (col k)) := by
  rw [integral_iff] at h ⊢
  rw [vG_prod] at h ⊢
  simpa only [vG_rename _ (hf _)] using h

end Formalism.MainNotions.PlaneGram
