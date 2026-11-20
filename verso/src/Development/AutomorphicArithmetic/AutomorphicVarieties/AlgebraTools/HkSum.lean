import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkFaith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualExp

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Introduce `R _ _ n q H _ _ b hb ι _ a c hd`. Set `S : H → Prop` to `fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R, ∑ u, b.th (e u) * b.T u = h`. Establish `S_zero : S 0` using `⟨0, by simp⟩`. Establish `S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂)`. Introduce and unpack `h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩`.

Use `⟨e₁ + e₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Simplify using `[add_mul]`. Establish `S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂)`.

Introduce and unpack `h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩`. Use `⟨e₁ - e₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Simplify using `[sub_mul]`.

Establish `S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k)` using `fun s f hf => Finset.sum_induction f S S_add S_zero hf`. Establish `S_th : ∀ x, S (b.th x)`. Introduce `x`. Use `⟨fun u => if u = 1 then x else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (1 : Perm (Fin n))]`.

Simplify using `[b.T_one]`. Introduce `u _ hu`. Simplify using `[hu]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `S_T : ∀ w h, S h → S (b.T w * h)`. Introduce and unpack `w h ⟨e, rfl⟩`. Take `⟨e', he'⟩` from `UpperTheory.V.AlgebraTools.hkSpan R n q H b w e`. Conclude with `⟨e', he'.symm⟩`. Establish `S_thmul : ∀ x h, S h → S (b.th x * h)`.

Introduce and unpack `x h ⟨e, rfl⟩`. Use `⟨fun u => x * e u, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc]`.

Establish `hE : S (∑ i, b.th (a i) * b.one * b.th (c i))`. Use `S_sum _ _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, Bern.one, Finset.sum_mul]`. Conclude with `S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))`. Take `⟨e, he⟩` from `S_sub _ _ hE (S_th (NN n q))`.

Establish `hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one = b.th (NN n q * x) * b.one`. Introduce `x`. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Establish `step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one = b.th (a i * dd (c i * (NN n q * x))) * b.one`. Introduce `i`.

Establish `hs` using `UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Simplify using `only [mul_assoc]`. Use `_ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]`.

Use `_ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by`. Rewrite using `[map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]`. Rewrite using `[Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum, (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]`. Establish `he0` using `UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by`. Rewrite using `[he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])`.

Rewrite `he` using `[he0]`. Simplify using `only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he`. Conclude with `(sub_eq_zero.mp he.symm)`.
-/
theorem UpperTheory.V.AlgebraTools.hkSum :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) R), IsDual a c →
      ∑ i, b.th (a i) * b.one * b.th (c i) = b.th (NN n q) := by
  intro R _ _ n q H _ _ b hb ι _ a c hd
  classical
  let S : H → Prop := fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R,
    ∑ u, b.th (e u) * b.T u = h
  have S_zero : S 0 := ⟨0, by simp⟩
  have S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ + e₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [add_mul]
  have S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ - e₂, ?_⟩
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sub_mul]
  have S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k) :=
    fun s f hf => Finset.sum_induction f S S_add S_zero hf
  have S_th : ∀ x, S (b.th x) := by
    intro x
    refine ⟨fun u => if u = 1 then x else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Perm (Fin n))]
    · simp [b.T_one]
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have S_T : ∀ w h, S h → S (b.T w * h) := by
    rintro w h ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := UpperTheory.V.AlgebraTools.hkSpan R n q H b w e
    exact ⟨e', he'.symm⟩
  have S_thmul : ∀ x h, S h → S (b.th x * h) := by
    rintro x h ⟨e, rfl⟩
    refine ⟨fun u => x * e u, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, mul_assoc]
  have hE : S (∑ i, b.th (a i) * b.one * b.th (c i)) := by
    refine S_sum _ _ fun i _ => ?_
    rw [mul_assoc, Bern.one, Finset.sum_mul]
    exact S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))
  obtain ⟨e, he⟩ := S_sub _ _ hE (S_th (NN n q))
  have hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one
      = b.th (NN n q * x) * b.one := by
    intro x
    rw [Finset.sum_mul, Finset.sum_mul]
    have step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one
        = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
      intro i
      have hs := UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)
      calc b.th (a i) * b.one * b.th (c i) * b.th x * b.one
          = b.th (a i) * (b.one * b.th (c i * x) * b.one) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]
        _ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
            rw [map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum,
      (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]
  have he0 := UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by
    rw [he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])
  rw [he0] at he
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.mp he.symm)
