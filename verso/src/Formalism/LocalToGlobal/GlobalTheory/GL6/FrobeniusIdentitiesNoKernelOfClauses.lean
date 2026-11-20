import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

noncomputable section

open Finset

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

/- English proof (translation)
Establish `h1 : ∑ b : kˣ, ψ (c * (b : k)) = ∑ b : kˣ, ψ (b : k)`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 c hc)) _ _ (fun b => by simp)`. Rewrite using `[h1]`. Establish `h2 : ∑ x : k, ψ x = 0` using `AddChar.sum_eq_zero_of_ne_one hψ`. Establish `h3 : ∑ x : k, ψ x = ψ 0 + ∑ b : kˣ, ψ (b : k)`.

Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]`. Use `congr 1`. Use `Finset.sum_bij' (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx)) (fun b _ => (b : k)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `intros`. Conclude with `Finset.mem_univ _`.

Introduce `b _`. Simplify using the standard rewrite rules. Introduce `x hx`. Simplify using the standard rewrite rules. Introduce `b _`.

Simplify using the standard rewrite rules. Introduce `x hx`. Simplify using the standard rewrite rules. Rewrite `h2` using `[h3, AddChar.map_zero_eq_one]`. Take the linear combination `h2`.
-/
theorem sum_units_addChar_mul {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : k) (hc : c ≠ 0) : ∑ b : kˣ, ψ (c * (b : k)) = -1 := by
  have h1 : ∑ b : kˣ, ψ (c * (b : k)) = ∑ b : kˣ, ψ (b : k) := by
    exact Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 c hc)) _ _ (fun b => by simp)
  rw [h1]
  have h2 : ∑ x : k, ψ x = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have h3 : ∑ x : k, ψ x = ψ 0 + ∑ b : kˣ, ψ (b : k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
    congr 1
    refine Finset.sum_bij' (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx)) (fun b _ => (b : k)) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro b _; simp
    · intro x hx; simp
    · intro b _; simp
    · intro x hx; simp
  rw [h3, AddChar.map_zero_eq_one] at h2
  linear_combination h2

/- English proof (translation)
Establish `e : ∀ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) = ψ (((c : k) - 1) * (b : k))`. Introduce `b`. Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Distinguish the cases in `hc : c = 1`. Substitute `hc` using the available equality. Simplify using `only [Units.val_one, sub_self, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, Fintype.card_units, if_true, mul_one, nsmul_eq_mul]`. Establish `: 1 ≤ Fintype.card k` using `Fintype.card_pos`.

Move the coercions through the operations in `[Nat.cast_sub this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc' : (c : k) - 1 ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Use `ext`. Simplify `h` using `[sub_eq_zero]`. Rewrite using `[sum_units_addChar_mul ψ hψ _ hc', if_neg hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_units_gauss_coeff {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : kˣ) : ∑ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) =
      (Fintype.card k : ℂ) * (if c = 1 then 1 else 0) - 1 := by
  have e : ∀ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) = ψ (((c : k) - 1) * (b : k)) := by
    intro b; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp only [e]
  by_cases hc : c = 1
  · subst hc
    simp only [Units.val_one, sub_self, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_units, if_true, mul_one, nsmul_eq_mul]
    have : 1 ≤ Fintype.card k := Fintype.card_pos
    push_cast [Nat.cast_sub this]
    ring
  · have hc' : (c : k) - 1 ≠ 0 := by
      intro h; apply hc; ext; simpa [sub_eq_zero] using h
    rw [sum_units_addChar_mul ψ hψ _ hc', if_neg hc]; ring

variable (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)

/- English proof (translation)
Introduce `i hi v φ hφ`. Take `⟨h1, hm⟩` from `h i hi v φ hφ`. Use `set ψ := (D.mem u).A.psiT v with hψdef`. Establish `hψ : ψ ≠ 1` using `(D.mem u).A.psiT_ne v`. Establish `step1 : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) = ∑ a : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ, (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_fi …`.

Simplify using `only [Formalism.MainNotions.product_first_zeroth_parts.Gs, Formalism.MainNotions.product_first_zeroth_parts.GsD, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[hm a b⁻¹, mul_comm]`. Establish `step2 : ∀ b : ((D.mem u).A.Fv v)ˣ, ∑ a : ((D.mem u).A.Fv v)ˣ, (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ = ∑ c : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) * ψ …`.

Introduce `b`. Use `(Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun c => ?_)).symm` and prove the remaining obligations. Simplify using `[mul_assoc]`. Establish `step3 : ∀ c : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ = (((Fintype.card ((D.mem u).A.Fv v) : ℂ) * (if c = 1 then 1 else 0 …`. Introduce `c`.

Rewrite using `[← Finset.sum_smul, sum_units_gauss_coeff ψ hψ, sub_smul, one_smul]`. Rewrite using `[step1, Finset.sum_comm, Finset.sum_congr rfl (fun b _ => step2 b), Finset.sum_comm, Finset.sum_congr rfl (fun c _ => step3 c), Finset.sum_sub_distrib, Fintype.sum_eq_single 1 (fun c hc => by simp [hc])]`. Simplify using `only [if_true, mul_one, h1, (D.mem u).A.card_Fv v, Formalism.MainNotions.product_first_zeroth_parts.Nm, LinearMap.sum_apply]`.
-/
theorem gs_gsD_of_diaMul (h : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
      Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ := by
  intro i hi v φ hφ
  obtain ⟨h1, hm⟩ := h i hi v φ hφ
  set ψ := (D.mem u).A.psiT v with hψdef
  have hψ : ψ ≠ 1 := (D.mem u).A.psiT_ne v
  have step1 : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) =
      ∑ a : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ,
        (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ := by
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Gs, Formalism.MainNotions.product_first_zeroth_parts.GsD, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hm a b⁻¹, mul_comm]
  have step2 : ∀ b : ((D.mem u).A.Fv v)ˣ,
      ∑ a : ((D.mem u).A.Fv v)ˣ, (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) •
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ =
      ∑ c : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ := by
    intro b
    refine (Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun c => ?_)).symm
    simp [mul_assoc]
  have step3 : ∀ c : ((D.mem u).A.Fv v)ˣ,
      ∑ b : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ =
      (((Fintype.card ((D.mem u).A.Fv v) : ℂ) * (if c = 1 then 1 else 0)) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ -
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ) := by
    intro c
    rw [← Finset.sum_smul, sum_units_gauss_coeff ψ hψ, sub_smul, one_smul]
  rw [step1, Finset.sum_comm, Finset.sum_congr rfl (fun b _ => step2 b), Finset.sum_comm,
    Finset.sum_congr rfl (fun c _ => step3 c), Finset.sum_sub_distrib,
    Fintype.sum_eq_single 1 (fun c hc => by simp [hc])]
  simp only [if_true, mul_one, h1, (D.mem u).A.card_Fv v, Formalism.MainNotions.product_first_zeroth_parts.Nm, LinearMap.sum_apply]

/- English proof (translation)
Establish `key : ∀ l : List (D.mem u).A.vT, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, (l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) φ ∈ …`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro φ hφ ψ _`. Simplify using `[hφ]`.

Consider the case `cons v l ih`. Introduce `φ hφ ψ hψ`. Take `⟨h1, h2⟩` from `ih φ hφ ψ hψ`. Take `⟨h3, _⟩` from `ih ψ hψ ψ hψ`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [List.foldr_cons, LinearMap.comp_apply]`. Conclude with `hc v _ h1`. Simplify using `only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]`. Rewrite using `[hd v _ h1 _ h3, h2, ← mul_assoc, ← pow_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Introduce `φ hφ ψ hψ`. Use `(key (Finset.univ : Finset (D.mem u).A.vT).toList φ hφ ψ hψ).2` as an intermediate fact. Rewrite `this` using `[Finset.length_toList, Finset.card_univ, (D.mem u).A.card_vT]`. Conclude with `this`.
-/
theorem ffAll_iso_of (i : ℕ)
    (hc : ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (hd : ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ) :
    ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFall D u i φ) (Formalism.MainNotions.product_first_zeroth_parts.FFall D u i ψ) =
        ((D.mem u).A.T : ℂ) ^ (D.R.f * D.R.N i) * (D.fm u).ipC i φ ψ := by
  have key : ∀ l : List (D.mem u).A.vT, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i ∧
      (D.fm u).ipC i ((l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) φ)
          ((l.foldr (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v).comp g) LinearMap.id) ψ) =
        ((D.mem u).A.T : ℂ) ^ (l.length * D.R.N i) * (D.fm u).ipC i φ ψ := by
    intro l
    induction l with
    | nil => intro φ hφ ψ _; simp [hφ]
    | cons v l ih =>
      intro φ hφ ψ hψ
      obtain ⟨h1, h2⟩ := ih φ hφ ψ hψ
      obtain ⟨h3, _⟩ := ih ψ hψ ψ hψ
      refine ⟨?_, ?_⟩
      · simp only [List.foldr_cons, LinearMap.comp_apply]; exact hc v _ h1
      · simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
        rw [hd v _ h1 _ h3, h2, ← mul_assoc, ← pow_add]
        congr 2; ring
  intro φ hφ ψ hψ
  have := (key (Finset.univ : Finset (D.mem u).A.vT).toList φ hφ ψ hψ).2
  rw [Finset.length_toList, Finset.card_univ, (D.mem u).A.card_vT] at this
  exact this

/- English proof (translation)
Assemble the required witnesses or components as `⟨h7a, gs_gsD_of_diaMul D u hD, h7c, h7d, fun i hi => ffAll_iso_of D u i (h7c i hi) (h7d i hi)⟩`.
-/
theorem frobenius_identities_no_kernel_of_clauses
    (h7a : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ))
    (h7c : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (h7d : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ)
    (hD : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u) : FrobeniusOperatorRelations D u :=
  ⟨h7a, gs_gsD_of_diaMul D u hD, h7c, h7d,
    fun i hi => ffAll_iso_of D u i (h7c i hi) (h7d i hi)⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
