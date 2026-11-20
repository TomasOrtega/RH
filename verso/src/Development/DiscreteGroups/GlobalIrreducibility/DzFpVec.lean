import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFpMat

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `h0 (LinearMap.ext h)`.
-/
theorem exists_ne_zero_of_ne {l : Module.Dual ℂ V} (h0 : l ≠ 0) : ∃ v, l v ≠ 0 := by
  by_contra h
  push_neg at h
  exact h0 (LinearMap.ext h)

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne_zero_of_ne h0`. Establish `e1` using `hl (u * u') (mul_mem hu hu') v`. Rewrite `e1` using `[map_mul, Module.End.mul_apply, hl u hu, hl u' hu']`. Establish `: ((ψ (superDiag (u * u')) : ℂ) - ψ (superDiag u) * ψ (superDiag u')) * l v = 0`. Rewrite using `[sub_mul, ← e1]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)`.
-/
theorem chi_mul {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) {u u' : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    (hu' : u' ∈ unipB k (Fin n)) :
    (ψ (superDiag (u * u')) : ℂ) = ψ (superDiag u) * ψ (superDiag u') := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_ne h0
  have e1 := hl (u * u') (mul_mem hu hu') v
  rw [map_mul, Module.End.mul_apply, hl u hu, hl u' hu'] at e1
  have : ((ψ (superDiag (u * u')) : ℂ) - ψ (superDiag u) * ψ (superDiag u')) * l v = 0 := by
    rw [sub_mul, ← e1]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)

/- English proof (translation)
Take `⟨v0, hv0⟩` from `exists_ne_zero_of_ne h0`. Use `⟨∑ u : unipB k (Fin n), ((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0, ?_, fun u' hu' => ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ u : unipB k (Fin n), l (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0) = l v0` using `fun u => by`. Rewrite using `[map_smul, hl _ u.2, smul_eq_mul, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]`. Rewrite using `[map_sum]`.

Simplify using `only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨1⟩).ne') hv0`. Establish `hχ : ∀ w : unipB k (Fin n), (ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ) = (ψ (superDiag u') : ℂ)⁻¹ * ψ (superDiag (w : GL (Fin n) k))` using `fun w => by`. Use `chi_mul hl h0 hu' (mul_mem (inv_mem hu') w.2)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`.

Rewrite using `[this, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]`. Both sides reduce to the same expression. Rewrite using `[map_sum, Finset.smul_sum]`. Use `set a : unipB k (Fin n) := ⟨u', hu'⟩ with ha`. Use `set F : unipB k (Fin n) → V := fun w => ((ψ (superDiag ((a⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 with hF`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Simplify using `only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Use `_ = ∑ w : unipB k (Fin n), ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 := Fintype.sum_equiv (Equiv.mulLeft a) (fun u => F (a * u)) F (fun _ => rfl)`. Use `_ = _ := by`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hχ, mul_inv, inv_inv, mul_smul]`.
-/
theorem exists_eigen [Fintype k] [DecidableEq k] {n : ℕ} {ψ : AddChar k Circle}
    {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) :
    ∃ v, l v ≠ 0 ∧ ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v := by
  classical
  obtain ⟨v0, hv0⟩ := exists_ne_zero_of_ne h0
  refine ⟨∑ u : unipB k (Fin n), ((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0, ?_, fun u' hu' => ?_⟩
  · have hterm : ∀ u : unipB k (Fin n), l (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0) = l v0 := fun u => by
      rw [map_smul, hl _ u.2, smul_eq_mul, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    rw [map_sum]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨1⟩).ne') hv0
  · have hχ : ∀ w : unipB k (Fin n), (ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
        GL (Fin n) k)) : ℂ) = (ψ (superDiag u') : ℂ)⁻¹ * ψ (superDiag (w : GL (Fin n) k)) := fun w => by
      have := chi_mul hl h0 hu' (mul_mem (inv_mem hu') w.2)
      rw [mul_inv_cancel_left] at this
      rw [this, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
      rfl
    rw [map_sum, Finset.smul_sum]
    set a : unipB k (Fin n) := ⟨u', hu'⟩ with ha
    set F : unipB k (Fin n) → V := fun w =>
      ((ψ (superDiag ((a⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 with hF
    calc ∑ u : unipB k (Fin n), ρ u' (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0)
        = ∑ u : unipB k (Fin n), (fun w : unipB k (Fin n) =>
            ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ •
              ρ w v0) (⟨u', hu'⟩ * u) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      _ = ∑ w : unipB k (Fin n), ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
            GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 := Fintype.sum_equiv (Equiv.mulLeft a) (fun u => F (a * u)) F (fun _ => rfl)
      _ = _ := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hχ, mul_inv, inv_inv, mul_smul]

/- English proof (translation)
Establish `e1 : l (ρ (u₁ * Y) v) = ψ (superDiag u₁) * l (ρ Y v)` using `by rw [map_mul, Module.End.mul_apply, hl u₁ h1]`. Establish `e2 : l (ρ (Y * u₂) v) = ψ (superDiag u₂) * l (ρ Y v)`. Rewrite using `[map_mul, Module.End.mul_apply, hv u₂ h2, map_smul, map_smul, smul_eq_mul]`. Rewrite `e1` using `[hc, e2]`. Establish `hne' : (ψ (superDiag u₁) : ℂ) ≠ ψ (superDiag u₂)` using `fun h => hne (Circle.ext h)`.

Establish `: ((ψ (superDiag u₂) : ℂ) - ψ (superDiag u₁)) * l (ρ Y v) = 0` using `by rw [sub_mul, e1, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne'.symm)`.
-/
theorem vanish_of_comm {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v) {Y u₁ u₂ : GL (Fin n) k}
    (h1 : u₁ ∈ unipB k (Fin n)) (h2 : u₂ ∈ unipB k (Fin n)) (hc : u₁ * Y = Y * u₂)
    (hne : ψ (superDiag u₁) ≠ ψ (superDiag u₂)) : l (ρ Y v) = 0 := by
  have e1 : l (ρ (u₁ * Y) v) = ψ (superDiag u₁) * l (ρ Y v) := by rw [map_mul, Module.End.mul_apply, hl u₁ h1]
  have e2 : l (ρ (Y * u₂) v) = ψ (superDiag u₂) * l (ρ Y v) := by
    rw [map_mul, Module.End.mul_apply, hv u₂ h2, map_smul, map_smul, smul_eq_mul]
  rw [hc, e2] at e1
  have hne' : (ψ (superDiag u₁) : ℂ) ≠ ψ (superDiag u₂) := fun h => hne (Circle.ext h)
  have : ((ψ (superDiag u₂) : ℂ) - ψ (superDiag u₁)) * l (ρ Y v) = 0 := by rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne'.symm)

/- English proof (translation)
Use `set S := Finset.univ.filter fun r : Fin (m + 1) => ∃ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c ≠ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c with hSdef`. Establish `hS : S.Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]`. Apply `hY` to reduce the goal to its premises.

Use extensionality with `r c`. Use `h (Finset.mem_univ r)` as an intermediate fact. Use `push_neg at this`. Rewrite using `[this c, Units.val_one]`. Establish `hr₀` using `Finset.max'_mem S hS`.

Establish `hle : ∀ r ∈ S, r ≤ S.max' hS` using `fun r hr => Finset.le_max' S r hr`. Take `⟨r₀, hr₀def⟩ : ∃ r₀, S.max' hS = r₀` from `⟨_, rfl⟩`. Rewrite `hr₀`, `hle` using `[hr₀def]`. Establish `hmax : ∀ r, r₀ < r → ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c` using `fun r hr c => by`. Assume the negation of the conclusion as `h`.

Conclude with `absurd (hle r (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, c, h⟩)) (not_le.2 hr)`. Rewrite `hr₀` using `[hSdef, Finset.mem_filter]`. Take `⟨j, hj⟩` from `hr₀.2`. Establish `hr₀last : r₀ ≠ Fin.last m` using `fun h => by rw [h] at hj; exact hj (hlast j)`. Take `⟨i, hi⟩` from `Fin.exists_castSucc_eq.2 hr₀last`.

Establish `hjle : j ≤ r₀`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hj (by rw [hlow _ _ h, Matrix.one_apply_ne (ne_of_lt h)])`. Establish `hcgt : r₀ < i.succ` using `by rw [← hi]; exact Fin.castSucc_lt_succ`.

Establish `hrow` using `hmax _ hcgt`. Establish `hcol : ∀ r, r₀ < r → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r j = 0` using `fun r hr => by`. Rewrite using `[hmax r hr j, Matrix.one_apply_ne (lt_of_le_of_lt hjle hr).ne']`. Establish `hd : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j ≠ 0` using `sub_ne_zero.2 hj`. Take `⟨s₀, hs₀⟩` from `AddChar.ne_one_iff.1 hψ`.

Establish `h1' : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) * (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j = 0` using `by rw [hcol _ hcgt, mul_zero]`. Establish `h2' : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) i.succ = 0`. Rewrite using `[Pi.single_apply, if_neg (lt_of_le_of_lt hjle hcgt).ne']`. Use `vanish_of_comm hl hv (colElt_mem _ _ h1' fun r hr => by rw [hcol r (lt_trans hcgt hr), mul_zero]) (colElt_mem _ _ h2' fun r hr => by rw [Pi.single_apply, if_neg (lt_trans (lt_of_le_of_lt hjle hcgt) hr).ne']) (colElt_comm Y i.succ j _ hrow h1' h2') ?_` and prove the remaining obligations. Rewrite using `[superDiag_colElt, superDiag_colElt, hi]`.

Establish `hsY : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) * (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j = s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) * (1 : Matri …`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsing : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) r₀ = s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) * (1 : Matrix (Fin (m + …`. Distinguish the cases in `h : r₀ = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_apply, if_neg h, Matrix.one_apply_ne h, mul_zero]`. Rewrite using `[hsY, hsing, AddChar.map_add_eq_mul]`. Introduce `h`.

Conclude with `hs₀ (by simpa using h)`.
-/
theorem vanish_lower {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) {ρ : Representation ℂ (GL (Fin (m + 1)) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin (m + 1)), ρ u v = (ψ (superDiag u) : ℂ) • v) (Y : GL (Fin (m + 1)) k)
    (hlow : ∀ r c : Fin (m + 1), r < c → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = 0)
    (hlast : ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c) (hY : Y ≠ 1) : l (ρ Y v) = 0 := by
  classical
  set S := Finset.univ.filter fun r : Fin (m + 1) =>
    ∃ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c ≠ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c with hSdef
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hY
    ext r c
    have := h (Finset.mem_univ r)
    push_neg at this
    rw [this c, Units.val_one]
  have hr₀ := Finset.max'_mem S hS
  have hle : ∀ r ∈ S, r ≤ S.max' hS := fun r hr => Finset.le_max' S r hr
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, S.max' hS = r₀ := ⟨_, rfl⟩
  rw [hr₀def] at hr₀ hle
  have hmax : ∀ r, r₀ < r → ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c := fun r hr c => by
    by_contra h
    exact absurd (hle r (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, c, h⟩)) (not_le.2 hr)
  rw [hSdef, Finset.mem_filter] at hr₀
  obtain ⟨j, hj⟩ := hr₀.2
  have hr₀last : r₀ ≠ Fin.last m := fun h => by rw [h] at hj; exact hj (hlast j)
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hr₀last
  have hjle : j ≤ r₀ := by
    by_contra h
    push_neg at h
    exact hj (by rw [hlow _ _ h, Matrix.one_apply_ne (ne_of_lt h)])
  have hcgt : r₀ < i.succ := by rw [← hi]; exact Fin.castSucc_lt_succ
  have hrow := hmax _ hcgt
  have hcol : ∀ r, r₀ < r → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r j = 0 := fun r hr => by
    rw [hmax r hr j, Matrix.one_apply_ne (lt_of_le_of_lt hjle hr).ne']
  have hd : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j ≠ 0 :=
    sub_ne_zero.2 hj
  obtain ⟨s₀, hs₀⟩ := AddChar.ne_one_iff.1 hψ
  have h1' : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j = 0 := by rw [hcol _ hcgt, mul_zero]
  have h2' : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) i.succ = 0 := by
    rw [Pi.single_apply, if_neg (lt_of_le_of_lt hjle hcgt).ne']
  refine vanish_of_comm hl hv
    (colElt_mem _ _ h1' fun r hr => by rw [hcol r (lt_trans hcgt hr), mul_zero])
    (colElt_mem _ _ h2' fun r hr => by rw [Pi.single_apply, if_neg (lt_trans (lt_of_le_of_lt hjle hcgt) hr).ne'])
    (colElt_comm Y i.succ j _ hrow h1' h2') ?_
  rw [superDiag_colElt, superDiag_colElt, hi]
  have hsY : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j + s₀ := by
    field_simp
    ring
  have hsing : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) r₀ =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j := by
    by_cases h : r₀ = j
    · subst h; simp
    · rw [Pi.single_apply, if_neg h, Matrix.one_apply_ne h, mul_zero]
  rw [hsY, hsing, AddChar.map_add_eq_mul]
  intro h
  exact hs₀ (by simpa using h)

end DiscreteGroups.sglob.DzFp
