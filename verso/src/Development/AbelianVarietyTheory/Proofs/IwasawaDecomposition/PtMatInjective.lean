import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

/- English proof (translation)
The claim follows from `| [], _, _ => by simp [ptEntry] | (t, s) :: bs, a, b => by rw [ptEntry, ptEntry, ptEntry_symm bs (a - s) (b - s), add_comm a b] simp only [and_comm]`.
-/
theorem ptEntry_symm : ∀ (bs : List (E × ℕ)) (a b : ℕ), ptEntry bs a b = ptEntry bs b a
  | [], _, _ => by simp [ptEntry]
  | (t, s) :: bs, a, b => by
    rw [ptEntry, ptEntry, ptEntry_symm bs (a - s) (b - s), add_comm a b]
    simp only [and_comm]

/- English proof (translation)
The claim follows from `| [], _, a, ha => by simp at ha | (t, s) :: bs, h, a, ha => by have ht : t ≠ 0 := (h (t, s) (by simp)).1 simp only [List.map_cons, List.sum_cons] at ha ⊢ by_cases has : a < s · refine ⟨s - 1 - a, by omega, ?_, fun b hb => ?_⟩ · rw [ptEntry, if_pos (by omega), if_pos (by omega)]; …`.
-/
theorem ptEntry_row : ∀ (bs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ a < (bs.map Prod.snd).sum, ∃ c < (bs.map Prod.snd).sum,
      ptEntry bs a c ≠ 0 ∧ ∀ b, b ≠ c → ptEntry bs a b = 0
  | [], _, a, ha => by simp at ha
  | (t, s) :: bs, h, a, ha => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    simp only [List.map_cons, List.sum_cons] at ha ⊢
    by_cases has : a < s
    · refine ⟨s - 1 - a, by omega, ?_, fun b hb => ?_⟩
      · rw [ptEntry, if_pos (by omega), if_pos (by omega)]; exact ht
      · rw [ptEntry]
        split_ifs <;> first | rfl | omega
    · obtain ⟨c, hc, h1, h2⟩ := ptEntry_row bs (fun b hb => h b (by simp [hb])) (a - s) (by omega)
      refine ⟨c + s, by omega, ?_, fun b hb => ?_⟩
      · rw [ptEntry, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]; exact h1
      · rw [ptEntry, if_neg (by omega)]
        split_ifs
        · exact h2 _ (by omega)
        · rfl

/- English proof (translation)
The claim follows from `| [], [], _, _, _, _ => rfl | [], (t, s) :: cs, _, h, e, _ => by have := (h (t, s) (by simp)).2 simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e this omega | (t, s) :: bs, [], h, _, e, _ => by have := (h (t, s) (by simp)).2 simp only [List.map_cons, List. …`.
-/
theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e this
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e this
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    obtain ⟨ht, hs⟩ : t ≠ 0 ∧ 1 ≤ s := h (t, s) (by simp)
    obtain ⟨-, hs'⟩ : t' ≠ 0 ∧ 1 ≤ s' := h' (t', s') (by simp)
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    rw [ptEntry, if_pos (by omega), if_pos (by omega), ptEntry] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    obtain ⟨rfl, rfl⟩ := hss
    congr 1
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have := k (a + s) (by omega) (b + s) (by omega)
    rwa [ptEntry, ptEntry, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel, Nat.add_sub_cancel] at this

/- English proof (translation)
Introduce `w w' h`. Use `Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)` and prove the remaining obligations. Rewrite `ha`, `hb` using `[w.2.2]`. Conclude with `congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩`.
-/
theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

/- English proof (translation)
Establish `row (a : Fin m) : ∃ c, ptMat w a c ≠ 0 ∧ ∀ b, b ≠ c → ptMat w a b = 0`. Take `⟨c, hc, h1, h2⟩` from `ptEntry_row w.1 w.2.1 a (by rw [w.2.2]; exact a.2)`. Rewrite `hc` using `[w.2.2]`. Conclude with `⟨⟨c, hc⟩, h1, fun b hb => h2 b fun e => hb (Fin.ext e)⟩`. Establish `sy (a b : Fin m) : ptMat w a b = ptMat w b a` using `ptEntry_symm _ _ _`.

Take `⟨c, h1, h2⟩` from `row a`. Take `⟨d, -, h4⟩` from `row c`. Take `rfl : a = d` from `by_contra fun e => h1 ((sy a c).trans (h4 a e))`. Conclude with `⟨c, h1, h2, fun k hk => (sy k c).trans (h4 k hk)⟩`.
-/
theorem ptMat_monomial {m : ℕ} (w : Point E m) (a : Fin m) :
    ∃ c, ptMat w a c ≠ 0 ∧ (∀ b, b ≠ c → ptMat w a b = 0) ∧ ∀ k, k ≠ a → ptMat w k c = 0 := by
  have row (a : Fin m) : ∃ c, ptMat w a c ≠ 0 ∧ ∀ b, b ≠ c → ptMat w a b = 0 := by
    obtain ⟨c, hc, h1, h2⟩ := ptEntry_row w.1 w.2.1 a (by rw [w.2.2]; exact a.2)
    rw [w.2.2] at hc
    exact ⟨⟨c, hc⟩, h1, fun b hb => h2 b fun e => hb (Fin.ext e)⟩
  have sy (a b : Fin m) : ptMat w a b = ptMat w b a := ptEntry_symm _ _ _
  obtain ⟨c, h1, h2⟩ := row a
  obtain ⟨d, -, h4⟩ := row c
  obtain rfl : a = d := by_contra fun e => h1 ((sy a c).trans (h4 a e))
  exact ⟨c, h1, h2, fun k hk => (sy k c).trans (h4 k hk)⟩

/- English proof (translation)
Use `up_inv (u := lᵀ) fun i j => ⟨(hl j i).1, fun e => (hl j i).2 e.symm⟩` as an intermediate fact. Rewrite `this` using `[← Matrix.transpose_nonsing_inv]`. Conclude with `fun i j => ⟨(this j i).1, fun e => (this j i).2 e.symm⟩`.
-/
theorem lo_inv {m : ℕ} {l : Matrix (Fin m) (Fin m) E} (hl : IsLo l) : IsLo l⁻¹ := by
  have := up_inv (u := lᵀ) fun i j => ⟨(hl j i).1, fun e => (hl j i).2 e.symm⟩
  rw [← Matrix.transpose_nonsing_inv] at this
  exact fun i j => ⟨(this j i).1, fun e => (this j i).2 e.symm⟩

/- English proof (translation)
Establish `e2 : l'⁻¹ * l * ptMat w = ptMat w' * (u' * u⁻¹)`. Use `congrArg (fun W => l'⁻¹ * W * u⁻¹) e` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, up_mul_inv hu, Matrix.mul_one] at this`. Rewrite `this` using `[← Matrix.mul_assoc l'⁻¹ l', Matrix.nonsing_inv_mul l' (by simp [lo_det hl']), Matrix.one_mul, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hv` using `up_mul hu' (up_inv hu)`.

Establish `e3` using `congrFun (congrFun e2 a) c`. Rewrite `e3` using `[Matrix.mul_apply, Matrix.mul_apply (M := ptMat w'), Finset.sum_eq_single a (fun k _ hk => by rw [h2 k hk, mul_zero]) (by simp), Finset.sum_eq_single c' (fun k _ hk => by rw [h3 k hk, zero_mul]) (by simp), (lo_mul (lo_inv hl') hl a a).2 rfl, one_mul]`. Conclude with `⟨not_lt.1 fun h => h1 (by rw [e3, (hv _ _).1 h, mul_zero]), fun h => by rw [e3, (hv _ _).2 h, mul_one]⟩`.
-/
theorem ptMat_row_le {m : ℕ} {w w' : Point E m} {l u l' u' : Matrix (Fin m) (Fin m) E} (hl : IsLo l) (hu : IsUp u)
    (hl' : IsLo l') (hu' : IsUp u') (e : l * ptMat w * u = l' * ptMat w' * u') {a c c' : Fin m}
    (h1 : ptMat w a c ≠ 0) (h2 : ∀ k, k ≠ a → ptMat w k c = 0) (h3 : ∀ b, b ≠ c' → ptMat w' a b = 0) :
    c' ≤ c ∧ (c' = c → ptMat w a c = ptMat w' a c') := by
  have e2 : l'⁻¹ * l * ptMat w = ptMat w' * (u' * u⁻¹) := by
    have := congrArg (fun W => l'⁻¹ * W * u⁻¹) e
    simp only [Matrix.mul_assoc, up_mul_inv hu, Matrix.mul_one] at this
    rwa [← Matrix.mul_assoc l'⁻¹ l', Matrix.nonsing_inv_mul l' (by simp [lo_det hl']), Matrix.one_mul,
      ← Matrix.mul_assoc] at this
  have hv := up_mul hu' (up_inv hu)
  have e3 := congrFun (congrFun e2 a) c
  rw [Matrix.mul_apply, Matrix.mul_apply (M := ptMat w'),
    Finset.sum_eq_single a (fun k _ hk => by rw [h2 k hk, mul_zero]) (by simp),
    Finset.sum_eq_single c' (fun k _ hk => by rw [h3 k hk, zero_mul]) (by simp),
    (lo_mul (lo_inv hl') hl a a).2 rfl, one_mul] at e3
  exact ⟨not_lt.1 fun h => h1 (by rw [e3, (hv _ _).1 h, mul_zero]),
    fun h => by rw [e3, (hv _ _).2 h, mul_one]⟩

/- English proof (translation)
Take `⟨l, u, hl, hu, e⟩` from `h`. Take `⟨l', u', hl', hu', e'⟩` from `h'`. Use `ptMat_injective (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Take `⟨c, h1, h2, h3⟩` from `ptMat_monomial w a`. Take `⟨c', k1, k2, k3⟩` from `ptMat_monomial w' a`.

Establish `p` using `ptMat_row_le hl hu hl' hu' (e.symm.trans e') h1 h3 k2`. Establish `q` using `ptMat_row_le hl' hu' hl hu (e'.symm.trans e) k1 k3 h2`. Take `rfl : c' = c` from `le_antisymm p.1 q.1`. Break down `eq_or_ne b c' with rfl | hb` into its components or cases. Conclude with `p.2 rfl`.

Rewrite using `[h2 b hb, k2 b hb]`.
-/
theorem liesAt_unique {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w w' : Point E (r + 1))
    (h : LiesAt w Z) (h' : LiesAt w' Z) : w = w' := by
  obtain ⟨l, u, hl, hu, e⟩ := h
  obtain ⟨l', u', hl', hu', e'⟩ := h'
  refine ptMat_injective (Matrix.ext fun a b => ?_)
  obtain ⟨c, h1, h2, h3⟩ := ptMat_monomial w a
  obtain ⟨c', k1, k2, k3⟩ := ptMat_monomial w' a
  have p := ptMat_row_le hl hu hl' hu' (e.symm.trans e') h1 h3 k2
  have q := ptMat_row_le hl' hu' hl hu (e'.symm.trans e) k1 k3 h2
  obtain rfl : c' = c := le_antisymm p.1 q.1
  rcases eq_or_ne b c' with rfl | hb
  · exact p.2 rfl
  · rw [h2 b hb, k2 b hb]

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

/- English proof (translation)
The claim follows from `liesAt_unique t.Zhat _ _ h h'`.
-/
theorem Term.At.unique {t : Term σ J T' g P} {w w' : Point E (r + 1)} (h : t.At w) (h' : t.At w') : w = w' :=
  liesAt_unique t.Zhat _ _ h h'

end GlobalTheory.IntTerm
