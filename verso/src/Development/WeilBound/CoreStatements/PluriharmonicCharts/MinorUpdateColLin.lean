import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MCoordIdealLeOfHomog
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N j : ℕ}

section Ring

variable {R : Type} [CommRing R]

/- English proof (translation)
Rewrite using `[minorIJ_eq_det B S S _ rfl rfl, det_of_lowerTriangular, prod_mem_eq_prod_enum S (fun c => B c c)]`. Both sides reduce to the same expression. Introduce `x y hxy`. Conclude with `hB _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _) ((S.orderEmbOfFin rfl).strictMono hxy)`.
-/
theorem minor_self_of_lower (B : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (hB : ∀ a ∈ S, ∀ c ∈ S, a < c → B a c = 0) : minorIJ B S S = ∏ c ∈ S, B c c := by
  rw [minorIJ_eq_det B S S _ rfl rfl, det_of_lowerTriangular, prod_mem_eq_prod_enum S (fun c => B c c)]
  · rfl
  · intro x y hxy
    exact hB _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _)
      ((S.orderEmbOfFin rfl).strictMono hxy)

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Use `congr 1`. Use extensionality with `x y`. Conclude with `h _ _ (Finset.orderEmbOfFin_mem _ _ _)`.

Both sides reduce to the same expression.
-/
theorem minor_congr_cols {A B : Matrix (Fin N) (Fin N) R} (I J : Finset (Fin N))
    (h : ∀ r, ∀ c ∈ J, A r c = B r c) : minorIJ A I J = minorIJ B I J := by
  unfold minorIJ
  split_ifs with e
  · congr 1
    ext x y
    exact h _ _ (Finset.orderEmbOfFin_mem _ _ _)
  · rfl

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Establish `hr : c ∈ Set.range (J.orderEmbOfFin rfl)` using `by rw [Finset.range_orderEmbOfFin]; exact hc`. Take `⟨x₀, rfl⟩` from `hr`. Establish `key : ∀ u : Fin N → R, (A.updateCol (J.orderEmbOfFin rfl x₀) u).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) = (A.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)).updateCol x₀ (u ∘ I.orderEmbOfFin e)` using `fun u => by`.

Use extensionality with `x y`. Simplify using `only [submatrix_apply, updateCol_apply, (J.orderEmbOfFin rfl).injective.eq_iff, Function.comp]`. Rewrite using `[key, key, key, show (β • v + δ • w) ∘ I.orderEmbOfFin e = β • (v ∘ I.orderEmbOfFin e) + δ • (w ∘ I.orderEmbOfFin e) from rfl, det_updateCol_add, det_updateCol_smul, det_updateCol_smul]`. Simplify using the standard rewrite rules.
-/
theorem minor_updateCol_lin (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {c : Fin N} (hc : c ∈ J)
    (β δ : R) (v w : Fin N → R) :
    minorIJ (A.updateCol c (β • v + δ • w)) I J =
      β * minorIJ (A.updateCol c v) I J + δ * minorIJ (A.updateCol c w) I J := by
  unfold minorIJ
  split_ifs with e
  · have hr : c ∈ Set.range (J.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hc
    obtain ⟨x₀, rfl⟩ := hr
    have key : ∀ u : Fin N → R, (A.updateCol (J.orderEmbOfFin rfl x₀) u).submatrix (I.orderEmbOfFin e)
        (J.orderEmbOfFin rfl) = (A.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)).updateCol x₀
          (u ∘ I.orderEmbOfFin e) := fun u => by
      ext x y
      simp only [submatrix_apply, updateCol_apply, (J.orderEmbOfFin rfl).injective.eq_iff, Function.comp]
    rw [key, key, key, show (β • v + δ • w) ∘ I.orderEmbOfFin e = β • (v ∘ I.orderEmbOfFin e) +
      δ • (w ∘ I.orderEmbOfFin e) from rfl, det_updateCol_add, det_updateCol_smul, det_updateCol_smul]
  · simp

/- English proof (translation)
Establish `hn : cb ∉ S.erase ca` using `fun h => absurd (hS _ (Finset.mem_of_mem_erase h)) (not_le.2 hcb)`. Establish `hcard : (insert cb (S.erase ca)).card = S.card`. Rewrite using `[Finset.card_insert_of_notMem hn, Finset.card_erase_add_one hca]`. Distinguish the cases in `e : I.card = S.card`. Rewrite using `[minorIJ_eq_det _ _ _ _ e hcard, minorIJ_eq_det _ _ _ _ e rfl]`.

Establish `hf : (fun x => if S.orderEmbOfFin rfl x = ca then cb else S.orderEmbOfFin rfl x) = (insert cb (S.erase ca)).orderEmbOfFin hcard`. Use `Finset.orderEmbOfFin_unique hcard (fun x => ?_) fun x y hxy => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `Finset.mem_insert_self _ _`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, Finset.orderEmbOfFin_mem _ _ _⟩)`.

Establish `h1` using `(S.orderEmbOfFin rfl).strictMono hxy`. Establish `h2` using `hS _ (Finset.orderEmbOfFin_mem S rfl y)`. Use `split_ifs with h h' h'`. Rewrite `h1` using `[h, h']`. Conclude with `absurd h1 (lt_irrefl _)`.

Rewrite `h1` using `[h]`. Conclude with `absurd h2 (not_le.2 h1)`. Conclude with `(hS _ (Finset.orderEmbOfFin_mem S rfl x)).trans_lt hcb`. Conclude with `h1`. Use `congr 1`.

Use extensionality with `x y`. Simplify using `only [submatrix_apply, updateCol_apply, ← hf]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ (by rwa [hcard])]`.
-/
theorem minor_swapCol (A : Matrix (Fin N) (Fin N) R) (I S : Finset (Fin N)) {ca cb : Fin N} (hca : ca ∈ S)
    (hS : ∀ c ∈ S, c ≤ ca) (hcb : ca < cb) :
    minorIJ A I (insert cb (S.erase ca)) = minorIJ (A.updateCol ca fun r => A r cb) I S := by
  have hn : cb ∉ S.erase ca := fun h => absurd (hS _ (Finset.mem_of_mem_erase h)) (not_le.2 hcb)
  have hcard : (insert cb (S.erase ca)).card = S.card := by
    rw [Finset.card_insert_of_notMem hn, Finset.card_erase_add_one hca]
  by_cases e : I.card = S.card
  · rw [minorIJ_eq_det _ _ _ _ e hcard, minorIJ_eq_det _ _ _ _ e rfl]
    have hf : (fun x => if S.orderEmbOfFin rfl x = ca then cb else S.orderEmbOfFin rfl x) =
        (insert cb (S.erase ca)).orderEmbOfFin hcard := by
      refine Finset.orderEmbOfFin_unique hcard (fun x => ?_) fun x y hxy => ?_
      · split_ifs with h
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, Finset.orderEmbOfFin_mem _ _ _⟩)
      · have h1 := (S.orderEmbOfFin rfl).strictMono hxy
        have h2 := hS _ (Finset.orderEmbOfFin_mem S rfl y)
        split_ifs with h h' h'
        · rw [h, h'] at h1; exact absurd h1 (lt_irrefl _)
        · rw [h] at h1; exact absurd h2 (not_le.2 h1)
        · exact (hS _ (Finset.orderEmbOfFin_mem S rfl x)).trans_lt hcb
        · exact h1
    congr 1
    ext x y
    simp only [submatrix_apply, updateCol_apply, ← hf]
    split_ifs <;> rfl
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ (by rwa [hcard])]

/- English proof (translation)
The claim follows from `minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun e => hb (e ▸ hc)`.
-/
theorem minor_one_of_ne {I J : Finset (Fin N)} {a : Fin N} (ha : a ∈ I) (hb : a ∉ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) I J = 0 :=
  minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun e => hb (e ▸ hc)

end Ring

/- English proof (translation)
Establish `main : ∀ n ≤ N, ∃ ρ : Fin N → Fin N, (∀ a, ((ρ a : ℕ) < N - j ↔ (a : ℕ) < N - j)) ∧ ∀ n' ≤ n, ∀ v : Fin N → k, (∀ a : Fin N, n' ≤ (a : ℕ) → v a = 0) → (∀ a : Fin N, (a : ℕ) < n' → (M *ᵥ v) (ρ a) = 0) → v = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_`.

Use `⟨id, fun _ => Iff.rfl, fun n' hn' v hv _ => funext fun a => hv a (by omega)⟩` and prove the remaining obligations. Consider the case `succ n ih`. Introduce `hn`. Take `⟨ρ, hρ, H⟩` from `ih (by omega)`. Set `b : Fin N` to `⟨n, by omega⟩`.

Distinguish the cases in `hex : ∃ v : Fin N → k, (∀ a : Fin N, n + 1 ≤ (a : ℕ) → v a = 0) ∧ (∀ a : Fin N, (a : ℕ) < n → (M *ᵥ v) (ρ a) = 0) ∧ v ≠ 0`. Take `⟨v, hv1, hv2, hv0⟩` from `hex`. Establish `hvb : v b ≠ 0` using `fun e => hv0 (H n le_rfl v (fun a ha => by`. Break down `Nat.lt_or_ge n a with h | h` into its components or cases. Conclude with `hv1 a h`.

Rewrite using `[show a = b from Fin.ext (le_antisymm h ha)]`. Conclude with `e) hv2)`. Set `v' : Fin N → k` to `fun a => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then v a else 0`. Establish `hv' : M *ᵥ v' ≠ 0` using `fun e => hvb (by`. Use `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd e) b` as an intermediate fact.

Simplify `this)` using `[v']`. Take `⟨r, hr⟩` from `Function.ne_iff.1 hv'`. Establish `hrb : ((r : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Assume the negation of the conclusion as `hc`. Use `hr (show ∑ c, M r c * v' c = 0 from Finset.sum_eq_zero fun c _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Use `show M r c * _ = 0`. Rewrite using `[hM r c fun e' => hc (e'.trans e), zero_mul]`. Use `show _ * v' c = 0`. Simplify using `only [v', if_neg e, mul_zero]`.

Establish `hr' : (M *ᵥ v) r ≠ 0`. Use `fun e => hr (Eq.trans (show ∑ c, M r c * v' c = ∑ c, M r c * v c from Finset.sum_congr rfl fun c _ => ?_) e)` and prove the remaining obligations. Distinguish the cases in `e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Use `show _ * v' c = _`. Simplify using `only [v', if_pos e]`.

Use `show M r c * _ = M r c * _`. Rewrite using `[hM r c fun e' => e (e'.symm.trans hrb), zero_mul, zero_mul]`. Establish `hup : ∀ a : Fin N, (a : ℕ) < n → Function.update ρ b r a = ρ a` using `fun a ha => Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _`. Use `⟨Function.update ρ b r, fun a => ?_, fun n' hn' w hw1 hw2 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : a = b`.

Rewrite using `[e, Function.update_self]`. Conclude with `hrb`. Rewrite using `[Function.update_of_ne e]`. Conclude with `hρ a`. Break down `Nat.lt_or_ge n' (n + 1) with h | h` into its components or cases.

Conclude with `H n' (by omega) w hw1 fun a ha => by rw [← hup a (by omega)]; exact hw2 a ha`. Take `rfl : n' = n + 1` from `by omega`. Establish `h0` using `H n le_rfl (w - (w b / v b) • v) (fun a ha => by`. Break down `Nat.lt_or_ge n a with h | h` into its components or cases. Simplify using `[hv1 a h, hw1 a h]`.

Rewrite using `[show a = b from Fin.ext (le_antisymm h ha)]`. Simplify using `[div_mul_cancel₀ _ hvb]) fun a ha => by`. Use `hw2 a (by omega)` as an intermediate fact. Rewrite `this` using `[hup a ha]`. Rewrite using `[mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, this, hv2 a ha, smul_zero, sub_zero]`.

Establish `h1` using `sub_eq_zero.1 h0`. Establish `h2` using `hw2 b (by simp [b])`. Rewrite `h2` using `[Function.update_self, h1, mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[h1, (mul_eq_zero.1 h2).resolve_right hr', zero_smul]`. Use `push Not at hex`.

Use `⟨ρ, hρ, fun n' hn' w hw1 hw2 => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge n' (n + 1) with h | h` into its components or cases. Conclude with `H n' (by omega) w hw1 hw2`. Take `rfl : n' = n + 1` from `by omega`. Conclude with `hex w hw1 fun a ha => hw2 a (by omega)`.

Take `⟨ρ, hρ, H⟩` from `main N le_rfl`. Use `⟨ρ, hρ, fun b h0 => ?_⟩` and prove the remaining obligations. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Set `P : Fin N → Prop` to `fun a => a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Set `v : Fin N → k` to `fun a => if h : P a then w ⟨a, h⟩ else 0`.

Establish `hv` using `H (b + 1) b.2 v (fun a ha => dif_neg fun h => by have : (a : ℕ) ≤ b := h.1; omega) fun a ha => by`. Establish `e1 : (M *ᵥ v) (ρ a) = ∑ c : {c // P c}, M (ρ a) c * w c` using `by show ∑ c, M (ρ a) c * v c = _`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ P, Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by`. Rewrite using `[show v c = 0 from dif_neg (Finset.mem_filter.1 hc).2, mul_zero]), add_zero,`. Use the proof step `Finset.sum_subtype (p := P) _ (by simp)]`.

Conclude with `Finset.sum_congr rfl fun c _ => by rw [show v c = w c from dif_pos c.2]`. Rewrite using `[e1]`. Distinguish the cases in `e : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Conclude with `congrFun hw ⟨a, (by omega : (a : ℕ) ≤ b), e⟩`. Conclude with `Finset.sum_eq_zero fun c _ => by`.

Rewrite using `[hM _ _ fun e' => e ((hρ a).symm.trans (e'.trans c.2.2)), zero_mul]`. Use `hw0 (funext fun c => ?_)` and prove the remaining obligations. Use `congrFun hv c` as an intermediate fact. Rewrite `this` using `[show v c = w c from dif_pos c.2]`. Then use the resulting hypothesis.
-/
theorem exists_rows {k : Type} [Field k] (M : Matrix (Fin N) (Fin N) k) (hM : IsBlockDiag j M) (hd : M.det ≠ 0) :
    ∃ ρ : Fin N → Fin N, (∀ a, ((ρ a : ℕ) < N - j ↔ (a : ℕ) < N - j)) ∧ ∀ b : Fin N,
      ((M.submatrix ρ id).submatrix
        (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det ≠ 0 := by
  have main : ∀ n ≤ N, ∃ ρ : Fin N → Fin N, (∀ a, ((ρ a : ℕ) < N - j ↔ (a : ℕ) < N - j)) ∧ ∀ n' ≤ n,
      ∀ v : Fin N → k, (∀ a : Fin N, n' ≤ (a : ℕ) → v a = 0) → (∀ a : Fin N, (a : ℕ) < n' → (M *ᵥ v) (ρ a) = 0) →
        v = 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨id, fun _ => Iff.rfl, fun n' hn' v hv _ => funext fun a => hv a (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨ρ, hρ, H⟩ := ih (by omega)
      let b : Fin N := ⟨n, by omega⟩
      by_cases hex : ∃ v : Fin N → k, (∀ a : Fin N, n + 1 ≤ (a : ℕ) → v a = 0) ∧
          (∀ a : Fin N, (a : ℕ) < n → (M *ᵥ v) (ρ a) = 0) ∧ v ≠ 0
      · obtain ⟨v, hv1, hv2, hv0⟩ := hex
        have hvb : v b ≠ 0 := fun e => hv0 (H n le_rfl v (fun a ha => by
          rcases Nat.lt_or_ge n a with h | h
          · exact hv1 a h
          · rw [show a = b from Fin.ext (le_antisymm h ha)]; exact e) hv2)
        let v' : Fin N → k := fun a => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then v a else 0
        have hv' : M *ᵥ v' ≠ 0 := fun e => hvb (by
          have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd e) b
          simpa [v'] using this)
        obtain ⟨r, hr⟩ := Function.ne_iff.1 hv'
        have hrb : ((r : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
          by_contra hc
          refine hr (show ∑ c, M r c * v' c = 0 from Finset.sum_eq_zero fun c _ => ?_)
          by_cases e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)
          · show M r c * _ = 0
            rw [hM r c fun e' => hc (e'.trans e), zero_mul]
          · show _ * v' c = 0
            simp only [v', if_neg e, mul_zero]
        have hr' : (M *ᵥ v) r ≠ 0 := by
          refine fun e => hr (Eq.trans (show ∑ c, M r c * v' c = ∑ c, M r c * v c from
            Finset.sum_congr rfl fun c _ => ?_) e)
          by_cases e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)
          · show _ * v' c = _
            simp only [v', if_pos e]
          · show M r c * _ = M r c * _
            rw [hM r c fun e' => e (e'.symm.trans hrb), zero_mul, zero_mul]
        have hup : ∀ a : Fin N, (a : ℕ) < n → Function.update ρ b r a = ρ a := fun a ha =>
          Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
        refine ⟨Function.update ρ b r, fun a => ?_, fun n' hn' w hw1 hw2 => ?_⟩
        · by_cases e : a = b
          · rw [e, Function.update_self]; exact hrb
          · rw [Function.update_of_ne e]; exact hρ a
        · rcases Nat.lt_or_ge n' (n + 1) with h | h
          · exact H n' (by omega) w hw1 fun a ha => by rw [← hup a (by omega)]; exact hw2 a ha
          · obtain rfl : n' = n + 1 := by omega
            have h0 := H n le_rfl (w - (w b / v b) • v) (fun a ha => by
              rcases Nat.lt_or_ge n a with h | h
              · simp [hv1 a h, hw1 a h]
              · rw [show a = b from Fin.ext (le_antisymm h ha)]
                simp [div_mul_cancel₀ _ hvb]) fun a ha => by
              have := hw2 a (by omega)
              rw [hup a ha] at this
              rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, this, hv2 a ha, smul_zero, sub_zero]
            have h1 := sub_eq_zero.1 h0
            have h2 := hw2 b (by simp [b])
            rw [Function.update_self, h1, mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2
            rw [h1, (mul_eq_zero.1 h2).resolve_right hr', zero_smul]
      · push Not at hex
        refine ⟨ρ, hρ, fun n' hn' w hw1 hw2 => ?_⟩
        rcases Nat.lt_or_ge n' (n + 1) with h | h
        · exact H n' (by omega) w hw1 hw2
        · obtain rfl : n' = n + 1 := by omega
          exact hex w hw1 fun a ha => hw2 a (by omega)
  obtain ⟨ρ, hρ, H⟩ := main N le_rfl
  refine ⟨ρ, hρ, fun b h0 => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let P : Fin N → Prop := fun a => a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  let v : Fin N → k := fun a => if h : P a then w ⟨a, h⟩ else 0
  have hv := H (b + 1) b.2 v (fun a ha => dif_neg fun h => by have : (a : ℕ) ≤ b := h.1; omega) fun a ha => by
    have e1 : (M *ᵥ v) (ρ a) = ∑ c : {c // P c}, M (ρ a) c * w c := by
      show ∑ c, M (ρ a) c * v c = _
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P,
        Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by
          rw [show v c = 0 from dif_neg (Finset.mem_filter.1 hc).2, mul_zero]), add_zero,
        Finset.sum_subtype (p := P) _ (by simp)]
      exact Finset.sum_congr rfl fun c _ => by rw [show v c = w c from dif_pos c.2]
    rw [e1]
    by_cases e : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · exact congrFun hw ⟨a, (by omega : (a : ℕ) ≤ b), e⟩
    · exact Finset.sum_eq_zero fun c _ => by
        rw [hM _ _ fun e' => e ((hρ a).symm.trans (e'.trans c.2.2)), zero_mul]
  refine hw0 (funext fun c => ?_)
  have := congrFun hv c
  rwa [show v c = w c from dif_pos c.2] at this

/- English proof (translation)
Establish `h' : (c : ℕ) < r` using `h`. Establish `hr` using `r.2`. Distinguish the cases in `e : (c : ℕ) < N - j`. Use `hs.2 e` as an intermediate fact. Use `⟨⟨c + j, by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]; omega`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Rewrite `ha` using `[if_neg (by omega)]`. Use `show (a : ℕ) ≤ c`.

Use linear arithmetic over natural numbers and integers. Use `⟨⟨c - (N - j), by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]; omega`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha`.

Rewrite `ha` using `[if_pos (by omega)]`. Use `show (a : ℕ) ≤ c`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_step_of_lt (hj : j ≤ N) {r c : Fin N} (h : c < r) (hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)) :
    ∃ i, IsProperStep N j i ∧ c ∈ stepCols N j i ∧ ∀ a ∈ stepCols N j i, a ≤ c := by
  have h' : (c : ℕ) < r := h
  have hr := r.2
  by_cases e : (c : ℕ) < N - j
  · have := hs.2 e
    refine ⟨⟨c + j, by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg (by omega)]; omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_neg (by omega)] at ha
      show (a : ℕ) ≤ c
      omega
  · refine ⟨⟨c - (N - j), by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]; omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_pos (by omega)] at ha
      show (a : ℕ) ≤ c
      omega

/- English proof (translation)
Take `⟨V, hV⟩` from `(LocalSubring.mk O).exists_le_valuationSubring`. Take `⟨hOV, hloc⟩` from `hV`. Establish `hOV' : ∀ s ∈ O, s ∈ V` using `fun s hs => hOV hs`. Establish `dom : ∀ s ∈ O, s ≠ 0 → s⁻¹ ∈ V → s⁻¹ ∈ O` using `fun s hs h0 hi => by`. Establish `hu : IsUnit (Subring.inclusion hOV ⟨s, hs⟩)` using `IsUnit.of_mul_eq_one ⟨s⁻¹, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))`.

Take `⟨t, ht⟩` from `(hloc.1 _ hu).exists_right_inv`. Establish `ht' : s * (t : L) = 1` using `congrArg Subtype.val ht`. Rewrite using `[inv_eq_of_mul_eq_one_right ht']`. Conclude with `t.2`. Take `⟨b₀, hb₀, hb₀t, hb₀d, hmem, hdet, hinv⟩` from `GlobalTheory.T.block_diag_valuation_normalization L V N j h hb hd`.

Set `Hv : Matrix (Fin N) (Fin N) V` to `Matrix.of fun a c => ⟨(h * b₀) a c, hmem a c⟩`. Establish `hHv : Hv.map V.subtype = h * b₀` using `by ext a c; rfl`. Establish `hHvb : IsBlockDiag j Hv` using `fun a c e => Subtype.ext ((hb.mul hb₀) a c e)`. Establish `hunit : IsUnit Hv.det`. Establish `hdetc : ((Hv.det : V) : L) = (h * b₀).det`.

Use `RingHom.map_det V.subtype Hv` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, hHv]`. Conclude with `this`. Use `IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Hv.det : V) : L) * _ = 1`.

Rewrite using `[hdetc, mul_inv_cancel₀ hdet]`. Take `⟨ρ, hρ, hρd⟩` from `exists_rows (Hv.map (IsLocalRing.residue V)) (hHvb.map _) (by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(hunit.map _).ne_zero)`. Take `⟨B, hB, hBt, hlo⟩` from `IsBlockDiag.exists_upper (j := j) (G := Hv.submatrix ρ id) (fun a c e => hHvb _ _ fun e' => e ((hρ a).symm.trans e')) fun c => by`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Conclude with `hρd c`. Set `B'` to `B.map V.subtype`. Set `E : Matrix (Fin N) (Fin N) L` to `(1 : Matrix (Fin N) (Fin N) L).submatrix ρ id`. Establish `hE : ∀ A : Matrix (Fin N) (Fin N) L, E * A = A.submatrix ρ id` using `fun A => by`.

Rewrite using `[show E * A = (1 * A).submatrix ρ id from by ext; rfl, one_mul]`. Establish `hEO : ∀ a c, E a c ∈ O` using `fun a c => by show (1 : Matrix (Fin N) (Fin N) L) (ρ a) c ∈ O`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [O.one_mem, O.zero_mem]`.

Set `H` to `h * (b₀ * B')`. Establish `hHV : H = (Hv * B).map V.subtype` using `by rw [Matrix.map_mul, hHv, Matrix.mul_assoc]`. Establish `hLo : IsLowerUni (E * H)`. Use `hlo.map V.subtype` as an intermediate fact. Rewrite using `[hE, hHV]`.

Conclude with `this`. Establish `hdEH : E.det * H.det = 1` using `by rw [← det_mul, hLo.det]`. Establish `hbb : IsBlockDiag j (b₀ * B')` using `hb₀.mul (hB.map _)`. Establish `hbt : (b₀ * B').BlockTriangular id` using `hb₀t.mul (hBt.map _)`. Establish `hbd : ∀ a, (b₀ * B') a a ≠ 0` using `fun a h0 => by`.

Establish `h2 : ∏ i, (b₀ * B') i i = 0` using `Finset.prod_eq_zero (Finset.mem_univ a) h0`. Rewrite `hdEH` using `[det_mul, det_of_upperTriangular hbt, h2, mul_zero, mul_zero]`. Conclude with `zero_ne_one hdEH`. Establish `hEb : IsBlockDiag j E` using `fun a c e => isBlockDiag_one _ _ fun e' => e ((hρ a).symm.trans e')`. Establish `hLoO : ∀ r c, (E * H) r c ∈ O`.

Introduce `r c`. Break down `lt_trichotomy r c with e | e | e` into its components or cases. Rewrite using `[hLo.2 _ _ e]`. Conclude with `O.zero_mem`. Rewrite using `[e, hLo.1]`.

Conclude with `O.one_mem`. Distinguish the cases in `hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)`. Use `swap`. Rewrite using `[(hEb.mul (hb.mul hbb)) r c hs]`. Conclude with `O.zero_mem`.

Take `⟨i, hi, hc, hmax⟩` from `exists_step_of_lt hj e hs`. Take `⟨η, hη, hO, I₀, hI₀, hI₀'⟩` from `hP i hi`. Use `set S := stepCols N j i`. Set `θ : L` to `(∏ c ∈ S, (b₀ * B') c c) / η`. Establish `hθ : ∀ I, minorIJ H I S = θ * (η * minorIJ h I S)` using `fun I => by`.

Rewrite using `[(minors_main L N j i hj).2.2.1 h _ I hbb hbt]`. Simplify using `only [θ, S]`. Clear the denominators using the available nonvanishing facts. Establish `hA : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → ∃ o ∈ O, minorIJ (A * H) S S = θ * o` using `fun A hA => ⟨∑ I, minorIJ A S I * (η * minorIJ h I S), sum_mem fun I _ => O.mul_mem (CPts.minorIJ_mem O hA _ _) (hO I), by`. Rewrite using `[minorIJ_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun I _ => by rw [hθ]; ring⟩`. Establish `hθV : θ ∈ V`. Establish `h1 : minorIJ H I₀ S ∈ V.toSubring` using `CPts.minorIJ_mem _ (fun a c => by rw [hHV]; exact ((Hv * B) a c).2) _ _`. Rewrite using `[show θ = minorIJ H I₀ S * (η * minorIJ h I₀ S)⁻¹ by rw [hθ, mul_inv_cancel_right₀ hI₀]]`. Conclude with `V.mul_mem _ _ h1 (hOV' _ hI₀')`.

Establish `hθO : θ ∈ O`. Take `⟨o, ho, e1⟩` from `hA E hEO`. Rewrite `e1` using `[minor_self_of_lower _ _ fun a _ c _ l => hLo.2 _ _ l, Finset.prod_eq_one fun c _ => hLo.1 c]`. Establish `e2 : o⁻¹ = θ` using `inv_eq_of_mul_eq_one_left e1.symm`. Rewrite `hθV`, the goal using `[← e2]`.

Conclude with `dom o ho (right_ne_zero_of_mul_eq_one e1.symm) hθV`. Take `⟨o, ho, e1⟩` from `hA (E.updateRow c (E r)) fun a c' => by`. Apply the tactic sequence `rw [updateRow_apply]; split_ifs <;> exact hEO _ _`. Establish `e3 : E.updateRow c (E r) * H = (E * H).updateRow c ((E * H) r)`. Use extensionality with `a c'`.

Distinguish the cases in `e : a = c`. Substitute `e` using the available equality. Simplify using `[Matrix.mul_apply]`. Simplify using `[Matrix.mul_apply, updateRow_ne e]`. Rewrite using `[e3, minor_self_of_lower _ _ fun a ha c' hc' l => by`.

Rewrite using `[updateRow_ne (fun e : a = c => absurd (hmax c' hc') (not_le.2 (e ▸ l))), hLo.2 _ _ l],`. Use the proof step `Finset.prod_eq_single c (fun a _ ha => by rw [updateRow_ne ha, hLo.1]) (fun h => absurd hc h),`. Use the proof step `updateRow_self] at e1`. Rewrite using `[e1]`. Conclude with `O.mul_mem hθO ho`.

Establish `invO : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → A.det⁻¹ ∈ O → ∀ a c, A⁻¹ a c ∈ O`. Introduce `A hA hdA a c`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]`. Use `O.mul_mem hdA (CPts.det_mem O fun x y => ?_)` and prove the remaining obligations. Rewrite using `[updateRow_apply]`.

Use `split_ifs`. Rewrite using `[Pi.single_apply]`. Use `split_ifs exacts [O.one_mem, O.zero_mem]`. Conclude with `hA _ _`. Establish `hEd : E.det ≠ 0` using `left_ne_zero_of_mul_eq_one hdEH`.

Establish `hEi : E.det⁻¹ ∈ O` using `dom _ (CPts.det_mem O hEO) hEd (by`. Rewrite using `[inv_eq_of_mul_eq_one_right hdEH]`. Conclude with `CPts.det_mem V.toSubring fun a c => by rw [hHV]; exact ((Hv * B) a c).2)`. Establish `hHO : ∀ a c, H a c ∈ O` using `fun a c => by`. Rewrite using `[← Matrix.nonsing_inv_mul_cancel_left E H hEd.isUnit, Matrix.mul_apply]`.

Conclude with `sum_mem fun x _ => O.mul_mem (invO E hEO hEi _ _) (hLoO _ _)`. Use `⟨b₀ * B', hbb, hbt, hbd, hHO, invO H hHO ?_⟩` and prove the remaining obligations. Rewrite using `[inv_eq_of_mul_eq_one_left hdEH]`. Conclude with `CPts.det_mem O hEO`.
-/
theorem exists_local_frame {L : Type} [Field L] (O : Subring L) [IsLocalRing O] (hj : j ≤ N)
    (h : Matrix (Fin N) (Fin N) L) (hb : IsBlockDiag j h) (hd : h.det ≠ 0)
    (hP : ∀ i, IsProperStep N j i → ∃ η : L, η ≠ 0 ∧ (∀ I, η * minorIJ h I (stepCols N j i) ∈ O) ∧
      ∃ I, η * minorIJ h I (stepCols N j i) ≠ 0 ∧ (η * minorIJ h I (stepCols N j i))⁻¹ ∈ O) :
    ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧
      (∀ a c, (h * b) a c ∈ O) ∧ ∀ a c, (h * b)⁻¹ a c ∈ O := by
  obtain ⟨V, hV⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  obtain ⟨hOV, hloc⟩ := hV
  have hOV' : ∀ s ∈ O, s ∈ V := fun s hs => hOV hs
  have dom : ∀ s ∈ O, s ≠ 0 → s⁻¹ ∈ V → s⁻¹ ∈ O := fun s hs h0 hi => by
    have hu : IsUnit (Subring.inclusion hOV ⟨s, hs⟩) :=
      IsUnit.of_mul_eq_one ⟨s⁻¹, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
    obtain ⟨t, ht⟩ := (hloc.1 _ hu).exists_right_inv
    have ht' : s * (t : L) = 1 := congrArg Subtype.val ht
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2
  obtain ⟨b₀, hb₀, hb₀t, hb₀d, hmem, hdet, hinv⟩ := GlobalTheory.T.block_diag_valuation_normalization L V N j h hb hd
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a c => ⟨(h * b₀) a c, hmem a c⟩
  have hHv : Hv.map V.subtype = h * b₀ := by ext a c; rfl
  have hHvb : IsBlockDiag j Hv := fun a c e => Subtype.ext ((hb.mul hb₀) a c e)
  have hunit : IsUnit Hv.det := by
    have hdetc : ((Hv.det : V) : L) = (h * b₀).det := by
      have := RingHom.map_det V.subtype Hv
      rw [RingHom.mapMatrix_apply, hHv] at this
      exact this
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)
    change ((Hv.det : V) : L) * _ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  obtain ⟨ρ, hρ, hρd⟩ := exists_rows (Hv.map (IsLocalRing.residue V)) (hHvb.map _) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hunit.map _).ne_zero)
  obtain ⟨B, hB, hBt, hlo⟩ := IsBlockDiag.exists_upper (j := j) (G := Hv.submatrix ρ id)
    (fun a c e => hHvb _ _ fun e' => e ((hρ a).symm.trans e')) fun c => by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      exact hρd c
  let B' := B.map V.subtype
  let E : Matrix (Fin N) (Fin N) L := (1 : Matrix (Fin N) (Fin N) L).submatrix ρ id
  have hE : ∀ A : Matrix (Fin N) (Fin N) L, E * A = A.submatrix ρ id := fun A => by
    rw [show E * A = (1 * A).submatrix ρ id from by ext; rfl, one_mul]
  have hEO : ∀ a c, E a c ∈ O := fun a c => by
    show (1 : Matrix (Fin N) (Fin N) L) (ρ a) c ∈ O
    rw [Matrix.one_apply]; split_ifs
    exacts [O.one_mem, O.zero_mem]
  let H := h * (b₀ * B')
  have hHV : H = (Hv * B).map V.subtype := by rw [Matrix.map_mul, hHv, Matrix.mul_assoc]
  have hLo : IsLowerUni (E * H) := by
    have := hlo.map V.subtype
    rw [hE, hHV]
    exact this
  have hdEH : E.det * H.det = 1 := by rw [← det_mul, hLo.det]
  have hbb : IsBlockDiag j (b₀ * B') := hb₀.mul (hB.map _)
  have hbt : (b₀ * B').BlockTriangular id := hb₀t.mul (hBt.map _)
  have hbd : ∀ a, (b₀ * B') a a ≠ 0 := fun a h0 => by
    have h2 : ∏ i, (b₀ * B') i i = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h0
    rw [det_mul, det_of_upperTriangular hbt, h2, mul_zero, mul_zero] at hdEH
    exact zero_ne_one hdEH
  have hEb : IsBlockDiag j E := fun a c e => isBlockDiag_one _ _ fun e' => e ((hρ a).symm.trans e')
  have hLoO : ∀ r c, (E * H) r c ∈ O := by
    intro r c
    rcases lt_trichotomy r c with e | e | e
    · rw [hLo.2 _ _ e]; exact O.zero_mem
    · rw [e, hLo.1]; exact O.one_mem
    by_cases hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)
    swap
    · rw [(hEb.mul (hb.mul hbb)) r c hs]; exact O.zero_mem
    obtain ⟨i, hi, hc, hmax⟩ := exists_step_of_lt hj e hs
    obtain ⟨η, hη, hO, I₀, hI₀, hI₀'⟩ := hP i hi
    set S := stepCols N j i
    let θ : L := (∏ c ∈ S, (b₀ * B') c c) / η
    have hθ : ∀ I, minorIJ H I S = θ * (η * minorIJ h I S) := fun I => by
      rw [(minors_main L N j i hj).2.2.1 h _ I hbb hbt]
      simp only [θ, S]
      field_simp
    have hA : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → ∃ o ∈ O, minorIJ (A * H) S S = θ * o :=
      fun A hA => ⟨∑ I, minorIJ A S I * (η * minorIJ h I S),
        sum_mem fun I _ => O.mul_mem (CPts.minorIJ_mem O hA _ _) (hO I), by
          rw [minorIJ_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ => by rw [hθ]; ring⟩
    have hθV : θ ∈ V := by
      have h1 : minorIJ H I₀ S ∈ V.toSubring := CPts.minorIJ_mem _ (fun a c => by rw [hHV]; exact ((Hv * B) a c).2) _ _
      rw [show θ = minorIJ H I₀ S * (η * minorIJ h I₀ S)⁻¹ by rw [hθ, mul_inv_cancel_right₀ hI₀]]
      exact V.mul_mem _ _ h1 (hOV' _ hI₀')
    have hθO : θ ∈ O := by
      obtain ⟨o, ho, e1⟩ := hA E hEO
      rw [minor_self_of_lower _ _ fun a _ c _ l => hLo.2 _ _ l, Finset.prod_eq_one fun c _ => hLo.1 c] at e1
      have e2 : o⁻¹ = θ := inv_eq_of_mul_eq_one_left e1.symm
      rw [← e2] at hθV ⊢
      exact dom o ho (right_ne_zero_of_mul_eq_one e1.symm) hθV
    obtain ⟨o, ho, e1⟩ := hA (E.updateRow c (E r)) fun a c' => by
      rw [updateRow_apply]; split_ifs <;> exact hEO _ _
    have e3 : E.updateRow c (E r) * H = (E * H).updateRow c ((E * H) r) := by
      ext a c'
      by_cases e : a = c
      · subst e; simp [Matrix.mul_apply]
      · simp [Matrix.mul_apply, updateRow_ne e]
    rw [e3, minor_self_of_lower _ _ fun a ha c' hc' l => by
      rw [updateRow_ne (fun e : a = c => absurd (hmax c' hc') (not_le.2 (e ▸ l))), hLo.2 _ _ l],
      Finset.prod_eq_single c (fun a _ ha => by rw [updateRow_ne ha, hLo.1]) (fun h => absurd hc h),
      updateRow_self] at e1
    rw [e1]
    exact O.mul_mem hθO ho
  have invO : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → A.det⁻¹ ∈ O → ∀ a c, A⁻¹ a c ∈ O := by
    intro A hA hdA a c
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
    refine O.mul_mem hdA (CPts.det_mem O fun x y => ?_)
    rw [updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      exacts [O.one_mem, O.zero_mem]
    · exact hA _ _
  have hEd : E.det ≠ 0 := left_ne_zero_of_mul_eq_one hdEH
  have hEi : E.det⁻¹ ∈ O := dom _ (CPts.det_mem O hEO) hEd (by
    rw [inv_eq_of_mul_eq_one_right hdEH]
    exact CPts.det_mem V.toSubring fun a c => by rw [hHV]; exact ((Hv * B) a c).2)
  have hHO : ∀ a c, H a c ∈ O := fun a c => by
    rw [← Matrix.nonsing_inv_mul_cancel_left E H hEd.isUnit, Matrix.mul_apply]
    exact sum_mem fun x _ => O.mul_mem (invO E hEO hEi _ _) (hLoO _ _)
  refine ⟨b₀ * B', hbb, hbt, hbd, hHO, invO H hHO ?_⟩
  rw [inv_eq_of_mul_eq_one_left hdEH]
  exact CPts.det_mem O hEO

end PositivityTheory.Xgp.W
