import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Consider the cases of `x with`. Consider the case `top => exact le_top`. Consider the case `coe z => simp`.
-/
theorem coe_untopD_le_alt (x : WithTop ℤ) (d : ℤ) : ((x.untopD d : ℤ) : WithTop ℤ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe z => simp

/- English proof (translation)
Consider the cases of `x with`. Consider the case `top => simpa using hd`. Consider the case `coe z => simpa using h`.
-/
theorem le_untopD_of_coe_le {x : WithTop ℤ} {c d : ℤ} (h : ((c : ℤ) : WithTop ℤ) ≤ x) (hd : c ≤ d) : c ≤ x.untopD d := by
  cases x with
  | top => simpa using hd
  | coe z => simpa using h

/- English proof (translation)
Consider the cases of `x with`. Consider the case `bot => exact bot_le`. Consider the case `coe z => simp`.
-/
theorem le_coe_unbotD' (x : WithBot ℤ) (d : ℤ) : x ≤ ((x.unbotD d : ℤ) : WithBot ℤ) := by
  cases x with
  | bot => exact bot_le
  | coe z => simp

/- English proof (translation)
Consider the cases of `x with`. Consider the case `bot => simpa using hd`. Consider the case `coe z => simpa using h`.
-/
theorem unbotD_le_of_le_coe {x : WithBot ℤ} {c d : ℤ} (h : x ≤ ((c : ℤ) : WithBot ℤ)) (hd : d ≤ c) : x.unbotD d ≤ c := by
  cases x with
  | bot => simpa using hd
  | coe z => simpa using h

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs _ a`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `by ext; simp`.

Rewrite using `[h0, P.zero]`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `hs hv a`. Establish `hsN : s < N` using `by omega`.

Establish `h1` using `P.step ⟨s, hsN⟩`. Rewrite `h1` using `[if_pos (hv ⟨s, hsN⟩ (by simp))]`. Establish `h2` using `ih (by omega) (fun i hi => hv i (by omega)) a`. Establish `h3` using `h1.1 a`. Conclude with `le_trans h2 h3`.
-/
theorem lattice_path_nonneg_prefix {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) :
    ∀ (s : ℕ) (hs : s < N + 1), (∀ i : Fin N, i.val < s → LL.vec i = true) → ∀ a, 0 ≤ P.mu ⟨s, hs⟩ a := by
  intro s
  induction s with
  | zero =>
    intro hs _ a
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := by ext; simp
    rw [h0, P.zero]; simp
  | succ s ih =>
    intro hs hv a
    have hsN : s < N := by omega
    have h1 := P.step ⟨s, hsN⟩
    rw [if_pos (hv ⟨s, hsN⟩ (by simp))] at h1
    have h2 := ih (by omega) (fun i hi => hv i (by omega)) a
    have h3 := h1.1 a
    exact le_trans h2 h3

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs _`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `by ext; simp`.

Rewrite using `[h0, P.zero]`. Consider the case `succ s ih`. Introduce `hs hv`. Establish `hsN : s < N` using `by omega`. Establish `h1` using `P.step ⟨s, hsN⟩`.

Rewrite `h1` using `[if_pos (hv ⟨s, hsN⟩ (by simp)).1, (hv ⟨s, hsN⟩ (by simp)).2]`. Establish `h2 : P.mu (Fin.castSucc ⟨s, hsN⟩) = 0` using `ih (by omega) (fun i hi => hv i (by omega))`. Take `⟨g1, _, g3⟩` from `h1`. Establish `g4` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sub_nonneg.2 (g1 a))).1 (by simpa using g3)`. Use function extensionality and compare the values at `a`.

Establish `g5` using `g4 a (Finset.mem_univ a)`. Rewrite `g5` using `[h2]`. Establish `g6 : P.mu (Fin.succ ⟨s, hsN⟩) a = 0` using `by simpa using g5`. Conclude with `g6`.
-/
theorem lattice_path_zero_prefix {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) :
    ∀ (s : ℕ) (hs : s < N + 1), (∀ i : Fin N, i.val < s → LL.vec i = true ∧ B i = 0) → P.mu ⟨s, hs⟩ = 0 := by
  intro s
  induction s with
  | zero =>
    intro hs _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := by ext; simp
    rw [h0, P.zero]
  | succ s ih =>
    intro hs hv
    have hsN : s < N := by omega
    have h1 := P.step ⟨s, hsN⟩
    rw [if_pos (hv ⟨s, hsN⟩ (by simp)).1, (hv ⟨s, hsN⟩ (by simp)).2] at h1
    have h2 : P.mu (Fin.castSucc ⟨s, hsN⟩) = 0 := ih (by omega) (fun i hi => hv i (by omega))
    obtain ⟨g1, _, g3⟩ := h1
    have g4 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sub_nonneg.2 (g1 a))).1 (by simpa using g3)
    funext a
    have g5 := g4 a (Finset.mem_univ a)
    rw [h2] at g5
    have g6 : P.mu (Fin.succ ⟨s, hsN⟩) a = 0 := by simpa using g5
    exact g6

section Fr

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `Finset.mem_filter.1 hx`. Establish `hx3` using `(Finset.mem_Icc.1 hx1).1`. Establish `claim : ∀ i, i < r → x ≤ F.fr (j - 1) i → ∃ i', i' < r ∧ x = F.fr (j - 1) i'`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro h0 h`. Conclude with `⟨0, h0, le_antisymm h hx3⟩`. Consider the case `succ i ih`. Introduce `hi h`. Distinguish the cases in `h1 : x ≤ F.fr (j - 1) i`.

Conclude with `ih (by omega) h1`. Distinguish the cases in `h2 : x = F.fr (j - 1) (i + 1)`. Conclude with `⟨i + 1, hi, h2⟩`. Conclude with `absurd hx2 (hV.2.2.2.2.2.1 (j - 1) i x hi (by omega) (by omega))`. Take `⟨i', hi', rfl⟩` from `claim (r - 1) (by omega) hW`.

Conclude with `(hV.2.2.2.2.1 (j - 1) i' hi').2`.
-/
theorem even_of_lower_letter (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j x : ℤ) (hx : x ∈ F.letters j) (hW : F.IsW j x) : Even x := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
  have hx3 := (Finset.mem_Icc.1 hx1).1
  have claim : ∀ i, i < r → x ≤ F.fr (j - 1) i → ∃ i', i' < r ∧ x = F.fr (j - 1) i' := by
    intro i
    induction i with
    | zero => intro h0 h; exact ⟨0, h0, le_antisymm h hx3⟩
    | succ i ih =>
      intro hi h
      by_cases h1 : x ≤ F.fr (j - 1) i
      · exact ih (by omega) h1
      · by_cases h2 : x = F.fr (j - 1) (i + 1)
        · exact ⟨i + 1, hi, h2⟩
        · exact absurd hx2 (hV.2.2.2.2.2.1 (j - 1) i x hi (by omega) (by omega))
  obtain ⟨i', hi', rfl⟩ := claim (r - 1) (by omega) hW
  exact (hV.2.2.2.2.1 (j - 1) i' hi').2

/- English proof (translation)
The claim follows from `((F.letters j).orderEmbOfFin rfl).monotone h`.
-/
theorem letter_enum_mono (j : ℤ) {i i' : Fin (Mj F j)} (h : i ≤ i') : eL F j i ≤ eL F j i' :=
  ((F.letters j).orderEmbOfFin rfl).monotone h

/- English proof (translation)
The claim follows from `Finset.orderEmbOfFin_mem _ _ _`.
-/
theorem letter_enum_mem (j : ℤ) (i : Fin (Mj F j)) : eL F j i ∈ F.letters j :=
  Finset.orderEmbOfFin_mem _ _ _

/- English proof (translation)
Establish `h1` using `frame_first_entry_le hV (j - 1) (r - 1) (by omega)`. Establish `h2` using `hV.2.2.2.1 (j - 1)`. Establish `h3` using `frame_first_entry_le hV j (r - 1) (by omega)`. Rewrite `h2` using `[sub_add_cancel]`. Establish `hmem : F.fr (j - 1) 0 ∈ F.letters j` using `Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 (by omega)).1⟩`.

Establish `hr' : F.fr (j - 1) 0 ∈ Set.range ((F.letters j).orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hmem`. Take `⟨i0, hi0⟩` from `hr'`. Establish `h4 : eL F j i ≤ eL F j i0` using `letter_enum_mono F j (by rw [Fin.le_def]; omega)`.

Establish `h5 : eL F j i0 = F.fr (j - 1) 0` using `hi0`. Unfold `Frames.IsW`. Use linear arithmetic over natural numbers and integers.
-/
theorem first_letter_is_lower (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : Fin (Mj F j)) (hi : i.val = 0) :
    F.IsW j (eL F j i) := by
  have h1 := frame_first_entry_le hV (j - 1) (r - 1) (by omega)
  have h2 := hV.2.2.2.1 (j - 1)
  have h3 := frame_first_entry_le hV j (r - 1) (by omega)
  rw [sub_add_cancel] at h2
  have hmem : F.fr (j - 1) 0 ∈ F.letters j :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 (by omega)).1⟩
  have hr' : F.fr (j - 1) 0 ∈ Set.range ((F.letters j).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hmem
  obtain ⟨i0, hi0⟩ := hr'
  have h4 : eL F j i ≤ eL F j i0 := letter_enum_mono F j (by rw [Fin.le_def]; omega)
  have h5 : eL F j i0 = F.fr (j - 1) 0 := hi0
  unfold Frames.IsW
  omega

end Fr

section Main

/- English proof (translation)
Establish `step1 : ∀ a ∈ SA, e (f a * h G) ∈ Submodule.span O T`. Introduce `a ha`. Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem b hb => exact key a ha b hb`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, mul_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul, mul_smul_comm, map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Proceed by induction on `hA using Submodule.span_induction with`.

Consider the case `mem a ha => exact step1 a ha`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, add_mul, map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul, smul_mul_assoc, map_smul]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem span_mul_image_mem_span {O : Type} [CommRing O] {σ τ υ : Type} (f : MvPolynomial σ O →ₐ[O] MvPolynomial υ O)
    (h : MvPolynomial τ O →ₐ[O] MvPolynomial υ O) {ρ : Type} (e : MvPolynomial υ O →ₐ[O] MvPolynomial ρ O)
    (SA : Set (MvPolynomial σ O)) (SG : Set (MvPolynomial τ O)) (T : Set (MvPolynomial ρ O))
    (key : ∀ a ∈ SA, ∀ b ∈ SG, e (f a * h b) ∈ Submodule.span O T)
    {A : MvPolynomial σ O} (hA : A ∈ Submodule.span O SA) {G : MvPolynomial τ O} (hG : G ∈ Submodule.span O SG) :
    e (f A * h G) ∈ Submodule.span O T := by
  have step1 : ∀ a ∈ SA, e (f a * h G) ∈ Submodule.span O T := by
    intro a ha
    induction hG using Submodule.span_induction with
    | mem b hb => exact key a ha b hb
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, mul_add, map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, mul_smul_comm, map_smul]; exact Submodule.smul_mem _ c hx
  induction hA using Submodule.span_induction with
  | mem a ha => exact step1 a ha
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul, map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ X j P hP`. Take `⟨d', d'', A, G, Mx, hA, hG, hW, hC, rfl⟩` from `hP`. Establish `hr : 1 ≤ r` using `by have := X.hH.2.1; omega`. Establish `hMK : Mj X.Fr j + r ≤ K`. Establish `h1 : Mj X.Fr j ≤ X.N₁` using `X.hV.2.2.2.2.2.2.2.1 j`.

Establish `h2` using `X.hK`. Use linear arithmetic over natural numbers and integers. Set `nxt : Fin (Mj X.Fr j) → Fin (Mj X.Fr j)` to `fun i => if h : i.val + 1 < Mj X.Fr j then ⟨i.val + 1, h⟩ else i`. Set `thA : Fin (Mj X.Fr j) → ℤ` to `fun i => (valS (LLs X.Fr j).toLetters {y | y ≤ i} A).untopD (max (Mx i) (Mx (nxt i)))`. Set `MA : Fin (Mj X.Fr j) → ℤ` to `fun i => (lam1S (LLs X.Fr j).toLetters {y | y ≤ i} A).unbotD 0`.

Set `thG : Fin (Mj X.Fr j) → ℤ` to `fun i => (valS (LLs X.Fr j).toLetters {y | y ≤ i} G).untopD 0`. Set `MG : Fin (Mj X.Fr j) → ℤ` to `fun i => (lam1S (LLs X.Fr j).toLetters {y | y ≤ i} G).unbotD (min (Mx i) (Mx (nxt i)))`. Establish `hAs` using `(hA3 p O X.S (Mj X.Fr j) r (LLs X.Fr j).toLetters d' thA MA).1`. Establish `hGs` using `(hA3 p O X.S (Mj X.Fr j) K (LLs X.Fr j).toLetters d'' thG MG).1`. Unfold `A3at at hAs hGs`.

Establish `hA'` using `(Set.ext_iff.1 hAs A).1 ⟨hA, fun i => ⟨coe_untopD_le_alt _ _, le_coe_unbotD' _ _⟩⟩`. Establish `hG'` using `(Set.ext_iff.1 hGs G).1 ⟨hG, fun i => ⟨coe_untopD_le_alt _ _, le_coe_unbotD' _ _⟩⟩`. Use `span_mul_image_mem_span (rename (plVar (K := K))) (rename (tanVar (r := r))) (plnm X.Fr j O K) _ _ _ ?_ hA' hG'` and prove the remaining obligations. Introduce and unpack `_ ⟨P1, I', hI', h1, rfl⟩ _ ⟨P2, I'', hI'', h2, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Establish `hpred : ∀ i : Fin (Mj X.Fr j), ¬ X.Fr.IsW j (eL X.Fr j i) → ∃ i' : Fin (Mj X.Fr j), i'.succ = i.castSucc ∧ nxt i' = i ∧ ({y | y < i} : Set (Fin (Mj X.Fr j))) = {y | y ≤ i'}`. Introduce `i hi`. Establish `h0 : i.val ≠ 0` using `fun h => hi (first_letter_is_lower X.Fr X.hV hr j i h)`. Use `⟨⟨i.val - 1, by omega⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `h3 : i.val - 1 + 1 < Mj X.Fr j` using `by have := i.2; omega show (if h : i.val - 1 + 1 < Mj X.Fr j then (⟨i.val - 1 + 1, h⟩ : Fin (Mj X.Fr j)) else _) = i`. Rewrite using `[dif_pos h3]`. Use `ext`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Use extensionality with `y show y < i ↔ y ≤ (⟨i.val - 1, by omega⟩ : Fin (Mj X.Fr j))`. Rewrite using `[Fin.lt_def, Fin.le_def]`. Use `show y.val < i.val ↔ y.val ≤ i.val - 1`.

Use linear arithmetic over natural numbers and integers. Establish `hCond : ∀ i, CondC (LLs X.Fr j).toLetters P1.mu P2.mu i`. Introduce `i`. Unfold `CondC`. Distinguish the cases in `hiW : X.Fr.IsW j (eL X.Fr j i)`.

Establish `hWle : ∀ i' : Fin (Mj X.Fr j), i'.val < i.val + 1 → X.Fr.IsW j (eL X.Fr j i')`. Introduce `i' hi'`. Use `letter_enum_mono X.Fr j (show i' ≤ i by rw [Fin.le_def]; omega)` as an intermediate fact. Unfold `Frames.IsW at hiW ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hvec : ∀ i' : Fin (Mj X.Fr j), i'.val < i.val + 1 → (LLs X.Fr j).toLetters.vec i' = true`. Introduce `i' hi'`. Use `show decide (Even (eL X.Fr j i')) = true`. Conclude with `decide_eq_true (even_of_lower_letter X.Fr X.hV hr j _ (letter_enum_mem X.Fr j i') (hWle i' hi'))`. Rewrite using `[if_pos (hvec i (by omega))]`.

Establish `hz : P2.mu i.succ = 0` using `lattice_path_zero_prefix P2 (i.val + 1) (by have := i.2; omega) (fun i' hi' => ⟨hvec i' hi', hW i' (hWle i' hi')⟩)`. Establish `hn : 0 ≤ P1.mu i.castSucc (lastIdx r)` using `lattice_path_nonneg_prefix P1 i.val (by have := i.2; omega) (fun i' hi' => hvec i' (by omega)) _`. Rewrite using `[hz]`. Conclude with `hn`. Take `⟨i', e1, e2, e3⟩` from `hpred i hiW`.

Take `⟨c1, c2⟩` from `hC i hiW`. Distinguish the cases in `hE : Even (eL X.Fr j i)`. Establish `hv : (LLs X.Fr j).toLetters.vec i = true` using `decide_eq_true hE`. Rewrite using `[if_pos hv]`. Take `⟨g1, g2⟩` from `c1 hE`.

Rewrite `g2` using `[add_zero, e3]`. Establish `k1 : P2.mu i.succ 0 ≤ Mx i` using `le_trans (h2 i).2 (unbotD_le_of_le_coe g1 (min_le_left _ _))`. Establish `k2 : Mx i ≤ P1.mu i'.succ (lastIdx r)` using `le_trans (le_untopD_of_coe_le g2 (by rw [e2]; exact le_max_right _ _)) (h1 i').1`. Rewrite using `[← e1]`. Conclude with `le_trans k1 k2`.

Establish `hv : ¬ (LLs X.Fr j).toLetters.vec i = true`. Introduce `h`. Conclude with `hE (of_decide_eq_true h)`. Rewrite using `[if_neg hv]`. Take `⟨g1, g2⟩` from `c2 hE`.

Rewrite `g2` using `[add_zero]`. Rewrite `g1` using `[e3]`. Establish `k1 : P2.mu i'.succ 0 ≤ Mx i` using `le_trans (h2 i').2 (unbotD_le_of_le_coe g1 (by rw [e2]; exact min_le_right _ _))`. Establish `k2 : Mx i ≤ P1.mu i.succ (lastIdx r)` using `le_trans (le_untopD_of_coe_le g2 (le_max_left _ _)) (h1 i).1`. Rewrite using `[← e1]`.

Conclude with `le_trans k1 k2`. Take `⟨Pth, hPth⟩` from `(hB1 (Mj X.Fr j) r K (LLs X.Fr j).toLetters (fun i => d' i + d'' i) hMK P1.mu P2.mu).2 ⟨d', d'', fun _ => rfl, ⟨P1, rfl⟩, ⟨P2, rfl⟩, hCond⟩`. Conclude with `⟨_, Pth, P1.mu, P2.mu, I', I'', hPth, hI', hI'', rfl⟩`.
-/
theorem generator_pair_conditions_of_admitted (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.SourceCleaning.StandardMonomialSpanBis D) (hB1 : Formalism.MainNotions.SourceCleaning.PathPairCorrespondence D) : GeneratorSpanInclusion := by
  intro p n' r K _ _ _ _ O _ _ _ _ X j P hP
  obtain ⟨d', d'', A, G, Mx, hA, hG, hW, hC, rfl⟩ := hP
  have hr : 1 ≤ r := by have := X.hH.2.1; omega
  have hMK : Mj X.Fr j + r ≤ K := by
    have h1 : Mj X.Fr j ≤ X.N₁ := X.hV.2.2.2.2.2.2.2.1 j
    have h2 := X.hK
    omega
  let nxt : Fin (Mj X.Fr j) → Fin (Mj X.Fr j) := fun i => if h : i.val + 1 < Mj X.Fr j then ⟨i.val + 1, h⟩ else i
  let thA : Fin (Mj X.Fr j) → ℤ := fun i =>
    (valS (LLs X.Fr j).toLetters {y | y ≤ i} A).untopD (max (Mx i) (Mx (nxt i)))
  let MA : Fin (Mj X.Fr j) → ℤ := fun i => (lam1S (LLs X.Fr j).toLetters {y | y ≤ i} A).unbotD 0
  let thG : Fin (Mj X.Fr j) → ℤ := fun i => (valS (LLs X.Fr j).toLetters {y | y ≤ i} G).untopD 0
  let MG : Fin (Mj X.Fr j) → ℤ := fun i =>
    (lam1S (LLs X.Fr j).toLetters {y | y ≤ i} G).unbotD (min (Mx i) (Mx (nxt i)))
  have hAs := (hA3 p O X.S (Mj X.Fr j) r (LLs X.Fr j).toLetters d' thA MA).1
  have hGs := (hA3 p O X.S (Mj X.Fr j) K (LLs X.Fr j).toLetters d'' thG MG).1
  unfold A3at at hAs hGs
  have hA' := (Set.ext_iff.1 hAs A).1 ⟨hA, fun i => ⟨coe_untopD_le_alt _ _, le_coe_unbotD' _ _⟩⟩
  have hG' := (Set.ext_iff.1 hGs G).1 ⟨hG, fun i => ⟨coe_untopD_le_alt _ _, le_coe_unbotD' _ _⟩⟩
  refine span_mul_image_mem_span (rename (plVar (K := K))) (rename (tanVar (r := r))) (plnm X.Fr j O K) _ _ _ ?_ hA' hG'
  rintro _ ⟨P1, I', hI', h1, rfl⟩ _ ⟨P2, I'', hI'', h2, rfl⟩
  apply Submodule.subset_span

  have hpred : ∀ i : Fin (Mj X.Fr j), ¬ X.Fr.IsW j (eL X.Fr j i) →
      ∃ i' : Fin (Mj X.Fr j), i'.succ = i.castSucc ∧ nxt i' = i ∧
        ({y | y < i} : Set (Fin (Mj X.Fr j))) = {y | y ≤ i'} := by
    intro i hi
    have h0 : i.val ≠ 0 := fun h => hi (first_letter_is_lower X.Fr X.hV hr j i h)
    refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_, ?_⟩
    · ext; simp; omega
    · have h3 : i.val - 1 + 1 < Mj X.Fr j := by have := i.2; omega
      show (if h : i.val - 1 + 1 < Mj X.Fr j then (⟨i.val - 1 + 1, h⟩ : Fin (Mj X.Fr j)) else _) = i
      rw [dif_pos h3]
      ext; simp; omega
    · ext y
      show y < i ↔ y ≤ (⟨i.val - 1, by omega⟩ : Fin (Mj X.Fr j))
      rw [Fin.lt_def, Fin.le_def]
      show y.val < i.val ↔ y.val ≤ i.val - 1
      omega
  have hCond : ∀ i, CondC (LLs X.Fr j).toLetters P1.mu P2.mu i := by
    intro i
    unfold CondC
    by_cases hiW : X.Fr.IsW j (eL X.Fr j i)
    ·
      have hWle : ∀ i' : Fin (Mj X.Fr j), i'.val < i.val + 1 → X.Fr.IsW j (eL X.Fr j i') := by
        intro i' hi'
        have := letter_enum_mono X.Fr j (show i' ≤ i by rw [Fin.le_def]; omega)
        unfold Frames.IsW at hiW ⊢
        omega
      have hvec : ∀ i' : Fin (Mj X.Fr j), i'.val < i.val + 1 → (LLs X.Fr j).toLetters.vec i' = true := by
        intro i' hi'
        show decide (Even (eL X.Fr j i')) = true
        exact decide_eq_true (even_of_lower_letter X.Fr X.hV hr j _ (letter_enum_mem X.Fr j i') (hWle i' hi'))
      rw [if_pos (hvec i (by omega))]
      have hz : P2.mu i.succ = 0 :=
        lattice_path_zero_prefix P2 (i.val + 1) (by have := i.2; omega) (fun i' hi' => ⟨hvec i' hi', hW i' (hWle i' hi')⟩)
      have hn : 0 ≤ P1.mu i.castSucc (lastIdx r) :=
        lattice_path_nonneg_prefix P1 i.val (by have := i.2; omega) (fun i' hi' => hvec i' (by omega)) _
      rw [hz]
      exact hn
    · obtain ⟨i', e1, e2, e3⟩ := hpred i hiW
      obtain ⟨c1, c2⟩ := hC i hiW
      by_cases hE : Even (eL X.Fr j i)
      · have hv : (LLs X.Fr j).toLetters.vec i = true := decide_eq_true hE
        rw [if_pos hv]
        obtain ⟨g1, g2⟩ := c1 hE
        rw [add_zero, e3] at g2
        have k1 : P2.mu i.succ 0 ≤ Mx i := le_trans (h2 i).2 (unbotD_le_of_le_coe g1 (min_le_left _ _))
        have k2 : Mx i ≤ P1.mu i'.succ (lastIdx r) :=
          le_trans (le_untopD_of_coe_le g2 (by rw [e2]; exact le_max_right _ _)) (h1 i').1
        rw [← e1]
        exact le_trans k1 k2
      · have hv : ¬ (LLs X.Fr j).toLetters.vec i = true := by
          intro h; exact hE (of_decide_eq_true h)
        rw [if_neg hv]
        obtain ⟨g1, g2⟩ := c2 hE
        rw [add_zero] at g2
        rw [e3] at g1
        have k1 : P2.mu i'.succ 0 ≤ Mx i :=
          le_trans (h2 i').2 (unbotD_le_of_le_coe g1 (by rw [e2]; exact min_le_right _ _))
        have k2 : Mx i ≤ P1.mu i.succ (lastIdx r) := le_trans (le_untopD_of_coe_le g2 (le_max_left _ _)) (h1 i).1
        rw [← e1]
        exact le_trans k1 k2
  obtain ⟨Pth, hPth⟩ := (hB1 (Mj X.Fr j) r K (LLs X.Fr j).toLetters (fun i => d' i + d'' i) hMK P1.mu P2.mu).2
    ⟨d', d'', fun _ => rfl, ⟨P1, rfl⟩, ⟨P2, rfl⟩, hCond⟩
  exact ⟨_, Pth, P1.mu, P2.mu, I', I'', hPth, hI', hI'', rfl⟩

end Main

end Formalism.MainNotions.G.symbolGeneratorData
