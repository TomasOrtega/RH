import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

/- English proof (translation)
Introduce `v hv`. Establish `hlen : (a ++ List.replicate (p - a.length - b.length) 0 ++ b).length = p`. Simplify using `only [List.length_append, List.length_replicate]`. Use linear arithmetic over natural numbers and integers. Take `⟨i, hi, rfl⟩` from `List.getElem_of_mem hv`.

Establish `h1` using `h ⟨i, hlen ▸ hi⟩`. Simplify using `only [pad, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at h1`. Conclude with `h1` after adjusting the coercions.
-/
theorem pad_all (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    ∀ v ∈ a ++ List.replicate (p - a.length - b.length) 0 ++ b, v = z := by
  intro v hv
  have hlen : (a ++ List.replicate (p - a.length - b.length) 0 ++ b).length = p := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have h1 := h ⟨i, hlen ▸ hi⟩
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at h1
  exact_mod_cast h1

/- English proof (translation)
Establish `hall` using `pad_all a b p hl z h`. Establish `hb' : b = []`. Break down `b with _ | ⟨v, b⟩` into its components or cases. Both sides reduce to the same expression. It suffices to derive a contradiction.

Establish `h1` using `hall v (by simp)`. Establish `h2` using `hb v (by simp)`. Use linear arithmetic over natural numbers and integers. Substitute `hb'` using the available equality. Establish `hk : p - a.length - ([] : List ℤ).length = 0`.

Assume the negation of the conclusion as `hne`. Use `hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩, rfl⟩` and prove the remaining obligations. Simplify using `only [List.length_nil] at hk hl`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pad_pos (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : 0 < z)
    (hb : ∀ v ∈ b, v < 0)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = List.replicate p z ∧ b = [] := by
  have hall := pad_all a b p hl z h
  have hb' : b = [] := by
    rcases b with _ | ⟨v, b⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := hb v (by simp)
      omega
  subst hb'
  have hk : p - a.length - ([] : List ℤ).length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩, rfl⟩
  simp only [List.length_nil] at hk hl
  omega

/- English proof (translation)
Establish `hall` using `pad_all a b p hl z h`. Establish `ha' : a = []`. Break down `a with _ | ⟨v, a⟩` into its components or cases. Both sides reduce to the same expression. It suffices to derive a contradiction.

Establish `h1` using `hall v (by simp)`. Establish `h2` using `ha v (by simp)`. Use linear arithmetic over natural numbers and integers. Substitute `ha'` using the available equality. Establish `hk : p - ([] : List ℤ).length - b.length = 0`.

Assume the negation of the conclusion as `hne`. Use `hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨rfl, List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩⟩` and prove the remaining obligations. Simplify using `only [List.length_nil] at hk hl`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pad_neg (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : z < 0)
    (ha : ∀ v ∈ a, 0 < v)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = [] ∧ b = List.replicate p z := by
  have hall := pad_all a b p hl z h
  have ha' : a = [] := by
    rcases a with _ | ⟨v, a⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := ha v (by simp)
      omega
  subst ha'
  have hk : p - ([] : List ℤ).length - b.length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨rfl, List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩⟩
  simp only [List.length_nil] at hk hl
  omega

/- English proof (translation)
Simplify using `only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append, List.getElem?_replicate, List.length_replicate]`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
theorem getD_pad_left (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by
  simp only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

/- English proof (translation)
Simplify using `only [pad, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append, List.getElem?_replicate, List.length_replicate]`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
theorem getD_pad_right (q r i : ℕ) (z : ℤ) (hq : q ≤ r) (hi : i < r) :
    (pad [] (r - q) (List.replicate q z)).getD i 0 = if r ≤ i + q then (z : ℚ) else 0 := by
  simp only [pad, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x`. Break down `x with k | l` into its components or cases. Apply the tactic sequence `simp only [shiftNu, laPos, ofBlocks, getD_pad_left] split_ifs <;> push_cast <;> ring`. Apply the tactic sequence `simp only [shiftNu, laPos, ofBlocks, getD_pad_left] split_ifs <;> push_cast <;> ring`.
-/
theorem shift_pos_eq (p q r s n m : ℕ) :
    shiftNu (cPair p q) (laPos p q r s n m) =
      ofBlocks (pad (List.replicate p (n : ℤ)) (r - p) []) (pad (List.replicate q (m : ℤ)) (s - q) []) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Break down `x with k | l` into its components or cases. Apply the tactic sequence `simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt] split_ifs <;> push_cast <;> ring`. Apply the tactic sequence `simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt] split_ifs <;> push_cast <;> ring`.
-/
theorem shift_neg_eq (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt]
    split_ifs <;> push_cast <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `congrFun h x` as an intermediate fact. Apply the tactic sequence `rcases x with k | l <;> simp only [shiftNu] at this <;> linarith`.
-/
theorem shiftNu_inj {r s : ℕ} (c : ℚ) {μ ν : Ix r s → ℚ} (h : shiftNu c μ = shiftNu c ν) : μ = ν := by
  funext x
  have := congrFun h x
  rcases x with k | l <;> simp only [shiftNu] at this <;> linarith

/- English proof (translation)
Establish `hn' : (0 : ℤ) < (n : ℤ)` using `by exact_mod_cast hn`. Establish `hm' : (0 : ℤ) < (m : ℤ)` using `by exact_mod_cast hm`. Use `⟨⟨List.replicate p (n : ℤ), [], List.replicate q (m : ℤ), [], ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => by simp at hv, fun v hv => by simp at hv, List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, ?_, …` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using `using hp`. Simplify using `using hq`. Use function extensionality and compare the values at `x`. Break down `x with i | j` into its components or cases.

Simplify using `only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self, Nat.zero_sub, getD_pad_left, i.isLt, if_true]`. Rewrite using `[h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self, Nat.zero_sub, getD_pad_left, j.isLt, if_true]`.

Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [List.length_replicate, List.length_nil, Nat.sub_zero]`. Conclude with `shift_pos_eq p q r s n m`.

Introduce and unpack `ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩`. Establish `hA` using `pad_pos a b p hab (n : ℤ) hn' hb (fun i => by`. Establish `hx` using `congrFun hs1 (Sum.inl i)`. Simplify using `only [shiftNu, ofBlocks] at hx`. Rewrite using `[← hx, h1]`.

Use `push_cast`. Use the proof step `ring)`. Establish `hC` using `pad_pos c d q hcd (m : ℤ) hm' hd (fun j => by`. Establish `hx` using `congrFun hs1 (Sum.inr j)`. Simplify using `only [shiftNu, ofBlocks] at hx`.

Rewrite using `[← hx, h2]`. Use `push_cast`. Use the proof step `ring)`. Take `⟨rfl, rfl⟩` from `hA`. Take `⟨rfl, rfl⟩` from `hC`.

Apply `shiftNu_inj (cPair p q)` to reduce the goal to its premises. Rewrite using `[hs2, shift_pos_eq]`. Simplify using `only [List.length_replicate, List.length_nil, Nat.sub_zero]`.
-/
theorem shape_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) :
    JointShape p q r s (fun _ => c0) (laPos p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laPos p q r s n m := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  refine ⟨⟨List.replicate p (n : ℤ), [], List.replicate q (m : ℤ), [], ?_⟩, ?_⟩
  · refine ⟨fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', fun v hv => (List.eq_of_mem_replicate hv) ▸ hm',
      fun v hv => by simp at hv, fun v hv => by simp at hv,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hp
    · simpa using hq
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, i.isLt, if_true]
        rw [h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, j.isLt, if_true]
        rw [h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_pos_eq p q r s n m
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_pos a b p hab (n : ℤ) hn' hb (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_pos c d q hcd (m : ℤ) hm' hd (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_pos_eq]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

/- English proof (translation)
Establish `hn' : (-(n : ℤ)) < 0`. Establish `: (0 : ℤ) < (n : ℤ)` using `by exact_mod_cast hn`. Use linear arithmetic over natural numbers and integers. Establish `hm' : (-(m : ℤ)) < 0`. Establish `: (0 : ℤ) < (m : ℤ)` using `by exact_mod_cast hm`.

Use linear arithmetic over natural numbers and integers. Use `⟨⟨[], List.replicate p (-(m : ℤ)), [], List.replicate q (-(n : ℤ)), ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨fun v hv => by simp at hv, fun v hv => by simp at hv, fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), ?_, …` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using `using hq`. Simplify using `using hp`. Use function extensionality and compare the values at `x`. Break down `x with i | j` into its components or cases. Simplify using `only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self, Nat.sub_zero]`.

Establish `e` using `getD_pad_right p p i (-(m : ℤ)) le_rfl i.isLt`. Rewrite `e` using `[Nat.sub_self, if_pos (by omega)]`. Rewrite using `[e, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self, Nat.sub_zero]`. Establish `e` using `getD_pad_right q q j (-(n : ℤ)) le_rfl j.isLt`. Rewrite `e` using `[Nat.sub_self, if_pos (by omega)]`. Rewrite using `[e, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [List.length_replicate, List.length_nil, Nat.sub_zero]`. Conclude with `shift_neg_eq p q r s n m hq hp`. Introduce and unpack `ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩`. Establish `hA` using `pad_neg a b p hab (-(m : ℤ)) hm' ha (fun i => by`.

Establish `hx` using `congrFun hs1 (Sum.inl i)`. Simplify using `only [shiftNu, ofBlocks] at hx`. Rewrite using `[← hx, h1]`. Use `push_cast`. Use the proof step `ring)`.

Establish `hC` using `pad_neg c d q hcd (-(n : ℤ)) hn' hc (fun j => by`. Establish `hx` using `congrFun hs1 (Sum.inr j)`. Simplify using `only [shiftNu, ofBlocks] at hx`. Rewrite using `[← hx, h2]`. Use `push_cast`.

Use the proof step `ring)`. Take `⟨rfl, rfl⟩` from `hA`. Take `⟨rfl, rfl⟩` from `hC`. Apply `shiftNu_inj (cPair p q)` to reduce the goal to its premises. Rewrite using `[hs2, shift_neg_eq p q r s n m hq hp]`.

Simplify using `only [List.length_replicate, List.length_nil, Nat.sub_zero]`.
-/
theorem shape_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) :
    JointShape p q r s (fun _ => c0) (laNeg p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laNeg p q r s n m := by
  have hn' : (-(n : ℤ)) < 0 := by
    have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  have hm' : (-(m : ℤ)) < 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    omega
  refine ⟨⟨[], List.replicate p (-(m : ℤ)), [], List.replicate q (-(n : ℤ)), ?_⟩, ?_⟩
  · refine ⟨fun v hv => by simp at hv, fun v hv => by simp at hv,
      fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => (List.eq_of_mem_replicate hv) ▸ hn',
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl),
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hq
    · simpa using hp
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right p p i (-(m : ℤ)) le_rfl i.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right q q j (-(n : ℤ)) le_rfl j.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_neg_eq p q r s n m hq hp
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_neg a b p hab (-(m : ℤ)) hm' ha (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_neg c d q hcd (-(n : ℤ)) hn' hc (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_neg_eq p q r s n m hq hp]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

end PositivityTheory.KReal

end
