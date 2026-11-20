import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaE
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BigCellLocal

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

def ee (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (m + m) := (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv

/- English proof (translation)
Use extensionality with `(i | i) (j | j)`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, finSumFinEquiv_apply_left, Fin.val_castAdd, fromBlocks_apply₁₁, Matrix.zero_apply]`. Rewrite using `[if_neg (by omega)]`.

Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd, fromBlocks_apply₁₂, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, …`. Conclude with `if_congr (by omega) rfl rfl`. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Simplify using `only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd, fromBlocks_apply₂₁, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, …`. Conclude with `if_congr (by omega) rfl rfl`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Simplify using `only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd, fromBlocks_apply₂₂, Matrix.zero_apply, Fin.revPerm_apply, Fin.val_rev]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem antiJ_submatrix (L : Type) [Field L] (m : ℕ) :
    (antiJ L (m + m)).submatrix (ee m) (ee m) = Wm L (Fin m) := by
  ext (i | i) (j | j)
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
      finSumFinEquiv_apply_left, Fin.val_castAdd, fromBlocks_apply₁₁, Matrix.zero_apply]
    rw [if_neg (by omega)]
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₁₂, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₂₁, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, fromBlocks_apply₂₂, Matrix.zero_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [if_neg (by omega)]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Wm, Matrix.one_apply, apply_ite f]`.
-/
theorem Wm_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (β : Type) [DecidableEq β] :
    (Wm A β).map f = Wm B β := by
  ext (i | i) (j | j) <;> simp [Wm, Matrix.one_apply, apply_ite f]

section

variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]

/- English proof (translation)
Establish `hcc : ∀ N : Matrix (β ⊕ β) (β ⊕ β) L, (N.map c).map c = N` using `fun N => Matrix.ext fun i j => hc _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun N => N.map c) h` as an intermediate fact. Simplify using `only [Matrix.map_mul, Wm_map, hcc] at this`.

Conclude with `this`. Introduce `h`. Use `congrArg (fun N => N.map c) h` as an intermediate fact. Simplify using `only [Matrix.map_mul, Wm_map] at this`. Rewrite `this` using `[cT, transpose_map, hcc]`.

Conclude with `this`.
-/
theorem iso_iff_cT (hc : ∀ x, c (c x) = x) (M : Matrix (β ⊕ β) (β ⊕ β) L) :
    Iso c (Wm L β) (Wm L β) M ↔ cT c M * Wm L β * M = Wm L β := by
  have hcc : ∀ N : Matrix (β ⊕ β) (β ⊕ β) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map] at this
    rw [cT, transpose_map, hcc] at this
    exact this

/- English proof (translation)
Establish `h1` using `(iso_iff_cT hc M).1 h`. Establish `h2 : Wm L β * cT c M * Wm L β * M = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c M), h1, Wm_mul_self]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_eq_of_iso (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) : N = Wm L β * cT c M * Wm L β := by
  have h1 := (iso_iff_cT hc M).1 h
  have h2 : Wm L β * cT c M * Wm L β * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c M), h1, Wm_mul_self]
  calc N = (Wm L β * cT c M * Wm L β * M) * N := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc _ M, hN, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[inv_eq_of_iso hc h hN]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Wm, cT, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem inv_apply_of_iso (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) (i j : β ⊕ β) : N i j = c (M j.swap i.swap) := by
  rw [inv_eq_of_iso hc h hN]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Wm, cT, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

end

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

/- English proof (translation)
Establish `hW : antiJ L (m + m) = (Wm L (Fin m)).submatrix (ee m).symm (ee m).symm`. Rewrite using `[← antiJ_submatrix]`. Simplify using the standard rewrite rules. Establish `h1 : fIwasawaUn c (M.submatrix (ee m).symm (ee m).symm)`. Unfold `fIwasawaUn`.

Rewrite using `[hW]`. Express the relevant statement in the definitionally equal form `(cT c M).submatrix (ee m).symm (ee m).symm * _ * _ = _`. Rewrite using `[submatrix_mul_equiv, submatrix_mul_equiv, (iso_iff_cT hc M).1 hM]`. Take `⟨k, hk, hT⟩` from `fIwasawa_upper c hc hv _ h1`. Use `⟨k.submatrix (ee m) (ee m), (iso_iff_cT hc _).2 ?_, fun i j => hk.2 _ _, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[← antiJ_submatrix]`. Express the relevant statement in the definitionally equal form `(cT c k).submatrix (ee m) (ee m) * _ * _ = _`. Rewrite using `[submatrix_mul_equiv, submatrix_mul_equiv, hk.1]`. Establish `e : k.submatrix (ee m) (ee m) * M = (k * M.submatrix (ee m).symm (ee m).symm).submatrix (ee m) (ee m)`. Rewrite using `[← submatrix_mul_equiv k _ (ee m) (ee m) (ee m)]`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `hT ?_` and prove the remaining obligations. Use `j.2` as an intermediate fact. Express the relevant statement in the definitionally equal form `(ee m (Sum.inl j)).val < (ee m (Sum.inr i)).val`.

Simplify using `only [ee, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_reduce (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hM : Iso c (Wm L (Fin m)) (Wm L (Fin m)) M) :
    ∃ k, Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧ (∀ i j, Valued.v (k i j) ≤ 1) ∧
      ∀ i j, (k * M) (Sum.inr i) (Sum.inl j) = 0 := by
  have hW : antiJ L (m + m) = (Wm L (Fin m)).submatrix (ee m).symm (ee m).symm := by
    rw [← antiJ_submatrix]; simp
  have h1 : fIwasawaUn c (M.submatrix (ee m).symm (ee m).symm) := by
    unfold fIwasawaUn
    rw [hW]
    change (cT c M).submatrix (ee m).symm (ee m).symm * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, (iso_iff_cT hc M).1 hM]
  obtain ⟨k, hk, hT⟩ := fIwasawa_upper c hc hv _ h1
  refine ⟨k.submatrix (ee m) (ee m), (iso_iff_cT hc _).2 ?_, fun i j => hk.2 _ _, fun i j => ?_⟩
  · rw [← antiJ_submatrix]
    change (cT c k).submatrix (ee m) (ee m) * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, hk.1]
  · have e : k.submatrix (ee m) (ee m) * M = (k * M.submatrix (ee m).symm (ee m).symm).submatrix (ee m) (ee m) := by
      rw [← submatrix_mul_equiv k _ (ee m) (ee m) (ee m)]; simp
    rw [e]
    refine hT ?_
    have := j.2
    change (ee m (Sum.inl j)).val < (ee m (Sum.inr i)).val
    simp only [ee, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega

/- English proof (translation)
Take `⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩` from `hU`. Establish `hinv : ∀ g i j, Φ g⁻¹ i j = c (Φ g j.swap i.swap)` using `fun g => inv_apply_of_iso hc (hiso g) (by rw [← map_mul, mul_inv_cancel, map_one])`. Establish `hK' : ∀ g ∈ U, (∀ i j, Valued.v (Φ g i j) ≤ 1) → g ∈ K` using `fun g hg h => (hK g).2 ⟨hg, h, fun i j => by rw [hinv, hv]; exact h _ _⟩`. Use `⟨fun h hh => ?_, fun χ hχ h1 k hk => ?_⟩` and prove the remaining obligations. Take `⟨k, hk1, hk2, hk3⟩` from `exists_reduce hc hv _ (hiso h⁻¹)`.

Take `⟨g, hg, rfl⟩` from `surj k hk1`. Use `⟨(g * h⁻¹)⁻¹, hP _ (inv_mem (mul_mem hg (inv_mem hh))) fun i j => ?_, g, hK' g hg hk2, by group⟩` and prove the remaining obligations. Rewrite using `[hinv, map_mul]`. Conclude with `(congrArg c (hk3 j i)).trans (map_zero c)`. Set `A : Subring L` to `(Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring.toSubring haveI : IsLocalRing A := inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)`.

Establish `hA : ∀ z, z ∈ A ↔ Valued.v z ≤ 1` using `fun _ => Iff.rfl`. Set `σ : A →+* A` to `c.restrict A A fun z hz => by rw [hA, hv]; exact hz`. Establish `hσσ : ∀ z, σ (σ z) = z` using `fun z => Subtype.ext (hc z)`. Establish `hx0 : c x - x ≠ 0`. Introduce `h`.

Rewrite `hx1` using `[h, map_zero]`. Conclude with `zero_ne_one hx1`. Establish `hxi : (c x - x)⁻¹ ∈ A` using `by rw [hA, map_inv₀, hx1, inv_one]`. Establish `hz : IsUnit (σ ⟨x, hx⟩ - σ (σ ⟨x, hx⟩))`. Rewrite using `[hσσ]`.

Conclude with `IsUnit.of_mul_eq_one ⟨_, hxi⟩ (Subtype.ext (mul_inv_cancel₀ hx0))`. Establish `hw : σ ⟨x, hx⟩ * ⟨_, hxi⟩ + σ (σ ⟨x, hx⟩ * ⟨_, hxi⟩) = 1` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1`. Rewrite using `[map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Establish `hmap : ∀ N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A, Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N ↔ Iso c (Wm L (Fin m)) (Wm L (Fin m)) (N.map A.subtype)` using `fun N => by`. Unfold `Iso`. Rewrite using `[← Wm_map A.subtype, ← transpose_map]`. Express the relevant statement in the definitionally equal form `_ ↔ _ * _ * (N.map σ).map A.subtype = _`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `(Matrix.map_injective A.subtype_injective).eq_iff.symm`. Establish `lift : ∀ N, Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N → ∃ g ∈ U, g ∈ K ∧ Φ g = N.map A.subtype` using `fun N hN => by`. Take `⟨g, hg, e⟩` from `surj _ ((hmap N).1 hN)`. Conclude with `⟨g, hg, hK' g hg fun i j => by rw [e]; exact (N i j).2, e⟩`.

Take `⟨hkU, hk1, -⟩` from `(hK k).1 hk`. Set `H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A` to `Matrix.of fun i j => ⟨_, hk1 i j⟩`. Establish `eH : H.map A.subtype = Φ k` using `rfl`. Take `⟨s, u, t, b, d, i1, i2, i3, -, e⟩` from `decomp_split hσσ hw hz ((hmap H).2 (eH ▸ hiso k))`. Take `⟨g1, u1, k1, e1⟩` from `lift _ i1`.

Take `⟨g2, u2, k2, e2⟩` from `lift _ i2`. Take `⟨g3, u3, k3, e3⟩` from `lift _ i3`. Take `⟨w, uw, kw, ew⟩` from `lift _ (iso_Wm (σ := σ) (β := Fin m))`. Establish `hmul : ∀ g ∈ K, ∀ g' ∈ K, g * g' ∈ K` using `fun g hg g' hg' => by`. Take `⟨a1, a2, -⟩` from `(hK g).1 hg`.

Take `⟨b1, b2, -⟩` from `(hK g').1 hg'`. Use `hK' _ (mul_mem a1 b1) fun i j => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.mul_apply]`. Conclude with `A.sum_mem fun l _ => A.mul_mem (a2 _ _) (b2 _ _)`. Establish `p1 : χ g1 = 1` using `h1 _ k1 (hP _ u1 fun i j => by rw [e1]; rfl)`.

Establish `p2 : χ g2 = 1` using `h1 _ k2 (hP _ u2 fun i j => by rw [e2]; rfl)`. Establish `p3 : χ g3 = 1` using `h1 _ k3 (hP _ u3 fun i j => by rw [e3]; rfl)`. Establish `pw : χ w * χ w = 1`. Rewrite using `[← hχ w kw w kw]`. Use `h1 _ (hmul _ kw _ kw) (hP _ (mul_mem uw uw) fun i j => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, ew, ← Matrix.map_mul, Wm_mul_self]`. Simplify using the standard rewrite rules. Establish `ek : k = g1 * (w * g2 * w) * g3` using `inj _ hkU _ (mul_mem (mul_mem u1 (mul_mem (mul_mem uw u2) uw)) u3) (by`. Rewrite using `[← eH, e]`. Simplify using `only [map_mul, Matrix.map_mul, e1, e2, e3, ew])`.

Rewrite using `[ek, hχ _ (hmul _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw)) _ k3, hχ _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw), hχ _ (hmul _ kw _ k2) _ kw, hχ _ kw _ k2, p1, p2, p3, mul_one, mul_one, one_mul, pw]`.
-/
theorem group_main {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {m : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hiso : ∀ g, Iso c (Wm L (Fin m)) (Wm L (Fin m)) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (Wm L (Fin m)) (Wm L (Fin m)) M → ∃ g ∈ U, Φ g = M) (K P : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1)
    (hP : ∀ g ∈ U, (∀ i j, Φ g (Sum.inr i) (Sum.inl j) = 0) → g ∈ P) :
    (∀ h ∈ U, ∃ p ∈ P, ∃ k ∈ K, h = p * k) ∧
    ∀ χ : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, χ (k * k') = χ k * χ k') → (∀ k ∈ K, k ∈ P → χ k = 1) → ∀ k ∈ K, χ k = 1 := by
  obtain ⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hinv : ∀ g i j, Φ g⁻¹ i j = c (Φ g j.swap i.swap) := fun g =>
    inv_apply_of_iso hc (hiso g) (by rw [← map_mul, mul_inv_cancel, map_one])
  have hK' : ∀ g ∈ U, (∀ i j, Valued.v (Φ g i j) ≤ 1) → g ∈ K := fun g hg h =>
    (hK g).2 ⟨hg, h, fun i j => by rw [hinv, hv]; exact h _ _⟩
  refine ⟨fun h hh => ?_, fun χ hχ h1 k hk => ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := exists_reduce hc hv _ (hiso h⁻¹)
    obtain ⟨g, hg, rfl⟩ := surj k hk1
    refine ⟨(g * h⁻¹)⁻¹, hP _ (inv_mem (mul_mem hg (inv_mem hh))) fun i j => ?_, g, hK' g hg hk2, by group⟩
    rw [hinv, map_mul]
    exact (congrArg c (hk3 j i)).trans (map_zero c)
  · let A : Subring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring.toSubring
    haveI : IsLocalRing A :=
      inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
    have hA : ∀ z, z ∈ A ↔ Valued.v z ≤ 1 := fun _ => Iff.rfl
    let σ : A →+* A := c.restrict A A fun z hz => by rw [hA, hv]; exact hz
    have hσσ : ∀ z, σ (σ z) = z := fun z => Subtype.ext (hc z)
    have hx0 : c x - x ≠ 0 := by
      intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
    have hxi : (c x - x)⁻¹ ∈ A := by rw [hA, map_inv₀, hx1, inv_one]
    have hz : IsUnit (σ ⟨x, hx⟩ - σ (σ ⟨x, hx⟩)) := by
      rw [hσσ]
      exact IsUnit.of_mul_eq_one ⟨_, hxi⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
    have hw : σ ⟨x, hx⟩ * ⟨_, hxi⟩ + σ (σ ⟨x, hx⟩ * ⟨_, hxi⟩) = 1 := Subtype.ext (by
      change c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1
      rw [map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]
      field_simp
      ring)
    have hmap : ∀ N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A,
        Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N ↔ Iso c (Wm L (Fin m)) (Wm L (Fin m)) (N.map A.subtype) := fun N => by
      unfold Iso
      rw [← Wm_map A.subtype, ← transpose_map]
      change _ ↔ _ * _ * (N.map σ).map A.subtype = _
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact (Matrix.map_injective A.subtype_injective).eq_iff.symm
    have lift : ∀ N, Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N → ∃ g ∈ U, g ∈ K ∧ Φ g = N.map A.subtype := fun N hN => by
      obtain ⟨g, hg, e⟩ := surj _ ((hmap N).1 hN)
      exact ⟨g, hg, hK' g hg fun i j => by rw [e]; exact (N i j).2, e⟩
    obtain ⟨hkU, hk1, -⟩ := (hK k).1 hk
    let H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A := Matrix.of fun i j => ⟨_, hk1 i j⟩
    have eH : H.map A.subtype = Φ k := rfl
    obtain ⟨s, u, t, b, d, i1, i2, i3, -, e⟩ := decomp_split hσσ hw hz ((hmap H).2 (eH ▸ hiso k))
    obtain ⟨g1, u1, k1, e1⟩ := lift _ i1
    obtain ⟨g2, u2, k2, e2⟩ := lift _ i2
    obtain ⟨g3, u3, k3, e3⟩ := lift _ i3
    obtain ⟨w, uw, kw, ew⟩ := lift _ (iso_Wm (σ := σ) (β := Fin m))
    have hmul : ∀ g ∈ K, ∀ g' ∈ K, g * g' ∈ K := fun g hg g' hg' => by
      obtain ⟨a1, a2, -⟩ := (hK g).1 hg
      obtain ⟨b1, b2, -⟩ := (hK g').1 hg'
      refine hK' _ (mul_mem a1 b1) fun i j => ?_
      rw [map_mul, Matrix.mul_apply]
      exact A.sum_mem fun l _ => A.mul_mem (a2 _ _) (b2 _ _)
    have p1 : χ g1 = 1 := h1 _ k1 (hP _ u1 fun i j => by rw [e1]; rfl)
    have p2 : χ g2 = 1 := h1 _ k2 (hP _ u2 fun i j => by rw [e2]; rfl)
    have p3 : χ g3 = 1 := h1 _ k3 (hP _ u3 fun i j => by rw [e3]; rfl)
    have pw : χ w * χ w = 1 := by
      rw [← hχ w kw w kw]
      refine h1 _ (hmul _ kw _ kw) (hP _ (mul_mem uw uw) fun i j => ?_)
      rw [map_mul, ew, ← Matrix.map_mul, Wm_mul_self]
      simp
    have ek : k = g1 * (w * g2 * w) * g3 :=
      inj _ hkU _ (mul_mem (mul_mem u1 (mul_mem (mul_mem uw u2) uw)) u3) (by
        rw [← eH, e]
        simp only [map_mul, Matrix.map_mul, e1, e2, e3, ew])
    rw [ek, hχ _ (hmul _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw)) _ k3, hχ _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw),
      hχ _ (hmul _ kw _ k2) _ kw, hχ _ kw _ k2, p1, p2, p3, mul_one, mul_one, one_mul, pw]

end PositivityTheory.ThKH.Iwas
