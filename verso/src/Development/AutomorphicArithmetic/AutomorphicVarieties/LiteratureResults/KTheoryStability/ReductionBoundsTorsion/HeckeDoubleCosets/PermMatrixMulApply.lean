import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section Perm

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Simplify using `[Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]`.
-/
theorem permMatrix_apply' (σ : Equiv.Perm n) (i j : n) :
    (σ.permMatrix R) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, permMatrix_apply', ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem permMatrix_mul_apply (σ τ : Equiv.Perm n) (i j : n) :
    (σ.permMatrix R * τ.permMatrix R) i j = if τ (σ i) = j then 1 else 0 := by
  simp only [Matrix.mul_apply, permMatrix_apply', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

def permU (σ : Equiv.Perm n) : GL n R :=
  ⟨σ.permMatrix R, σ⁻¹.permMatrix R, by
    ext i j
    rw [permMatrix_mul_apply, Matrix.one_apply]
    simp, by
    ext i j
    rw [permMatrix_mul_apply, Matrix.one_apply]
    simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem permU_coe (σ : Equiv.Perm n) : ((permU σ : GL n R) : Matrix n n R) = σ.permMatrix R := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem permU_inv_coe (σ : Equiv.Perm n) : (((permU σ)⁻¹ : GL n R) : Matrix n n R) = σ⁻¹.permMatrix R := rfl

end Perm

section Basic

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qel_coe (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) :
    ((qel L N π hπ : GK L N) : Matrix (Fin N) (Fin N) L) =
      diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toK_coe (N : ℕ) (γ : Gm L N) (i j : Fin N) :
    ((toK L N γ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) i j =
      algebraMap (𝓞 L) L ((γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) := rfl

/- English proof (translation)
The claim follows from `FaithfulSMul.algebraMap_injective (𝓞 L) L`.
-/
theorem algebraMap_inj : Function.Injective (algebraMap (𝓞 L) L) :=
  FaithfulSMul.algebraMap_injective (𝓞 L) L

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨x, ⟨δ, rfl⟩, hx⟩` from `Subgroup.mem_map.1 (Subgroup.mem_comap.1 h)`. Use `⟨δ, ?_⟩` and prove the remaining obligations. Establish `hx' : (qel L N π hπ)⁻¹ * toK L N δ * qel L N π hπ = toK L N γ`.

Simplify `hx` using `[MulAut.conj_apply]`. Rewrite using `[← hx']`. Use `group`. Introduce and unpack `⟨δ, h⟩`. Use `Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨toK L N δ, ⟨δ, rfl⟩, ?_⟩)` and prove the remaining obligations.

Use `show (MulAut.conj (qel L N π hπ)⁻¹) (toK L N δ) = toK L N γ`. Rewrite using `[MulAut.conj_apply, inv_inv, mul_assoc, h]`. Use `group`.
-/
theorem mem_Gq_iff' (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) (γ : Gm L N) :
    γ ∈ Gq (toK L N) (qel L N π hπ) ↔ ∃ δ : Gm L N, toK L N δ * qel L N π hπ = qel L N π hπ * toK L N γ := by
  constructor
  · intro h
    obtain ⟨x, ⟨δ, rfl⟩, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 h)
    refine ⟨δ, ?_⟩
    have hx' : (qel L N π hπ)⁻¹ * toK L N δ * qel L N π hπ = toK L N γ := by
      simpa [MulAut.conj_apply] using hx
    rw [← hx']
    group
  · rintro ⟨δ, h⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨toK L N δ, ⟨δ, rfl⟩, ?_⟩)
    show (MulAut.conj (qel L N π hπ)⁻¹) (toK L N δ) = toK L N γ
    rw [MulAut.conj_apply, inv_inv, mul_assoc, h]
    group

/- English proof (translation)
Rewrite using `[mem_Gq_iff']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ, h⟩ i j hj hi`. Establish `e` using `congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h`. Simplify using `only [Units.val_mul, qel_coe, Matrix.mul_diagonal, Matrix.diagonal_mul, hj, hi, if_true, if_false, toK_coe, one_mul] at e`.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨(δ : Matrix (Fin N) (Fin N) (𝓞 L)) i j, algebraMap_inj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `e`. Introduce `h`.

Establish `hd : ∀ i j : Fin N, (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 → ∃ a : 𝓞 L, a * π = (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j` using `fun i j hij => Ideal.mem_span_singleton'.1 (h i j hij.1 hij.2)`. Set `M : Matrix (Fin N) (Fin N) (𝓞 L)` to `Matrix.of fun i j => if hij : (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then Classical.choose (hd i j hij) else if (i : ℕ) = 0 ∧ (j : ℕ) ≠ 0 then π * (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j else (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j`. Establish `hM : M.map (algebraMap (𝓞 L) L) * diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) = diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) * (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (algebraMap (𝓞 L) L)`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, M, Matrix.of_apply]`.

Apply the tactic sequence `by_cases hj : (j : ℕ) = 0 <;> by_cases hi : (i : ℕ) = 0`. Rewrite using `[dif_neg (by tauto), if_neg (by tauto), if_pos hj, if_pos hi, mul_comm]`. Rewrite using `[dif_pos ⟨hj, hi⟩, if_pos hj, if_neg hi, one_mul]`. Establish `hs` using `Classical.choose_spec (hd i j ⟨hj, hi⟩)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[dif_neg (by tauto), if_pos ⟨hi, hj⟩, if_neg hj, if_pos hi, mul_one, map_mul]`. Rewrite using `[dif_neg (by tauto), if_neg (by tauto), if_neg hj, if_neg hi, mul_one, one_mul]`. Establish `hdet : M.det = (γ : Matrix (Fin N) (Fin N) (𝓞 L)).det`. Apply `algebraMap_inj` to reduce the goal to its premises. Establish `e` using `congrArg Matrix.det hM`.

Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, mul_comm]`. Establish `hne : (diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1)).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `fun h0 => hπ (algebraMap_inj (by simpa using h0))`. Conclude with `one_ne_zero`. Establish `e'` using `mul_left_cancel₀ hne e`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Conclude with `e'`.

Establish `hu : IsUnit M.det` using `hdet ▸ Matrix.isUnits_det_units γ`. Use `⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hu, Matrix.nonsing_inv_mul M hu⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, qel_coe]`. Conclude with `hM`.
-/
theorem mem_Gq_iff (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) (γ : Gm L N) :
    γ ∈ Gq (toK L N) (qel L N π hπ) ↔
      ∀ i j : Fin N, (j : ℕ) = 0 → (i : ℕ) ≠ 0 → (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j ∈ Ideal.span {π} := by
  rw [mem_Gq_iff']
  constructor
  · rintro ⟨δ, h⟩ i j hj hi
    have e := congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h
    simp only [Units.val_mul, qel_coe, Matrix.mul_diagonal, Matrix.diagonal_mul, hj, hi, if_true,
      if_false, toK_coe, one_mul] at e
    rw [Ideal.mem_span_singleton']
    refine ⟨(δ : Matrix (Fin N) (Fin N) (𝓞 L)) i j, algebraMap_inj ?_⟩
    rw [map_mul]
    exact e
  · intro h
    have hd : ∀ i j : Fin N, (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 →
        ∃ a : 𝓞 L, a * π = (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j hij =>
      Ideal.mem_span_singleton'.1 (h i j hij.1 hij.2)
    let M : Matrix (Fin N) (Fin N) (𝓞 L) := Matrix.of fun i j =>
      if hij : (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then Classical.choose (hd i j hij)
      else if (i : ℕ) = 0 ∧ (j : ℕ) ≠ 0 then π * (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j
      else (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j
    have hM : M.map (algebraMap (𝓞 L) L) * diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) =
        diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) *
          (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (algebraMap (𝓞 L) L) := by
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, M, Matrix.of_apply]
      by_cases hj : (j : ℕ) = 0 <;> by_cases hi : (i : ℕ) = 0
      · rw [dif_neg (by tauto), if_neg (by tauto), if_pos hj, if_pos hi, mul_comm]
      · rw [dif_pos ⟨hj, hi⟩, if_pos hj, if_neg hi, one_mul]
        have hs := Classical.choose_spec (hd i j ⟨hj, hi⟩)
        calc _ = algebraMap (𝓞 L) L (Classical.choose (hd i j ⟨hj, hi⟩) * π) := by rw [map_mul]
          _ = _ := by rw [hs]
      · rw [dif_neg (by tauto), if_pos ⟨hi, hj⟩, if_neg hj, if_pos hi, mul_one, map_mul]
      · rw [dif_neg (by tauto), if_neg (by tauto), if_neg hj, if_neg hi, mul_one, one_mul]
    have hdet : M.det = (γ : Matrix (Fin N) (Fin N) (𝓞 L)).det := by
      apply algebraMap_inj
      have e := congrArg Matrix.det hM
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at e
      have hne : (diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1)).det ≠ 0 := by
        rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
        split_ifs
        · exact fun h0 => hπ (algebraMap_inj (by simpa using h0))
        · exact one_ne_zero
      have e' := mul_left_cancel₀ hne e
      rw [RingHom.map_det, RingHom.map_det]
      exact e'
    have hu : IsUnit M.det := hdet ▸ Matrix.isUnits_det_units γ
    refine ⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hu, Matrix.nonsing_inv_mul M hu⟩, ?_⟩
    apply Units.ext
    simp only [Units.val_mul, qel_coe]
    exact hM

end Basic

section Index

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Use `Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hπ.ne_zero`.
-/
theorem span_isMaximal {π : 𝓞 L} (hπ : Prime π) : (Ideal.span {π} : Ideal (𝓞 L)).IsMaximal := by
  refine Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hπ.ne_zero

/- English proof (translation)
Introduce `h` and use `(span_isMaximal hπ).ne_top ((Ideal.eq_top_iff_one _).2 h)`.
-/
theorem one_not_mem_span {π : 𝓞 L} (hπ : Prime π) : (1 : 𝓞 L) ∉ Ideal.span {π} := fun h =>
  (span_isMaximal hπ).ne_top ((Ideal.eq_top_iff_one _).2 h)

/- English proof (translation)
Use `haveI := span_isMaximal hπ`. Break down `N with _ | N` into its components or cases. Use `haveI : Subsingleton (Gm L 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => i.elim0)⟩ haveI : Finite (Gm L 0) := Finite.of_subsingleton`. Conclude with `Quotient.finite _`. Set `f : Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero))) → (Fin (N + 1) → 𝓞 L ⧸ Ideal.span {π})` to `fun x l => Ideal.Quotient.mk _ (((x.out⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0)`.

Use `Finite.of_injective f fun x y hxy => ?_` and prove the remaining obligations. Rewrite using `[← Quotient.out_eq x, ← Quotient.out_eq y]`. Apply `Quotient.sound` to reduce the goal to its premises. Use `QuotientGroup.rightRel_apply.2 ?_` and prove the remaining obligations. Rewrite using `[mem_Gq_iff]`.

Introduce `i j hj hi`. Establish `hj' : j = 0` using `Fin.ext hj`. Substitute `hj'` using the available equality. Use `set a := x.out`. Use `set b := y.out`.

Establish `e1 : ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l * ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 = 0`. Use `congrFun (congrFun (Units.mul_inv b) i) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this, Matrix.one_apply, if_neg]`. Conclude with `fun h => hi (by rw [h]; rfl)`.

Establish `hmem : ∀ l, ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 - ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 ∈ Ideal.span {π}` using `fun l => Ideal.Quotient.eq.1 (congrFun hxy l)`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Establish `: ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l * ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 = ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l * (((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 - ((b⁻¹ : Gm L (N + …`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, e1, sub_zero]`. Rewrite using `[this]`.

Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hmem l)`.
-/
theorem finite_cosets (N : ℕ) (π : 𝓞 L) (hπ : Prime π) :
    Finite (Quotient (QuotientGroup.rightRel (Gq (toK L N) (qel L N π hπ.ne_zero)))) := by
  haveI := span_isMaximal hπ
  rcases N with _ | N
  · haveI : Subsingleton (Gm L 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Finite (Gm L 0) := Finite.of_subsingleton
    exact Quotient.finite _
  · let f : Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero))) →
        (Fin (N + 1) → 𝓞 L ⧸ Ideal.span {π}) := fun x l =>
      Ideal.Quotient.mk _ (((x.out⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0)
    refine Finite.of_injective f fun x y hxy => ?_
    rw [← Quotient.out_eq x, ← Quotient.out_eq y]
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.2 ?_
    rw [mem_Gq_iff]
    intro i j hj hi
    have hj' : j = 0 := Fin.ext hj
    subst hj'
    set a := x.out
    set b := y.out
    have e1 : ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 = 0 := by
      have := congrFun (congrFun (Units.mul_inv b) i) 0
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.one_apply, if_neg]
      exact fun h => hi (by rw [h]; rfl)
    have hmem : ∀ l, ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 -
        ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 ∈ Ideal.span {π} := fun l =>
      Ideal.Quotient.eq.1 (congrFun hxy l)
    rw [Units.val_mul, Matrix.mul_apply]
    have : ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 =
        ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        (((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 -
          ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0) := by
      simp only [mul_sub, Finset.sum_sub_distrib, e1, sub_zero]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hmem l)

/- English proof (translation)
Introduce `L _ _ N π hπ`. Establish `hfin` using `finite_cosets N π hπ`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]`. Break down `N with _ | N` into its components or cases.

Conclude with `Nat.zero_le _`. Set `g : Fin (N + 1) → Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero)))` to `fun j => Quotient.mk _ (permU (Equiv.swap 0 j))`. Establish `hg : Function.Injective g`. Introduce `j k hjk`. Assume the negation of the conclusion as `hne`.

Establish `h` using `QuotientGroup.rightRel_apply.1 (Quotient.exact hjk)`. Rewrite `h` using `[mem_Gq_iff]`. Establish `hk0 : ((Equiv.swap 0 k) j : ℕ) ≠ 0`. Introduce `h0`. Establish `: (Equiv.swap 0 k) j = 0` using `Fin.ext h0`.

Rewrite `this` using `[Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]`. Conclude with `hne this`. Use `h ((Equiv.swap 0 k) j) 0 rfl hk0` as an intermediate fact. Rewrite `this` using `[Units.val_mul, permU_coe, permU_inv_coe, permMatrix_mul_apply, if_pos]`. Conclude with `one_not_mem_span hπ this`.

Simplify using `[Equiv.swap_apply_self]`. Use `Nat.card_le_card_of_injective g hg` as an intermediate fact. Simplify using `using this`.
-/
theorem pIndex : PIndex := by
  intro L _ _ N π hπ
  have hfin := finite_cosets N π hπ
  refine ⟨hfin, ?_⟩
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rcases N with _ | N
  · exact Nat.zero_le _
  let g : Fin (N + 1) → Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero))) :=
    fun j => Quotient.mk _ (permU (Equiv.swap 0 j))
  have hg : Function.Injective g := by
    intro j k hjk
    by_contra hne
    have h := QuotientGroup.rightRel_apply.1 (Quotient.exact hjk)
    rw [mem_Gq_iff] at h
    have hk0 : ((Equiv.swap 0 k) j : ℕ) ≠ 0 := by
      intro h0
      have : (Equiv.swap 0 k) j = 0 := Fin.ext h0
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at this
      exact hne this
    have := h ((Equiv.swap 0 k) j) 0 rfl hk0
    rw [Units.val_mul, permU_coe, permU_inv_coe, permMatrix_mul_apply, if_pos] at this
    · exact one_not_mem_span hπ this
    · simp [Equiv.swap_apply_self]
  have := Nat.card_le_card_of_injective g hg
  simpa using this

end Index

section Stab

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Introduce `L _ _ π hπ n r hn`. Prove the components needed by the constructor for the conclusion. Introduce `c`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Rewrite using `[toK_coe, stab_apply, stab_apply]`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[stab_apply, qel_coe, qel_coe]`. Simplify using `only [Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [Fin.ext_iff] <;> omega`.
-/
theorem pStabK : PStabK := by
  intro L _ _ π hπ n r hn
  constructor
  · intro c
    apply Units.ext
    ext i j
    rw [toK_coe, stab_apply, stab_apply]
    split_ifs with h1 h2
    · rfl
    · simp
    · simp
  · apply Units.ext
    ext i j
    rw [stab_apply, qel_coe, qel_coe]
    simp only [Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/- English proof (translation)
Introduce `L _ _ π hπ n r hn c`. Rewrite using `[mem_Gq_iff, mem_Gq_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hj hi`. Use `h (Fin.castAdd r i) (Fin.castAdd r j) hj hi` as an intermediate fact.

Rewrite `this` using `[stab_apply, dif_pos ⟨i.2, j.2⟩]`. Then use the resulting hypothesis. Introduce `h i j hj hi`. Rewrite using `[stab_apply]`. Use `split_ifs with h1 h2`. Conclude with `h _ _ hj hi`.

Conclude with `absurd (congrArg Fin.val h2) (by omega)`. Conclude with `Submodule.zero_mem _`.
-/
theorem pGqStab : PGqStab := by
  intro L _ _ π hπ n r hn c
  rw [mem_Gq_iff, mem_Gq_iff]
  constructor
  · intro h i j hj hi
    have := h (Fin.castAdd r i) (Fin.castAdd r j) hj hi
    rwa [stab_apply, dif_pos ⟨i.2, j.2⟩] at this
  · intro h i j hj hi
    rw [stab_apply]
    split_ifs with h1 h2
    · exact h _ _ hj hi
    · exact absurd (congrArg Fin.val h2) (by omega)
    · exact Submodule.zero_mem _

end Stab

section Low

variable {R : Type} [CommRing R]

/- English proof (translation)
Set `z : Fin n` to `⟨0, hn⟩`. Set `σ : Equiv.Perm (Fin n)` to `Equiv.swap z a`. Set `W : Fin n → R` to `v ∘ σ`. Establish `hW : W z ∉ I` using `by simpa [W, σ] using ha`. Take `⟨s, t, ht, hst⟩` from `hI.exists_inv hW`.

Set `Nm : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i j => if (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then s * W i else 0`. Establish `hNN : Nm * Nm = 0`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Nm, Matrix.of_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs with h1 h2 <;> first | simp | exact absurd h1.1 h2.2`. Set `U : Matrix (Fin n) (Fin n) R` to `1 - Nm`. Establish `hU : U * (1 + Nm) = 1`. Simplify using `only [U, sub_mul, one_mul, mul_add, mul_one, hNN, add_zero]`. Normalize the expressions using the abelian group laws.

Set `M : Matrix (Fin n) (Fin n) R` to `U * σ.permMatrix R`. Establish `hM : IsUnit M.det`. Rewrite using `[Matrix.det_mul, Matrix.det_permutation]`. Use `(Matrix.isUnit_det_of_right_inverse hU).mul ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Use `⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hM, Matrix.nonsing_inv_mul M hM⟩, fun i hi => ?_⟩` and prove the remaining obligations. Use `show (M *ᵥ v) i ∈ I`. Establish `e : M *ᵥ v = U *ᵥ W`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]`. Rewrite using `[e]`.

Establish `e3 : (Nm *ᵥ W) i = s * W i * W z`. Simplify using `only [Matrix.mulVec, dotProduct, Nm, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single z]`. Simplify using `[z, hi]`. Introduce `b _ hb`.

Rewrite using `[if_neg, zero_mul]`. Conclude with `fun h => hb (Fin.ext h.1)`. Simplify using the standard rewrite rules. Establish `e2 : (U *ᵥ W) i = W i * t`. Rewrite using `[show U = 1 - Nm from rfl, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, e3, show t = 1 - s * W z by rw [← hst]; ring]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `I.mul_mem_left _ ht`.
-/
theorem exists_clear (n : ℕ) (hn : 1 ≤ n) (I : Ideal R) (hI : I.IsMaximal) (v : Fin n → R)
    (a : Fin n) (ha : v a ∉ I) :
    ∃ c' : GL (Fin n) R, ∀ i : Fin n, (i : ℕ) ≠ 0 → ((c' : Matrix (Fin n) (Fin n) R) *ᵥ v) i ∈ I := by
  let z : Fin n := ⟨0, hn⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap z a
  let W : Fin n → R := v ∘ σ
  have hW : W z ∉ I := by simpa [W, σ] using ha
  obtain ⟨s, t, ht, hst⟩ := hI.exists_inv hW
  let Nm : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then s * W i else 0
  have hNN : Nm * Nm = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Nm, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h1 h2 <;> first | simp | exact absurd h1.1 h2.2
  let U : Matrix (Fin n) (Fin n) R := 1 - Nm
  have hU : U * (1 + Nm) = 1 := by
    simp only [U, sub_mul, one_mul, mul_add, mul_one, hNN, add_zero]
    abel
  let M : Matrix (Fin n) (Fin n) R := U * σ.permMatrix R
  have hM : IsUnit M.det := by
    rw [Matrix.det_mul, Matrix.det_permutation]
    refine (Matrix.isUnit_det_of_right_inverse hU).mul ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine ⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hM, Matrix.nonsing_inv_mul M hM⟩, fun i hi => ?_⟩
  show (M *ᵥ v) i ∈ I
  have e : M *ᵥ v = U *ᵥ W := by
    rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  rw [e]
  have e3 : (Nm *ᵥ W) i = s * W i * W z := by
    simp only [Matrix.mulVec, dotProduct, Nm, Matrix.of_apply]
    rw [Finset.sum_eq_single z]
    · simp [z, hi]
    · intro b _ hb
      rw [if_neg, zero_mul]
      exact fun h => hb (Fin.ext h.1)
    · simp
  have e2 : (U *ᵥ W) i = W i * t := by
    rw [show U = 1 - Nm from rfl, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, e3,
      show t = 1 - s * W z by rw [← hst]; ring]
    ring
  rw [e2]
  exact I.mul_mem_left _ ht

end Low

/- English proof (translation)
Introduce `L _ _ π hπ n r hn c hc`. Establish `hmax` using `span_isMaximal hπ`. Set `z0 : Fin (n + r)` to `⟨0, by omega⟩`. Set `v : Fin n → 𝓞 L` to `fun a => ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r a) z0`. Establish `hex : ∃ a, v a ∉ Ideal.span {π}`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hall : ∀ l : Fin (n + r), ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) l z0 ∈ Ideal.span {π}`. Introduce `l`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) l` and prove the remaining obligations.

Conclude with `hcon a`. Conclude with `hc b`. Establish `h1` using `congrFun (congrFun (Units.mul_inv c) z0) z0`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Apply `one_not_mem_span hπ` to reduce the goal to its premises.

Rewrite using `[← h1]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hall l)`. Take `⟨a, ha⟩` from `hex`. Take `⟨c', hc'⟩` from `exists_clear n hn _ hmax v a ha`. Use `⟨c', ?_⟩` and prove the remaining obligations.

Rewrite using `[← Subgroup.inv_mem_iff, _root_.mul_inv_rev, inv_inv, mem_Gq_iff]`. Introduce `i j hj hi`. Establish `hj' : j = z0` using `Fin.ext hj`. Substitute `hj'` using the available equality. Rewrite using `[Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]`.

Consider the cases of `i using Fin.addCases with`. Consider the case `left i'`. Establish `hi' : (i' : ℕ) ≠ 0` using `by simpa using hi`. Establish `e : ∑ b : Fin r, (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c' : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r i') (Fin.natAdd n b) * ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n b) z0 = 0`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega), zero_mul]`. Rewrite using `[e, add_zero]`. Use `hc' i' hi'` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Use `this using 2 with b _` and compare the differences between its conclusion and the goal.

Rewrite using `[stab_apply, dif_pos ⟨by simp, by simp⟩]`. Both sides reduce to the same expression. Consider the case `right i'`. Use `Ideal.add_mem _ (Ideal.sum_mem _ fun b _ => ?_) (Ideal.sum_mem _ fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega), zero_mul]`.

Conclude with `Submodule.zero_mem _`. Conclude with `Ideal.mul_mem_left _ _ (hc b)`.
-/
theorem pLow : PLow := by
  intro L _ _ π hπ n r hn c hc
  have hmax := span_isMaximal hπ
  let z0 : Fin (n + r) := ⟨0, by omega⟩
  let v : Fin n → 𝓞 L := fun a =>
    ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r a) z0
  have hex : ∃ a, v a ∉ Ideal.span {π} := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ l : Fin (n + r),
        ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) l z0 ∈ Ideal.span {π} := by
      intro l
      refine Fin.addCases (fun a => ?_) (fun b => ?_) l
      · exact hcon a
      · exact hc b
    have h1 := congrFun (congrFun (Units.mul_inv c) z0) z0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    apply one_not_mem_span hπ
    rw [← h1]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hall l)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨c', hc'⟩ := exists_clear n hn _ hmax v a ha
  refine ⟨c', ?_⟩
  rw [← Subgroup.inv_mem_iff, _root_.mul_inv_rev, inv_inv, mem_Gq_iff]
  intro i j hj hi
  have hj' : j = z0 := Fin.ext hj
  subst hj'
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  cases i using Fin.addCases with
  | left i' =>
    have hi' : (i' : ℕ) ≠ 0 := by simpa using hi
    have e : ∑ b : Fin r, (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c' : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
        (Fin.castAdd r i') (Fin.natAdd n b) *
        ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n b) z0 = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
        zero_mul]
    rw [e, add_zero]
    have := hc' i' hi'
    simp only [Matrix.mulVec, dotProduct] at this
    convert this using 2 with b _
    rw [stab_apply, dif_pos ⟨by simp, by simp⟩]
    rfl
  | right i' =>
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun b _ => ?_) (Ideal.sum_mem _ fun b _ => ?_)
    · rw [stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
        zero_mul]
      exact Submodule.zero_mem _
    · exact Ideal.mul_mem_left _ _ (hc b)

end PositivityTheory.KB.AffineStabilizerVanishing

end
