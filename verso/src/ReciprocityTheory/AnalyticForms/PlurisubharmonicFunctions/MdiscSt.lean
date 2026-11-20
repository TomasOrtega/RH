import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscPos

namespace ReciprocityTheory.AnForm.A

open Matrix
open scoped ComplexOrder

variable {D : ℕ}

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose]`. Establish `h : (∑ k ∈ S, A k)ᵀ = fun j => ∑ k ∈ S, (fun i => A k i j)`. Use extensionality with `j i`. Simplify using `[Matrix.sum_apply, Finset.sum_apply]`. Rewrite using `[h]`.

Use `(Matrix.detRowAlternating (R := ℂ) (n := Fin D)).toMultilinearMap.map_sum_finset (fun j k => fun i => A k i j) (fun _ => S)` as an intermediate fact. Simplify using `only [AlternatingMap.coe_multilinearMap] at this`. Use `show Matrix.detRowAlternating _ = _`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun f _ => (Matrix.det_transpose _).symm`.
-/
private lemma det_sum_eq_pi (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (S : Finset (Fin D)) :
    (∑ k ∈ S, A k).det = ∑ f ∈ Fintype.piFinset (fun _ : Fin D => S),
      (Matrix.of fun i j => A (f j) i j).det := by
  classical
  rw [← Matrix.det_transpose]
  have h : (∑ k ∈ S, A k)ᵀ = fun j => ∑ k ∈ S, (fun i => A k i j) := by
    ext j i; simp [Matrix.sum_apply, Finset.sum_apply]
  rw [h]
  have := (Matrix.detRowAlternating (R := ℂ) (n := Fin D)).toMultilinearMap.map_sum_finset
    (fun j k => fun i => A k i j) (fun _ => S)
  simp only [AlternatingMap.coe_multilinearMap] at this
  show Matrix.detRowAlternating _ = _
  rw [this]
  exact Finset.sum_congr rfl fun f _ => (Matrix.det_transpose _).symm

/- English proof (translation)
Use `set T := Finset.univ.image f with hT`. Rewrite using `[← Equiv.sum_comp (Function.Involutive.toPerm _ (compl_involutive (α := Finset (Fin D))))]`. Establish `hc : ∀ U : Finset (Fin D), D - (Uᶜ).card = U.card`. Introduce `U`. Rewrite using `[Finset.card_compl, Fintype.card_fin]`.

Conclude with `Nat.sub_sub_self (by simpa using Finset.card_le_univ U)`. Establish `hmem : ∀ U : Finset (Fin D), f ∈ Fintype.piFinset (fun _ : Fin D => Uᶜ) ↔ U ∈ Tᶜ.powerset`. Introduce `U`. Simplify using `only [Fintype.mem_piFinset, Finset.mem_compl, Finset.mem_powerset, Finset.subset_iff, hT, Finset.mem_image, Finset.mem_univ, true_and, not_exists]`. Conclude with `⟨fun h x hx a ha => h a (ha ▸ hx), fun h a ha => h ha a rfl⟩`.

Simplify using `only [Function.Involutive.coe_toPerm, hc, hmem, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_mem, Finset.univ_inter]`. Establish `hz : (∑ U ∈ Tᶜ.powerset, (-1 : ℂ) ^ U.card) = ((∑ U ∈ Tᶜ.powerset, (-1 : ℤ) ^ U.card : ℤ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[hz, Finset.sum_powerset_neg_one_pow_card]`. Establish `hs : Tᶜ = ∅ ↔ Function.Surjective f`.

Rewrite using `[Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]`. Simplify using `[hT, Function.Surjective]`. Distinguish the cases in `h : Function.Surjective f`. Simplify using `[hs.2 h, h]`. Rewrite using `[if_neg (fun h' => h (hs.1 h')), if_neg h]`.

Simplify using the standard rewrite rules.
-/
private lemma sum_sign_indicator (f : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) *
      (if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) =
      if Function.Surjective f then 1 else 0 := by
  classical
  set T := Finset.univ.image f with hT
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (compl_involutive (α := Finset (Fin D))))]
  have hc : ∀ U : Finset (Fin D), D - (Uᶜ).card = U.card := by
    intro U
    rw [Finset.card_compl, Fintype.card_fin]
    exact Nat.sub_sub_self (by simpa using Finset.card_le_univ U)
  have hmem : ∀ U : Finset (Fin D),
      f ∈ Fintype.piFinset (fun _ : Fin D => Uᶜ) ↔ U ∈ Tᶜ.powerset := by
    intro U
    simp only [Fintype.mem_piFinset, Finset.mem_compl, Finset.mem_powerset, Finset.subset_iff, hT,
      Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact ⟨fun h x hx a ha => h a (ha ▸ hx), fun h a ha => h ha a rfl⟩
  simp only [Function.Involutive.coe_toPerm, hc, hmem, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hz : (∑ U ∈ Tᶜ.powerset, (-1 : ℂ) ^ U.card) = ((∑ U ∈ Tᶜ.powerset, (-1 : ℤ) ^ U.card : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hz, Finset.sum_powerset_neg_one_pow_card]
  have hs : Tᶜ = ∅ ↔ Function.Surjective f := by
    rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
    simp [hT, Function.Surjective]
  by_cases h : Function.Surjective f
  · simp [hs.2 h, h]
  · rw [if_neg (fun h' => h (hs.1 h')), if_neg h]; simp

/- English proof (translation)
Unfold `mdisc`. Use `congr 1`. Use `set G : (Fin D → Fin D) → ℂ := fun f => (Matrix.of fun i j => A (f j) i j).det with hG`. Establish `key : ∀ S : Finset (Fin D), (∑ k ∈ S, A k).det = ∑ f, (if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f`. Introduce `S`.

Rewrite using `[det_sum_eq_pi]`. Simplify using `only [ite_mul, one_mul, zero_mul, hG]`. Rewrite using `[← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]`. Repeatedly rewrite using `[key, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `h2 : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * ((if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f) = (if Function.Surjective f then 1 else 0) * G f`. Introduce `f`. Rewrite using `[← sum_sign_indicator f, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun S _ => by ring`. Repeatedly rewrite using `[h2, ite_mul, one_mul, zero_mul]`.

Rewrite using `[← Finset.sum_filter]`. Use `symm`. Use `Finset.sum_bij (fun σ _ => ⇑σ) (fun σ _ => by simpa using σ.surjective) (fun a _ b _ h => Equiv.ext (congrFun h)) (fun f hf => ?_) (fun σ _ => rfl)` and prove the remaining obligations. Establish `hs : Function.Surjective f` using `by simpa using hf`. Conclude with `⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hs, hs⟩, Finset.mem_univ _, rfl⟩`.
-/
theorem mdisc_eq_sum_perm (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ σ : Equiv.Perm (Fin D), (Matrix.of fun i j => A (σ j) i j).det := by
  classical
  unfold mdisc
  congr 1
  set G : (Fin D → Fin D) → ℂ := fun f => (Matrix.of fun i j => A (f j) i j).det with hG
  have key : ∀ S : Finset (Fin D), (∑ k ∈ S, A k).det =
      ∑ f, (if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f := by
    intro S
    rw [det_sum_eq_pi]
    simp only [ite_mul, one_mul, zero_mul, hG]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) *
      ((if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f) =
      (if Function.Surjective f then 1 else 0) * G f := by
    intro f
    rw [← sum_sign_indicator f, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  simp_rw [h2, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) (fun σ _ => by simpa using σ.surjective)
    (fun a _ b _ h => Equiv.ext (congrFun h)) (fun f hf => ?_) (fun σ _ => rfl)
  have hs : Function.Surjective f := by simpa using hf
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hs, hs⟩, Finset.mem_univ _, rfl⟩

/- English proof (translation)
Rewrite using `[mdisc_eq_sum_perm, mdisc_eq_sum_perm]`. Use `congr 1`. Conclude with `Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => (Matrix.of fun i j => A (τ j) i j).det)`.
-/
theorem mdisc_comp_perm (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (A ∘ σ) = mdisc A := by
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => (Matrix.of fun i j => A (τ j) i j).det)

private noncomputable def colMap (j : Fin D) : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) where
  toFun X := fun i => X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def mdiscML :
    MultilinearMap ℂ (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ :=
  ∑ σ : Equiv.Perm (Fin D), (1 / (D.factorial : ℂ)) •
    ((Matrix.detRowAlternating (R := ℂ) (n := Fin D)).toMultilinearMap.compLinearMap
      colMap).domDomCongr σ

/- English proof (translation)
Rewrite using `[mdisc_eq_sum_perm, mdiscML, _root_.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[_root_.smul_apply, smul_eq_mul, MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply]`. Use `congr 1`. Rewrite using `[← Matrix.det_transpose]`.

Both sides reduce to the same expression.
-/
private lemma mdiscML_apply (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : mdiscML A = mdisc A := by
  rw [mdisc_eq_sum_perm, mdiscML, _root_.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  rw [← Matrix.det_transpose]
  rfl

/- English proof (translation)
Simplify using `only [← mdiscML_apply]`. Conclude with `mdiscML.map_update_add A k B C`.
-/
theorem mdisc_update_add (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A k (B + C)) =
      mdisc (Function.update A k B) + mdisc (Function.update A k C) := by
  simp only [← mdiscML_apply]
  exact mdiscML.map_update_add A k B C

/- English proof (translation)
Simplify using `only [← mdiscML_apply]`. Conclude with `mdiscML.map_update_smul A k c B`.
-/
theorem mdisc_update_smul (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D) (c : ℂ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A k (c • B)) = c * mdisc (Function.update A k B) := by
  simp only [← mdiscML_apply]
  exact mdiscML.map_update_smul A k c B

/- English proof (translation)
Conclude with `⟨mdiscML, funext mdiscML_apply⟩`.
-/
theorem exists_multilinearMap_eq_mdisc :
    ∃ M : MultilinearMap ℂ (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ, ⇑M = mdisc := by
  exact ⟨mdiscML, funext mdiscML_apply⟩

/- English proof (translation)
Rewrite using `[mdisc_eq_sum_perm]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`. Establish `: (D.factorial : ℂ) ≠ 0` using `by exact_mod_cast D.factorial_ne_zero`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem mdisc_const (A : Matrix (Fin D) (Fin D) ℂ) : mdisc (fun _ => A) = A.det := by
  rw [mdisc_eq_sum_perm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp
  rfl

/- English proof (translation)
Rewrite using `[← mdisc_const, ← mdiscML_apply, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Use `MultilinearMap.map_smul_univ (mdiscML (D := D)) (fun i => c (f i)) (fun i => A (f i))` as an intermediate fact. Rewrite using `[this, smul_eq_mul, mdiscML_apply]`. Both sides reduce to the same expression.
-/
theorem det_sum_smul_eq_sum_mdisc {m : ℕ} (c : Fin m → ℂ)
    (A : Fin m → Matrix (Fin D) (Fin D) ℂ) :
    (∑ j, c j • A j).det = ∑ f : Fin D → Fin m, (∏ k, c (f k)) * mdisc (A ∘ f) := by
  rw [← mdisc_const, ← mdiscML_apply, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have := MultilinearMap.map_smul_univ (mdiscML (D := D)) (fun i => c (f i)) (fun i => A (f i))
  rw [this, smul_eq_mul, mdiscML_apply]
  rfl

/- English proof (translation)
Establish `h1 : Fintype.card {k : Fin D // (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∈ T}`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt, Finset.filter_mem_eq_inter, Finset.univ_inter]`. Conclude with `min_eq_right (by simpa using T.card_le_univ)`. Establish `h2 : Fintype.card {k : Fin D // ¬ (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∉ T}`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]`.

Use `⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < T.card`. Establish `e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inl ⟨k, hk⟩` using `Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin D => (x : ℕ) < T.card) hk`. Simplify using `only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`. Conclude with `iff_of_true (Fintype.equivOfCardEq h1 ⟨k, hk⟩).2 hk`.

Establish `e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inr ⟨k, hk⟩` using `Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin D => (x : ℕ) < T.card) hk`. Simplify using `only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]`. Conclude with `iff_of_false (Fintype.equivOfCardEq h2 ⟨k, hk⟩).2 hk`.
-/
private lemma exists_perm_mem_iff (T : Finset (Fin D)) :
    ∃ σ : Equiv.Perm (Fin D), ∀ k, σ k ∈ T ↔ (k : ℕ) < T.card := by
  classical
  have h1 : Fintype.card {k : Fin D // (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∈ T} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact min_eq_right (by simpa using T.card_le_univ)
  have h2 : Fintype.card {k : Fin D // ¬ (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∉ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun k => ?_⟩
  by_cases hk : (k : ℕ) < T.card
  · have e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inl ⟨k, hk⟩ :=
      Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin D => (x : ℕ) < T.card) hk
    simp only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    exact iff_of_true (Fintype.equivOfCardEq h1 ⟨k, hk⟩).2 hk
  · have e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inr ⟨k, hk⟩ :=
      Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin D => (x : ℕ) < T.card) hk
    simp only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    exact iff_of_false (Fintype.equivOfCardEq h2 ⟨k, hk⟩).2 hk

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_perm_mem_iff T`. Rewrite using `[← mdisc_comp_perm _ σ]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, hσ]`.
-/
private lemma mdisc_piecewise (T : Finset (Fin D)) (A B : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => if k ∈ T then A else B) = mdisc (fun k : Fin D => if (k : ℕ) < T.card then A else B) := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff T
  rw [← mdisc_comp_perm _ σ]
  congr 1
  funext k
  simp only [Function.comp_apply, hσ]

/- English proof (translation)
Rewrite using `[← mdisc_const, ← mdiscML_apply]`. Establish `h : (fun _ : Fin D => s • A + t • B) = (fun _ : Fin D => s • A) + (fun _ => t • B)` using `rfl`. Rewrite using `[h, MultilinearMap.map_add_univ]`. Establish `h2 : ∀ T : Finset (Fin D), mdiscML (T.piecewise (fun _ => s • A) (fun _ => t • B)) = s ^ T.card * t ^ (D - T.card) * mdisc (fun k : Fin D => if (k : ℕ) < T.card then A else B)`. Introduce `T`.

Establish `e : T.piecewise (fun _ : Fin D => s • A) (fun _ => t • B) = fun k => (if k ∈ T then s else t) • (if k ∈ T then A else B)`. Apply the tactic sequence `funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]`. Rewrite using `[e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, mdisc_piecewise, Finset.prod_ite, Finset.prod_const, Finset.prod_const]`. Use `congr 2`. Simplify using the standard rewrite rules.

Use `congr 1`. Rewrite using `[Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]`. Simplify using the standard rewrite rules. Simplify using `only [h2]`. Rewrite using `[← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun i => s ^ i * t ^ (D - i) * mdisc (fun k : Fin D => if (k : ℕ) < i then A else B)) (x := Finset.univ)]`.

Simplify using `only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]`.
-/
theorem det_smul_add_smul_eq_sum_mdisc (s t : ℂ) (A B : Matrix (Fin D) (Fin D) ℂ) :
    (s • A + t • B).det =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℂ) * s ^ i * t ^ (D - i) *
        mdisc (fun k : Fin D => if (k : ℕ) < i then A else B) := by
  classical
  rw [← mdisc_const, ← mdiscML_apply]
  have h : (fun _ : Fin D => s • A + t • B) = (fun _ : Fin D => s • A) + (fun _ => t • B) := rfl
  rw [h, MultilinearMap.map_add_univ]
  have h2 : ∀ T : Finset (Fin D), mdiscML (T.piecewise (fun _ => s • A) (fun _ => t • B)) =
      s ^ T.card * t ^ (D - T.card) * mdisc (fun k : Fin D => if (k : ℕ) < T.card then A else B) := by
    intro T
    have e : T.piecewise (fun _ : Fin D => s • A) (fun _ => t • B) =
        fun k => (if k ∈ T then s else t) • (if k ∈ T then A else B) := by
      funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, mdisc_piecewise,
      Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · simp
    · congr 1
      rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
        Finset.card_univ, Fintype.card_fin]
      simp
  simp only [h2]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun i => s ^ i * t ^ (D - i) *
      mdisc (fun k : Fin D => if (k : ℕ) < i then A else B)) (x := Finset.univ)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/- English proof (translation)
Simplify using `only [mdisc, star_mul', star_sum, ← Matrix.conjTranspose_sum, Matrix.det_conjTranspose, star_pow, star_neg, star_one, star_div₀, star_natCast]`.
-/
theorem star_mdisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    star (mdisc A) = mdisc (fun k => (A k)ᴴ) := by
  simp only [mdisc, star_mul', star_sum, ← Matrix.conjTranspose_sum, Matrix.det_conjTranspose,
    star_pow, star_neg, star_one, star_div₀, star_natCast]

/- English proof (translation)
Establish `h` using `star_mdisc A`. Establish `e : (fun k => (A k)ᴴ) = A` using `funext fun k => (hA k).eq`. Rewrite `h` using `[e]`. Conclude with `Complex.conj_eq_iff_im.1 h`.
-/
theorem mdisc_im_eq_zero_of_isHermitian (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).IsHermitian) : (mdisc A).im = 0 := by
  have h := star_mdisc A
  have e : (fun k => (A k)ᴴ) = A := funext fun k => (hA k).eq
  rw [e] at h
  exact Complex.conj_eq_iff_im.1 h

/- English proof (translation)
Conclude with `mixedDiscriminant_nonneg_of_gram A hA`.
-/
theorem mdisc_nonneg_of_posSemidef (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by
  exact mixedDiscriminant_nonneg_of_gram A hA

/- English proof (translation)
Conclude with `mixedDiscriminant_pos_of_gram A hA`.
-/
theorem mdisc_pos_of_posDef (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosDef) : (mdisc A).im = 0 ∧ 0 < (mdisc A).re := by
  exact mixedDiscriminant_pos_of_gram A hA

/- English proof (translation)
Conclude with `mixedDiscriminant_re_mono_of_gram A B hA hAB`.
-/
theorem mdisc_re_mono (A B : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ k, (A k).PosSemidef)
    (hAB : ∀ k, (B k - A k).PosSemidef) : (mdisc A).re ≤ (mdisc B).re := by
  exact mixedDiscriminant_re_mono_of_gram A B hA hAB

/- English proof (translation)
Unfold `mdisc`. Establish `h : ∀ S : Finset (Fin D), (∑ k ∈ S, B * A k * C).det = B.det * C.det * (∑ k ∈ S, A k).det`. Introduce `S`. Rewrite using `[← Finset.sum_mul, ← Finset.mul_sum, Matrix.det_mul, Matrix.det_mul]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun S _ => by ring`.
-/
theorem mdisc_mul_mul (B C : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => B * A k * C) = B.det * C.det * mdisc A := by
  unfold mdisc
  have h : ∀ S : Finset (Fin D),
      (∑ k ∈ S, B * A k * C).det = B.det * C.det * (∑ k ∈ S, A k).det := by
    intro S
    rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.det_mul, Matrix.det_mul]
    ring
  simp_rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/- English proof (translation)
Rewrite using `[mdisc_mul_mul, Matrix.det_conjTranspose]`. Use `congr 1`. Rewrite using `[mul_comm]`. Conclude with `Complex.mul_conj _`.
-/
theorem mdisc_conjTranspose_mul_mul (P : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => Pᴴ * A k * P) = (Complex.normSq P.det : ℂ) * mdisc A := by
  rw [mdisc_mul_mul, Matrix.det_conjTranspose]
  congr 1
  rw [mul_comm]
  exact Complex.mul_conj _

/- English proof (translation)
Rewrite using `[mdisc_mul_mul, Matrix.det_transpose, show (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det from (RingHom.map_det _ _).symm]`. Use `congr 1`. Conclude with `Complex.mul_conj _`.
-/
theorem mdisc_transpose_mul_mul_conj (J : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = (Complex.normSq J.det : ℂ) * mdisc A := by
  rw [mdisc_mul_mul, Matrix.det_transpose,
    show (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det from (RingHom.map_det _ _).symm]
  congr 1
  exact Complex.mul_conj _

/- English proof (translation)
Establish `hc : J.map (starRingEnd ℂ) *ᵥ star w = star (J *ᵥ w)`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum]`. Establish `hv : ∀ k, (Jᵀ * A k * J.map (starRingEnd ℂ)) *ᵥ star w = 0`. Introduce `k`.

Rewrite using `[← Matrix.mulVec_mulVec, hc, hJw, star_zero, Matrix.mulVec_zero]`. Establish `hw' : star w ≠ 0` using `by simpa using hw`. Establish `h0 : ∀ S : Finset (Fin D), (∑ k ∈ S, Jᵀ * A k * J.map (starRingEnd ℂ)).det = 0`. Introduce `S`. Conclude with `Matrix.exists_mulVec_eq_zero_iff.1 ⟨star w, hw', by rw [Matrix.sum_mulVec]; exact Finset.sum_eq_zero fun k _ => hv k⟩`.

Simplify using `[mdisc, h0]`.
-/
theorem mdisc_transpose_mul_mul_conj_eq_zero {E : ℕ} (J : Matrix (Fin E) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin E) (Fin E) ℂ) (w : Fin D → ℂ) (hw : w ≠ 0) (hJw : J *ᵥ w = 0) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = 0 := by
  classical
  have hc : J.map (starRingEnd ℂ) *ᵥ star w = star (J *ᵥ w) := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum]
  have hv : ∀ k, (Jᵀ * A k * J.map (starRingEnd ℂ)) *ᵥ star w = 0 := by
    intro k
    rw [← Matrix.mulVec_mulVec, hc, hJw, star_zero, Matrix.mulVec_zero]
  have hw' : star w ≠ 0 := by simpa using hw
  have h0 : ∀ S : Finset (Fin D), (∑ k ∈ S, Jᵀ * A k * J.map (starRingEnd ℂ)).det = 0 := by
    intro S
    exact Matrix.exists_mulVec_eq_zero_iff.1
      ⟨star w, hw', by rw [Matrix.sum_mulVec]; exact Finset.sum_eq_zero fun k _ => hv k⟩
  simp [mdisc, h0]

/- English proof (translation)
Establish `h3 : ((B - A) + (A + B)).PosSemidef` using `h1.add h2`. Establish `h4 : (B - A) + (A + B) = (2 : ℂ) • B` using `by rw [two_smul]; abel`. Rewrite `h3` using `[h4]`. Establish `h5` using `h3.smul (a := ((1 / 2 : ℝ) : ℂ)) (Complex.zero_le_real.2 (by norm_num))`. Establish `h6 : ((1 / 2 : ℝ) : ℂ) • ((2 : ℂ) • B) = B`.

Rewrite using `[smul_smul]`. Evaluate the numerical expressions. Rewrite `h5` using `[h6]`. Then use the resulting hypothesis.
-/
private lemma posSemidef_of_sub_of_add {A B : Matrix (Fin D) (Fin D) ℂ} (h1 : (B - A).PosSemidef)
    (h2 : (A + B).PosSemidef) : B.PosSemidef := by
  have h3 : ((B - A) + (A + B)).PosSemidef := h1.add h2
  have h4 : (B - A) + (A + B) = (2 : ℂ) • B := by rw [two_smul]; abel
  rw [h4] at h3
  have h5 := h3.smul (a := ((1 / 2 : ℝ) : ℂ)) (Complex.zero_le_real.2 (by norm_num))
  have h6 : ((1 / 2 : ℝ) : ℂ) • ((2 : ℂ) • B) = B := by
    rw [smul_smul]; norm_num
  rwa [h6] at h5

/- English proof (translation)
Establish `hB : ∀ k, (B k).PosSemidef` using `fun k => posSemidef_of_sub_of_add (hle k) (hge k)`. Establish `hA : A = (fun k => A k + B k) + (fun k => (-1 : ℂ) • B k)`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `hexp : mdisc A = ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B)` using `by conv_lhs => rw [← mdiscML_apply, hA]`.

Rewrite using `[MultilinearMap.map_add_univ]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Establish `e : T.piecewise (fun k => A k + B k) (fun k => (-1 : ℂ) • B k) = fun k => (if k ∈ T then (1 : ℂ) else -1) • T.piecewise (fun k => A k + B k) B k`. Apply the tactic sequence `funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]`. Rewrite using `[e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, one_mul]`.

Use `congr 2`. Rewrite using `[Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]`. Simplify using the standard rewrite rules. Establish `hterm : ∀ T : Finset (Fin D), ‖mdisc (T.piecewise (fun k => A k + B k) B)‖ ≤ 2 ^ T.card * (mdisc B).re`. Introduce `T`.

Establish `hP : ∀ k, (T.piecewise (fun k => A k + B k) B k).PosSemidef` using `fun k => by`. Apply the tactic sequence `by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk, hge k, hB k]`. Take `⟨him, hre⟩` from `mixedDiscriminant_nonneg_of_gram _ hP`. Establish `hmono` using `mixedDiscriminant_re_mono_of_gram (T.piecewise (fun k => A k + B k) B) (T.piecewise (fun k => (2 : ℂ) • B k) B) hP (fun k => by`. Distinguish the cases in `hk : k ∈ T`.

Establish `e : (2 : ℂ) • B k - (A k + B k) = B k - A k` using `by rw [two_smul]; abel`. Simplify `hle k` using `[Finset.piecewise, hk, e]`. Simplify `Matrix.PosSemidef.zero)` using `[Finset.piecewise, hk]`. Establish `h2 : mdisc (T.piecewise (fun k => (2 : ℂ) • B k) B) = (((2 : ℝ) ^ T.card : ℝ) : ℂ) * mdisc B`. Rewrite using `[← mdiscML_apply, ← mdiscML_apply]`.

Establish `e : T.piecewise (fun k => (2 : ℂ) • B k) B = fun k => (if k ∈ T then (2 : ℂ) else 1) • B k`. Apply the tactic sequence `funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]`. Rewrite using `[e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]`. Simplify using the standard rewrite rules. Establish `hz : mdisc (T.piecewise (fun k => A k + B k) B) = ((mdisc (T.piecewise (fun k => A k + B k) B)).re : ℂ)`.

Apply the tactic sequence `apply Complex.ext <;> simp [him]`. Rewrite using `[hz, Complex.norm_of_nonneg hre]`. Rewrite `hmono` using `[h2, Complex.re_ofReal_mul]`. Conclude with `hmono`. Rewrite using `[hexp]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Conclude with `hterm T`. Use `_ = 3 ^ D * (mdisc B).re := by`. Rewrite using `[← Finset.sum_mul]`.

Use `congr 1`. Use `Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 (Finset.univ : Finset (Fin D))` as an intermediate fact. Simplify using `only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin, Finset.powerset_univ] at this`. Rewrite using `[this]`. Evaluate the numerical expressions.
-/
theorem norm_mdisc_le_of_abs_le (A B : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hle : ∀ k, (B k - A k).PosSemidef) (hge : ∀ k, (A k + B k).PosSemidef) :
    ‖mdisc A‖ ≤ (3 : ℝ) ^ D * (mdisc B).re := by
  classical
  have hB : ∀ k, (B k).PosSemidef := fun k => posSemidef_of_sub_of_add (hle k) (hge k)
  have hA : A = (fun k => A k + B k) + (fun k => (-1 : ℂ) • B k) := by
    funext k; simp
  have hexp : mdisc A = ∑ T : Finset (Fin D),
      (-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B) := by
    conv_lhs => rw [← mdiscML_apply, hA]
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    have e : T.piecewise (fun k => A k + B k) (fun k => (-1 : ℂ) • B k) =
        fun k => (if k ∈ T then (1 : ℂ) else -1) • T.piecewise (fun k => A k + B k) B k := by
      funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const, one_pow, one_mul]
    congr 2
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
      Finset.card_univ, Fintype.card_fin]
    simp
  have hterm : ∀ T : Finset (Fin D),
      ‖mdisc (T.piecewise (fun k => A k + B k) B)‖ ≤ 2 ^ T.card * (mdisc B).re := by
    intro T
    have hP : ∀ k, (T.piecewise (fun k => A k + B k) B k).PosSemidef := fun k => by
      by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk, hge k, hB k]
    obtain ⟨him, hre⟩ := mixedDiscriminant_nonneg_of_gram _ hP
    have hmono := mixedDiscriminant_re_mono_of_gram (T.piecewise (fun k => A k + B k) B)
      (T.piecewise (fun k => (2 : ℂ) • B k) B) hP (fun k => by
        by_cases hk : k ∈ T
        · have e : (2 : ℂ) • B k - (A k + B k) = B k - A k := by rw [two_smul]; abel
          simpa [Finset.piecewise, hk, e] using hle k
        · simpa [Finset.piecewise, hk] using Matrix.PosSemidef.zero)
    have h2 : mdisc (T.piecewise (fun k => (2 : ℂ) • B k) B) =
        (((2 : ℝ) ^ T.card : ℝ) : ℂ) * mdisc B := by
      rw [← mdiscML_apply, ← mdiscML_apply]
      have e : T.piecewise (fun k => (2 : ℂ) • B k) B =
          fun k => (if k ∈ T then (2 : ℂ) else 1) • B k := by
        funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
      rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const, one_pow, mul_one]
      simp
    have hz : mdisc (T.piecewise (fun k => A k + B k) B) =
        ((mdisc (T.piecewise (fun k => A k + B k) B)).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hz, Complex.norm_of_nonneg hre]
    rw [h2, Complex.re_ofReal_mul] at hmono
    exact hmono
  rw [hexp]
  calc ‖∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B)‖
      ≤ ∑ T : Finset (Fin D),
          ‖(-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ T : Finset (Fin D), 2 ^ T.card * (mdisc B).re :=
        Finset.sum_le_sum fun T _ => by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hterm T
    _ = 3 ^ D * (mdisc B).re := by
        rw [← Finset.sum_mul]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 (Finset.univ : Finset (Fin D))
        simp only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin,
          Finset.powerset_univ] at this
        rw [this]
        norm_num

/- English proof (translation)
Use `set A : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Fin.cons (Matrix.single 0 0 1) B with hA`. Rewrite using `[mdisc_eq_sum_perm, mdisc_eq_sum_perm, ← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := n)).symm, Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin (n + 1))]`. Establish `hterm : ∀ τ : Equiv.Perm (Fin n), (Matrix.of fun i j => A (Equiv.Perm.decomposeFin.symm (0, τ) j) i j).det = (Matrix.of fun i j => (B (τ j)).submatrix Fin.succ Fin.succ i j).det`. Introduce `τ`. Rewrite using `[Matrix.det_succ_column_zero, Finset.sum_eq_single 0]`.

Simplify using `only [Matrix.of_apply, Equiv.Perm.decomposeFin_symm_apply_zero, hA, Fin.cons_zero, Matrix.single_apply, and_self, if_true, Fin.val_zero, pow_zero, one_mul]`. Use `congr 1`. Introduce `b _ hb`. Simplify using `[hA, Equiv.Perm.decomposeFin_symm_apply_zero, Ne.symm hb]`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[hterm]`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]`. Establish `h1 : (n.factorial : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Establish `h2 : (n : ℂ) + 1 ≠ 0` using `by exact_mod_cast n.succ_ne_zero`. Clear the denominators using the available nonvanishing facts.

Introduce `p _ hp`. Use `Finset.sum_eq_zero fun τ _ => ?_` and prove the remaining obligations. Use `set σ := Equiv.Perm.decomposeFin.symm (p, τ) with hσ`. Establish `hσ0 : σ 0 = p` using `Equiv.Perm.decomposeFin_symm_apply_zero p τ`. Establish `hj : σ.symm 0 ≠ 0`.

Introduce `h`. Apply `hp` to reduce the goal to its premises. Use `σ.apply_symm_apply 0` as an intermediate fact. Rewrite `this` using `[h, hσ0]`. Conclude with `this`.

Apply `Matrix.det_eq_zero_of_column_eq_zero (σ.symm 0)` to reduce the goal to its premises. Introduce `i`. Simplify using `[hA, Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
theorem mdisc_cons_single_zero {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (Matrix.single 0 0 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix Fin.succ Fin.succ) := by
  set A : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Fin.cons (Matrix.single 0 0 1) B with hA
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm,
    ← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := n)).symm, Fintype.sum_prod_type,
    Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hterm : ∀ τ : Equiv.Perm (Fin n),
        (Matrix.of fun i j => A (Equiv.Perm.decomposeFin.symm (0, τ) j) i j).det =
          (Matrix.of fun i j => (B (τ j)).submatrix Fin.succ Fin.succ i j).det := by
      intro τ
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · simp only [Matrix.of_apply, Equiv.Perm.decomposeFin_symm_apply_zero, hA, Fin.cons_zero,
          Matrix.single_apply, and_self, if_true, Fin.val_zero, pow_zero, one_mul]
        congr 1
      · intro b _ hb
        simp [hA, Equiv.Perm.decomposeFin_symm_apply_zero, Ne.symm hb]
      · simp
    simp_rw [hterm]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
  · intro p _ hp
    refine Finset.sum_eq_zero fun τ _ => ?_
    set σ := Equiv.Perm.decomposeFin.symm (p, τ) with hσ
    have hσ0 : σ 0 = p := Equiv.Perm.decomposeFin_symm_apply_zero p τ
    have hj : σ.symm 0 ≠ 0 := by
      intro h
      apply hp
      have := σ.apply_symm_apply 0
      rw [h, hσ0] at this
      exact this
    apply Matrix.det_eq_zero_of_column_eq_zero (σ.symm 0)
    intro i
    simp [hA, Ne.symm hj]
  · simp

/- English proof (translation)
Unfold `maDens`. Conclude with `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _)) (mixedDiscriminant_nonneg_of_gram _ hφ).2`.
-/
theorem maDens_nonneg_of_posSemidef (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hφ : ∀ k, (hessC (φ k) z).PosSemidef) : 0 ≤ maDens φ z := by
  unfold maDens
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _))
    (mixedDiscriminant_nonneg_of_gram _ hφ).2

end ReciprocityTheory.AnForm.A
