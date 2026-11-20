import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

namespace GlobalTheory.LFun.ExSatGL

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Polynomial

/- English proof (translation)
Use `set c : Fin n → ℂ := fun i => (-1) ^ (n - (i : ℕ)) * a (n - (i : ℕ)) with hc`. Use `set q : Polynomial ℂ := ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) with hq`. Use `set p : Polynomial ℂ := Polynomial.X ^ n + q with hp`. Establish `hdeg : q.degree < n` using `Polynomial.degree_sum_fin_lt c`. Establish `hmon : p.Monic` using `Polynomial.monic_X_pow_add hdeg`.

Establish `hnat : p.natDegree = n`. Rewrite using `[hp, Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.natDegree_X_pow]`. Establish `hqc : ∀ k (hk : k < n), q.coeff k = c ⟨k, hk⟩`. Introduce `k hk`. Rewrite using `[hq, Polynomial.finset_sum_coeff, Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]`.

Rewrite using `[Polynomial.coeff_C_mul_X_pow, if_pos rfl]`. Introduce `i _ hi`. Rewrite using `[Polynomial.coeff_C_mul_X_pow, if_neg]`. Introduce `h`. Conclude with `hi (Fin.ext h.symm)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hpc : ∀ k (hk : k < n), p.coeff k = c ⟨k, hk⟩`. Introduce `k hk`. Rewrite using `[hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hk.ne, zero_add, hqc k hk]`.

Establish `hroots : Multiset.card p.roots = p.natDegree` using `by first`. Consider the case `exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)`. Consider the case `exact (IsAlgClosed.splits p).card_roots`. Consider the case `exact Polynomial.Splits.card_roots (IsAlgClosed.splits p)`. Establish `h0c : p.coeff 0 ≠ 0`.

Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `[hp, hq]`. Rewrite using `[hpc 0 h]`. Simplify using `only [hc, Fin.val_mk, Nat.sub_zero]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hn`. Establish `hne : ∀ r ∈ p.roots, r ≠ 0`. Introduce `r hr h0`. Substitute `h0` using the available equality. Use `(Polynomial.mem_roots hmon.ne_zero).mp hr` as an intermediate fact.

Rewrite `this` using `[Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero]`. Conclude with `h0c this`. Use `⟨p.roots.attach.map fun r => Units.mk0 r.1 (hne r.1 r.2), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.card_map, Multiset.card_attach, hroots, hnat]`. Establish `hB : ((p.roots.attach.map fun r => Units.mk0 r.1 (hne r.1 r.2)).map fun b : ℂˣ => (b : ℂ)) = p.roots`.

Rewrite using `[Multiset.map_map]`. Conclude with `Multiset.attach_map_val' _ _ |>.trans (Multiset.map_id' _)`. Introduce `j hj`. Rewrite using `[hB]`. Establish `hv` using `Polynomial.coeff_eq_esymm_roots_of_card hroots (k := n - j) (by rw [hnat]; exact Nat.sub_le n j)`.

Rewrite `hv` using `[hmon.leadingCoeff, hnat, Nat.sub_sub_self hj, one_mul]`. Break down `Nat.eq_zero_or_pos j with hj0 | hj0` into its components or cases. Substitute `hj0` using the available equality. Rewrite using `[Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.sum_singleton, Multiset.prod_zero, h0]`. Establish `hlt : n - j < n` using `Nat.sub_lt (lt_of_lt_of_le hj0 hj) hj0`.

Rewrite `hv` using `[hpc _ hlt]`. Simplify using `only [hc, Fin.val_mk, Nat.sub_sub_self hj] at hv`. Establish `hu : ((-1 : ℂ) ^ j) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Conclude with `(mul_left_cancel₀ hu hv).symm`.
-/
theorem exists_esymm_eq (n : ℕ) (a : ℕ → ℂ) (h0 : a 0 = 1) (hn : a n ≠ 0) :
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, (B.map fun b : ℂˣ => (b : ℂ)).esymm j = a j := by
  classical
  set c : Fin n → ℂ := fun i => (-1) ^ (n - (i : ℕ)) * a (n - (i : ℕ)) with hc
  set q : Polynomial ℂ := ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) with hq
  set p : Polynomial ℂ := Polynomial.X ^ n + q with hp
  have hdeg : q.degree < n := Polynomial.degree_sum_fin_lt c
  have hmon : p.Monic := Polynomial.monic_X_pow_add hdeg
  have hnat : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  have hqc : ∀ k (hk : k < n), q.coeff k = c ⟨k, hk⟩ := by
    intro k hk
    rw [hq, Polynomial.finset_sum_coeff, Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hi
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h; exact hi (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hpc : ∀ k (hk : k < n), p.coeff k = c ⟨k, hk⟩ := by
    intro k hk
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hk.ne, zero_add, hqc k hk]
  have hroots : Multiset.card p.roots = p.natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
    | exact (IsAlgClosed.splits p).card_roots
    | exact Polynomial.Splits.card_roots (IsAlgClosed.splits p)
  have h0c : p.coeff 0 ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [hp, hq]
    · rw [hpc 0 h]
      simp only [hc, Fin.val_mk, Nat.sub_zero]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hn
  have hne : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr h0
    subst h0
    have := (Polynomial.mem_roots hmon.ne_zero).mp hr
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero] at this
    exact h0c this
  refine ⟨p.roots.attach.map fun r => Units.mk0 r.1 (hne r.1 r.2), ?_, ?_⟩
  · rw [Multiset.card_map, Multiset.card_attach, hroots, hnat]
  · have hB : ((p.roots.attach.map fun r => Units.mk0 r.1 (hne r.1 r.2)).map fun b : ℂˣ => (b : ℂ)) = p.roots := by
      rw [Multiset.map_map]
      exact Multiset.attach_map_val' _ _ |>.trans (Multiset.map_id' _)
    intro j hj
    rw [hB]
    have hv := Polynomial.coeff_eq_esymm_roots_of_card hroots (k := n - j) (by rw [hnat]; exact Nat.sub_le n j)
    rw [hmon.leadingCoeff, hnat, Nat.sub_sub_self hj, one_mul] at hv
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.sum_singleton,
        Multiset.prod_zero, h0]
    · have hlt : n - j < n := Nat.sub_lt (lt_of_lt_of_le hj0 hj) hj0
      rw [hpc _ hlt] at hv
      simp only [hc, Fin.val_mk, Nat.sub_sub_self hj] at hv
      have hu : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_left_cancel₀ hu hv).symm

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Unfold `IsUnifV at h h'`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe h`.

Use `set u : w.adicCompletion E := ϖ' * ϖ⁻¹ with hu`. Establish `hvu : Valued.v u = 1`. Rewrite using `[hu, map_mul, map_inv₀, h, h', mul_inv_cancel₀ (by simp)]`. Establish `hvu' : Valued.v u⁻¹ = 1` using `by rw [map_inv₀, hvu, inv_one]`. Establish `huO : u ∈ Ov E w` using `by show u ∈ w.adicCompletionIntegers E`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvu]`. Establish `huO' : u⁻¹ ∈ Ov E w` using `by show u⁻¹ ∈ w.adicCompletionIntegers E`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvu']`. Establish `hu0 : u ≠ 0` using `by intro h0; rw [h0, map_zero] at hvu; exact zero_ne_one hvu`. Establish `hϖ' : ϖ' = ϖ * u` using `by rw [hu, mul_comm ϖ' _, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]`.

Set `dO : Matrix (Fin n) (Fin n) (Ov E w)` to `Matrix.diagonal fun i => if (i : ℕ) < j then ⟨u, huO⟩ else 1`. Set `dO' : Matrix (Fin n) (Fin n) (Ov E w)` to `Matrix.diagonal fun i => if (i : ℕ) < j then ⟨u⁻¹, huO'⟩ else 1`. Establish `hdd : dO * dO' = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `split_ifs`. Conclude with `Subtype.ext (by simp [mul_inv_cancel₀ hu0])`. Simplify using the standard rewrite rules. Establish `hdd' : dO' * dO = 1`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `split_ifs`. Conclude with `Subtype.ext (by simp [inv_mul_cancel₀ hu0])`.

Simplify using the standard rewrite rules. Set `D : GL (Fin n) (Ov E w)` to `⟨dO, dO', hdd, hdd'⟩`. Use `set Dk : GL (Fin n) (w.adicCompletion E) := bc (Ov E w).subtype D with hDkdef`. Establish `hDk : Dk ∈ GLint (Fin n) (Ov E w)`. Unfold `GLint`.

Conclude with `⟨D, rfl⟩`. Establish `hDval : (Dk : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < j then u else 1`. Rewrite using `[hDkdef]`. Use extensionality with `a b`. Use `first`.

Consider the case `(simp [bc, D, dO, Matrix.diagonal_apply]; done)`. Consider the case `(simp [bc, D, dO, Matrix.diagonal_apply]; split_ifs <;> simp)`. Consider the case `(unfold bc; simp [D, dO, Matrix.diagonal_apply]; split_ifs <;> simp)`. Consider the case `(simp [bc, D, dO, Matrix.diagonal_apply, Matrix.map_apply, RingHom.mapMatrix_apply]; split_ifs <;> simp)`. Establish `hdiag : diagJ n ϖ' j = diagJ n ϖ j * (Dk : Matrix (Fin n) (Fin n) (w.adicCompletion E))`.

Rewrite using `[hDval]`. Unfold `diagJ`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `split_ifs <;> simp [hϖ']`. Establish `hdiag' : diagJ n ϖ j = diagJ n ϖ' j * ((Dk⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) _)`. Rewrite using `[hdiag, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Unfold `Tj`. Use `congr 1`.

Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Use `⟨a, ha, Dk * b, mul_mem hDk hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[hab, hdiag, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Use `⟨a, ha, Dk⁻¹ * b, mul_mem (inv_mem hDk) hb, ?_⟩` and prove the remaining obligations. Rewrite using `[hab, hdiag', Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`.
-/
theorem Tj_indep (j : ℕ) {ϖ ϖ' : w.adicCompletion E} (h : IsUnifV E w ϖ) (h' : IsUnifV E w ϖ') :
    Tj ℂ n (Ov E w) ϖ' j = Tj ℂ n (Ov E w) ϖ j := by
  classical
  unfold IsUnifV at h h'
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at h; exact WithZero.zero_ne_coe h
  set u : w.adicCompletion E := ϖ' * ϖ⁻¹ with hu
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_inv₀, h, h', mul_inv_cancel₀ (by simp)]
  have hvu' : Valued.v u⁻¹ = 1 := by rw [map_inv₀, hvu, inv_one]
  have huO : u ∈ Ov E w := by
    show u ∈ w.adicCompletionIntegers E
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvu]
  have huO' : u⁻¹ ∈ Ov E w := by
    show u⁻¹ ∈ w.adicCompletionIntegers E
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvu']
  have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hvu; exact zero_ne_one hvu
  have hϖ' : ϖ' = ϖ * u := by rw [hu, mul_comm ϖ' _, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

  let dO : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.diagonal fun i => if (i : ℕ) < j then ⟨u, huO⟩ else 1
  let dO' : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.diagonal fun i => if (i : ℕ) < j then ⟨u⁻¹, huO'⟩ else 1
  have hdd : dO * dO' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    split_ifs
    · exact Subtype.ext (by simp [mul_inv_cancel₀ hu0])
    · simp
  have hdd' : dO' * dO = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    split_ifs
    · exact Subtype.ext (by simp [inv_mul_cancel₀ hu0])
    · simp
  let D : GL (Fin n) (Ov E w) := ⟨dO, dO', hdd, hdd'⟩
  set Dk : GL (Fin n) (w.adicCompletion E) := bc (Ov E w).subtype D with hDkdef
  have hDk : Dk ∈ GLint (Fin n) (Ov E w) := by
    unfold GLint
    exact ⟨D, rfl⟩
  have hDval : (Dk : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun i : Fin n => if (i : ℕ) < j then u else 1 := by
    rw [hDkdef]
    ext a b
    first
    | (simp [bc, D, dO, Matrix.diagonal_apply]; done)
    | (simp [bc, D, dO, Matrix.diagonal_apply]; split_ifs <;> simp)
    | (unfold bc; simp [D, dO, Matrix.diagonal_apply]; split_ifs <;> simp)
    | (simp [bc, D, dO, Matrix.diagonal_apply, Matrix.map_apply, RingHom.mapMatrix_apply]; split_ifs <;> simp)
  have hdiag : diagJ n ϖ' j = diagJ n ϖ j * (Dk : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hDval]
    unfold diagJ
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    split_ifs <;> simp [hϖ']
  have hdiag' : diagJ n ϖ j = diagJ n ϖ' j * ((Dk⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) _) := by
    rw [hdiag, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  unfold Tj
  congr 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ha, Dk * b, mul_mem hDk hb, ?_⟩
    rw [hab, hdiag, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ha, Dk⁻¹ * b, mul_mem (inv_mem hDk) hb, ?_⟩
    rw [hab, hdiag', Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/- English proof (translation)
Establish `hfix : ∀ k ∈ KGL w n, ρ k x = x`. Introduce `k hk`. Establish `hx'` using `hx`. Unfold `fixed eig at hx'`. Use `hx' ⟨k, hk⟩` as an intermediate fact.

Simplify using `using this`. Establish `hd : diagJ n ϖ 0 = 1`. Unfold `diagJ`. Simplify using the standard rewrite rules. Establish `hK : ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ 0 g = if g ∈ KGL w n then 1 else 0`.

Introduce `g`. Unfold `Tj`. Rewrite using `[Set.indicator_apply]`. Distinguish the cases in `hg : g ∈ KGL w n`. Rewrite using `[if_pos hg, if_pos]`.

Both sides reduce to the same expression. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨g, hg, 1, one_mem _, by simp [hd]⟩`. Rewrite using `[if_neg hg, if_neg]`. Simplify using `only [Set.mem_setOf_eq]`.

Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Apply `hg` to reduce the goal to its premises. Establish `hg' : g = a * b` using `Units.ext (by simp [hab, hd])`. Rewrite using `[hg']`. Conclude with `mul_mem ha hb`.

Unfold `heckeVec`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk 1 : GL (Fin n) (w.adicCompletion E) ⧸ KGL w n)]`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (KGL w n) (1 : GL (Fin n) (w.adicCompletion E))`. Rewrite using `[hk, one_mul, hK, if_pos k.2, one_smul, hfix _ k.2]`. Introduce `c hc`.

Rewrite using `[hK, if_neg, zero_smul]`. Introduce `hmem`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' c]`. Conclude with `QuotientGroup.eq.mpr (by rw [mul_one]; exact inv_mem hmem)`.
-/
theorem heckeVec_Tj_zero (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E)
    {x : V} (hx : x ∈ fixed ρ (KGL w n)) : heckeVec ρ (KGL w n) (Tj ℂ n (Ov E w) ϖ 0) x = x := by
  classical
  have hfix : ∀ k ∈ KGL w n, ρ k x = x := by
    intro k hk
    have hx' := hx
    unfold fixed eig at hx'
    have := hx' ⟨k, hk⟩
    simpa using this
  have hd : diagJ n ϖ 0 = 1 := by
    unfold diagJ
    simp
  have hK : ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ 0 g = if g ∈ KGL w n then 1 else 0 := by
    intro g
    unfold Tj
    rw [Set.indicator_apply]
    by_cases hg : g ∈ KGL w n
    · rw [if_pos hg, if_pos]
      · rfl
      · simp only [Set.mem_setOf_eq]
        exact ⟨g, hg, 1, one_mem _, by simp [hd]⟩
    · rw [if_neg hg, if_neg]
      simp only [Set.mem_setOf_eq]
      rintro ⟨a, ha, b, hb, hab⟩
      apply hg
      have hg' : g = a * b := Units.ext (by simp [hab, hd])
      rw [hg']
      exact mul_mem ha hb
  unfold heckeVec
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : GL (Fin n) (w.adicCompletion E) ⧸ KGL w n)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w n) (1 : GL (Fin n) (w.adicCompletion E))
    rw [hk, one_mul, hK, if_pos k.2, one_smul, hfix _ k.2]
  · intro c hc
    rw [hK, if_neg, zero_smul]
    intro hmem
    apply hc
    rw [← QuotientGroup.out_eq' c]
    exact QuotientGroup.eq.mpr (by rw [mul_one]; exact inv_mem hmem)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0, hx00⟩ : ∃ x ∈ fixed ρ (KGL w n), x ≠ 0 := by`. Establish `hsp` using `hs`. Unfold `GlobalTheory.LGrp.IsSpherical at hsp`. Conclude with `Submodule.exists_mem_ne_zero_of_ne_bot hsp`. Take `⟨π0, hπ0⟩` from `w.valuation_exists_uniformizer E`.

Use `set π : w.adicCompletion E := (π0 : w.adicCompletion E) with hπdef`. Establish `hπ : IsUnifV E w π`. Unfold `IsUnifV`. Use `first`. Consider the case `(rw [hπdef, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ0]; rfl)`.

Consider the case `(rw [hπdef, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation, hπ0]; rfl)`. Consider the case `simpa [hπdef] using hπ0`. Establish `hπne : π ≠ 0`. Introduce `h0`. Establish `h1` using `hπ`.

Unfold `IsUnifV at h1`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe h1`. Use `set πu : (w.adicCompletion E)ˣ := Units.mk0 π hπne with hπu`. Establish `hTa : ∀ j g, Tj ℂ n (Ov E w) π j g = if ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), g = a * GlobalTheory.LFun.ConjPlace.dGL n πu j * b then 1 else 0` using `fun j g => by`.

Use `GlobalTheory.LFun.ConjPlace.Tj_apply (Ov E w) πu j g` as an intermediate fact. Simplify `this` using `[hπu]`. Establish `hbi : ∀ j, IsBiInv (KGL w n) (Tj ℂ n (Ov E w) π j)`. Introduce `j`. Unfold `IsBiInv`.

Introduce `a b g`. Rewrite using `[hTa, hTa]`. Establish `hK : ∀ k : KGL w n, (k : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (Ov E w)` using `fun k => k.2`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression.

It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Take `⟨a', ha', b', hb', h⟩` from `h1`. Use `⟨(a : GL (Fin n) (w.adicCompletion E))⁻¹ * a', mul_mem (inv_mem (hK a)) ha', b' * (b : GL (Fin n) (w.adicCompletion E))⁻¹, mul_mem hb' (inv_mem (hK b)), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises. Take `⟨a', ha', b', hb', h⟩` from `h2`. Use `⟨(a : GL (Fin n) (w.adicCompletion E)) * a', mul_mem (hK a) ha', b' * b, mul_mem hb' (hK b), ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Use `group`. Both sides reduce to the same expression. Establish `hfin : ∀ j, FinDosetSupp (KGL w n) (Tj ℂ n (Ov E w) π j)`. Introduce `j`. Unfold `FinDosetSupp`.

Use `⟨{GlobalTheory.LFun.ConjPlace.dGL n πu j}, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[hTa]`. Use `split_ifs at hg with h1`. Take `⟨a, ha, b, hb, h⟩` from `h1`. Conclude with `⟨_, by simp, ⟨a, ha⟩, ⟨b, hb⟩, h⟩`.

Conclude with `absurd rfl hg`. Establish `hmem : ∀ j, Tj ℂ n (Ov E w) π j ∈ Hecke ℂ (KGL w n)`. Introduce `j`. Unfold `Hecke`. Simplify using `only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`.

Conclude with `⟨hbi j, hfin j⟩`. Use `choose c hc using fun j => hH _ (hmem j)`. Establish `hq : (qV E w : ℂ) ≠ 0`. Unfold `qV`. Conclude with `Nat.cast_ne_zero.mpr fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)`.

Establish `hqs : ∀ s : ℂ, (qV E w : ℂ) ^ s ≠ 0` using `fun s => by`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. The claim follows by propositional logic. Establish `hc0 : c 0 = 1`. Establish `h1` using `hc 0 x0 hx0`.

Rewrite `h1` using `[heckeVec_Tj_zero ρ π hx0]`. Establish `h2 : (1 - c 0) • x0 = 0` using `by rw [sub_smul, one_smul, ← h1, sub_self]`. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `(sub_eq_zero.mp h).symm`. Conclude with `absurd h hx00`.

Establish `hcn : c n ≠ 0`. Introduce `h0`. Use `set z := GlobalTheory.LFun.ConjPlace.dGL n πu n with hz`. Establish `h1` using `GlobalTheory.LFun.ConjPlace.apply_heckeVec_shift (hbi n) hx0 z`. Establish `hsh : (fun g => Tj ℂ n (Ov E w) π n (z * g)) = Tj ℂ n (Ov E w) π 0`.

Use function extensionality and compare the values at `g`. Use `GlobalTheory.LFun.ConjPlace.Tj_shift_self (Ov E w) πu g` as an intermediate fact. Simplify `this` using `[hπu, hz]`. Rewrite `h1` using `[hsh, heckeVec_Tj_zero ρ π hx0, hc n x0 hx0, h0, zero_smul]`. Apply `hx00` to reduce the goal to its premises.

Establish `h2` using `congrArg (ρ z⁻¹) h1`. Establish `h3 : ρ z⁻¹ (ρ z x0) = x0` using `by first`. Consider the case `(rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])`. Consider the case `(rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)`. Consider the case `simp [← Module.End.mul_apply, ← map_mul]`.

Rewrite `h2` using `[h3, map_zero]`. Conclude with `h2`. Use `set A : ℕ → ℂ := fun j => c j / (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) with hA`. Take `⟨B, hB, hBe⟩` from `exists_esymm_eq n A (by simp [hA, hc0]) (by simp [hA, hcn])`. Use `⟨B, hs, fun x hx hx0' => ⟨hx0', hx, hB, fun ϖ hϖ j hj => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Tj_indep j hπ hϖ, hc j x hx]`. Use `congr 1`. Unfold `satEig`. Rewrite using `[hBe j hj, hA]`. Clear denominators, using `[hqs]` for the nonvanishing conditions.
-/
theorem exists_hasSatGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (hs : GlobalTheory.LGrp.IsSpherical ρ (KGL w n))
    (hH : ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed ρ (KGL w n), heckeVec ρ (KGL w n) h x = c • x) :
    ∃ B, HasSatGL w ρ B := by
  classical
  obtain ⟨x0, hx0, hx00⟩ : ∃ x ∈ fixed ρ (KGL w n), x ≠ 0 := by
    have hsp := hs
    unfold GlobalTheory.LGrp.IsSpherical at hsp
    exact Submodule.exists_mem_ne_zero_of_ne_bot hsp
  obtain ⟨π0, hπ0⟩ := w.valuation_exists_uniformizer E
  set π : w.adicCompletion E := (π0 : w.adicCompletion E) with hπdef
  have hπ : IsUnifV E w π := by
    unfold IsUnifV
    first
    | (rw [hπdef, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ0]; rfl)
    | (rw [hπdef, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation, hπ0]; rfl)
    | simpa [hπdef] using hπ0
  have hπne : π ≠ 0 := by
    intro h0; have h1 := hπ; unfold IsUnifV at h1; rw [h0, map_zero] at h1; exact WithZero.zero_ne_coe h1
  set πu : (w.adicCompletion E)ˣ := Units.mk0 π hπne with hπu
  have hTa : ∀ j g, Tj ℂ n (Ov E w) π j g = if ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      g = a * GlobalTheory.LFun.ConjPlace.dGL n πu j * b then 1 else 0 := fun j g => by
    have := GlobalTheory.LFun.ConjPlace.Tj_apply (Ov E w) πu j g
    simpa [hπu] using this
  have hbi : ∀ j, IsBiInv (KGL w n) (Tj ℂ n (Ov E w) π j) := by
    intro j
    unfold IsBiInv
    intro a b g
    rw [hTa, hTa]
    have hK : ∀ k : KGL w n, (k : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (Ov E w) := fun k => k.2
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      obtain ⟨a', ha', b', hb', h⟩ := h1
      refine ⟨(a : GL (Fin n) (w.adicCompletion E))⁻¹ * a', mul_mem (inv_mem (hK a)) ha',
        b' * (b : GL (Fin n) (w.adicCompletion E))⁻¹, mul_mem hb' (inv_mem (hK b)), ?_⟩
      calc g = (a : GL (Fin n) (w.adicCompletion E))⁻¹ * ((a : GL (Fin n) (w.adicCompletion E)) * g * b) *
            (b : GL (Fin n) (w.adicCompletion E))⁻¹ := by group
        _ = _ := by rw [h]; group
    · exfalso; apply h1
      obtain ⟨a', ha', b', hb', h⟩ := h2
      refine ⟨(a : GL (Fin n) (w.adicCompletion E)) * a', mul_mem (hK a) ha', b' * b, mul_mem hb' (hK b), ?_⟩
      rw [h]; group
    · rfl
  have hfin : ∀ j, FinDosetSupp (KGL w n) (Tj ℂ n (Ov E w) π j) := by
    intro j
    unfold FinDosetSupp
    refine ⟨{GlobalTheory.LFun.ConjPlace.dGL n πu j}, fun g hg => ?_⟩
    rw [hTa] at hg
    split_ifs at hg with h1
    · obtain ⟨a, ha, b, hb, h⟩ := h1
      exact ⟨_, by simp, ⟨a, ha⟩, ⟨b, hb⟩, h⟩
    · exact absurd rfl hg
  have hmem : ∀ j, Tj ℂ n (Ov E w) π j ∈ Hecke ℂ (KGL w n) := by
    intro j
    unfold Hecke
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    exact ⟨hbi j, hfin j⟩
  choose c hc using fun j => hH _ (hmem j)
  have hq : (qV E w : ℂ) ≠ 0 := by
    unfold qV
    exact Nat.cast_ne_zero.mpr fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have hqs : ∀ s : ℂ, (qV E w : ℂ) ^ s ≠ 0 := fun s => by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hc0 : c 0 = 1 := by
    have h1 := hc 0 x0 hx0
    rw [heckeVec_Tj_zero ρ π hx0] at h1
    have h2 : (1 - c 0) • x0 = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hx00
  have hcn : c n ≠ 0 := by
    intro h0
    set z := GlobalTheory.LFun.ConjPlace.dGL n πu n with hz
    have h1 := GlobalTheory.LFun.ConjPlace.apply_heckeVec_shift (hbi n) hx0 z
    have hsh : (fun g => Tj ℂ n (Ov E w) π n (z * g)) = Tj ℂ n (Ov E w) π 0 := by
      funext g
      have := GlobalTheory.LFun.ConjPlace.Tj_shift_self (Ov E w) πu g
      simpa [hπu, hz] using this
    rw [hsh, heckeVec_Tj_zero ρ π hx0, hc n x0 hx0, h0, zero_smul] at h1
    apply hx00
    have h2 := congrArg (ρ z⁻¹) h1
    have h3 : ρ z⁻¹ (ρ z x0) = x0 := by
      first
      | (rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
      | (rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      | simp [← Module.End.mul_apply, ← map_mul]
    rw [h3, map_zero] at h2
    exact h2
  set A : ℕ → ℂ := fun j => c j / (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) with hA
  obtain ⟨B, hB, hBe⟩ := exists_esymm_eq n A (by simp [hA, hc0]) (by simp [hA, hcn])
  refine ⟨B, hs, fun x hx hx0' => ⟨hx0', hx, hB, fun ϖ hϖ j hj => ?_⟩⟩
  rw [Tj_indep j hπ hϖ, hc j x hx]
  congr 1
  unfold satEig
  rw [hBe j hj, hA]
  field_simp [hqs]

end GlobalTheory.LFun.ExSatGL

end
