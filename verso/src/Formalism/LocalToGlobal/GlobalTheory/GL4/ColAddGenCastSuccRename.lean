import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingLinkFamilyNormalised
import Formalism.BranchSandwichDivisors.StatementW

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree

def colEmb (r n : ℕ) : Fin r × Fin n → Fin r × Fin (n + 1) := fun v => (v.1, v.2.castSucc)

/- English proof (translation)
Establish `h : (rowGen R (n` using `n + 1) a b).comp (rename (colEmb r n)) = (Polynomial.mapAlgHom (rename (colEmb r n))).comp (rowGen R (n := n) a b) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Polynomial.coe_mapAlgHom, Polynomial.map_add, Polynomial.map_C, colEmb]`. Apply the tactic sequence `split_ifs <;> simp [colEmb]`.

Establish `h2` using `congrArg (fun φ => φ f) h`. Simplify `h2` using `[Polynomial.coe_mapAlgHom]`.
-/
theorem rowGen_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen R a b (rename (colEmb r n) f) =
      Polynomial.map ((rename (colEmb r n) : MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin (n + 1)) R) :
        MvPolynomial (Fin r × Fin n) R →+* MvPolynomial (Fin r × Fin (n + 1)) R) (rowGen R a b f) := by
  have h : (rowGen R (n := n + 1) a b).comp (rename (colEmb r n)) =
      (Polynomial.mapAlgHom (rename (colEmb r n))).comp (rowGen R (n := n) a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Polynomial.coe_mapAlgHom, Polynomial.map_add,
      Polynomial.map_C, colEmb]
    split_ifs <;> simp [colEmb]
  have h2 := congrArg (fun φ => φ f) h
  simpa [Polynomial.coe_mapAlgHom] using h2

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[rowGen_rename, Polynomial.coeff_map]`. Both sides reduce to the same expression.
-/
theorem rowDiv_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (rename (colEmb r n) f) = rename (colEmb r n) (rowDiv R a b k f) := by
  unfold rowDiv
  rw [rowGen_rename, Polynomial.coeff_map]
  rfl

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih`. Simplify using `only [applyWord, List.foldr_cons] at ih ⊢`. Rewrite using `[ih, rowDiv_rename]`.
-/
theorem applyWord_rename (R : Type) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R w (rename (colEmb r n) f) = rename (colEmb r n) (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, rowDiv_rename]

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[show (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) = (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) from rfl, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, colEmb]`.

Both sides reduce to the same expression.
-/
theorem lpMinor_rename (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (hr : s ≤ n + 1) (hn : s ≤ n) :
    lpMinor R (r := n + 1) (n := n + 1) s hr (by omega) =
      rename (colEmb (n + 1) n) (lpMinor R (r := n + 1) (n := n) s hr hn) := by
  unfold lpMinor
  rw [show (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) =
      (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) from rfl,
    AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, colEmb]
  rfl

/- English proof (translation)
Unfold `hw`. Rewrite using `[Fin.prod_univ_castSucc, map_prod]`. Establish `hl : ν (Fin.last n) - nuNext ν (Fin.last n) = 0` using `by rw [hlast]; simp`. Rewrite using `[hl, pow_zero, mul_one]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `s _`. Rewrite using `[map_pow]`. Establish `hexp : nuNext ν s.castSucc = nuNext (fun s => ν s.castSucc) s`. Unfold `nuNext`. Distinguish the cases in `h : s.val + 1 < n`.

Apply the tactic sequence `rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega), dif_pos h]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h]`. Establish `hs : s.val + 1 = n` using `by omega`. Apply the tactic sequence `rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega)]`.

Apply the tactic sequence `have : (⟨(s.castSucc : Fin (n + 1)).val + 1, by simp only [Fin.val_castSucc] <;> omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last] <;> omega)`. Rewrite using `[this, hlast]`. Rewrite using `[hexp]`. Use `congr 1`. Conclude with `lpMinor_rename R (s.val + 1) (by omega) (by omega)`.
-/
theorem hw_rename (R : Type) [CommRing R] {n : ℕ} (ν : Fin (n + 1) → ℕ) (hlast : ν (Fin.last n) = 0) :
    hw R (r := n + 1) (n := n + 1) le_rfl ν =
      rename (colEmb (n + 1) n) (hw R (r := n + 1) (n := n) (Nat.le_succ n) (fun s => ν s.castSucc)) := by
  unfold hw
  rw [Fin.prod_univ_castSucc, map_prod]
  have hl : ν (Fin.last n) - nuNext ν (Fin.last n) = 0 := by rw [hlast]; simp
  rw [hl, pow_zero, mul_one]
  apply Finset.prod_congr rfl
  intro s _
  rw [map_pow]
  have hexp : nuNext ν s.castSucc = nuNext (fun s => ν s.castSucc) s := by
    unfold nuNext
    by_cases h : s.val + 1 < n
    · rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega), dif_pos h]
      rfl
    · rw [dif_neg h]
      have hs : s.val + 1 = n := by omega
      rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega)]
      have : (⟨(s.castSucc : Fin (n + 1)).val + 1, by simp only [Fin.val_castSucc] <;> omega⟩ : Fin (n + 1)) = Fin.last n :=
        Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last] <;> omega)
      rw [this, hlast]
  rw [hexp]
  congr 1
  exact lpMinor_rename R (s.val + 1) (by omega) (by omega)

/- English proof (translation)
Unfold `DomWeight.natW DomWeight.detShift`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Establish `: (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n` using `Fin.ext (by simp)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem natW_last {n : ℕ} (lam : DomWeight (n + 1)) : lam.natW (Fin.last n) = 0 := by
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  simp

/- English proof (translation)
Unfold `delSq weyl`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `applyWord R w (hw R le_rfl lam.natW) = rename (colEmb (n + 1) n) (applyWord R w (hw R (Nat.le_succ n) fun s => lam.natW s.castSucc))`.

Rewrite using `[← applyWord_rename, ← hw_rename R lam.natW (natW_last lam)]`.
-/
theorem delSq_eq_map (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight (n + 1)) :
    delSq R (n + 1) lam =
      (weyl R (n + 1) n (Nat.le_succ n) (fun s => lam.natW s.castSucc)).map
        (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _).toLinearMap := by
  unfold delSq weyl
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext w
  change applyWord R w (hw R le_rfl lam.natW) =
    rename (colEmb (n + 1) n) (applyWord R w (hw R (Nat.le_succ n) fun s => lam.natW s.castSucc))
  rw [← applyWord_rename, ← hw_rename R lam.natW (natW_last lam)]

/- English proof (translation)
Establish `h : (rowAct R (n` using `n + 1) g).comp (rename (colEmb r n)) = (rename (colEmb r n)).comp (rowAct R (n := n) g) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[rowAct, colEmb, map_sum]`. Conclude with `congrArg (fun φ => φ f) h`.
-/
theorem rowAct_rename (R : Type) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowAct R g (rename (colEmb r n) f) = rename (colEmb r n) (rowAct R g f) := by
  have h : (rowAct R (n := n + 1) g).comp (rename (colEmb r n)) =
      (rename (colEmb r n)).comp (rowAct R (n := n) g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct, colEmb, map_sum]
  exact congrArg (fun φ => φ f) h

/- English proof (translation)
Use extensionality with `a b`. Unfold `blockMat Formalism.BranchingDeterminantCap.extM`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Simplify using `[Matrix.reindex_apply, finSumFinEquiv_symm_last]`. Simplify using `[Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `[Matrix.reindex_apply]`.
-/
theorem blockMat_eq_extM {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : blockMat g = Formalism.BranchingDeterminantCap.extM ℂ g := by
  ext a b
  unfold blockMat Formalism.BranchingDeterminantCap.extM
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply]

/- English proof (translation)
Unfold `blockMat`. Rewrite using `[Matrix.transpose_reindex, Matrix.fromBlocks_transpose]`. Simplify using the standard rewrite rules.
-/
theorem blockMat_transpose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).transpose = blockMat g.transpose := by
  unfold blockMat
  rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

/- English proof (translation)
Establish `hd : lt.detShift = 0`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Establish `: (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n` using `Fin.ext (by simp)`. Rewrite using `[this, h0]`.

Unfold `sqAct detPow`. Rewrite using `[hd, zpow_zero, Units.val_one, one_smul]`.
-/
theorem sqAct_of_last_zero (R : Type) [CommRing R] {n : ℕ} (lt : DomWeight (n + 1))
    (h0 : lt.w (Fin.last n) = 0) (H : GL (Fin (n + 1)) R) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R) :
    sqAct R (n + 1) lt H f = rowAct R (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R).transpose f := by
  have hd : lt.detShift = 0 := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos n)]
    have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    rw [this, h0]
  unfold sqAct detPow
  rw [hd, zpow_zero, Units.val_one, one_smul]

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Rewrite using `[support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]`. Establish `hp` using `Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he`.

Unfold `Finsupp.prod at hp`. Rewrite using `[hp]`.
-/
theorem fockF_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (rename e f) (rename e g) = Formalism.REAL.fockF f g := by
  classical
  unfold Formalism.REAL.fockF
  rw [support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  have hp := Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he
  unfold Finsupp.prod at hp
  rw [hp]

/- English proof (translation)
Introduce `v w h`. Simplify using `only [colEmb, Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.castSucc_injective _ h.2)`.
-/
theorem colEmb_inj (r n : ℕ) : Function.Injective (colEmb r n) := by
  intro v w h
  simp only [colEmb, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castSucc_injective _ h.2)

/- English proof (translation)
Establish `h : (colAddGen R (r` using `r) l (Fin.last n)).comp (rename (colEmb r n)) = (rename some).comp (rename (colEmb r n)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Establish `hv : (colEmb r n v).2 ≠ Fin.last n` using `Fin.castSucc_ne_last v.2`. Simplify using `[colAddGen, hv]`.

Conclude with `congrArg (fun φ => φ f) h`.
-/
theorem colAddGen_last_rename (R : Type) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n) (rename (colEmb r n) f) = rename some (rename (colEmb r n) f) := by
  have h : (colAddGen R (r := r) l (Fin.last n)).comp (rename (colEmb r n)) =
      (rename some).comp (rename (colEmb r n)) := by
    apply MvPolynomial.algHom_ext
    intro v
    have hv : (colEmb r n v).2 ≠ Fin.last n := Fin.castSucc_ne_last v.2
    simp [colAddGen, hv]
  exact congrArg (fun φ => φ f) h

/- English proof (translation)
Establish `h : (colAddGen R (r` using `r) l.castSucc j.castSucc).comp (rename (colEmb r n)) = (rename (Option.map (colEmb r n))).comp (colAddGen R l j) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, colAddGen, aeval_X]`. Distinguish the cases in `hv : v.2 = j`.

Establish `hv' : (colEmb r n v).2 = j.castSucc` using `by simp [colEmb, hv]`. Rewrite using `[if_pos hv', if_pos hv]`. Simplify using `[colEmb]`. Establish `hv' : (colEmb r n v).2 ≠ j.castSucc`. Simplify using `only [colEmb, ne_eq, Fin.castSucc_inj]`.

Conclude with `hv`. Rewrite using `[if_neg hv', if_neg hv]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun φ => φ f) h`.
-/
theorem colAddGen_castSucc_rename (R : Type) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc (rename (colEmb r n) f) =
      rename (Option.map (colEmb r n)) (colAddGen R l j f) := by
  have h : (colAddGen R (r := r) l.castSucc j.castSucc).comp (rename (colEmb r n)) =
      (rename (Option.map (colEmb r n))).comp (colAddGen R l j) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, colAddGen, aeval_X]
    by_cases hv : v.2 = j
    · have hv' : (colEmb r n v).2 = j.castSucc := by simp [colEmb, hv]
      rw [if_pos hv', if_pos hv]
      simp [colEmb]
    · have hv' : (colEmb r n v).2 ≠ j.castSucc := by
        simp only [colEmb, ne_eq, Fin.castSucc_inj]
        exact hv
      rw [if_neg hv', if_neg hv]
      simp
  exact congrArg (fun φ => φ f) h

/- English proof (translation)
Unfold `dualWeyl at hf ⊢`. Rewrite `hf`, the goal using `[Submodule.mem_inf]`. Take `⟨hw, hk⟩` from `hf`. Prove the components needed by the constructor for the conclusion. Rewrite `hw`, the goal using `[mem_weightedHomogeneousSubmodule]`.

Introduce `d hd`. Establish `hmem : d ∈ (rename (colEmb (n + 1) n) f).support` using `mem_support_iff.mpr hd`. Rewrite `hmem` using `[support_rename_of_injective (colEmb_inj _ _), Finset.mem_image]`. Take `⟨d', hd', rfl⟩` from `hmem`. Establish `h1` using `hw (mem_support_iff.mp hd')`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj (colEmb_inj _ _)]`. Rewrite `h1` using `[Finsupp.weight_apply]`. Use function extensionality and compare the values at `t`. Break down `Fin.eq_castSucc_or_eq_last t with ⟨i, rfl⟩ | rfl` into its components or cases. Use `congrFun h1 i` as an intermediate fact.

Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply, Fin.castSucc_inj] at this ⊢`. Conclude with `this`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply, hlast]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `v _`.

Rewrite using `[if_neg (Fin.castSucc_ne_last v.2).symm, smul_zero]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at hk ⊢`. Introduce `l j hlj`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl` into its components or cases. Establish `hl : l.val < n`.

Use `Fin.lt_def.mp hlj` as an intermediate fact. Simplify using `only [Fin.val_castSucc] at this`. Use linear arithmetic over natural numbers and integers. Establish `hll : l = (⟨l.val, hl⟩ : Fin n).castSucc` using `Fin.ext rfl`. Establish `hlt : (⟨l.val, hl⟩ : Fin n) < j'`.

Rewrite `hlj`, the goal using `[Fin.lt_def]`. Simplify using `using hlj`. Rewrite using `[hll, colAddGen_castSucc_rename, hk _ j' hlt, rename_rename, rename_rename]`. Both sides reduce to the same expression. Conclude with `colAddGen_last_rename R l f`.
-/
theorem rename_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} (ν : Fin (n + 1) → ℕ) (hlast : ν (Fin.last n) = 0)
    (f : MvPolynomial (Fin (n + 1) × Fin n) R) (hf : f ∈ dualWeyl R (n + 1) n (fun s => ν s.castSucc)) :
    rename (colEmb (n + 1) n) f ∈ dualWeyl R (n + 1) (n + 1) ν := by
  classical
  unfold dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨hw, hk⟩ := hf
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    intro d hd
    have hmem : d ∈ (rename (colEmb (n + 1) n) f).support := mem_support_iff.mpr hd
    rw [support_rename_of_injective (colEmb_inj _ _), Finset.mem_image] at hmem
    obtain ⟨d', hd', rfl⟩ := hmem
    have h1 := hw (mem_support_iff.mp hd')
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj (colEmb_inj _ _)]
    rw [Finsupp.weight_apply] at h1
    funext t
    rcases Fin.eq_castSucc_or_eq_last t with ⟨i, rfl⟩ | rfl
    · have := congrFun h1 i
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply,
        Fin.castSucc_inj] at this ⊢
      exact this
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply, hlast]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (Fin.castSucc_ne_last v.2).symm, smul_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hk ⊢
    intro l j hlj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hl : l.val < n := by
        have := Fin.lt_def.mp hlj
        simp only [Fin.val_castSucc] at this
        omega
      have hll : l = (⟨l.val, hl⟩ : Fin n).castSucc := Fin.ext rfl
      have hlt : (⟨l.val, hl⟩ : Fin n) < j' := by
        rw [Fin.lt_def] at hlj ⊢
        simpa using hlj
      rw [hll, colAddGen_castSucc_rename, hk _ j' hlt, rename_rename, rename_rename]
      rfl
    · exact colAddGen_last_rename R l f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scaleMat_eq_zScale (n : ℕ) (T : ℝ) : scaleMat n T = Formalism.BranchingDeterminantCap.zScale n (Real.sqrt T) := rfl

/- English proof (translation)
Unfold `scaleMat`. Conclude with `Matrix.diagonal_transpose _`.
-/
theorem scaleMat_transpose (n : ℕ) (T : ℝ) : (scaleMat n T).transpose = scaleMat n T := by
  unfold scaleMat
  exact Matrix.diagonal_transpose _

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
