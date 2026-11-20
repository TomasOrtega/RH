import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.GradedWeylDivisibility.FinalC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Introduce `h0`. Use `(colLexInitMinor ℂ r n s I hs hI).2` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`.
-/
theorem initMinor_ne_zero_of_strictMono {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (hI : StrictMono I) :
    initMinor ℂ I hs ≠ 0 := by
  intro h0
  have := (colLexInitMinor ℂ r n s I hs hI).2
  rw [h0] at this
  simp at this

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.xiB`. Use `Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)` and prove the remaining obligations. Use `initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_` and prove the remaining obligations. Conclude with `hpq`. Use `initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_` and prove the remaining obligations.

Establish `h1` using `p.2`. Establish `h2` using `q.2`. Establish `h3` using `i.2`. Rewrite `hpq`, the goal using `[Fin.lt_def]`. Simplify using `only [Formalism.BranchingDeterminantCap.rowsB]`.

Apply the tactic sequence `split_ifs <;> simp <;> omega`.
-/
theorem xiB_ne_zero {n : ℕ} (lam sg : Fin n → ℕ) : Formalism.BranchingDeterminantCap.xiB ℂ lam sg ≠ 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    exact hpq
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    have h1 := p.2
    have h2 := q.2
    have h3 := i.2
    rw [Fin.lt_def] at hpq ⊢
    simp only [Formalism.BranchingDeterminantCap.rowsB]
    split_ifs <;> simp <;> omega

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `e : (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm` using `rfl`. Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using the standard rewrite rules.
-/
theorem det_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  have e : (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.transpose_apply, embGL_apply]`. Simplify using `only [Formalism.BranchingDeterminantCap.extM, Matrix.of_apply, Matrix.transpose_apply]`. Distinguish the cases in `h : a.val < n ∧ b.val < n`. Rewrite using `[dif_pos h, dif_pos h.symm]`.

Rewrite using `[dif_neg h, dif_neg (fun h' => h h'.symm)]`. Simplify using `only [eq_comm]`.
-/
theorem transpose_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose := by
  ext a b
  rw [Matrix.transpose_apply, embGL_apply]
  simp only [Formalism.BranchingDeterminantCap.extM, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dif_pos h, dif_pos h.symm]
  · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
    simp only [eq_comm]

/- English proof (translation)
Introduce `n N h lam mu hI`. Substitute `h` using the available equality. Use `set c : ℕ := (mu.detShift - lam.detShift).toNat with hcdef`. Establish `hls : lam.detShift = lam.w (Fin.last n)`. Simplify using `[DomWeight.detShift, Fin.last]`.

Establish `hlow : ∀ i, lam.detShift ≤ lam.w i` using `fun i => hls ▸ lam.anti (Fin.le_last i)`. Establish `hc : 0 < n → (c : ℤ) = mu.detShift - lam.detShift`. Introduce `hn`. Establish `h1` using `(hI ⟨n - 1, by omega⟩).2`. Establish `h2` using `hlow ⟨n - 1 + 1, by omega⟩`.

Establish `h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩` using `by simp [DomWeight.detShift, hn]`. Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers. Establish `hmlow : ∀ i, mu.detShift ≤ mu.w i` using `fun i => by`. Establish `hn : 0 < n` using `i.pos`.

Establish `h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩` using `by simp [DomWeight.detShift, hn]`. Rewrite using `[h3]`. Use `mu.anti ?_` and prove the remaining obligations. Use `i.2` as an intermediate fact. Rewrite using `[Fin.le_def]`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hsg : ∀ i, ((mu.natW i + c : ℕ) : ℤ) = mu.w i - lam.detShift` using `fun i => by`. Establish `h1` using `hc i.pos`. Establish `h2` using `hmlow i`.

Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers. Establish `hlz : ∀ a, Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc) a = lam.w a - lam.detShift` using `fun a => by`. Establish `h2` using `hlow a`. Unfold `Formalism.BranchingDeterminantCap.lamZ`.

Use `split_ifs with ha`. Establish `: (⟨a.val, ha⟩ : Fin n).castSucc = a` using `rfl`. Simplify using `only [DomWeight.natW, this]`. Use linear arithmetic over natural numbers and integers. Establish `: a = Fin.last n` using `Fin.ext (by have := a.2; simp; omega)`.

Rewrite using `[hls, this]`. Simplify using the standard rewrite rules. Establish `hI' : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc)) (fun i => ((mu.natW i + c : ℕ) : ℤ))`. Introduce `i`. Simplify using `only [hsg, hlz]`.

Establish `h1 : mu.w i ≤ lam.w i.castSucc` using `(hI i).1`. Establish `h2 : lam.w i.succ ≤ mu.w i` using `(hI i).2`. Apply the tactic sequence `constructor <;> omega`. Take `⟨io, hmem, heq, hhw, -⟩` from `Formalism.BranchingDeterminantCap.branchMap ℂ n (fun i : Fin n => lam.natW i.castSucc) (fun i => mu.natW i + c) hI'`. Take `⟨dm, de, dh⟩` from `GlobalTheory.Branching.genericDet_pow_mul n c mu.natW`.

Take `⟨am, ae⟩` from `GlobalTheory.Branching.AddColumn.add_column (n + 1) n lam.natW (by simp [DomWeight.natW, hls])`. Establish `ha : Antitone mu.natW` using `fun i j hij => by`. Use `mu.anti hij` as an intermediate fact. Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers.

Set `D : nablaSq ℂ n mu →ₗ[ℂ] dualWeyl ℂ n n (fun i => mu.natW i + c)` to `{ toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩ map_add' := fun f f' => Subtype.ext (by simp [mul_add]) map_smul' := fun a f => Subtype.ext (by simp) }`. Set `L : nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ (n + 1) lam` to `{ toFun := fun f => ⟨rename (Prod.map id Fin.castSucc) (io (D f)), am _ (hmem _)⟩ map_add' := fun f f' => Subtype.ext (by simp) map_smul' := fun a f => Subtype.ext (by simp) }`. Establish `hdet : ∀ g : GL (Fin n) ℂ, detPow ℂ n g mu.detShift = detPow ℂ n g lam.detShift * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c`. Introduce `g`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases.

Substitute `hn` using the available equality. Establish `: Matrix.GeneralLinearGroup.det g = 1` using `Units.ext (by simp)`. Simplify using `[detPow, this]`. Establish `: mu.detShift = lam.detShift + c` using `by have := hc hn; omega`. Rewrite using `[this, detPow, detPow, zpow_add, zpow_natCast]`.

Simplify using the standard rewrite rules. Establish `hL : ∀ (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu), L (sqRep ℂ n mu g f) = sqRep ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (L f)`. Introduce `g f`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hd0 : detPow ℂ n g lam.detShift ≠ 0` using `Units.ne_zero _`.

Establish `h1 : io ((detPow ℂ n g lam.detShift)⁻¹ • D (sqRep ℂ n mu g f)) = rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose) (io (D f))`. Apply `heq` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(detPow ℂ n g lam.detShift)⁻¹ • (lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n mu g f) = rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))`. Rewrite using `[de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]`. Establish `h2 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = detPow ℂ n g lam.detShift`.

Rewrite using `[detPow, detPow, det_embGL]`. Express the relevant statement in the definitionally equal form `rename (Prod.map id Fin.castSucc) (io (D (sqRep ℂ n mu g f))) = sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (rename (Prod.map id Fin.castSucc) (io (D f)))`. Rewrite using `[sqAct, transpose_embGL, ae, ← h1, h2, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]`. Use `⟨⟨L, fun g => LinearMap.ext fun f => hL g f⟩, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : L ⟨_, hwMem ℂ n n le_rfl _ ha⟩ = 0`.

Use `congrArg (fun φ => φ.toLinearMap ⟨_, hwMem ℂ n n le_rfl _ ha⟩) h0` as an intermediate fact. Conclude with `this`. Establish `h2 : rename (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) (io (D ⟨_, hwMem ℂ n n le_rfl _ ha⟩)) = 0` using `congrArg Subtype.val h1`. Rewrite `h2` using `[hhw _ (dh ha)]`. Establish `hinj : Function.Injective (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))` using `Function.injective_id.prodMap (Fin.castSucc_injective n)`.

Establish `h3` using `rename_injective _ hinj (h2.trans (map_zero _).symm)`. Break down `smul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `(Formalism.BranchingDeterminantCap.capConst n _ _ hI').1 (by exact_mod_cast h4)`. Conclude with `xiB_ne_zero _ _ h4`.
-/
theorem exists_intertwining_ne_zero : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu → ∃ φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam), φ ≠ 0 := by
  intro n N h lam mu hI
  subst h
  set c : ℕ := (mu.detShift - lam.detShift).toNat with hcdef
  have hls : lam.detShift = lam.w (Fin.last n) := by
    simp [DomWeight.detShift, Fin.last]
  have hlow : ∀ i, lam.detShift ≤ lam.w i := fun i => hls ▸ lam.anti (Fin.le_last i)
  have hc : 0 < n → (c : ℤ) = mu.detShift - lam.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have h2 := hlow ⟨n - 1 + 1, by omega⟩
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    simp only at h1
    omega
  have hmlow : ∀ i, mu.detShift ≤ mu.w i := fun i => by
    have hn : 0 < n := i.pos
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    rw [h3]
    refine mu.anti ?_
    have := i.2
    rw [Fin.le_def]
    simp only
    omega
  have hsg : ∀ i, ((mu.natW i + c : ℕ) : ℤ) = mu.w i - lam.detShift := fun i => by
    have h1 := hc i.pos
    have h2 := hmlow i
    simp only [DomWeight.natW]
    omega
  have hlz : ∀ a, Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc) a = lam.w a - lam.detShift := fun a => by
    have h2 := hlow a
    unfold Formalism.BranchingDeterminantCap.lamZ
    split_ifs with ha
    · have : (⟨a.val, ha⟩ : Fin n).castSucc = a := rfl
      simp only [DomWeight.natW, this]
      omega
    · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
      rw [hls, this]; simp
  have hI' : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc))
      (fun i => ((mu.natW i + c : ℕ) : ℤ)) := by
    intro i
    simp only [hsg, hlz]
    have h1 : mu.w i ≤ lam.w i.castSucc := (hI i).1
    have h2 : lam.w i.succ ≤ mu.w i := (hI i).2
    constructor <;> omega
  obtain ⟨io, hmem, heq, hhw, -⟩ := Formalism.BranchingDeterminantCap.branchMap ℂ n (fun i : Fin n => lam.natW i.castSucc)
    (fun i => mu.natW i + c) hI'
  obtain ⟨dm, de, dh⟩ := GlobalTheory.Branching.genericDet_pow_mul n c mu.natW
  obtain ⟨am, ae⟩ := GlobalTheory.Branching.AddColumn.add_column (n + 1) n lam.natW (by simp [DomWeight.natW, hls])
  have ha : Antitone mu.natW := fun i j hij => by
    have := mu.anti hij
    simp only [DomWeight.natW]
    omega
  let D : nablaSq ℂ n mu →ₗ[ℂ] dualWeyl ℂ n n (fun i => mu.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  let L : nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ (n + 1) lam :=
    { toFun := fun f => ⟨rename (Prod.map id Fin.castSucc) (io (D f)), am _ (hmem _)⟩
      map_add' := fun f f' => Subtype.ext (by simp)
      map_smul' := fun a f => Subtype.ext (by simp) }
  have hdet : ∀ g : GL (Fin n) ℂ, detPow ℂ n g mu.detShift =
      detPow ℂ n g lam.detShift * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    intro g
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have : mu.detShift = lam.detShift + c := by have := hc hn; omega
      rw [this, detPow, detPow, zpow_add, zpow_natCast]
      simp
  have hL : ∀ (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu),
      L (sqRep ℂ n mu g f) = sqRep ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (L f) := by
    intro g f
    apply Subtype.ext
    have hd0 : detPow ℂ n g lam.detShift ≠ 0 := Units.ne_zero _
    have h1 : io ((detPow ℂ n g lam.detShift)⁻¹ • D (sqRep ℂ n mu g f)) =
        rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose) (io (D f)) := by
      apply heq
      change (detPow ℂ n g lam.detShift)⁻¹ • (lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n mu g f) =
        rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose
          (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
      rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    have h2 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = detPow ℂ n g lam.detShift := by
      rw [detPow, detPow, det_embGL]
    change rename (Prod.map id Fin.castSucc) (io (D (sqRep ℂ n mu g f))) =
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (rename (Prod.map id Fin.castSucc) (io (D f)))
    rw [sqAct, transpose_embGL, ae, ← h1, h2, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  refine ⟨⟨L, fun g => LinearMap.ext fun f => hL g f⟩, fun h0 => ?_⟩
  have h1 : L ⟨_, hwMem ℂ n n le_rfl _ ha⟩ = 0 := by
    have := congrArg (fun φ => φ.toLinearMap ⟨_, hwMem ℂ n n le_rfl _ ha⟩) h0
    exact this
  have h2 : rename (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))
      (io (D ⟨_, hwMem ℂ n n le_rfl _ ha⟩)) = 0 := congrArg Subtype.val h1
  rw [hhw _ (dh ha)] at h2
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  have h3 := rename_injective _ hinj (h2.trans (map_zero _).symm)
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact (Formalism.BranchingDeterminantCap.capConst n _ _ hI').1 (by exact_mod_cast h4)
  · exact xiB_ne_zero _ _ h4

end GlobalTheory.Branching
