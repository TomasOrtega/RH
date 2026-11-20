import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace CompanionTheory.RgGu.NR.DerEq

section Abstract

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hle : twKer ρ N₁ θ₁ ≤ twKer ρ N θ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, v, rfl⟩`. Take `⟨h, hθ⟩` from `h1 u`. Conclude with `Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩`.

Establish `key : twKer σ N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨a, x, rfl⟩`. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H v`. Take `⟨h, hθ⟩` from `h2 a`. Use `⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]`. Rewrite using `[Submodule.map_le_iff_le_comap]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, v, rfl⟩`. Take `⟨u₁, a, hu⟩` from `h3 u`. Take `⟨hu₁, e1⟩` from `h1 u₁`. Take `⟨ha, e2⟩` from `h2 a`.

Establish `hθ : θ u = θ₁ u₁ * θ₂ a`. Establish `: u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩` using `Subtype.ext hu`. Rewrite using `[this, map_mul, e1, e2]`. Establish `hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v = (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) + ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v)`. Rewrite using `[hθ, hu, map_mul, Module.End.mul_apply, Units.val_mul, smul_sub, mul_smul]`.

Normalize the expressions using the abelian group laws. Establish `hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁` using `Submodule.subset_span ⟨u₁, _, rfl⟩`. Use `show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer σ N₂ θ₂`. Rewrite using `[hdec, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)` and prove the remaining obligations.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]`. Rewrite using `[key, Submodule.comap_map_mkQ, sup_eq_right.2 hle]`.
-/
theorem comap_twKer (ρ : Representation ℂ G V) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ)
    (σ : Representation ℂ M (TwJacquet ρ N₁ θ₁)) (s : M →* G)
    (hσ : ∀ m v, σ m (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (s m) v))
    (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
    (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
    (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
    (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
    (twKer σ N₂ θ₂).comap (twKer ρ N₁ θ₁).mkQ = twKer ρ N θ := by
  have hle : twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    obtain ⟨h, hθ⟩ := h1 u
    exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
  have key : twKer σ N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro w ⟨a, x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨h, hθ⟩ := h2 a
        refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
        rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨u₁, a, hu⟩ := h3 u
      obtain ⟨hu₁, e1⟩ := h1 u₁
      obtain ⟨ha, e2⟩ := h2 a
      have hθ : θ u = θ₁ u₁ * θ₂ a := by
        have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
        rw [this, map_mul, e1, e2]
      have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
          (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
            ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
        rw [hθ, hu, map_mul, Module.End.mul_apply, Units.val_mul, smul_sub, mul_smul]
        abel
      have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
        Submodule.subset_span ⟨u₁, _, rfl⟩
      show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer σ N₂ θ₂
      rw [hdec, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]
  rw [key, Submodule.comap_map_mkQ, sup_eq_right.2 hle]

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def Q (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → (τ : MRep k (n + j)) →
    τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1
  | 0, τ => (twKer τ.ρ (MirUin k n) 1).mkQ
  | j + 1, τ => (Q ψ j (MRep.phiM k ψ τ)) ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ

/- English proof (translation)
The claim follows from `| 0, τ => Submodule.mkQ_surjective _ | j + 1, τ => (Q_surj ψ j (MRep.phiM k ψ τ)).comp (Submodule.mkQ_surjective _)`.
-/
theorem Q_surj (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)), Function.Surjective (Q k ψ j τ)
  | 0, τ => Submodule.mkQ_surjective _
  | j + 1, τ => (Q_surj ψ j (MRep.phiM k ψ τ)).comp (Submodule.mkQ_surjective _)

/- English proof (translation)
The claim follows from `| 0, τ => by show LinearMap.ker (twKer τ.ρ (MirUin k n) 1).mkQ = _ rw [Submodule.ker_mkQ] exact GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ | j + 1, τ => by have hnm : n ≤ n + j := Nat.le_add_right n j have H := comap_twKer τ.ρ (MirUin k (n + j + 1)) (mi …`.
-/
theorem ker_Q (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    LinearMap.ker (Q k ψ j τ) = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)
  | 0, τ => by
    show LinearMap.ker (twKer τ.ρ (MirUin k n) 1).mkQ = _
    rw [Submodule.ker_mkQ]
    exact GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ
  | j + 1, τ => by
    have hnm : n ≤ n + j := Nat.le_add_right n j
    have H := comap_twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j)) (phiMinus k ψ τ.ρ)
      ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype) (fun _ _ => rfl) (derUnipM k (n + j) n)
      (derCharM k ψ (n + j) n) (derUnipM k (n + j + 1) n) (derCharM k ψ (n + j + 1) n)
      (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
      (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
    ext v
    have e1 := Submodule.ext_iff.1 H v
    rw [Submodule.mem_comap] at e1
    refine Iff.trans ?_ e1
    have e2 := Submodule.ext_iff.1 (ker_Q ψ j (MRep.phiM k ψ τ))
      ((twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ v)
    exact e2

variable (k) in

def E {n : ℕ} : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => (levi k (n + j + 1)).comp ((Mir k (n + j)).subtype.comp (E j))

/- English proof (translation)
The claim follows from `| 0, τ, g, v => rfl | j + 1, τ, g, v => Q_equiv ψ j (MRep.phiM k ψ τ) g (Submodule.Quotient.mk v)`.
-/
theorem Q_equiv (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)) (g : GL (Fin n) k) (v : τ.V),
    Q k ψ j τ (τ.ρ (E k j g) v) = derivM k ψ j τ g (Q k ψ j τ v)
  | 0, τ, g, v => rfl
  | j + 1, τ, g, v => Q_equiv ψ j (MRep.phiM k ψ τ) g (Submodule.Quotient.mk v)

/- English proof (translation)
Use `show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i l = _`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [glEmbMat]`.

Consider the case `cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm]`. Consider the case `cast i`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]`. Consider the case `cast l => simp [glEmbMat]`.
-/
theorem E_val_zero {n : ℕ} (g : GL (Fin n) k) (i l : Fin (n + 1)) :
    (((E k 0 g : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i l = _
  induction i using Fin.lastCases with
  | last =>
    induction l using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm]
  | cast i =>
    induction l using Fin.lastCases with
    | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast l => simp [glEmbMat]

/- English proof (translation)
Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `: ¬ ((n + j + 1 : ℕ) < n)` using `by omega`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [glEmbMat, this]`.

Consider the case `cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm, this]`. Consider the case `cast i`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last`. Establish `: ¬ ((n + j + 1 : ℕ) < n)` using `by omega`.

Simplify using `[glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last, this]`. Consider the case `cast l`. Simplify using `only [glEmbMat, Fin.lastCases_castSucc]`. Rewrite using `[ih i l]`. Simplify using `[Matrix.one_apply]`.
-/
theorem E_val_succ {n j : ℕ} (g : GL (Fin n) k)
    (ih : ∀ i l : Fin (n + j + 1), (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l) (i l : Fin (n + j + 1 + 1)) :
    glEmbMat k (n + j + 1) (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1 + 1)) (Fin (n + j + 1 + 1)) k) i l := by
  induction i using Fin.lastCases with
  | last =>
    have : ¬ ((n + j + 1 : ℕ) < n) := by omega
    induction l using Fin.lastCases with
    | last => simp [glEmbMat, this]
    | cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm, this]
  | cast i =>
    induction l using Fin.lastCases with
    | last =>
      have : ¬ ((n + j + 1 : ℕ) < n) := by omega
      simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last, this]
    | cast l =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      rw [ih i l]
      simp [Matrix.one_apply]

/- English proof (translation)
The claim follows from `| 0, i, l => E_val_zero g i l | j + 1, i, l => E_val_succ g (E_val g j) i l`.
-/
theorem E_val {n : ℕ} (g : GL (Fin n) k) : ∀ (j : ℕ) (i l : Fin (n + j + 1)),
    (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l
  | 0, i, l => E_val_zero g i l
  | j + 1, i, l => E_val_succ g (E_val g j) i l

/- English proof (translation)
Rewrite using `[val_emb₂]`. Simplify using `[Matrix.reindex_apply]`.
-/
theorem emb_val {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (a b : Fin n ⊕ Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) =
      fromBlocks (g.1 : Matrix (Fin n) (Fin n) k) 0 0 (g.2 : Matrix (Fin t) (Fin t) k) a b := by
  rw [val_emb₂]
  simp [Matrix.reindex_apply]

/- English proof (translation)
The claim follows from `(stdSum h).injective.eq_iff`.
-/
theorem stdSum_inj {n t N : ℕ} (h : n + t = N) {a b : Fin n ⊕ Fin t} : stdSum h a = stdSum h b ↔ a = b :=
  (stdSum h).injective.eq_iff

/- English proof (translation)
Simplify using `[Matrix.one_apply, stdSum_inj]`.
-/
theorem one_std {n t N : ℕ} (h : n + t = N) (a b : Fin n ⊕ Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) = (1 : Matrix (Fin n ⊕ Fin t) (Fin n ⊕ Fin t) k) a b := by
  simp [Matrix.one_apply, stdSum_inj]

/- English proof (translation)
Use extensionality with `i l`. Take `⟨a, rfl⟩` from `(stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective i`. Take `⟨b, rfl⟩` from `(stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective l`. Rewrite using `[emb_val, E_val]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`.

Establish `ha` using `a.2`. Establish `hb` using `b.2`. Simplify using `only [stdSum_inl, fromBlocks_apply₁₁]`. Rewrite using `[dif_pos ⟨ha, hb⟩]`. Simplify using `only [stdSum_inl, stdSum_inr, fromBlocks_apply₁₂, Matrix.zero_apply]`.

Rewrite using `[dif_neg (by omega), one_std]`. Simplify using the standard rewrite rules. Simplify using `only [stdSum_inl, stdSum_inr, fromBlocks_apply₂₁, Matrix.zero_apply]`. Rewrite using `[dif_neg (by omega), one_std]`. Simplify using the standard rewrite rules.

Simplify using `only [stdSum_inr, fromBlocks_apply₂₂]`. Rewrite using `[dif_neg (by omega), one_std]`. Simplify using `[Matrix.one_apply]`.
-/
theorem E_eq {n j : ℕ} (g : GL (Fin n) k) :
    ((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (show n + (j + 1) = n + j + 1 from rfl)) (g, 1) := by
  ext i l
  obtain ⟨a, rfl⟩ := (stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective i
  obtain ⟨b, rfl⟩ := (stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective l
  rw [emb_val, E_val]
  rcases a with a | a <;> rcases b with b | b
  · have ha := a.2
    have hb := b.2
    simp only [stdSum_inl, fromBlocks_apply₁₁]
    rw [dif_pos ⟨ha, hb⟩]
  · simp only [stdSum_inl, stdSum_inr, fromBlocks_apply₁₂, Matrix.zero_apply]
    rw [dif_neg (by omega), one_std]
    simp
  · simp only [stdSum_inl, stdSum_inr, fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [dif_neg (by omega), one_std]
    simp
  · simp only [stdSum_inr, fromBlocks_apply₂₂]
    rw [dif_neg (by omega), one_std]
    simp [Matrix.one_apply]

section Blocks

variable {n t N : ℕ} (h : n + t = N)

def InU (g : GL (Fin N) k) : Prop :=
  ∀ i l : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (l : ℕ)) → (g : Matrix (Fin N) (Fin N) k) i l = (1 : Matrix (Fin N) (Fin N) k) i l

/- English proof (translation)
Take `⟨hp, hd⟩` from `mem_unipRad.1 hg`. Introduce `i l hil`. Take `⟨a, rfl⟩` from `(stdSum h).surjective i`. Take `⟨b, rfl⟩` from `(stdSum h).surjective l`. Rewrite using `[one_std]`.

Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `(hd false a b).trans (by simp [Matrix.one_apply])`. Conclude with `absurd ⟨by simp [a.2], by simp⟩ hil`. Establish `hlt : ((two (stdSum h)).symm ((two (stdSum h)) ⟨false, b⟩)).1 < ((two (stdSum h)).symm ((two (stdSum h)) ⟨true, a⟩)).1`. Rewrite using `[Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (show (false : Bool) < true by decide)`.

Use `hp hlt` as an intermediate fact. Conclude with `this.trans (by simp)`. Conclude with `(hd true a b).trans (by simp [Matrix.one_apply])`.
-/
theorem inU_of_mem {g : GL (Fin N) k} (hg : g ∈ unipRad k (two (stdSum h))) : InU (n := n) g := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hg
  intro i l hil
  obtain ⟨a, rfl⟩ := (stdSum h).surjective i
  obtain ⟨b, rfl⟩ := (stdSum h).surjective l
  rw [one_std]
  rcases a with a | a <;> rcases b with b | b
  · exact (hd false a b).trans (by simp [Matrix.one_apply])
  · exact absurd ⟨by simp [a.2], by simp⟩ hil
  · have hlt : ((two (stdSum h)).symm ((two (stdSum h)) ⟨false, b⟩)).1 <
        ((two (stdSum h)).symm ((two (stdSum h)) ⟨true, a⟩)).1 := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (show (false : Bool) < true by decide)
    have := hp hlt
    exact this.trans (by simp)
  · exact (hd true a b).trans (by simp [Matrix.one_apply])

/- English proof (translation)
Use `mem_unipRad.2 ⟨?_, fun a i j => ?_⟩` and prove the remaining obligations. Introduce `i l hlt`. Take `⟨⟨a, x⟩, rfl⟩` from `(two (stdSum h)).surjective i`. Take `⟨⟨b, y⟩, rfl⟩` from `(two (stdSum h)).surjective l`. Establish `hb : ((two (stdSum h)).symm ((two (stdSum h)) ⟨b, y⟩)).1 < ((two (stdSum h)).symm ((two (stdSum h)) ⟨a, x⟩)).1` using `hlt`.

Rewrite `hb` using `[Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `cases a <;> cases b`. Conclude with `absurd hb (show ¬ ((false : Bool) < false) by decide)`. Conclude with `absurd hb (show ¬ ((true : Bool) < false) by decide)`. Establish `e` using `H ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) (by simp)`.

Establish `e' : (1 : Matrix (Fin N) (Fin N) k) ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) = 0`. Rewrite using `[one_std]`. Simplify using the standard rewrite rules. Conclude with `e.trans e'`. Conclude with `absurd hb (show ¬ ((true : Bool) < true) by decide)`.

Consider the cases of `a`. Conclude with `(H ((stdSum h) (Sum.inl i)) ((stdSum h) (Sum.inl j)) (by simp)).trans (by rw [one_std]; simp [Matrix.one_apply])`. Conclude with `(H ((stdSum h) (Sum.inr i)) ((stdSum h) (Sum.inr j)) (by simp)).trans (by rw [one_std]; simp [Matrix.one_apply])`.
-/
theorem mem_of_inU {g : GL (Fin N) k} (H : InU (n := n) g) : g ∈ unipRad k (two (stdSum h)) := by
  refine mem_unipRad.2 ⟨?_, fun a i j => ?_⟩
  · intro i l hlt
    obtain ⟨⟨a, x⟩, rfl⟩ := (two (stdSum h)).surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := (two (stdSum h)).surjective l
    have hb : ((two (stdSum h)).symm ((two (stdSum h)) ⟨b, y⟩)).1 <
        ((two (stdSum h)).symm ((two (stdSum h)) ⟨a, x⟩)).1 := hlt
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hb
    cases a <;> cases b
    · exact absurd hb (show ¬ ((false : Bool) < false) by decide)
    · exact absurd hb (show ¬ ((true : Bool) < false) by decide)
    · have e := H ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) (by simp)
      have e' : (1 : Matrix (Fin N) (Fin N) k) ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) = 0 := by
        rw [one_std]; simp
      exact e.trans e'
    · exact absurd hb (show ¬ ((true : Bool) < true) by decide)
  · cases a
    · exact (H ((stdSum h) (Sum.inl i)) ((stdSum h) (Sum.inl j)) (by simp)).trans
        (by rw [one_std]; simp [Matrix.one_apply])
    · exact (H ((stdSum h) (Sum.inr i)) ((stdSum h) (Sum.inr j)) (by simp)).trans
        (by rw [one_std]; simp [Matrix.one_apply])

end Blocks

variable (k) in

def Q' (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t) :=
  (twKer (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t)).mkQ ∘ₗ
    (twKer π (unipRad k (two (stdSum h))) 1).mkQ

/- English proof (translation)
The claim follows from `(Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)`.
-/
theorem Q'_surj (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : Function.Surjective (Q' k ψ h π) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Q'_equiv (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (g : GL (Fin n) k) (v : V) :
    Q' k ψ h π (π (emb₂ k (stdSum h) (g, 1)) v) = derRep k ψ h π g (Q' k ψ h π v) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derChar_val (ψ : AddChar k Circle) {N n : ℕ} (x : derUnip k N n) :
    derChar k ψ N n x = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
      (fun p : Fin N × Fin N => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
        ((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2)) := rfl

/- English proof (translation)
Establish `H` using `comap_twKer π (unipRad k (two (stdSum h))) 1 (jacU₂ (stdSum h) π) (emb₂ k (stdSum h)) (fun _ _ => rfl) (rightUnip k n t) (rightWhit k ψ n t) (derUnip k N n) (derChar k ψ N n) ?_ ?_ ?_`. Use extensionality with `v`. Establish `e1` using `Submodule.ext_iff.1 H v`. Rewrite `e1` using `[Submodule.mem_comap]`. Rewrite using `[LinearMap.mem_ker, ← e1]`.

Conclude with `Submodule.Quotient.mk_eq_zero _`. Introduce `u`. Establish `hU` using `inU_of_mem h u.2`. Establish `hmem : (u : GL (Fin N) k) ∈ derUnip k N n`. Use `⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩` and prove the remaining obligations.

Rewrite using `[hU i l (by omega)]`. Conclude with `Matrix.one_apply_ne (fun e => by rw [e] at hli; exact lt_irrefl _ hli)`. Rewrite using `[hU i i (by omega)]`. Conclude with `Matrix.one_apply_eq i`. Conclude with `hU i l (by omega)`.

Use `⟨hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[derChar_val]`. Establish `: ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), (((⟨(u : GL (Fin N) k), hmem⟩ : derUnip k N n) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`.

Use `show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0`. Rewrite using `[hU p.1 p.2 (by omega)]`. Conclude with `Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Introduce `a`. Take `⟨⟨a1, w⟩, ha⟩` from `a`. Establish `ha1 : a1 = 1` using `Subgroup.mem_bot.1 (Subgroup.mem_prod.1 ha).1`. Establish `hw : w ∈ unipB k (Fin t)` using `(Subgroup.mem_prod.1 ha).2`. Substitute `ha1` using the available equality.

Take `⟨hw1, hw2⟩` from `(mem_unipB k).1 hw`. Establish `hent : ∀ a b : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) = fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (w : Matrix (Fin t) (Fin t) k) a b`. Introduce `a b`. Rewrite using `[emb_val]`. Both sides reduce to the same expression.

Establish `hmem : emb₂ k (stdSum h) (1, w) ∈ derUnip k N n`. Use `⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(stdSum h).surjective i`. Take `⟨b, rfl⟩` from `(stdSum h).surjective l`. Rewrite using `[hent]`.

Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `only [fromBlocks_apply₁₁]`. Conclude with `Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hli)`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Simplify using `only [fromBlocks_apply₂₂]`. Conclude with `hw1 a b (by rw [Fin.lt_iff_val_lt_val] at hli ⊢; simp at hli; omega)`. Take `⟨a, rfl⟩` from `(stdSum h).surjective i`. Rewrite using `[hent]`. Break down `a with a | a` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[hw2 a]`. Take `⟨a, rfl⟩` from `(stdSum h).surjective i`. Take `⟨b, rfl⟩` from `(stdSum h).surjective l`. Rewrite using `[hent, one_std]`.

Break down `b with b | b` into its components or cases. Apply the tactic sequence `rcases a with a | a <;> simp [Matrix.one_apply]`. Simplify using `at hl`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[derChar_val]`.

Use `show _ = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter (fun p : Fin t × Fin t => (p.2 : ℕ) = p.1 + 1), (w : Matrix (Fin t) (Fin t) k) p.1 p.2))`. Use `congr 2`. Use `Finset.sum_bij' (fun q hq => (⟨(q.1 : ℕ) - n, ?_⟩, ⟨(q.2 : ℕ) - n, ?_⟩)) (fun p _ => ((stdSum h (Sum.inr p.1)), (stdSum h (Sum.inr p.2)))) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Use `q.1.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Use `q.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `q hq`.

Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`. Use `(Finset.mem_filter.1 hp).2` as an intermediate fact.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, stdSum_inr]`. Use linear arithmetic over natural numbers and integers. Introduce `q hq`. Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Apply the tactic sequence `ext <;> simp <;> omega`.

Introduce `p hp`. Apply the tactic sequence `ext <;> simp`. Introduce `q hq`. Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Establish `e1 : q.1 = stdSum h (Sum.inr ⟨(q.1 : ℕ) - n, by have` using `q.1.2; omega⟩) := by ext; simp; omega`.

Establish `e2 : q.2 = stdSum h (Sum.inr ⟨(q.2 : ℕ) - n, by have` using `q.2.2; omega⟩) := by ext; simp; omega`. Use `show (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) q.1 q.2 = _`. Use `conv_lhs => rw [e1, e2]`. Rewrite using `[hent]`. Both sides reduce to the same expression.

Introduce `u`. Take `⟨hu1, hu2⟩` from `(mem_unipB k).1 u.2.1`. Establish `hcol` using `(GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).1 u.2.2`. Set `D : Matrix (Fin t) (Fin t) k` to `fun x y => ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr x)) (stdSum h (Sum.inr y))`. Establish `hDl : ∀ x y, y < x → D x y = 0` using `fun x y hxy => hu1 _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; exact hxy)`.

Establish `hDd : ∀ x, D x x = 1` using `fun x => hu2 _`. Establish `hdet : D.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun x y hxy => hDl x y hxy)]`. Simplify using `[hDd]`. Establish `hD : IsUnit D` using `(Matrix.isUnit_iff_isUnit_det D).2 (by rw [hdet]; exact isUnit_one)`.

Set `Dg : GL (Fin t) k` to `hD.unit`. Establish `hDg : Dg ∈ unipB k (Fin t)` using `(mem_unipB k).2 ⟨hDl, hDd⟩`. Set `a : rightUnip k n t` to `⟨(1, Dg), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hDg⟩⟩`. Establish `hDinv : D * ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1` using `by show ((Dg : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) * _ = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hmemU : (u : GL (Fin N) k) * (emb₂ k (stdSum h) (1, Dg))⁻¹ ∈ unipRad k (two (stdSum h))`. Apply `mem_of_inU h` to reduce the goal to its premises. Introduce `i l hil`. Rewrite using `[← map_inv, Prod.inv_mk, inv_one, Units.val_mul, Matrix.mul_apply, ← (stdSum h).sum_comp, Fintype.sum_sum_type]`. Take `⟨b, rfl⟩` from `(stdSum h).surjective l`.

Establish `hent : ∀ c : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, Dg⁻¹) : Matrix (Fin N) (Fin N) k) (stdSum h c) (stdSum h b) = fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) c b` using `fun c => by rw [emb_val]; rfl`. Simplify using `only [hent]`. Break down `b with b | b` into its components or cases. Simplify using `only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `hcol i _ (by simp)`.

Take `⟨a', rfl⟩` from `(stdSum h).surjective i`. Break down `a' with a' | a'` into its components or cases. Conclude with `absurd ⟨by simp [a'.2], by simp⟩ hil`. Simplify using `only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]`. Rewrite using `[one_std]`.

Use `congrFun (congrFun hDinv a') b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Simplify `this` using `[Matrix.one_apply]`. Conclude with `⟨⟨_, hmemU⟩, a, by simp [a]⟩`.
-/
theorem ker_Q' (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    LinearMap.ker (Q' k ψ h π) = twKer π (derUnip k N n) (derChar k ψ N n) := by
  have H := comap_twKer π (unipRad k (two (stdSum h))) 1 (jacU₂ (stdSum h) π) (emb₂ k (stdSum h)) (fun _ _ => rfl)
    (rightUnip k n t) (rightWhit k ψ n t) (derUnip k N n) (derChar k ψ N n) ?_ ?_ ?_
  · ext v
    have e1 := Submodule.ext_iff.1 H v
    rw [Submodule.mem_comap] at e1
    rw [LinearMap.mem_ker, ← e1]
    exact Submodule.Quotient.mk_eq_zero _
  ·
    intro u
    have hU := inU_of_mem h u.2
    have hmem : (u : GL (Fin N) k) ∈ derUnip k N n := by
      refine ⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩
      · rw [hU i l (by omega)]
        exact Matrix.one_apply_ne (fun e => by rw [e] at hli; exact lt_irrefl _ hli)
      · rw [hU i i (by omega)]
        exact Matrix.one_apply_eq i
      · exact hU i l (by omega)
    refine ⟨hmem, ?_⟩
    rw [derChar_val]
    have : ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
        (((⟨(u : GL (Fin N) k), hmem⟩ : derUnip k N n) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
      show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
      rw [hU p.1 p.2 (by omega)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)
    rw [this]
    simp
  ·
    intro a
    obtain ⟨⟨a1, w⟩, ha⟩ := a
    have ha1 : a1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 ha).1
    have hw : w ∈ unipB k (Fin t) := (Subgroup.mem_prod.1 ha).2
    subst ha1
    obtain ⟨hw1, hw2⟩ := (mem_unipB k).1 hw
    have hent : ∀ a b : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) =
        fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (w : Matrix (Fin t) (Fin t) k) a b := by
      intro a b; rw [emb_val]; rfl
    have hmem : emb₂ k (stdSum h) (1, w) ∈ derUnip k N n := by
      refine ⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        obtain ⟨b, rfl⟩ := (stdSum h).surjective l
        rw [hent]
        rcases a with a | a <;> rcases b with b | b
        · simp only [fromBlocks_apply₁₁]
          exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hli)
        · rfl
        · rfl
        · simp only [fromBlocks_apply₂₂]
          exact hw1 a b (by rw [Fin.lt_iff_val_lt_val] at hli ⊢; simp at hli; omega)
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        rw [hent]
        rcases a with a | a
        · simp
        · simp [hw2 a]
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        obtain ⟨b, rfl⟩ := (stdSum h).surjective l
        rw [hent, one_std]
        rcases b with b | b
        · rcases a with a | a <;> simp [Matrix.one_apply]
        · simp at hl
    refine ⟨hmem, ?_⟩
    rw [derChar_val]
    show _ = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter (fun p : Fin t × Fin t => (p.2 : ℕ) = p.1 + 1),
      (w : Matrix (Fin t) (Fin t) k) p.1 p.2))
    congr 2
    refine Finset.sum_bij' (fun q hq => (⟨(q.1 : ℕ) - n, ?_⟩, ⟨(q.2 : ℕ) - n, ?_⟩))
      (fun p _ => ((stdSum h (Sum.inr p.1)), (stdSum h (Sum.inr p.2)))) ?_ ?_ ?_ ?_ ?_
    · have := (Finset.mem_filter.1 hq).2; have := q.1.2; omega
    · have := (Finset.mem_filter.1 hq).2; have := q.2.2; omega
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro p hp
      have := (Finset.mem_filter.1 hp).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, stdSum_inr]
      omega
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      ext <;> simp <;> omega
    · intro p hp
      ext <;> simp
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      have e1 : q.1 = stdSum h (Sum.inr ⟨(q.1 : ℕ) - n, by have := q.1.2; omega⟩) := by ext; simp; omega
      have e2 : q.2 = stdSum h (Sum.inr ⟨(q.2 : ℕ) - n, by have := q.2.2; omega⟩) := by ext; simp; omega
      show (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) q.1 q.2 = _
      conv_lhs => rw [e1, e2]
      rw [hent]
      rfl
  ·
    intro u
    obtain ⟨hu1, hu2⟩ := (mem_unipB k).1 u.2.1
    have hcol := (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).1 u.2.2
    let D : Matrix (Fin t) (Fin t) k := fun x y =>
      ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr x)) (stdSum h (Sum.inr y))
    have hDl : ∀ x y, y < x → D x y = 0 := fun x y hxy =>
      hu1 _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; exact hxy)
    have hDd : ∀ x, D x x = 1 := fun x => hu2 _
    have hdet : D.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun x y hxy => hDl x y hxy)]
      simp [hDd]
    have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).2 (by rw [hdet]; exact isUnit_one)
    let Dg : GL (Fin t) k := hD.unit
    have hDg : Dg ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨hDl, hDd⟩
    let a : rightUnip k n t := ⟨(1, Dg), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hDg⟩⟩
    have hDinv : D * ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
      show ((Dg : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) * _ = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmemU : (u : GL (Fin N) k) * (emb₂ k (stdSum h) (1, Dg))⁻¹ ∈ unipRad k (two (stdSum h)) := by
      apply mem_of_inU h
      intro i l hil
      rw [← map_inv, Prod.inv_mk, inv_one, Units.val_mul, Matrix.mul_apply,
        ← (stdSum h).sum_comp, Fintype.sum_sum_type]
      obtain ⟨b, rfl⟩ := (stdSum h).surjective l
      have hent : ∀ c : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, Dg⁻¹) : Matrix (Fin N) (Fin N) k) (stdSum h c)
          (stdSum h b) = fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0
            ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) c b := fun c => by rw [emb_val]; rfl
      simp only [hent]
      rcases b with b | b
      · simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
          Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact hcol i _ (by simp)
      · obtain ⟨a', rfl⟩ := (stdSum h).surjective i
        rcases a' with a' | a'
        · exact absurd ⟨by simp [a'.2], by simp⟩ hil
        · simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
            Finset.sum_const_zero, zero_add]
          rw [one_std]
          have := congrFun (congrFun hDinv a') b
          rw [Matrix.mul_apply] at this
          simpa [Matrix.one_apply] using this
    exact ⟨⟨_, hmemU⟩, a, by simp [a]⟩

end CompanionTheory.RgGu.NR.DerEq

namespace CompanionTheory.RgGu.NR

open DerEq in
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `ψ n j V _ _ π`. Establish `hh : n + (j + 1) = n + j + 1` using `rfl`. Set `A : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1` to `Q k ψ j (resM k π)`. Set `B : V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum hh) π) (rightUnip k n (j + 1)) (rightWhit k ψ n (j + 1))` to `Q' k ψ hh π`. Establish `hAs : Function.Surjective A` using `Q_surj ψ j (resM k π)`.

Establish `hBs : Function.Surjective B` using `Q'_surj ψ hh π`. Establish `hA : LinearMap.ker A = LinearMap.ker B`. Establish `e1 : LinearMap.ker A = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n)` using `(ker_Q ψ j (resM k π)).trans (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + j) n V π)`. Rewrite using `[e1, ker_Q']`. Set `L` to `((LinearMap.quotKerEquivOfSurjective A hAs).symm.trans (Submodule.quotEquivOfEq _ _ hA)).trans (LinearMap.quotKerEquivOfSurjective B hBs)`.

Establish `hL : ∀ v, L (A v) = B v`. Introduce `v`. Establish `e0 : (LinearMap.quotKerEquivOfSurjective A hAs).symm (A v) = Submodule.Quotient.mk v` using `(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk A hAs v).symm`. Simplify using `only [L, LinearEquiv.trans_apply, e0, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Use `⟨.mk L (fun g => ?_)⟩` and prove the remaining obligations.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hAs x`. Establish `e1 : A (π ((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) v) = derivM k ψ j (resM k π) g (A v)` using `Q_equiv ψ j (resM k π) g v`. Establish `e2 : B (π (emb₂ k (stdSum hh) (g, 1)) v) = derRep k ψ hh π g (B v)` using `Q'_equiv ψ hh π g v`. Use `show L (derivM k ψ j (resM k π) g (A v)) = derRep k ψ hh π g (L (A v))`.

Rewrite using `[hL, ← e2, ← e1, hL, E_eq g]`.
-/
theorem derEquiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    DerEquiv k := by
  intro ψ n j V _ _ π
  have hh : n + (j + 1) = n + j + 1 := rfl
  let A : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1 := Q k ψ j (resM k π)
  let B : V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum hh) π) (rightUnip k n (j + 1)) (rightWhit k ψ n (j + 1)) := Q' k ψ hh π
  have hAs : Function.Surjective A := Q_surj ψ j (resM k π)
  have hBs : Function.Surjective B := Q'_surj ψ hh π
  have hA : LinearMap.ker A = LinearMap.ker B := by
    have e1 : LinearMap.ker A = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
      (ker_Q ψ j (resM k π)).trans (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + j) n V π)
    rw [e1, ker_Q']
  let L := ((LinearMap.quotKerEquivOfSurjective A hAs).symm.trans (Submodule.quotEquivOfEq _ _ hA)).trans
    (LinearMap.quotKerEquivOfSurjective B hBs)
  have hL : ∀ v, L (A v) = B v := by
    intro v
    have e0 : (LinearMap.quotKerEquivOfSurjective A hAs).symm (A v) = Submodule.Quotient.mk v :=
      (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk A hAs v).symm
    simp only [L, LinearEquiv.trans_apply, e0, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨.mk L (fun g => ?_)⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := hAs x
  have e1 : A (π ((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) v) = derivM k ψ j (resM k π) g (A v) :=
    Q_equiv ψ j (resM k π) g v
  have e2 : B (π (emb₂ k (stdSum hh) (g, 1)) v) = derRep k ψ hh π g (B v) := Q'_equiv ψ hh π g v
  show L (derivM k ψ j (resM k π) g (A v)) = derRep k ψ hh π g (L (A v))
  rw [hL, ← e2, ← e1, hL, E_eq g]

end CompanionTheory.RgGu.NR
