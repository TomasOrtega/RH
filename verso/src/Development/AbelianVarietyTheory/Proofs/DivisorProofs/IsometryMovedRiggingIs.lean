import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.TriMove

variable {D : D7} {S S' : HSp D}

/- English proof (translation)
Substitute `h` using the available equality. Use extensionality with `i j`. Simplify using `[rdx, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
theorem rdx_conj_diag {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    (rdx (K := ℂ) h)ᴴ * diagonal d * rdx (K := ℂ) h = diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp [rdx, Matrix.one_apply, Matrix.diagonal_apply]

/- English proof (translation)
Substitute `h` using the available equality. Use extensionality with `i j`. Simplify using `only [rdx, finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.mul_one, Matrix.one_mul, Function.comp_id]`.
-/
theorem diag_rdx {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    diagonal d * rdx (K := ℂ) h = rdx (K := ℂ) h * diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp only [rdx, finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.mul_one, Matrix.one_mul,
    Function.comp_id]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[rdi, Matrix.one_apply]`.
-/
theorem rdi_mulVec {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (v : Fin m → K) (i : Fin n) :
    (rdi (K := K) h *ᵥ v) i = v ((finCongr h).symm i) := by
  subst h
  simp [rdi, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem cT_sig_eq (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := by
  ext i j
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩ show I.Q *ᵥ (I.P *ᵥ u) ∈ Λ`. Rewrite using `[Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]` and apply the resulting hypothesis. Introduce `hy`. Use `⟨I.Q *ᵥ y, hy, ?_⟩` and prove the remaining obligations.

Use `show I.P *ᵥ (I.Q *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]`.
-/
theorem mem_latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (y : Fin S'.rank → D.host.E) :
    y ∈ latMove I Λ ↔ I.Q *ᵥ y ∈ Λ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show I.Q *ᵥ (I.P *ᵥ u) ∈ Λ
    rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  · intro hy
    refine ⟨I.Q *ᵥ y, hy, ?_⟩
    show I.P *ᵥ (I.Q *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]

/- English proof (translation)
Simplify using `[dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem sumForm_eq (G : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `hg : I.Pᴴ * S'.gram * I.P = S.gram` using `by rw [← cT_sig_eq]; exact I.gram`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]`.
-/
theorem form_move (I : IsoMat S S') (x y : Fin S.rank → D.host.E) :
    star (I.P *ᵥ x) ⬝ᵥ (S'.gram *ᵥ (I.P *ᵥ y)) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  have hg : I.Pᴴ * S'.gram * I.P = S.gram := by rw [← cT_sig_eq]; exact I.gram
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x0, hx0, rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨M *ᵥ x0, hM x0 hx0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Consider the case `zero => rw [mulVec_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [mulVec_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `e : (M.map (Formalism.UG.inclE (F` using `F) R)) *ᵥ (a • x) = a • ((M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x) := by`. Rewrite using `[Subring.smul_def, Subring.smul_def, mulVec_smul]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem latS_mulVec_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (T : Subring (TensorProduct F E R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ Formalism.UG.latS (F := F) R T Λ', (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x ∈ Formalism.UG.latS (F := F) R T Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `latS_mulVec_mem _ _ I.Q (latMove I Λ) Λ (fun y hy => (mem_latMove I Λ y).1 hy) x hx`. Introduce `hx`. Establish `h` using `latS_mulVec_mem _ _ I.P Λ (latMove I Λ) (fun y hy => (mem_latMove I Λ _).2 (by rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec])) _ hx`.

Establish `e : I.P.map (Formalism.UG.inclE _) *ᵥ (fQ I *ᵥ x) = x` using `by show fP I *ᵥ (fQ I *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, fP_fQ, Matrix.one_mulVec]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem mem_hatL_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : Fin S'.rank → Lev.EAf D) :
    x ∈ Formalism.L2.Herm.hatL (latMove I Λ) ↔ fQ I *ᵥ x ∈ Formalism.L2.Herm.hatL Λ := by
  constructor
  · intro hx
    exact latS_mulVec_mem _ _ I.Q (latMove I Λ) Λ (fun y hy => (mem_latMove I Λ y).1 hy) x hx
  · intro hx
    have h := latS_mulVec_mem _ _ I.P Λ (latMove I Λ)
      (fun y hy => (mem_latMove I Λ _).2 (by rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec])) _ hx
    have e : I.P.map (Formalism.UG.inclE _) *ᵥ (fQ I *ᵥ x) = x := by
      show fP I *ᵥ (fQ I *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, fP_fQ, Matrix.one_mulVec]
    rwa [e] at h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frame_inv (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) :
    ((betaMove I β)⁻¹ : GL (Fin S'.rank) (Lev.EAf D)).val =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) I.rank_eq) (β⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) (fQ I) := rfl

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_hatL_move, hβ, frame_inv]`. Simplify using `only [← Matrix.mulVec_mulVec, rdi_mulVec]`. Conclude with `⟨fun H i => H _, fun H j => by simpa using H (finCongr I.rank_eq j)⟩`.
-/
theorem frame_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    Formalism.L2.DIV.IsFrame (F := D.host.F) (E := D.host.E) (n := S'.rank) (betaMove I β) (latMove I Λ) := by
  intro x
  rw [mem_hatL_move, hβ, frame_inv]
  simp only [← Matrix.mulVec_mulVec, rdi_mulVec]
  exact ⟨fun H i => H _, fun H j => by simpa using H (finCongr I.rank_eq j)⟩

/- English proof (translation)
Establish `hPQ : ∀ y, I.P *ᵥ (I.Q *ᵥ y) = y` using `fun y => by rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]`. Establish `hQP : ∀ y, I.Q *ᵥ (I.P *ᵥ y) = y` using `fun y => by rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]`. Take `⟨hl, hd⟩` from `h`. Use `⟨⟨hl.fg.map _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[latMove, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image (Matrix.mulVecLin I.P), hl.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `fun y => ⟨I.Q *ᵥ y, hPQ y⟩`. Introduce `y`. Rewrite using `[mem_latMove, hd (I.Q *ᵥ y)]`. Simplify using `only [sumForm_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `H x hx`. Rewrite `hx` using `[mem_latMove]`. Take `⟨b, hb⟩` from `H _ hx`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, ← form_move I, hPQ, hPQ]`.

Introduce `H x hx`. Establish `hx' : I.P *ᵥ x ∈ latMove I Λ` using `by rw [mem_latMove, hQP]; exact hx`. Take `⟨b, hb⟩` from `H _ hx'`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, ← form_move I, hPQ]`.
-/
theorem selfDual_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (h : IsSelfDualC S Λ) :
    IsSelfDualC S' (latMove I Λ) := by
  have hPQ : ∀ y, I.P *ᵥ (I.Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]
  have hQP : ∀ y, I.Q *ᵥ (I.P *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  obtain ⟨hl, hd⟩ := h
  refine ⟨⟨hl.fg.map _, ?_⟩, ?_⟩
  · rw [latMove, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image (Matrix.mulVecLin I.P),
      hl.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨I.Q *ᵥ y, hPQ y⟩
  · intro y
    rw [mem_latMove, hd (I.Q *ᵥ y)]
    simp only [sumForm_eq]
    constructor
    · intro H x hx
      rw [mem_latMove] at hx
      obtain ⟨b, hb⟩ := H _ hx
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ, hPQ]
    · intro H x hx
      have hx' : I.P *ᵥ x ∈ latMove I Λ := by rw [mem_latMove, hQP]; exact hx
      obtain ⟨b, hb⟩ := H _ hx'
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hs`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul, conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e : G' * (a * s * b) = bᴴ * (G * s) * b`. Rewrite using `[← hb]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc b a, hba, Matrix.one_mul]`. Rewrite using `[e]`.

Use `h3.conjTranspose_mul_mul_same fun u v huv => ?_` and prove the remaining obligations. Use `congrArg (a *ᵥ ·) huv` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hab]`.
-/
theorem cartan_conj {m n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hab : a * b = 1) (hba : b * a = 1) (hb : bᴴ * G * b = G') (ha : aᴴ * G' * a = G)
    {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCartanInv G' (a * s * b) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · calc a * s * b * (a * s * b) = a * (s * (b * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hba, Matrix.mul_one, h1, Matrix.mul_one, hab]
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (sᴴ * aᴴ) * G' * (a * s * b) = bᴴ * (sᴴ * (aᴴ * G' * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [ha, h2, hb]
  · have e : G' * (a * s * b) = bᴴ * (G * s) * b := by
      rw [← hb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
    rw [e]
    refine h3.conjTranspose_mul_mul_same fun u v huv => ?_
    have := congrArg (a *ᵥ ·) huv
    simpa [Matrix.mulVec_mulVec, hab] using this

/- English proof (translation)
Take `⟨ε, hε, hd, hsB⟩` from `hs`. Use `⟨fun i => ε ((finCongr h).symm i), fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hε ((finCongr h).symm i)`. Rewrite using `[conjTranspose_mul, conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc b a, hba, Matrix.one_mul, ← Matrix.mul_assoc s B, hsB, Matrix.mul_assoc B, diag_rdx h]`. Both sides reduce to the same expression.
-/
theorem onb_conj {m n : ℕ} (h : n = m) {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ}
    {a : Matrix (Fin m) (Fin n) ℂ} {b : Matrix (Fin n) (Fin m) ℂ} (hba : b * a = 1) (ha : aᴴ * G' * a = G)
    {s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (hs : IsONBasis G s B p) :
    IsONBasis G' (a * s * b) (a * B * rdx (K := ℂ) h) p := by
  obtain ⟨ε, hε, hd, hsB⟩ := hs
  refine ⟨fun i => ε ((finCongr h).symm i), fun i => ?_, ?_, ?_⟩
  · simpa using hε ((finCongr h).symm i)
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (rdx (K := ℂ) h)ᴴ * (Bᴴ * aᴴ) * G' * (a * B * rdx (K := ℂ) h)
        = (rdx (K := ℂ) h)ᴴ * (Bᴴ * (aᴴ * G' * a) * B) * rdx (K := ℂ) h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hd]; exact rdx_conj_diag h _
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul, ← Matrix.mul_assoc s B, hsB, Matrix.mul_assoc B, diag_rdx h]
    rfl

/- English proof (translation)
Unfold `Rig.Is at hr ⊢`. Take `⟨h1, h2, h3⟩` from `hr`. Use `⟨selfDual_move I r.Λ h1, frame_move I r.Λ r.β h2, fun τ => ?_⟩` and prove the remaining obligations. Establish `hG' : (I.qT τ)ᴴ * gramAt D S τ * I.qT τ = gramAt D S' τ` using `I.qT_gram τ`. Establish `hG : (I.pT τ)ᴴ * gramAt D S' τ * I.pT τ = gramAt D S τ` using `I.symm.qT_gram τ`.

Take `⟨hc, p, hp⟩` from `h3 τ`. Conclude with `⟨cartan_conj (I.pT_qT τ) (I.qT_pT τ) hG' hG hc, p, onb_conj I.rank_eq (I.qT_pT τ) hG hp⟩`.
-/
theorem rigMove_is {S S' : HSp D} (I : IsoMat S S') (r : Rig S) (hr : r.Is) : (rigMove I r).Is := by
  unfold Rig.Is at hr ⊢
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨selfDual_move I r.Λ h1, frame_move I r.Λ r.β h2, fun τ => ?_⟩
  have hG' : (I.qT τ)ᴴ * gramAt D S τ * I.qT τ = gramAt D S' τ := I.qT_gram τ
  have hG : (I.pT τ)ᴴ * gramAt D S' τ * I.pT τ = gramAt D S τ := I.symm.qT_gram τ
  obtain ⟨hc, p, hp⟩ := h3 τ
  exact ⟨cartan_conj (I.pT_qT τ) (I.qT_pT τ) hG' hG hc, p, onb_conj I.rank_eq (I.qT_pT τ) hG hp⟩

end GlobalTheory.TriMove

end
