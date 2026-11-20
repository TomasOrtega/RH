import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

noncomputable section

namespace GlobalTheory.SpanBlockAction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section

variable {O : Type} [CommRing O] {n r t : ℕ}

def ActsAs (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (M : Matrix (Fin n) (Fin n) O) (P : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Prop :=
  ∀ u, e ((M.map (toFr O)).mulVec u) =
    ((P.map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (d c) * (e u).2 c)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[smul_eq_mul]`.
-/
theorem map_smul_toFr {k : ℕ} (c : O) (M : Matrix (Fin k) (Fin k) O) :
    (c • M).map (toFr O) = toFr O c • M.map (toFr O) := by
  ext i j
  simp [smul_eq_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.sum_apply]`.
-/
theorem map_sum_toFr {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) O) :
    (∑ i, M i).map (toFr O) = ∑ i, (M i).map (toFr O) := by
  ext i j
  simp [Matrix.sum_apply]

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
private theorem sum_mulVec_eq {K : Type} [CommRing K] {k m : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (∑ i, A i).mulVec v = ∑ i, (A i).mulVec v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
private theorem smul_mulVec_eq' {K : Type} [CommRing K] {k : ℕ} (a : K) (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (a • A).mulVec v = a • A.mulVec v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Unfold `ActsAs at h ⊢`. Introduce `u`. Rewrite using `[map_sum_toFr, map_sum_toFr]`. Simplify using `only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Simplify using `[Prod.fst_sum]`. Use function extensionality and compare the values at `j`. Simplify using `[Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.
-/
theorem actsAs_sum
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    {m : ℕ} (c : Fin m → O) (M : Fin m → Matrix (Fin n) (Fin n) O) (P : Fin m → Matrix (Fin r) (Fin r) O)
    (d : Fin m → Fin t → O) (h : ∀ k, ActsAs e (M k) (P k) (d k)) :
    ActsAs e (∑ k, c k • M k) (∑ k, c k • P k) (fun j => ∑ k, c k * d k j) := by
  unfold ActsAs at h ⊢
  intro u
  rw [map_sum_toFr, map_sum_toFr]
  simp only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Algebra.smul_def]

/- English proof (translation)
Establish `hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v`. Introduce `v`. Establish `h1` using `h (e.symm (v, 0))`. Establish `h2` using `h' (e.symm (v, 0))`. Rewrite `h2` using `[h1]`.

Simplify using `using congrArg Prod.fst h2`. Establish `hm : P.map (toFr O) = P'.map (toFr O)`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Conclude with `LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v`. Use extensionality with `i j`.

Apply `IsFractionRing.injective O (FractionRing O)` to reduce the goal to its premises. Use `congrFun (congrFun hm i) j` as an intermediate fact. Simplify `this` using `[toFr]`.
-/
theorem ActsAs.unique
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    {M : Matrix (Fin n) (Fin n) O} {P P' : Matrix (Fin r) (Fin r) O} {d d' : Fin t → O}
    (h : ActsAs e M P d) (h' : ActsAs e M P' d') : P = P' := by
  have hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v := by
    intro v
    have h1 := h (e.symm (v, 0))
    have h2 := h' (e.symm (v, 0))
    rw [h1] at h2
    simpa using congrArg Prod.fst h2
  have hm : P.map (toFr O) = P'.map (toFr O) := by
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v
  ext i j
  apply IsFractionRing.injective O (FractionRing O)
  have := congrFun (congrFun hm i) j
  simpa [toFr] using this

end

/- English proof (translation)
Unfold `ActsAs`. Introduce `u`. Simplify `h g u` using `[overK, matRep, mapM, mat]`.
-/
theorem actsAs_mat {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    {σ : Γ →* GL (Fin n) O} {ρ : Γ →* GL (Fin r) O} {χ : ℕ → (Γ →* Oˣ)}
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    (h : IsDecomp (t := t) σ ρ χ e) (g : Γ) :
    ActsAs e (mat σ g) (mat ρ g) (fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)) := by
  unfold ActsAs
  intro u
  simpa [overK, matRep, mapM, mat] using h g u

/- English proof (translation)
Establish `hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))), ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2`. Introduce `M hM`. Take `⟨m, c, g, rfl⟩` from `Submodule.mem_span_set'.mp hM`. Establish `hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O)` using `fun k => (g k).2`. Use `choose γ hγ using hg`.

Use `⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩` and prove the remaining obligations. Use `actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k)) (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))` as an intermediate fact. Simplify `this` using `only [hγ]`. Use `⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2 then h.choose.1 else 0, fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2 then h.choose.2 j else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha u`.

Establish `hex` using `hact (a π) (eval_mem_span ha π)`. Simplify using `only [dif_pos hex]`. Conclude with `hex.choose_spec u`. Introduce `P`. Establish `hP : P ∈ Submodule.span O (Set.range (mat ρ))` using `hspan ▸ Submodule.mem_top`.

Take `⟨m, c, g, hsum⟩` from `Submodule.mem_span_set'.mp hP`. Establish `hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O)` using `fun k => (g k).2`. Use `choose γ hγ using hg`. Use `⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))`.

Establish `hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k)`. Simplify using `[Finset.sum_apply]`. Establish `hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k)) (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O))`. Rewrite using `[hev]`. Conclude with `actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k)) (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))`.

Establish `hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2` using `⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩`. Simplify using `only [dif_pos hex]`. Rewrite using `[ActsAs.unique hex.choose_spec hA, ← hsum]`. Simplify using `only [hγ]`.
-/
theorem exists_block_action {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ))
    (π : X)
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (hspan : Submodule.span O (Set.range (mat ρ)) = ⊤) (hdec : IsDecomp (t := t) (rep π) ρ χ e) :
    ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O)
      (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O),
      (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) =
        (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧
      ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  classical
  have hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))),
      ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2 := by
    intro M hM
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.mp hM
    have hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩
    have := actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
      (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
    simpa only [hγ] using this
  refine ⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.1 else 0,
    fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.2 j else 0, ?_, ?_⟩
  · intro a ha u
    have hex := hact (a π) (eval_mem_span ha π)
    simp only [dif_pos hex]
    exact hex.choose_spec u
  · intro P
    have hP : P ∈ Submodule.span O (Set.range (mat ρ)) := hspan ▸ Submodule.mem_top
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hP
    have hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩
    · exact inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))
    · have hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k) := by
        simp [Finset.sum_apply]
      have hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k))
          (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) := by
        rw [hev]
        exact actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
          (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
      have hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O),
          ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2 :=
        ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩
      simp only [dif_pos hex]
      rw [ActsAs.unique hex.choose_spec hA, ← hsum]
      simp only [hγ]

end GlobalTheory.SpanBlockAction

end
