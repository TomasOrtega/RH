import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

variable {E : Type} [Field E] {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}

def autOf (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g.val.submatrix e.symm e.symm)) (Matrix.toLin' ((g⁻¹).val.submatrix e.symm e.symm))
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv, Matrix.toLin'_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem autOf_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    autOf e g v = (g.val.submatrix e.symm e.symm).mulVec v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem autOf_inv_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    (autOf e g)⁻¹ v = ((g⁻¹).val.submatrix e.symm e.symm).mulVec v := rfl

/- English proof (translation)
Break down `hm : e.symm l with a | i` into its components or cases. Establish `h1 : l = e (Sum.inl a)` using `by rw [← hm]; simp`. Use `eX_lt e hcc he a` as an intermediate fact. Rewrite `this` using `[← h1]`. Simplify using `[lev, this]`.

Establish `h1 : l = e (Sum.inr i)` using `by rw [← hm]; simp`. Use `he i` as an intermediate fact. Rewrite `this` using `[← h1]`. Simplify using `[lev, this]`.
-/
theorem lev_symm (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (l : Fin (M + c')) : lev (n := A) (c := c) 1 (e.symm l) = if l.val < M then 1 else l.val - M + 1 := by
  rcases hm : e.symm l with a | i
  · have h1 : l = e (Sum.inl a) := by rw [← hm]; simp
    have := eX_lt e hcc he a
    rw [← h1] at this
    simp [lev, this]
  · have h1 : l = e (Sum.inr i) := by rw [← hm]; simp
    have := he i
    rw [← h1] at this
    simp [lev, this]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]`. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]`. Introduce `j _ hj`. Distinguish the cases in `h0 : v j = 0`.

Rewrite using `[h0, mul_zero]`. Rewrite using `[hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_fix (e : A ⊕ Fin c ≃ Fin (M + c')) (m : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E)
    (hm : ∀ r s, lev 1 s ≤ lev 1 r → m r s = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E) r s) (v : Fin (M + c') → E)
    (l : Fin (M + c')) (hv : ∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) :
    (m.submatrix e.symm e.symm).mulVec v l = v l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single l]
  · rw [hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    by_cases h0 : v j = 0
    · rw [h0, mul_zero]
    · rw [hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]
  · simp

/- English proof (translation)
Establish `hL` using `lev_symm e hcc he`. Establish `key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')), (∀ j, v j ≠ 0 → lev (n` using `A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) → (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv => mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv`. Establish `hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E), (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r`. Introduce `g hg r hr`. Use `⟨fun i v hv => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations.

Introduce `l hl`. Simplify using `only [Set.mem_setOf_eq, not_lt] at hl`. Rewrite using `[hr, key g hg v l ?_]`. Conclude with `hv l (by simpa using hl)`. Introduce `j hj`.

Establish `: j.val < M + i`. Assume the negation of the conclusion as `h`. Conclude with `hj (hv j (by simpa using h))`. Apply the tactic sequence `rw [hL, hL]; split_ifs <;> omega`. Use function extensionality and compare the values at `l`.

Rewrite using `[hr, key g hg _ l]`. Introduce `j hj`. Establish `: j.val = M`. Assume the negation of the conclusion as `h; exact hj (by simp [Loc.eN, h])`. Apply the tactic sequence `rw [hL, hL]; split_ifs <;> omega`.

Introduce `l hl`. Simplify using `only [Set.mem_setOf_eq, not_lt] at hl`. Rewrite using `[Pi.sub_apply, hr, key g hg _ l, sub_self]`. Introduce `j hj`. Establish `: j.val = M + i`.

Assume the negation of the conclusion as `h; exact hj (by simp [Loc.eN, h])`. Apply the tactic sequence `rw [hL, hL]; split_ifs <;> omega`. Use `⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Rewrite using `[autOf_apply, key g hg _ l]`.

Introduce `j hj`. Establish `: j.val < M`. Assume the negation of the conclusion as `h`. Conclude with `hj (by simp [Loc.inX, h])`. Apply the tactic sequence `rw [hL, hL]; split_ifs <;> omega`.
-/
theorem mem_normOneIdeles (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (g : GL (A ⊕ Fin c) E) (hg : g ∈ N E A c 1) : autOf e g ∈ Loc.N1 E M c' := by
  have hL := lev_symm e hcc he
  have key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')),
      (∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) →
      (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv =>
    mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv
  have hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E),
      (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r := by
    intro g hg r hr
    refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [hr, key g hg v l ?_]
      · exact hv l (by simpa using hl)
      · intro j hj
        have : j.val < M + i := by
          by_contra h
          exact hj (hv j (by simpa using h))
        rw [hL, hL]; split_ifs <;> omega
    · funext l
      rw [hr, key g hg _ l]
      intro j hj
      have : j.val = M := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [Pi.sub_apply, hr, key g hg _ l, sub_self]
      intro j hj
      have : j.val = M + i := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
  refine ⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩
  funext l
  rw [autOf_apply, key g hg _ l]
  intro j hj
  have : j.val < M := by
    by_contra h
    exact hj (by simp [Loc.inX, h])
  rw [hL, hL]; split_ifs <;> omega

/- English proof (translation)
Rewrite using `[locHom_val]`. Use extensionality with `i j`. Simplify using `[GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]`.
-/
theorem locHom_autOf {k : Type} [Field k] (ι : E →+* k) (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) :
    (locHom ι e (autOf e g)).val = g.val.map ι := by
  rw [locHom_val]
  ext i j
  simp [GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]

end GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

namespace GlobalTheory.VolBridge
open NormOneIdeleAutomorphisms

/- English proof (translation)
Introduce `E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV`. Set `f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k` to `fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)`. Establish `hf : Continuous f` using `continuous_subtype_val.comp (VolN.continuous_mkNel 1)`. Establish `hW : IsOpen (f ⁻¹' V)` using `hV.preimage hf`. Establish `h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V` using `by show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V`.

Rewrite using `[VolN.mkNel_co]`. Conclude with `huV`. Establish `hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k))` using `DenseRange.piMap fun _ => hι`. Take `⟨b, hb⟩` from `hD.exists_mem_open hW ⟨_, h0⟩`. Use `⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩` and prove the remaining obligations.

Establish `: locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[locHom_autOf]`. Use `show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val`. Rewrite using `[VolN.val_mkNel, VolN.val_mkNel]`.

Use extensionality with `r s`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, map_add, VolN.ext0, Matrix.of_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Conclude with `hb`.
-/
theorem exists_N1_local_hom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV
  let f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k := fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)
  have hf : Continuous f := continuous_subtype_val.comp (VolN.continuous_mkNel 1)
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V := by
    show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V
    rw [VolN.mkNel_co]; exact huV
  have hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨b, hb⟩ := hD.exists_mem_open hW ⟨_, h0⟩
  refine ⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩
  have : locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b) := by
    apply Units.ext
    rw [locHom_autOf]
    show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val
    rw [VolN.val_mkNel, VolN.val_mkNel]
    ext r s
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, VolN.ext0, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]; exact hb

end GlobalTheory.VolBridge
