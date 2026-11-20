import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable (D : D7) (u : D.what₂.Word)

def BwIncl : Prop :=
  ∀ w, OverT D u w →
    ∀ i, i ≤ D.R.m → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
      ∀ x ∈ (D.fm u).Bw i w v,
        ((D.mem u).A.T : D.what₂.LL) ^ (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • x ∈ (D.fm u).S i w

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem emb_tpow_smul (i n : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i (((D.mem u).A.T : D.what₂.LL) ^ n • x) = tpow D u n • (D.fm u).emb i x := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem lattice_inclusion_iff : WeightLatticeInclusion D u ↔ BwIncl D u := by
  constructor
  · intro h w hw i hi hs v hv x hx
    obtain ⟨y, hy, he⟩ := h w hw i hi hs v hv x hx
    have hxy : ((D.mem u).A.T : D.what₂.LL) ^ (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • x = y := by
      apply (D.fm u).emb_inj i
      rw [emb_tpow_smul]
      exact he.symm
    rw [hxy]
    exact hy
  · intro h w hw i hi hs v hv x hx
    exact ⟨_, h w hw i hi hs v hv x hx, emb_tpow_smul D u _ _ x⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem lattice_inclusion_family_of (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → BwIncl D u) : WeightLatticeInclusionFamily :=
  fun D u h1 h2 => (lattice_inclusion_iff D u).2 (h D u h1 h2)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem eval_subP {ι : Type} [Fintype ι] {n : ℕ} (N Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (N x.1 * Z x.1) x.2.1 x.2.2) P =
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => Z x.1 x.2.1 x.2.2) (Formalism.L2.Forms.subP N P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.L2.Forms.subP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, MvPolynomial.eval_X, hp]
    simp [Formalism.L2.Forms.subP, Matrix.mul_apply, MvPolynomial.eval_sum]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fnOf_mul {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (N M : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.fnOf G s (fun τ => N τ * M τ) P =
      Formalism.L2.Forms.fnOf G s M (MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N P) := by
  funext y
  simp only [Formalism.L2.Forms.fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C]
  have h := eval_subP N (fun τ => M τ * y.1 τ) P
  simp only [← Matrix.mul_assoc] at h
  rw [h]
  simp only [Matrix.mul_assoc (N _), Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
