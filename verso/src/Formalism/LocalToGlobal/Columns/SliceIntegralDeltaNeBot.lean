import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

open Module NumberField ComplexOrder IsDedekindDomain
open scoped Matrix Kronecker

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.DIV Formalism.LFunctionChainParameters.LLcv

namespace T2

abbrev piL {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (β : Type) (L : Submodule R V) :
    Submodule R (β → V) := Submodule.pi Set.univ fun _ => L

def kronMap (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] {α β : Type} [Fintype β] (t : Matrix β α ℤ) :
    (β → M) →ₗ[R] (α → M) :=
  LinearMap.pi fun a => ∑ b, t b a • LinearMap.proj b

def piKron {ι : Type} [Fintype ι] {α : ι → Type} {R : Type} [CommRing R] (M : ∀ i, Matrix (α i) (α i) R) :
    Matrix (∀ i, α i) (∀ i, α i) R :=
  Matrix.of fun a b => ∏ i, M i (a i) (b i)

def piKronOn {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, DecidableEq (α i)] {R : Type} [CommRing R]
    (M : ∀ i, Matrix (α i) (α i) R) (s : Finset ι) : Matrix (∀ i, α i) (∀ i, α i) R :=
  Matrix.of fun a b => (∏ i ∈ s, M i (a i) (b i)) * if ∀ i, i ∉ s → a i = b i then 1 else 0

section

variable {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, DecidableEq (G i)]

abbrev SzIdx : Type := ∀ i, {g : G i // g ≠ 1}

def szVec : Matrix (SzIdx G) (∀ i, G i) ℤ :=
  Matrix.of fun b a => ∏ i, ((if a i = (b i : G i) then 1 else 0) - (if a i = 1 then 1 else 0))

def szGram1 (i : ι) : Matrix {g : G i // g ≠ 1} {g : G i // g ≠ 1} ℤ :=
  Matrix.of fun b c => (if b = c then 1 else 0) + 1

def szGram : Matrix (SzIdx G) (SzIdx G) ℤ := piKron (szGram1 G)

def SzIdx.pt {G : ι → Type} [∀ i, CommGroup (G i)] (b : SzIdx G) : ∀ i, G i := fun i => (b i : G i)

end

end T2

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}
  {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D]

@[reducible] def Slice.WH (σ : S.Slice A) (h : S.Ok) : HLat K :=
  (S.restr σ.T).toH (S.restr_ok h σ.T) (S.restr σ.T).intDel

def Slice.kron (σ : S.Slice A) {β : Type} [Fintype β] (t : Matrix β A ℤ) :
    (β → (S.restr σ.T).EqFun) →ₗ[K] S.EqFun :=
  σ.split.symm.toLinearMap ∘ₗ T2.kronMap K _ t

end GSD

namespace T2

section Index

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

variable {β : Type} [Fintype β]

/- English proof (translation)
Set `f : (β → A') →ₗ[R] (β → V)` to `LinearMap.pi fun b => A'.subtype ∘ₗ LinearMap.proj b`. Establish `hr : f.toAddMonoidHom.range = (piL β A').toAddSubgroup`. Use extensionality with `F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨G, rfl⟩`.

Introduce `b _`. Conclude with `(G b).2`. Introduce `hF`. Conclude with `⟨fun b => ⟨F b, hF b (Set.mem_univ b)⟩, rfl⟩`. Establish `hc : (piL β A).toAddSubgroup.comap f.toAddMonoidHom = (Submodule.pi Set.univ fun _ : β => A.comap A'.subtype).toAddSubgroup`.

Use extensionality with `F`. Both sides reduce to the same expression. Rewrite using `[← hr, ← AddSubgroup.index_comap, hc]`. Use `show Nat.card ((β → A') ⧸ Submodule.pi Set.univ fun _ : β => A.comap A'.subtype) = _`. Rewrite using `[Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ]`.

Both sides reduce to the same expression.
-/
theorem relIndex_piL (A A' : Submodule R V) :
    (piL β A).toAddSubgroup.relIndex (piL β A').toAddSubgroup =
      (A.toAddSubgroup.relIndex A'.toAddSubgroup) ^ Fintype.card β := by
  classical
  let f : (β → A') →ₗ[R] (β → V) := LinearMap.pi fun b => A'.subtype ∘ₗ LinearMap.proj b
  have hr : f.toAddMonoidHom.range = (piL β A').toAddSubgroup := by
    ext F
    constructor
    · rintro ⟨G, rfl⟩
      intro b _
      exact (G b).2
    · intro hF
      exact ⟨fun b => ⟨F b, hF b (Set.mem_univ b)⟩, rfl⟩
  have hc : (piL β A).toAddSubgroup.comap f.toAddMonoidHom =
      (Submodule.pi Set.univ fun _ : β => A.comap A'.subtype).toAddSubgroup := by
    ext F
    rfl
  rw [← hr, ← AddSubgroup.index_comap, hc]
  show Nat.card ((β → A') ⧸ Submodule.pi Set.univ fun _ : β => A.comap A'.subtype) = _
  rw [Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[← Finset.univ_sum_single x]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Establish `hb : x b ∈ Submodule.span R (Set.range e)` using `hx b (Set.mem_univ b)`.

Establish `hle : Submodule.map (LinearMap.single R (fun _ : β => V) b) (Submodule.span R (Set.range e)) ≤ Submodule.span R (Set.range fun p : β × γ => (Pi.single p.1 (e p.2) : β → V))`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `Submodule.subset_span ⟨(b, g), rfl⟩`. Conclude with `hle (Submodule.mem_map.mpr ⟨x b, hb, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨b, g⟩, rfl⟩`. Simplify using `only [piL, SetLike.mem_coe, Submodule.mem_pi]`. Introduce `i _`. Distinguish the cases in `h : i = b`.

Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `Submodule.subset_span (Set.mem_range_self g)`. Simplify using `[h]`.
-/
theorem piL_span [DecidableEq β] {γ : Type} (e : γ → V) :
    piL β (Submodule.span R (Set.range e)) =
      Submodule.span R (Set.range fun p : β × γ => (Pi.single p.1 (e p.2) : β → V)) := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun b _ => ?_
    have hb : x b ∈ Submodule.span R (Set.range e) := hx b (Set.mem_univ b)
    have hle : Submodule.map (LinearMap.single R (fun _ : β => V) b) (Submodule.span R (Set.range e)) ≤
        Submodule.span R (Set.range fun p : β × γ => (Pi.single p.1 (e p.2) : β → V)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨(b, g), rfl⟩
    exact hle (Submodule.mem_map.mpr ⟨x b, hb, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨b, g⟩, rfl⟩
    simp only [piL, SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    by_cases h : i = b
    · subst h
      simp only [Pi.single_eq_same]
      exact Submodule.subset_span (Set.mem_range_self g)
    · simp [h]

end Index

section Slope

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

/- English proof (translation)
Establish `h1` using `(sizeMu K V ι b X hX L hL h0).2.1`. Establish `h2` using `(plLat K V ι b X hX L hL).2.2`. Rewrite using `[h1]`. Unfold `size`. Rewrite using `[Real.log_rpow h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mu_eq_log_ht {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (h0 : L ≠ ⊥) :
    muDef b X L = -Real.log (ht b X L) / ((nPl K : ℝ) * (rkK L : ℝ)) := by
  have h1 := (sizeMu K V ι b X hX L hL h0).2.1
  have h2 := (plLat K V ι b X hX L hL).2.2
  rw [h1]
  unfold size
  rw [Real.log_rpow h2]
  ring

/- English proof (translation)
Establish `: FiniteDimensional K Wh.V` using `Module.Finite.of_basis Wh.b`. Take `⟨w, e, he, heL, hsp⟩` from `covolume_exists K Wh.V Wh.L`. Take `⟨hrkW, hw, hdet, -, -⟩` from `log_covolume_slope_mu K Wh.V Wh.ι Wh.b Wh.X hW.1 w e Wh.L he hW.2.1 hW0 hsp`. Take `⟨hG1, hG2⟩` from `htGram K Wh.V Wh.ι Wh.b Wh.X hW.1 w e he`. Establish `heL' : Submodule.span (𝓞 K) (Set.range e) ≤ Wh.L` using `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact heL a)`.

Establish `hG3` using `hG2 Wh.L hW.2.1 heL' hrkW`. Establish `hspT : Submodule.span K (Set.range e) = ⊤` using `hsp ▸ hW.2.2`. Use `set n := Fintype.card β with hn`. Establish `hn0 : 0 < n` using `Fintype.card_pos`. Set `ε : Fin (n * w) ≃ β × Fin w` to `finProdFinEquiv.symm.trans ((Fintype.equivFin β).symm.prodCongr (Equiv.refl _))`.

Set `P : β × Fin w → (β → Wh.V)` to `fun p => Pi.single p.1 (e p.2)`. Set `E : Fin (n * w) → B.V` to `fun k => Ψ (P (ε k))`. Set `bW : Basis (Fin w) K Wh.V` to `Basis.mk he hspT.ge`. Set `bP : Basis (Σ _ : β, Fin w) K (β → Wh.V)` to `Pi.basis fun _ => bW`. Establish `hP : ∀ p, P p = bP ⟨p.1, p.2⟩`.

Introduce `p`. Simplify using `[P, bP, bW, Pi.basis_apply, Basis.mk_apply]`. Establish `hPli : LinearIndependent K P`. Establish `h1` using `bP.linearIndependent.comp (fun p : β × Fin w => (⟨p.1, p.2⟩ : Σ _ : β, Fin w)) (fun p q h => by`. Take `⟨p1, p2⟩` from `p`.

Take `⟨q1, q2⟩` from `q`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq] at h`. Conclude with `Prod.ext h.1 h.2)`. Establish `h2 : P = bP ∘ fun p : β × Fin w => (⟨p.1, p.2⟩ : Σ _ : β, Fin w)` using `funext hP`. Rewrite using `[h2]`.

Conclude with `h1`. Establish `hPsp : Submodule.span K (Set.range P) = ⊤`. Rewrite using `[eq_top_iff, ← bP.span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨⟨b, i⟩, rfl⟩`.

Conclude with `⟨(b, i), hP (b, i)⟩`. Establish `hEli : LinearIndependent K E` using `(hPli.map' Ψ (LinearMap.ker_eq_bot.2 hΨ)).comp ε ε.injective`. Establish `hrange : Set.range E = Ψ '' Set.range P`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨P (ε k), ⟨ε k, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨p, rfl⟩, rfl⟩`. Conclude with `⟨ε.symm p, by simp [E]⟩`. Use `set LN : Submodule (𝓞 K) B.V := (piL β Wh.L).map (Ψ.restrictScalars (𝓞 K)) with hLN`.

Establish `hspanE : Submodule.span (𝓞 K) (Set.range E) = (piL β (Submodule.span (𝓞 K) (Set.range e))).map (Ψ.restrictScalars (𝓞 K))`. Rewrite using `[piL_span, Submodule.map_span, hrange]`. Both sides reduce to the same expression. Establish `hEle : Submodule.span (𝓞 K) (Set.range E) ≤ LN`. Rewrite using `[hspanE]`.

Conclude with `Submodule.map_mono fun F hF b hb => heL' (hF b hb)`. Establish `hLNfg : LN.FG` using `(Submodule.fg_pi fun _ => hW.2.1).map _`. Establish `hnw : 0 < n * w` using `Nat.mul_pos hn0 hw`. Establish `hLN0 : LN ≠ ⊥`. Introduce `h0`.

Establish `h1 : E ⟨0, hnw⟩ ∈ LN` using `hEle (Submodule.subset_span ⟨_, rfl⟩)`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Conclude with `hEli.ne_zero _ h1`. Establish `hspK : Submodule.span K (LN : Set B.V) = Submodule.span K (Set.range E)`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, -, rfl⟩`. Establish `h1 : F ∈ Submodule.span K (Set.range P)` using `hPsp ▸ Submodule.mem_top`. Establish `h2` using `Submodule.mem_map_of_mem (f := Ψ) h1`. Rewrite `h2` using `[Submodule.map_span, ← hrange]`.

Conclude with `h2`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hEle (Submodule.subset_span ⟨k, rfl⟩)`. Take `⟨hrkN, -, -, -, -⟩` from `log_covolume_slope_mu K B.V B.ι B.b B.X hB (n * w) E LN hEli hLNfg hLN0 hspK`.

Take `⟨hH1, hH2⟩` from `htGram K B.V B.ι B.b B.X hB (n * w) E hEli`. Establish `hH3` using `hH2 LN hLNfg hEle hrkN`. Establish `hidx : (Submodule.span (𝓞 K) (Set.range E)).toAddSubgroup.relIndex LN.toAddSubgroup = ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex Wh.L.toAddSubgroup) ^ n`. Rewrite using `[hspanE, hLN, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]`. Conclude with `(AddSubgroup.relIndex_map_map_of_injective _ _ hΨ).trans (relIndex_piL _ _)`.

Establish `hz : ∀ v (x : Wh.V), majAt Wh.b Wh.X v 0 x = 0 ∧ majAt Wh.b Wh.X v x 0 = 0`. Introduce `v x`. Take `⟨-, -, h3, h4⟩` from `isSesq_maj Wh.b Wh.X v`. Prove the components needed by the constructor for the conclusion. Use `h3 0 0 x` as an intermediate fact.

Simplify using `using this`. Use `h4 0 x 0` as an intermediate fact. Simplify using `using this`. Establish `hgram : ∀ v, gramPl B.b B.X v E = Matrix.reindex ε.symm ε.symm ((g.map (Int.cast : ℤ → ℂ)) ⊗ₖ gramPl Wh.b Wh.X v e)`. Introduce `v`.

Use extensionality with `k l`. Simplify using `only [gramPl, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.kroneckerMap_apply, Matrix.map_apply, E, hmaj]`. Rewrite using `[Finset.sum_eq_single (ε k).1, Finset.sum_eq_single (ε l).1]`. Simplify using `[P]`. Introduce `c _ hc`.

Simplify using `[P, Pi.single_eq_of_ne hc, (hz v _).2]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Simplify using `[P, Pi.single_eq_of_ne hb, (hz v _).1]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Set `d : InfinitePlace K → ℝ` to `fun v => (gramPl Wh.b Wh.X v e).det.re`. Establish `hd : ∀ v, 0 < d v` using `fun v => (hdet v).1`.

Establish `hdc : ∀ v, (gramPl Wh.b Wh.X v e).det = ((d v : ℝ) : ℂ)` using `fun v => Complex.ext rfl (by simpa using (hdet v).2)`. Establish `hdetE : ∀ v, (gramPl B.b B.X v E).det.re = (g.det : ℝ) ^ w * d v ^ n`. Introduce `v`. Establish `h1 : (g.map (Int.cast : ℤ → ℂ)).det = ((g.det : ℤ) : ℂ)`. Use `(Int.castRingHom ℂ).map_det g` as an intermediate fact.

Simplify `this.symm` using `[RingHom.mapMatrix_apply]`. Rewrite using `[hgram, Matrix.det_reindex_self, Matrix.det_kronecker, h1, hdc, Fintype.card_fin]`. Establish `: (((g.det : ℤ) : ℂ) ^ w * ((d v : ℝ) : ℂ) ^ Fintype.card β) = ((((g.det : ℝ) ^ w * d v ^ n : ℝ)) : ℂ)`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_intCast]`. Rewrite using `[this, Complex.ofReal_re]`.

Use `set I : ℕ := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex Wh.L.toAddSubgroup with hI`. Establish `hWpos` using `(plLat K Wh.V Wh.ι Wh.b Wh.X hW.1 Wh.L hW.2.1).2.2`. Establish `hNpos` using `(plLat K B.V B.ι B.b B.X hB LN hLNfg).2.2`. Rewrite `hG3` using `[hG1]`. Rewrite `hH3` using `[hH1, hidx]`.

Establish `hPpos : 0 < ∏ v, d v` using `Finset.prod_pos fun v _ => hd v`. Establish `hIpos : (0 : ℝ) < (I : ℝ)`. Establish `h1 : 0 < ht Wh.b Wh.X Wh.L * (I : ℝ)` using `by rw [hG3]; exact hPpos`. Conclude with `(pos_iff_pos_of_mul_pos h1).1 hWpos`. Establish `hgR : (0 : ℝ) < (g.det : ℝ)` using `by exact_mod_cast hg`.

Establish `hlogW : Real.log (ht Wh.b Wh.X Wh.L) + Real.log I = ∑ v, Real.log (d v)`. Rewrite using `[← Real.log_mul hWpos.ne' hIpos.ne', hG3, Real.log_prod]`. Introduce `v _`. Conclude with `(hd v).ne'`. Establish `hlogN : Real.log (ht B.b B.X LN) + n * Real.log I = (nPl K : ℝ) * (w * Real.log (g.det : ℝ)) + n * ∑ v, Real.log (d v)`.

Establish `h1 : Real.log (ht B.b B.X LN * ((I ^ n : ℕ) : ℝ)) = ∑ v, Real.log ((g.det : ℝ) ^ w * d v ^ n)`. Rewrite using `[hH3, Real.log_prod]`. Conclude with `Finset.sum_congr rfl fun v _ => by rw [hdetE]`. Introduce `v _`. Rewrite using `[hdetE]`.

Conclude with `(mul_pos (pow_pos hgR _) (pow_pos (hd v) _)).ne'`. Rewrite `h1` using `[Nat.cast_pow]`. Rewrite `h1` using `[Real.log_mul hNpos.ne' (pow_pos hIpos _).ne', Real.log_pow]`. Rewrite using `[h1]`. Establish `h2 : ∀ v, Real.log ((g.det : ℝ) ^ w * d v ^ n) = w * Real.log (g.det : ℝ) + n * Real.log (d v)`.

Introduce `v`. Rewrite using `[Real.log_mul (pow_pos hgR _).ne' (pow_pos (hd v) _).ne', Real.log_pow, Real.log_pow]`. Simplify using `only [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]`. Both sides reduce to the same expression. Establish `hnPl : (0 : ℝ) < (nPl K : ℝ)`.

Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions. Establish `hnR : (0 : ℝ) < (n : ℝ)` using `by exact_mod_cast hn0`. Establish `hwR : (0 : ℝ) < (w : ℝ)` using `by exact_mod_cast hw`. Use `show muDef B.b B.X LN = muDef Wh.b Wh.X Wh.L - _`.

Rewrite using `[mu_eq_log_ht B.b B.X hB LN hLNfg hLN0, mu_eq_log_ht Wh.b Wh.X hW.1 Wh.L hW.2.1 hW0, hrkN, hrkW]`. Establish `h3 : Real.log (ht B.b B.X LN) = (nPl K : ℝ) * (w * Real.log (g.det : ℝ)) + n * Real.log (ht Wh.b Wh.X Wh.L)`. Rewrite `hlogN` using `[← hlogW]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h3]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kron_mu (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    {β : Type} [Fintype β] [DecidableEq β] [Nonempty β]
    (Ψ : (β → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ) (g : Matrix β β ℤ) (hg : 0 < g.det)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') =
      ∑ b, ∑ c, (g b c : ℂ) * majAt Wh.b Wh.X v (F b) (F' c)) :
    (withL B ((piL β Wh.L).map (Ψ.restrictScalars (𝓞 K)))).mu =
      Wh.mu - Real.log (g.det : ℝ) / (Fintype.card β : ℝ) := by
  classical
  have : FiniteDimensional K Wh.V := Module.Finite.of_basis Wh.b
  obtain ⟨w, e, he, heL, hsp⟩ := covolume_exists K Wh.V Wh.L
  obtain ⟨hrkW, hw, hdet, -, -⟩ := log_covolume_slope_mu K Wh.V Wh.ι Wh.b Wh.X hW.1 w e Wh.L he hW.2.1 hW0 hsp
  obtain ⟨hG1, hG2⟩ := htGram K Wh.V Wh.ι Wh.b Wh.X hW.1 w e he
  have heL' : Submodule.span (𝓞 K) (Set.range e) ≤ Wh.L :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact heL a)
  have hG3 := hG2 Wh.L hW.2.1 heL' hrkW
  have hspT : Submodule.span K (Set.range e) = ⊤ := hsp ▸ hW.2.2
  set n := Fintype.card β with hn
  have hn0 : 0 < n := Fintype.card_pos
  let ε : Fin (n * w) ≃ β × Fin w :=
    finProdFinEquiv.symm.trans ((Fintype.equivFin β).symm.prodCongr (Equiv.refl _))
  let P : β × Fin w → (β → Wh.V) := fun p => Pi.single p.1 (e p.2)
  let E : Fin (n * w) → B.V := fun k => Ψ (P (ε k))
  let bW : Basis (Fin w) K Wh.V := Basis.mk he hspT.ge
  let bP : Basis (Σ _ : β, Fin w) K (β → Wh.V) := Pi.basis fun _ => bW
  have hP : ∀ p, P p = bP ⟨p.1, p.2⟩ := by
    intro p
    simp [P, bP, bW, Pi.basis_apply, Basis.mk_apply]
  have hPli : LinearIndependent K P := by
    have h1 := bP.linearIndependent.comp (fun p : β × Fin w => (⟨p.1, p.2⟩ : Σ _ : β, Fin w))
      (fun p q h => by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [Sigma.mk.injEq, heq_eq_eq] at h
        exact Prod.ext h.1 h.2)
    have h2 : P = bP ∘ fun p : β × Fin w => (⟨p.1, p.2⟩ : Σ _ : β, Fin w) := funext hP
    rw [h2]
    exact h1
  have hPsp : Submodule.span K (Set.range P) = ⊤ := by
    rw [eq_top_iff, ← bP.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨⟨b, i⟩, rfl⟩
    exact ⟨(b, i), hP (b, i)⟩
  have hEli : LinearIndependent K E :=
    (hPli.map' Ψ (LinearMap.ker_eq_bot.2 hΨ)).comp ε ε.injective
  have hrange : Set.range E = Ψ '' Set.range P := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨P (ε k), ⟨ε k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨ε.symm p, by simp [E]⟩
  set LN : Submodule (𝓞 K) B.V := (piL β Wh.L).map (Ψ.restrictScalars (𝓞 K)) with hLN
  have hspanE : Submodule.span (𝓞 K) (Set.range E) =
      (piL β (Submodule.span (𝓞 K) (Set.range e))).map (Ψ.restrictScalars (𝓞 K)) := by
    rw [piL_span, Submodule.map_span, hrange]
    rfl
  have hEle : Submodule.span (𝓞 K) (Set.range E) ≤ LN := by
    rw [hspanE]
    exact Submodule.map_mono fun F hF b hb => heL' (hF b hb)
  have hLNfg : LN.FG := (Submodule.fg_pi fun _ => hW.2.1).map _
  have hnw : 0 < n * w := Nat.mul_pos hn0 hw
  have hLN0 : LN ≠ ⊥ := by
    intro h0
    have h1 : E ⟨0, hnw⟩ ∈ LN := hEle (Submodule.subset_span ⟨_, rfl⟩)
    rw [h0, Submodule.mem_bot] at h1
    exact hEli.ne_zero _ h1
  have hspK : Submodule.span K (LN : Set B.V) = Submodule.span K (Set.range E) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨F, -, rfl⟩
      have h1 : F ∈ Submodule.span K (Set.range P) := hPsp ▸ Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := Ψ) h1
      rw [Submodule.map_span, ← hrange] at h2
      exact h2
    · apply Submodule.span_mono
      rintro _ ⟨k, rfl⟩
      exact hEle (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨hrkN, -, -, -, -⟩ := log_covolume_slope_mu K B.V B.ι B.b B.X hB (n * w) E LN hEli hLNfg hLN0 hspK
  obtain ⟨hH1, hH2⟩ := htGram K B.V B.ι B.b B.X hB (n * w) E hEli
  have hH3 := hH2 LN hLNfg hEle hrkN
  have hidx : (Submodule.span (𝓞 K) (Set.range E)).toAddSubgroup.relIndex LN.toAddSubgroup =
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex Wh.L.toAddSubgroup) ^ n := by
    rw [hspanE, hLN, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact (AddSubgroup.relIndex_map_map_of_injective _ _ hΨ).trans (relIndex_piL _ _)
  have hz : ∀ v (x : Wh.V), majAt Wh.b Wh.X v 0 x = 0 ∧ majAt Wh.b Wh.X v x 0 = 0 := by
    intro v x
    obtain ⟨-, -, h3, h4⟩ := isSesq_maj Wh.b Wh.X v
    constructor
    · have := h3 0 0 x
      simpa using this
    · have := h4 0 x 0
      simpa using this
  have hgram : ∀ v, gramPl B.b B.X v E =
      Matrix.reindex ε.symm ε.symm ((g.map (Int.cast : ℤ → ℂ)) ⊗ₖ gramPl Wh.b Wh.X v e) := by
    intro v
    ext k l
    simp only [gramPl, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.kroneckerMap_apply, Matrix.map_apply, E, hmaj]
    rw [Finset.sum_eq_single (ε k).1, Finset.sum_eq_single (ε l).1]
    · simp [P]
    · intro c _ hc
      simp [P, Pi.single_eq_of_ne hc, (hz v _).2]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [P, Pi.single_eq_of_ne hb, (hz v _).1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  let d : InfinitePlace K → ℝ := fun v => (gramPl Wh.b Wh.X v e).det.re
  have hd : ∀ v, 0 < d v := fun v => (hdet v).1
  have hdc : ∀ v, (gramPl Wh.b Wh.X v e).det = ((d v : ℝ) : ℂ) := fun v =>
    Complex.ext rfl (by simpa using (hdet v).2)
  have hdetE : ∀ v, (gramPl B.b B.X v E).det.re = (g.det : ℝ) ^ w * d v ^ n := by
    intro v
    have h1 : (g.map (Int.cast : ℤ → ℂ)).det = ((g.det : ℤ) : ℂ) := by
      have := (Int.castRingHom ℂ).map_det g
      simpa [RingHom.mapMatrix_apply] using this.symm
    rw [hgram, Matrix.det_reindex_self, Matrix.det_kronecker, h1, hdc, Fintype.card_fin]
    have : (((g.det : ℤ) : ℂ) ^ w * ((d v : ℝ) : ℂ) ^ Fintype.card β) =
        ((((g.det : ℝ) ^ w * d v ^ n : ℝ)) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_intCast]
    rw [this, Complex.ofReal_re]
  set I : ℕ := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex Wh.L.toAddSubgroup with hI
  have hWpos := (plLat K Wh.V Wh.ι Wh.b Wh.X hW.1 Wh.L hW.2.1).2.2
  have hNpos := (plLat K B.V B.ι B.b B.X hB LN hLNfg).2.2
  rw [hG1] at hG3
  rw [hH1, hidx] at hH3
  have hPpos : 0 < ∏ v, d v := Finset.prod_pos fun v _ => hd v
  have hIpos : (0 : ℝ) < (I : ℝ) := by
    have h1 : 0 < ht Wh.b Wh.X Wh.L * (I : ℝ) := by rw [hG3]; exact hPpos
    exact (pos_iff_pos_of_mul_pos h1).1 hWpos
  have hgR : (0 : ℝ) < (g.det : ℝ) := by exact_mod_cast hg
  have hlogW : Real.log (ht Wh.b Wh.X Wh.L) + Real.log I = ∑ v, Real.log (d v) := by
    rw [← Real.log_mul hWpos.ne' hIpos.ne', hG3, Real.log_prod]
    intro v _
    exact (hd v).ne'
  have hlogN : Real.log (ht B.b B.X LN) + n * Real.log I =
      (nPl K : ℝ) * (w * Real.log (g.det : ℝ)) + n * ∑ v, Real.log (d v) := by
    have h1 : Real.log (ht B.b B.X LN * ((I ^ n : ℕ) : ℝ)) = ∑ v, Real.log ((g.det : ℝ) ^ w * d v ^ n) := by
      rw [hH3, Real.log_prod]
      · exact Finset.sum_congr rfl fun v _ => by rw [hdetE]
      · intro v _
        rw [hdetE]
        exact (mul_pos (pow_pos hgR _) (pow_pos (hd v) _)).ne'
    rw [Nat.cast_pow] at h1
    rw [Real.log_mul hNpos.ne' (pow_pos hIpos _).ne', Real.log_pow] at h1
    rw [h1]
    have h2 : ∀ v, Real.log ((g.det : ℝ) ^ w * d v ^ n) = w * Real.log (g.det : ℝ) + n * Real.log (d v) := by
      intro v
      rw [Real.log_mul (pow_pos hgR _).ne' (pow_pos (hd v) _).ne', Real.log_pow, Real.log_pow]
    simp only [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
    rfl
  have hnPl : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  show muDef B.b B.X LN = muDef Wh.b Wh.X Wh.L - _
  rw [mu_eq_log_ht B.b B.X hB LN hLNfg hLN0, mu_eq_log_ht Wh.b Wh.X hW.1 Wh.L hW.2.1 hW0, hrkN, hrkW]
  have h3 : Real.log (ht B.b B.X LN) =
      (nPl K : ℝ) * (w * Real.log (g.det : ℝ)) + n * Real.log (ht Wh.b Wh.X Wh.L) := by
    rw [← hlogW] at hlogN
    linarith
  rw [h3]
  push_cast
  field_simp
  ring

end Slope

section PiKron

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
  {R : Type} [CommRing R]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[piKronOn, Matrix.one_apply, funext_iff]`.
-/
theorem piKronOn_empty (M : ∀ i, Matrix (α i) (α i) R) : piKronOn M ∅ = 1 := by
  ext a b
  simp [piKronOn, Matrix.one_apply, funext_iff]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[piKronOn, piKron]`.
-/
theorem piKronOn_univ (M : ∀ i, Matrix (α i) (α i) R) : piKronOn M Finset.univ = piKron M := by
  ext a b
  simp [piKronOn, piKron]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Function.update b k (a k))]`. Establish `h1 : ∀ i ∈ s, M i (a i) (Function.update b k (a k) i) = M i (a i) (b i)`. Introduce `i hi`. Rewrite using `[Function.update_of_ne (fun h : i = k => hk (h ▸ hi))]`.

Establish `h2 : (∀ i, i ∉ ({k} : Finset ι) → Function.update b k (a k) i = b i)`. Introduce `i hi`. Rewrite using `[Function.update_of_ne (fun h : i = k => hi (by simp [h]))]`. Establish `h3 : (∀ i, i ∉ s → a i = Function.update b k (a k) i) ↔ ∀ i, i ∉ insert k s → a i = b i`. Prove the components needed by the constructor for the conclusion.

Introduce `H i hi`. Rewrite `hi` using `[Finset.mem_insert, not_or]`. Use `H i hi.2` as an intermediate fact. Rewrite `this` using `[Function.update_of_ne hi.1]`. Then use the resulting hypothesis. Introduce `H i hi`.

Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Rewrite using `[Function.update_self]`. Rewrite using `[Function.update_of_ne hik]`. Conclude with `H i (by rw [Finset.mem_insert, not_or]; exact ⟨hik, hi⟩)`.

Simplify using `only [piKronOn, Matrix.of_apply, Finset.prod_insert hk, Finset.prod_singleton, Function.update_self, if_pos h2, mul_one, Finset.prod_congr rfl h1]`. Distinguish the cases in `h4 : ∀ i, i ∉ insert k s → a i = b i`. Rewrite using `[if_pos h4, if_pos (h3.2 h4)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h4, if_neg (fun H => h4 (h3.1 H))]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Distinguish the cases in `h5 : ∀ i, i ∉ ({k} : Finset ι) → c i = b i`. Establish `h6 : ¬ ∀ i, i ∉ s → a i = c i`. Introduce `H`.

Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Rewrite using `[Function.update_self, H i hk]`.

Rewrite using `[Function.update_of_ne hik]`. Conclude with `h5 i (by simpa using hik)`. Simplify using `[piKronOn, if_neg h6]`. Simplify using `only [piKronOn, Matrix.of_apply, if_neg h5, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem piKronOn_insert (M : ∀ i, Matrix (α i) (α i) R) (s : Finset ι) (k : ι) (hk : k ∉ s) :
    piKronOn M (insert k s) = piKronOn M s * piKronOn M {k} := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update b k (a k))]
  · have h1 : ∀ i ∈ s, M i (a i) (Function.update b k (a k) i) = M i (a i) (b i) := by
      intro i hi
      rw [Function.update_of_ne (fun h : i = k => hk (h ▸ hi))]
    have h2 : (∀ i, i ∉ ({k} : Finset ι) → Function.update b k (a k) i = b i) := by
      intro i hi
      rw [Function.update_of_ne (fun h : i = k => hi (by simp [h]))]
    have h3 : (∀ i, i ∉ s → a i = Function.update b k (a k) i) ↔ ∀ i, i ∉ insert k s → a i = b i := by
      constructor
      · intro H i hi
        rw [Finset.mem_insert, not_or] at hi
        have := H i hi.2
        rwa [Function.update_of_ne hi.1] at this
      · intro H i hi
        by_cases hik : i = k
        · subst hik
          rw [Function.update_self]
        · rw [Function.update_of_ne hik]
          exact H i (by rw [Finset.mem_insert, not_or]; exact ⟨hik, hi⟩)
    simp only [piKronOn, Matrix.of_apply, Finset.prod_insert hk, Finset.prod_singleton, Function.update_self,
      if_pos h2, mul_one, Finset.prod_congr rfl h1]
    by_cases h4 : ∀ i, i ∉ insert k s → a i = b i
    · rw [if_pos h4, if_pos (h3.2 h4)]
      ring
    · rw [if_neg h4, if_neg (fun H => h4 (h3.1 H))]
      ring
  · intro c _ hc
    by_cases h5 : ∀ i, i ∉ ({k} : Finset ι) → c i = b i
    · have h6 : ¬ ∀ i, i ∉ s → a i = c i := by
        intro H
        apply hc
        funext i
        by_cases hik : i = k
        · subst hik
          rw [Function.update_self, H i hk]
        · rw [Function.update_of_ne hik]
          exact h5 i (by simpa using hik)
      simp [piKronOn, if_neg h6]
    · simp only [piKronOn, Matrix.of_apply, if_neg h5, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h : piKronOn M {k} = Matrix.reindex (Equiv.piSplitAt k α).symm (Equiv.piSplitAt k α).symm (M k ⊗ₖ (1 : Matrix (∀ j : {j // j ≠ k}, α j) (∀ j : {j // j ≠ k}, α j) R))`. Use extensionality with `a b`. Simplify using `only [piKronOn, Matrix.of_apply, Finset.prod_singleton, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.kroneckerMap_apply, Equiv.piSplitAt_apply, Matrix.one_apply]`. Use `congr 1`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Use function extensionality and compare the values at `j`. Conclude with `H j (by simpa using j.2)`. Introduce `H i hi`.

Conclude with `congrFun H ⟨i, by simpa using hi⟩`. Rewrite using `[h, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_pi]`. Use `congr 1`. Rewrite using `[← Finset.prod_subtype (Finset.univ.erase k) (by simp) fun j => Fintype.card (α j)]`.
-/
theorem det_piKronOn_singleton (M : ∀ i, Matrix (α i) (α i) R) (k : ι) :
    (piKronOn M {k}).det = (M k).det ^ ∏ j ∈ Finset.univ.erase k, Fintype.card (α j) := by
  have h : piKronOn M {k} = Matrix.reindex (Equiv.piSplitAt k α).symm (Equiv.piSplitAt k α).symm
      (M k ⊗ₖ (1 : Matrix (∀ j : {j // j ≠ k}, α j) (∀ j : {j // j ≠ k}, α j) R)) := by
    ext a b
    simp only [piKronOn, Matrix.of_apply, Finset.prod_singleton, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Matrix.kroneckerMap_apply, Equiv.piSplitAt_apply, Matrix.one_apply]
    congr 1
    refine if_congr ?_ rfl rfl
    constructor
    · intro H
      funext j
      exact H j (by simpa using j.2)
    · intro H i hi
      exact congrFun H ⟨i, by simpa using hi⟩
  rw [h, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_pi]
  congr 1
  rw [← Finset.prod_subtype (Finset.univ.erase k) (by simp) fun j => Fintype.card (α j)]

/- English proof (translation)
Use `Finset.induction_on s (by simp [piKronOn_empty]) ?_` and prove the remaining obligations. Introduce `k s hk ih`. Rewrite using `[piKronOn_insert M s k hk, Matrix.det_mul, ih, det_piKronOn_singleton, Finset.prod_insert hk, mul_comm]`.
-/
theorem det_piKronOn (M : ∀ i, Matrix (α i) (α i) R) (s : Finset ι) :
    (piKronOn M s).det = ∏ k ∈ s, (M k).det ^ ∏ j ∈ Finset.univ.erase k, Fintype.card (α j) := by
  refine Finset.induction_on s (by simp [piKronOn_empty]) ?_
  intro k s hk ih
  rw [piKronOn_insert M s k hk, Matrix.det_mul, ih, det_piKronOn_singleton, Finset.prod_insert hk, mul_comm]

/- English proof (translation)
Rewrite using `[← piKronOn_univ, det_piKronOn]`.
-/
theorem det_piKron (M : ∀ i, Matrix (α i) (α i) R) :
    (piKron M).det = ∏ k, (M k).det ^ ∏ j ∈ Finset.univ.erase k, Fintype.card (α j) := by
  rw [← piKronOn_univ, det_piKronOn]

end PiKron

section KronMap

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] {α β : Type} [Fintype β]

variable {R M}

/- English proof (translation)
Simplify using `[kronMap]`.
-/
theorem kronMap_apply (t : Matrix β α ℤ) (F : β → M) (a : α) : kronMap R M t F a = ∑ b, t b a • F b := by
  simp [kronMap]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Use function extensionality and compare the values at `a`. Simplify using `[kronMap_apply, Matrix.one_apply]`.
-/
theorem kronMap_one [DecidableEq β] : kronMap R M (1 : Matrix β β ℤ) = LinearMap.id := by
  apply LinearMap.ext
  intro F
  funext a
  simp [kronMap_apply, Matrix.one_apply]

end KronMap

section Model

variable {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

/- English proof (translation)
Establish `hfac : ∀ (b c : SzIdx G) (i : ι), (∑ x : G i, ((if x = (b i : G i) then (1 : ℤ) else 0) - (if x = 1 then 1 else 0)) * ((if x = (c i : G i) then 1 else 0) - (if x = 1 then 1 else 0))) = (if b i = c i then 1 else 0) + 1`. Introduce `b c i`. Establish `hb` using `(b i).2`. Establish `hc` using `(c i).2`. Establish `e : ∀ x : G i, ((if x = (b i : G i) then (1 : ℤ) else 0) - (if x = 1 then 1 else 0)) * ((if x = (c i : G i) then 1 else 0) - (if x = 1 then 1 else 0)) = (if x = (b i : G i) then (if (b i : G i) = (c i : G i) then (1 : ℤ) else 0) else 0) + (if x = 1 then 1 else 0)`.

Introduce `x`. Apply the tactic sequence `by_cases h1 : x = (b i : G i) <;> by_cases h2 : x = 1 <;> by_cases h3 : x = (c i : G i) <;> simp_all`. Rewrite using `[Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_univ, if_true, add_left_inj]`. Use `split_ifs with h1 h2 h2`.

Both sides reduce to the same expression. Conclude with `absurd (Subtype.ext h1) h2`. Conclude with `absurd (congrArg Subtype.val h2) h1`. Both sides reduce to the same expression. Use extensionality with `b c`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, szVec, szGram, piKron, szGram1, Matrix.of_apply]`. Repeatedly rewrite using `[← Finset.prod_mul_distrib]`. Repeatedly rewrite using `[← hfac b c]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`.
-/
theorem szVec_mul_transpose : szVec G * (szVec G)ᵀ = szGram G := by
  have hfac : ∀ (b c : SzIdx G) (i : ι), (∑ x : G i, ((if x = (b i : G i) then (1 : ℤ) else 0) - (if x = 1 then 1 else 0)) *
      ((if x = (c i : G i) then 1 else 0) - (if x = 1 then 1 else 0))) = (if b i = c i then 1 else 0) + 1 := by
    intro b c i
    have hb := (b i).2
    have hc := (c i).2
    have e : ∀ x : G i, ((if x = (b i : G i) then (1 : ℤ) else 0) - (if x = 1 then 1 else 0)) *
        ((if x = (c i : G i) then 1 else 0) - (if x = 1 then 1 else 0)) =
        (if x = (b i : G i) then (if (b i : G i) = (c i : G i) then (1 : ℤ) else 0) else 0) +
          (if x = 1 then 1 else 0) := by
      intro x
      by_cases h1 : x = (b i : G i) <;> by_cases h2 : x = 1 <;> by_cases h3 : x = (c i : G i) <;> simp_all
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, add_left_inj]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Subtype.ext h1) h2
    · exact absurd (congrArg Subtype.val h2) h1
    · rfl
  ext b c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, szVec, szGram, piKron, szGram1, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  simp_rw [← hfac b c]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`.
-/
theorem card_ne_one (i : ι) : Fintype.card {g : G i // g ≠ 1} = Fintype.card (G i) - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/- English proof (translation)
Simplify using `[Fintype.card_pi, card_ne_one]`.
-/
theorem card_SzIdx : Fintype.card (SzIdx G) = ∏ i, (Fintype.card (G i) - 1) := by
  simp [Fintype.card_pi, card_ne_one]

/- English proof (translation)
Establish `h : szGram1 G i = 1 + Matrix.vecMulVec (fun _ => (1 : ℤ)) (fun _ => 1)`. Use extensionality with `b c`. Simplify using `[szGram1, Matrix.one_apply, Matrix.vecMulVec_apply]`. Establish `hdet : (1 + Matrix.vecMulVec (fun _ : {g : G i // g ≠ 1} => (1 : ℤ)) (fun _ => 1)).det = 1 + (fun _ : {g : G i // g ≠ 1} => (1 : ℤ)) ⬝ᵥ (fun _ => 1)` using `by first`. Consider the case `(rw [Matrix.vecMulVec_eq (ι := Unit)]`.

Conclude with `Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) _ _)`. Consider the case `(rw [Matrix.vecMulVec_eq Unit]`. Conclude with `Matrix.det_one_add_replicateCol_mul_replicateRow _ _)`. Consider the case `(simp only [Matrix.vecMulVec_eq (ι := Unit)]`. Conclude with `Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) _ _)`.

Establish `hpos : 1 ≤ Fintype.card (G i)` using `Fintype.card_pos`. Rewrite using `[h, hdet]`. Simplify using `[dotProduct, card_ne_one, Nat.cast_sub hpos]`.
-/
theorem det_szGram1 (i : ι) : (szGram1 G i).det = (Fintype.card (G i) : ℤ) := by
  have h : szGram1 G i = 1 + Matrix.vecMulVec (fun _ => (1 : ℤ)) (fun _ => 1) := by
    ext b c
    simp [szGram1, Matrix.one_apply, Matrix.vecMulVec_apply]
  have hdet : (1 + Matrix.vecMulVec (fun _ : {g : G i // g ≠ 1} => (1 : ℤ)) (fun _ => 1)).det =
      1 + (fun _ : {g : G i // g ≠ 1} => (1 : ℤ)) ⬝ᵥ (fun _ => 1) := by
    first
    | (rw [Matrix.vecMulVec_eq (ι := Unit)]
       exact Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) _ _)
    | (rw [Matrix.vecMulVec_eq Unit]
       exact Matrix.det_one_add_replicateCol_mul_replicateRow _ _)
    | (simp only [Matrix.vecMulVec_eq (ι := Unit)]
       exact Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) _ _)
  have hpos : 1 ≤ Fintype.card (G i) := Fintype.card_pos
  rw [h, hdet]
  simp [dotProduct, card_ne_one, Nat.cast_sub hpos]

/- English proof (translation)
Rewrite using `[szGram, det_piKron]`. Simplify using `only [det_szGram1, card_ne_one]`.
-/
theorem det_szGram : (szGram G).det =
    ∏ k, (Fintype.card (G k) : ℤ) ^ ∏ j ∈ Finset.univ.erase k, (Fintype.card (G j) - 1) := by
  rw [szGram, det_piKron]
  simp only [det_szGram1, card_ne_one]

/- English proof (translation)
Rewrite using `[det_szGram]`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `k _`. Apply `pow_pos` to reduce the goal to its premises. Conclude with `Fintype.card_pos` after adjusting the coercions.
-/
theorem det_szGram_pos : 0 < (szGram G).det := by
  rw [det_szGram]
  apply Finset.prod_pos
  intro k _
  apply pow_pos
  exact_mod_cast Fintype.card_pos

/- English proof (translation)
Simplify using `only [szVec, Matrix.of_apply, SzIdx.pt]`. Establish `h1 : ∀ i, ((c i : G i) = 1) ↔ False` using `fun i => iff_false_intro (c i).2`. Simplify using `only [h1, if_false, sub_zero]`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hbc]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, b i ≠ c i := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hbc (funext h)`. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Use `split_ifs with h`. Conclude with `absurd (Subtype.ext h.symm) hi`. Conclude with `if_neg h`.
-/
theorem szVec_pt (b c : SzIdx G) : szVec G b c.pt = if b = c then 1 else 0 := by
  dsimp only [szVec, Matrix.of_apply, SzIdx.pt]
  have h1 : ∀ i, ((c i : G i) = 1) ↔ False := fun i => iff_false_intro (c i).2
  simp only [h1, if_false, sub_zero]
  by_cases hbc : b = c
  · subst hbc
    simp
  · rw [if_neg hbc]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra h
      push_neg at h
      exact hbc (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    split_ifs with h
    · exact absurd (Subtype.ext h.symm) hi
    · exact if_neg h

/- English proof (translation)
Simplify using `only [szVec, Matrix.of_apply]`. Establish `key : ∀ g : G i, (∏ j, ((if (Pi.mulSingle i g * c) j = (b j : G j) then (1 : ℤ) else 0) - (if (Pi.mulSingle i g * c) j = 1 then 1 else 0))) = ((if g * c i = (b i : G i) then 1 else 0) - (if g * c i = 1 then 1 else 0)) * ∏ j ∈ Finset.univ.erase i, ((if c j = (b j : G j) then (1 : …`. Introduce `g`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Use `congr 1`.

Simplify using the standard rewrite rules. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), one_mul]`. Establish `h1 : ∀ x : G i, (∑ g : G i, if g * c i = x then (1 : ℤ) else 0) = 1`.

Introduce `x`. Rewrite using `[Finset.sum_eq_single (x * (c i)⁻¹)]`. Simplify using the standard rewrite rules. Introduce `g _ hg`. Rewrite using `[if_neg (fun h => hg (eq_mul_inv_of_mul_eq h))]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl (fun g _ => key g), ← Finset.sum_mul, Finset.sum_sub_distrib, h1, h1, sub_self, zero_mul]`.
-/
theorem sum_szVec (b : SzIdx G) (i : ι) (c : ∀ i, G i) : ∑ g : G i, szVec G b (Pi.mulSingle i g * c) = 0 := by
  simp only [szVec, Matrix.of_apply]
  have key : ∀ g : G i, (∏ j, ((if (Pi.mulSingle i g * c) j = (b j : G j) then (1 : ℤ) else 0) -
      (if (Pi.mulSingle i g * c) j = 1 then 1 else 0))) =
      ((if g * c i = (b i : G i) then 1 else 0) - (if g * c i = 1 then 1 else 0)) *
        ∏ j ∈ Finset.univ.erase i, ((if c j = (b j : G j) then (1 : ℤ) else 0) - (if c j = 1 then 1 else 0)) := by
    intro g
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), one_mul]
  have h1 : ∀ x : G i, (∑ g : G i, if g * c i = x then (1 : ℤ) else 0) = 1 := by
    intro x
    rw [Finset.sum_eq_single (x * (c i)⁻¹)]
    · simp
    · intro g _ hg
      rw [if_neg (fun h => hg (eq_mul_inv_of_mul_eq h))]
    · simp
  rw [Finset.sum_congr rfl (fun g _ => key g), ← Finset.sum_mul, Finset.sum_sub_distrib, h1, h1, sub_self, zero_mul]

end Model

section Ram

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type)
  [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {M : Type} [AddCommGroup M] [Module K M]

/- English proof (translation)
Simplify using `[kronMap_apply, szVec_pt]`.
-/
theorem kron_szVec_pt (F : SzIdx G → M) (c : SzIdx G) : kronMap K M (szVec G) F c.pt = F c := by
  simp [kronMap_apply, szVec_pt]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `F hF`. Use function extensionality and compare the values at `c`. Establish `h` using `kron_szVec_pt (K := K) G F c`. Rewrite `h` using `[hF]`.

Simplify using `using h.symm`.
-/
theorem kron_szVec_injective : Function.Injective (kronMap K M (szVec G)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  funext c
  have h := kron_szVec_pt (K := K) G F c
  rw [hF] at h
  simpa using h.symm

/- English proof (translation)
Simplify using `only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `i`. Use function extensionality and compare the values at `c`. Simplify using `only [RamFun.nmF, RamFun.trl, LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply, kronMap_apply, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, sum_szVec, zero_smul]`.
-/
theorem kron_szVec_mem (F : SzIdx G → M) : kronMap K M (szVec G) F ∈ RamFun.ramFun K G M := by
  simp only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i
  funext c
  simp only [RamFun.nmF, RamFun.trl, LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply, kronMap_apply,
    Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_smul, sum_szVec, zero_smul]

/- English proof (translation)
Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨F, rfl⟩`. Conclude with `kron_szVec_mem G F`. Rewrite using `[LinearMap.finrank_range_of_inj (kron_szVec_injective G), RamFun.finrank_ramFun, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, card_SzIdx, smul_eq_mul, mul_comm]`.
-/
theorem range_kron_szVec [FiniteDimensional K M] :
    LinearMap.range (kronMap K M (szVec G)) = RamFun.ramFun K G M := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨F, rfl⟩
    exact kron_szVec_mem G F
  · rw [LinearMap.finrank_range_of_inj (kron_szVec_injective G), RamFun.finrank_ramFun, Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, card_SzIdx, smul_eq_mul, mul_comm]

end Ram

end T2

namespace T2

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `hH v`. Establish `sumL : ∀ {κ : Type} (s : Finset κ) (f : κ → V) (y : V), H v (∑ k ∈ s, f k) y = ∑ k ∈ s, H v (f k) y`. Introduce `κ s f y`. Conclude with `map_sum (AddMonoidHom.mk' (fun x => H v x y) (fun x x' => h1 x x' y)) f s`. Establish `sumR : ∀ {κ : Type} (s : Finset κ) (f : κ → V) (x : V), H v x (∑ k ∈ s, f k) = ∑ k ∈ s, H v x (f k)`.

Introduce `κ s f x`. Conclude with `map_sum (AddMonoidHom.mk' (fun y => H v x y) (fun y y' => h2 x y y')) f s`. Establish `zL : ∀ (n : ℤ) (x y : V), H v (n • x) y = (n : ℂ) * H v x y`. Introduce `n x y`. Establish `h` using `map_zsmul (AddMonoidHom.mk' (fun x => H v x y) (fun x x' => h1 x x' y)) n x`.

Simplify `h` using `[zsmul_eq_mul]`. Establish `zR : ∀ (n : ℤ) (x y : V), H v x (n • y) = (n : ℂ) * H v x y`. Introduce `n x y`. Establish `h` using `map_zsmul (AddMonoidHom.mk' (fun y => H v x y) (fun y y' => h2 x y y')) n y`. Simplify `h` using `[zsmul_eq_mul]`.

Rewrite using `[sumL]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[zL, sumR, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[zR]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sesq_sum_zsmul {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (v : InfinitePlace K) {β γ : Type} [Fintype β] [Fintype γ]
    (z : β → ℤ) (x : β → V) (z' : γ → ℤ) (y : γ → V) :
    H v (∑ b, z b • x b) (∑ c, z' c • y c) = ∑ b, ∑ c, ((z b : ℂ) * (z' c : ℂ)) * H v (x b) (y c) := by
  obtain ⟨h1, h2, -, -⟩ := hH v
  have sumL : ∀ {κ : Type} (s : Finset κ) (f : κ → V) (y : V), H v (∑ k ∈ s, f k) y = ∑ k ∈ s, H v (f k) y := by
    intro κ s f y
    exact map_sum (AddMonoidHom.mk' (fun x => H v x y) (fun x x' => h1 x x' y)) f s
  have sumR : ∀ {κ : Type} (s : Finset κ) (f : κ → V) (x : V), H v x (∑ k ∈ s, f k) = ∑ k ∈ s, H v x (f k) := by
    intro κ s f x
    exact map_sum (AddMonoidHom.mk' (fun y => H v x y) (fun y y' => h2 x y y')) f s
  have zL : ∀ (n : ℤ) (x y : V), H v (n • x) y = (n : ℂ) * H v x y := by
    intro n x y
    have h := map_zsmul (AddMonoidHom.mk' (fun x => H v x y) (fun x x' => h1 x x' y)) n x
    simpa [zsmul_eq_mul] using h
  have zR : ∀ (n : ℤ) (x y : V), H v x (n • y) = (n : ℂ) * H v x y := by
    intro n x y
    have h := map_zsmul (AddMonoidHom.mk' (fun y => H v x y) (fun y y' => h2 x y y')) n y
    simpa [zsmul_eq_mul] using h
  rw [sumL]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [zL, sumR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [zR]
  ring

end T2

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

variable {S}

/- English proof (translation)
The claim follows from `R.pair_rat act_rat := R.act_rat pos := R.pos`.
-/
theorem Rat.restr (R : S.Rat) (T : SubMulAction S.G S.D) : (S.restr T).Rat where
  pair_rat := R.pair_rat
  act_rat := R.act_rat
  pos := R.pos

variable {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D]

/- English proof (translation)
Set `_` to `h.fintypeCl`. Set `_` to `(S.restr_ok h σ.T).fintypeCl`. Set `sT` to `(S.restr σ.T).outSec`. Rewrite using `[R.ipAt_indep h (σ.sec sT)]`. Simplify using `only [(R.restr σ.T).ipAt_indep (S.restr_ok h σ.T) sT]`.

Rewrite using `[← Fintype.sum_prod_type']`. Use `Fintype.sum_equiv (σ.clEquiv sT).symm _ _ fun c => ?_` and prove the remaining obligations. Use `show ((Nat.card (MulAction.stabilizer S.G (((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D))) : ℂ))⁻¹ * _ = _`. Rewrite using `[Slice.card_stab_smul', ← S.restr_card_stab σ.T]`. Both sides reduce to the same expression.
-/
theorem Slice.ipAt_split [Fintype A] (σ : S.Slice A) (R : S.Rat) (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.EqFun) :
    S.ipAt h v φ ψ = ∑ b : A, (S.restr σ.T).ipAt (S.restr_ok h σ.T) v (σ.split φ b) (σ.split ψ b) := by
  let _ := h.fintypeCl
  let _ := (S.restr_ok h σ.T).fintypeCl
  let sT := (S.restr σ.T).outSec
  rw [R.ipAt_indep h (σ.sec sT)]
  simp only [(R.restr σ.T).ipAt_indep (S.restr_ok h σ.T) sT]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (σ.clEquiv sT).symm _ _ fun c => ?_
  show ((Nat.card (MulAction.stabilizer S.G
      (((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D))) : ℂ))⁻¹ * _ = _
  rw [Slice.card_stab_smul', ← S.restr_card_stab σ.T]
  rfl

end GSD

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}
  {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D]

/- English proof (translation)
The claim follows from `σ.split.apply_symm_apply _`.
-/
theorem Slice.split_kron (σ : S.Slice A) {β : Type} [Fintype β] (t : Matrix β A ℤ)
    (F : β → (S.restr σ.T).EqFun) : σ.split (σ.kron t F) = T2.kronMap K _ t F :=
  σ.split.apply_symm_apply _

/- English proof (translation)
Rewrite using `[R.maj_eq, σ.ipAt_split R h]`. Simplify using `only [σ.split_kron, T2.kronMap_apply]`. Establish `hs` using `fun a : A => T2.sesq_sum_zsmul ((S.restr σ.T).isSesq_ipAt (S.restr_ok h σ.T)) v (fun b => t b a) F (fun c => t c a) F'`. Simplify using `only [hs]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[(R.restr σ.T).maj_eq, ← Finset.sum_mul, Matrix.mul_apply]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem Slice.kron_maj [Fintype A] (σ : S.Slice A) (R : S.Rat) (h : S.Ok) {β : Type} [Fintype β]
    (t : Matrix β A ℤ) (v : InfinitePlace K) (F F' : β → (S.restr σ.T).EqFun) :
    majAt (S.hB h) (stdFrame (S.hGram h)) v (σ.kron t F) (σ.kron t F') =
      ∑ b, ∑ c, (((t * tᵀ) b c : ℤ) : ℂ) * majAt (σ.WH h).b (σ.WH h).X v (F b) (F' c) := by
  rw [R.maj_eq, σ.ipAt_split R h]
  simp only [σ.split_kron, T2.kronMap_apply]
  have hs := fun a : A => T2.sesq_sum_zsmul ((S.restr σ.T).isSesq_ipAt (S.restr_ok h σ.T)) v
    (fun b => t b a) F (fun c => t c a) F'
  simp only [hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(R.restr σ.T).maj_eq, ← Finset.sum_mul, Matrix.mul_apply]
  push_cast
  rfl

/- English proof (translation)
The claim follows from `T2.kron_mu (S.toH h ⊥) (σ.WH h) ((R.posH h).frameOK ⊥) (((R.restr σ.T).posH (S.restr_ok h σ.T)).good ((S.restr σ.T).intDel_isLattice (S.restr_ok h σ.T) fun d => hD _)) hW0 (σ.kron t) (σ.split.symm.injective.comp hinj) (t * tᵀ) hdet (σ.kron_maj R h t)`.
-/
theorem Slice.mu_kron [IsTotallyComplex K] [Fintype A] (σ : S.Slice A) (R : S.Rat) (h : S.Ok)
    (hD : ∀ d, Submodule.IsLattice K (S.Del d)) (hW0 : (S.restr σ.T).intDel ≠ ⊥)
    {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (t : Matrix β A ℤ)
    (hinj : Function.Injective (T2.kronMap K (S.restr σ.T).EqFun t)) (hdet : 0 < (t * tᵀ).det) :
    (S.toH h ((T2.piL β (S.restr σ.T).intDel).map ((σ.kron t).restrictScalars (𝓞 K)))).mu =
      (σ.WH h).mu - Real.log (((t * tᵀ).det : ℤ) : ℝ) / (Fintype.card β : ℝ) :=
  T2.kron_mu (S.toH h ⊥) (σ.WH h) ((R.posH h).frameOK ⊥)
    (((R.restr σ.T).posH (S.restr_ok h σ.T)).good
      ((S.restr σ.T).intDel_isLattice (S.restr_ok h σ.T) fun d => hD _)) hW0 (σ.kron t)
    (σ.split.symm.injective.comp hinj) (t * tᵀ) hdet (σ.kron_maj R h t)

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF, rfl⟩`. Rewrite using `[σ.split_mem_intDel hN]`. Introduce `b`.

Use `show σ.split (σ.kron 1 F) b ∈ _`. Rewrite using `[σ.split_kron, T2.kronMap_one]`. Conclude with `hF b (Set.mem_univ b)`. Introduce `hφ`. Use `⟨σ.split φ, fun b _ => (σ.split_mem_intDel hN φ).1 hφ b, ?_⟩` and prove the remaining obligations.

Use `show σ.kron 1 (σ.split φ) = φ`. Unfold `Slice.kron`. Rewrite using `[T2.kronMap_one]`. Conclude with `σ.split.symm_apply_apply φ`.
-/
theorem Slice.map_kron_one [Fintype A] [DecidableEq A] (σ : S.Slice A)
    (hN : ∀ (b : A) (d : S.D), S.Del (b • d) = S.Del d) :
    (T2.piL A (S.restr σ.T).intDel).map ((σ.kron (1 : Matrix A A ℤ)).restrictScalars (𝓞 K)) = S.intDel := by
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    rw [σ.split_mem_intDel hN]
    intro b
    show σ.split (σ.kron 1 F) b ∈ _
    rw [σ.split_kron, T2.kronMap_one]
    exact hF b (Set.mem_univ b)
  · intro hφ
    refine ⟨σ.split φ, fun b _ => (σ.split_mem_intDel hN φ).1 hφ b, ?_⟩
    show σ.kron 1 (σ.split φ) = φ
    unfold Slice.kron
    rw [T2.kronMap_one]
    exact σ.split.symm_apply_apply φ

end GSD

namespace T2

variable {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => ⟨(Fintype.exists_ne_of_one_lt_card (h2 i) 1).choose, (Fintype.exists_ne_of_one_lt_card (h2 i) 1).choose_spec⟩⟩`.
-/
theorem nonempty_SzIdx (h2 : ∀ i, 1 < Fintype.card (G i)) : Nonempty (SzIdx G) := ⟨fun i => ⟨(Fintype.exists_ne_of_one_lt_card (h2 i) 1).choose,
    (Fintype.exists_ne_of_one_lt_card (h2 i) 1).choose_spec⟩⟩

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, q = m + 3` from `⟨q - 3, by omega⟩`. Establish `hG' : ∀ i, Fintype.card (G i) = m + 2` using `fun i => by rw [hG]; omega`. Rewrite using `[det_szGram, card_SzIdx]`. Simplify using `only [hG', show m + 2 - 1 = m + 1 by omega, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`. Use `push_cast`.

Rewrite using `[← pow_mul, Real.log_pow]`. Break down `Nat.eq_zero_or_pos (Fintype.card ι) with hf | hf` into its components or cases. Simplify using `[hf]`. Take `⟨e, he⟩ : ∃ e, Fintype.card ι = e + 1` from `⟨_, (Nat.succ_pred_eq_of_pos hf).symm⟩`. Rewrite using `[he, Nat.add_sub_cancel]`.

Use `push_cast`. Rewrite using `[show (m : ℝ) + 3 - 1 = m + 2 by ring, show (m : ℝ) + 3 - 2 = m + 1 by ring, pow_succ]`. Establish `h1 : (m : ℝ) + 1 ≠ 0` using `by positivity`. Establish `h2 : ((m : ℝ) + 1) ^ e ≠ 0` using `pow_ne_zero _ h1`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_det_szGram_div (q : ℕ) (hq : 3 ≤ q) (hG : ∀ i, Fintype.card (G i) = q - 1) :
    Real.log (((szGram G).det : ℤ) : ℝ) / (Fintype.card (SzIdx G) : ℝ) =
      (Fintype.card ι : ℝ) * Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 3 := ⟨q - 3, by omega⟩
  have hG' : ∀ i, Fintype.card (G i) = m + 2 := fun i => by rw [hG]; omega
  rw [det_szGram, card_SzIdx]
  simp only [hG', show m + 2 - 1 = m + 1 by omega, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  push_cast
  rw [← pow_mul, Real.log_pow]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hf | hf
  · simp [hf]
  · obtain ⟨e, he⟩ : ∃ e, Fintype.card ι = e + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hf).symm⟩
    rw [he, Nat.add_sub_cancel]
    push_cast
    rw [show (m : ℝ) + 3 - 1 = m + 2 by ring, show (m : ℝ) + 3 - 2 = m + 1 by ring, pow_succ]
    have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have h2 : ((m : ℝ) + 1) ^ e ≠ 0 := pow_ne_zero _ h1
    field_simp

end T2

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)] [MulAction (∀ i, G i) S.D] [SMulCommClass (∀ i, G i) S.G S.D]

/- English proof (translation)
Establish `: FiniteDimensional K (S.restr σ.T).EqFun` using `GSD.finiteDimensional_EqFun _ (S.restr_ok h σ.T)`. Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show σ.kron (T2.szVec G) F ∈ S.intDel`. Rewrite using `[σ.split_mem_intDel hN]`. Introduce `b`. Rewrite using `[σ.split_kron, T2.kronMap_apply]`. Conclude with `Submodule.sum_mem _ fun c _ => zsmul_mem (hF c (Set.mem_univ c)) _`.

Use `show σ.kron (T2.szVec G) F ∈ U`. Establish `h1 : σ.split (σ.kron (T2.szVec G) F) ∈ RamFun.ramFun K G (S.restr σ.T).EqFun`. Rewrite using `[σ.split_kron]`. Conclude with `T2.kron_szVec_mem G F`. Rewrite `h1` using `[← hU]`.

Take `⟨φ', hφ', he⟩` from `h1`. Rewrite using `[← σ.split.injective he]`. Conclude with `hφ'`. Introduce and unpack `⟨hφ, hφU⟩`. Establish `h1 : σ.split φ ∈ RamFun.ramFun K G (S.restr σ.T).EqFun`.

Rewrite using `[← hU]`. Conclude with `Submodule.mem_map_of_mem hφU`. Rewrite `h1` using `[← T2.range_kron_szVec]`. Take `⟨F, hF⟩` from `h1`. Use `⟨F, fun c _ => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← T2.kron_szVec_pt (K := K) G F c, hF]`. Conclude with `(σ.split_mem_intDel hN φ).1 hφ _`. Use `show σ.kron (T2.szVec G) F = φ`. Unfold `Slice.kron`. Rewrite using `[LinearMap.comp_apply, hF]`.

Conclude with `σ.split.symm_apply_apply φ`.
-/
theorem Slice.map_kron_sz (σ : S.Slice (∀ i, G i)) (h : S.Ok)
    (hN : ∀ (b : ∀ i, G i) (d : S.D), S.Del (b • d) = S.Del d) (U : Submodule K S.EqFun)
    (hU : U.map (σ.split : S.EqFun →ₗ[K] ((∀ i, G i) → (S.restr σ.T).EqFun)) =
      RamFun.ramFun K G (S.restr σ.T).EqFun) :
    (T2.piL (T2.SzIdx G) (S.restr σ.T).intDel).map ((σ.kron (T2.szVec G)).restrictScalars (𝓞 K)) =
      S.intDel ⊓ U.restrictScalars (𝓞 K) := by
  have : FiniteDimensional K (S.restr σ.T).EqFun := GSD.finiteDimensional_EqFun _ (S.restr_ok h σ.T)
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨?_, ?_⟩
    · show σ.kron (T2.szVec G) F ∈ S.intDel
      rw [σ.split_mem_intDel hN]
      intro b
      rw [σ.split_kron, T2.kronMap_apply]
      exact Submodule.sum_mem _ fun c _ => zsmul_mem (hF c (Set.mem_univ c)) _
    · show σ.kron (T2.szVec G) F ∈ U
      have h1 : σ.split (σ.kron (T2.szVec G) F) ∈ RamFun.ramFun K G (S.restr σ.T).EqFun := by
        rw [σ.split_kron]
        exact T2.kron_szVec_mem G F
      rw [← hU] at h1
      obtain ⟨φ', hφ', he⟩ := h1
      rw [← σ.split.injective he]
      exact hφ'
  · rintro ⟨hφ, hφU⟩
    have h1 : σ.split φ ∈ RamFun.ramFun K G (S.restr σ.T).EqFun := by
      rw [← hU]
      exact Submodule.mem_map_of_mem hφU
    rw [← T2.range_kron_szVec] at h1
    obtain ⟨F, hF⟩ := h1
    refine ⟨F, fun c _ => ?_, ?_⟩
    · rw [← T2.kron_szVec_pt (K := K) G F c, hF]
      exact (σ.split_mem_intDel hN φ).1 hφ _
    · show σ.kron (T2.szVec G) F = φ
      unfold Slice.kron
      rw [LinearMap.comp_apply, hF]
      exact σ.split.symm_apply_apply φ

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] in
/- English proof (translation)
Introduce `h0`. Apply `hS0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `φ hφ`. Establish `h1` using `(σ.split_mem_intDel hN φ).1 hφ`.

Rewrite `h1` using `[h0]`. Establish `h3 : σ.split φ = 0` using `funext fun b => (Submodule.mem_bot _).1 (h1 b)`. Rewrite using `[Submodule.mem_bot]`. Conclude with `σ.split.injective (h3.trans (map_zero _).symm)`.
-/
theorem Slice.slice_integral_delta_ne_bot (σ : S.Slice (∀ i, G i))
    (hN : ∀ (b : ∀ i, G i) (d : S.D), S.Del (b • d) = S.Del d) (hS0 : S.intDel ≠ ⊥) :
    (S.restr σ.T).intDel ≠ ⊥ := by
  intro h0
  apply hS0
  rw [eq_bot_iff]
  intro φ hφ
  have h1 := (σ.split_mem_intDel hN φ).1 hφ
  rw [h0] at h1
  have h3 : σ.split φ = 0 := funext fun b => (Submodule.mem_bot _).1 (h1 b)
  rw [Submodule.mem_bot]
  exact σ.split.injective (h3.trans (map_zero _).symm)

/- English proof (translation)
Establish `e2` using `σ.mu_kron R h hD (σ.slice_integral_delta_ne_bot hN hS0) (1 : Matrix (∀ i, G i) (∀ i, G i) ℤ) (by rw [T2.kronMap_one]; exact Function.injective_id) (by simp)`. Rewrite `e2` using `[σ.map_kron_one hN]`. Simplify `e2` using `only [Matrix.transpose_one, mul_one, Matrix.det_one, Int.cast_one, Real.log_one, zero_div, sub_zero]`.
-/
theorem Slice.mu_all [IsTotallyComplex K] (σ : S.Slice (∀ i, G i)) (R : S.Rat) (h : S.Ok)
    (hD : ∀ d, Submodule.IsLattice K (S.Del d))
    (hN : ∀ (b : ∀ i, G i) (d : S.D), S.Del (b • d) = S.Del d) (hS0 : S.intDel ≠ ⊥) :
    (S.toH h S.intDel).mu = (σ.WH h).mu := by
  have e2 := σ.mu_kron R h hD (σ.slice_integral_delta_ne_bot hN hS0) (1 : Matrix (∀ i, G i) (∀ i, G i) ℤ)
    (by rw [T2.kronMap_one]; exact Function.injective_id) (by simp)
  rw [σ.map_kron_one hN] at e2
  simpa only [Matrix.transpose_one, mul_one, Matrix.det_one, Int.cast_one, Real.log_one, zero_div, sub_zero] using e2

/- English proof (translation)
Use `T2.nonempty_SzIdx G h2` as an intermediate fact. Establish `e1` using `σ.mu_kron R h hD (σ.slice_integral_delta_ne_bot hN hS0) (T2.szVec G) (T2.kron_szVec_injective G) (by rw [T2.szVec_mul_transpose]; exact T2.det_szGram_pos G)`. Rewrite `e1` using `[σ.map_kron_sz h hN U hU, T2.szVec_mul_transpose]`. Rewrite using `[e1, σ.mu_all R h hD hN hS0]`.
-/
theorem Slice.mu_ram [IsTotallyComplex K] (σ : S.Slice (∀ i, G i)) (R : S.Rat) (h : S.Ok)
    (hD : ∀ d, Submodule.IsLattice K (S.Del d))
    (hN : ∀ (b : ∀ i, G i) (d : S.D), S.Del (b • d) = S.Del d) (hS0 : S.intDel ≠ ⊥)
    (h2 : ∀ i, 1 < Fintype.card (G i)) (U : Submodule K S.EqFun)
    (hU : U.map (σ.split : S.EqFun →ₗ[K] ((∀ i, G i) → (S.restr σ.T).EqFun)) =
      RamFun.ramFun K G (S.restr σ.T).EqFun) :
    (S.toH h (S.intDel ⊓ U.restrictScalars (𝓞 K))).mu = (S.toH h S.intDel).mu -
      Real.log (((T2.szGram G).det : ℤ) : ℝ) / (Fintype.card (T2.SzIdx G) : ℝ) := by
  have := T2.nonempty_SzIdx G h2
  have e1 := σ.mu_kron R h hD (σ.slice_integral_delta_ne_bot hN hS0) (T2.szVec G) (T2.kron_szVec_injective G)
    (by rw [T2.szVec_mul_transpose]; exact T2.det_szGram_pos G)
  rw [σ.map_kron_sz h hN U hU, T2.szVec_mul_transpose] at e1
  rw [e1, σ.mu_all R h hD hN hS0]

end GSD

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

open Classical in

/- English proof (translation)
Set `_ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ` to `fun P => fintypeResU P.1`. Use extensionality with `F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, hφ, rfl⟩`. Use `(Submodule.mem_iInf _).2 fun P => ?_` and prove the remaining obligations.

Use `show RamFun.nmF X.K _ P (σ.split φ) = 0`. Rewrite using `[← split_NmOp, (mem_ColRamV W Ch u j φ).1 hφ P, map_zero]`. Introduce `hF`. Use `⟨σ.split.symm F, ?_, σ.split.apply_symm_apply F⟩` and prove the remaining obligations. Use `show σ.split.symm F ∈ ColRamV W Ch u j`.

Rewrite using `[mem_ColRamV]`. Introduce `P`. Apply `σ.split.injective` to reduce the goal to its premises. Rewrite using `[split_NmOp, σ.split.apply_symm_apply, map_zero]`. Conclude with `(Submodule.mem_iInf _).1 hF P`.
-/
theorem map_split_ColRamV (u : Pr.Word) (j : ℕ) (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u))) :
    letI : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
    (ColRamV W Ch u j).map (σ.split : ColV W Ch u j →ₗ[X.K] _) =
      RamFun.ramFun X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
        ((colGSD W Ch u j).restr σ.T).EqFun := by
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  ext F
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine (Submodule.mem_iInf _).2 fun P => ?_
    show RamFun.nmF X.K _ P (σ.split φ) = 0
    rw [← split_NmOp, (mem_ColRamV W Ch u j φ).1 hφ P, map_zero]
  · intro hF
    refine ⟨σ.split.symm F, ?_, σ.split.apply_symm_apply F⟩
    show σ.split.symm F ∈ ColRamV W Ch u j
    rw [mem_ColRamV]
    intro P
    apply σ.split.injective
    rw [split_NmOp, σ.split.apply_symm_apply, map_zero]
    exact (Submodule.mem_iInf _).1 hF P

open Classical in

/- English proof (translation)
Set `_ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ` to `fun P => fintypeResU P.1`. Rewrite using `[latH_maj, σ.ipAt_split (colRat W Ch hX u j) (colOk W Ch hX u j)]`. Conclude with `Finset.sum_congr rfl fun c _ => (((colRat W Ch hX u j).restr σ.T).maj_eq _ v _ _).symm`.
-/
theorem col_split_maj (u : Pr.Word) (j : ℕ) (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u)))
    (v : InfinitePlace X.K) (φ ψ : ColV W Ch u j) :
    letI : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
    majAt (latH W Ch hX u j).b (latH W Ch hX u j).X v φ ψ =
      ∑ c : DiaG X.E (Pr.vT u), majAt (σ.WH (colOk W Ch hX u j)).b (σ.WH (colOk W Ch hX u j)).X v
        (σ.split φ c) (σ.split ψ c) := by
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  rw [latH_maj, σ.ipAt_split (colRat W Ch hX u j) (colOk W Ch hX u j)]
  exact Finset.sum_congr rfl fun c _ => (((colRat W Ch hX u j).restr σ.T).maj_eq _ v _ _).symm

/- English proof (translation)
The claim follows from `σ.split_mem_intDel (colDel_dia W Ch u j) φ`.
-/
theorem col_split_mem (u : Pr.Word) (j : ℕ) (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u))) (φ : ColV W Ch u j) :
    φ ∈ ColL W Ch u j ↔ ∀ c, σ.split φ c ∈ ((colGSD W Ch u j).restr σ.T).intDel :=
  σ.split_mem_intDel (colDel_dia W Ch u j) φ

include hX in
/- English proof (translation)
Introduce `h0`. Establish `h1` using `(Mu0H_good W Ch hX u).2.2`. Establish `h2 : (Mu0H W Ch hX u).L = ⊥` using `h0`. Rewrite `h1` using `[h2]`. Establish `h3` using `finrank_MfV_pos W Ch hX hPr hbig u`.

Establish `h4 : (⊤ : Submodule X.K (MfV W Ch u)) = ⊥`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Rewrite `h3` using `[← finrank_top X.K (MfV W Ch u), h4, finrank_bot]`. Conclude with `lt_irrefl _ h3`.
-/
theorem integral_delta_ne_bot (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (colGSD W Ch u 0).intDel ≠ ⊥ := by
  intro h0
  have h1 := (Mu0H_good W Ch hX u).2.2
  have h2 : (Mu0H W Ch hX u).L = ⊥ := h0
  rw [h2] at h1
  have h3 := finrank_MfV_pos W Ch hX hPr hbig u
  have h4 : (⊤ : Submodule X.K (MfV W Ch u)) = ⊥ := by
    rw [← h1]
    simp
  rw [← finrank_top X.K (MfV W Ch u), h4, finrank_bot] at h3
  exact lt_irrefl _ h3

open Classical in

/- English proof (translation)
Use `hX.cplxK` as an intermediate fact. Set `_ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ` to `fun P => fintypeResU P.1`. Conclude with `σ.mu_all (colRat W Ch hX u 0) (colOk W Ch hX u 0) (thl_colDel_isLattice W Ch u 0) (colDel_dia W Ch u 0) (integral_delta_ne_bot W Ch hX hPr hbig u)`.
-/
theorem Mu0H_mu_eq (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (σ : (colGSD W Ch u 0).Slice (DiaG X.E (Pr.vT u))) :
    (Mu0H W Ch hX u).mu = (σ.WH (colOk W Ch hX u 0)).mu := by
  have := hX.cplxK
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  exact σ.mu_all (colRat W Ch hX u 0) (colOk W Ch hX u 0) (thl_colDel_isLattice W Ch u 0)
    (colDel_dia W Ch u 0) (integral_delta_ne_bot W Ch hX hPr hbig u)

open Classical in

/- English proof (translation)
Use `hX.cplxK` as an intermediate fact. Set `_ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ` to `fun P => fintypeResU P.1`. Take `⟨σ⟩` from `(colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)`. Establish `hcard : ∀ P : {P // P ∈ Pr.vT u}, Fintype.card (𝓞 X.E ⧸ P.1.asIdeal)ˣ = Pr.T u - 1` using `fun P => by`. Rewrite using `[← Nat.card_eq_fintype_card, card_resU hPr u P]`.

Establish `hS0` using `integral_delta_ne_bot W Ch hX hPr hbig u`. Establish `key` using `σ.mu_ram (colRat W Ch hX u 0) (colOk W Ch hX u 0) (thl_colDel_isLattice W Ch u 0) (colDel_dia W Ch u 0) hS0 (fun P => by rw [hcard P]; omega) (MramV W Ch u) (map_split_ColRamV W Ch u 0 σ)`. Rewrite `key` using `[T2.log_det_szGram_div _ (Pr.T u) hT hcard, Fintype.card_coe, hPr.vT_card u]`. Rewrite using `[(MramH_numbers W Ch hX u).1]`. Conclude with `key`.
-/
theorem MramH_mu (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (MramH W Ch hX u).mu =
      (Mu0H W Ch hX u).mu - (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2) := by
  have := hX.cplxK
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  obtain ⟨σ⟩ := (colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)
  have hcard : ∀ P : {P // P ∈ Pr.vT u}, Fintype.card (𝓞 X.E ⧸ P.1.asIdeal)ˣ = Pr.T u - 1 := fun P => by
    rw [← Nat.card_eq_fintype_card, card_resU hPr u P]
  have hS0 := integral_delta_ne_bot W Ch hX hPr hbig u
  have key := σ.mu_ram (colRat W Ch hX u 0) (colOk W Ch hX u 0) (thl_colDel_isLattice W Ch u 0)
    (colDel_dia W Ch u 0) hS0 (fun P => by rw [hcard P]; omega) (MramV W Ch u) (map_split_ColRamV W Ch u 0 σ)
  rw [T2.log_det_szGram_div _ (Pr.T u) hT hcard, Fintype.card_coe, hPr.vT_card u] at key
  rw [(MramH_numbers W Ch hX u).1]
  exact key

/- English proof (translation)
Establish `hT' : (3 : ℝ) ≤ T` using `by exact_mod_cast (hT : 3 ≤ T)`. Apply `div_nonneg` to reduce the goal to its premises. Apply `Real.log_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_ratio_nonneg {T : ℕ} (hT : 2 < T) : 0 ≤ Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) := by
  have hT' : (3 : ℝ) ≤ T := by exact_mod_cast (hT : 3 ≤ T)
  apply div_nonneg
  · apply Real.log_nonneg
    linarith
  · linarith

/- English proof (translation)
Rewrite using `[MramH_mu W Ch hX hPr hbig u hT]`. Establish `h` using `log_ratio_nonneg hT`. Establish `hf : (0 : ℝ) ≤ X.f` using `Nat.cast_nonneg _`. Establish `: 0 ≤ (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2)`. Rewrite using `[mul_div_assoc]`.

Conclude with `mul_nonneg hf h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem MramH_mu_le (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (MramH W Ch hX u).mu ≤ (Mu0H W Ch hX u).mu := by
  rw [MramH_mu W Ch hX hPr hbig u hT]
  have h := log_ratio_nonneg hT
  have hf : (0 : ℝ) ≤ X.f := Nat.cast_nonneg _
  have : 0 ≤ (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2) := by
    rw [mul_div_assoc]
    exact mul_nonneg hf h
  linarith

/- English proof (translation)
Rewrite using `[MramH_mu W Ch hX hPr hbig u hT]`. Establish `hT' : (3 : ℝ) ≤ Pr.T u` using `by exact_mod_cast (hT : 3 ≤ Pr.T u)`. Establish `hlog : Real.log ((Pr.T u : ℝ) - 1) ≤ (Pr.T u : ℝ) - 2`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < (Pr.T u : ℝ) - 1 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpos : (0 : ℝ) < (Pr.T u : ℝ) - 2` using `by linarith`. Establish `hf : (0 : ℝ) ≤ X.f` using `Nat.cast_nonneg _`. Establish `: (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2) ≤ X.f`. Rewrite using `[div_le_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Mu0H_sub_MramH_le (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (Mu0H W Ch hX u).mu - (MramH W Ch hX u).mu ≤ (X.f : ℝ) := by
  rw [MramH_mu W Ch hX hPr hbig u hT]
  have hT' : (3 : ℝ) ≤ Pr.T u := by exact_mod_cast (hT : 3 ≤ Pr.T u)
  have hlog : Real.log ((Pr.T u : ℝ) - 1) ≤ (Pr.T u : ℝ) - 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (Pr.T u : ℝ) - 1 by linarith)
    linarith
  have hpos : (0 : ℝ) < (Pr.T u : ℝ) - 2 := by linarith
  have hf : (0 : ℝ) ≤ X.f := Nat.cast_nonneg _
  have : (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2) ≤ X.f := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨card_MramH_eq W Ch hX hPr hbig u hT, MramH_mu W Ch hX hPr hbig u hT, MramH_muMax_le W Ch hX hPr hbig u hT⟩`.
-/
theorem ramified_slope_clauses (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (hT : 2 < Pr.T u) :
    (Fintype.card (MramH W Ch hX u).ι : ℝ) =
      (Fintype.card (Mu0H W Ch hX u).ι : ℝ) * (1 - 1 / ((Pr.T u : ℝ) - 1)) ^ X.f ∧
    Formalism.HN.muDef (MramH W Ch hX u).b (MramH W Ch hX u).X (MramH W Ch hX u).L =
      Formalism.HN.muDef (Mu0H W Ch hX u).b (Mu0H W Ch hX u).X (Mu0H W Ch hX u).L -
        (X.f : ℝ) * Real.log ((Pr.T u : ℝ) - 1) / ((Pr.T u : ℝ) - 2) ∧
    Formalism.HN.muMaxDef (MramH W Ch hX u).b (MramH W Ch hX u).X (MramH W Ch hX u).L ≤
      Formalism.HN.muMaxDef (Mu0H W Ch hX u).b (Mu0H W Ch hX u).X (Mu0H W Ch hX u).L :=
  ⟨card_MramH_eq W Ch hX hPr hbig u hT, MramH_mu W Ch hX hPr hbig u hT, MramH_muMax_le W Ch hX hPr hbig u hT⟩

end Cols

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℚ Formalism.L2.Host.Qb` using `AlgebraicClosure.isAlgebraic ℚ`. Set `ι : Formalism.L2.Host.Qb →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Formalism.L2.Host.Qb)).toRingHom`. Establish `hX` using `quadFields_ok 1 ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic one_pos`. Establish `hPr` using `gaussianPrimesSmall_ok ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic`. Establish `hbig` using `gaussianSmallPrime_gt_twice_rank ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic`.

Establish `hT : 2 < (gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).T ()` using `by show 2 < 14145788201`. Evaluate the numerical expressions. Establish `hf : (gaussFields ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).f = 1` using `gauss_f ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic`. Set `Ch : Chars (gaussFields ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic) (gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic) Examples₂.R0.m` to `⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1, fun _ => 1⟩`. Establish `h1` using `MramH_mu (exampleWeights _ _) Ch hX hPr hbig () hT`.

Establish `h2 : (((gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).T () : ℕ) : ℝ) = 14145788201` using `by show ((14145788201 : ℕ) : ℝ) = 14145788201`. Evaluate the numerical expressions. Rewrite `h1` using `[hf, h2]`. Evaluate the numerical expressions using `at h1`. Use `⟨_, _, exampleWeights _ _, Ch, hX, (), h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1]`. Establish `h3 : 0 < Real.log 14145788200 / 14145788199` using `div_pos (Real.log_pos (by norm_num)) (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ramified_slope_nonvacuous : ∃ (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word Examples₂.R0) (Ch : Chars X Pr Examples₂.R0.m)
    (hX : X.Ok) (u : Pr.Word),
      (MramH W Ch hX u).mu = (Mu0H W Ch hX u).mu - Real.log 14145788200 / 14145788199 ∧
      (MramH W Ch hX u).mu < (Mu0H W Ch hX u).mu := by
  have : Algebra.IsAlgebraic ℚ Formalism.L2.Host.Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Formalism.L2.Host.Qb →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Formalism.L2.Host.Qb)).toRingHom
  have hX := quadFields_ok 1 ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic one_pos
  have hPr := gaussianPrimesSmall_ok ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic
  have hbig := gaussianSmallPrime_gt_twice_rank ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic
  have hT : 2 < (gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).T () := by
    show 2 < 14145788201
    norm_num
  have hf : (gaussFields ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).f = 1 := gauss_f ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic
  let Ch : Chars (gaussFields ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic)
      (gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic) Examples₂.R0.m :=
    ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1, fun _ => 1⟩
  have h1 := MramH_mu (exampleWeights _ _) Ch hX hPr hbig () hT
  have h2 : (((gaussianPrimesSmall ι (Formalism.L2.Host.cycQ 780) gaussian_field_le_cyclotomic).T () : ℕ) : ℝ) = 14145788201 := by
    show ((14145788201 : ℕ) : ℝ) = 14145788201
    norm_num
  rw [hf, h2] at h1
  norm_num at h1
  refine ⟨_, _, exampleWeights _ _, Ch, hX, (), h1, ?_⟩
  rw [h1]
  have h3 : 0 < Real.log 14145788200 / 14145788199 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  linarith

end Formalism.L2.Col
