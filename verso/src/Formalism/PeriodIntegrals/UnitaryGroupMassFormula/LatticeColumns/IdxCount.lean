import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.UnitaryLevelClosureSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Matrix

variable {D : D7}

def KvA (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).comap
    (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J).subtype

def KvH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (KvA X v).subgroupOf _

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Unfold `stabT at hg ⊢`. Rewrite `hg`, the goal using `[MulAction.mem_stabilizer_iff]`. Unfold `haMap ratTup at *`. Use function extensionality and compare the values at `b i`. Establish `hb` using `congrFun (congrFun hg b) i`.

Simplify using `only [HSMul.hSMul, SMul.smul] at hb ⊢`. Simplify using `only [actTup] at hb`. Establish `hv : (fun j => inclR R' (X0 b j)) = fun j => tensMap (E` using `E) φ (inclR R (X0 b j)) := by`. Use function extensionality and compare the values at `j`. Rewrite using `[tensMap_inclR]`.

Use `show ((Formalism.UG.bc (tensMap (E := E) φ) (HA.mat R σ J g) : GL (Fin n) (R' ⊗[F] E)) : Matrix (Fin n) (Fin n) (R' ⊗[F] E)).mulVec (fun j => inclR R' (X0 b j)) i = inclR R' (X0 b i)`. Rewrite using `[hv, ← tensMap_inclR (E := E) φ (X0 b i), ← hb, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem haMap_mem_stabT {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') {a : ℕ} (X0 : Fin a → Fin n → E) (g : HA R σ J) (hg : g ∈ stabT R σ J X0) :
    haMap σ J φ g ∈ stabT R' σ J X0 := by
  unfold stabT at hg ⊢
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  unfold haMap ratTup at *
  funext b i
  have hb := congrFun (congrFun hg b) i
  dsimp only [HSMul.hSMul, SMul.smul] at hb ⊢
  simp only [actTup] at hb
  have hv : (fun j => inclR R' (X0 b j)) = fun j => tensMap (E := E) φ (inclR R (X0 b j)) := by
    funext j
    rw [tensMap_inclR]
  show ((Formalism.UG.bc (tensMap (E := E) φ) (HA.mat R σ J g) : GL (Fin n) (R' ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (R' ⊗[F] E)).mulVec (fun j => inclR R' (X0 b j)) i = inclR R' (X0 b i)
  rw [hv, ← tensMap_inclR (E := E) φ (X0 b i), ← hb, RingHom.map_mulVec]
  rfl

end Gen

def piH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) →* Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X u) :=
  ((haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v)).comp
    (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)).subtype).codRestrict _
    (fun h => haMap_mem_stabT X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) _ _ h.2)

def unitaryLevelLocalComponent (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (unitaryLevelClosureSubgroup X hb u).map (piH X u v)

def lIdxH (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : ℕ :=
  (unitaryLevelLocalComponent X hb u p.1).relIndex (KvH X u p.1)

def IdxProdH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    (unitaryLevelClosureSubgroup X hb u).relIndex (KHg X u) = ∏ p : TypX X, lIdxH X hb u p

def LocRedH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
    ∃ ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)), Function.Surjective ρ ∧
      ρ.ker ≤ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ∧
      Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ) = ukC D.R.k (gOf p)

/- English proof (translation)
Unfold `gOf`. Use `split_ifs`. Conclude with `D.host.g_prime 0`. Conclude with `D.host.g_prime 1`.
-/
theorem gOf_prime' (X : HidaSetting D) (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

/- English proof (translation)
Use `haveI : Fact (gOf p).Prime := ⟨gOf_prime' X p⟩`. Use `haveI : NeZero (gOf p) := ⟨(gOf_prime' X p).ne_zero⟩`. Establish `hidx : (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ).index = lIdxH X hb u p` using `Subgroup.index_map_eq _ hs hk`. Establish `hmul` using `Subgroup.card_mul_index (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ)`. Establish `hpos : 0 < Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ)` using `Nat.card_pos`.

Rewrite `hmul` using `[hidx, hc]`. Rewrite `hpos` using `[hc]`. Establish `hgl : Nat.card (GL (Fin D.R.k) (ZMod (gOf p))) = glkC D.R.k (gOf p)`. Unfold `glkC`. Use `first`.

Consider the case `rfl`. Consider the case `(rw [Matrix.card_GL_field, ZMod.card]; done)`. Consider the case `done`. Rewrite `hmul` using `[hgl]`. Rewrite using `[eq_div_iff (by exact_mod_cast hpos.ne'), ← hmul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lIdxH_eq_of_red (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p))) (hs : Function.Surjective ρ)
    (hk : ρ.ker ≤ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1))
    (hc : Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ) = ukC D.R.k (gOf p)) :
    (lIdxH X hb u p : ℝ) = (glkC D.R.k (gOf p) : ℝ) / (ukC D.R.k (gOf p) : ℝ) := by
  classical
  haveI : Fact (gOf p).Prime := ⟨gOf_prime' X p⟩
  haveI : NeZero (gOf p) := ⟨(gOf_prime' X p).ne_zero⟩
  have hidx : (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ).index = lIdxH X hb u p :=
    Subgroup.index_map_eq _ hs hk
  have hmul := Subgroup.card_mul_index (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ)
  have hpos : 0 < Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ) := Nat.card_pos
  rw [hidx, hc] at hmul
  rw [hc] at hpos
  have hgl : Nat.card (GL (Fin D.R.k) (ZMod (gOf p))) = glkC D.R.k (gOf p) := by
    unfold glkC
    first
      | rfl
      | (rw [Matrix.card_GL_field, ZMod.card]; done)
      | done
  rw [hgl] at hmul
  rw [eq_div_iff (by exact_mod_cast hpos.ne'), ← hmul]
  push_cast
  ring

/- English proof (translation)
Introduce `D X hb hK u hM hL`. Rewrite using `[h1 X hb hK u hM hL]`. Use `push_cast`. Use `Finset.prod_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Take `⟨ρ, hs, hk, hc⟩` from `h2 X hb hK u hM hL p`.

Conclude with `lIdxH_eq_of_red X hb u p ρ hs hk hc`.
-/
theorem idxCountStep_of (h1 : IdxProdH) (h2 : LocRedH) : IdxCountStep := by
  intro D X hb hK u hM hL
  rw [h1 X hb hK u hM hL]
  push_cast
  refine Finset.prod_congr rfl (fun p _ => ?_)
  obtain ⟨ρ, hs, hk, hc⟩ := h2 X hb hK u hM hL p
  exact lIdxH_eq_of_red X hb u p ρ hs hk hc

end PIW.MassDataColumns
