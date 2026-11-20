import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHomStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExactStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaEquivariantFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalMatrixCoprimeDecompositionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.Fam

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Crv.Inhab

variable {K : Type} [Field K] (C : ACurve K) {d : ℕ}

def colLat (i : C.I) (g : Matrix (Fin d) (Fin d) K) : AddSubgroup (Fin d → K) :=
  (trivLat C d i).map (Matrix.toLin' g).toAddMonoidHom

def stdH (d : ℕ) (i : C.I) : AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (trivLat C d i).prod (trivLat C d i)

def imLat (i : C.I) (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) :
    AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (stdH C d i).map T.toAddMonoidHom

/- English proof (translation)
Simplify using `[colLat, AddSubgroup.mem_map]`.
-/
theorem mem_colLat {i : C.I} {g : Matrix (Fin d) (Fin d) K} {x : Fin d → K} :
    x ∈ colLat C i g ↔ ∃ w ∈ trivLat C d i, g.mulVec w = x := by
  simp [colLat, AddSubgroup.mem_map]

/- English proof (translation)
Simplify using `[imLat, AddSubgroup.mem_map]`.
-/
theorem mem_imLat {i : C.I} {T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)}
    {y : (Fin d → K) × (Fin d → K)} : y ∈ imLat C i T ↔ ∃ w ∈ stdH C d i, T w = y := by
  simp [imLat, AddSubgroup.mem_map]

/- English proof (translation)
The claim follows from `AddSubgroup.mem_prod`.
-/
theorem mem_stdH {i : C.I} {y : (Fin d → K) × (Fin d → K)} :
    y ∈ stdH C d i ↔ y.1 ∈ trivLat C d i ∧ y.2 ∈ trivLat C d i := AddSubgroup.mem_prod

/- English proof (translation)
Rewrite using `[mem_colLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite using `[Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]`. Conclude with `hw`.

Introduce `h`. Conclude with `⟨g'.mulVec x, h, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩`.
-/
theorem mem_colLat_iff {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    {x : Fin d → K} : x ∈ colLat C i g ↔ ∀ j, C.v i (g'.mulVec x j) ≤ 1 := by
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]
    exact hw
  · intro h
    exact ⟨g'.mulVec x, h, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

def frame {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    Module.Basis (Fin d) K (Fin d → K) :=
  (Pi.basisFun K (Fin d)).map (Matrix.toLin'OfInv h₂ h₁)

/- English proof (translation)
Simplify using `[frame, Matrix.toLin'OfInv]`.
-/
theorem frame_repr {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (x : Fin d → K) (q : Fin d) : (frame h₁ h₂).repr x q = g'.mulVec x q := by
  simp [frame, Matrix.toLin'OfInv]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `[frame, Matrix.toLin'OfInv]`.
-/
theorem frame_apply {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (q : Fin d) : frame h₁ h₂ q = fun r => g r q := by
  funext r
  simp [frame, Matrix.toLin'OfInv]

/- English proof (translation)
Introduce `x` and use `by rw [mem_colLat_iff C h₁ h₂] simp only [frame_repr]`.
-/
theorem isLatOf_frame (i : C.I) {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    IsLatOf C i (frame h₁ h₂) (colLat C i g) := fun x => by
  rw [mem_colLat_iff C h₁ h₂]
  simp only [frame_repr]

/- English proof (translation)
Set `e : ι ≃ Fin (Module.finrank K V)` to `Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm`. Establish `re : ∀ (c : Module.Basis ι K V) (i : C.I) (L' : AddSubgroup V), (∀ x, x ∈ L' ↔ ∀ q, C.v i (c.repr x q) ≤ 1) → IsLatOf C i (c.reindex e) L'`. Introduce `c i L' h x`. Rewrite using `[h]`. Simplify using `only [Module.Basis.repr_reindex_apply]`.

Conclude with `⟨fun H q => H _, fun H q => by simpa using H (e q)⟩`. Conclude with `⟨fun i => ⟨_, re _ i _ (hb i)⟩, b₀.reindex e, hfin.subset fun i hi h => hi (re _ _ _ h)⟩`.
-/
theorem isBun_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : C.I → Module.Basis ι K V) (b₀ : Module.Basis ι K V) (L : C.I → AddSubgroup V)
    (hb : ∀ i x, x ∈ L i ↔ ∀ q, C.v i ((b i).repr x q) ≤ 1)
    (hfin : {i | ¬ ∀ x, x ∈ L i ↔ ∀ q, C.v i (b₀.repr x q) ≤ 1}.Finite) : IsBun C L := by
  let e : ι ≃ Fin (Module.finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  have re : ∀ (c : Module.Basis ι K V) (i : C.I) (L' : AddSubgroup V),
      (∀ x, x ∈ L' ↔ ∀ q, C.v i (c.repr x q) ≤ 1) → IsLatOf C i (c.reindex e) L' := by
    intro c i L' h x
    rw [h]
    simp only [Module.Basis.repr_reindex_apply]
    exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩
  exact ⟨fun i => ⟨_, re _ i _ (hb i)⟩, b₀.reindex e,
    hfin.subset fun i hi h => hi (re _ _ _ h)⟩

def IntM (i : C.I) (M : Matrix (Fin d) (Fin d) K) : Prop := ∀ a b, C.v i (M a b) ≤ 1

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_colLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `mulVec_mem_trivLat C hg hw`.

Introduce `hx`. Conclude with `⟨g'.mulVec x, mulVec_mem_trivLat C hg' hx, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩`.
-/
theorem colLat_eq_triv {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (hg : IntM C i g) (hg' : IntM C i g') : colLat C i g = trivLat C d i := by
  ext x
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_trivLat C hg hw
  · intro hx
    exact ⟨g'.mulVec x, mulVec_mem_trivLat C hg' hx, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

/- English proof (translation)
Use `isBun_frames C (fun i => frame (h₁ i) (h₂ i)) (Pi.basisFun K (Fin d)) _ (fun i x => (isLatOf_frame C i (h₁ i) (h₂ i)) x) (hfin.subset fun i hi h => hi ?_)` and prove the remaining obligations. Introduce `x`. Rewrite using `[colLat_eq_triv C (h₁ i) (h₂ i) h.1 h.2]`. Simplify using `[mem_trivLat]`.
-/
theorem isBun_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) (hfin : {i | ¬ (IntM C i (g i) ∧ IntM C i (g' i))}.Finite) :
    IsBun C fun i => colLat C i (g i) := by
  refine isBun_frames C (fun i => frame (h₁ i) (h₂ i)) (Pi.basisFun K (Fin d)) _
    (fun i x => (isLatOf_frame C i (h₁ i) (h₂ i)) x) (hfin.subset fun i hi h => hi ?_)
  intro x
  rw [colLat_eq_triv C (h₁ i) (h₂ i) h.1 h.2]
  simp [mem_trivLat]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `t₁ : (g' i).transpose * (g i).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, h₁, Matrix.transpose_one]`. Establish `t₂ : (g i).transpose * (g' i).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, h₂, Matrix.transpose_one]`.

Use `DegDual.isLatOf_dual C (fun i => colLat C i (g i)) (dotProductBilin K K) i (frame (h₁ i) (h₂ i)) (frame t₁ t₂) (fun y q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))` as an intermediate fact. Use extensionality with `y`. Rewrite using `[show dotDual C (fun i => colLat C i (g i)) i = dualLat C _ (dotProductBilin K K) i from rfl, this y, (isLatOf_frame C i t₁ t₂) y]`. Rewrite using `[frame_repr, frame_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.transpose_apply]`.
-/
theorem dotDual_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) :
    dotDual C (fun i => colLat C i (g i)) = fun i => colLat C i (g' i).transpose := by
  funext i
  have t₁ : (g' i).transpose * (g i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : (g i).transpose * (g' i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have := DegDual.isLatOf_dual C (fun i => colLat C i (g i)) (dotProductBilin K K) i
    (frame (h₁ i) (h₂ i)) (frame t₁ t₂) (fun y q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [show dotDual C (fun i => colLat C i (g i)) i = dualLat C _ (dotProductBilin K K) i from rfl,
      this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_repr, frame_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `e : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M` using `fun M => rfl`. Establish `t₁ : (g i).map (· ^ p) * (g' i).map (· ^ p) = 1`. Rewrite using `[e, e, ← map_mul, h₁, map_one]`. Establish `t₂ : (g' i).map (· ^ p) * (g i).map (· ^ p) = 1`.

Rewrite using `[e, e, ← map_mul, h₂, map_one]`. Use `DegFrob.isLatOf_frob C p (fun i => colLat C i (g i)) i (frame (h₁ i) (h₂ i)) (frame t₁ t₂) (fun q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))` as an intermediate fact. Use extensionality with `y`. Rewrite using `[this y, (isLatOf_frame C i t₁ t₂) y]`. Rewrite using `[frame_apply, frame_apply]`.

Both sides reduce to the same expression.
-/
theorem frobLat_colLat (p : ℕ) [Fact p.Prime] [CharP K p] (g g' : C.I → Matrix (Fin d) (Fin d) K)
    (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1) :
    frobLat C p (fun i => colLat C i (g i)) = fun i => colLat C i ((g i).map (· ^ p)) := by
  funext i
  have e : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M := fun M => rfl
  have t₁ : (g i).map (· ^ p) * (g' i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₁, map_one]
  have t₂ : (g' i).map (· ^ p) * (g i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₂, map_one]
  have := DegFrob.isLatOf_frob C p (fun i => colLat C i (g i)) i (frame (h₁ i) (h₂ i)) (frame t₁ t₂)
    (fun q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_apply, frame_apply]
    rfl

local notation "VV" K:max d:max => ((Fin d → K) × (Fin d → K))

def stdBasis (K : Type) [Field K] (d : ℕ) : Module.Basis (Fin d ⊕ Fin d) K (VV K d) :=
  (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))

/- English proof (translation)
Rewrite using `[mem_stdH, Sum.forall]`. Simplify using `[stdBasis, mem_trivLat]`.
-/
theorem forall_stdBasis (i : C.I) (y : VV K d) :
    (∀ q, C.v i ((stdBasis K d).repr y q) ≤ 1) ↔ y ∈ stdH C d i := by
  rw [mem_stdH, Sum.forall]
  simp [stdBasis, mem_trivLat]

/- English proof (translation)
Use `isBun_frames C (fun i => (stdBasis K d).map (LinearEquiv.ofBijective (T i) (hT i))) (stdBasis K d) _ (fun i x => ?_) (hfin.subset fun i hi h => hi ?_)` and prove the remaining obligations. Rewrite using `[mem_imLat]`. Simplify using `only [Module.Basis.map_repr, LinearEquiv.trans_apply]`. Rewrite using `[forall_stdBasis]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, rfl⟩`. Establish `: (LinearEquiv.ofBijective (T i) (hT i)).symm (T i w) = w` using `(LinearEquiv.ofBijective (T i) (hT i)).symm_apply_apply w`. Rewrite using `[this]` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨_, h, (LinearEquiv.ofBijective (T i) (hT i)).apply_symm_apply x⟩`.

Introduce `x`. Rewrite using `[forall_stdBasis]`. Conclude with `iff_of_eq (congrArg (x ∈ ·) h)`.
-/
theorem isBun_imLat (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (hfin : {i | imLat C i (T i) ≠ stdH C d i}.Finite) : IsBun C fun i => imLat C i (T i) := by
  refine isBun_frames C (fun i => (stdBasis K d).map (LinearEquiv.ofBijective (T i) (hT i)))
    (stdBasis K d) _ (fun i x => ?_) (hfin.subset fun i hi h => hi ?_)
  · rw [mem_imLat]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [forall_stdBasis]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (LinearEquiv.ofBijective (T i) (hT i)).symm (T i w) = w :=
        (LinearEquiv.ofBijective (T i) (hT i)).symm_apply_apply w
      rwa [this]
    · intro h
      exact ⟨_, h, (LinearEquiv.ofBijective (T i) (hT i)).apply_symm_apply x⟩
  · intro x
    rw [forall_stdBasis]
    exact iff_of_eq (congrArg (x ∈ ·) h)

/- English proof (translation)
Rewrite `hw`, the goal using `[mem_stdH]`. Rewrite using `[transH_apply]`. Conclude with `⟨mulVec_mem_trivLat C hg hw.1, mulVec_mem_trivLat C (fun a b => hg' b a) (add_mem hw.2 (mulVec_mem_trivLat C (fun a b => hl b a) hw.1))⟩`.
-/
theorem transH_mem_stdH {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1))
    {w : VV K d} (hw : w ∈ stdH C d i) : transH φ ψ lam w ∈ stdH C d i := by
  rw [mem_stdH] at hw ⊢
  rw [transH_apply]
  exact ⟨mulVec_mem_trivLat C hg hw.1, mulVec_mem_trivLat C (fun a b => hg' b a)
    (add_mem hw.2 (mulVec_mem_trivLat C (fun a b => hl b a) hw.1))⟩

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_imLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `transH_mem_stdH C hg hg' hl hw`.

Introduce `hy`. Establish `hy'` using `(mem_stdH C).1 hy`. Establish `a₁` using `mulVec_mem_trivLat C hg' hy'.1`. Establish `a₂` using `mulVec_mem_trivLat C (fun a b => hl b a) a₁`. Establish `a₃` using `mulVec_mem_trivLat C (fun a b => hg b a) hy'.2`.

Use `⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 - (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)), (mem_stdH C).2 ⟨a₁, sub_mem a₃ a₂⟩, ?_⟩` and prove the remaining obligations. Establish `t : (lin ψ 1).transpose * (lin φ 1).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, h₁, Matrix.transpose_one]`. Rewrite using `[transH_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]`. Simplify using `only [sub_add_cancel, Matrix.mulVec_mulVec, t, Matrix.one_mulVec]`.
-/
theorem imLat_transH_eq {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (h₁ : lin φ 1 * lin ψ 1 = 1) (h₂ : lin ψ 1 * lin φ 1 = 1)
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1)) :
    imLat C i (transH φ ψ lam) = stdH C d i := by
  ext y
  rw [mem_imLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact transH_mem_stdH C hg hg' hl hw
  · intro hy
    have hy' := (mem_stdH C).1 hy
    have a₁ := mulVec_mem_trivLat C hg' hy'.1
    have a₂ := mulVec_mem_trivLat C (fun a b => hl b a) a₁
    have a₃ := mulVec_mem_trivLat C (fun a b => hg b a) hy'.2
    refine ⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 -
      (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)),
      (mem_stdH C).2 ⟨a₁, sub_mem a₃ a₂⟩, ?_⟩
    have t : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
      rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
    rw [transH_apply]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
    · simp only [sub_add_cancel, Matrix.mulVec_mulVec, t, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[dotDual_colLat C _ _ h₁ h₂]`. Use `⟨LinearMap.inr_injective, Function.Exact.inr_fst, LinearMap.fst_surjective, fun i x => ?_, fun i z => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_colLat]`. Simplify using `only [LinearMap.inr_apply]`. Rewrite using `[mem_imLat]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Use `⟨(0, w), (mem_stdH C).2 ⟨zero_mem _, hw⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[transH_apply]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨w, hw, e⟩`. Rewrite `e` using `[transH_apply, Prod.mk.injEq]`. Establish `hw'` using `(mem_stdH C).1 hw`. Establish `e₁ : w.1 = 0`. Use `congrArg (lin (ψ i) 1).mulVec e.1` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_mulVec, h₂ i]`. Use `⟨w.2, hw'.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.2, e₁]`. Simplify using the standard rewrite rules. Rewrite using `[mem_colLat]`.

Simplify using `only [LinearMap.fst_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Use `⟨transH (φ i) (ψ i) (lam i) (w, 0), (mem_imLat C).2 ⟨(w, 0), (mem_stdH C).2 ⟨hw, zero_mem _⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[transH_apply]`.

Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨w, hw, rfl⟩` from `(mem_imLat C).1 hy`. Conclude with `⟨w.1, ((mem_stdH C).1 hw).1, by rw [transH_apply]⟩`.
-/
theorem hodge_family (φ ψ : C.I → Pt K 1 d) (lam : C.I → PS K 2 d)
    (h₁ : ∀ i, lin (φ i) 1 * lin (ψ i) 1 = 1) (h₂ : ∀ i, lin (ψ i) 1 * lin (φ i) 1 = 1) :
    ShortExact C (dotDual C fun i => colLat C i (lin (φ i) 1))
      (fun i => imLat C i (transH (φ i) (ψ i) (lam i))) (fun i => colLat C i (lin (φ i) 1))
      (LinearMap.inr K _ _) (LinearMap.fst K _ _) := by
  rw [dotDual_colLat C _ _ h₁ h₂]
  refine ⟨LinearMap.inr_injective, Function.Exact.inr_fst, LinearMap.fst_surjective,
    fun i x => ?_, fun i z => ?_⟩
  · rw [mem_colLat]
    simp only [LinearMap.inr_apply]
    rw [mem_imLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(0, w), (mem_stdH C).2 ⟨zero_mem _, hw⟩, ?_⟩
      rw [transH_apply]
      simp
    · rintro ⟨w, hw, e⟩
      rw [transH_apply, Prod.mk.injEq] at e
      have hw' := (mem_stdH C).1 hw
      have e₁ : w.1 = 0 := by
        have := congrArg (lin (ψ i) 1).mulVec e.1
        simpa [Matrix.mulVec_mulVec, h₂ i] using this
      refine ⟨w.2, hw'.2, ?_⟩
      rw [← e.2, e₁]
      simp
  · rw [mem_colLat]
    simp only [LinearMap.fst_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨transH (φ i) (ψ i) (lam i) (w, 0), (mem_imLat C).2
        ⟨(w, 0), (mem_stdH C).2 ⟨hw, zero_mem _⟩, rfl⟩, ?_⟩
      rw [transH_apply]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨w.1, ((mem_stdH C).1 hw).1, by rw [transH_apply]⟩

structure LocSplit (i : C.I) (a : (Fin d → K) →ₗ[K] VV K d) (b : VV K d →ₗ[K] Fin d → K) : Prop where

  a_int : ∀ u ∈ trivLat C d i, a u ∈ stdH C d i

  b_int : ∀ y ∈ stdH C d i, b y ∈ trivLat C d i

  zero : ∀ u, b (a u) = 0

  split : ∃ (r : VV K d →ₗ[K] Fin d → K) (s : (Fin d → K) →ₗ[K] VV K d),
    (∀ y ∈ stdH C d i, r y ∈ trivLat C d i) ∧ (∀ z ∈ trivLat C d i, s z ∈ stdH C d i) ∧
      (∀ u, r (a u) = u) ∧ (∀ z, b (s z) = z) ∧ ∀ y, a (r y) + s (b y) = y

/- English proof (translation)
Establish `fm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M` using `fun _ => rfl`. Establish `t₁ : ∀ i, (g' i).transpose * (g i).transpose = 1` using `fun i => by`. Rewrite using `[← Matrix.transpose_mul, h₁, Matrix.transpose_one]`. Establish `t₂ : ∀ i, (g i).transpose * (g' i).transpose = 1` using `fun i => by`. Rewrite using `[← Matrix.transpose_mul, h₂, Matrix.transpose_one]`.

Establish `hF₂ : frobLat C p (dotDual C fun i => colLat C i (g i)) = fun i => colLat C i ((g' i).transpose.map (· ^ p))`. Rewrite using `[dotDual_colLat C g g' h₁ h₂]`. Conclude with `frobLat_colLat C p (fun i => (g' i).transpose) (fun i => (g i).transpose) t₁ t₂`. Rewrite using `[hF₂, frobLat_colLat C p g g' h₁ h₂]`. Establish `G₁ : ∀ i (u : Fin d → K), ((g i).map (· ^ p)).mulVec (((g' i).map (· ^ p)).mulVec u) = u` using `fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₁, map_one, Matrix.one_mulVec]`.

Establish `G₂ : ∀ i (u : Fin d → K), ((g' i).map (· ^ p)).mulVec (((g i).map (· ^ p)).mulVec u) = u` using `fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₂, map_one, Matrix.one_mulVec]`. Establish `D₁ : ∀ i (u : Fin d → K), ((g' i).transpose.map (· ^ p)).mulVec (((g i).transpose.map (· ^ p)).mulVec u) = u` using `fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₁, map_one, Matrix.one_mulVec]`. Establish `D₂ : ∀ i (u : Fin d → K), ((g i).transpose.map (· ^ p)).mulVec (((g' i).transpose.map (· ^ p)).mulVec u) = u` using `fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₂, map_one, Matrix.one_mulVec]`. Take `⟨i₀⟩` from `hI`. Take `⟨r₀, s₀, -, -, ra₀, bs₀, as₀⟩` from `(hloc i₀).split`.

Use `⟨?_, ?_, ?_, fun i x => ?_, fun i z => ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `e : T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) = 0`. Rewrite using `[← hα, G₁, hx]`.

Establish `e' : a i₀ (((g' i₀).map (· ^ p)).mulVec x) = 0` using `(hT i₀).1 (by rw [e, map_zero])`. Establish `e''` using `ra₀ (((g' i₀).map (· ^ p)).mulVec x)`. Rewrite `e''` using `[e', map_zero]`. Rewrite using `[← G₁ i₀ x, ← e'', Matrix.mulVec_zero]`. Introduce `y`.

Take `⟨w, rfl⟩` from `(hT i₀).2 y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite `hy` using `[hβ]`. Establish `e : b i₀ w = 0`.

Rewrite using `[← D₂ i₀ (b i₀ w), hy, Matrix.mulVec_zero]`. Establish `e'` using `as₀ w`. Rewrite `e'` using `[e, map_zero, add_zero]`. Conclude with `⟨((g i₀).map (· ^ p)).mulVec (r₀ w), by rw [hα, e']⟩`. Introduce and unpack `⟨x, hx⟩`.

Establish `e : T i₀ w = T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x))`. Rewrite using `[← hα, G₁, hx]`. Rewrite using `[e, hβ, (hloc i₀).zero, Matrix.mulVec_zero]`. Introduce `z`. Use `⟨T i₀ (s₀ (((g i₀).transpose.map (· ^ p)).mulVec z)), ?_⟩` and prove the remaining obligations.

Rewrite using `[hβ, bs₀, D₁]`. Take `⟨r, s, hr, hs, ra, bs, as⟩` from `(hloc i).split`. Rewrite using `[mem_colLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `(mem_imLat C).2 ⟨a i w, (hloc i).a_int w hw, (hα i w).symm⟩`. Introduce `hx`. Take `⟨w, hw, e⟩` from `(mem_imLat C).1 hx`. Establish `e' : w = a i (((g' i).map (· ^ p)).mulVec x)` using `(hT i).1 (by rw [e, ← hα, G₁])`. Use `⟨r w, hr w hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[e', ra, G₁]`. Take `⟨r, s, hr, hs, ra, bs, as⟩` from `(hloc i).split`. Rewrite using `[mem_colLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `⟨T i (s w), (mem_imLat C).2 ⟨s w, hs w hw, rfl⟩, by rw [hβ, bs]⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨w, hw, rfl⟩` from `(mem_imLat C).1 hy`. Conclude with `⟨b i w, (hloc i).b_int w hw, (hβ i w).symm⟩`.
-/
theorem conj_family (p : ℕ) [Fact p.Prime] [CharP K p] (hI : Nonempty C.I)
    (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1)
    (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (α : (Fin d → K) →ₗ[K] VV K d) (β : VV K d →ₗ[K] Fin d → K)
    (a : C.I → (Fin d → K) →ₗ[K] VV K d) (b : C.I → VV K d →ₗ[K] Fin d → K)
    (hα : ∀ i u, α (((g i).map (· ^ p)).mulVec u) = T i (a i u))
    (hβ : ∀ i y, β (T i y) = ((g' i).transpose.map (· ^ p)).mulVec (b i y))
    (hloc : ∀ i, LocSplit C i (a i) (b i)) :
    ShortExact C (frobLat C p fun i => colLat C i (g i)) (fun i => imLat C i (T i))
      (frobLat C p (dotDual C fun i => colLat C i (g i))) α β := by
  have fm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M :=
    fun _ => rfl
  have t₁ : ∀ i, (g' i).transpose * (g i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : ∀ i, (g i).transpose * (g' i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have hF₂ : frobLat C p (dotDual C fun i => colLat C i (g i)) =
      fun i => colLat C i ((g' i).transpose.map (· ^ p)) := by
    rw [dotDual_colLat C g g' h₁ h₂]
    exact frobLat_colLat C p (fun i => (g' i).transpose) (fun i => (g i).transpose) t₁ t₂
  rw [hF₂, frobLat_colLat C p g g' h₁ h₂]
  have G₁ : ∀ i (u : Fin d → K), ((g i).map (· ^ p)).mulVec (((g' i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₁, map_one, Matrix.one_mulVec]
  have G₂ : ∀ i (u : Fin d → K), ((g' i).map (· ^ p)).mulVec (((g i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₂, map_one, Matrix.one_mulVec]
  have D₁ : ∀ i (u : Fin d → K), ((g' i).transpose.map (· ^ p)).mulVec
      (((g i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₁, map_one, Matrix.one_mulVec]
  have D₂ : ∀ i (u : Fin d → K), ((g i).transpose.map (· ^ p)).mulVec
      (((g' i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₂, map_one, Matrix.one_mulVec]
  obtain ⟨i₀⟩ := hI
  obtain ⟨r₀, s₀, -, -, ra₀, bs₀, as₀⟩ := (hloc i₀).split
  refine ⟨?_, ?_, ?_, fun i x => ?_, fun i z => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e : T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) = 0 := by
      rw [← hα, G₁, hx]
    have e' : a i₀ (((g' i₀).map (· ^ p)).mulVec x) = 0 :=
      (hT i₀).1 (by rw [e, map_zero])
    have e'' := ra₀ (((g' i₀).map (· ^ p)).mulVec x)
    rw [e', map_zero] at e''
    rw [← G₁ i₀ x, ← e'', Matrix.mulVec_zero]
  · intro y
    obtain ⟨w, rfl⟩ := (hT i₀).2 y
    constructor
    · intro hy
      rw [hβ] at hy
      have e : b i₀ w = 0 := by
        rw [← D₂ i₀ (b i₀ w), hy, Matrix.mulVec_zero]
      have e' := as₀ w
      rw [e, map_zero, add_zero] at e'
      exact ⟨((g i₀).map (· ^ p)).mulVec (r₀ w), by rw [hα, e']⟩
    · rintro ⟨x, hx⟩
      have e : T i₀ w = T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) := by
        rw [← hα, G₁, hx]
      rw [e, hβ, (hloc i₀).zero, Matrix.mulVec_zero]
  · intro z
    refine ⟨T i₀ (s₀ (((g i₀).transpose.map (· ^ p)).mulVec z)), ?_⟩
    rw [hβ, bs₀, D₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_imLat C).2 ⟨a i w, (hloc i).a_int w hw, (hα i w).symm⟩
    · intro hx
      obtain ⟨w, hw, e⟩ := (mem_imLat C).1 hx
      have e' : w = a i (((g' i).map (· ^ p)).mulVec x) := (hT i).1 (by rw [e, ← hα, G₁])
      refine ⟨r w, hr w hw, ?_⟩
      rw [e', ra, G₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨T i (s w), (mem_imLat C).2 ⟨s w, hs w hw, rfl⟩, by rw [hβ, bs]⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨b i w, (hloc i).b_int w hw, (hβ i w).symm⟩

/- English proof (translation)
Introduce `a b` and use `(Valuation.mem_valuationSubring_iff _ _).1 (M a b).2`.
-/
theorem intM_map (i : C.I) (M : Matrix (Fin d) (Fin d) (C.v i).valuationSubring) :
    IntM C i (M.map (C.v i).valuationSubring.subtype) := fun a b =>
  (Valuation.mem_valuationSubring_iff _ _).1 (M a b).2

omit [Field K] in
/- English proof (translation)
Use extensionality with `a b`. Use `congrFun (h (Pi.single b 1)) a` as an intermediate fact. Simplify using `using this`.
-/
theorem matrix_eq_zero_of_mulVec {R : Type} [CommRing R] {M : Matrix (Fin d) (Fin d) R}
    (h : ∀ u, M.mulVec u = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa using this

variable {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Use `⟨fun u hu => ?_, fun y hy => ?_, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[alpha_apply]`. Conclude with `(mem_stdH C).2 ⟨mulVec_mem_trivLat C ih hu, mulVec_mem_trivLat C (fun a b => ia b a) hu⟩`. Establish `hy'` using `(mem_stdH C).1 hy`. Rewrite using `[beta_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]`.

Conclude with `sub_mem (mulVec_mem_trivLat C (fun a b => ih b a) hy'.2) (sub_mem (mulVec_mem_trivLat C ia hy'.1) (mulVec_mem_trivLat C (fun a b => ih b a) (mulVec_mem_trivLat C iS hy'.1)))`. Set `r : VV K d →ₗ[K] Fin d → K` to `Matrix.toLin' r₁ ∘ₗ LinearMap.fst K _ _ + Matrix.toLin' r₂ ∘ₗ LinearMap.snd K _ _`. Set `s : (Fin d → K) →ₗ[K] VV K d` to `LinearMap.prod (-Matrix.toLin' s₁) (-Matrix.toLin' s₂)`. Establish `hr : ∀ y, r y = r₁.mulVec y.1 + r₂.mulVec y.2` using `fun y => by simp [r]`. Establish `hs : ∀ z, s z = (-(s₁.mulVec z), -(s₂.mulVec z))` using `fun z => by simp [s]`.

Use `⟨r, s, fun y hy => ?_, fun z hz' => ?_, fun u => ?_, fun z => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `hy'` using `(mem_stdH C).1 hy`. Rewrite using `[hr]`. Conclude with `add_mem (mulVec_mem_trivLat C ir₁ hy'.1) (mulVec_mem_trivLat C ir₂ hy'.2)`. Rewrite using `[hs]`.

Conclude with `(mem_stdH C).2 ⟨neg_mem (mulVec_mem_trivLat C is₁ hz'), neg_mem (mulVec_mem_trivLat C is₂ hz')⟩`. Rewrite using `[hr, alpha_apply]`. Simplify using `only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, e₁, Matrix.one_mulVec]`. Establish `E : ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z - ((hw B p).transpose * s₂).mulVec z = z`. Rewrite using `[← Matrix.sub_mulVec, e₂, Matrix.one_mulVec]`.

Rewrite using `[hs, beta_apply]`. Simplify using `only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Establish `E₃ : (hw B p * r₁).mulVec y.1 + (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = y.1`. Rewrite using `[← Matrix.add_mulVec, e₃, Matrix.one_mulVec]`.

Establish `E₄ : (hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2 = 0`. Rewrite using `[← Matrix.sub_mulVec, e₄, Matrix.zero_mulVec]`. Establish `E₅ : ((am B p).transpose * r₁).mulVec y.1 + (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = 0`. Rewrite using `[← Matrix.add_mulVec, e₅, Matrix.zero_mulVec]`. Establish `E₆ : ((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2 = y.2`.

Rewrite using `[← Matrix.sub_mulVec, e₆, Matrix.one_mulVec]`. Rewrite using `[alpha_apply, hs, hr, beta_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only [Prod.fst_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub, Matrix.mulVec_mulVec]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Prod.snd_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub, Matrix.mulVec_mulVec]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem locSplit_of_mats (B : FB K d O) (p : ℕ) (i : C.I) (r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) K)
    (ih : IntM C i (hw B p)) (ia : IntM C i (am B p)) (iS : IntM C i (bil B.sy 1 1))
    (ir₁ : IntM C i r₁) (ir₂ : IntM C i r₂) (is₁ : IntM C i s₁) (is₂ : IntM C i s₂)
    (hz : ∀ u, beta B p (alpha B p u) = 0)
    (e₁ : r₁ * hw B p + r₂ * (am B p).transpose = 1)
    (e₂ : (am B p - (hw B p).transpose * bil B.sy 1 1) * s₁ - (hw B p).transpose * s₂ = 1)
    (e₃ : hw B p * r₁ + s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 1)
    (e₄ : hw B p * r₂ - s₁ * (hw B p).transpose = 0)
    (e₅ : (am B p).transpose * r₁ + s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 0)
    (e₆ : (am B p).transpose * r₂ - s₂ * (hw B p).transpose = 1) :
    LocSplit C i (alpha B p) (beta B p) := by
  refine ⟨fun u hu => ?_, fun y hy => ?_, hz, ?_⟩
  · rw [alpha_apply]
    exact (mem_stdH C).2 ⟨mulVec_mem_trivLat C ih hu, mulVec_mem_trivLat C (fun a b => ia b a) hu⟩
  · have hy' := (mem_stdH C).1 hy
    rw [beta_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    exact sub_mem (mulVec_mem_trivLat C (fun a b => ih b a) hy'.2)
      (sub_mem (mulVec_mem_trivLat C ia hy'.1) (mulVec_mem_trivLat C (fun a b => ih b a)
        (mulVec_mem_trivLat C iS hy'.1)))
  · let r : VV K d →ₗ[K] Fin d → K := Matrix.toLin' r₁ ∘ₗ LinearMap.fst K _ _ +
      Matrix.toLin' r₂ ∘ₗ LinearMap.snd K _ _
    let s : (Fin d → K) →ₗ[K] VV K d := LinearMap.prod (-Matrix.toLin' s₁) (-Matrix.toLin' s₂)
    have hr : ∀ y, r y = r₁.mulVec y.1 + r₂.mulVec y.2 := fun y => by simp [r]
    have hs : ∀ z, s z = (-(s₁.mulVec z), -(s₂.mulVec z)) := fun z => by simp [s]
    refine ⟨r, s, fun y hy => ?_, fun z hz' => ?_, fun u => ?_, fun z => ?_, fun y => ?_⟩
    · have hy' := (mem_stdH C).1 hy
      rw [hr]
      exact add_mem (mulVec_mem_trivLat C ir₁ hy'.1) (mulVec_mem_trivLat C ir₂ hy'.2)
    · rw [hs]
      exact (mem_stdH C).2 ⟨neg_mem (mulVec_mem_trivLat C is₁ hz'),
        neg_mem (mulVec_mem_trivLat C is₂ hz')⟩
    · rw [hr, alpha_apply]
      simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, e₁, Matrix.one_mulVec]
    · have E : ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z = z := by
        rw [← Matrix.sub_mulVec, e₂, Matrix.one_mulVec]
      rw [hs, beta_apply]
      simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      calc _ = ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z := by abel
        _ = z := E
    · have E₃ : (hw B p * r₁).mulVec y.1 +
          (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = y.1 := by
        rw [← Matrix.add_mulVec, e₃, Matrix.one_mulVec]
      have E₄ : (hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2 = 0 := by
        rw [← Matrix.sub_mulVec, e₄, Matrix.zero_mulVec]
      have E₅ : ((am B p).transpose * r₁).mulVec y.1 +
          (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = 0 := by
        rw [← Matrix.add_mulVec, e₅, Matrix.zero_mulVec]
      have E₆ : ((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2 = y.2 := by
        rw [← Matrix.sub_mulVec, e₆, Matrix.one_mulVec]
      rw [alpha_apply, hs, hr, beta_apply]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = ((hw B p * r₁).mulVec y.1 +
              (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            ((hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.1 := by rw [E₃, E₄, add_zero]
      · simp only [Prod.snd_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = (((am B p).transpose * r₁).mulVec y.1 +
              (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            (((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.2 := by rw [E₅, E₆, zero_add]

/- English proof (translation)
Use `haveI : CharP (C.v i).valuationSubring p := (RingHom.charP_iff (C.v i).valuationSubring.subtype Subtype.val_injective p).2 inferInstance`. Establish `mK` using `GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O (F.Bi i) (F.BK i) (F.mapK i)`. Establish `mk` using `GlobalTheory.T.formal_data_base_change _ _ (IsLocalRing.residue _) d O (F.Bi i) (F.Bk i) (F.mapk i)`. Establish `iz : am (F.Bi i) p * hw (F.Bi i) p - (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p - (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose = 0`. Establish `h0` using `matrix_eq_zero_of_mulVec (M := (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose - am (F.Bi i) p * hw (F.Bi i) p + (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p) fun u => by`.

Rewrite using `[← beta_alpha_apply]`. Conclude with `LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact _ p d O (F.Bi i)).2 u`. Rewrite using `[← neg_eq_zero, ← h0]`. Normalize the expressions using the abelian group laws. Establish `inj : ∀ u : Fin d → IsLocalRing.ResidueField (C.v i).valuationSubring, ((hw (F.Bi i) p).map (IsLocalRing.residue _)).mulVec u = 0 → ((am (F.Bi i) p).transpose.map (IsLocalRing.residue _)).mulVec u = 0 → u = 0`.

Introduce `u h1 h2`. Apply `F.inj i` to reduce the goal to its premises. Rewrite using `[map_zero, alpha_apply, (mk.2.2 p).1, (mk.2.2 p).2, ← Matrix.transpose_map, h1, h2]`. Both sides reduce to the same expression. Take `⟨r₁, r₂, s₁, s₂, e₁, e₂, e₃, e₄, e₅, e₆⟩` from `GlobalTheory.T.local_matrix_coprime_decomposition _ d _ _ _ iz inj`.

Set `Φ` to `(C.v i).valuationSubring.subtype.mapMatrix (m := Fin d)`. Establish `hT : ∀ M, Φ M.transpose = (Φ M).transpose` using `fun M => rfl`. Establish `hh : hw (F.BK i) p = Φ (hw (F.Bi i) p)` using `(mK.2.2 p).1`. Establish `ha : am (F.BK i) p = Φ (am (F.Bi i) p)` using `(mK.2.2 p).2`. Establish `hS : bil (F.BK i).sy 1 1 = Φ (bil (F.Bi i).sy 1 1)` using `mK.2.1`.

Establish `c₁` using `congrArg Φ e₁`. Establish `c₂` using `congrArg Φ e₂`. Establish `c₃` using `congrArg Φ e₃`. Establish `c₄` using `congrArg Φ e₄`. Establish `c₅` using `congrArg Φ e₅`.

Establish `c₆` using `congrArg Φ e₆`. Simplify using `only [map_add, map_sub, map_mul, map_one, map_zero, hT] at c₁ c₂ c₃ c₄ c₅ c₆`. Use `locSplit_of_mats C (F.BK i) p i (Φ r₁) (Φ r₂) (Φ s₁) (Φ s₂) ?_ ?_ ?_ (intM_map C i _) (intM_map C i _) (intM_map C i _) (intM_map C i _) (fun u => LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact K p d O (F.BK i)).2 u) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hh]`. Conclude with `intM_map C i _`.

Rewrite using `[ha]`. Conclude with `intM_map C i _`. Rewrite using `[hS]`. Conclude with `intM_map C i _`. Apply the tactic sequence `all_goals simp only [hh, ha, hS]`.

Use `exacts [c₁, c₂, c₃, c₄, c₅, c₆]`.
-/
theorem locSplit {p : ℕ} [Fact p.Prime] [CharP K p] (F : Family C p d O) (i : C.I) :
    LocSplit C i (alpha (F.BK i) p) (beta (F.BK i) p) := by
  haveI : CharP (C.v i).valuationSubring p :=
    (RingHom.charP_iff (C.v i).valuationSubring.subtype Subtype.val_injective p).2 inferInstance
  have mK := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O (F.Bi i) (F.BK i) (F.mapK i)
  have mk := GlobalTheory.T.formal_data_base_change _ _ (IsLocalRing.residue _) d O (F.Bi i) (F.Bk i) (F.mapk i)
  have iz : am (F.Bi i) p * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose = 0 := by
    have h0 := matrix_eq_zero_of_mulVec (M := (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose -
        am (F.Bi i) p * hw (F.Bi i) p +
        (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p) fun u => by
      rw [← beta_alpha_apply]
      exact LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact _ p d O (F.Bi i)).2 u
    rw [← neg_eq_zero, ← h0]
    abel
  have inj : ∀ u : Fin d → IsLocalRing.ResidueField (C.v i).valuationSubring,
      ((hw (F.Bi i) p).map (IsLocalRing.residue _)).mulVec u = 0 →
      ((am (F.Bi i) p).transpose.map (IsLocalRing.residue _)).mulVec u = 0 → u = 0 := by
    intro u h1 h2
    apply F.inj i
    rw [map_zero, alpha_apply, (mk.2.2 p).1, (mk.2.2 p).2, ← Matrix.transpose_map, h1, h2]
    rfl
  obtain ⟨r₁, r₂, s₁, s₂, e₁, e₂, e₃, e₄, e₅, e₆⟩ := GlobalTheory.T.local_matrix_coprime_decomposition _ d _ _ _ iz inj
  let Φ := (C.v i).valuationSubring.subtype.mapMatrix (m := Fin d)
  have hT : ∀ M, Φ M.transpose = (Φ M).transpose := fun M => rfl
  have hh : hw (F.BK i) p = Φ (hw (F.Bi i) p) := (mK.2.2 p).1
  have ha : am (F.BK i) p = Φ (am (F.Bi i) p) := (mK.2.2 p).2
  have hS : bil (F.BK i).sy 1 1 = Φ (bil (F.Bi i).sy 1 1) := mK.2.1
  have c₁ := congrArg Φ e₁
  have c₂ := congrArg Φ e₂
  have c₃ := congrArg Φ e₃
  have c₄ := congrArg Φ e₄
  have c₅ := congrArg Φ e₅
  have c₆ := congrArg Φ e₆
  simp only [map_add, map_sub, map_mul, map_one, map_zero, hT] at c₁ c₂ c₃ c₄ c₅ c₆
  refine locSplit_of_mats C (F.BK i) p i (Φ r₁) (Φ r₂) (Φ s₁) (Φ s₂) ?_ ?_ ?_
    (intM_map C i _) (intM_map C i _) (intM_map C i _) (intM_map C i _)
    (fun u => LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact K p d O (F.BK i)).2 u) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hh]; exact intM_map C i _
  · rw [ha]; exact intM_map C i _
  · rw [hS]; exact intM_map C i _
  all_goals simp only [hh, ha, hS]
  exacts [c₁, c₂, c₃, c₄, c₅, c₆]

/- English proof (translation)
Take `⟨hm, -⟩` from `GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O B₀ B h`. Establish `hr : ∀ b, IntM C i (rho B b)` using `fun b => by rw [(hm b).1]; exact intM_map C i _`. Establish `ha : IntM C i (bil (B.ad a) 1 1)` using `by rw [(hm a).2]; exact intM_map C i _`. Rewrite `hw`, the goal using `[mem_stdH]`. Rewrite using `[rhoH_apply]`.

Conclude with `⟨mulVec_mem_trivLat C (hr a) hw.1, sub_mem (mulVec_mem_trivLat C (fun x y => hr _ y x) hw.2) (mulVec_mem_trivLat C (fun x y => ha y x) hw.1)⟩`.
-/
theorem rhoH_mem_stdH (i : C.I) (B₀ : FB (C.v i).valuationSubring d O) (B : FB K d O)
    (h : IsMapOf (C.v i).valuationSubring.subtype B₀ B) (a : O) {w : VV K d}
    (hw : w ∈ stdH C d i) : rhoH B a w ∈ stdH C d i := by
  obtain ⟨hm, -⟩ := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O B₀ B h
  have hr : ∀ b, IntM C i (rho B b) := fun b => by rw [(hm b).1]; exact intM_map C i _
  have ha : IntM C i (bil (B.ad a) 1 1) := by rw [(hm a).2]; exact intM_map C i _
  rw [mem_stdH] at hw ⊢
  rw [rhoH_apply]
  exact ⟨mulVec_mem_trivLat C (hr a) hw.1, sub_mem (mulVec_mem_trivLat C (fun x y => hr _ y x) hw.2)
    (mulVec_mem_trivLat C (fun x y => ha y x) hw.1)⟩

/- English proof (translation)
Introduce `K _ C p _ _ d O _ _ F hI`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.formal_group_action_ring_hom K d O F.B`. Take `⟨⟨ρH, hρH⟩, -, -⟩` from `GlobalTheory.T.formal_hermitian_action_pairing K d O F.B`. Establish `iso` using `fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)`. Establish `h₁` using `fun i => (iso i).1`.

Establish `h₂` using `fun i => (iso i).2.1`. Establish `hT` using `fun i => (iso i).2.2.1`. Establish `hc` using `fun i => (iso i).2.2.2.2.1`. Establish `good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧ C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧ IntM C i (bil (F.lam i) 1 1)` using `fun i h => ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩`. Establish `hiso` using `fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)`.

Use `⟨{ lie := fun i => colLat C i (lin (F.φ i) 1) H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i)) lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ?_) H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi ?_) ρ := ρ ρH := ρH ρH_hom := fun a i x hx => ? …` and prove the remaining obligations. Conclude with `⟨(good i h).1, (good i h).2.1⟩`. Take `⟨g₁, g₂, g₃⟩` from `good i h`. Conclude with `imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃`. Take `⟨w, hw, rfl⟩` from `(mem_imLat C).1 hx`.

Rewrite using `[hρH]`. Use `(mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩` and prove the remaining obligations. Conclude with `(LinearMap.congr_fun (hc i a) w).symm`. Rewrite using `[hρH, rhoH_fst, hρ]`. Rewrite using `[hρH, rhoH_inr, hρ]`.

Rewrite using `[hρ, hρH]`. Conclude with `GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u`. Rewrite using `[hρ, hρH]`. Conclude with `GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y`.
-/
theorem family_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρ a = rho F.B a) ∧
      ∀ i u, u ∈ D.lie i ↔ ∀ j, C.v i ((lin (F.ψ i) 1).mulVec u j) ≤ 1 := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formal_group_action_ring_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing K d O F.B
  have iso := fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ?_)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi ?_)
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρ, fun i u => mem_colLat_iff C (h₁ i) (h₂ i)⟩
  · exact ⟨(good i h).1, (good i h).2.1⟩
  · obtain ⟨g₁, g₂, g₃⟩ := good i h
    exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u
  · rw [hρ, hρH]
    exact GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y

end GlobalTheory.CompanionTheory.Ar.Conj.Fam
