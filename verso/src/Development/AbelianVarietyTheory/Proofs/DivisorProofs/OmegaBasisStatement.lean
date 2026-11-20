import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeights

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.OmegaHT

namespace GlobalTheory.OmegaHT.RankForms

open GlobalTheory.Cartier GlobalTheory.VB
open GlobalTheory.TrueGeo.SmallSec (fnMap)

def rowMinor {A : Type} [CommRing A] {g n : ℕ} (η : Fin n → Fin g → A) (K : Fin g → Fin n) : A :=
  (Matrix.of fun l => η (K l)).det

/- English proof (translation)
Unfold `rowMinor`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem map_rowMinor {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {g n : ℕ} (η : Fin n → Fin g → A)
    (K : Fin g → Fin n) : φ (rowMinor η K) = rowMinor (fun j i => φ (η j i)) K := by
  unfold rowMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Take `⟨M, hM⟩` from `h`. Assume the negation of the conclusion as `h0`. Use `push Not at h0`. Establish `e1 : (Matrix.of fun i => ∑ j, M i j • η j) = (p : A) • (1 : Matrix (Fin g) (Fin g) A)`. Use extensionality with `i k`.

Simplify using `only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hM, Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `e2 : (Matrix.of fun i => ∑ j, M i j • η j).det = 0`. Use `(Matrix.detRowAlternating (n := Fin g) (R := A)).toMultilinearMap.map_sum (fun i j => M i j • η j)` as an intermediate fact. Use `this.trans (Finset.sum_eq_zero fun K _ => ?_)` and prove the remaining obligations.

Rewrite using `[MultilinearMap.map_smul_univ]`. Conclude with `smul_eq_zero_of_right _ (h0 K)`. Rewrite `e2` using `[e1, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `hp (eq_zero_of_pow_eq_zero e2)`.
-/
theorem exists_rowMinor_ne_zero {A : Type} [CommRing A] [IsDomain A] {p : ℕ} (hp : (p : A) ≠ 0) {g n : ℕ}
    {η : Fin n → Fin g → A} (h : SpansP p η) : ∃ K, rowMinor η K ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := h
  by_contra h0
  push Not at h0
  have e1 : (Matrix.of fun i => ∑ j, M i j • η j) = (p : A) • (1 : Matrix (Fin g) (Fin g) A) := by
    ext i k
    simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hM, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e2 : (Matrix.of fun i => ∑ j, M i j • η j).det = 0 := by
    have := (Matrix.detRowAlternating (n := Fin g) (R := A)).toMultilinearMap.map_sum (fun i j => M i j • η j)
    refine this.trans (Finset.sum_eq_zero fun K _ => ?_)
    rw [MultilinearMap.map_smul_univ]
    exact smul_eq_zero_of_right _ (h0 K)
  rw [e1, Matrix.det_smul, Matrix.det_one, mul_one] at e2
  exact hp (eq_zero_of_pow_eq_zero e2)

/- English proof (translation)
Use `choose c hc using hd`. Use `⟨fun l => c (Function.update J l j), fun i => mul_left_cancel₀ hJ ?_⟩` and prove the remaining obligations. Set `a : Matrix (Fin g) (Fin g) A` to `Matrix.of fun l => η (J l)`. Establish `e` using `congrFun (Matrix.mulVec_cramer a.transpose (η j)) i`. Establish `e' (l : Fin g) : Matrix.cramer a.transpose (η j) l = rowMinor η J * c (Function.update J l j)`.

Rewrite using `[Matrix.cramer_transpose_apply, ← hc]`. Unfold `rowMinor`. Use `congr 1`. Use extensionality with `k m`. Distinguish the cases in `h : k = l`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.updateRow_ne h, Function.update_of_ne h, a]`. Rewrite `e` using `[Matrix.det_transpose]`. Simplify using `only [Matrix.mulVec, dotProduct, e', Pi.smul_apply, smul_eq_mul] at e`.

Use `e.symm.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, a, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_comb_of_dvd {A : Type} [CommRing A] [IsDomain A] {g n : ℕ} {η : Fin n → Fin g → A} {J : Fin g → Fin n}
    (hJ : rowMinor η J ≠ 0) (hd : ∀ K, rowMinor η J ∣ rowMinor η K) (j : Fin n) :
    ∃ N : Fin g → A, ∀ i, η j i = ∑ l, N l * η (J l) i := by
  classical
  choose c hc using hd
  refine ⟨fun l => c (Function.update J l j), fun i => mul_left_cancel₀ hJ ?_⟩
  let a : Matrix (Fin g) (Fin g) A := Matrix.of fun l => η (J l)
  have e := congrFun (Matrix.mulVec_cramer a.transpose (η j)) i
  have e' (l : Fin g) : Matrix.cramer a.transpose (η j) l = rowMinor η J * c (Function.update J l j) := by
    rw [Matrix.cramer_transpose_apply, ← hc]
    unfold rowMinor
    congr 1
    ext k m
    by_cases h : k = l
    · subst h; simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h, a]
  rw [Matrix.det_transpose] at e
  simp only [Matrix.mulVec, dotProduct, e', Pi.smul_apply, smul_eq_mul] at e
  refine e.symm.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.transpose_apply, a, Matrix.of_apply]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) (p : ℕ)

/- English proof (translation)
Rewrite using `[← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]`.
-/
theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

/- English proof (translation)
Use `⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩` and prove the remaining obligations. Simplify using `only [bc_bc]`. Rewrite `hw`, the goal using `[← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]`. Conclude with `h.2 T (ψ.comp φ) w hw`.
-/
theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x e) (φ : R →+* S) :
    IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

/- English proof (translation)
Take `⟨M, hM⟩` from `h`. Use `⟨fun i j => φ (M i j), fun i k => ?_⟩` and prove the remaining obligations. Use `congrArg φ (hM i k)` as an intermediate fact. Simplify `this` using `[map_sum, apply_ite φ]`.
-/
theorem spansP_map {R S : Type} [CommRing R] [CommRing S] {g n : ℕ} {η : Fin n → Fin g → R} (h : SpansP p η)
    (φ : R →+* S) : SpansP p fun j i => φ (η j i) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun i j => φ (M i j), fun i k => ?_⟩
  have := congrArg φ (hM i k)
  simpa [map_sum, apply_ite φ] using this

/- English proof (translation)
Introduce `C κ a v hv`. Simplify using `only [bc_bc] at hv`. Rewrite `hv`, the goal using `[← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]`. Conclude with `h C (κ.comp φ) a v hv`.
-/
theorem cutsHT_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g n : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} {η : Fin n → Fin g → R} (h : CutsHT t p x e η) (φ : R →+* S) :
    CutsHT t p (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) fun j i => φ (η j i) := by
  intro C κ a v hv
  simp only [bc_bc] at hv
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hv ⊢
  exact h C (κ.comp φ) a v hv

/- English proof (translation)
Take `⟨M, hM⟩` from `h`. Use `choose N hN using hN`. Use `⟨fun i l => ∑ j, M i j * N j l, fun i k => ?_⟩` and prove the remaining obligations. Rewrite using `[← hM i k]`. Simplify using `only [Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hN j k, Finset.mul_sum]`. Simplify using `only [mul_assoc]`.
-/
theorem spansP_rows {R : Type} [CommRing R] {g n : ℕ} {η : Fin n → Fin g → R} (h : SpansP p η) {J : Fin g → Fin n}
    (hN : ∀ j, ∃ N : Fin g → R, ∀ i, η j i = ∑ l, N l * η (J l) i) : SpansP p fun l => η (J l) := by
  obtain ⟨M, hM⟩ := h
  choose N hN using hN
  refine ⟨fun i l => ∑ j, M i j * N j l, fun i k => ?_⟩
  rw [← hM i k]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hN j k, Finset.mul_sum]
  simp only [mul_assoc]

/- English proof (translation)
Introduce `C κ a v hv`. Rewrite using `[h C κ a v hv]`. Use `⟨fun k l => k (J l), fun k j => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `hN j`. Establish `e1 : ∑ i, (κ (η j i) : ↥C.S) * a i = ∑ l, (κ (N l) : ↥C.S) * ∑ i, (κ (η (J l) i) : ↥C.S) * a i`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hN i, map_sum]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `(intO ↥C.S).sum_mem fun l _ => (intO ↥C.S).mul_mem (κ (N l)).2 (k l)`.
-/
theorem cutsHT_rows {R : Type} [CommRing R] {x : Sp R ⟶ X} {g n : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} {η : Fin n → Fin g → R} (h : CutsHT t p x e η) {J : Fin g → Fin n}
    (hN : ∀ j, ∃ N : Fin g → R, ∀ i, η j i = ∑ l, N l * η (J l) i) : CutsHT t p x e fun l => η (J l) := by
  intro C κ a v hv
  rw [h C κ a v hv]
  refine ⟨fun k l => k (J l), fun k j => ?_⟩
  obtain ⟨N, hN⟩ := hN j
  have e1 : ∑ i, (κ (η j i) : ↥C.S) * a i = ∑ l, (κ (N l) : ↥C.S) * ∑ i, (κ (η (J l) i) : ↥C.S) * a i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN i, map_sum]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    push_cast
    ring
  rw [e1]
  exact (intO ↥C.S).sum_mem fun l _ => (intO ↥C.S).mul_mem (κ (N l)).2 (k l)

/- English proof (translation)
Introduce `h0`. Establish `h1 : B.const (q : O) = 0`. Apply `fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _)` to reduce the goal to its premises. Use `congrArg (fnOf V hV) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`.

Rewrite using `[Vert.Model.const, map_natCast, map_natCast, map_zero, this]`. Use `B.gen_le_basicOpen (Nat.cast_ne_zero.2 hq : (q : O) ≠ 0) B.genericPoint_mem_gen` as an intermediate fact. Rewrite `this` using `[h1, Scheme.basicOpen_zero]`. Conclude with `this`.
-/
theorem natCast_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : Vert.Model O)
    {V : B.X.Opens} (hV : genericPoint B.X ∈ V) {q : ℕ} (hq : q ≠ 0) : (q : Γ(B.X, V)) ≠ 0 := by
  intro h0
  have h1 : B.const (q : O) = 0 := by
    apply fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _)
    have := congrArg (fnOf V hV) h0
    rw [map_natCast, map_zero] at this
    rw [Vert.Model.const, map_natCast, map_natCast, map_zero, this]
  have := B.gen_le_basicOpen (Nat.cast_ne_zero.2 hq : (q : O) ≠ 0) B.genericPoint_mem_gen
  rw [h1, Scheme.basicOpen_zero] at this
  exact this

/- English proof (translation)
Use `choose u hu huJ using hdiv`. Take `⟨W, hyW, hW⟩` from `InvertIdeal.exists_common_open (x := y) hu`. Use `choose s hsu using hW`. Take `⟨U, hU, hyU, hUle⟩` from `exists_isAffineOpen_mem_and_subset (X := S') (x := y) (U := W ⊓ φ ⁻¹ᵁ V.1) ⟨hyW, hy⟩`. Establish `hle : U ≤ φ ⁻¹ᵁ V.1` using `fun z hz => (hUle hz).2`.

Establish `hle' : U ≤ W` using `fun z hz => (hUle hz).1`. Establish `hgU : genericPoint S' ∈ U` using `gen_mem hyU`. Establish `: Nonempty U` using `⟨⟨y, hyU⟩⟩`. Set `ψ : Γ(S, V.1) →+* Γ(S', U)` to `(φ.appLE V.1 U hle).hom`. Establish `hx : hU.fromSpec ≫ φ ≫ ρ = spMap ψ ≫ V.2.fromSpec ≫ ρ`.

Rewrite using `[← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec φ V.2 hU hle, Category.assoc]`. Both sides reduce to the same expression. Establish `hfn (K : Fin g → Fin n) : fnOf U hgU (rowMinor (fun j i => ψ (η j i)) K) = fnMap φ hη (fnOf V.1 hV (rowMinor η K))`. Rewrite using `[CorankOne.fnMap_fnOf_appLE φ hη hle hV hgU, ← map_rowMinor]`. Establish `hN` using `exists_comb_of_dvd (η := fun j i => ψ (η j i)) (J := J) (fun h0 => by`.

Establish `e` using `hfn J`. Rewrite `e` using `[h0, map_zero]`. Conclude with `hJ ((map_eq_zero_iff _ (fnMap φ hη).injective).1 e.symm)) fun K => ⟨resG S' hle' (s K), fnOf_injective _ hgU (by rw [map_mul, hfn, hfn, fnOf_resG, hsu, mul_comm, huJ])⟩`. Use `⟨⟨U, hU⟩, g, fun i => spMap (dualMap ψ) ≫ e i, fun l i => ψ (η (J l) i), hyU, ?_, spansP_rows p (spansP_map p hs ψ) hN, ?_⟩` and prove the remaining obligations. Conclude with `hx ▸ isTanBasis_map t he ψ`.

Conclude with `hx ▸ cutsHT_rows t p (cutsHT_map t p hc ψ) hN`.
-/
theorem chart {S S' : Scheme.{0}} [IsIntegral S] [IsIntegral S'] (φ : S' ⟶ S) (ρ : S ⟶ X)
    (hη : φ (genericPoint S') ⤳ genericPoint S) (V : S.affineOpens) (hV : genericPoint S ∈ V.1) {g n : ℕ}
    {e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)} {η : Fin n → Fin g → Γ(S, V.1)}
    (he : IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e) (hs : SpansP p η)
    (hc : CutsHT t p (A := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e η) (J : Fin g → Fin n) (y : S') (hy : y ∈ φ ⁻¹ᵁ V.1)
    (hJ : fnOf V.1 hV (rowMinor η J) ≠ 0)
    (hdiv : ∀ K : Fin g → Fin n, ∃ u, RegAt y u ∧
      u * fnMap φ hη (fnOf V.1 hV (rowMinor η J)) = fnMap φ hη (fnOf V.1 hV (rowMinor η K))) :
    ∃ (V' : S'.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S', V'.1)) ⟶ t.G.left))
      (η : Fin g → Fin g → Γ(S', V'.1)), y ∈ V'.1 ∧ IsTanBasis t (R := Γ(S', V'.1)) (V'.2.fromSpec ≫ φ ≫ ρ) e ∧
        SpansP p η ∧ CutsHT t p (A := Γ(S', V'.1)) (V'.2.fromSpec ≫ φ ≫ ρ) e η := by
  classical
  choose u hu huJ using hdiv
  obtain ⟨W, hyW, hW⟩ := InvertIdeal.exists_common_open (x := y) hu
  choose s hsu using hW
  obtain ⟨U, hU, hyU, hUle⟩ := exists_isAffineOpen_mem_and_subset (X := S') (x := y) (U := W ⊓ φ ⁻¹ᵁ V.1) ⟨hyW, hy⟩
  have hle : U ≤ φ ⁻¹ᵁ V.1 := fun z hz => (hUle hz).2
  have hle' : U ≤ W := fun z hz => (hUle hz).1
  have hgU : genericPoint S' ∈ U := gen_mem hyU
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  let ψ : Γ(S, V.1) →+* Γ(S', U) := (φ.appLE V.1 U hle).hom
  have hx : hU.fromSpec ≫ φ ≫ ρ = spMap ψ ≫ V.2.fromSpec ≫ ρ := by
    rw [← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec φ V.2 hU hle, Category.assoc]
    rfl
  have hfn (K : Fin g → Fin n) : fnOf U hgU (rowMinor (fun j i => ψ (η j i)) K) =
      fnMap φ hη (fnOf V.1 hV (rowMinor η K)) := by
    rw [CorankOne.fnMap_fnOf_appLE φ hη hle hV hgU, ← map_rowMinor]
  have hN := exists_comb_of_dvd (η := fun j i => ψ (η j i)) (J := J) (fun h0 => by
    have e := hfn J
    rw [h0, map_zero] at e
    exact hJ ((map_eq_zero_iff _ (fnMap φ hη).injective).1 e.symm)) fun K =>
      ⟨resG S' hle' (s K), fnOf_injective _ hgU (by rw [map_mul, hfn, hfn, fnOf_resG, hsu, mul_comm, huJ])⟩
  refine ⟨⟨U, hU⟩, g, fun i => spMap (dualMap ψ) ≫ e i, fun l i => ψ (η (J l) i), hyU, ?_,
    spansP_rows p (spansP_map p hs ψ) hN, ?_⟩
  · exact hx ▸ isTanBasis_map t he ψ
  · exact hx ▸ cutsHT_rows t p (cutsHT_map t p hc ψ) hN

/- English proof (translation)
Introduce `E _ _ _ H X t p hp O _ _ _ _ B hn ρ hG`. Use `choose V g n e η hxV he hs hc using hG`. Take `⟨T, hT⟩` from `CompactSpace.elim_nhds_subcover (fun x => ((V x).1 : Set B.X)) fun x => (V x).1.isOpen.mem_nhds (hxV x)`. Set `D : ∀ α : (T : Set B.X), (Fin (g α) → Fin (n α)) → B.X.functionField` to `fun α K => fnOf (V α).1 (gen_mem (hxV α)) (rowMinor (η α) K)`. Set `w : ↥(T : Set B.X) → (Σ α : (T : Set B.X), (Fin (g α) → Fin (n α))) → B.X.functionField` to `fun α j => if h : j.1 = α then D α (h ▸ j.2) else 0`.

Establish `hw (α : (T : Set B.X)) (K : Fin (g α) → Fin (n α)) : w α ⟨α, K⟩ = D α K`. Simplify using `only [w, dif_pos rfl]`. Establish `hw0 : ∀ α, ∃ j, w α j ≠ 0`. Introduce `α`. Establish `: Nonempty (V α).1` using `⟨⟨_, hxV α⟩⟩`.

Take `⟨K, hK⟩` from `exists_rowMinor_ne_zero (natCast_ne_zero B (gen_mem (hxV α)) hp.out.ne_zero) (hs α)`. Use `⟨⟨α, K⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `(map_ne_zero_iff _ (fnOf_injective _ _)).2 hK`. Take `⟨B', f, hη, hN', hrel, hmod⟩` from `CorankOneNormal.exists_modification O B hn _ _ w hw0`.

Use `⟨B', f, hN', hrel, fun y => ?_⟩` and prove the remaining obligations. Establish `hm : f.f y ∈ ⋃ x ∈ T, ((V x).1 : Set B.X)` using `by rw [hT]; trivial`. Take `⟨x, hxt, hfy⟩` from `Set.mem_iUnion₂.1 hm`. Take `⟨⟨α, K₀⟩, hK₀, hdiv⟩` from `hmod y ⟨x, hxt⟩`. Distinguish the cases in `h : α = ⟨x, hxt⟩`.

Substitute `h` using the available equality. Rewrite `hK₀` using `[hw]`. Conclude with `chart t p f.f ρ (specializes_of_eq hη) (V x) (gen_mem (hxV x)) (he x) (hs x) (hc x) K₀ y hfy hK₀ fun K => by`. Take `⟨u, hu, k⟩` from `hdiv ⟨⟨x, hxt⟩, K⟩`. Rewrite `k` using `[hw, hw]`.

Conclude with `⟨u, hu, k⟩`. Conclude with `absurd (dif_neg h) hK₀`.
-/
theorem basisSt : GlobalTheory.OmegaHT.BasisSt := by
  intro E _ _ _ H X t p hp O _ _ _ _ B hn ρ hG
  classical
  choose V g n e η hxV he hs hc using hG
  obtain ⟨T, hT⟩ := CompactSpace.elim_nhds_subcover (fun x => ((V x).1 : Set B.X))
    fun x => (V x).1.isOpen.mem_nhds (hxV x)
  let D : ∀ α : (T : Set B.X), (Fin (g α) → Fin (n α)) → B.X.functionField :=
    fun α K => fnOf (V α).1 (gen_mem (hxV α)) (rowMinor (η α) K)
  let w : ↥(T : Set B.X) → (Σ α : (T : Set B.X), (Fin (g α) → Fin (n α))) → B.X.functionField :=
    fun α j => if h : j.1 = α then D α (h ▸ j.2) else 0
  have hw (α : (T : Set B.X)) (K : Fin (g α) → Fin (n α)) : w α ⟨α, K⟩ = D α K := by
    simp only [w, dif_pos rfl]
  have hw0 : ∀ α, ∃ j, w α j ≠ 0 := by
    intro α
    have : Nonempty (V α).1 := ⟨⟨_, hxV α⟩⟩
    obtain ⟨K, hK⟩ := exists_rowMinor_ne_zero (natCast_ne_zero B (gen_mem (hxV α)) hp.out.ne_zero) (hs α)
    refine ⟨⟨α, K⟩, ?_⟩
    rw [hw]
    exact (map_ne_zero_iff _ (fnOf_injective _ _)).2 hK
  obtain ⟨B', f, hη, hN', hrel, hmod⟩ := CorankOneNormal.exists_modification O B hn _ _ w hw0
  refine ⟨B', f, hN', hrel, fun y => ?_⟩
  have hm : f.f y ∈ ⋃ x ∈ T, ((V x).1 : Set B.X) := by rw [hT]; trivial
  obtain ⟨x, hxt, hfy⟩ := Set.mem_iUnion₂.1 hm
  obtain ⟨⟨α, K₀⟩, hK₀, hdiv⟩ := hmod y ⟨x, hxt⟩
  by_cases h : α = ⟨x, hxt⟩
  · subst h
    rw [hw] at hK₀
    exact chart t p f.f ρ (specializes_of_eq hη) (V x) (gen_mem (hxV x)) (he x) (hs x) (hc x) K₀ y hfy hK₀
      fun K => by
        obtain ⟨u, hu, k⟩ := hdiv ⟨⟨x, hxt⟩, K⟩
        rw [hw, hw] at k
        exact ⟨u, hu, k⟩
  · exact absurd (dif_neg h) hK₀

end GlobalTheory.OmegaHT.RankForms
