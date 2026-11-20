import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlockStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RefRoot

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Iic_pred {N : ℕ} (i : Fin N) (hi : 0 < (i : ℕ)) :
    Finset.Iic i = insert i (Finset.Iic (⟨(i : ℕ) - 1, by omega⟩ : Fin N)) := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
  omega

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Iic_zero {N : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) : Finset.Iic i = {i} := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
  omega

/- English proof (translation)
Simplify using `only [Finset.mem_Iic, Fin.le_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_mem_Iic_pred {N : ℕ} (i : Fin N) (hi : 0 < (i : ℕ)) :
    i ∉ Finset.Iic (⟨(i : ℕ) - 1, by omega⟩ : Fin N) := by
  simp only [Finset.mem_Iic, Fin.le_def]
  omega

/- English proof (translation)
Introduce `i`. Take `⟨n, hn⟩` from `i`. Proceed by induction on `n with`. Consider the case `zero => rw [Iic_zero _ rfl, Finset.sum_singleton]`. Conclude with `h0 _ rfl`.

Consider the case `succ n ih`. Establish `hi : 0 < ((⟨n + 1, hn⟩ : Fin N) : ℕ)` using `Nat.succ_pos n`. Establish `h1 : g ⟨n + 1, hn⟩ = f ⟨n, by omega⟩ - f ⟨n + 1, hn⟩` using `hs _ hi`. Establish `h2 : ∑ k ∈ Finset.Iic (⟨(⟨n + 1, hn⟩ : Fin N) - 1, by simp; omega⟩ : Fin N), g k = - f ⟨n, by omega⟩` using `ih (by omega)`. Rewrite using `[Iic_pred _ hi, Finset.sum_insert (not_mem_Iic_pred _ hi), h1, h2]`.

Normalize the expressions using the abelian group laws.
-/
theorem sum_Iic_step {N : ℕ} {M : Type} [AddCommGroup M] (f g : Fin N → M)
    (h0 : ∀ i : Fin N, (i : ℕ) = 0 → g i = - f i)
    (hs : ∀ (i : Fin N) (hi : 0 < (i : ℕ)), g i = f ⟨(i : ℕ) - 1, by omega⟩ - f i) :
    ∀ i : Fin N, ∑ k ∈ Finset.Iic i, g k = - f i := by
  intro i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => rw [Iic_zero _ rfl, Finset.sum_singleton]; exact h0 _ rfl
  | succ n ih =>
    have hi : 0 < ((⟨n + 1, hn⟩ : Fin N) : ℕ) := Nat.succ_pos n
    have h1 : g ⟨n + 1, hn⟩ = f ⟨n, by omega⟩ - f ⟨n + 1, hn⟩ := hs _ hi
    have h2 : ∑ k ∈ Finset.Iic (⟨(⟨n + 1, hn⟩ : Fin N) - 1, by simp; omega⟩ : Fin N), g k = - f ⟨n, by omega⟩ :=
      ih (by omega)
    rw [Iic_pred _ hi, Finset.sum_insert (not_mem_Iic_pred _ hi), h1, h2]
    abel

def prevLine {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : HermLine G.J :=
  if h : (r.2 : ℕ) = 0 then Top.trivLine G.J
  else A.Re.line (some (r.1, ⟨(r.2 : ℕ) - 1, by have := r.2.2; omega⟩)) t

def stepLine {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : HermLine G.J :=
  PB.combLine ![prevLine A t r, A.Re.line (some r) t] ![1, -1]

/- English proof (translation)
Simplify using `[stepLine, PB.combLine_h, Fin.prod_univ_two, div_eq_mul_inv]`.
-/
theorem stepLine_h {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) (z : (Σ k, G.J k) → ℂ) :
    (stepLine A t r).h z = (prevLine A t r).h z / (A.Re.line (some r) t).h z := by
  simp [stepLine, PB.combLine_h, Fin.prod_univ_two, div_eq_mul_inv]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Take `⟨τ, i⟩` from `r`. Establish `hl : ∀ i' : Fin (D.p + D.q), (A.Re.line (some (τ, i')) t).a b = -∑ k ∈ Finset.Iic i', G.xdeg (τ, k) b`. Introduce `i'`. Rewrite using `[A.Re.line_deg, A.fund_deg]`.

Simplify using `[Finset.sum_apply]`. Simplify using `only [stepLine, PB.combLine_a, Fin.sum_univ_two]`. Distinguish the cases in `h : (i : ℕ) = 0`. Simplify using `only [prevLine, dif_pos h]`. Simplify using `[Top.trivLine, hl, Iic_zero i h]`.

Establish `hi : 0 < (i : ℕ)` using `Nat.pos_of_ne_zero h`. Simplify using `only [prevLine, dif_neg h]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, hl]`. Rewrite using `[Iic_pred i hi, Finset.sum_insert (not_mem_Iic_pred i hi)]`. Simplify using the standard rewrite rules.
-/
theorem stepLine_a {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) :
    (stepLine A t r).a = G.xdeg r := by
  funext b
  obtain ⟨τ, i⟩ := r
  have hl : ∀ i' : Fin (D.p + D.q), (A.Re.line (some (τ, i')) t).a b = -∑ k ∈ Finset.Iic i', G.xdeg (τ, k) b := by
    intro i'
    rw [A.Re.line_deg, A.fund_deg]
    simp [Finset.sum_apply]
  simp only [stepLine, PB.combLine_a, Fin.sum_univ_two]
  by_cases h : (i : ℕ) = 0
  · simp only [prevLine, dif_pos h]
    simp [Top.trivLine, hl, Iic_zero i h]
  · have hi : 0 < (i : ℕ) := Nat.pos_of_ne_zero h
    simp only [prevLine, dif_neg h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hl]
    rw [Iic_pred i hi, Finset.sum_insert (not_mem_Iic_pred i hi)]
    simp

/- English proof (translation)
Establish `hp : IsSmoothHerm (prevLine A t r)`. Unfold `prevLine`. Use `split_ifs with h`. Conclude with `contDiffOn_const`. Conclude with `(A.conj _ t).1`.

Establish `hl` using `(A.conj (some r) t).1`. Establish `e : (stepLine A t r).h = fun z => (prevLine A t r).h z / (A.Re.line (some r) t).h z`. Use function extensionality and compare the values at `(stepLine_h A t r)`. Use `show ContDiffOn _ _ (stepLine A t r).h _`. Rewrite using `[e]`.

Conclude with `ContDiffOn.div hp hl fun z hz => ((A.Re.line (some r) t).pos z hz).ne'`.
-/
theorem stepLine_smooth {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : IsSmoothHerm (stepLine A t r) := by
  have hp : IsSmoothHerm (prevLine A t r) := by
    unfold prevLine
    split_ifs with h
    · exact contDiffOn_const
    · exact (A.conj _ t).1
  have hl := (A.conj (some r) t).1
  have e : (stepLine A t r).h = fun z => (prevLine A t r).h z / (A.Re.line (some r) t).h z :=
    funext (stepLine_h A t r)
  show ContDiffOn _ _ (stepLine A t r).h _
  rw [e]
  exact ContDiffOn.div hp hl fun z hz => ((A.Re.line (some r) t).pos z hz).ne'

/- English proof (translation)
Establish `hp : IsConjInvariantH (prevLine A t r)`. Unfold `prevLine`. Use `split_ifs with h`. Introduce `z`. Both sides reduce to the same expression.

Conclude with `(A.conj _ t).2`. Introduce `z`. Rewrite using `[stepLine_h, stepLine_h, hp z, (A.conj (some r) t).2 z]`.
-/
theorem stepLine_conj {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : IsConjInvariantH (stepLine A t r) := by
  have hp : IsConjInvariantH (prevLine A t r) := by
    unfold prevLine
    split_ifs with h
    · intro z; rfl
    · exact (A.conj _ t).2
  intro z
  rw [stepLine_h, stepLine_h, hp z, (A.conj (some r) t).2 z]

/- English proof (translation)
Use `sum_Iic_step (fun i' : Fin (D.p + D.q) => Real.log ((A.Re.line (some (τ, i')) t).h z)) (fun k => Real.log ((stepLine A t (τ, k)).h z)) (fun k hk => by` as an intermediate fact. Simplify using `only [stepLine_h, prevLine, dif_pos hk, Top.trivLine]`. Rewrite using `[Real.log_div one_ne_zero ((A.Re.line _ t).pos z hz).ne']`. Use the proof step `simp) (fun k hk => by`. Simplify using `only [stepLine_h, prevLine, dif_neg hk.ne']`.

Rewrite using `[Real.log_div ((A.Re.line _ t).pos z hz).ne' ((A.Re.line _ t).pos z hz).ne']) i`. Rewrite using `[this, neg_neg]`.
-/
theorem log_line_eq {G : RefGeo Y} (A : G.An) (t : ℝ) (τ : CMType H) (i : Fin (D.p + D.q))
    (z : (Σ k, G.J k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.Re.line (some (τ, i)) t).h z) =
      -∑ k ∈ Finset.Iic i, Real.log ((stepLine A t (τ, k)).h z) := by
  have := sum_Iic_step (fun i' : Fin (D.p + D.q) => Real.log ((A.Re.line (some (τ, i')) t).h z))
    (fun k => Real.log ((stepLine A t (τ, k)).h z)) (fun k hk => by
      simp only [stepLine_h, prevLine, dif_pos hk, Top.trivLine]
      rw [Real.log_div one_ne_zero ((A.Re.line _ t).pos z hz).ne']
      simp) (fun k hk => by
      simp only [stepLine_h, prevLine, dif_neg hk.ne']
      rw [Real.log_div ((A.Re.line _ t).pos z hz).ne' ((A.Re.line _ t).pos z hz).ne']) i
  rw [this, neg_neg]

end Step

section Build

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

@[reducible] def refModel {G : RefGeo Y} (A : G.An) (hb : Birational G.y) (k : ℕ) (hk : 0 < k) (δ : ℕ) (hδ : 0 < δ) :
    Top.RootModel (CMType H) (D.p + D.q) where
  K := G.K
  «ι» := G.J
  Ω := G.Ω
  y := G.y
  arith := A.Re.arith
  birational := hb
  xdeg := G.xdeg
  x t r := stepLine A t r
  x_deg t r := stepLine_a A t r
  x_smooth t r := stepLine_smooth A t r
  x_conj t r := stepLine_conj A t r
  kA := k
  kA_pos := hk
  A := A.Re.ref none
  A_smooth := A.Re.ref_smooth none
  A_conj := fun z => by
    rw [A.none_h, A.none_h]
    simp only [RCLike.norm_conj]
  δ := δ
  δ_pos := hδ

@[reducible] def refFixed {G : RefGeo Y} (A : G.An) (Mf : LieModel Y.t.G (G.𝔐.ξ ≫ G.𝔐.f) G.𝔐.Li) (m : ℕ)
    (ix : Fin (m + 1) ≃ G.J G.k₀)
    (gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤)
    (pt : A.Sys.X → Fin (m + 1) → ℂ) (pt_ne : ∀ x, pt x ≠ 0) (pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x')
    (k q' : ℕ) (hq : 0 < q') (n : RootIx D → ℤ) (s : G.Ω) (hs : s ≠ 0) : FixedData Y A.Sys where
  Ωf := G.Ω
  ξf := G.𝔐.ξ ≫ G.𝔐.f
  Lif := G.𝔐.Li
  Mf := Mf
  bf := G.Fl.b
  m := m
  yf i := G.y ⟨G.k₀, ix i⟩
  generate := gen
  hf u := Real.sqrt (∑ i, ‖u i‖ ^ 2)
  kA := k
  pt := pt
  pt_ne := pt_ne
  pt_inj := pt_inj
  pos := A.pos
  ph_none := A.ph_none
  q' := q'
  q'_pos := hq
  n := n
  sE := s
  sE_ne := hs

/- English proof (translation)
Establish `: dualMap (RingHom.id R) = RingHom.id _`. Apply the tactic sequence `ext a <;> simp [dualMap]`. Rewrite using `[this]`. Simplify using `[spMap]`.
-/
theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  have : dualMap (RingHom.id R) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  simp [spMap]

def refOrigin {G : RefGeo Y} (A : G.An) (hb : Birational G.y) (k : ℕ) (hk : 0 < k) (hδ : 0 < Module.finrank ℚ c.F * G.Fl.deg)
    (Mf : LieModel Y.t.G (G.𝔐.ξ ≫ G.𝔐.f) G.𝔐.Li)
    (hMf : ∀ e, (Mf.pt e).left = (G.𝔐.M.pt e).left ≫ G.𝔐.m.φ) (m : ℕ)
    (ix : Fin (m + 1) ≃ G.J G.k₀)
    (gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤)
    (pt : A.Sys.X → Fin (m + 1) → ℂ) (pt_ne : ∀ x, pt x ≠ 0) (pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x')
    (hpt : ∀ x, ∃ a : ℂ, (fun i => A.Re.R.lift x x ⟨G.k₀, ix i⟩) = a • pt (A.Re.π x))
    (q' : ℕ) (hq : 0 < q') (n : RootIx D → ℤ) (s : G.Ω) (hs : s ≠ 0)
    (hconst : ∀ a : G.Ω, IsAlgebraic ℤ a → a ∈ G.𝔐.cst.range) (heff : G.IsEff n q' s) :
    RootOrigin Y ∅ (refModel A hb k hk _ hδ) (refFixed A Mf m ix gen pt pt_ne pt_inj k q' hq n s hs) where
  𝔐 := G.𝔐
  Fl := G.Fl
  g := RingHom.id G.Ω
  g_over := by
    show G.𝔐.ξ ≫ G.𝔐.f = spMap (RingHom.id G.Ω) ≫ G.𝔐.ξ ≫ G.𝔐.f
    simp [spMap]
  g_flag s i := by
    show (G.𝔐.M.pt (G.Fl.b s i)).left ≫ G.𝔐.m.φ = spMap (dualMap (RingHom.id G.Ω)) ≫ (Mf.pt (G.Fl.b s i)).left
    rw [spMap_dualMap_id, hMf]
    exact (Category.id_comp _).symm
  g_deg := (Module.finrank_self G.Ω).trans G.deg_one.symm
  g_const a ha := hconst a ha
  δ_eq := rfl
  e := G.e
  lines := G.lines
  sing := A.sing
  sing_deg := A.sing_deg
  hodge := A.hodge
  k₀ := G.k₀
  ix := ix
  y_eq i := rfl
  kA_eq := rfl
  A_deg := A.none_deg
  A_h z hz := by
    show (A.Re.ref none).h z = Real.sqrt (∑ i, ‖z ⟨G.k₀, ix i⟩‖ ^ 2)
    rw [A.none_h]
    congr 1
    exact (Equiv.sum_comp ix fun i => ‖z ⟨G.k₀, i⟩‖ ^ 2).symm
  eff p hp i t hi ht := heff p hp (ix i) t
    ⟨hi.1, fun c' => by simpa using hi.2 (ix.symm c')⟩ ht
  Re := A.Re
  Re_deg := A.deg_one.trans G.deg_one.symm
  π_pt := hpt
  interior := A.interior
  fund_deg := A.fund_deg
  fund_sing := A.fund_sing
  fund_reg τ i t h0 h1 z hz := log_line_eq A t τ i z hz.1
  ref_none := ⟨rfl, fun _ _ => rfl⟩

end Build

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `h.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Simplify using `only [genMap, genCpt, TopCat.Presheaf.stalkSpecializes_refl]`. Conclude with `congrArg (fun f : X.presheaf.stalk (genPt ξ) ⟶ _ => f.hom s) (Category.id_comp (Scheme.stalkClosedPointTo ξ))`.
-/
theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, rfl⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  simp only [genMap, genCpt, TopCat.Presheaf.stalkSpecializes_refl]
  exact congrArg (fun f : X.presheaf.stalk (genPt ξ) ⟶ _ => f.hom s) (Category.id_comp (Scheme.stalkClosedPointTo ξ))

/- English proof (translation)
Establish `hc : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r (genCpt ξ)` using `fun r hr hf => hf ⟨Nat.cast_ne_zero.2 hr.ne_zero, mem_regAt_genCpt h _, mem_regAt_genCpt h _⟩`. Take `⟨⟨i, hi⟩, h2⟩` from `he (genCpt ξ) hc`. Use `⟨⟨i⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `a _`.

Take `⟨s, hs, hu, hsa⟩` from `(h2 i hi).1 a (mem_regAt_genCpt h a)`. Establish `hle : ∀ b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i), b ∈ Subfield.closure (Set.range fun ij : κ × κ => x ij.1 / x ij.2)`. Introduce `b hb`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem b hb`.

Take `⟨j, rfl⟩` from `hb`. Conclude with `Subfield.subset_closure ⟨(j, i), rfl⟩`. Consider the case `algebraMap r`. Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem _ r`.

Consider the case `add _ _ _ _ h1 h2 => exact add_mem h1 h2`. Consider the case `mul _ _ _ _ h1 h2 => exact mul_mem h1 h2`. Establish `e : a = s * a / s` using `by rw [mul_div_cancel_left₀ _ hu.1]`. Rewrite using `[e]`. Conclude with `div_mem (hle _ hsa) (hle _ hs)`.
-/
theorem EmbedsGeneric.exists_closure {κ : Type} {x : κ → Ω} (h : IsCptGen ξ) (he : EmbedsGeneric ξ x) :
    Nonempty κ ∧ Subfield.closure (Set.range fun ij : κ × κ => x ij.1 / x ij.2) = ⊤ := by
  have hc : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r (genCpt ξ) := fun r hr hf =>
    hf ⟨Nat.cast_ne_zero.2 hr.ne_zero, mem_regAt_genCpt h _, mem_regAt_genCpt h _⟩
  obtain ⟨⟨i, hi⟩, h2⟩ := he (genCpt ξ) hc
  refine ⟨⟨i⟩, ?_⟩
  rw [eq_top_iff]
  intro a _
  obtain ⟨s, hs, hu, hsa⟩ := (h2 i hi).1 a (mem_regAt_genCpt h a)
  have hle : ∀ b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i),
      b ∈ Subfield.closure (Set.range fun ij : κ × κ => x ij.1 / x ij.2) := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨j, rfl⟩ := hb
      exact Subfield.subset_closure ⟨(j, i), rfl⟩
    | algebraMap r =>
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ r
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have e : a = s * a / s := by rw [mul_div_cancel_left₀ _ hu.1]
  rw [e]
  exact div_mem (hle _ hsa) (hle _ hs)

end Gen

section Main

/- English proof (translation)
Establish `h : ∀ P : Sp Ω', (spMap i ≫ ξ) P = ξ (spMap i P)` using `fun P => by simp`. Conclude with `(h _).trans (congrArg ξ (@Subsingleton.elim (PrimeSpectrum Ω) _ _ _))`.
-/
theorem genPt_comp_spMap {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : genPt (spMap i ≫ ξ) = genPt ξ := by
  have h : ∀ P : Sp Ω', (spMap i ≫ ξ) P = ξ (spMap i P) := fun P => by simp
  exact (h _).trans (congrArg ξ (@Subsingleton.elim (PrimeSpectrum Ω) _ _ _))

/- English proof (translation)
Introduce `j z hz`. Take `⟨k, hk⟩` from `A.cover (h ((B.chart j).symm z))`. Establish `h1` using `hh.2 j k z ⟨hz.1, hk⟩`. Establish `h2` using `hg k ((A.chart k) (h ((B.chart j).symm z))) ⟨(A.chart k).map_source hk, by`. Simplify `hz.2⟩` using `[(A.chart k).left_inv hk]`.

Establish `h3` using `h2.comp_of_eq h1 rfl`. Use `h3.congr ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (h ∘ (B.chart j).symm) z` using `hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hz.1)`. Use `filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with w hw`. Conclude with `congrArg g ((A.chart k).left_inv hw)`.
-/
theorem holoOn_comp {e e' : ℕ} {M M' : Type} [TopologicalSpace M] [TopologicalSpace M']
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas e M} {B : ReciprocityTheory.AnForm.M.FinHolAtlas e' M'} {h : M' → M}
    (hh : ReciprocityTheory.AnForm.M.HoloMap B A h) {V : Set M} {g : M → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) (g ∘ h) := by
  intro j z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  have h1 := hh.2 j k z ⟨hz.1, hk⟩
  have h2 := hg k ((A.chart k) (h ((B.chart j).symm z)))
    ⟨(A.chart k).map_source hk, by
      simpa [(A.chart k).left_inv hk] using hz.2⟩
  have h3 := h2.comp_of_eq h1 rfl
  refine h3.congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with w hw
  exact congrArg g ((A.chart k).left_inv hw)

end Main

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y G A ν k q' s ⟨inv, hinvH, hinv⟩ hsplit hk hq hs heff`. Take `⟨hne, hclos⟩` from `EmbedsGeneric.exists_closure (x := fun i : G.J G.k₀ => G.y ⟨G.k₀, i⟩) G.𝔐.tie.gen G.embeds`. Take `⟨m, hm⟩ : ∃ m, Fintype.card (G.J G.k₀) = m + 1` from `⟨Fintype.card (G.J G.k₀) - 1, by have := Fintype.card_pos (α := G.J G.k₀); omega⟩`. Set `ix : Fin (m + 1) ≃ G.J G.k₀` to `(Fintype.equivFinOfCardEq hm).symm`. Establish `gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) => G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤`.

Rewrite using `[← hclos]`. Use `congr 1`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ij, rfl⟩`.

Conclude with `⟨(ix ij.1, ix ij.2), rfl⟩`. Introduce and unpack `⟨ij, rfl⟩`. Conclude with `⟨(ix.symm ij.1, ix.symm ij.2), by simp⟩`. Take `⟨Mf, hMf⟩` from `GlobalTheory.T.lie_model_push_along_map E H _ _ G.𝔐.t Y.t G.𝔐.f G.𝔐.m G.Ω G.𝔐.ξ G.𝔐.Li G.𝔐.M`. Use `haveI : Nonempty G.K := ⟨G.k₀⟩`.

Establish `hb : Birational G.y` using `(GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl (RingOfIntegers.coe_injective)).1`. Establish `hδ : 0 < Module.finrank ℚ c.F * G.Fl.deg`. Rewrite using `[G.deg_one, _root_.mul_one]`. Use `haveI := c.fin`. Conclude with `Module.finrank_pos`.

Establish `hcov : ∀ x : A.Sys.X, A.Re.π (inv x) = x` using `fun x => by`. Take `⟨u, rfl⟩` from `A.π_bij.2 x`. Rewrite using `[hinv]`. Set `pt : A.Sys.X → Fin (m + 1) → ℂ` to `fun x i => A.Re.R.lift (inv x) (inv x) ⟨G.k₀, ix i⟩`. Establish `hmem : ∀ x, A.Re.R.lift x x ∈ mcPts (mCoordIdeal G.y)` using `fun x => A.embedded.mem x x (A.embedded.mem_U x)`.

Establish `pt_ne : ∀ x, pt x ≠ 0` using `fun x h => by`. Take `⟨i, hi⟩` from `(hmem (inv x)).1 G.k₀`. Conclude with `hi (by simpa [pt] using congrFun h (ix.symm i))`. Establish `pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x'` using `fun x x' a h => by`. Establish `ho` using `GlobalTheory.T.same_orbit_of_proportional_coords G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ (hmem (inv x)) _ (hmem (inv x')) a (fun i => by simpa [pt] using congrFun h (ix.symm i))`.

Use `A.embedded.inj _ _ ho` as an intermediate fact. Rewrite using `[← hcov x, this, hcov]`. Establish `hpt : ∀ x, ∃ a : ℂ, (fun i => A.Re.R.lift x x ⟨G.k₀, ix i⟩) = a • pt (A.Re.π x)` using `fun x => ⟨1, by simp [pt, hinv]⟩`. Establish `hconst` using `GlobalTheory.T.algebraic_constants_in_range E H D l Xo c Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl hsplit G.deg_one`. Use `⟨refFixed A Mf m ix gen pt pt_ne pt_inj k q' hq (fun r => (k * q' : ℕ) * ν r) s hs, refModel A hb k hk _ hδ, refOrigin A hb k hk hδ Mf hMf m ix gen pt pt_ne pt_inj hpt q' hq _ s hs hconst heff, ?_, rfl, rfl, fun _ => rfl, G.deg_one, A.J_top, ?_, A.embedded, A.π_bij, ?_⟩` and prove the remaining obligations.

Use `show genPt (G.𝔐.ξ ≫ G.𝔐.f) = _`. Establish `e : G.𝔐.ξ ≫ G.𝔐.f = spMap G.𝔐.fn ≫ G.𝔐.ξ₀` using `G.𝔐.fn_over`. Rewrite using `[e]`. Conclude with `genPt_comp_spMap _ _`. Conclude with `GlobalTheory.T.ample_of_single_coord_block G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ _ G.𝔐.tie G.embeds A.none_deg.1 A.none_deg.2`.

Introduce `x`. Establish `hx₁` using `A.Re.R.mem_U (inv x)`. Use `⟨inv ⁻¹' A.Re.R.U (inv x), fun y i => A.Re.R.lift (inv x) (inv y) ⟨G.k₀, ix i⟩, (A.Re.R.isOpen_U _).preimage hinvH.1, hx₁, fun i => holoOn_comp hinvH (A.Re.R.holo (inv x) _), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨c', hc', e⟩` from `A.embedded.compat (inv x) (inv y) (inv y) ⟨hy, A.Re.R.mem_U _⟩`.

Conclude with `⟨c' G.k₀, hc' _, funext fun i => congrFun e ⟨G.k₀, ix i⟩⟩`. Introduce `p hp j hj`. Take `⟨j₁, hj₁⟩` from `A.Re.R.A.cover (inv x)`. Take `⟨h1, h2⟩` from `GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ _ A.Re.R.A _ _ A.embedded (Fin (m + 1)) ix (inv x) p hp j₁ hj₁`. Conclude with `GlobalTheory.T.holomorphic_inverse_chart_value _ _ _ _ A.Re.R.A A.Sys.A A.Re.π inv A.Re.holo hinvH A.π_bij hinv (fun y i => A.Re.R.lift (inv x) y ⟨G.k₀, ix i⟩ / A.Re.R.lift (inv x) y ⟨G.k₀, ix p⟩) x j₁ j hj₁ hj h1 h2`.
-/
theorem refRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  intro E _ _ _ H D l Xo c Y G A ν k q' s ⟨inv, hinvH, hinv⟩ hsplit hk hq hs heff
  classical
  obtain ⟨hne, hclos⟩ := EmbedsGeneric.exists_closure (x := fun i : G.J G.k₀ => G.y ⟨G.k₀, i⟩) G.𝔐.tie.gen G.embeds
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (G.J G.k₀) = m + 1 :=
    ⟨Fintype.card (G.J G.k₀) - 1, by have := Fintype.card_pos (α := G.J G.k₀); omega⟩
  let ix : Fin (m + 1) ≃ G.J G.k₀ := (Fintype.equivFinOfCardEq hm).symm
  have gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤ := by
    rw [← hclos]
    congr 1
    ext a
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨(ix ij.1, ix ij.2), rfl⟩
    · rintro ⟨ij, rfl⟩
      exact ⟨(ix.symm ij.1, ix.symm ij.2), by simp⟩
  obtain ⟨Mf, hMf⟩ := GlobalTheory.T.lie_model_push_along_map E H _ _ G.𝔐.t Y.t G.𝔐.f G.𝔐.m G.Ω G.𝔐.ξ G.𝔐.Li G.𝔐.M
  haveI : Nonempty G.K := ⟨G.k₀⟩
  have hb : Birational G.y := (GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl
    (RingOfIntegers.coe_injective)).1
  have hδ : 0 < Module.finrank ℚ c.F * G.Fl.deg := by
    rw [G.deg_one, _root_.mul_one]
    haveI := c.fin
    exact Module.finrank_pos
  have hcov : ∀ x : A.Sys.X, A.Re.π (inv x) = x := fun x => by
    obtain ⟨u, rfl⟩ := A.π_bij.2 x
    rw [hinv]
  let pt : A.Sys.X → Fin (m + 1) → ℂ := fun x i => A.Re.R.lift (inv x) (inv x) ⟨G.k₀, ix i⟩
  have hmem : ∀ x, A.Re.R.lift x x ∈ mcPts (mCoordIdeal G.y) := fun x =>
    A.embedded.mem x x (A.embedded.mem_U x)
  have pt_ne : ∀ x, pt x ≠ 0 := fun x h => by
    obtain ⟨i, hi⟩ := (hmem (inv x)).1 G.k₀
    exact hi (by simpa [pt] using congrFun h (ix.symm i))
  have pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x' := fun x x' a h => by
    have ho := GlobalTheory.T.same_orbit_of_proportional_coords G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ (hmem (inv x)) _ (hmem (inv x')) a
      (fun i => by simpa [pt] using congrFun h (ix.symm i))
    have := A.embedded.inj _ _ ho
    rw [← hcov x, this, hcov]
  have hpt : ∀ x, ∃ a : ℂ, (fun i => A.Re.R.lift x x ⟨G.k₀, ix i⟩) = a • pt (A.Re.π x) := fun x =>
    ⟨1, by simp [pt, hinv]⟩
  have hconst := GlobalTheory.T.algebraic_constants_in_range E H D l Xo c Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl hsplit G.deg_one
  refine ⟨refFixed A Mf m ix gen pt pt_ne pt_inj k q' hq (fun r => (k * q' : ℕ) * ν r) s hs,
    refModel A hb k hk _ hδ,
    refOrigin A hb k hk hδ Mf hMf m ix gen pt pt_ne pt_inj hpt q' hq _ s hs hconst heff,
    ?_, rfl, rfl, fun _ => rfl, G.deg_one, A.J_top, ?_, A.embedded, A.π_bij, ?_⟩
  · show genPt (G.𝔐.ξ ≫ G.𝔐.f) = _
    have e : G.𝔐.ξ ≫ G.𝔐.f = spMap G.𝔐.fn ≫ G.𝔐.ξ₀ := G.𝔐.fn_over
    rw [e]
    exact genPt_comp_spMap _ _
  · exact GlobalTheory.T.ample_of_single_coord_block G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ _ G.𝔐.tie G.embeds A.none_deg.1 A.none_deg.2
  · intro x
    have hx₁ := A.Re.R.mem_U (inv x)
    refine ⟨inv ⁻¹' A.Re.R.U (inv x), fun y i => A.Re.R.lift (inv x) (inv y) ⟨G.k₀, ix i⟩,
      (A.Re.R.isOpen_U _).preimage hinvH.1, hx₁, fun i => holoOn_comp hinvH (A.Re.R.holo (inv x) _), ?_, ?_⟩
    · intro y hy
      obtain ⟨c', hc', e⟩ := A.embedded.compat (inv x) (inv y) (inv y) ⟨hy, A.Re.R.mem_U _⟩
      exact ⟨c' G.k₀, hc' _, funext fun i => congrFun e ⟨G.k₀, ix i⟩⟩
    · intro p hp j hj
      obtain ⟨j₁, hj₁⟩ := A.Re.R.A.cover (inv x)
      obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ _ A.Re.R.A _ _ A.embedded
        (Fin (m + 1)) ix (inv x) p hp j₁ hj₁
      exact GlobalTheory.T.holomorphic_inverse_chart_value _ _ _ _ A.Re.R.A A.Sys.A A.Re.π inv A.Re.holo hinvH A.π_bij hinv
        (fun y i => A.Re.R.lift (inv x) y ⟨G.k₀, ix i⟩ / A.Re.R.lift (inv x) y ⟨G.k₀, ix p⟩) x j₁ j hj₁ hj h1 h2

end GlobalTheory.CompanionTheory.Ar.RefRoot
