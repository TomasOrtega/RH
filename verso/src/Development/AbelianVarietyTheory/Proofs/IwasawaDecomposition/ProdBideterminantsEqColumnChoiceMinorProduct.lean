import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

/- English proof (translation)
Establish `key : ∀ {C : Type} [Fintype C] (f : C → ℕ) (c : ℕ), 0 < c → (Finset.univ.filter fun x => f x = c).card + (Finset.univ.filter fun x => c < f x).card = (Finset.univ.filter fun x => c - 1 < f x).card`. Introduce `C _ f c hc`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_filter]`. Introduce `x _ h1 h2`. Use linear arithmetic over natural numbers and integers.

Establish `fib : ∀ c, Fintype.card {x : {x // 0 < a x} // a x.1 = c} = Fintype.card {y // b y = c}`. Introduce `c`. Break down `Nat.eq_zero_or_pos c with rfl | hc` into its components or cases. Establish `h1 : IsEmpty {x : {x // 0 < a x} // a x.1 = 0}` using `⟨fun x => by have := x.1.2; have := x.2; omega⟩`. Establish `h2 : IsEmpty {y // b y = 0}` using `⟨fun y => by have := hb y.1; have := y.2; omega⟩`.

Simplify using the standard rewrite rules. Establish `e1 : Fintype.card {x : {x // 0 < a x} // a x.1 = c} = (Finset.univ.filter fun x => a x = c).card`. Rewrite using `[← Fintype.card_subtype]`. Use `Fintype.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, by have := x.2; omega⟩, x.2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Both sides reduce to the same expression. Introduce `x`. Both sides reduce to the same expression. Establish `e2 : Fintype.card {y // b y = c} = (Finset.univ.filter fun x => b x = c).card`. Rewrite using `[Fintype.card_subtype]`.

Rewrite using `[e1, e2]`. Establish `k1` using `key a c hc`. Establish `k2` using `key b c hc`. Establish `h1` using `h c`. Establish `h2` using `h (c - 1)`.

Use linear arithmetic over natural numbers and integers. Use `⟨Equiv.ofFiberEquiv (f := fun x : {x // 0 < a x} => a x.1) (g := b) (fun c => Fintype.equivOfCardEq (fib c)), fun x => ?_⟩` and prove the remaining obligations. Conclude with `Equiv.ofFiberEquiv_map _ x`.
-/
theorem exists_equiv_of_counts {A B : Type} [Fintype A] [Fintype B] (a : A → ℕ) (b : B → ℕ)
    (hb : ∀ x, 0 < b x)
    (h : ∀ t : ℕ, (Finset.univ.filter fun x => t < a x).card = (Finset.univ.filter fun x => t < b x).card) :
    ∃ e : {x // 0 < a x} ≃ B, ∀ x, b (e x) = a x.1 := by
  classical
  have key : ∀ {C : Type} [Fintype C] (f : C → ℕ) (c : ℕ), 0 < c →
      (Finset.univ.filter fun x => f x = c).card + (Finset.univ.filter fun x => c < f x).card =
        (Finset.univ.filter fun x => c - 1 < f x).card := by
    intro C _ f c hc
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      omega
  have fib : ∀ c, Fintype.card {x : {x // 0 < a x} // a x.1 = c} = Fintype.card {y // b y = c} := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · have h1 : IsEmpty {x : {x // 0 < a x} // a x.1 = 0} := ⟨fun x => by have := x.1.2; have := x.2; omega⟩
      have h2 : IsEmpty {y // b y = 0} := ⟨fun y => by have := hb y.1; have := y.2; omega⟩
      simp
    · have e1 : Fintype.card {x : {x // 0 < a x} // a x.1 = c} = (Finset.univ.filter fun x => a x = c).card := by
        rw [← Fintype.card_subtype]
        refine Fintype.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, by have := x.2; omega⟩, x.2⟩, ?_, ?_⟩
        · intro x; rfl
        · intro x; rfl
      have e2 : Fintype.card {y // b y = c} = (Finset.univ.filter fun x => b x = c).card := by
        rw [Fintype.card_subtype]
      rw [e1, e2]
      have k1 := key a c hc
      have k2 := key b c hc
      have h1 := h c
      have h2 := h (c - 1)
      omega
  refine ⟨Equiv.ofFiberEquiv (f := fun x : {x // 0 < a x} => a x.1) (g := b)
    (fun c => Fintype.equivOfCardEq (fib c)), fun x => ?_⟩
  exact Equiv.ofFiberEquiv_map _ x

/- English proof (translation)
Establish `hle : μ.rowLen t ≤ μ.rowLen 0` using `μ.rowLen_anti 0 t (Nat.zero_le _)`. Establish `: (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c) = Finset.univ.filter fun c : Fin (μ.rowLen 0) => c.val < μ.rowLen t`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]`.

Rewrite using `[this, ← Fintype.card_subtype]`. Rewrite using `[Fintype.card_congr (β := Fin (μ.rowLen t)) ⟨fun c => ⟨c.1.1, c.2⟩, fun c => ⟨⟨c.1, by have := c.2; omega⟩, c.2⟩, fun _ => rfl, fun _ => rfl⟩]`. Simplify using the standard rewrite rules.
-/
theorem card_colLen_gt (μ : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card = μ.rowLen t := by
  classical
  have hle : μ.rowLen t ≤ μ.rowLen 0 := μ.rowLen_anti 0 t (Nat.zero_le _)
  have : (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c) =
      Finset.univ.filter fun c : Fin (μ.rowLen 0) => c.val < μ.rowLen t := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  rw [this, ← Fintype.card_subtype]
  rw [Fintype.card_congr (β := Fin (μ.rowLen t))
    ⟨fun c => ⟨c.1.1, c.2⟩, fun c => ⟨⟨c.1, by have := c.2; omega⟩, c.2⟩, fun _ => rfl, fun _ => rfl⟩]
  simp

/- English proof (translation)
Substitute `e` using the available equality. Use `congr 1`. Use extensionality with `p q`. Establish `hq : (q : ℕ) < N` using `lt_of_lt_of_le q.2 hN`. Simplify using `[GL3Columns.colsOf, hq, Fin.castLE]`.
-/
theorem minor_cast {K : Type} [CommRing K] {N h h' : ℕ} (Y : Matrix (Fin N) (Fin N) K) (e : h = h') (hN : h ≤ N)
    (I : Fin h → Fin N) :
    Matrix.det (Matrix.of fun p q : Fin h => Y (I p) (Fin.castLE hN q)) =
      Matrix.det (Matrix.of fun i j : Fin h' => GL3Columns.colsOf Y (I (Fin.cast e.symm i)) (j : ℕ)) := by
  subst e
  congr 1
  ext p q
  have hq : (q : ℕ) < N := lt_of_lt_of_le q.2 hN
  simp [GL3Columns.colsOf, hq, Fin.castLE]

/- English proof (translation)
Take `⟨Kc, sz, hsz, I, hshape, hI, rfl⟩` from `hg`. Establish `count : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card = (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card`. Introduce `t`. Rewrite using `[card_colLen_gt]`. Distinguish the cases in `ht : t < N`.

Use `congrFun hshape ⟨t, ht⟩` as an intermediate fact. Rewrite using `[h1 ⟨t, ht⟩, ← this]`. Simplify using `only [Formalism.GradedWeylDivisibility.shapeDeg]`. Rewrite using `[h2 t (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `k _`.

Use `hsz k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpos : ∀ c : Fin (μ.rowLen 0), 0 < μ.colLen c`. Introduce `c`. Rewrite using `[← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]`.

Conclude with `c.2`. Take `⟨e, he⟩` from `exists_equiv_of_counts sz (fun c : Fin (μ.rowLen 0) => μ.colLen c) hpos count`. Establish `hk : ∀ c, sz (e.symm c).1 = μ.colLen c`. Introduce `c`. Use `he (e.symm c)` as an intermediate fact.

Simplify using `using this.symm`. Use `⟨fun c => OrderEmbedding.ofStrictMono (fun i => I (e.symm c).1 (Fin.cast (hk c).symm i)) (fun i j hij => hI _ (by simpa using hij)), fun Y => ?_⟩` and prove the remaining obligations. Establish `hone : ∀ k, ¬ 0 < sz k → Matrix.det (Matrix.of fun p q : Fin (sz k) => Y (I k p) (Fin.castLE (hsz k) q)) = 1`. Introduce `k hk0`. Establish `h0 : sz k = 0` using `by omega`.

Use `haveI : IsEmpty (Fin (sz k)) := by rw [h0]; infer_instance`. Conclude with `Matrix.det_isEmpty`. Establish `hev : MvPolynomial.eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I) = ∏ k, Matrix.det (Matrix.of fun p q : Fin (sz k) => Y (I k p) (Fin.castLE (hsz k) q))`. Simplify using `only [Formalism.GradedWeylDivisibility.bideterminant, Formalism.GradedWeylDivisibility.initMinor, map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules. Use `show MvPolynomial.eval _ _ = _`.

Rewrite using `[hev, ← Finset.prod_filter_of_ne (p := fun k => 0 < sz k) (fun k _ hne => by by_contra hc; exact hne (hone k hc)), Finset.prod_subtype _ (p := fun k => 0 < sz k) (by simp)]`. Use `(Fintype.prod_equiv e.symm _ _ fun c => ?_).symm` and prove the remaining obligations. Conclude with `(minor_cast Y (hk c) (hsz _) (I (e.symm c).1)).symm`.
-/
theorem bidFns_eq_minors {K : Type} [CommRing K] {N : ℕ} (μ : YoungDiagram) (ν : Fin N → ℕ)
    (h1 : ∀ r : Fin N, μ.rowLen r = ν r) (h2 : ∀ r, N ≤ r → μ.rowLen r = 0)
    (g : Matrix (Fin N) (Fin N) K → K) (hg : g ∈ bideterminantFunctionsOfShape K N ν) :
    ∃ J : ∀ c : Fin (μ.rowLen 0), Fin (μ.colLen c) ↪o Fin N, ∀ Y : Matrix (Fin N) (Fin N) K,
      g Y = ∏ c : Fin (μ.rowLen 0), Matrix.det (Matrix.of fun i j : Fin (μ.colLen c) =>
        GL3Columns.colsOf Y (J c i) (j : ℕ)) := by
  classical
  obtain ⟨Kc, sz, hsz, I, hshape, hI, rfl⟩ := hg
  have count : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < N
    · have := congrFun hshape ⟨t, ht⟩
      rw [h1 ⟨t, ht⟩, ← this]
      simp only [Formalism.GradedWeylDivisibility.shapeDeg]
    · rw [h2 t (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hpos : ∀ c : Fin (μ.rowLen 0), 0 < μ.colLen c := by
    intro c
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    exact c.2
  obtain ⟨e, he⟩ := exists_equiv_of_counts sz (fun c : Fin (μ.rowLen 0) => μ.colLen c) hpos count
  have hk : ∀ c, sz (e.symm c).1 = μ.colLen c := by
    intro c
    have := he (e.symm c)
    simpa using this.symm
  refine ⟨fun c => OrderEmbedding.ofStrictMono (fun i => I (e.symm c).1 (Fin.cast (hk c).symm i))
    (fun i j hij => hI _ (by simpa using hij)), fun Y => ?_⟩
  have hone : ∀ k, ¬ 0 < sz k → Matrix.det (Matrix.of fun p q : Fin (sz k) =>
      Y (I k p) (Fin.castLE (hsz k) q)) = 1 := by
    intro k hk0
    have h0 : sz k = 0 := by omega
    haveI : IsEmpty (Fin (sz k)) := by rw [h0]; infer_instance
    exact Matrix.det_isEmpty
  have hev : MvPolynomial.eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I) =
      ∏ k, Matrix.det (Matrix.of fun p q : Fin (sz k) => Y (I k p) (Fin.castLE (hsz k) q)) := by
    simp only [Formalism.GradedWeylDivisibility.bideterminant, Formalism.GradedWeylDivisibility.initMinor, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp
  show MvPolynomial.eval _ _ = _
  rw [hev, ← Finset.prod_filter_of_ne (p := fun k => 0 < sz k)
    (fun k _ hne => by by_contra hc; exact hne (hone k hc)), Finset.prod_subtype _ (p := fun k => 0 < sz k) (by simp)]
  refine (Fintype.prod_equiv e.symm _ _ fun c => ?_).symm
  exact (minor_cast Y (hk c) (hsz _) (I (e.symm c).1)).symm

/- English proof (translation)
Introduce `D K _ N nu ν hfit g hg`. Establish `hJ` using `fun z => bidFns_eq_minors (nu z) (ν (tauPl D z)) (hfit.1 z) (hfit.2 z) (g (tauPl D z)) (hg _)`. Use `choose J hJ using hJ`. Use `⟨J, fun y => ?_⟩` and prove the remaining obligations. Use `((tauPl_bij D).prod_comp (fun τ => g τ (y τ))).symm.trans ?_` and prove the remaining obligations.

Conclude with `Finset.prod_congr rfl fun z _ => hJ z (y (tauPl D z))`.
-/
theorem prod_bidFns_eq_minY : ∀ (D : D7) (K : Type) [CommRing K] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν → ∀ g : D.what₂.Tau → Matrix (Fin N) (Fin N) K → K,
    (∀ τ, g τ ∈ bideterminantFunctionsOfShape K N (ν τ)) → ∃ J : KM.ColChoice N nu, ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) K,
      ∏ τ, g τ (y τ) = GL3Columns.minY N nu J (fun s => GL3Columns.colsOf (y (tauPl D s))) := by
  classical
  intro D K _ N nu ν hfit g hg
  have hJ := fun z => bidFns_eq_minors (nu z) (ν (tauPl D z)) (hfit.1 z) (hfit.2 z) (g (tauPl D z)) (hg _)
  choose J hJ using hJ
  refine ⟨J, fun y => ?_⟩
  refine ((tauPl_bij D).prod_comp (fun τ => g τ (y τ))).symm.trans ?_
  exact Finset.prod_congr rfl fun z _ => hJ z (y (tauPl D z))

end GlobalTheory.Mem.CanonicalSurjection
