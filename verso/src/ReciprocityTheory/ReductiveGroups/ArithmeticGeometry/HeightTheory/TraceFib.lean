import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsB

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Use `letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra`. Use `letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra`. Take `⟨hfd, hrk⟩` from `d.omS_finite hd h c`. Establish `: CharZero (KTf K d.D d.N)` using `charZero_of_injective_algebraMap (R := K) (algebraMap K (KTf K d.D d.N)).injective`. Establish `hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0` using `fun i h0 => by`.

Use `hpt (X (i.succ, 0)) (X_ne_zero _)` as an intermediate fact. Rewrite `this` using `[eval₂_X, NPB.gpt_succ, h0, zero_mul]`. Conclude with `this rfl`. Take `⟨hinj, hrange⟩` from `d.fibre_core hd h c sg _ hpt`. Rewrite `hrange` using `[d.ST_scale c sg t y hy]`.

Rewrite using `[← hrange, finsum_mem_range hinj, finsum_eq_sum_of_fintype]`. Conclude with `trace_eq_sum_embeddings ℂ`.
-/
theorem trace_fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) (g : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    tauPev sg _ hpt (Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)) =
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrk⟩ := d.omS_finite hd h c
  have : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (R := K) (algebraMap K (KTf K d.D d.N)).injective
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := fun i h0 => by
    have := hpt (X (i.succ, 0)) (X_ne_zero _)
    rw [eval₂_X, NPB.gpt_succ, h0, zero_mul] at this
    exact this rfl
  obtain ⟨hinj, hrange⟩ := d.fibre_core hd h c sg _ hpt
  rw [d.ST_scale c sg t y hy] at hrange
  rw [← hrange, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  exact trace_eq_sum_embeddings ℂ

/- English proof (translation)
Use `haveI : Countable K := countable_numberField K`. Use `filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz hb`. Use `(div_eq_iff hb).2 ?_` and prove the remaining obligations. Establish `hG : ∀ (m : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K), ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m p → p ≠ 0 → eval₂ sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) p ≠ 0` using `fun m p h1 h2 => hz m p h1 h2`. Establish `h0 : ∀ q : MvPolynomial (TVar d.D d.N) K, eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) q = d.evT sg 0 (d.tOf z) q`.

Introduce `q`. Unfold `Data.evT`. Use `congr 1`. Use function extensionality and compare the values at `v`. Take `⟨i, j⟩` from `v`.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [NPB.gpt]`. Consider the case `succ i => simp [NPB.gpt]`. It suffices to establish `H : ∀ Dv : ℂ, (∀ y : Fin (d.N + 1 + d.D) → ℂ, (∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) q ≠ 0) → eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) a = Dv * eval₂ sg (NPB.gpt (fun …`. Use `H _ fun y hpt => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg (tauPev sg _ hpt) hab.2.1`. Rewrite `h1` using `[map_mul, tauPev_apply, tauPev_apply]`. Rewrite using `[h1]`. Use `congr 1`. Rewrite using `[Data.De, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `k l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `ht` using `d.trace_fib hd h c sg (d.tOf z) y hpt (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) * ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))`.

Simplify using `only [map_mul] at ht`. Simplify `ht` using `only [Data.bvecG]`. Introduce `Dv hDv`. Establish `hR : NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) a - MvPolynomial.C Dv * NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) b = 0`. Assume the negation of the conclusion as `hR`.

Take `⟨y, hy, hgen⟩` from `NPB.exists_gen sg _ hG _ hR`. Apply `hy` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, hDv y hgen, sub_self]`. Establish `e0` using `congrArg (MvPolynomial.eval (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) hR`. Rewrite `e0` using `[map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, h0, h0, map_zero]`.

Conclude with `sub_eq_zero.mp e0`.
-/
theorem de_fibre (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      d.evT sg 0 (d.tOf z) b ≠ 0 →
      d.evT sg 0 (d.tOf z) a / d.evT sg 0 (d.tOf z) b =
        (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))).det := by
  haveI : Countable K := countable_numberField K
  filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz hb
  refine (div_eq_iff hb).2 ?_
  have hG : ∀ (m : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m p → p ≠ 0 →
      eval₂ sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) p ≠ 0 :=
    fun m p h1 h2 => hz m p h1 h2
  have h0 : ∀ q : MvPolynomial (TVar d.D d.N) K,
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2)
        (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) q =
        d.evT sg 0 (d.tOf z) q := by
    intro q
    unfold Data.evT
    congr 1
    funext v
    obtain ⟨i, j⟩ := v
    induction i using Fin.cases with
    | zero => simp [NPB.gpt]
    | succ i => simp [NPB.gpt]
  suffices H : ∀ Dv : ℂ, (∀ y : Fin (d.N + 1 + d.D) → ℂ,
      (∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
        eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) q ≠ 0) →
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) a =
        Dv * eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) b) →
      d.evT sg 0 (d.tOf z) a = Dv * d.evT sg 0 (d.tOf z) b by
    refine H _ fun y hpt => ?_
    have h1 := congrArg (tauPev sg _ hpt) hab.2.1
    rw [map_mul, tauPev_apply, tauPev_apply] at h1
    rw [h1]
    congr 1
    rw [Data.De, RingHom.map_det]
    congr 1
    ext k l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have ht := d.trace_fib hd h c sg (d.tOf z) y hpt
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) *
        ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))
    simp only [map_mul] at ht
    simpa only [Data.bvecG] using ht
  intro Dv hDv
  have hR : NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) a -
      MvPolynomial.C Dv * NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) b = 0 := by
    by_contra hR
    obtain ⟨y, hy, hgen⟩ := NPB.exists_gen sg _ hG _ hR
    apply hy
    rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, hDv y hgen, sub_self]
  have e0 := congrArg
    (MvPolynomial.eval (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) hR
  rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, h0, h0, map_zero] at e0
  exact sub_eq_zero.mp e0

end Data

end ReciprocityTheory.ChartRestriction.G.T0
