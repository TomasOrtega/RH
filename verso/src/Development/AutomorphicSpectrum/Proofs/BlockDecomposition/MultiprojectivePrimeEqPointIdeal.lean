import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Onto

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [Geo.mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p q hp`. Rewrite using `[map_mul, map_mul, map_mul, hp]`. Simplify using `[Geo.mConeMap]`. Use extensionality with `f`. Simplify using `only [Geo.mCoordIdeal, RingHom.mem_ker, key]`.

Conclude with `map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)`.
-/
theorem mCoordIdeal_comp_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    Geo.mCoordIdeal (fun p => j (w p)) = Geo.mCoordIdeal w := by
  have key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Geo.mConeMap]
  ext f
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

/- English proof (translation)
Set `φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (c k) * X k`. Set `φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (c k)⁻¹ * X k`. Establish `hinv : φ'.comp φ = AlgHom.id Ω _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `k`.

Simplify using `only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]`. Establish `hinj : Function.Injective φ` using `fun a b h => by`. Use `congrArg φ' h` as an intermediate fact. Rewrite `this` using `[← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv]`. Then use the resulting hypothesis.

Establish `hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g)`. Introduce `g`. Establish `: Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`.

Simplify using `only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C, algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Both sides reduce to the same expression. Use extensionality with `g`.

Simplify using `only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]`.
-/
theorem mCoordIdeal_blockScale {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → Ω) :
    Geo.mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = Geo.mCoordIdeal z := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k) * X k
  let φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k)⁻¹ * X k
  have hinv : φ'.comp φ = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg φ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at this
  have hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g) := by
    intro g
    have : Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C,
        algebraMap_eq]
      ring
    rw [this]; rfl
  ext g
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]

/- English proof (translation)
Establish `hev : ∀ f, aeval (fun p => φ (X p)) f = φ f`. Introduce `f`. Establish `: ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ` using `MvPolynomial.ringHom_ext (fun r => RingHom.congr_fun (Subsingleton.elim (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r) (fun p => by simp)`. Conclude with `congrArg (fun ψ => ψ f) this`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `f hf`. Rewrite `hf` using `[Geo.mCoordIdeal, RingHom.mem_ker]`. Establish `e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`.

Simplify using `[Geo.mConeMap]`. Use `congrArg (fun ψ => ψ f) e` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, hf, map_zero, hev] at this`. Rewrite using `[← hφ, RingHom.mem_ker]`. Conclude with `this.symm`.

Establish `hP'` using `hP`. Take `⟨S, hS, hPS⟩` from `hP'`. Rewrite using `[hPS, Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`.

Establish `h0 : φ f = 0`. Rewrite using `[← RingHom.mem_ker, hφ, hPS]`. Conclude with `Ideal.subset_span hf`. Rewrite using `[SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]`.
-/
theorem mCoordIdeal_of_ker {Ω : Type} [Field Ω] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (φ : Geo.MRing ι →+* Ω) (hφ : RingHom.ker φ = P) : Geo.mCoordIdeal (fun p => φ (X p)) = P := by
  have hev : ∀ f, aeval (fun p => φ (X p)) f = φ f := by
    intro f
    have : ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ :=
      MvPolynomial.ringHom_ext
        (fun r => RingHom.congr_fun (Subsingleton.elim
          (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r)
        (fun p => by simp)
    exact congrArg (fun ψ => ψ f) this
  apply le_antisymm
  · intro f hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf
    have e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp
        (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [Geo.mConeMap]
    have := congrArg (fun ψ => ψ f) e
    simp only [AlgHom.comp_apply, hf, map_zero, hev] at this
    rw [← hφ, RingHom.mem_ker]
    exact this.symm
  · have hP' := hP
    obtain ⟨S, hS, hPS⟩ := hP'
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h0 : φ f = 0 := by
      rw [← RingHom.mem_ker, hφ, hPS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]

end Coord

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Use `show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Both sides reduce to the same expression.
-/
theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/- English proof (translation)
Establish `hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤` using `fun k => by`. Take `⟨i, hi⟩` from `hv k`. Conclude with `Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)`. Set `a : ∀ k, Sp F ⟶ PSpace ℤ (n k)` to `fun k => GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)`. Establish `ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F)` using `fun k => GlobalTheory.ProjSpace.pt_str _ _ _`.

Set `g : Sp F ⟶ MP ℤ m n` to `ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha`. Establish `hg : ∀ k, g ≫ prB n k = a k` using `fun k => ProjSpace.lift_pr m n _ a ha k`. Set `p : Sp F` to `IsLocalRing.closedPoint F`. Set `x : MP ℤ m n` to `g p`. Set `θ : F →+* (Sp F).residueField p` to `((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom`.

Set `ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p` to `(g.residueFieldMap p).hom`. Establish `key : ∀ (k : Fin (m + 1)) (j : Bk n k), θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩)`. Introduce `k j`. Establish `hx : g p ∈ blockChart n k (ptChart x k)` using `mem_ptChart x k`. Establish `hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k)`.

Rewrite using `[← hg k]`. Conclude with `le_of_eq rfl`. Establish `e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j)`. Use `(Scheme.evaluation_naturality_apply g p hx _).trans ?_` and prove the remaining obligations. Use `congrArg _ ?_` and prove the remaining obligations.

Use `appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl` as an intermediate fact. Conclude with `this.trans (pullRatio_of_eq (hg k) _ _)`. Establish `e2` using `pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k) (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW`. Establish `e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b` using `fun b => evaluation_resG' le_top p hx _`. Use `congrArg ((Sp F).evaluation _ p hx).hom e2` as an intermediate fact.

Rewrite `this` using `[map_mul, e3, e3]`. Rewrite using `[e1, mul_comm]`. Conclude with `this`. Establish `hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0`. Introduce `k`.

Use `(map_ne_zero θ).2 fun h0 => ?_` and prove the remaining obligations. Establish `hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k)`. Establish `: g p ∈ blockChart n k (ptChart x k)` using `mem_ptChart x k`. Rewrite using `[← hg k]`. Conclude with `this`.

Rewrite `hx` using `[GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen]`. Conclude with `hx (h0 ▸ Ideal.zero_mem _)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v, ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Take `⟨k, j⟩` from `q`. Conclude with `key k j`.
-/
theorem exists_ptIdeal_eq_mCoordIdeal {F : Type} [Field F] (v : (Σ k, Bk n k) → F)
    (hv : ∀ k, ∃ i, v ⟨k, i⟩ ≠ 0) : ∃ x : MP ℤ m n, ptIdeal x = Geo.mCoordIdeal v := by
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hv k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp F ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
  have ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F) := fun k =>
    GlobalTheory.ProjSpace.pt_str _ _ _
  let g : Sp F ⟶ MP ℤ m n := ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha
  have hg : ∀ k, g ≫ prB n k = a k := fun k => ProjSpace.lift_pr m n _ a ha k
  let p : Sp F := IsLocalRing.closedPoint F
  let x : MP ℤ m n := g p
  let θ : F →+* (Sp F).residueField p :=
    ((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp F).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  refine ⟨x, ?_⟩
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v,
    ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

/- English proof (translation)
Take `⟨hp, hh, hr⟩` from `hP`. Set `φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P)` to `(algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)`. Establish `hφ : RingHom.ker φ = P`. Use extensionality with `f`. Rewrite using `[RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P))) (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))`. Establish `hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hr k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, RingHom.mem_ker]`.

Conclude with `h0`. Take `⟨x, hx⟩` from `exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv`. Conclude with `⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩`.
-/
theorem exists_ptIdeal_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Geo.MRing (Bk n)))
    (hP : Geo.IsMultiProjPrime P) : ∃ x : MP ℤ m n, ptIdeal x = P := by
  obtain ⟨hp, hh, hr⟩ := hP
  let φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P) :=
    (algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)
  have hφ : RingHom.ker φ = P := by
    ext f
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
      (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
  have hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hφ, RingHom.mem_ker]
    exact h0
  obtain ⟨x, hx⟩ := exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv
  exact ⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩

end GlobalTheory.CompanionTheory.MPDict.Onto
