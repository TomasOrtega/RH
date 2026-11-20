import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphImage

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Simplify using `only [dualLatticeCoord, hab p.2, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum, map_sum, mul_assoc]`.
-/
theorem coord_stacked {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (p : Σ _ : Unit, T) :
    dualLatticeCoord b p = (a p.2 : ProjField K i) * dualLatticeCoord b' p := by
  simp only [dualLatticeCoord, hab p.2, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum,
    map_sum, mul_assoc]

def twist (Ω : Type) [Field Ω] : MvPolynomial Unit Ω →+* MvPolynomial Unit (MvPolynomial Unit Ω) :=
  eval₂Hom (C.comp C) fun u => C (X u) * X u

/- English proof (translation)
Establish `h : (MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω))).comp (twist Ω) = RingHom.id _`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun u => ?_)` and prove the remaining obligations. Simplify using `[twist]`. Simplify using `[twist]`. Conclude with `Function.LeftInverse.injective (g := MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω))) fun x => RingHom.congr_fun h x`.
-/
theorem twist_injective (Ω : Type) [Field Ω] : Function.Injective (twist Ω) := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω))).comp (twist Ω) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun u => ?_)
    · simp [twist]
    · simp [twist]
  exact Function.LeftInverse.injective (g := MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω)))
    fun x => RingHom.congr_fun h x

/- English proof (translation)
Set `ψ : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)` to `mConeMap (dualLatticeCoord b')`. Set `ι : (MRing (dualBlocks T) ⧸ dualIdeal b') →+* MvPolynomial Unit (ProjField K i)` to `Ideal.Quotient.lift (dualIdeal b') ψ fun x hx => RingHom.mem_ker.mp hx`. Establish `hι : Function.Injective ι`. Use `(injective_iff_map_eq_zero ι).mpr fun x hx => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Rewrite `hx` using `[Ideal.Quotient.lift_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr hx)`. Establish `hcomp : (MvPolynomial.map ι).comp ((graphMap (dualIdeal b') (linForm (stackedDiag a))).comp (rename (inrV (ι` using `dualBlocks T) (ι₂ := dualBlocks T)) : MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom) = (twist (ProjField K i)).comp (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* _) := by`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Take `⟨u, t⟩` from `p`. Consider the cases of `u`. Simplify using `[graphMap, inrV, twist, mConeMap, TopDualSimpleStacked.linForm_stackedDiag, ι, ψ, coord_stacked hab]`. Rewrite using `[show eval₂ (C.comp C) (fun u => C (X u) * X u) ((a t : ℤ) : MvPolynomial Unit (ProjField K i)) = ((a t : ℤ) : MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) from map_intCast (twist _) _]`. Expand and normalize the polynomial expressions, which then agree.

Use extensionality with `f`. Establish `e` using `RingHom.congr_fun hcomp f`. Simplify using `only [RingHom.comp_apply] at e`. Establish `e1` using `map_eq_zero_iff _ (MvPolynomial.map_injective ι hι) (x := graphMap (dualIdeal b') (linForm (stackedDiag a)) ((rename (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) : MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom f))`. Establish `e2` using `map_eq_zero_iff _ (twist_injective (ProjField K i)) (x := (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) f)`.

Rewrite `e1` using `[e]`. Rewrite using `[imageZ, Ideal.mem_comap, stackedGraph, graphIdeal, RingHom.mem_ker, ← e1, e2]`. Conclude with `RingHom.mem_ker.symm`.
-/
theorem image_eq {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) :
    imageZ inrV (stackedGraph b' a) = dualIdeal b := by
  let ψ : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i) := mConeMap (dualLatticeCoord b')
  let ι : (MRing (dualBlocks T) ⧸ dualIdeal b') →+* MvPolynomial Unit (ProjField K i) :=
    Ideal.Quotient.lift (dualIdeal b') ψ fun x hx => RingHom.mem_ker.mp hx
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr hx)
  have hcomp : (MvPolynomial.map ι).comp ((graphMap (dualIdeal b') (linForm (stackedDiag a))).comp
      (rename (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) :
        MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom) =
      (twist (ProjField K i)).comp (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* _) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp
    · obtain ⟨u, t⟩ := p
      cases u
      simp [graphMap, inrV, twist, mConeMap, TopDualSimpleStacked.linForm_stackedDiag, ι, ψ,
        coord_stacked hab]
      rw [show eval₂ (C.comp C) (fun u => C (X u) * X u) ((a t : ℤ) : MvPolynomial Unit (ProjField K i)) =
        ((a t : ℤ) : MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) from map_intCast (twist _) _]
      ring
  ext f
  have e := RingHom.congr_fun hcomp f
  simp only [RingHom.comp_apply] at e
  have e1 := map_eq_zero_iff _ (MvPolynomial.map_injective ι hι)
    (x := graphMap (dualIdeal b') (linForm (stackedDiag a))
      ((rename (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) :
        MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom f))
  have e2 := map_eq_zero_iff _ (twist_injective (ProjField K i))
    (x := (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) f)
  rw [e] at e1
  rw [imageZ, Ideal.mem_comap, stackedGraph, graphIdeal, RingHom.mem_ker, ← e1, e2]
  exact RingHom.mem_ker.symm

/- English proof (translation)
Establish `hP' : IsArithVar (dualIdeal b') i` using `DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F' T b' hi`. Establish `hP : IsArithVar (dualIdeal b) i` using `DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F T b hi`. Establish `hprime : (dualIdeal b').IsPrime` using `hP'.2.1.1`. Establish `ha : ∀ t, a t ≠ 0`. Introduce `t h0`.

Apply `b.ne_zero t` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hab t, h0, zero_smul]`. Both sides reduce to the same expression. Take `⟨t₀, ht₀⟩` from `hP'.2.1.2.2 ()`.

Establish `hlin : (C (a t₀) * X ⟨(), t₀⟩ : MRing (dualBlocks T)) ∉ dualIdeal b'` using `TopDualSimpleStacked.C_mul_X_not_mem hprime hP'.2.2.1 (ha t₀) ht₀`. Establish `hform : ∀ q : Σ _ : Unit, T, IsMultiHomog (linForm (stackedDiag a) q) ((fun _ _ => 1 : Unit → Unit → ℕ) q.1)`. Introduce and unpack `⟨u, t⟩`. Consider the cases of `u`. Rewrite using `[TopDualSimpleStacked.linForm_stackedDiag]`.

Establish `h` using `TopDualSimpleStacked.isMultiHomog_C_mul (TopDualSimpleStacked.isMultiHomog_X_int (ι := dualBlocks T) () t) (a t)`. Establish `he : (Pi.single () 1 : Unit → ℕ) = fun _ => 1`. Use function extensionality and compare the values at `u`. Consider the cases of `u`. Simplify using the standard rewrite rules.

Rewrite `h` using `[he]`. Then use the resulting hypothesis. Establish `hΓ : IsArithVar (stackedGraph b' a) i` using `(hGr Unit (dualBlocks T) Unit (dualBlocks T) (dualIdeal b') i (linForm (stackedDiag a)) (fun _ _ => 1) hP' hform (fun _ => ⟨t₀, by rw [TopDualSimpleStacked.linForm_stackedDiag]; exact hlin⟩)).1`. Establish `hIm : IsArithVar (imageZ inrV (stackedGraph b' a)) i`. Rewrite using `[image_eq hab]`. Conclude with `hP`.

Establish `hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0` using `hDim Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inr inrV _ i 0 G isBlockMap_inr hΓ hIm`. Establish `hmem : ∀ f, f ∈ stackedGraph b' a ↔ aeval G.x' f = 0` using `fun f => by`. Rewrite using `[← RingHom.mem_ker, G.genericFibre_ker_target]`. Establish `hx0 : G.x' ⟨Sum.inl (), t₀⟩ ≠ 0`. Introduce `h`.

Establish `hm : (X ⟨Sum.inl (), t₀⟩ : MRing (stackedBlocks T)) ∈ stackedGraph b' a` using `(hmem _).2 (by rw [aeval_X]; exact h)`. Rewrite `hm` using `[stackedGraph, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X']`. Conclude with `ht₀ (Ideal.Quotient.eq_zero_iff_mem.1 (C_eq_zero.1 hm))`. Establish `hy0 : G.x' ⟨Sum.inr (), t₀⟩ ≠ 0`. Introduce `h`.

Conclude with `TopDualSimpleStacked.second_not_mem hprime a hlin ((hmem _).2 (by rw [graphSecond, aeval_X]; exact h))`. Establish `haΦ : ∀ t, (a t : G.Φ) ≠ 0`. Introduce `t h`. Establish `hm : (C (a t) : MRing (dualBlocks T)) ∈ dualIdeal b`. Rewrite using `[← image_eq hab, ← G.ker_x, RingHom.mem_ker, aeval_C]`.

Simplify using `using h`. Establish `h2 : a t ∈ (dualIdeal b).comap (C : ℤ →+* MRing (dualBlocks T))` using `hm`. Rewrite `h2` using `[hP.2.2.1]`. Conclude with `ha t (Ideal.mem_bot.mp h2)`. Establish `hrat : ∀ t, G.x' ⟨Sum.inl (), t⟩ / G.x' ⟨Sum.inl (), t₀⟩ = algebraMap G.Φ G.Φ' ((a t₀ : G.Φ) * G.x ⟨(), t⟩ / ((a t : G.Φ) * G.x ⟨(), t₀⟩))`.

Introduce `t`. Establish `hm` using `(hmem _).1 (TopDualSimpleStacked.minor_mem (dualIdeal b') a t₀ t)`. Simplify using `only [graphFirst, graphSecond, map_sub, map_mul, aeval_X, eq_intCast, map_intCast] at hm`. Establish `c1 : G.x' ⟨Sum.inr (), t⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t⟩)` using `G.compat ⟨(), t⟩`. Establish `c0 : G.x' ⟨Sum.inr (), t₀⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t₀⟩)` using `G.compat ⟨(), t₀⟩`.

Establish `hat : (a t : G.Φ') ≠ 0`. Rewrite using `[← map_intCast (algebraMap G.Φ G.Φ')]`. Conclude with `(map_ne_zero _).2 (haΦ t)`. Rewrite using `[map_div₀, map_mul, map_mul, map_intCast, map_intCast, ← c1, ← c0, div_eq_div_iff hx0 (mul_ne_zero hat hy0)]`. Take the linear combination `hm`.

Set `ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (stackedBlocks T) Sum.inr k` to `fun`. Consider the case `⟨Sum.inl _, _⟩ => t₀`. Consider the case `⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h`. Establish `hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0`. Introduce and unpack `⟨(u | u), h⟩`.

Consider the cases of `u`. Conclude with `hx0`. Conclude with `absurd ⟨u, rfl⟩ h`. Establish `hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch`. Introduce `k`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]`. Conclude with `hz k`. Rewrite using `[hJ.1 _ _ _ hpt hch]`. Establish `hdeg` using `Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) (fibreIdx (stackedBlocks T) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1`. Establish `hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (stackedBlocks T) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥`.

Rewrite using `[eq_bot_iff, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨⟨(u | u), h⟩, t⟩, rfl⟩`. Consider the cases of `u`. Conclude with `IntermediateField.mem_bot.2 ⟨_, (hrat t).symm⟩`. Conclude with `absurd ⟨u, rfl⟩ h`.

Express the relevant statement in the definitionally equal form `((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]`.
-/
theorem fibre_deg (hGr : GraphStatement) (hDim : FibreDimStatement) {F F' : HermLattice K i}
    {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hi : 1 ≤ i) (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K))
    (G : GenFibre inrV (stackedGraph b' a))
    (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit)))
    (hJ : IsFieldIntersection J) :
    J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1 := by
  have hP' : IsArithVar (dualIdeal b') i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F' T b' hi
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F T b hi
  have hprime : (dualIdeal b').IsPrime := hP'.2.1.1
  have ha : ∀ t, a t ≠ 0 := by
    intro t h0
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h0, zero_smul]
    rfl
  obtain ⟨t₀, ht₀⟩ := hP'.2.1.2.2 ()
  have hlin : (C (a t₀) * X ⟨(), t₀⟩ : MRing (dualBlocks T)) ∉ dualIdeal b' :=
    TopDualSimpleStacked.C_mul_X_not_mem hprime hP'.2.2.1 (ha t₀) ht₀
  have hform : ∀ q : Σ _ : Unit, T,
      IsMultiHomog (linForm (stackedDiag a) q) ((fun _ _ => 1 : Unit → Unit → ℕ) q.1) := by
    rintro ⟨u, t⟩
    cases u
    rw [TopDualSimpleStacked.linForm_stackedDiag]
    have h := TopDualSimpleStacked.isMultiHomog_C_mul
      (TopDualSimpleStacked.isMultiHomog_X_int (ι := dualBlocks T) () t) (a t)
    have he : (Pi.single () 1 : Unit → ℕ) = fun _ => 1 := by
      funext u
      cases u
      simp
    rwa [he] at h
  have hΓ : IsArithVar (stackedGraph b' a) i :=
    (hGr Unit (dualBlocks T) Unit (dualBlocks T) (dualIdeal b') i (linForm (stackedDiag a)) (fun _ _ => 1) hP'
      hform (fun _ => ⟨t₀, by rw [TopDualSimpleStacked.linForm_stackedDiag]; exact hlin⟩)).1
  have hIm : IsArithVar (imageZ inrV (stackedGraph b' a)) i := by
    rw [image_eq hab]
    exact hP
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inr inrV _ i 0 G isBlockMap_inr hΓ hIm
  have hmem : ∀ f, f ∈ stackedGraph b' a ↔ aeval G.x' f = 0 := fun f => by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]

  have hx0 : G.x' ⟨Sum.inl (), t₀⟩ ≠ 0 := by
    intro h
    have hm : (X ⟨Sum.inl (), t₀⟩ : MRing (stackedBlocks T)) ∈ stackedGraph b' a :=
      (hmem _).2 (by rw [aeval_X]; exact h)
    rw [stackedGraph, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at hm
    exact ht₀ (Ideal.Quotient.eq_zero_iff_mem.1 (C_eq_zero.1 hm))
  have hy0 : G.x' ⟨Sum.inr (), t₀⟩ ≠ 0 := by
    intro h
    exact TopDualSimpleStacked.second_not_mem hprime a hlin
      ((hmem _).2 (by rw [graphSecond, aeval_X]; exact h))

  have haΦ : ∀ t, (a t : G.Φ) ≠ 0 := by
    intro t h
    have hm : (C (a t) : MRing (dualBlocks T)) ∈ dualIdeal b := by
      rw [← image_eq hab, ← G.ker_x, RingHom.mem_ker, aeval_C]
      simpa using h
    have h2 : a t ∈ (dualIdeal b).comap (C : ℤ →+* MRing (dualBlocks T)) := hm
    rw [hP.2.2.1] at h2
    exact ha t (Ideal.mem_bot.mp h2)

  have hrat : ∀ t, G.x' ⟨Sum.inl (), t⟩ / G.x' ⟨Sum.inl (), t₀⟩ =
      algebraMap G.Φ G.Φ' ((a t₀ : G.Φ) * G.x ⟨(), t⟩ / ((a t : G.Φ) * G.x ⟨(), t₀⟩)) := by
    intro t
    have hm := (hmem _).1 (TopDualSimpleStacked.minor_mem (dualIdeal b') a t₀ t)
    simp only [graphFirst, graphSecond, map_sub, map_mul, aeval_X, eq_intCast, map_intCast] at hm
    have c1 : G.x' ⟨Sum.inr (), t⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t⟩) := G.compat ⟨(), t⟩
    have c0 : G.x' ⟨Sum.inr (), t₀⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t₀⟩) := G.compat ⟨(), t₀⟩
    have hat : (a t : G.Φ') ≠ 0 := by
      rw [← map_intCast (algebraMap G.Φ G.Φ')]
      exact (map_ne_zero _).2 (haΦ t)
    rw [map_div₀, map_mul, map_mul, map_intCast, map_intCast, ← c1, ← c0,
      div_eq_div_iff hx0 (mul_ne_zero hat hy0)]
    linear_combination hm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (stackedBlocks T) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => t₀
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact hx0
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (stackedBlocks T) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (stackedBlocks T) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, t⟩, rfl⟩
    · cases u
      exact IntermediateField.mem_bot.2 ⟨_, (hrat t).symm⟩
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end StackedGraphImage

open StackedGraphImage in

/- English proof (translation)
Introduce `K _ _ i F F' T _ _ b b' a hi hab`. Conclude with `⟨image_eq hab, fun G J hJ => fibre_deg hGr hDim hi hab G J hJ⟩`.
-/
theorem DualStackedGraphImage.proof (hGr : GraphStatement) (hDim : FibreDimStatement) :
    DualStackedGraphImage.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hab
  exact ⟨image_eq hab, fun G J hJ => fibre_deg hGr hDim hi hab G J hJ⟩

end

end GroundTheory.Heights₂.Heights
