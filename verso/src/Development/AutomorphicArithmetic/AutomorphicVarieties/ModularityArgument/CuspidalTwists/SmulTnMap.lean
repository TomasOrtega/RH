import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.IrrKey
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IrrAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd
open scoped Matrix

namespace UpperTheory.V.Cu.IrreducibilityFourDim

/- English proof (translation)
The claim follows from `UpperTheory.V.Cu.IrrKey.key h2 On A B hon hkp hkm hirr t hoff hBt hAt u hu hAu hne W hW`.
-/
theorem key {K : Type} [Field K] {ι : Type} (h2 : (2 : K) ≠ 0) (On : Set ι) (A B : ι → Matrix (Fin 2) (Fin 2) K)
    (hon : ∀ i ∈ On, B i 1 1 = B i 0 0 ∧ B i 1 0 = B i 0 1)
    (hkp : ∀ i ∈ On, B i 0 0 + B i 0 1 ≠ 0) (hkm : ∀ i ∈ On, B i 0 0 - B i 0 1 ≠ 0)
    (hirr : ∀ V : Submodule K (Fin 2 → K), (∀ i ∈ On, ∀ v ∈ V, A i *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤)
    (t : ι) (hoff : B t 1 1 = -B t 0 0 ∧ B t 1 0 = -B t 0 1) (hBt : (B t).det ≠ 0) (hAt : (A t).det ≠ 0)
    (u : ι) (hu : u ∈ On) (hAu : (A u).det ≠ 0)
    (hne : (B u 0 0 + B u 0 1) ^ 2 ≠ (B u 0 0 - B u 0 1) ^ 2)
    (W : Submodule K (Fin 4 → K)) (hW : ∀ i, (i ∈ On ∨ i = t) → ∀ v ∈ W, UpperTheory.V.Cu.tn (A i) (B i) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  UpperTheory.V.Cu.IrrKey.key h2 On A B hon hkp hkm hirr t hoff hBt hAt u hu hAu hne W hW

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Take `⟨h1, -, h3⟩` from `hr`. Use `⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩` and prove the remaining obligations. Establish `key` using `h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by`. Establish `h4` using `hi s _ hv`.

Rewrite `h4` using `[hg s]`. Simplify `h4)` using `[Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))` using `fun v => ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩`. Establish `e` using `Submodule.map_comap_eq_of_surjective hs W`.

Break down `key with key | key` into its components or cases. Use `left`. Rewrite using `[← e, key, Submodule.map_bot]`. Use `right`. Rewrite using `[← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]`.
-/
private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]

/- English proof (translation)
The claim follows from `IsUnit.of_mul_eq_one (ρ g⁻¹).det (by rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one])`.
-/
private theorem det_unit {Γ R : Type} [Group Γ] [CommRing R] (ρ : Γ →* Matrix (Fin 2) (Fin 2) R) (g : Γ) :
    IsUnit (ρ g).det :=
  IsUnit.of_mul_eq_one (ρ g⁻¹).det (by rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one])

/- English proof (translation)
Establish `e` using `congrFun (congrFun hf 0) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e`. Use `first`. Consider the case `linear_combination e + (X 1 0 + X 0 1) * h10`. Consider the case `linear_combination -e + (X 1 0 + X 0 1) * h10`.
-/
private theorem on_form {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R)
    (hf : Xᵀ * !![1, 0; 0, -1] * X = !![1, 0; 0, -1]) (h10 : X 1 0 = X 0 1) :
    (X 0 0 + X 0 1) * (X 0 0 - X 0 1) = 1 := by
  have e := congrFun (congrFun hf 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  first
    | linear_combination e + (X 1 0 + X 0 1) * h10
    | linear_combination -e + (X 1 0 + X 0 1) * h10

/- English proof (translation)
Establish `e00 : X 0 0 * Y 0 0 + X 0 1 * Y 1 0 = 1`. Use `congrFun (congrFun h 0) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]`. Then use the resulting hypothesis. Establish `e01 : X 0 0 * Y 0 1 + X 0 1 * Y 1 1 = 0`. Use `congrFun (congrFun h 0) 1` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Then use the resulting hypothesis. Rewrite `e00` using `[b2]`. Rewrite `e01` using `[a2]`. Conclude with `⟨by linear_combination e00 + e01, by linear_combination e00 - e01⟩`.
-/
private theorem on_inv {R : Type} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) (a1 : X 1 1 = X 0 0) (b1 : X 1 0 = X 0 1)
    (a2 : Y 1 1 = Y 0 0) (b2 : Y 1 0 = Y 0 1) (h : X * Y = 1) :
    (X 0 0 + X 0 1) * (Y 0 0 + Y 0 1) = 1 ∧ (X 0 0 - X 0 1) * (Y 0 0 - Y 0 1) = 1 := by
  have e00 : X 0 0 * Y 0 0 + X 0 1 * Y 1 0 = 1 := by
    have := congrFun (congrFun h 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
  have e01 : X 0 0 * Y 0 1 + X 0 1 * Y 1 1 = 0 := by
    have := congrFun (congrFun h 0) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at this
  rw [b2] at e00
  rw [a2] at e01
  exact ⟨by linear_combination e00 + e01, by linear_combination e00 - e01⟩

/- English proof (translation)
Establish `e00 : Y1 0 0 * Y2 0 0 + Y1 0 1 * Y2 1 0 = 1`. Use `congrFun (congrFun hY 0) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]`. Then use the resulting hypothesis. Establish `e01 : Y1 0 0 * Y2 0 1 + Y1 0 1 * Y2 1 1 = 0`. Use `congrFun (congrFun hY 0) 1` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Then use the resulting hypothesis. Rewrite `e00` using `[d2]`. Rewrite `e01` using `[c2]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, a1, b1, a2, b2, c1, d1, c2, d2]`. Use `⟨by ring, by ring, ?_, ?_⟩` and prove the remaining obligations.

Take the linear combination `(X1 0 0 + X1 0 1) * (X2 0 0 - X2 0 1) * e00 + (X1 0 0 + X1 0 1) * (X2 0 0 - X2 0 1) * e01`. Take the linear combination `(X1 0 0 - X1 0 1) * (X2 0 0 + X2 0 1) * e00 - (X1 0 0 - X1 0 1) * (X2 0 0 + X2 0 1) * e01`.
-/
private theorem shape4 {R : Type} [CommRing R] (X1 Y1 X2 Y2 : Matrix (Fin 2) (Fin 2) R)
    (a1 : X1 1 1 = X1 0 0) (b1 : X1 1 0 = X1 0 1) (a2 : X2 1 1 = X2 0 0) (b2 : X2 1 0 = X2 0 1)
    (c1 : Y1 1 1 = -Y1 0 0) (d1 : Y1 1 0 = -Y1 0 1) (c2 : Y2 1 1 = -Y2 0 0) (d2 : Y2 1 0 = -Y2 0 1)
    (hY : Y1 * Y2 = 1) :
    (X1 * Y1 * X2 * Y2) 1 1 = (X1 * Y1 * X2 * Y2) 0 0 ∧ (X1 * Y1 * X2 * Y2) 1 0 = (X1 * Y1 * X2 * Y2) 0 1 ∧
    (X1 * Y1 * X2 * Y2) 0 0 + (X1 * Y1 * X2 * Y2) 0 1 = (X1 0 0 + X1 0 1) * (X2 0 0 - X2 0 1) ∧
    (X1 * Y1 * X2 * Y2) 0 0 - (X1 * Y1 * X2 * Y2) 0 1 = (X1 0 0 - X1 0 1) * (X2 0 0 + X2 0 1) := by
  have e00 : Y1 0 0 * Y2 0 0 + Y1 0 1 * Y2 1 0 = 1 := by
    have := congrFun (congrFun hY 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
  have e01 : Y1 0 0 * Y2 0 1 + Y1 0 1 * Y2 1 1 = 0 := by
    have := congrFun (congrFun hY 0) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at this
  rw [d2] at e00
  rw [c2] at e01
  simp only [Matrix.mul_apply, Fin.sum_univ_two, a1, b1, a2, b2, c1, d1, c2, d2]
  refine ⟨by ring, by ring, ?_, ?_⟩
  · linear_combination (X1 0 0 + X1 0 1) * (X2 0 0 - X2 0 1) * e00 + (X1 0 0 + X1 0 1) * (X2 0 0 - X2 0 1) * e01
  · linear_combination (X1 0 0 - X1 0 1) * (X2 0 0 + X2 0 1) * e00 - (X1 0 0 - X1 0 1) * (X2 0 0 + X2 0 1) * e01

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Cu.tn]`.
-/
private theorem smul_tn_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (X Y : Matrix (Fin 2) (Fin 2) R) :
    (c • UpperTheory.V.Cu.tn X Y).map f = f c • UpperTheory.V.Cu.tn (X.map f) (Y.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Cu.tn]

/- English proof (translation)
Take `⟨g, hg⟩` from `hi`. Establish `h' : IsIrr (r.toHomUnits.comp φ)` using `isIrr_iso (r := ρ.comp φ) ⟨g, fun s => hg (φ s)⟩ h`. Conclude with `h'.2.2 V le_top hV`.
-/
private theorem irr_mat {Γ S k : Type} [Group Γ] [Group S] [Field k] (φ : S →* Γ) (ρ : Γ →* GL (Fin 2) k)
    (r : Γ →* Matrix (Fin 2) (Fin 2) k) (hi : RepIso ρ r.toHomUnits) (h : IsIrr (ρ.comp φ)) (V : Submodule k (Fin 2 → k))
    (hV : ∀ s, ∀ v ∈ V, r (φ s) *ᵥ v ∈ V) : V = ⊥ ∨ V = ⊤ := by
  obtain ⟨g, hg⟩ := hi
  have h' : IsIrr (r.toHomUnits.comp φ) := isIrr_iso (r := ρ.comp φ) ⟨g, fun s => hg (φ s)⟩ h
  exact h'.2.2 V le_top hV

end UpperTheory.V.Cu.IrreducibilityFourDim

open UpperTheory.V.Cu.IrreducibilityFourDim in
/- English proof (translation)
Introduce `hal Ω _ _ _ l _ d T hle hok`. Take `⟨t, htG, htK⟩` from `hal Ω l d T hle hok`. Establish `hD : d.D.Good` using `d.ctx.1`. Set `f : d.c₁.O →+* PadicAlgCl l` to `algebraMap d.c₁.O (PadicAlgCl l)`. Use `haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩`.

Take `⟨hcont, -, -, -, hres, -⟩` from `resFacts ℚ T.F Ω l 2 d.ρ`. Establish `hop : IsOpen ((T.GalL ⊓ d.K'.fixingSubgroup.comap (resQ T.F) : Subgroup (G T.F Ω)) : Set (G T.F Ω))` using `((IntermediateField.fixingSubgroup_isOpen T.K).preimage hcont).inter ((IntermediateField.fixingSubgroup_isOpen d.K').preimage hcont)`. Establish `hI` using `irrAb l (G T.F Ω) 2 (d.ρ.comp (galEmb ℚ T.F Ω)) (d.eis.cont.comp hcont) (hres d.irr) (T.GalL ⊓ d.K'.fixingSubgroup.comap (resQ T.F)) (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)) hop (inf_le_inf_right _ inf_le_left) (fun a ha b hb => ⟨⟨T.GalL.mul_mem (T.GalL.mul_mem (T.GalL.mul_m …`. Express the relevant statement in the definitionally equal form `_ ∈ (cycZ T.F Ω l).ker`. Rewrite using `[MonoidHom.mem_ker]`.

Simplify using `only [map_mul, map_inv]`. Rewrite using `[mul_comm (cycZ T.F Ω l a), mul_inv_cancel_right, mul_inv_cancel]⟩,`. Use the proof step `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha.2 hb.2) (Subgroup.inv_mem _ ha.2)) (Subgroup.inv_mem _ hb.2)⟩)`. Establish `hirrA : ∀ V : Submodule (PadicAlgCl l) (Fin 2 → PadicAlgCl l), (∀ i ∈ {x : T.G' | resQ T.F (x : G T.F Ω) ∈ d.K'.fixingSubgroup}, ∀ v ∈ V, (d.ρ₁ (resQ T.F i)).map f *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤` using `fun V hV => by`. Use `irr_mat ((galEmb ℚ T.F Ω).comp (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)).subtype) d.ρ (mapRep f d.ρ₁) d.mod.iso (by rw [← MonoidHom.comp_assoc]; exact hI) V fun s v hv => ?_` and prove the remaining obligations.

Establish `e : mapRep f d.ρ₁ (((galEmb ℚ T.F Ω).comp (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)).subtype) s) = (d.ρ₁ (resQ T.F s.1)).map f` using `rfl`. Rewrite using `[e]`. Conclude with `hV ⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩ (Subgroup.mem_inf.1 s.2).2 v hv`. Establish `hl : l.Prime` using `Fact.out`. Establish `hA : (d.D.pl l).valuation (l : Ω) < 1` using `hD.pl_over l hl`.

Choose the witnesses or unpack the hypotheses as in `⟨n, hn, hsn⟩ : ∃ n : ℕ, 0 < n ∧ (d.D.s0 : G ℚ Ω) ^ n ∈ T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup := by`. Establish `hU : IsOpen ((T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))` using `((IntermediateField.fixingSubgroup_isOpen T.F).inter (IntermediateField.fixingSubgroup_isOpen T.K)).inter (IntermediateField.fixingSubgroup_isOpen d.K')`. Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Use `haveI : Finite (G ℚ Ω ⧸ (T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup)) := Subgroup.quotient_finite_of_isOpen _ hU`. Use `haveI : (T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Take `⟨n, hn, -, h⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup)) (d.D.s0 : G ℚ Ω)`. Conclude with `⟨n, hn, h⟩`. Take `⟨h, hhdef⟩ : ∃ h : G ℚ Ω, h = (d.D.s0 : G ℚ Ω) ^ n` from `⟨_, rfl⟩`. Rewrite `hsn` using `[← hhdef]`. Establish `hh : h ∈ Ine (F` using `ℚ) (d.D.pl l) := hhdef ▸ pow_mem hD.decompSigma_mem.1.1 n`.

Set `hT : G T.F Ω` to `AlgEquiv.ofRingEquiv (f := h.toRingEquiv) (fun x => hsn.1.1 ⟨x.1, x.2⟩)`. Establish `hhT : resQ T.F hT = h` using `AlgEquiv.ext fun _ => rfl`. Establish `hTL : hT ∈ T.GalL` using `by show resQ T.F hT ∈ T.K.fixingSubgroup`. Rewrite using `[hhT]`. Conclude with `hsn.1.2`.

Establish `huG : hT * t * hT⁻¹ * t⁻¹ ∈ T.G'` using `⟨T.GalL.mul_mem (T.GalL.mul_mem (T.GalL.mul_mem hTL htG.1) (T.GalL.inv_mem hTL)) (T.GalL.inv_mem htG.1), by`. Express the relevant statement in the definitionally equal form `_ ∈ (cycZ T.F Ω l).ker`. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `only [map_mul, map_inv]`. Rewrite using `[mul_comm (cycZ T.F Ω l hT), mul_inv_cancel_right, mul_inv_cancel]⟩`.

Establish `hru : resQ T.F (hT * t * hT⁻¹ * t⁻¹) = h * resQ T.F t * h⁻¹ * (resQ T.F t)⁻¹`. Simplify using `only [map_mul, map_inv, hhT]`. Establish `onh` using `d.tau.on h hsn.2`. Establish `onhi` using `d.tau.on h⁻¹ (inv_mem hsn.2)`. Establish `offt` using `d.tau.off (resQ T.F t) htK`.

Establish `offti` using `d.tau.off (resQ T.F t)⁻¹ (fun hc => htK (by simpa using inv_mem hc))`. Establish `hYt : d.τ (resQ T.F t) * d.τ (resQ T.F t)⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hXh : d.τ h * d.τ h⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hZ : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) = d.τ h * d.τ (resQ T.F t) * d.τ h⁻¹ * d.τ (resQ T.F t)⁻¹`. Rewrite using `[hru, map_mul, map_mul, map_mul]`.

Take `⟨z1, z2, zp, zm⟩` from `shape4 _ _ _ _ onh.1 onh.2 onhi.1 onhi.2 offt.1 offt.2 offti.1 offti.2 hYt`. Rewrite `z1`, `z2`, `zp`, `zm` using `[← hZ]`. Establish `huK : resQ T.F (hT * t * hT⁻¹ * t⁻¹) ∈ d.K'.fixingSubgroup`. Assume the negation of the conclusion as `hc`. Take `⟨o1, o2⟩` from `d.tau.off _ hc`.

Establish `e0 : (2 : PadicAlgCl l) * f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) = 0`. Use `congrArg f (z1.symm.trans o1)` as an intermediate fact. Rewrite `this` using `[map_neg]`. Take the linear combination `this`. Establish `e1 : (2 : PadicAlgCl l) * f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1) = 0`.

Use `congrArg f (z2.symm.trans o2)` as an intermediate fact. Rewrite `this` using `[map_neg]`. Take the linear combination `this`. Establish `h0` using `(mul_eq_zero.1 e0).resolve_left two_ne_zero`. Establish `h1` using `(mul_eq_zero.1 e1).resolve_left two_ne_zero`.

Apply `((det_unit d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹))).map f).ne_zero` to reduce the goal to its premises. Rewrite using `[Matrix.det_fin_two, map_sub, map_mul f, map_mul f, h0, h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : (f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) + f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1)) ^ 2 ≠ (f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) - f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1)) ^ 2`. Introduce `heq`.

Take `⟨i1, i2⟩` from `on_inv _ _ onh.1 onh.2 onhi.1 onhi.2 hXh`. Establish `fm` using `on_form _ (d.tau.form h) onh.2`. Establish `kp : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0 + d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1 = (d.τ h 0 0 + d.τ h 0 1) ^ 2`. Take the linear combination `zp - (d.τ h 0 0 + d.τ h 0 1) * (d.τ h⁻¹ 0 0 - d.τ h⁻¹ 0 1) * fm + (d.τ h 0 0 + d.τ h 0 1) ^ 2 * i2`. Establish `km : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0 - d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1 = (d.τ h 0 0 - d.τ h 0 1) ^ 2`.

Take the linear combination `zm - (d.τ h 0 0 - d.τ h 0 1) * (d.τ h⁻¹ 0 0 + d.τ h⁻¹ 0 1) * fm + (d.τ h 0 0 - d.τ h 0 1) ^ 2 * i1`. Establish `fm' : f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) = 1`. Rewrite using `[← map_mul, fm, map_one]`. Rewrite `heq` using `[← map_add, ← map_sub, kp, km, map_pow, map_pow]`. Establish `hx8 : f (d.τ h 0 0 + d.τ h 0 1) ^ 8 = 1`.

Take the linear combination `f (d.τ h 0 0 + d.τ h 0 1) ^ 4 * heq + ((f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 3 + (f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 2 + f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) + 1) * fm'`. Establish `hy8 : f (d.τ h 0 0 - d.τ h 0 1) ^ 8 = 1`. Take the linear combination `-(f (d.τ h 0 0 - d.τ h 0 1) ^ 4) * heq + ((f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 3 + (f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 2 + f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) + 1) * fm'`. Establish `hi` using `d.tau.ine (d.D.pl l) hA h hh`. Establish `E8 : f (chiO ℚ Ω l d.c₁.O h : d.c₁.O) ^ (d.m * 8) = 1`.

Break down `d.tau.sgn (d.D.pl l) with hs | hs` into its components or cases. Rewrite `hi` using `[hs, mul_one]`. Rewrite `hx8` using `[hi, Units.val_pow_eq_pow_val, map_pow, ← pow_mul]`. Conclude with `hx8`. Rewrite `hi` using `[hs]`.

Establish `hi' : d.τ h 0 0 - d.τ h 0 1 = ((chiO ℚ Ω l d.c₁.O h ^ d.m : d.c₁.Oˣ) : d.c₁.O)`. Rewrite using `[← hi]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hy8` using `[hi', Units.val_pow_eq_pow_val, map_pow, ← pow_mul]`. Conclude with `hy8`.

Establish `hE : f (chiO ℚ Ω l d.c₁.O h : d.c₁.O) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l h : ℤ_[l])` using `(IsScalarTower.algebraMap_apply ℤ_[l] d.c₁.O (PadicAlgCl l) _).symm`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Conclude with `(algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp Subtype.val_injective`. Establish `hc : (cycZ ℚ Ω l h) ^ (d.m * 8) = 1`.

Apply `Units.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, ← hE]`. Conclude with `E8`. Rewrite `hc` using `[hhdef, map_pow, ← pow_mul]`.

Conclude with `hD.decompSigma_ord (isOfFinOrder_iff_pow_eq_one.2 ⟨n * (d.m * 8), Nat.mul_pos hn (Nat.mul_pos d.tau.pos (by norm_num)), hc⟩)`. Establish `hkpm : ∀ i : T.G', resQ T.F (i : G T.F Ω) ∈ d.K'.fixingSubgroup → (f (d.τ (resQ T.F i) 0 0) + f (d.τ (resQ T.F i) 0 1)) * (f (d.τ (resQ T.F i) 0 0) - f (d.τ (resQ T.F i) 0 1)) = 1` using `fun i hi => by`. Rewrite using `[← map_add, ← map_sub, ← map_mul, on_form _ (d.tau.form _) (d.tau.on _ hi).2, map_one]`. Apply `KStar.Schema.span_eq_top_of_irreducible` to reduce the goal to its premises. Introduce `W hW`.

Use `key two_ne_zero {x : T.G' | resQ T.F (x : G T.F Ω) ∈ d.K'.fixingSubgroup} (fun i => (d.ρ₁ (resQ T.F i)).map f) (fun i => (d.τ (resQ T.F i)).map f) (fun i hi => ⟨congrArg f (d.tau.on _ hi).1, congrArg f (d.tau.on _ hi).2⟩) (fun i hi => left_ne_zero_of_mul_eq_one (hkpm i hi)) (fun …` and prove the remaining obligations. Introduce `i _ v hv`. Establish `e : ((d.Q T).map f).r.comp T.G'.subtype i = f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) • UpperTheory.V.Cu.tn ((d.ρ₁ (resQ T.F i)).map f) ((d.τ (resQ T.F i)).map f)` using `smul_tn_map f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) (d.ρ₁ (resQ T.F i)) (d.τ (resQ T.F i))`. Establish `h1 : (f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) • UpperTheory.V.Cu.tn ((d.ρ₁ (resQ T.F i)).map f) ((d.τ (resQ T.F i)).map f)) *ᵥ v ∈ W`. Rewrite using `[← e]`.

Conclude with `hW i v hv`. Rewrite `h1` using `[Matrix.smul_mulVec]`. Establish `hne0 : f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) ≠ 0` using `((S3.toC d.h d.δ (resQ T.F i)).isUnit.map f).ne_zero`. Use `W.smul_mem (f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O))⁻¹ h1` as an intermediate fact. Rewrite `this` using `[inv_smul_smul₀ hne0]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Cu.irrOf4_of : AlNe → IrrOf4 := by
  intro hal Ω _ _ _ l _ d T hle hok
  obtain ⟨t, htG, htK⟩ := hal Ω l d T hle hok
  have hD : d.D.Good := d.ctx.1
  let f : d.c₁.O →+* PadicAlgCl l := algebraMap d.c₁.O (PadicAlgCl l)

  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  obtain ⟨hcont, -, -, -, hres, -⟩ := resFacts ℚ T.F Ω l 2 d.ρ
  have hop : IsOpen ((T.GalL ⊓ d.K'.fixingSubgroup.comap (resQ T.F) : Subgroup (G T.F Ω)) : Set (G T.F Ω)) :=
    ((IntermediateField.fixingSubgroup_isOpen T.K).preimage hcont).inter
      ((IntermediateField.fixingSubgroup_isOpen d.K').preimage hcont)
  have hI := irrAb l (G T.F Ω) 2 (d.ρ.comp (galEmb ℚ T.F Ω)) (d.eis.cont.comp hcont) (hres d.irr)
    (T.GalL ⊓ d.K'.fixingSubgroup.comap (resQ T.F)) (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)) hop
    (inf_le_inf_right _ inf_le_left)
    (fun a ha b hb => ⟨⟨T.GalL.mul_mem (T.GalL.mul_mem (T.GalL.mul_mem ha.1 hb.1) (T.GalL.inv_mem ha.1)) (T.GalL.inv_mem hb.1), by
      change _ ∈ (cycZ T.F Ω l).ker
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_comm (cycZ T.F Ω l a), mul_inv_cancel_right, mul_inv_cancel]⟩,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha.2 hb.2) (Subgroup.inv_mem _ ha.2)) (Subgroup.inv_mem _ hb.2)⟩)
  have hirrA : ∀ V : Submodule (PadicAlgCl l) (Fin 2 → PadicAlgCl l),
      (∀ i ∈ {x : T.G' | resQ T.F (x : G T.F Ω) ∈ d.K'.fixingSubgroup}, ∀ v ∈ V,
        (d.ρ₁ (resQ T.F i)).map f *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤ := fun V hV => by
    refine irr_mat ((galEmb ℚ T.F Ω).comp (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)).subtype) d.ρ (mapRep f d.ρ₁) d.mod.iso
      (by rw [← MonoidHom.comp_assoc]; exact hI) V fun s v hv => ?_
    have e : mapRep f d.ρ₁ (((galEmb ℚ T.F Ω).comp (T.G' ⊓ d.K'.fixingSubgroup.comap (resQ T.F)).subtype) s) =
        (d.ρ₁ (resQ T.F s.1)).map f := rfl
    rw [e]
    exact hV ⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩ (Subgroup.mem_inf.1 s.2).2 v hv

  have hl : l.Prime := Fact.out
  have hA : (d.D.pl l).valuation (l : Ω) < 1 := hD.pl_over l hl
  obtain ⟨n, hn, hsn⟩ : ∃ n : ℕ, 0 < n ∧ (d.D.s0 : G ℚ Ω) ^ n ∈
      T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup := by
    have hU : IsOpen ((T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup : Subgroup (G ℚ Ω)) :
        Set (G ℚ Ω)) :=
      ((IntermediateField.fixingSubgroup_isOpen T.F).inter (IntermediateField.fixingSubgroup_isOpen T.K)).inter
        (IntermediateField.fixingSubgroup_isOpen d.K')
    haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
    haveI : Finite (G ℚ Ω ⧸ (T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup)) :=
      Subgroup.quotient_finite_of_isOpen _ hU
    haveI : (T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup).FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨n, hn, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := T.F.fixingSubgroup ⊓ T.K.fixingSubgroup ⊓ d.K'.fixingSubgroup))
      (d.D.s0 : G ℚ Ω)
    exact ⟨n, hn, h⟩
  obtain ⟨h, hhdef⟩ : ∃ h : G ℚ Ω, h = (d.D.s0 : G ℚ Ω) ^ n := ⟨_, rfl⟩
  rw [← hhdef] at hsn
  have hh : h ∈ Ine (F := ℚ) (d.D.pl l) := hhdef ▸ pow_mem hD.decompSigma_mem.1.1 n
  let hT : G T.F Ω := AlgEquiv.ofRingEquiv (f := h.toRingEquiv) (fun x => hsn.1.1 ⟨x.1, x.2⟩)
  have hhT : resQ T.F hT = h := AlgEquiv.ext fun _ => rfl
  have hTL : hT ∈ T.GalL := by
    show resQ T.F hT ∈ T.K.fixingSubgroup
    rw [hhT]
    exact hsn.1.2

  have huG : hT * t * hT⁻¹ * t⁻¹ ∈ T.G' := ⟨T.GalL.mul_mem (T.GalL.mul_mem (T.GalL.mul_mem hTL htG.1)
      (T.GalL.inv_mem hTL)) (T.GalL.inv_mem htG.1), by
    change _ ∈ (cycZ T.F Ω l).ker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (cycZ T.F Ω l hT), mul_inv_cancel_right, mul_inv_cancel]⟩
  have hru : resQ T.F (hT * t * hT⁻¹ * t⁻¹) = h * resQ T.F t * h⁻¹ * (resQ T.F t)⁻¹ := by
    simp only [map_mul, map_inv, hhT]
  have onh := d.tau.on h hsn.2
  have onhi := d.tau.on h⁻¹ (inv_mem hsn.2)
  have offt := d.tau.off (resQ T.F t) htK
  have offti := d.tau.off (resQ T.F t)⁻¹ (fun hc => htK (by simpa using inv_mem hc))
  have hYt : d.τ (resQ T.F t) * d.τ (resQ T.F t)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hXh : d.τ h * d.τ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hZ : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) = d.τ h * d.τ (resQ T.F t) * d.τ h⁻¹ * d.τ (resQ T.F t)⁻¹ := by
    rw [hru, map_mul, map_mul, map_mul]
  obtain ⟨z1, z2, zp, zm⟩ := shape4 _ _ _ _ onh.1 onh.2 onhi.1 onhi.2 offt.1 offt.2 offti.1 offti.2 hYt
  rw [← hZ] at z1 z2 zp zm
  have huK : resQ T.F (hT * t * hT⁻¹ * t⁻¹) ∈ d.K'.fixingSubgroup := by
    by_contra hc
    obtain ⟨o1, o2⟩ := d.tau.off _ hc
    have e0 : (2 : PadicAlgCl l) * f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) = 0 := by
      have := congrArg f (z1.symm.trans o1)
      rw [map_neg] at this
      linear_combination this
    have e1 : (2 : PadicAlgCl l) * f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1) = 0 := by
      have := congrArg f (z2.symm.trans o2)
      rw [map_neg] at this
      linear_combination this
    have h0 := (mul_eq_zero.1 e0).resolve_left two_ne_zero
    have h1 := (mul_eq_zero.1 e1).resolve_left two_ne_zero
    apply ((det_unit d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹))).map f).ne_zero
    rw [Matrix.det_fin_two, map_sub, map_mul f, map_mul f, h0, h1]
    ring

  have hne : (f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) + f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1)) ^ 2 ≠
      (f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0) - f (d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1)) ^ 2 := by
    intro heq
    obtain ⟨i1, i2⟩ := on_inv _ _ onh.1 onh.2 onhi.1 onhi.2 hXh
    have fm := on_form _ (d.tau.form h) onh.2
    have kp : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0 + d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1 =
        (d.τ h 0 0 + d.τ h 0 1) ^ 2 := by
      linear_combination zp - (d.τ h 0 0 + d.τ h 0 1) * (d.τ h⁻¹ 0 0 - d.τ h⁻¹ 0 1) * fm +
        (d.τ h 0 0 + d.τ h 0 1) ^ 2 * i2
    have km : d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 0 - d.τ (resQ T.F (hT * t * hT⁻¹ * t⁻¹)) 0 1 =
        (d.τ h 0 0 - d.τ h 0 1) ^ 2 := by
      linear_combination zm - (d.τ h 0 0 - d.τ h 0 1) * (d.τ h⁻¹ 0 0 + d.τ h⁻¹ 0 1) * fm +
        (d.τ h 0 0 - d.τ h 0 1) ^ 2 * i1
    have fm' : f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) = 1 := by
      rw [← map_mul, fm, map_one]
    rw [← map_add, ← map_sub, kp, km, map_pow, map_pow] at heq
    have hx8 : f (d.τ h 0 0 + d.τ h 0 1) ^ 8 = 1 := by
      linear_combination f (d.τ h 0 0 + d.τ h 0 1) ^ 4 * heq +
        ((f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 3 +
          (f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 2 +
          f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) + 1) * fm'
    have hy8 : f (d.τ h 0 0 - d.τ h 0 1) ^ 8 = 1 := by
      linear_combination -(f (d.τ h 0 0 - d.τ h 0 1) ^ 4) * heq +
        ((f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 3 +
          (f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1)) ^ 2 +
          f (d.τ h 0 0 + d.τ h 0 1) * f (d.τ h 0 0 - d.τ h 0 1) + 1) * fm'
    have hi := d.tau.ine (d.D.pl l) hA h hh
    have E8 : f (chiO ℚ Ω l d.c₁.O h : d.c₁.O) ^ (d.m * 8) = 1 := by
      rcases d.tau.sgn (d.D.pl l) with hs | hs
      · rw [hs, mul_one] at hi
        rw [hi, Units.val_pow_eq_pow_val, map_pow, ← pow_mul] at hx8
        exact hx8
      · rw [hs] at hi
        have hi' : d.τ h 0 0 - d.τ h 0 1 = ((chiO ℚ Ω l d.c₁.O h ^ d.m : d.c₁.Oˣ) : d.c₁.O) := by
          rw [← hi]; ring
        rw [hi', Units.val_pow_eq_pow_val, map_pow, ← pow_mul] at hy8
        exact hy8
    have hE : f (chiO ℚ Ω l d.c₁.O h : d.c₁.O) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l h : ℤ_[l]) :=
      (IsScalarTower.algebraMap_apply ℤ_[l] d.c₁.O (PadicAlgCl l) _).symm
    have hinj : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp Subtype.val_injective
    have hc : (cycZ ℚ Ω l h) ^ (d.m * 8) = 1 := by
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, ← hE]
      exact E8
    rw [hhdef, map_pow, ← pow_mul] at hc
    exact hD.decompSigma_ord (isOfFinOrder_iff_pow_eq_one.2 ⟨n * (d.m * 8), Nat.mul_pos hn (Nat.mul_pos d.tau.pos (by norm_num)), hc⟩)

  have hkpm : ∀ i : T.G', resQ T.F (i : G T.F Ω) ∈ d.K'.fixingSubgroup →
      (f (d.τ (resQ T.F i) 0 0) + f (d.τ (resQ T.F i) 0 1)) * (f (d.τ (resQ T.F i) 0 0) - f (d.τ (resQ T.F i) 0 1)) = 1 :=
    fun i hi => by
      rw [← map_add, ← map_sub, ← map_mul, on_form _ (d.tau.form _) (d.tau.on _ hi).2, map_one]
  apply KStar.Schema.span_eq_top_of_irreducible
  intro W hW
  refine key two_ne_zero {x : T.G' | resQ T.F (x : G T.F Ω) ∈ d.K'.fixingSubgroup}
    (fun i => (d.ρ₁ (resQ T.F i)).map f) (fun i => (d.τ (resQ T.F i)).map f)
    (fun i hi => ⟨congrArg f (d.tau.on _ hi).1, congrArg f (d.tau.on _ hi).2⟩)
    (fun i hi => left_ne_zero_of_mul_eq_one (hkpm i hi)) (fun i hi => right_ne_zero_of_mul_eq_one (hkpm i hi))
    hirrA ⟨t, htG⟩
    ⟨(congrArg f (d.tau.off _ htK).1).trans (map_neg f _), (congrArg f (d.tau.off _ htK).2).trans (map_neg f _)⟩
    (fun h0 => ((det_unit d.τ (resQ T.F t)).map f).ne_zero ((RingHom.map_det f _).trans h0))
    (fun h0 => ((det_unit d.ρ₁ (resQ T.F t)).map f).ne_zero ((RingHom.map_det f _).trans h0))
    ⟨hT * t * hT⁻¹ * t⁻¹, huG⟩ huK
    (fun h0 => ((det_unit d.ρ₁ (resQ T.F (hT * t * hT⁻¹ * t⁻¹))).map f).ne_zero ((RingHom.map_det f _).trans h0))
    hne W ?_
  intro i _ v hv
  have e : ((d.Q T).map f).r.comp T.G'.subtype i = f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) •
      UpperTheory.V.Cu.tn ((d.ρ₁ (resQ T.F i)).map f) ((d.τ (resQ T.F i)).map f) :=
    smul_tn_map f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) (d.ρ₁ (resQ T.F i)) (d.τ (resQ T.F i))
  have h1 : (f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) •
      UpperTheory.V.Cu.tn ((d.ρ₁ (resQ T.F i)).map f) ((d.τ (resQ T.F i)).map f)) *ᵥ v ∈ W := by
    rw [← e]
    exact hW i v hv
  rw [Matrix.smul_mulVec] at h1
  have hne0 : f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O) ≠ 0 := ((S3.toC d.h d.δ (resQ T.F i)).isUnit.map f).ne_zero
  have := W.smul_mem (f (S3.toC d.h d.δ (resQ T.F i) : d.c₁.O))⁻¹ h1
  rwa [inv_smul_smul₀ hne0] at this

end
