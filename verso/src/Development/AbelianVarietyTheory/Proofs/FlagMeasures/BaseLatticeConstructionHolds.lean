import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotien
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace

noncomputable section
open scoped Classical Pointwise
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm

namespace GlobalTheory.TypeAsm.LatticeOrthogonalComplement

section Gen
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {r : ℕ}

/- English proof (translation)
Rewrite using `[← H.herm, h, star_zero]`.
-/
theorem B_swap {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

/- English proof (translation)
Establish `key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0`. Introduce `b`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact F.zperp b`. Consider the case `cast c => exact F.iso b c`.

Establish `: F.X ≤ LinearMap.ker (H.B.flip (F.e a))`. Unfold `FlagD.X FlagD.Xa`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Simplify using `using key b`.

Simplify using `using this hx`.
-/
theorem X_B_e (F : FlagD H r) (a : Fin (r + 1)) (x : V) (hx : x ∈ F.X) : H.B x (F.e a) = 0 := by
  have key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0 := by
    intro b
    induction a using Fin.lastCases with
    | last => exact F.zperp b
    | cast c => exact F.iso b c
  have : F.X ≤ LinearMap.ker (H.B.flip (F.e a)) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using key b
  simpa using this hx

/- English proof (translation)
Establish `: F.X ≤ LinearMap.ker (H.B.flip v)`. Unfold `FlagD.X FlagD.Xa`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Simplify using `using hv b.castSucc`.

Simplify using `using this hx`.
-/
theorem X_B_perp (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) (x : V) (hx : x ∈ F.X) :
    H.B x v = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip v) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  simpa using this hx

/- English proof (translation)
Unfold `V0`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))`. Consider the case `cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))`.
-/
theorem flag_vector_mem_base_lattice (F : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F := by
  unfold V0
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))

/- English proof (translation)
Rewrite using `[wSp, mem_perp_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`. Conclude with `B_swap (h _ (flag_vector_mem_base_lattice F a))`. Introduce `h x hx`.

Apply `B_swap` to reduce the goal to its premises. Establish `: V0 F F ≤ LinearMap.ker (H.B.flip v)`. Unfold `V0`. Use `sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce `y hy`.

Simplify using `using X_B_perp F h y hy`. Introduce `y hy`. Simplify using `using X_B_perp F h y hy`. Apply the tactic sequence `rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)`. Simplify using `using this hx`.
-/
theorem mem_wSp (F : FlagD H r) (v : V) : v ∈ wSp F F ↔ ∀ a, H.B (F.e a) v = 0 := by
  rw [wSp, mem_perp_iff]
  constructor
  · intro h a
    exact B_swap (h _ (flag_vector_mem_base_lattice F a))
  · intro h x hx
    apply B_swap
    have : V0 F F ≤ LinearMap.ker (H.B.flip v) := by
      unfold V0
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro y hy; simpa using X_B_perp F h y hy
      · intro y hy; simpa using X_B_perp F h y hy
      · rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)
    simpa using this hx

/- English proof (translation)
Simplify using `only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, h1⟩, h2⟩`. Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨⟨?_, h1⟩, h2⟩` and prove the remaining obligations. Rewrite using `[uPerp, mem_perp_iff]`. Rewrite `h2` using `[wSp, mem_perp_iff]`. Conclude with `fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)`.
-/
theorem mem_perp_lattice_flag_iff (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (v : V) :
    v ∈ flagPairDefinitePartLattice F F Λ ↔ v ∈ Λ ⊔ rs (𝓞 K) F.X ∧ v ∈ wSp F F := by
  simp only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [uPerp, mem_perp_iff]
    rw [wSp, mem_perp_iff] at h2
    exact fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)

variable {F : FlagD H r} {e : W →ₗ[K] V}

/- English proof (translation)
The claim follows from `(hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a`.
-/
theorem e_perp (hE : IsEmb F HW e) (w : W) (a : Fin (r + 1)) : H.B (F.e a) (e w) = 0 :=
  (hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a

/- English proof (translation)
The claim follows from `(mem_wSp F _).2 (e_perp hE w)`.
-/
theorem e_wSp (hE : IsEmb F HW e) (w : W) : e w ∈ wSp F F := (mem_wSp F _).2 (e_perp hE w)

/- English proof (translation)
The claim follows from `(mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)`.
-/
theorem X_wSp (x : V) (hx : x ∈ F.X) : x ∈ wSp F F :=
  (mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)

/- English proof (translation)
Take `⟨_, ⟨w, rfl⟩, z, hz, h⟩` from `Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))`. Conclude with `⟨w, by rw [← h]; simpa using hz⟩`.
-/
theorem decomp (hE : IsEmb F HW e) {v : V} (hv : v ∈ wSp F F) : ∃ w, v - e w ∈ F.X := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))
  exact ⟨w, by rw [← h]; simpa using hz⟩

/- English proof (translation)
The claim follows from `X_B_perp F (e_perp hE w) x hx`.
-/
theorem XB_e (hE : IsEmb F HW e) (x : V) (hx : x ∈ F.X) (w : W) : H.B x (e w) = 0 :=
  X_B_perp F (e_perp hE w) x hx

/- English proof (translation)
The claim follows from `(mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩`.
-/
theorem memL_e (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V) (w : W) :
    e w ∈ flagPairDefinitePartLattice F F Λ ↔ w ∈ lat0 F e Λ :=
  (mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩

/- English proof (translation)
The claim follows from `(mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩`.
-/
theorem X_L (Λ : Submodule (𝓞 K) V) (x : V) (hx : x ∈ F.X) : x ∈ flagPairDefinitePartLattice F F Λ :=
  (mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩

/- English proof (translation)
Use `set L := flagPairDefinitePartLattice F F Λ with hL`. Use `set M := lat0 F e Λ with hM`. Use `set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW`. Use `set DV := dual H L with hDV`. Establish `hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K)` using `fun w => by`.

Rewrite using `[hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Simplify using `only [LinearMap.flip_apply]`. Establish `hin : ∀ w : DW, e w ∈ DV`. Introduce and unpack `⟨w, hw⟩`. Rewrite using `[hDV, mem_dual_iff, hspan]`.

Use `⟨e_wSp hE w, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨w', hw'⟩` from `decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2`. Establish `hw'M : w' ∈ M` using `(memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))`. Establish `h1 : H.B (e w) x = HW.B w w'`. Establish `e1 : x = e w' + (x - e w')` using `by abel`.

Rewrite using `[e1, map_add, B_swap (XB_e hE _ hw' w), add_zero, hE.1]`. Rewrite using `[h1]`. Conclude with `(hmemW w).1 hw w' hw'M`. Set `f : DW →ₗ[𝓞 K] DV` to `LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)`. Set `Φ` to `(L.comap DV.subtype).mkQ ∘ₗ f`.

Establish `hker : LinearMap.ker Φ = M.comap DW.subtype`. Use extensionality with `w`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap]`. Conclude with `memL_e hE Λ w`. Establish `hsurj : Function.Surjective Φ`.

Introduce `q`. Take `⟨⟨v, hv⟩, rfl⟩` from `Submodule.mkQ_surjective _ q`. Establish `hv'` using `(mem_dual_iff H L v).1 hv`. Rewrite `hv'` using `[hspan]`. Take `⟨w, hw⟩` from `decomp hE hv'.1`.

Establish `hwD : w ∈ DW` using `(hmemW w).2 fun y hy => by`. Establish `h1 : HW.B w y = H.B v (e y)`. Rewrite using `[← hE.1]`. Establish `e1 : v = e w + (v - e w)` using `by abel`. Use `conv_rhs => rw [e1]`.

Rewrite using `[map_add, LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]`. Rewrite using `[h1]`. Conclude with `hv'.2 _ ((memL_e hE Λ y).2 hy)`. Use `⟨⟨w, hwD⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩`.

Rewrite using `[Submodule.Quotient.eq]`. Use `show e w - v ∈ L`. Use `L.neg_mem (X_L Λ _ hw)` as an intermediate fact. Simplify using `using this`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩`.
-/
theorem quotEquiv (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V)
    (hspan : Submodule.span K (flagPairDefinitePartLattice F F Λ : Set V) = wSp F F) :
    Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)) ⧸
        (lat0 F e Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)).subtype) ≃ₗ[𝓞 K]
      (↥(dual H (flagPairDefinitePartLattice F F Λ)) ⧸ (flagPairDefinitePartLattice F F Λ).comap (dual H (flagPairDefinitePartLattice F F Λ)).subtype)) := by
  set L := flagPairDefinitePartLattice F F Λ with hL
  set M := lat0 F e Λ with hM
  set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW
  set DV := dual H L with hDV
  have hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K) := fun w => by
    rw [hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    simp only [LinearMap.flip_apply]
  have hin : ∀ w : DW, e w ∈ DV := by
    rintro ⟨w, hw⟩
    rw [hDV, mem_dual_iff, hspan]
    refine ⟨e_wSp hE w, fun x hx => ?_⟩
    obtain ⟨w', hw'⟩ := decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2
    have hw'M : w' ∈ M := (memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))
    have h1 : H.B (e w) x = HW.B w w' := by
      have e1 : x = e w' + (x - e w') := by abel
      rw [e1, map_add, B_swap (XB_e hE _ hw' w), add_zero, hE.1]
    rw [h1]
    exact (hmemW w).1 hw w' hw'M
  let f : DW →ₗ[𝓞 K] DV :=
    LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)
  let Φ := (L.comap DV.subtype).mkQ ∘ₗ f
  have hker : LinearMap.ker Φ = M.comap DW.subtype := by
    ext w
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    exact memL_e hE Λ w
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hv' := (mem_dual_iff H L v).1 hv
    rw [hspan] at hv'
    obtain ⟨w, hw⟩ := decomp hE hv'.1
    have hwD : w ∈ DW := (hmemW w).2 fun y hy => by
      have h1 : HW.B w y = H.B v (e y) := by
        rw [← hE.1]
        have e1 : v = e w + (v - e w) := by abel
        conv_rhs => rw [e1]
        rw [map_add, LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]
      rw [h1]
      exact hv'.2 _ ((memL_e hE Λ y).2 hy)
    refine ⟨⟨w, hwD⟩, ?_⟩
    show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩
    rw [Submodule.Quotient.eq]
    show e w - v ∈ L
    have := L.neg_mem (X_L Λ _ hw)
    simpa using this
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

end Gen

end GlobalTheory.TypeAsm.LatticeOrthogonalComplement

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
open LatticeOrthogonalComplement
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D large₂ X Y u hS W HW hE Λ hΛ`. Take `⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩` from `GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS`. Take `⟨N, hF, hF', -, hT, -, hTerm, -, -⟩` from `GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS Λ (Or.inl hΛ)`. Establish `hg1 : 1 ≤ gS D` using `by omega`. Take `⟨-, -, -, hLat, -, hNe⟩` from `GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm`.

Rewrite `hLat`, `hNe` using `[hF, hF']`. Rewrite `hNe` using `[hT]`. Establish `hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N`. Use `adapt_self N` as an intermediate fact. Rewrite `this` using `[hF, hF']`. Then use the resulting hypothesis.

Take `⟨⟨hInt, -⟩, -⟩` from `GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N (gS D) Λ hg1 hE hAd hTerm`. Establish `hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ`. Use extensionality with `w`. Express the relevant statement in the definitionally equal form `W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ`. Rewrite using `[sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]`.

Use `⟨hd ▸ hInt, ?_⟩` and prove the remaining obligations. Take `⟨q⟩` from `quotEquiv hE Λ hLat.2`. Take `⟨i⟩` from `hNe`. Conclude with `⟨q.trans i⟩`.
-/
theorem lat0C : LatticeNormalizationCondition := by
  intro D large₂ X Y u hS W HW hE Λ hΛ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', -, hT, -, hTerm, -, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS Λ (Or.inl hΛ)
  have hg1 : 1 ≤ gS D := by omega
  obtain ⟨-, -, -, hLat, -, hNe⟩ := GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm
  rw [hF, hF'] at hLat hNe
  rw [hT] at hNe
  have hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N := by
    have := adapt_self N
    rwa [hF, hF'] at this
  obtain ⟨⟨hInt, -⟩, -⟩ := GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N
    (gS D) Λ hg1 hE hAd hTerm
  have hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ := by
    ext w
    change W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ
    rw [sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]
  refine ⟨hd ▸ hInt, ?_⟩
  obtain ⟨q⟩ := quotEquiv hE Λ hLat.2
  obtain ⟨i⟩ := hNe
  exact ⟨q.trans i⟩

end GlobalTheory.TypeAsm
