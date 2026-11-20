import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ResLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxCpRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)` as an intermediate fact. Conclude with `this`.
-/
private theorem preLine_desc {Λ A T S : Type} [CommRing Λ] [CommRing A] [CommRing T] [CommRing S] [Algebra Λ A]
    [Algebra Λ T] [Algebra Λ S] (f : A →ₐ[Λ] S) (j : T →ₐ[Λ] S) (hj : Function.Injective j)
    (h : ∀ x, f x ∈ j.range) : ∃ g : A →ₐ[Λ] T, ∀ x, j (g x) = f x := by
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩
  have := congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)
  exact this

/- English proof (translation)
Introduce `O Γ _ _ _ Φ Λ _ _ a Y Q hQ`. Use `haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1`. Use `haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit`. Take `⟨h1, h2⟩` from `sxResLift Q hQ`. Take `⟨f, hf⟩` from `Y.univ _ _ _ h1 h2`.

Set `j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ)` to `{ (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with commutes' := fun x => by`. Simplify using `[Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }`. Establish `hj : Function.Injective j` using `Polynomial.coe_injective _`. Establish `hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ))` using `hf`. Establish `hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l)` using `fun g i l => congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'`.

Establish `hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l)` using `fun v i l => congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'`. Establish `hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B)`. Use `Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)` and prove the remaining obligations. Use `show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))`. Rewrite using `[← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red, ← Matrix.charpoly_map]`.

Establish `e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ))` using `by ext1 i l`. Conclude with `hr g i l`. Rewrite using `[e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]`. Simplify using `[Polynomial.map_prod]`. Use `show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))`.

Rewrite using `[Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf', (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]`. Both sides reduce to the same expression. Establish `hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b))` using `fun b => DFunLike.congr_fun hB b`. Establish `hrange : ∀ x, f x ∈ j.range`. Introduce `x`.

Establish `hx : x ∈ Algebra.adjoin Y.B _` using `Y.gen ▸ Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨y, rfl⟩ | ⟨y, rfl⟩` into its components or cases. Conclude with `⟨_, (hr _ _ _).symm⟩`.

Conclude with `⟨_, (hn _ _ _).symm⟩`. Consider the case `algebraMap b => exact ⟨_, (hB' b).symm⟩`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`. Take `⟨g, hg⟩` from `preLine_desc f j hj hrange`. Use `⟨g, ?_, fun b hb => hj ?_⟩` and prove the remaining obligations. Use `PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)` and prove the remaining obligations. Conclude with `(hg _).trans (hr s i l)`.

Conclude with `(hg _).trans (hn v i l)`. Rewrite using `[hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]`.
-/
theorem UpperTheory.V.Ws.sxPreLine :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Y.Line := by
  intro O Γ _ _ _ Φ Λ _ _ a Y Q hQ
  haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit
  obtain ⟨h1, h2⟩ := sxResLift Q hQ
  obtain ⟨f, hf⟩ := Y.univ _ _ _ h1 h2
  let j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ) :=
    { (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with
      commutes' := fun x => by
        simp [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }
  have hj : Function.Injective j := Polynomial.coe_injective _
  have hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := hf
  have hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l) := fun g i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'
  have hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l) := fun v i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'
  have hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B) := by
    refine Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) =
        (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))
      rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red,
        ← Matrix.charpoly_map]
      have e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := by
        ext1 i l
        exact hr g i l
      rw [e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]
      simp [Polynomial.map_prod]
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))
      rw [Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf',
        (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]
      rfl
  have hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b)) := fun b => DFunLike.congr_fun hB b
  have hrange : ∀ x, f x ∈ j.range := by
    intro x
    have hx : x ∈ Algebra.adjoin Y.B _ := Y.gen ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨_, (hr _ _ _).symm⟩
      · exact ⟨_, (hn _ _ _).symm⟩
    | algebraMap b => exact ⟨_, (hB' b).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨g, hg⟩ := preLine_desc f j hj hrange
  refine ⟨g, ?_, fun b hb => hj ?_⟩
  · refine PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)
    · exact (hg _).trans (hr s i l)
    · exact (hg _).trans (hn v i l)
  · rw [hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]
