import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

/- English proof (translation)
Set `k` to `AlgebraicClosure (IsLocalRing.ResidueField V)`. Set `g₀ : V →+* k` to `(algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)`. Use `haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _`. Establish `hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V`. Introduce `q`.

Establish `hq : q = IsLocalRing.closedPoint k` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[hq]`. Conclude with `IsLocalRing.comap_closedPoint g₀`. Take `⟨⟨x, σ⟩, h⟩` from `(Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)`. Rewrite `h` using `[Scheme.SpecToEquivOfField_symm_apply]`.

Establish `hx : x = y (IsLocalRing.closedPoint V)`. Set `q : Sp k` to `IsLocalRing.closedPoint k`. Establish `e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q` using `congrArg (fun g : Sp k ⟶ X => g q) h`. Rewrite `e` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply]`. Conclude with `e`.

Substitute `hx` using the available equality. Conclude with `⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩`.
-/
theorem exists_geomPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (y : Sp V ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : X.residueField (y (IsLocalRing.closedPoint V)) →+* k)
      (π : Sp k ⟶ Sp V), π ≫ y = spMap σ ≫ X.fromSpecResidueField (y (IsLocalRing.closedPoint V)) ∧
      ∀ q, π q = IsLocalRing.closedPoint V := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _
  have hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V := by
    intro q
    have hq : q = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hq]
    exact IsLocalRing.comap_closedPoint g₀
  obtain ⟨⟨x, σ⟩, h⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)
  rw [Scheme.SpecToEquivOfField_symm_apply] at h
  have hx : x = y (IsLocalRing.closedPoint V) := by
    let q : Sp k := IsLocalRing.closedPoint k
    have e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q := congrArg (fun g : Sp k ⟶ X => g q) h
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hx
  exact ⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩

/- English proof (translation)
Introduce and unpack `p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩`. Set `eK : K →+* FractionRing V` to `(IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom`. Establish `heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V)`. Use extensionality with `a`. Conclude with `(IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a`.

Set `kF : Sp (FractionRing V) ⟶ Sp V` to `spMap (algebraMap V (FractionRing V))`. Set `x' : Sp (FractionRing V) ⟶ Y₀` to `spMap eK ≫ x`. Establish `hk : kF = spMap eK ≫ spMap (algebraMap V K)`. Simplify using `only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `hxy' : kF ≫ y = x' ≫ s₀` using `by rw [hk, Category.assoc, hxy]; rfl`.

Establish `hxz' : kF ≫ z' = x' ≫ t₀` using `by rw [hk, Category.assoc, hxz]; rfl`. Take `⟨o, ⟨my⟩⟩` from `GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ`. Take `⟨oK, ⟨mK⟩⟩` from `GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o`. Establish `m1 : ObjMap oK M.univ (x' ≫ s₀)` using `hxy' ▸ GlobalTheory.UPel.HT.ObjMap.comp mK my`. Take `⟨n₀, -⟩` from `GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀`.

Establish `key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ → ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x')`. Introduce and unpack `σ rfl`. Conclude with `GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'`. Take `⟨oK', ⟨n₀'⟩⟩` from `key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])`. Take `⟨ψK, hψK, -⟩` from `ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x' o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ`.

Take `⟨o', m', ψ, hψV, -⟩` from `IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK`. Take `⟨z, ⟨hz, ⟨mz⟩⟩, -⟩` from `M.rep (Sp V) (y ≫ M.s) o'`. Take `⟨f, -, huniq⟩` from `M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'`. Establish `e1` using `huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMap.comp m' mz⟩⟩`. Establish `e2` using `huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc], ⟨GlobalTheory.UPel.HT.ObjMap.comp n₀' mt₀⟩⟩`.

Use `haveI : IsSeparated M.s := by`. Take `⟨n, i, hi, -, e⟩` from `M.qproj`. Establish `: IsSeparated (PSpace.str R n)`. Unfold `PSpace.str`. Use `infer_instance`.

Rewrite using `[← e]`. Use `infer_instance`. Use `haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩`. Take `⟨_, _⟩` from `GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)`. Use `haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))`.

Establish `hzz : z = z'` using `ext_of_isDominant kF (by rw [e1, ← e2, hxz'])`. Substitute `hzz` using the available equality. Take `⟨k, _, _, σ, π, hπ, hπc⟩` from `exists_geomPt_closedPoint V M.X y`. Use `⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩` and prove the remaining obligations. Rewrite using `[← hπ]`.

Take `⟨o₁, ⟨n⟩⟩` from `GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o`. Take `⟨o₁', ⟨n'⟩⟩` from `GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'`. Take `⟨ψ₁, hψ₁, -⟩` from `ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π o o' o₁ o₁' n n' ψ hψV`. Use `⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`.

Conclude with `⟨o₁, o₁', ψ₁, ⟨n.comp my⟩, ⟨n'.comp mz⟩, hψ₁⟩`.
-/
theorem exists_isogTarget_of_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  rintro p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  have hxz' : kF ≫ z' = x' ≫ t₀ := by rw [hk, Category.assoc, hxz]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMap.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ →
      ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x'
    o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', ψ, hψV, -⟩ := IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMap.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMap.comp n₀' mt₀⟩⟩
  haveI : IsSeparated M.s := by
    obtain ⟨n, i, hi, -, e⟩ := M.qproj
    have : IsSeparated (PSpace.str R n) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))
  have hzz : z = z' := ext_of_isDominant kF (by rw [e1, ← e2, hxz'])
  subst hzz
  obtain ⟨k, _, _, σ, π, hπ, hπc⟩ := exists_geomPt_closedPoint V M.X y
  refine ⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩
  rw [← hπ]
  obtain ⟨o₁, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o
  obtain ⟨o₁', ⟨n'⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'
  obtain ⟨ψ₁, hψ₁, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π
    o o' o₁ o₁' n n' ψ hψV
  refine ⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩
  rw [Category.assoc]
  exact ⟨o₁, o₁', ψ₁, ⟨n.comp my⟩, ⟨n'.comp mz⟩, hψ₁⟩

end GlobalTheory.UPel.HT.ES.CorrQF
