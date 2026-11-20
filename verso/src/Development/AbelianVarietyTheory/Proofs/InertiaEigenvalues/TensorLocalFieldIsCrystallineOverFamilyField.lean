import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocCrysU

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]`. Conclude with `congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm`.
-/
theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

/- English proof (translation)
Introduce `D hFo i r hr Xs w hw n hP k M hSub hM`. Take `⟨K', h, hN, hFi, hS, Sig, Fr, -, -, -, -, hx⟩` from `hP`. Take `⟨-, x₀, hx₀, j, hjinj, hjeq⟩` from `hSub`. Use `⟨K', h, ?_⟩` and prove the remaining obligations. Use `haveI := GlobalTheory.Pass.LocDirect.isTopRing i w hw`.

Establish `hcont` using `(GlobalTheory.Pass.FamCont.stepCont D i r hr x₀).1`. Establish `hc1 : Continuous (Br.loc D.nbr i w hw (rTwO D.nd i r x₀))` using `GlobalTheory.PotDual.continuous_loc D i w hw _ hcont`. Establish `hinc : Continuous (Subgroup.inclusion (GK_le h))` using `Continuous.subtype_mk continuous_subtype_val _`. Establish `hpc` using `(hx ⟨x₀, hx₀⟩).1`. Establish `hcr` using `((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hFi hS _ (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)))).2).1 hpc`.

Set `A₁` to `GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) hc1)`. Set `A₀` to `GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM)`. Set `f` to `Br.toLLK (D.nbr i w hw)`. Set `J` to `(LinearMap.toMatrix' j).map f`. Take `⟨jl, hjl⟩` from `LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hjinj)`.

Establish `hJl : ((LinearMap.toMatrix' jl).map f) * J = 1`. Rewrite using `[← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hjl, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero f) (map_one f)]`. Set `ι : A₀.V →ₗ[Br.LL D.nbr i w hw] A₁.V` to `Matrix.toLin' J`. Establish `hinj : Function.Injective ι`. Establish `e : ∀ z : Fin k → Br.LL D.nbr i w hw, ((LinearMap.toMatrix' jl).map f).mulVec (J.mulVec z) = z` using `fun z => by`.

Rewrite using `[Matrix.mulVec_mulVec, hJl, Matrix.one_mulVec]`. Introduce `u v huv`. Establish `huv' : J.mulVec u = J.mulVec v` using `huv`. Rewrite using `[← e u, ← e v, huv']`. Establish `hJeq : ∀ γ : GE D.nd, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ = mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j`.

Introduce `γ`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply, Matrix.toLin'_apply, hjeq]`.

Establish `h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)`. Introduce `g (x : Fin k → Br.LL D.nbr i w hw)`. Establish `hmat : J * Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g) = Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g) * J`. Rewrite using `[loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJeq]`. Establish `key : J.mulVec ((Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g)).mulVec x) = (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g)).mulVec (J.mulVec x)`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]`. Conclude with `key`. Establish `hU : ∀ g, ∀ u ∈ LinearMap.range ι, A₁.ρ g u ∈ LinearMap.range ι`. Introduce and unpack `g _ ⟨x, rfl⟩`. Conclude with `⟨A₀.ρ g x, h1 g x⟩`.

Set `A₂` to `A₁.quot (LinearMap.range ι) hU`. Establish `hF` using `hFo (D.nd.l i) K' (D.nbr i w hw).LL`. Conclude with `((hF.1 A₀ A₁ A₂ ι (LinearMap.range ι).mkQ h1 (fun _ _ => rfl) hinj (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm).1 hcr).1`.
-/
theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g), ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hFo i r hr Xs w hw n hP k M hSub hM
  obtain ⟨K', h, hN, hFi, hS, Sig, Fr, -, -, -, -, hx⟩ := hP
  obtain ⟨-, x₀, hx₀, j, hjinj, hjeq⟩ := hSub
  refine ⟨K', h, ?_⟩
  haveI := GlobalTheory.Pass.LocDirect.isTopRing i w hw
  have hcont := (GlobalTheory.Pass.FamCont.stepCont D i r hr x₀).1
  have hc1 : Continuous (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) :=
    GlobalTheory.PotDual.continuous_loc D i w hw _ hcont
  have hinc : Continuous (Subgroup.inclusion (GK_le h)) :=
    Continuous.subtype_mk continuous_subtype_val _

  have hpc := (hx ⟨x₀, hx₀⟩).1
  have hcr := ((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hFi hS
    _ (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)))).2).1 hpc
  let A₁ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) hc1)
  let A₀ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM)

  let f := Br.toLLK (D.nbr i w hw)
  let J := (LinearMap.toMatrix' j).map f
  obtain ⟨jl, hjl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hjinj)
  have hJl : ((LinearMap.toMatrix' jl).map f) * J = 1 := by
    rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hjl, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero f) (map_one f)]
  let ι : A₀.V →ₗ[Br.LL D.nbr i w hw] A₁.V := Matrix.toLin' J
  have hinj : Function.Injective ι := by
    have e : ∀ z : Fin k → Br.LL D.nbr i w hw, ((LinearMap.toMatrix' jl).map f).mulVec (J.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, hJl, Matrix.one_mulVec]
    intro u v huv
    have huv' : J.mulVec u = J.mulVec v := huv
    rw [← e u, ← e v, huv']
  have hJeq : ∀ γ : GE D.nd, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply, hjeq]
  have h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x) := by
    intro g (x : Fin k → Br.LL D.nbr i w hw)
    have hmat : J * Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g) =
        Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g) * J := by
      rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJeq]
    have key : J.mulVec ((Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g)).mulVec x) =
        (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g)).mulVec (J.mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
    exact key
  have hU : ∀ g, ∀ u ∈ LinearMap.range ι, A₁.ρ g u ∈ LinearMap.range ι := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A₀.ρ g x, h1 g x⟩
  let A₂ := A₁.quot (LinearMap.range ι) hU
  have hF := hFo (D.nd.l i) K' (D.nbr i w hw).LL
  exact ((hF.1 A₀ A₁ A₂ ι (LinearMap.range ι).mkQ h1 (fun _ _ => rfl) hinj (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm).1 hcr).1

end GlobalTheory.Pass.LocCrysU

end
