import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

/- English proof (translation)
Introduce `L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F`. Set `m : (Fin n → L) →ₗ[Ks] (Fin n → L')` to `{ toFun := fun x k => ι (x k) map_add' := fun x y => by funext k; simp map_smul' := fun c x => by`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }`. Establish `minj : Function.Injective m`.

Introduce `x y h`. Use function extensionality and compare the values at `k`. Conclude with `ι.injective (congrFun h k)`. Set `e` to `Submodule.equivMapOfInjective m minj F.WK`. Set `ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L'))` to `(Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))`.

Set `j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι)` to `fun σ' => { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1) map_add' := fun x y => by`. Simplify using `only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }`. Set `F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G` to `{ WK := F.WK.map m Pt := F.Pt nrm := fun lp y φ' => F.nrm lp y (e.symm φ') nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _ nrm_zero := fun lp y => by simp only [map_zero]; exact F.nrm_zero lp y nrm_add := fun lp y f g => by simp only [map_add]; exact F.nrm_add lp y _ _ nrm_smul : …`.

Use `⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩` and prove the remaining obligations. Introduce `σ' x`. Establish `hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L)`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x`. Use `conv_rhs => rw [hx]`. Simplify using `only [map_sum, map_smulₛₗ, RingHom.comp_apply]`. Introduce `x' show x' ∈ F.WK.map m ↔ _`. Rewrite using `[Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`.

Introduce `g`. Both sides reduce to the same expression. Introduce `g x show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _`. Use function extensionality and compare the values at `k`. Rewrite using `[Matrix.toLin'_apply]`.

Use `RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_mulVec]`. Conclude with `this.symm`. Introduce `lp y' y hy φ' φ hφ`. Establish `hyy : y' = y` using `eq_of_heq hy`.

Substitute `hyy` using the available equality. Use `show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ`. Establish `: φ' = e φ` using `Subtype.ext hφ`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`.
-/
theorem formsL_exists_baseChange_coordinates : ∀ {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L] [Algebra Ks L'] (ι : L →+* L'), (∀ y : Ks, ι (algebraMap Ks L y) = algebraMap Ks L' y) → ∀ (n : ℕ) (W : (L →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] (G : Type) [Group G] (F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G),
  ∃ F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G,
    (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
    (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
    (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
    (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
    F'.Pt = F.Pt ∧
    ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) → F'.nrm lp y' φ' = F.nrm lp y φ := by
  intro L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F
  let m : (Fin n → L) →ₗ[Ks] (Fin n → L') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  have minj : Function.Injective m := by
    intro x y h
    funext k
    exact ι.injective (congrFun h k)
  let e := Submodule.equivMapOfInjective m minj F.WK
  let ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L')) :=
    (Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp
      ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))
  let j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι) := fun σ' =>
    { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  let F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G :=
    { WK := F.WK.map m
      Pt := F.Pt
      nrm := fun lp y φ' => F.nrm lp y (e.symm φ')
      nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _
      nrm_zero := fun lp y => by simp only [map_zero]; exact F.nrm_zero lp y
      nrm_add := fun lp y f g => by simp only [map_add]; exact F.nrm_add lp y _ _
      nrm_smul := fun lp y a f => by simp only [map_smul]; exact F.nrm_smul lp y a _
      towKs := inferInstance
      ρ := ρ'
      chi := (Units.map ι.toMonoidHom).comp F.chi
      j := j' }
  refine ⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro σ' x
    have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x
    conv_rhs => rw [hx]
    simp only [map_sum, map_smulₛₗ, RingHom.comp_apply]
  · intro x'
    show x' ∈ F.WK.map m ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · intro g; rfl
  · intro g x
    show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _
    funext k
    rw [Matrix.toLin'_apply]
    have := RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k
    rw [LinearMap.toMatrix'_mulVec] at this
    exact this.symm
  · intro lp y' y hy φ' φ hφ
    have hyy : y' = y := eq_of_heq hy
    subst hyy
    show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ
    have : φ' = e φ := Subtype.ext hφ
    rw [this, LinearEquiv.symm_apply_apply]

end GlobalTheory
