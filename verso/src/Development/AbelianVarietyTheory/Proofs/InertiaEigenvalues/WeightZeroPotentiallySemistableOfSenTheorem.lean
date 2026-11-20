import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInertiaImpliesPotSemistableProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PMon

/- English proof (translation)
Unfold `fr`. Rewrite using `[pow_zero]`. Both sides reduce to the same expression.
-/
theorem fr_zero_apply (l : ℕ) [Fact l.Prime] (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  unfold fr
  rw [pow_zero]
  rfl

/- English proof (translation)
Introduce `l _ P AI T n _ _ K r ρ hρ hF`. Take `⟨ρ₀, p, hc₀, hp, hρ₀⟩` from `GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates l n K r ρ hρ`. Take `⟨S, θ, hS, -, -, hθΩ, hθg⟩` from `GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T`. Use `choose U hU hUg using hF`. Establish `hΩ : ∀ y : Om l, algebraMap (Om l) P.R.BdR y ∈ S` using `fun y => (hθΩ y).1`.

Establish `hkd : ∀ c : ↥(MaximalUnramifiedExtension l), kd P c ∈ S` using `fun c => hΩ _`. Set `kS : ↥(MaximalUnramifiedExtension l) →+* ↥S` to `(kd P).codRestrict S hkd`. Set `Φ` to `(kd P).mapMatrix (m := n × Fin r)`. Set `ΦS` to `kS.mapMatrix (m := n × Fin r)`. Set `ιS` to `S.subtype.mapMatrix (m := n × Fin r)`.

Establish `hinj : Function.Injective ιS` using `Matrix.map_injective Subtype.val_injective`. Establish `hιΦ : ∀ A, ιS (ΦS A) = Φ A` using `fun A => by ext i j; rfl`. Establish `hpp : Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hpp' : Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hfix : ∀ g : ↥(GK K), (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (Φ p) = Φ p`. Introduce `g`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Φ]`.

Establish `hK : ((((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) ∈ K.1` using `hρ.le _ (hp i j)`. Establish `hg` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ hK`. Use `show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR _) = algebraMap (Om l) P.R.BdR _`. Rewrite using `[P.actQdR_Om]`. Conclude with `congrArg _ hg`.

Set `Ut : Matrix (n × Fin r) (n × Fin r) P.R.BdR` to `Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR)`. Set `Ut' : Matrix (n × Fin r) (n × Fin r) P.R.BdR` to `Matrix.blockDiagonal fun m => ((U m)⁻¹ : GL n P.R.BdR)`. Establish `hUU : Ut * Ut' = 1`. Simplify using `only [Ut, Ut']`. Rewrite using `[← Matrix.blockDiagonal_mul]`.

Establish `: (fun m => (U m : Matrix n n P.R.BdR) * ((U m)⁻¹ : GL n P.R.BdR)) = fun _ => 1`. Use function extensionality and compare the values at `m`. Conclude with `Units.mul_inv (U m)`. Rewrite using `[this]`. Conclude with `Matrix.blockDiagonal_one`.

Set `US : Fin r → Matrix n n ↥S` to `fun m => Matrix.of fun i j => ⟨(U m : Matrix n n P.R.BdR) i j, (hS _).2 ((hU m).1 i j)⟩`. Set `VS : Fin r → Matrix n n ↥S` to `fun m => Matrix.of fun i j => ⟨((U m)⁻¹ : GL n P.R.BdR) i j, (hS _).2 ((hU m).2 i j)⟩`. Set `XS` to `ΦS ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Matrix.blockDiagonal US`. Set `YS` to `Matrix.blockDiagonal VS * ΦS (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))`. Establish `hX : ιS XS = Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Ut`.

Simplify using `only [XS, map_mul, hιΦ]`. Use `congr 1`. Simplify using `only [ιS, RingHom.mapMatrix_apply, Ut]`. Rewrite using `[Matrix.blockDiagonal_map _ _ (by simp)]`. Both sides reduce to the same expression.

Establish `hY : ιS YS = Ut' * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))`. Simplify using `only [YS, map_mul, hιΦ]`. Use `congr 1`. Simplify using `only [ιS, RingHom.mapMatrix_apply, Ut']`. Rewrite using `[Matrix.blockDiagonal_map _ _ (by simp)]`.

Both sides reduce to the same expression. Establish `hXY : XS * YS = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hX, hY, map_one, mul_assoc, ← mul_assoc Ut, hUU, one_mul, hpp']`. Establish `hmain : ∀ g : ↥(GK K), Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) * (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) = ιS XS`.

Introduce `g`. Use `set Ψ := (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (m := n × Fin r)`. Use `set pk := Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))`. Use `set pki := Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))`. Use `set R₀ := Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)))`.

Use `set Dk := Φ (Matrix.blockDiagonal fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))`. Establish `hW : pk * R₀ = Dk * pk`. Simplify using `only [pk, R₀, Dk, ← map_mul, hρ₀ g]`. Establish `hD : Dk * Ψ Ut = Ut`. Establish `h1 : Dk = Matrix.blockDiagonal fun m : Fin r => matD P ρ m g`.

Simplify using `only [Dk, Φ, RingHom.mapMatrix_apply]`. Rewrite using `[Matrix.blockDiagonal_map _ _ (by simp)]`. Both sides reduce to the same expression. Establish `h2 : Ψ Ut = Matrix.blockDiagonal fun m : Fin r => (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l))`. Simplify using `only [Ψ, Ut, RingHom.mapMatrix_apply]`.

Rewrite using `[Matrix.blockDiagonal_map _ _ (by simp)]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, ← Matrix.blockDiagonal_mul]`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Rewrite using `[hUg m g]`. Simplify using the standard rewrite rules. Establish `hΨpki : Ψ pki = pki`. Establish `hΨp : Ψ pk = pk` using `hfix g`. Combine the equalities or inequalities in the displayed calculation.

Establish `hR : R₀ = pki * Dk * pk`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hX, map_mul, hΨpki, hR]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc pk pki, hpp, one_mul]`. Use `_ = pki * Ut := by rw [hD]`. Set `actS : GQ l → ↥S → ↥S` to `fun g x => ⟨P.actQdR g x, (hθg g x).1⟩`. Set `qS : ℚ_[l] → ↥S` to `fun q => kS (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)`. Establish `hES : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS * XS.map (actS (g : GQ l)) = XS`.

Introduce `g`. Apply `hinj` to reduce the goal to its premises. Establish `e1 : ιS ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) = Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)))` using `by ext i j; rfl`. Establish `e2 : ιS (XS.map (actS (g : GQ l))) = (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[map_mul, e1, e2]`. Conclude with `hmain g`. Set `Θ` to `θ.mapMatrix (m := n × Fin r)`. Establish `hMM : Θ XS * Θ YS = 1` using `by rw [← map_mul, hXY, map_one]`.

Apply the tactic sequence `let Mu : GL (n × Fin r) ℂ_[l] := ⟨Θ XS, Θ YS, hMM, (by first | exact mul_eq_one_comm.mp hMM | exact Matrix.mul_eq_one_comm.1 hMM)⟩`. Establish `hSen : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Mu`. Introduce `g`. Establish `h1 : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) = Θ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS)`. Use extensionality with `i j`.

Simplify using `only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `(hθΩ (((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j)) : ↥(MaximalUnramifiedExtension l)) : Om l)).2` as an intermediate fact. Conclude with `this.symm`. Establish `h2 : (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Θ (XS.map (actS (g : GQ l)))`. Use extensionality with `i j`.

Simplify using `only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `((hθg (g : GQ l) (XS i j)).2).symm`. Rewrite using `[h1, h2, ← map_mul, hES g]`. Establish `hfin₀` using `GlobalTheory.T.sen_admissible_representation_finite_inertia l (n × Fin r) K ρ₀ hc₀ Mu hSen`. Establish `hr : 0 < r` using `hρ.pos`.

Set `z : Fin r` to `⟨0, hr⟩`. Set `F : GL (n × Fin r) ℚ_[l] → Matrix n n ↥(MaximalUnramifiedExtension l)` to `fun A => Matrix.of fun i j => ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (A : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) * ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) ( …`. Establish `hFρ : ∀ g, F (ρ₀ g) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))`. Introduce `g`. Use extensionality with `i j`.

Simplify using `only [F, Matrix.of_apply]`. Rewrite using `[hρ₀ g, mul_assoc, Units.mul_inv, mul_one, Matrix.blockDiagonal_apply_eq, Matrix.map_apply]`. Conclude with `congrArg Subtype.val (fr_zero_apply l ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j))`. Establish `hfin : (ρ '' (IK K : Set ↥(GK K))).Finite`. Establish `h1 : ((fun A : GL n ↥(MaximalUnramifiedExtension l) => (A : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (ρ '' (IK K : Set ↥(GK K)))).Finite`.

Rewrite using `[Set.image_image]`. Establish `: (fun g => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (IK K : Set ↥(GK K)) = F '' (ρ₀ '' (IK K : Set ↥(GK K)))`. Rewrite using `[Set.image_image]`. Simplify using `only [hFρ]`. Rewrite using `[this]`.

Conclude with `hfin₀.image F`. Conclude with `Set.Finite.of_finite_image h1 (fun a _ b _ h => Units.ext h)`. Conclude with `GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof l P AI T n K r ρ hρ hfin`.
-/
theorem senStep : SenStep := by
  intro l _ P AI T n _ _ K r ρ hρ hF
  classical
  obtain ⟨ρ₀, p, hc₀, hp, hρ₀⟩ := GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates l n K r ρ hρ
  obtain ⟨S, θ, hS, -, -, hθΩ, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  choose U hU hUg using hF
  have hΩ : ∀ y : Om l, algebraMap (Om l) P.R.BdR y ∈ S := fun y => (hθΩ y).1
  have hkd : ∀ c : ↥(MaximalUnramifiedExtension l), kd P c ∈ S := fun c => hΩ _
  let kS : ↥(MaximalUnramifiedExtension l) →+* ↥S := (kd P).codRestrict S hkd
  let Φ := (kd P).mapMatrix (m := n × Fin r)
  let ΦS := kS.mapMatrix (m := n × Fin r)
  let ιS := S.subtype.mapMatrix (m := n × Fin r)
  have hinj : Function.Injective ιS := Matrix.map_injective Subtype.val_injective
  have hιΦ : ∀ A, ιS (ΦS A) = Φ A := fun A => by ext i j; rfl
  have hpp : Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpp' : Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]

  have hfix : ∀ g : ↥(GK K), (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (Φ p) = Φ p := by
    intro g
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Φ]
    have hK : ((((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) ∈ K.1 := hρ.le _ (hp i j)
    have hg := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ hK
    show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR _) = algebraMap (Om l) P.R.BdR _
    rw [P.actQdR_Om]
    exact congrArg _ hg

  let Ut : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR)
  let Ut' : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => ((U m)⁻¹ : GL n P.R.BdR)
  have hUU : Ut * Ut' = 1 := by
    simp only [Ut, Ut']
    rw [← Matrix.blockDiagonal_mul]
    have : (fun m => (U m : Matrix n n P.R.BdR) * ((U m)⁻¹ : GL n P.R.BdR)) = fun _ => 1 := by
      funext m; exact Units.mul_inv (U m)
    rw [this]
    exact Matrix.blockDiagonal_one
  let US : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j => ⟨(U m : Matrix n n P.R.BdR) i j, (hS _).2 ((hU m).1 i j)⟩
  let VS : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j =>
    ⟨((U m)⁻¹ : GL n P.R.BdR) i j, (hS _).2 ((hU m).2 i j)⟩
  let XS := ΦS ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Matrix.blockDiagonal US
  let YS := Matrix.blockDiagonal VS * ΦS (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
  have hX : ιS XS = Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Ut := by
    simp only [XS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut]
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hY : ιS YS = Ut' * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := by
    simp only [YS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut']
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hXY : XS * YS = 1 := by
    apply hinj
    rw [map_mul, hX, hY, map_one, mul_assoc, ← mul_assoc Ut, hUU, one_mul, hpp']

  have hmain : ∀ g : ↥(GK K),
      Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) *
        (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) = ιS XS := by
    intro g
    set Ψ := (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (m := n × Fin r)
    set pk := Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set pki := Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set R₀ := Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)))
    set Dk := Φ (Matrix.blockDiagonal fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
    have hW : pk * R₀ = Dk * pk := by
      simp only [pk, R₀, Dk, ← map_mul, hρ₀ g]
    have hD : Dk * Ψ Ut = Ut := by
      have h1 : Dk = Matrix.blockDiagonal fun m : Fin r => matD P ρ m g := by
        simp only [Dk, Φ, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      have h2 : Ψ Ut = Matrix.blockDiagonal fun m : Fin r => (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
        simp only [Ψ, Ut, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      rw [h1, h2, ← Matrix.blockDiagonal_mul]
      congr 1
      funext m
      rw [hUg m g]
      simp
    have hΨpki : Ψ pki = pki := by
      have hΨp : Ψ pk = pk := hfix g
      calc Ψ pki = Ψ pki * (pk * pki) := by rw [hpp, mul_one]
        _ = Ψ (pki * pk) * pki := by rw [map_mul, hΨp, mul_assoc]
        _ = pki := by rw [hpp', map_one, one_mul]
    have hR : R₀ = pki * Dk * pk := by
      calc R₀ = pki * (pk * R₀) := by rw [← mul_assoc, hpp', one_mul]
        _ = pki * Dk * pk := by rw [hW, mul_assoc]
    rw [hX, map_mul, hΨpki, hR]
    calc pki * Dk * pk * (pki * Ψ Ut) = pki * (Dk * Ψ Ut) := by
          simp only [mul_assoc]
          rw [← mul_assoc pk pki, hpp, one_mul]
      _ = pki * Ut := by rw [hD]

  let actS : GQ l → ↥S → ↥S := fun g x => ⟨P.actQdR g x, (hθg g x).1⟩
  let qS : ℚ_[l] → ↥S := fun q => kS (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hES : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS * XS.map (actS (g : GQ l)) = XS := by
    intro g
    apply hinj
    have e1 : ιS ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) =
        Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) := by ext i j; rfl
    have e2 : ιS (XS.map (actS (g : GQ l))) = (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) := by
      ext i j; rfl
    rw [map_mul, e1, e2]
    exact hmain g
  let Θ := θ.mapMatrix (m := n × Fin r)
  have hMM : Θ XS * Θ YS = 1 := by rw [← map_mul, hXY, map_one]
  let Mu : GL (n × Fin r) ℂ_[l] := ⟨Θ XS, Θ YS, hMM, (by first | exact mul_eq_one_comm.mp hMM | exact Matrix.mul_eq_one_comm.1 hMM)⟩
  have hSen : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Mu := by
    intro g
    have h1 : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) =
        Θ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      have := (hθΩ (((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j)) : ↥(MaximalUnramifiedExtension l)) : Om l)).2
      exact this.symm
    have h2 : (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Θ (XS.map (actS (g : GQ l))) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact ((hθg (g : GQ l) (XS i j)).2).symm
    rw [h1, h2, ← map_mul, hES g]
  have hfin₀ := GlobalTheory.T.sen_admissible_representation_finite_inertia l (n × Fin r) K ρ₀ hc₀ Mu hSen

  have hr : 0 < r := hρ.pos
  let z : Fin r := ⟨0, hr⟩
  let F : GL (n × Fin r) ℚ_[l] → Matrix n n ↥(MaximalUnramifiedExtension l) := fun A => Matrix.of fun i j =>
    ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (A : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) *
      ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) (i, z) (j, z)
  have hFρ : ∀ g, F (ρ₀ g) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
    intro g
    ext i j
    simp only [F, Matrix.of_apply]
    rw [hρ₀ g, mul_assoc, Units.mul_inv, mul_one, Matrix.blockDiagonal_apply_eq, Matrix.map_apply]
    exact congrArg Subtype.val (fr_zero_apply l ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j))
  have hfin : (ρ '' (IK K : Set ↥(GK K))).Finite := by
    have h1 : ((fun A : GL n ↥(MaximalUnramifiedExtension l) => (A : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (ρ '' (IK K : Set ↥(GK K)))).Finite := by
      rw [Set.image_image]
      have : (fun g => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (IK K : Set ↥(GK K)) = F '' (ρ₀ '' (IK K : Set ↥(GK K))) := by
        rw [Set.image_image]
        simp only [hFρ]
      rw [this]
      exact hfin₀.image F
    exact Set.Finite.of_finite_image h1 (fun a _ b _ h => Units.ext h)
  exact GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof l P AI T n K r ρ hρ hfin

end GlobalTheory.PMon
