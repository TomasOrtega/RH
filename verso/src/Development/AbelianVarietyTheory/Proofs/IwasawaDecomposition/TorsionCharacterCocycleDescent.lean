import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalEqOfMultiplicativeOnPoints

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LineNorm

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis R B`. Establish `h1 : ∀ σ : B →ₐ[R] R, TensorProduct.lid R B (σ.toLinearMap.rTensor B s) = 0`. Introduce `σ`. Use `inj _ fun τ => ?_` and prove the remaining obligations. Rewrite using `[← h σ τ]`.

Use `clear h`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Establish `h2 : ∀ f : B →ₗ[R] R, TensorProduct.rid R B (f.lTensor B s) = 0`. Introduce `f`. Use `inj _ fun σ => ?_` and prove the remaining obligations. Establish `: σ (TensorProduct.rid R B (f.lTensor B s)) = f (TensorProduct.lid R B (σ.toLinearMap.rTensor B s))` using `by clear h h1`. Proceed by induction on `s using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [mul_comm]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[this, h1, map_zero]`. Use `(Algebra.TensorProduct.basis B e).ext_elem fun i => ?_` and prove the remaining obligations.

Establish `: (Algebra.TensorProduct.basis B e).repr s i = TensorProduct.rid R B ((e.coord i).lTensor B s)` using `by clear h h1 h2`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Algebra.smul_def, mul_comm]`. Consider the case `add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]`.

Rewrite using `[this, h2]`. Simplify using the standard rewrite rules.
-/
theorem tensor_eq_zero_of_sections {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Module.Free R B]
    (inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0) (s : B ⊗[R] B)
    (h : ∀ σ τ : B →ₐ[R] R, Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _) s = 0) : s = 0 := by
  classical
  let e := Module.Free.chooseBasis R B
  have h1 : ∀ σ : B →ₐ[R] R, TensorProduct.lid R B (σ.toLinearMap.rTensor B s) = 0 := by
    intro σ
    refine inj _ fun τ => ?_
    rw [← h σ τ]
    clear h
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ f : B →ₗ[R] R, TensorProduct.rid R B (f.lTensor B s) = 0 := by
    intro f
    refine inj _ fun σ => ?_
    have : σ (TensorProduct.rid R B (f.lTensor B s)) = f (TensorProduct.lid R B (σ.toLinearMap.rTensor B s)) := by
      clear h h1
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mul_comm]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [this, h1, map_zero]
  refine (Algebra.TensorProduct.basis B e).ext_elem fun i => ?_
  have : (Algebra.TensorProduct.basis B e).repr s i = TensorProduct.rid R B ((e.coord i).lTensor B s) := by
    clear h h1 h2
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.smul_def, mul_comm]
    | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
  rw [this, h2]
  simp

/- English proof (translation)
Set `C` to `FractionRing R`. Establish `hinj : Function.Injective (algebraMap R C)` using `IsFractionRing.injective R C`. Set `j : (B →ₐ[R] R) → (B →ₐ[R] C)` to `fun σ => (Algebra.ofId R C).comp σ`. Establish `hj : Function.Injective j` using `fun σ τ h => AlgHom.ext fun b => hinj (AlgHom.congr_fun h b)`. Take `⟨d, a, hd, ha⟩` from `GlobalTheory.exists_smul_fun_eq_eval_points R C B (Function.extend j (fun σ => algebraMap R C (κ σ)) 0)`.

Establish `ha' : ∀ σ : B →ₐ[R] R, σ a = d * κ σ`. Introduce `σ`. Apply `hinj` to reduce the goal to its premises. Use `ha (j σ)` as an intermediate fact. Rewrite `this` using `[hj.extend_apply]`.

Rewrite using `[map_mul, ← this]`. Both sides reduce to the same expression. Establish `hε : ε a = d` using `by rw [ha', hone, mul_one]`. Establish `hΔ : d • Δ a = a ⊗ₜ a`. Rewrite using `[← sub_eq_zero]`.

Use `tensor_eq_zero_of_sections inj _ fun σ τ => ?_` and prove the remaining obligations. Establish `h1` using `ha' ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)`. Rewrite `h1` using `[hmul, AlgHom.comp_apply]`. Rewrite using `[map_sub, map_smul, h1, Algebra.TensorProduct.lift_tmul, ha', ha', smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ f : B →ₗ[R] R, d ∣ f a`. Introduce `f`. Use `GlobalTheory.dvd_of_smul_apply_eq_smul R C B ((TensorProduct.rid R B).toLinearMap ∘ₗ f.lTensor B ∘ₗ Δ.toLinearMap) ε.toLinearMap d (f a) a hd (by simpa [hε] using hd) ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]`. Rewrite using `[← map_smul, ← map_smul, hΔ]`.

Simplify using the standard rewrite rules. Set `e` to `Module.Free.chooseBasis R B`. Use `choose g hg using fun i => key (e.coord i)`. Establish `hb : a = d • ∑ i, g i • e i` using `by conv_lhs => rw [← e.sum_repr a]`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_smul, ← hg i, Module.Basis.coord_apply]`. Establish `hv : ∀ σ : B →ₐ[R] R, σ (∑ i, g i • e i) = κ σ` using `fun σ => mul_left_cancel₀ hd (by rw [← ha', ← smul_eq_mul, ← map_smul, ← hb])`. Use `⟨∑ i, g i • e i, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `tensor_eq_zero_of_sections inj _ fun σ τ => ?_` and prove the remaining obligations. Establish `h1` using `hv ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)`. Rewrite `h1` using `[hmul, AlgHom.comp_apply]`. Rewrite using `[map_sub, h1, Algebra.TensorProduct.lift_tmul, hv, hv, sub_self]`.
-/
theorem exists_groupLike_of_sections {R B : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Module.Free R B]
    (inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0) (Δ : B →ₐ[R] B ⊗[R] B) (ε : B →ₐ[R] R)
    (κ : (B →ₐ[R] R) → R)
    (hmul : ∀ σ τ : B →ₐ[R] R,
      κ ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ) = κ σ * κ τ)
    (hone : κ ε = 1) : ∃ b : B, (∀ σ : B →ₐ[R] R, σ b = κ σ) ∧ Δ b = b ⊗ₜ b := by
  classical
  let C := FractionRing R
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  let j : (B →ₐ[R] R) → (B →ₐ[R] C) := fun σ => (Algebra.ofId R C).comp σ
  have hj : Function.Injective j := fun σ τ h => AlgHom.ext fun b => hinj (AlgHom.congr_fun h b)
  obtain ⟨d, a, hd, ha⟩ := GlobalTheory.exists_smul_fun_eq_eval_points R C B
    (Function.extend j (fun σ => algebraMap R C (κ σ)) 0)
  have ha' : ∀ σ : B →ₐ[R] R, σ a = d * κ σ := by
    intro σ
    apply hinj
    have := ha (j σ)
    rw [hj.extend_apply] at this
    rw [map_mul, ← this]
    rfl
  have hε : ε a = d := by rw [ha', hone, mul_one]
  have hΔ : d • Δ a = a ⊗ₜ a := by
    rw [← sub_eq_zero]
    refine tensor_eq_zero_of_sections inj _ fun σ τ => ?_
    have h1 := ha' ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)
    rw [hmul, AlgHom.comp_apply] at h1
    rw [map_sub, map_smul, h1, Algebra.TensorProduct.lift_tmul, ha', ha', smul_eq_mul]
    ring
  have key : ∀ f : B →ₗ[R] R, d ∣ f a := by
    intro f
    refine GlobalTheory.dvd_of_smul_apply_eq_smul R C B
      ((TensorProduct.rid R B).toLinearMap ∘ₗ f.lTensor B ∘ₗ Δ.toLinearMap) ε.toLinearMap d (f a) a
      hd (by simpa [hε] using hd) ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
    rw [← map_smul, ← map_smul, hΔ]
    simp
  let e := Module.Free.chooseBasis R B
  choose g hg using fun i => key (e.coord i)
  have hb : a = d • ∑ i, g i • e i := by
    conv_lhs => rw [← e.sum_repr a]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_smul, ← hg i, Module.Basis.coord_apply]
  have hv : ∀ σ : B →ₐ[R] R, σ (∑ i, g i • e i) = κ σ := fun σ =>
    mul_left_cancel₀ hd (by rw [← ha', ← smul_eq_mul, ← map_smul, ← hb])
  refine ⟨∑ i, g i • e i, hv, ?_⟩
  rw [← sub_eq_zero]
  refine tensor_eq_zero_of_sections inj _ fun σ τ => ?_
  have h1 := hv ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)
  rw [hmul, AlgHom.comp_apply] at h1
  rw [map_sub, h1, Algebra.TensorProduct.lift_tmul, hv, hv, sub_self]

end GlobalTheory.LineNorm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Set `p : ∀ _ : B →ₐ[R] B ⊗[R] B, (Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x) ⟶ Over.mk (spMap (algebraMap R B) ≫ x))` to `fun i => Over.homMk (spMap i.toRingHom) (by`. Simplify using `only [Over.mk_left, Over.mk_hom]`. Rewrite using `[← Category.assoc, sp_comp]`. Use `congr 2`. Conclude with `i.comp_algebraMap)`.

Set `i₁ : B →ₐ[R] B ⊗[R] B` to `Algebra.TensorProduct.includeLeft (S := R)`. Set `i₂ : B →ₐ[R] B ⊗[R] B` to `Algebra.TensorProduct.includeRight`. Take `⟨δ, hδ, hδ'⟩` from `hu.mul _ _ (p i₁ ≫ u) (p i₂ ≫ u) ⟨i₁.toRingHom, i₁.comp_algebraMap, rfl⟩ ⟨i₂.toRingHom, i₂.comp_algebraMap, rfl⟩`. Use `⟨⟨δ, fun r => RingHom.congr_fun hδ r⟩, ?_⟩` and prove the remaining obligations. Introduce `S _ φ w w' ν hν h1 h2`.

Set `g : Over.mk (spMap φ ≫ x) ⟶ Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x)` to `Over.homMk (spMap ν) (by`. Simplify using `only [Over.mk_left, Over.mk_hom]`. Rewrite using `[← Category.assoc, sp_comp, hν])`. Establish `e1 : w = g ≫ p i₁ ≫ u` using `by ext1`. Rewrite using `[← h1, ← sp_comp, Category.assoc]`.

Both sides reduce to the same expression. Establish `e2 : w' = g ≫ p i₂ ≫ u` using `by ext1`. Rewrite using `[← h2, ← sp_comp, Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, ← MonObj.comp_mul, ← sp_comp, Category.assoc, Over.comp_left, ← hδ']`.

Both sides reduce to the same expression.
-/
theorem IsFinPart.exists_comul {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X}
    {q : ℕ} {B : Type} [CommRing B] [Algebra R B] {u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G}
    (hu : IsFinPart t x q u) : ∃ Δ : B →ₐ[R] B ⊗[R] B,
      ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (ν : B ⊗[R] B →+* S),
        ν.comp (algebraMap R (B ⊗[R] B)) = φ →
        spMap (ν.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom) ≫ u.left = w.left →
        spMap (ν.comp (Algebra.TensorProduct.includeRight).toRingHom) ≫ u.left = w'.left →
        spMap (ν.comp Δ.toRingHom) ≫ u.left = (w * w').left := by
  let p : ∀ _ : B →ₐ[R] B ⊗[R] B, (Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R B) ≫ x)) := fun i =>
    Over.homMk (spMap i.toRingHom) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp]
      congr 2
      exact i.comp_algebraMap)
  let i₁ : B →ₐ[R] B ⊗[R] B := Algebra.TensorProduct.includeLeft (S := R)
  let i₂ : B →ₐ[R] B ⊗[R] B := Algebra.TensorProduct.includeRight
  obtain ⟨δ, hδ, hδ'⟩ := hu.mul _ _ (p i₁ ≫ u) (p i₂ ≫ u) ⟨i₁.toRingHom, i₁.comp_algebraMap, rfl⟩
    ⟨i₂.toRingHom, i₂.comp_algebraMap, rfl⟩
  refine ⟨⟨δ, fun r => RingHom.congr_fun hδ r⟩, ?_⟩
  intro S _ φ w w' ν hν h1 h2
  let g : Over.mk (spMap φ ≫ x) ⟶ Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x) :=
    Over.homMk (spMap ν) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp, hν])
  have e1 : w = g ≫ p i₁ ≫ u := by
    ext1
    rw [← h1, ← sp_comp, Category.assoc]
    rfl
  have e2 : w' = g ≫ p i₂ ≫ u := by
    ext1
    rw [← h2, ← sp_comp, Category.assoc]
    rfl
  rw [e1, e2, ← MonObj.comp_mul, ← sp_comp, Category.assoc, Over.comp_left, ← hδ']
  rfl

/- English proof (translation)
Introduce `E _ _ _ H X t R _ _ _ x q B _ _ u hu κ hκ`. Use `haveI := hu.finite`. Use `haveI := hu.free`. Take `⟨Δ, hΔ⟩` from `hu.exists_comul`. Take `⟨ε₀, hε, hε'⟩` from `hu.one R (RingHom.id R)`.

Set `ε : B →ₐ[R] R` to `⟨ε₀, fun r => RingHom.congr_fun hε r⟩`. Establish `hone : κ ε = 1`. Use `hκ ε ε ε 1 1 hε' hε' (by rw [_root_.mul_one]; exact hε')` as an intermediate fact. Conclude with `left_eq_mul.mp this`. Set `p : ∀ _ : B →ₐ[R] R, (Over.mk (spMap (RingHom.id R) ≫ x) ⟶ Over.mk (spMap (algebraMap R B) ≫ x))` to `fun i => Over.homMk (spMap i.toRingHom) (by`.

Simplify using `only [Over.mk_left, Over.mk_hom]`. Rewrite using `[← Category.assoc, sp_comp]`. Use `congr 2`. Conclude with `i.comp_algebraMap)`. Establish `hmul : ∀ σ τ : B →ₐ[R] R, κ ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ) = κ σ * κ τ`.

Introduce `σ τ`. Use `hκ σ τ _ (p σ ≫ u) (p τ ≫ u) rfl rfl ?_` and prove the remaining obligations. Use `hΔ R (RingHom.id R) _ _ (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).toRingHom (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp_algebraMap ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = spMap σ.toRingHom ≫ u.left`. Use `congr 2`.

Use extensionality with `b`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `_ = spMap τ.toRingHom ≫ u.left`. Use `congr 2`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Take `⟨b, hb, hb'⟩` from `exists_groupLike_of_sections hu.inj Δ ε (fun σ => (κ σ : R)) (fun σ τ => by simp only [hmul, Units.val_mul]) (by simp only [hone, Units.val_one])`. Take `⟨c, hc, -⟩` from `exists_groupLike_of_sections hu.inj Δ ε (fun σ => (((κ σ)⁻¹ : Rˣ) : R)) (fun σ τ => by simp only [hmul, mul_inv, Units.val_mul]) (by simp only [hone, inv_one, Units.val_one])`. Establish `hbc : b * c = 1`. Rewrite using `[← sub_eq_zero]`.

Use `hu.inj _ fun σ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, hb, hc, map_one, Units.mul_inv, sub_self]`. Use `⟨⟨b, c, hbc, by rw [_root_.mul_comm, hbc]⟩, hb, ?_⟩` and prove the remaining obligations. Introduce `S _ φ w w' β β' β'' h h' h'' k k' k''`. Use `letI : Algebra R S := φ.toAlgebra`.

Set `a : B →ₐ[R] S` to `⟨β, fun r => RingHom.congr_fun h r⟩`. Set `a' : B →ₐ[R] S` to `⟨β', fun r => RingHom.congr_fun h' r⟩`. Set `ν : B ⊗[R] B →ₐ[R] S` to `Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)`. Establish `h3` using `hΔ S φ w w' ν.toRingHom ν.comp_algebraMap (by rw [← k]; congr 2; ext y; simp [ν, a]) (by rw [← k']; congr 2; ext y; simp [ν, a'])`. Establish `h4 : β'' = ν.toRingHom.comp Δ.toRingHom` using `hu.mono S _ _ (h''.trans (ν.comp Δ).comp_algebraMap.symm) (k''.trans h3.symm)`.

Establish `h5 : β'' b = ν (Δ b)` using `by rw [h4]; rfl`. Express the relevant statement in the definitionally equal form `β'' b = β b * β' b`. Rewrite using `[h5, hb', Algebra.TensorProduct.lift_tmul]`. Both sides reduce to the same expression.
-/
theorem exists_groupLike_unit_of_isFinPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (x : Sp R ⟶ X) (q : ℕ) (B : Type) [CommRing B] [Algebra R B] (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), IsFinPart t x q u → ∀ κ : (B →ₐ[R] R) → Rˣ, (∀ (σ σ' σ'' : B →ₐ[R] R) (w w' : Over.mk (spMap (RingHom.id R) ≫ x) ⟶ t.G), spMap σ.toRingHom ≫ u.left = w.left → spMap σ'.toRingHom ≫ u.left = w'.left → spMap σ''.toRingHom ≫ u.left = (w * w').left → κ σ'' = κ σ * κ σ') → ∃ b : Bˣ, (∀ σ : B →ₐ[R] R, σ (b : B) = (κ σ : R)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (β β' β'' : B →+* S), β.comp (algebraMap R B) = φ → β'.comp (algebraMap R B) = φ → β''.comp (algebraMap R B) = φ → spMap β ≫ u.left = w.left → spMap β' ≫ u.left = w'.left → spMap β'' ≫ u.left = (w * w').left → β'' (b : B) = β (b : B) * β' (b : B) := by
  intro E _ _ _ H X t R _ _ _ x q B _ _ u hu κ hκ
  haveI := hu.finite
  haveI := hu.free
  obtain ⟨Δ, hΔ⟩ := hu.exists_comul
  obtain ⟨ε₀, hε, hε'⟩ := hu.one R (RingHom.id R)
  let ε : B →ₐ[R] R := ⟨ε₀, fun r => RingHom.congr_fun hε r⟩
  have hone : κ ε = 1 := by
    have := hκ ε ε ε 1 1 hε' hε' (by rw [_root_.mul_one]; exact hε')
    exact left_eq_mul.mp this
  let p : ∀ _ : B →ₐ[R] R, (Over.mk (spMap (RingHom.id R) ≫ x) ⟶
      Over.mk (spMap (algebraMap R B) ≫ x)) := fun i =>
    Over.homMk (spMap i.toRingHom) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp]
      congr 2
      exact i.comp_algebraMap)
  have hmul : ∀ σ τ : B →ₐ[R] R,
      κ ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ) = κ σ * κ τ := by
    intro σ τ
    refine hκ σ τ _ (p σ ≫ u) (p τ ≫ u) rfl rfl ?_
    refine hΔ R (RingHom.id R) _ _ (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).toRingHom
      (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp_algebraMap ?_ ?_
    · change _ = spMap σ.toRingHom ≫ u.left
      congr 2
      ext b
      simp
    · change _ = spMap τ.toRingHom ≫ u.left
      congr 2
      ext b
      simp
  obtain ⟨b, hb, hb'⟩ := exists_groupLike_of_sections hu.inj Δ ε (fun σ => (κ σ : R))
    (fun σ τ => by simp only [hmul, Units.val_mul]) (by simp only [hone, Units.val_one])
  obtain ⟨c, hc, -⟩ := exists_groupLike_of_sections hu.inj Δ ε (fun σ => (((κ σ)⁻¹ : Rˣ) : R))
    (fun σ τ => by simp only [hmul, mul_inv, Units.val_mul]) (by simp only [hone, inv_one, Units.val_one])
  have hbc : b * c = 1 := by
    rw [← sub_eq_zero]
    refine hu.inj _ fun σ => ?_
    rw [map_sub, map_mul, hb, hc, map_one, Units.mul_inv, sub_self]
  refine ⟨⟨b, c, hbc, by rw [_root_.mul_comm, hbc]⟩, hb, ?_⟩
  intro S _ φ w w' β β' β'' h h' h'' k k' k''
  letI : Algebra R S := φ.toAlgebra
  let a : B →ₐ[R] S := ⟨β, fun r => RingHom.congr_fun h r⟩
  let a' : B →ₐ[R] S := ⟨β', fun r => RingHom.congr_fun h' r⟩
  let ν : B ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
  have h3 := hΔ S φ w w' ν.toRingHom ν.comp_algebraMap
    (by rw [← k]; congr 2; ext y; simp [ν, a]) (by rw [← k']; congr 2; ext y; simp [ν, a'])
  have h4 : β'' = ν.toRingHom.comp Δ.toRingHom :=
    hu.mono S _ _ (h''.trans (ν.comp Δ).comp_algebraMap.symm) (k''.trans h3.symm)
  have h5 : β'' b = ν (Δ b) := by rw [h4]; rfl
  change β'' b = β b * β' b
  rw [h5, hb', Algebra.TensorProduct.lift_tmul]
  rfl

end GlobalTheory.LineNorm
