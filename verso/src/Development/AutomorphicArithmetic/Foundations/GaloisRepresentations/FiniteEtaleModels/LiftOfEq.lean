import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IdemCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bezout

set_option autoImplicit false

noncomputable section

open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Core

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

/- English proof (translation)
Use `Submodule.smul_induction_on hw ?_ ?_` and prove the remaining obligations. Introduce `c hc m _`. Take `⟨d, hd⟩` from `ha c hc`. Conclude with `⟨d • m, by rw [smul_smul, hd, mul_smul, Nat.cast_smul_eq_nsmul]⟩`. Introduce and unpack `x y ⟨z, hz⟩ ⟨z', hz'⟩`.

Conclude with `⟨z + z', by rw [smul_add, hz, hz', smul_add]⟩`.
-/
private theorem kill {a : A} {N : ℕ} {I : Ideal A} (ha : ∀ x ∈ I, (N : A) ∣ a * x) {w : M}
    (hw : w ∈ (I • ⊤ : Submodule A M)) : ∃ z : M, a • w = N • z := by
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro c hc m _
    obtain ⟨d, hd⟩ := ha c hc
    exact ⟨d • m, by rw [smul_smul, hd, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [smul_add, hz, hz', smul_add]⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ef_nsmul (EF : LinearMap.BilinForm ℤ M) (N : ℕ) (x y : M) :
    EF (N • x) y = (N : ℤ) * EF x y := by
  simp

/- English proof (translation)
Take `⟨d, rfl⟩` from `hc`. Rewrite using `[mul_smul, Nat.cast_smul_eq_nsmul, ef_nsmul]`. Conclude with `Dvd.intro _ rfl`.
-/
private theorem dvd_left (EF : LinearMap.BilinForm ℤ M) {N : ℕ} {c : A} (hc : (N : A) ∣ c) (x y : M) :
    (N : ℤ) ∣ EF (c • x) y := by
  obtain ⟨d, rfl⟩ := hc
  rw [mul_smul, Nat.cast_smul_eq_nsmul, ef_nsmul]
  exact Dvd.intro _ rfl

/- English proof (translation)
Use `alt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem skew (EF : LinearMap.BilinForm ℤ M) (alt : ∀ x, EF x x = 0) (x y : M) :
    EF x y = - EF y x := by
  have := alt (x + y)
  simp only [map_add, LinearMap.add_apply, alt] at this
  linarith

variable (bar : A ≃+* A) (EF : LinearMap.BilinForm ℤ M)

/- English proof (translation)
Establish `hee : (N : A) ∣ ε * bar ε` using `h3 _ h2`. Establish `hsq : (N : A) ∣ ε * ε - ε`. Take `⟨d, hd⟩` from `h3 _ h1`. Conclude with `⟨-d, by linear_combination -hd⟩`. Establish `cross : ∀ x y, (N : ℤ) ∣ EF (ε • g x) (bar ε • k y) - EF (ε • x) y`.

Introduce `x y`. Take `⟨z, hz⟩` from `kill h3 (hhg x)`. Establish `e1 : EF (ε • g x) (bar ε • k y) = EF (ε • ε • g x) (k y)` using `(adj ε _ _).symm`. Take `⟨a, ha⟩` from `hk (ε • ε • g x) y`. Establish `e2 : h (ε • ε • g x) = N • (ε • z) + (ε * ε - ε) • x + ε • x`.

Rewrite using `[map_smul, map_smul, smul_comm N ε z, ← hz]`. Use `module`. Take `⟨b, hb⟩` from `dvd_left EF hsq x y`. Rewrite `ha` using `[e2]`. Simplify using `only [map_add, LinearMap.add_apply, ef_nsmul] at ha`.

Rewrite using `[e1]`. Conclude with `⟨EF (ε • z) y + b - a, by linear_combination hb - ha⟩`. Take `⟨a₁, h₁⟩` from `dvd_left EF hee (g x) (g y)`. Take `⟨a₂, h₂⟩` from `dvd_left EF hee (k x) (k y)`. Take `⟨a₃, h₃⟩` from `cross x y`.

Take `⟨a₄, h₄⟩` from `cross y x`. Take `⟨a₅, h₅⟩` from `dvd_left EF h4 x y`. Establish `f₁ : EF (ε • g x) (ε • g y) = EF ((ε * bar ε) • g x) (g y)`. Rewrite using `[mul_comm, mul_smul, adj (bar ε), hbb]`. Establish `f₂ : EF (bar ε • k x) (bar ε • k y) = EF ((ε * bar ε) • k x) (k y)`.

Rewrite using `[mul_smul, adj ε]`. Establish `f₃ : EF (bar ε • k x) (ε • g y) = - EF (ε • g y) (bar ε • k x)` using `skew EF alt _ _`. Establish `f₄ : EF (ε • y) x = - EF (bar ε • x) y`. Rewrite using `[adj (bar ε), hbb]`. Conclude with `skew EF alt _ _`.

Establish `f₅ : EF ((ε + bar ε - 1) • x) y = EF (ε • x) y + EF (bar ε • x) y - EF x y`. Rewrite using `[sub_smul, add_smul, one_smul]`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[f₁, f₂, f₃, h₁, h₂]`.

Conclude with `⟨a₁ + a₂ + a₃ - a₄ + a₅, by linear_combination h₃ - h₄ + h₅ - f₅ - f₄⟩`.
-/
private theorem iso_step (hbb : ∀ c, bar (bar c) = c) (alt : ∀ x, EF x x = 0)
    (adj : ∀ (c : A) (x y : M), EF (c • x) y = EF x (bar c • y))
    (N : ℕ) (u : Ideal A) (ε : A) (g h : M →ₗ[A] M) (k : M →+ M)
    (h1 : 1 - ε ∈ u) (h2 : bar ε ∈ u) (h3 : ∀ x ∈ u, (N : A) ∣ ε * x) (h4 : (N : A) ∣ ε + bar ε - 1)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hk : ∀ x y, (N : ℤ) ∣ EF (h x) y - EF x (k y)) (x y : M) :
    (N : ℤ) ∣ EF (ε • g x + bar ε • k x) (ε • g y + bar ε • k y) - EF x y := by
  have hee : (N : A) ∣ ε * bar ε := h3 _ h2
  have hsq : (N : A) ∣ ε * ε - ε := by
    obtain ⟨d, hd⟩ := h3 _ h1
    exact ⟨-d, by linear_combination -hd⟩
  have cross : ∀ x y, (N : ℤ) ∣ EF (ε • g x) (bar ε • k y) - EF (ε • x) y := by
    intro x y
    obtain ⟨z, hz⟩ := kill h3 (hhg x)
    have e1 : EF (ε • g x) (bar ε • k y) = EF (ε • ε • g x) (k y) := (adj ε _ _).symm
    obtain ⟨a, ha⟩ := hk (ε • ε • g x) y
    have e2 : h (ε • ε • g x) = N • (ε • z) + (ε * ε - ε) • x + ε • x := by
      rw [map_smul, map_smul, smul_comm N ε z, ← hz]
      module
    obtain ⟨b, hb⟩ := dvd_left EF hsq x y
    rw [e2] at ha
    simp only [map_add, LinearMap.add_apply, ef_nsmul] at ha
    rw [e1]
    exact ⟨EF (ε • z) y + b - a, by linear_combination hb - ha⟩
  obtain ⟨a₁, h₁⟩ := dvd_left EF hee (g x) (g y)
  obtain ⟨a₂, h₂⟩ := dvd_left EF hee (k x) (k y)
  obtain ⟨a₃, h₃⟩ := cross x y
  obtain ⟨a₄, h₄⟩ := cross y x
  obtain ⟨a₅, h₅⟩ := dvd_left EF h4 x y
  have f₁ : EF (ε • g x) (ε • g y) = EF ((ε * bar ε) • g x) (g y) := by
    rw [mul_comm, mul_smul, adj (bar ε), hbb]
  have f₂ : EF (bar ε • k x) (bar ε • k y) = EF ((ε * bar ε) • k x) (k y) := by
    rw [mul_smul, adj ε]
  have f₃ : EF (bar ε • k x) (ε • g y) = - EF (ε • g y) (bar ε • k x) := skew EF alt _ _
  have f₄ : EF (ε • y) x = - EF (bar ε • x) y := by
    rw [adj (bar ε), hbb]
    exact skew EF alt _ _
  have f₅ : EF ((ε + bar ε - 1) • x) y = EF (ε • x) y + EF (bar ε • x) y - EF x y := by
    rw [sub_smul, add_smul, one_smul]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [f₁, f₂, f₃, h₁, h₂]
  exact ⟨a₁ + a₂ + a₃ - a₄ + a₅, by linear_combination h₃ - h₄ + h₅ - f₅ - f₄⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `hk`. Use `⟨b • z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, map_smul, smul_add, smul_add, smul_comm N b z, smul_comm ε c, smul_comm b c]`. Normalize the expressions using the abelian group laws.
-/
private theorem lin_step (N : ℕ) (ε b : A) (g : M →ₗ[A] M) (k : M →+ M)
    (c : A) (x : M) (hk : ∃ z, k (c • x) = c • k x + N • z) :
    ∃ z, ε • g (c • x) + b • k (c • x) = c • (ε • g x + b • k x) + N • z := by
  obtain ⟨z, hz⟩ := hk
  refine ⟨b • z, ?_⟩
  rw [hz, map_smul, smul_add, smul_add, smul_comm N b z, smul_comm ε c, smul_comm b c]
  abel

/- English proof (translation)
Use `Submodule.smul_induction_on hv ?_ ?_` and prove the remaining obligations. Introduce `c hc m _`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hc Submodule.mem_top`. Introduce `x y hx hy`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
private theorem smul_le (I : Ideal A) (h : M →ₗ[A] M) {v : M} (hv : v ∈ (I • ⊤ : Submodule A M)) :
    h v ∈ (I • ⊤ : Submodule A M) := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro c hc m _
    rw [map_smul]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/- English proof (translation)
Establish `e : h' y - h y = h ((g (h' y) - y) - (g (h y) - y)) - (h (g (h' y - h y)) - (h' y - h y))`. Simplify using `only [map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `sub_mem (smul_le u h (sub_mem (hgh' y) (hgh y))) (hhg _)`.
-/
private theorem diff_mem (u : Ideal A) (g h h' : M →ₗ[A] M)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh : ∀ x, g (h x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh' : ∀ x, g (h' x) - x ∈ (u • ⊤ : Submodule A M)) (y : M) :
    h' y - h y ∈ (u • ⊤ : Submodule A M) := by
  have e : h' y - h y = h ((g (h' y) - y) - (g (h y) - y)) - (h (g (h' y - h y)) - (h' y - h y)) := by
    simp only [map_sub]
    abel
  rw [e]
  exact sub_mem (smul_le u h (sub_mem (hgh' y) (hgh y))) (hhg _)

/- English proof (translation)
Establish `hmid : ∃ z, bar ε • (k' x - k x) = 0 + N • z`. Use `nd _ fun y => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `kill h3 (diff_mem u g h h' hhg hgh hgh' y)`. Take `⟨a, ha⟩` from `hk (ε • y) x`. Take `⟨b, hb⟩` from `hk' (ε • y) x`.

Establish `e₁ : EF (bar ε • (k' x - k x)) y = EF (k' x) (ε • y) - EF (k x) (ε • y)`. Rewrite using `[adj (bar ε), hbb]`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Establish `e₂ : EF (h' (ε • y)) x - EF (h (ε • y)) x = (N : ℤ) * EF w x`. Establish `e₀ : h' (ε • y) - h (ε • y) = ε • (h' y - h y)` using `by simp only [map_smul, smul_sub]`.

Rewrite using `[← ef_nsmul, ← hw, ← e₀]`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Rewrite using `[e₁, skew EF alt (k' x), skew EF alt (k x)]`. Conclude with `⟨b - a - EF w x, by linear_combination hb - ha - e₂⟩`. Take `⟨z, hz⟩` from `hmid`.

Take `⟨d, hd⟩` from `hεε`. Establish `hd' : bar ε' - bar ε = (N : A) * bar d`. Rewrite using `[← map_sub, hd, map_mul, map_natCast]`. Use `⟨d • g x + bar d • k' x + z, ?_⟩` and prove the remaining obligations. Establish `e₁ : ε' = ε + (N : A) * d` using `by linear_combination hd`.

Establish `e₂ : bar ε' = bar ε + (N : A) * bar d` using `by linear_combination hd'`. Rewrite `hz` using `[zero_add]`. Establish `e₃ : bar ε • k' x = bar ε • k x + N • z`. Rewrite using `[← hz, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e₂, add_smul, e₃, e₁, add_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_add, smul_add]`. Normalize the expressions using the abelian group laws.
-/
private theorem tow_step (alt : ∀ x, EF x x = 0) (hbb : ∀ c, bar (bar c) = c)
    (adj : ∀ (c : A) (x y : M), EF (c • x) y = EF x (bar c • y))
    (N : ℕ) (u : Ideal A) (ε ε' : A) (g h h' : M →ₗ[A] M) (k k' : M →+ M)
    (h3 : ∀ x ∈ u, (N : A) ∣ ε * x) (hεε : (N : A) ∣ ε' - ε)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh : ∀ x, g (h x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh' : ∀ x, g (h' x) - x ∈ (u • ⊤ : Submodule A M))
    (hk : ∀ x y, (N : ℤ) ∣ EF (h x) y - EF x (k y))
    (hk' : ∀ x y, (N : ℤ) ∣ EF (h' x) y - EF x (k' y))
    (nd : ∀ x : M, (∀ y, (N : ℤ) ∣ EF x y) → ∃ z, x = 0 + N • z) (x : M) :
    ∃ z, ε' • g x + bar ε' • k' x = ε • g x + bar ε • k x + N • z := by
  have hmid : ∃ z, bar ε • (k' x - k x) = 0 + N • z := by
    refine nd _ fun y => ?_
    obtain ⟨w, hw⟩ := kill h3 (diff_mem u g h h' hhg hgh hgh' y)
    obtain ⟨a, ha⟩ := hk (ε • y) x
    obtain ⟨b, hb⟩ := hk' (ε • y) x
    have e₁ : EF (bar ε • (k' x - k x)) y = EF (k' x) (ε • y) - EF (k x) (ε • y) := by
      rw [adj (bar ε), hbb]
      simp only [map_sub, LinearMap.sub_apply]
    have e₂ : EF (h' (ε • y)) x - EF (h (ε • y)) x = (N : ℤ) * EF w x := by
      have e₀ : h' (ε • y) - h (ε • y) = ε • (h' y - h y) := by simp only [map_smul, smul_sub]
      rw [← ef_nsmul, ← hw, ← e₀]
      simp only [map_sub, LinearMap.sub_apply]
    rw [e₁, skew EF alt (k' x), skew EF alt (k x)]
    exact ⟨b - a - EF w x, by linear_combination hb - ha - e₂⟩
  obtain ⟨z, hz⟩ := hmid
  obtain ⟨d, hd⟩ := hεε
  have hd' : bar ε' - bar ε = (N : A) * bar d := by
    rw [← map_sub, hd, map_mul, map_natCast]
  refine ⟨d • g x + bar d • k' x + z, ?_⟩
  have e₁ : ε' = ε + (N : A) * d := by linear_combination hd
  have e₂ : bar ε' = bar ε + (N : A) * bar d := by linear_combination hd'
  rw [zero_add] at hz
  have e₃ : bar ε • k' x = bar ε • k x + N • z := by
    rw [← hz, smul_sub]
    abel
  rw [e₂, add_smul, e₃, e₁, add_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    smul_add, smul_add]
  abel

/- English proof (translation)
Establish `e : (ε • v + b • w) - v = b • w - (1 - ε) • v` using `by module`. Rewrite using `[e]`. Conclude with `sub_mem (Submodule.smul_mem_smul h2 Submodule.mem_top) (Submodule.smul_mem_smul h1 Submodule.mem_top)`.
-/
private theorem lev_step (𝔟 : Ideal A) (ε b : A) (h1 : 1 - ε ∈ 𝔟) (h2 : b ∈ 𝔟) (v w : M) :
    (ε • v + b • w) - v ∈ (𝔟 • ⊤ : Submodule A M) := by
  have e : (ε • v + b • w) - v = b • w - (1 - ε) • v := by module
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul h2 Submodule.mem_top) (Submodule.smul_mem_smul h1 Submodule.mem_top)

end Core

/- English proof (translation)
Substitute `hP` using the available equality. Conclude with `liftUnit A M u 𝔞 hu hf g₀`.
-/
private theorem lift_of_eq (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (u 𝔞 : Ideal A) (hu : u ≠ ⊥) (hf : ∃ f : ℕ, u ^ f ≤ 𝔞)
    (P : Submodule A M) (hP : P = 𝔞 • ⊤) (g₀ : (M ⧸ P) ≃ₗ[A] (M ⧸ P)) :
    ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, P.mkQ (g x) = g₀ (P.mkQ x)) ∧
      ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M) := by
  subst hP
  exact liftUnit A M u 𝔞 hu hf g₀

/- English proof (translation)
Introduce `q _ D hm r hr 𝔞 hf g₀`. Take `⟨hbij, hproj, hfin⟩` from `mOne q D hm`. Take `⟨ε, hε⟩` from `idem q D r hr`. Use `letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)`. Use `haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩`.

Use `haveI : Module.Finite (𝓞 D.F) D.O := Module.Finite.of_surjective (Algebra.linearMap _ _) hbij.2`. Use `haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.trans D.O D.La`. Use `haveI : Module.Projective (𝓞 D.F) D.La := by`. Set `ρ : D.O ≃+* 𝓞 D.F` to `(RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).symm`. Use `letI i₁ : RingHomInvPair (ρ : D.O →+* 𝓞 D.F) (ρ.symm : 𝓞 D.F →+* D.O) := RingHomInvPair.of_ringEquiv ρ`.

Use `letI i₂ : RingHomInvPair (ρ.symm : 𝓞 D.F →+* D.O) (ρ : D.O →+* 𝓞 D.F) := RingHomInvPair.symm _ _`. Set `e₂ : D.La ≃ₛₗ[(ρ : D.O →+* 𝓞 D.F)] D.La` to `{ AddEquiv.refl D.La with map_smul' := fun c x => by`. Express the relevant statement in the definitionally equal form `c • x = algebraMap (𝓞 D.F) D.O (ρ c) • x`. Use `congr 1`. Conclude with `((RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).apply_symm_apply c).symm }`.

Conclude with `Module.Projective.of_equiv (σ' := (ρ.symm : 𝓞 D.F →+* D.O)) e₂`. Establish `hbb : ∀ c, D.bar (D.bar c) = c` using `fun c => hbij.1 (by`. Use `D.star_star (algebraMap _ _ c)` as an intermediate fact. Rewrite `this` using `[D.star_F, MulOpposite.unop_op, D.star_F, MulOpposite.unop_op]`. Conclude with `this)`.

Establish `adjA : ∀ (c : 𝓞 D.F) (x y : D.La), D.EF (c • x) y = D.EF x (D.bar c • y)` using `fun c x y => by`. Use `D.adj (algebraMap _ _ c) x y` as an intermediate fact. Rewrite `this` using `[D.star_F, MulOpposite.unop_op]`. Conclude with `this`. Establish `hP : (wSub D 𝔞 1).restrictScalars (𝓞 D.F) = 𝔞 • (⊤ : Submodule (𝓞 D.F) D.La)`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ ((Submodule.restrictScalars_mem _ _ _).1 hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, z, rfl⟩`. Conclude with `Submodule.smul_mem_smul (by rwa [pow_one] at hc) Submodule.mem_top`.

Conclude with `zero_mem _`. Introduce `a b _ _ ha hb`. Conclude with `add_mem ha hb`. Introduce `b a _ ha`. Take `⟨c, rfl⟩` from `hbij.2 b`.

Conclude with `Submodule.smul_mem _ c ha`. Use `Submodule.smul_le.2 fun c hc x _ => ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨c, by rwa [pow_one], x, rfl⟩`. Establish `hu : ES.uIdeal D r ≠ ⊥`. Introduce `h0`.

Establish `h1` using `ES.p_mem_uIdeal D r`. Rewrite `h1` using `[h0, Ideal.mem_bot]`. Conclude with `(Fact.out : q.Prime).ne_zero (Nat.cast_eq_zero.1 h1)`. Set `e₀` to `Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D 𝔞 1)`. Take `⟨g, h, hg, hgh⟩` from `lift_of_eq (𝓞 D.F) D.La (ES.uIdeal D r) 𝔞 hu hf _ hP (e₀.trans ((g₀.restrictScalars (𝓞 D.F)).trans e₀.symm))`.

Establish `hg' : ∀ x, (wSub D 𝔞 1).mkQ (g x) = g₀ ((wSub D 𝔞 1).mkQ x)` using `fun x => by`. Establish `he : ∀ y, e₀ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y` using `fun _ => rfl`. Use `congrArg e₀ (hg x)` as an intermediate fact. Simplify `this` using `[he]`. Set `hO : ℕ → (D.La →ₗ[D.O] D.La)` to `fun e => { toFun := h e map_add' := map_add _ map_smul' := fun c x => by`.

Take `⟨a, rfl⟩` from `hbij.2 c`. Conclude with `map_smul (h e) a x }`. Use `choose k hk hkl using fun e => (adj q D e).2.1 (hO e)`. Establish `hcast : ∀ e : ℕ, ((q ^ e : ℕ) : 𝓞 D.F) = (q : 𝓞 D.F) ^ e` using `fun e => by push_cast; rfl`. Use `⟨fun e => AddMonoidHom.mk' (fun x => ε e • g x + D.bar (ε e) • k e x) fun x y => by` and prove the remaining obligations.

Simplify using `only [map_add, smul_add]`. Use the proof step `abel, fun e => ?_⟩`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hε e`. Rewrite `h4`, `h5` using `[← hcast]`. Establish `h3' : ∀ x ∈ ES.uIdeal D r ^ e, ((q ^ e : ℕ) : 𝓞 D.F) ∣ ε e * x` using `fun x hx => by`.

Rewrite using `[hcast]`. Conclude with `h3 x hx`. Use `⟨fun c x => ?_, fun x y => ?_, fun x => ?_, fun hq x => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hbij.2 c`. Conclude with `lin_step (q ^ e) (ε e) (D.bar (ε e)) g (k e) a x (hkl e _ x)`.

Conclude with `iso_step D.bar D.EF hbb D.alt adjA (q ^ e) _ (ε e) g (h e) (k e) h1 h2 h3' h4 (fun x => (hgh e x).2) (hk e) x y`. Conclude with `tow_step D.bar D.EF D.alt hbb adjA (q ^ e) _ (ε e) (ε (e + 1)) g (h e) (h (e + 1)) (k e) (k (e + 1)) h3' h5 (fun x => (hgh e x).2) (fun x => (hgh e x).1) (fun x => Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) (hgh (e + 1) x).1) (hk e) (fun x y => dvd_trans (b …`. Establish `hle` using `h6 𝔞 hf hq`. Establish `hmem` using `lev_step 𝔞 (ε e) (D.bar (ε e)) (hle h1) (hle h2) (g x) (k e x)`. Rewrite `hmem` using `[← hP]`.

Rewrite using `[← hg' x]`. Conclude with `(Submodule.Quotient.eq _).2 hmem`.
-/
theorem qSys : QSys := by
  intro q _ D hm r hr 𝔞 hf g₀
  obtain ⟨hbij, hproj, hfin⟩ := mOne q D hm
  obtain ⟨ε, hε⟩ := idem q D r hr
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI : Module.Finite (𝓞 D.F) D.O := Module.Finite.of_surjective (Algebra.linearMap _ _) hbij.2
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.trans D.O D.La
  haveI : Module.Projective (𝓞 D.F) D.La := by
    let ρ : D.O ≃+* 𝓞 D.F := (RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).symm
    letI i₁ : RingHomInvPair (ρ : D.O →+* 𝓞 D.F) (ρ.symm : 𝓞 D.F →+* D.O) := RingHomInvPair.of_ringEquiv ρ
    letI i₂ : RingHomInvPair (ρ.symm : 𝓞 D.F →+* D.O) (ρ : D.O →+* 𝓞 D.F) := RingHomInvPair.symm _ _
    let e₂ : D.La ≃ₛₗ[(ρ : D.O →+* 𝓞 D.F)] D.La :=
      { AddEquiv.refl D.La with
        map_smul' := fun c x => by
          change c • x = algebraMap (𝓞 D.F) D.O (ρ c) • x
          congr 1
          exact ((RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).apply_symm_apply c).symm }
    exact Module.Projective.of_equiv (σ' := (ρ.symm : 𝓞 D.F →+* D.O)) e₂
  have hbb : ∀ c, D.bar (D.bar c) = c := fun c => hbij.1 (by
    have := D.star_star (algebraMap _ _ c)
    rw [D.star_F, MulOpposite.unop_op, D.star_F, MulOpposite.unop_op] at this
    exact this)
  have adjA : ∀ (c : 𝓞 D.F) (x y : D.La), D.EF (c • x) y = D.EF x (D.bar c • y) := fun c x y => by
    have := D.adj (algebraMap _ _ c) x y
    rw [D.star_F, MulOpposite.unop_op] at this
    exact this
  have hP : (wSub D 𝔞 1).restrictScalars (𝓞 D.F) = 𝔞 • (⊤ : Submodule (𝓞 D.F) D.La) := by
    apply le_antisymm
    · intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ((Submodule.restrictScalars_mem _ _ _).1 hx)
      · rintro _ ⟨c, hc, z, rfl⟩
        exact Submodule.smul_mem_smul (by rwa [pow_one] at hc) Submodule.mem_top
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro b a _ ha
        obtain ⟨c, rfl⟩ := hbij.2 b
        exact Submodule.smul_mem _ c ha
    · refine Submodule.smul_le.2 fun c hc x _ => ?_
      exact Submodule.subset_span ⟨c, by rwa [pow_one], x, rfl⟩
  have hu : ES.uIdeal D r ≠ ⊥ := by
    intro h0
    have h1 := ES.p_mem_uIdeal D r
    rw [h0, Ideal.mem_bot] at h1
    exact (Fact.out : q.Prime).ne_zero (Nat.cast_eq_zero.1 h1)
  let e₀ := Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D 𝔞 1)
  obtain ⟨g, h, hg, hgh⟩ := lift_of_eq (𝓞 D.F) D.La (ES.uIdeal D r) 𝔞 hu hf _ hP
    (e₀.trans ((g₀.restrictScalars (𝓞 D.F)).trans e₀.symm))
  have hg' : ∀ x, (wSub D 𝔞 1).mkQ (g x) = g₀ ((wSub D 𝔞 1).mkQ x) := fun x => by
    have he : ∀ y, e₀ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := fun _ => rfl
    have := congrArg e₀ (hg x)
    simpa [he] using this
  let hO : ℕ → (D.La →ₗ[D.O] D.La) := fun e =>
    { toFun := h e
      map_add' := map_add _
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := hbij.2 c
        exact map_smul (h e) a x }
  choose k hk hkl using fun e => (adj q D e).2.1 (hO e)
  have hcast : ∀ e : ℕ, ((q ^ e : ℕ) : 𝓞 D.F) = (q : 𝓞 D.F) ^ e := fun e => by push_cast; rfl
  refine ⟨fun e => AddMonoidHom.mk' (fun x => ε e • g x + D.bar (ε e) • k e x) fun x y => by
    simp only [map_add, smul_add]; abel, fun e => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hε e
  rw [← hcast] at h4 h5
  have h3' : ∀ x ∈ ES.uIdeal D r ^ e, ((q ^ e : ℕ) : 𝓞 D.F) ∣ ε e * x := fun x hx => by
    rw [hcast]; exact h3 x hx
  refine ⟨fun c x => ?_, fun x y => ?_, fun x => ?_, fun hq x => ?_⟩
  · obtain ⟨a, rfl⟩ := hbij.2 c
    exact lin_step (q ^ e) (ε e) (D.bar (ε e)) g (k e) a x (hkl e _ x)
  · exact iso_step D.bar D.EF hbb D.alt adjA (q ^ e) _ (ε e) g (h e) (k e) h1 h2 h3' h4
      (fun x => (hgh e x).2) (hk e) x y
  · exact tow_step D.bar D.EF D.alt hbb adjA (q ^ e) _ (ε e) (ε (e + 1)) g (h e) (h (e + 1)) (k e) (k (e + 1)) h3' h5
      (fun x => (hgh e x).2) (fun x => (hgh e x).1)
      (fun x => Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) (hgh (e + 1) x).1)
      (hk e)
      (fun x y => dvd_trans (by exact_mod_cast pow_dvd_pow q (Nat.le_succ e)) (hk (e + 1) x y))
      (adj q D e).1 x
  · have hle := h6 𝔞 hf hq
    have hmem := lev_step 𝔞 (ε e) (D.bar (ε e)) (hle h1) (hle h2) (g x) (k e x)
    rw [← hP] at hmem
    rw [← hg' x]
    exact (Submodule.Quotient.eq _).2 hmem

end UpperTheory.Gal.FiniteEtaleModels.O
